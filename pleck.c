/*
 * pleck — a tiny Plex client.
 *
 * Terminal browser on libcurl; playback is handed to mpv (hardware decoding,
 * direct play of the original file). The UI blocks in read() when idle and in
 * poll() during playback, so it uses no CPU unless a key is pressed.
 *
 * Lower qualities ask the server to transcode to HLS at a capped bitrate.
 *
 *   pleck          browse and play (signs in on first run)
 *   pleck logout   forget the stored token
 */
#define _GNU_SOURCE
#include <curl/curl.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

#define VERSION "0.1"
#define PAGE 500 /* library items fetched per request */
#define TICK 10  /* seconds between progress reports while playing */
#ifdef __APPLE__
#define PLATFORM "macOS"
#define OPENER "open"
#else
#define PLATFORM "Linux"
#define OPENER "xdg-open"
#endif

static void tui_end(void);

static void die(const char *fmt, ...)
{
	va_list ap;
	tui_end();
	va_start(ap, fmt);
	fputs("pleck: ", stderr);
	vfprintf(stderr, fmt, ap);
	fputc('\n', stderr);
	va_end(ap);
	exit(1);
}

/* ---------- arena ---------- */

typedef struct Block {
	struct Block *next;
	size_t used, cap;
	char data[];
} Block;
typedef struct {
	Block *head;
} Arena;

static void *aalloc(Arena *a, size_t n)
{
	n = (n + 7) & ~(size_t)7;
	if (!a->head || a->head->used + n > a->head->cap) {
		size_t cap = n > 16384 ? n : 16384;
		Block *b = malloc(sizeof *b + cap);
		if (!b)
			die("out of memory");
		b->next = a->head;
		b->used = 0;
		b->cap = cap;
		a->head = b;
	}
	void *p = a->head->data + a->head->used;
	a->head->used += n;
	return p;
}

static void afree(Arena *a)
{
	for (Block *b = a->head, *n; b; b = n) {
		n = b->next;
		free(b);
	}
	a->head = NULL;
}

static char *astrdup(Arena *a, const char *s)
{
	size_t n = strlen(s) + 1;
	return memcpy(aalloc(a, n), s, n);
}

/* ---------- growable buffer ---------- */

typedef struct {
	char *p;
	size_t n, cap;
} Buf;

static void bgrow(Buf *b, size_t extra)
{
	if (b->n + extra + 1 <= b->cap)
		return;
	size_t c = b->cap ? b->cap : 4096;
	while (c < b->n + extra + 1)
		c *= 2;
	b->p = realloc(b->p, c);
	if (!b->p)
		die("out of memory");
	b->cap = c;
}

static void bput(Buf *b, const char *d, size_t n)
{
	bgrow(b, n);
	memcpy(b->p + b->n, d, n);
	b->n += n;
	b->p[b->n] = 0;
}

static void bputs(Buf *b, const char *s)
{
	bput(b, s, strlen(s));
}

static void bfmt(Buf *b, const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	int n = vsnprintf(NULL, 0, fmt, ap);
	va_end(ap);
	if (n < 0)
		return;
	bgrow(b, (size_t)n);
	va_start(ap, fmt);
	vsnprintf(b->p + b->n, (size_t)n + 1, fmt, ap);
	va_end(ap);
	b->n += (size_t)n;
}

/* append s as the inside of a JSON string */
static void bjson(Buf *b, const char *s)
{
	for (; *s; s++) {
		unsigned char c = (unsigned char)*s;
		if (c == '"' || c == '\\')
			bfmt(b, "\\%c", c);
		else if (c < 0x20)
			bfmt(b, "\\u%04x", c);
		else
			bput(b, s, 1);
	}
}

/* ---------- JSON (parsed in place; the text buffer is modified) ---------- */

typedef enum { J_NULL, J_BOOL, J_NUM, J_STR, J_ARR, J_OBJ } JType;
typedef struct JVal {
	JType t;
	const char *key;
	struct JVal *next, *child;
	union {
		double num;
		const char *str;
		int b;
	};
} JVal;
typedef struct {
	char *p;
	Arena *a;
	int err, depth;
} JP;

static void jws(JP *j)
{
	while (*j->p == ' ' || *j->p == '\n' || *j->p == '\t' || *j->p == '\r')
		j->p++;
}

static unsigned jhex4(JP *j)
{
	unsigned v = 0;
	for (int i = 0; i < 4; i++) {
		char c = *j->p;
		if (c >= '0' && c <= '9')
			v = v << 4 | (unsigned)(c - '0');
		else if ((c | 32) >= 'a' && (c | 32) <= 'f')
			v = v << 4 | (unsigned)((c | 32) - 'a' + 10);
		else {
			j->err = 1;
			return 0;
		}
		j->p++;
	}
	return v;
}

static char *jstr(JP *j)
{
	char *r = ++j->p, *w = r;
	for (;;) {
		unsigned char c = (unsigned char)*j->p;
		if (!c) {
			j->err = 1;
			return r;
		}
		j->p++;
		if (c == '"')
			break;
		if (c != '\\') {
			*w++ = (char)c;
			continue;
		}
		c = (unsigned char)*j->p;
		if (!c) {
			j->err = 1;
			return r;
		}
		j->p++;
		switch (c) {
		case 'n': *w++ = '\n'; break;
		case 't': *w++ = '\t'; break;
		case 'r': *w++ = '\r'; break;
		case 'b': *w++ = '\b'; break;
		case 'f': *w++ = '\f'; break;
		case 'u': {
			unsigned cp = jhex4(j);
			if (cp >= 0xD800 && cp < 0xDC00 && j->p[0] == '\\' && j->p[1] == 'u') {
				j->p += 2;
				cp = 0x10000 + ((cp - 0xD800) << 10) + (jhex4(j) & 0x3FF);
			}
			if (j->err)
				return r;
			if (cp < 0x80)
				*w++ = (char)cp;
			else if (cp < 0x800) {
				*w++ = (char)(0xC0 | cp >> 6);
				*w++ = (char)(0x80 | (cp & 0x3F));
			} else if (cp < 0x10000) {
				*w++ = (char)(0xE0 | cp >> 12);
				*w++ = (char)(0x80 | (cp >> 6 & 0x3F));
				*w++ = (char)(0x80 | (cp & 0x3F));
			} else {
				*w++ = (char)(0xF0 | cp >> 18);
				*w++ = (char)(0x80 | (cp >> 12 & 0x3F));
				*w++ = (char)(0x80 | (cp >> 6 & 0x3F));
				*w++ = (char)(0x80 | (cp & 0x3F));
			}
			break;
		}
		default: *w++ = (char)c;
		}
	}
	*w = 0;
	return r;
}

static JVal *jval(JP *j)
{
	JVal *v = aalloc(j->a, sizeof *v);
	memset(v, 0, sizeof *v);
	jws(j);
	if (j->err)
		return v;
	if (++j->depth > 64) {
		j->err = 1;
		return v;
	}
	char c = *j->p;
	if (c == '{' || c == '[') {
		char close = c == '{' ? '}' : ']';
		JVal **tail = &v->child;
		v->t = c == '{' ? J_OBJ : J_ARR;
		j->p++;
		jws(j);
		if (*j->p == close)
			j->p++;
		else
			for (;;) {
				const char *key = NULL;
				if (v->t == J_OBJ) {
					jws(j);
					if (*j->p != '"') {
						j->err = 1;
						break;
					}
					key = jstr(j);
					jws(j);
					if (j->err || *j->p != ':') {
						j->err = 1;
						break;
					}
					j->p++;
				}
				JVal *e = jval(j);
				if (j->err)
					break;
				e->key = key;
				*tail = e;
				tail = &e->next;
				jws(j);
				if (*j->p == ',') {
					j->p++;
					continue;
				}
				if (*j->p == close) {
					j->p++;
					break;
				}
				j->err = 1;
				break;
			}
	} else if (c == '"') {
		v->t = J_STR;
		v->str = jstr(j);
	} else if (!strncmp(j->p, "true", 4)) {
		v->t = J_BOOL;
		v->b = 1;
		j->p += 4;
	} else if (!strncmp(j->p, "false", 5)) {
		v->t = J_BOOL;
		j->p += 5;
	} else if (!strncmp(j->p, "null", 4)) {
		j->p += 4;
	} else if (c == '-' || (c >= '0' && c <= '9')) {
		char *e;
		v->t = J_NUM;
		v->num = strtod(j->p, &e);
		if (e == j->p)
			j->err = 1;
		j->p = e;
	} else
		j->err = 1;
	j->depth--;
	return v;
}

static JVal *jparse(char *text, Arena *a)
{
	JP j = {text, a, 0, 0};
	JVal *v = jval(&j);
	return j.err ? NULL : v;
}

static JVal *jget(JVal *o, const char *k)
{
	if (!o || o->t != J_OBJ)
		return NULL;
	for (JVal *c = o->child; c; c = c->next)
		if (!strcmp(c->key, k))
			return c;
	return NULL;
}

static const char *jstrv(JVal *o, const char *k)
{
	JVal *v = jget(o, k);
	return v && v->t == J_STR ? v->str : NULL;
}

static double jnum(JVal *o, const char *k)
{
	JVal *v = jget(o, k);
	if (!v)
		return 0;
	if (v->t == J_NUM)
		return v->num;
	if (v->t == J_BOOL)
		return v->b;
	if (v->t == J_STR)
		return atof(v->str);
	return 0;
}

/* ---------- config ---------- */

static char cfg_dir[900], cfg_path[1024], client_id[64], token[256];

/* Stream qualities; 0 plays the original file, the rest transcode on the server. */
static const struct {
	const char *name, *res;
	int kbps;
} quals[] = {
	{"original", NULL, 0},        {"1080p 8 Mbps", "1920x1080", 8000}, {"720p 4 Mbps", "1280x720", 4000},
	{"720p 2 Mbps", "1280x720", 2000}, {"480p 1.5 Mbps", "720x480", 1500},  {"360p 0.7 Mbps", "576x320", 720},
	{"240p 0.3 Mbps", "420x240", 320},
};
#define NQUAL ((int)(sizeof quals / sizeof *quals))
static int quality;
static const char *plextv = "https://plex.tv";

static void cfg_save(void)
{
	mkdir(cfg_dir, 0700);
	int fd = open(cfg_path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
	if (fd < 0)
		die("cannot write %s: %s", cfg_path, strerror(errno));
	dprintf(fd, "client_id=%s\ntoken=%s\nquality=%d\n", client_id, token, quality);
	close(fd);
}

static void cfg_load(void)
{
	const char *x = getenv("XDG_CONFIG_HOME"), *h = getenv("HOME");
	if (x && *x)
		snprintf(cfg_dir, sizeof cfg_dir, "%s/pleck", x);
	else {
		char base[800];
		snprintf(base, sizeof base, "%s/.config", h ? h : ".");
		mkdir(base, 0700);
		snprintf(cfg_dir, sizeof cfg_dir, "%s/pleck", base);
	}
	snprintf(cfg_path, sizeof cfg_path, "%s/config", cfg_dir);

	FILE *f = fopen(cfg_path, "r");
	char line[512];
	while (f && fgets(line, sizeof line, f)) {
		line[strcspn(line, "\r\n")] = 0;
		if (!strncmp(line, "client_id=", 10))
			snprintf(client_id, sizeof client_id, "%s", line + 10);
		else if (!strncmp(line, "token=", 6))
			snprintf(token, sizeof token, "%s", line + 6);
		else if (!strncmp(line, "quality=", 8))
			quality = atoi(line + 8);
	}
	if (f)
		fclose(f);
	if (quality < 0 || quality >= NQUAL)
		quality = 0;

	if (!client_id[0]) {
		unsigned char r[16] = {0};
		int fd = open("/dev/urandom", O_RDONLY);
		if (fd < 0 || read(fd, r, sizeof r) != sizeof r)
			die("cannot read /dev/urandom");
		close(fd);
		for (int i = 0; i < 16; i++)
			sprintf(client_id + i * 2, "%02x", r[i]);
		cfg_save();
	}
}

/* ---------- HTTP ---------- */

static CURL *curl;
static Buf resp;
static char msg[512]; /* one-shot message for the footer */

static size_t on_data(char *d, size_t sz, size_t nm, void *u)
{
	bput(u, d, sz * nm);
	return sz * nm;
}

static size_t on_discard(char *d, size_t sz, size_t nm, void *u)
{
	(void)d;
	(void)u;
	return sz * nm;
}

static struct curl_slist *plex_headers(const char *tok)
{
	char line[400];
	struct curl_slist *h = NULL;
	h = curl_slist_append(h, "Accept: application/json");
	h = curl_slist_append(h, "X-Plex-Product: pleck");
	h = curl_slist_append(h, "X-Plex-Version: " VERSION);
	h = curl_slist_append(h, "X-Plex-Platform: " PLATFORM);
	h = curl_slist_append(h, "X-Plex-Device-Name: pleck");
	snprintf(line, sizeof line, "X-Plex-Client-Identifier: %s", client_id);
	h = curl_slist_append(h, line);
	if (tok && *tok) {
		snprintf(line, sizeof line, "X-Plex-Token: %s", tok);
		h = curl_slist_append(h, line);
	}
	return h;
}

/* Returns the HTTP status, or -1 on transport failure (msg is set). */
static long http(const char *method, const char *url, const char *tok, Buf *out, long timeout)
{
	char err[CURL_ERROR_SIZE] = "";
	struct curl_slist *h = plex_headers(tok);
	long code = -1;

	out->n = 0;
	bput(out, "", 0);
	curl_easy_reset(curl); /* keeps the connection cache */
	curl_easy_setopt(curl, CURLOPT_URL, url);
	curl_easy_setopt(curl, CURLOPT_HTTPHEADER, h);
	curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, on_data);
	curl_easy_setopt(curl, CURLOPT_WRITEDATA, out);
	curl_easy_setopt(curl, CURLOPT_TIMEOUT, timeout);
	curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, 8L);
	curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
	curl_easy_setopt(curl, CURLOPT_ACCEPT_ENCODING, "");
	curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, err);
	if (!strcmp(method, "POST"))
		curl_easy_setopt(curl, CURLOPT_POSTFIELDS, "");
	CURLcode rc = curl_easy_perform(curl);
	if (rc == CURLE_OK)
		curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &code);
	else
		snprintf(msg, sizeof msg, "Network error: %s", err[0] ? err : curl_easy_strerror(rc));
	curl_slist_free_all(h);
	return code;
}

/* ---------- account ---------- */

static void login(void)
{
	char url[1024], id[32], code[128];
	Arena a = {0};

	snprintf(url, sizeof url, "%s/api/v2/pins?strong=true", plextv);
	long st = http("POST", url, NULL, &resp, 20);
	JVal *r = st == 200 || st == 201 ? jparse(resp.p, &a) : NULL;
	if (!r || !jstrv(r, "code"))
		die("could not start sign-in (%s)", st < 0 ? msg : "unexpected response from plex.tv");
	snprintf(id, sizeof id, "%.0f", jnum(r, "id"));
	snprintf(code, sizeof code, "%s", jstrv(r, "code"));
	afree(&a);

	snprintf(url, sizeof url,
	         "https://app.plex.tv/auth#?clientID=%s&code=%s&context%%5Bdevice%%5D%%5Bproduct%%5D=pleck",
	         client_id, code);
	printf("Sign in to Plex in your browser:\n\n  %s\n\nWaiting for approval...\n", url);
	fflush(stdout);
	pid_t pid = fork();
	if (pid == 0) {
		int nul = open("/dev/null", O_RDWR);
		dup2(nul, 1);
		dup2(nul, 2);
		execlp(OPENER, OPENER, url, (char *)NULL);
		_exit(127);
	}
	if (pid > 0)
		waitpid(pid, NULL, 0);

	snprintf(url, sizeof url, "%s/api/v2/pins/%s", plextv, id);
	for (int i = 0; i < 300; i++) {
		sleep(2);
		st = http("GET", url, NULL, &resp, 20);
		if (st == 404)
			break;
		if (st != 200 || !(r = jparse(resp.p, &a)))
			continue;
		const char *t = jstrv(r, "authToken");
		if (t && *t) {
			snprintf(token, sizeof token, "%s", t);
			afree(&a);
			cfg_save();
			puts("Signed in.");
			return;
		}
		afree(&a);
	}
	die("sign-in timed out");
}

/* ---------- servers ---------- */

#define MAXCONN 16
typedef struct {
	char *name, *token, *base; /* base: chosen connection, NULL until connected */
	char *uri[MAXCONN];
	int rank[MAXCONN]; /* 0 local, 1 remote, 2 relay */
	int nuri;
} Server;

static Arena perm;
static Server *srv, *cur;
static int nsrv;

/* Returns the HTTP status of the resources request. */
static long load_servers(void)
{
	char url[1024];
	Arena a = {0};

	snprintf(url, sizeof url, "%s/api/v2/resources?includeHttps=1&includeRelay=1", plextv);
	long st = http("GET", url, token, &resp, 30);
	if (st != 200)
		return st;
	JVal *r = jparse(resp.p, &a);
	if (!r || r->t != J_ARR)
		die("unexpected response from plex.tv");
	int n = 0;
	for (JVal *d = r->child; d; d = d->next)
		n++;
	srv = aalloc(&perm, sizeof *srv * (size_t)(n ? n : 1));
	for (JVal *d = r->child; d; d = d->next) {
		const char *prov = jstrv(d, "provides"), *name = jstrv(d, "name"), *tok = jstrv(d, "accessToken");
		JVal *conns = jget(d, "connections");
		if (!prov || !strstr(prov, "server") || !name || !tok || !conns)
			continue;
		Server *s = &srv[nsrv];
		memset(s, 0, sizeof *s);
		s->name = astrdup(&perm, name);
		s->token = astrdup(&perm, tok);
		for (JVal *c = conns->child; c && s->nuri < MAXCONN; c = c->next) {
			const char *uri = jstrv(c, "uri");
			if (!uri)
				continue;
			s->rank[s->nuri] = jnum(c, "relay") ? 2 : jnum(c, "local") ? 0 : 1;
			s->uri[s->nuri++] = astrdup(&perm, uri);
		}
		if (s->nuri)
			nsrv++;
	}
	afree(&a);
	return st;
}

/*
 * Probe every connection at once and keep the most direct one that answers.
 * Once one answers, more direct ones get a second to beat it.
 */
static int connect_server(Server *s)
{
	CURLM *m = curl_multi_init();
	CURL *h[MAXCONN];
	int done[MAXCONN] = {0}, ok[MAXCONN] = {0}, running = 0, best = -1;
	time_t first_ok = 0;
	char url[1024];

	for (int i = 0; i < s->nuri; i++) {
		h[i] = curl_easy_init();
		snprintf(url, sizeof url, "%s/identity", s->uri[i]);
		curl_easy_setopt(h[i], CURLOPT_URL, url);
		curl_easy_setopt(h[i], CURLOPT_WRITEFUNCTION, on_discard);
		curl_easy_setopt(h[i], CURLOPT_TIMEOUT, 6L);
		curl_easy_setopt(h[i], CURLOPT_NOSIGNAL, 1L);
		curl_easy_setopt(h[i], CURLOPT_PRIVATE, (char *)(intptr_t)i);
		curl_multi_add_handle(m, h[i]);
	}
	do {
		CURLMsg *cm;
		int q;
		curl_multi_perform(m, &running);
		while ((cm = curl_multi_info_read(m, &q))) {
			char *pv;
			long code = 0;
			if (cm->msg != CURLMSG_DONE)
				continue;
			curl_easy_getinfo(cm->easy_handle, CURLINFO_PRIVATE, &pv);
			curl_easy_getinfo(cm->easy_handle, CURLINFO_RESPONSE_CODE, &code);
			int i = (int)(intptr_t)pv;
			done[i] = 1;
			ok[i] = cm->data.result == CURLE_OK && code == 200;
		}
		best = -1;
		for (int i = 0; i < s->nuri; i++)
			if (ok[i] && (best < 0 || s->rank[i] < s->rank[best]))
				best = i;
		if (best >= 0) {
			int better_pending = 0;
			for (int i = 0; i < s->nuri; i++)
				if (!done[i] && s->rank[i] < s->rank[best])
					better_pending = 1;
			if (!first_ok)
				first_ok = time(NULL);
			if (!better_pending || time(NULL) - first_ok >= 2)
				break;
		}
		if (running)
			curl_multi_poll(m, NULL, 0, 500, NULL);
	} while (running);
	for (int i = 0; i < s->nuri; i++) {
		curl_multi_remove_handle(m, h[i]);
		curl_easy_cleanup(h[i]);
	}
	curl_multi_cleanup(m);
	s->base = best >= 0 ? s->uri[best] : NULL;
	return best >= 0;
}

/* ---------- views ---------- */

enum { IT_SERVER, IT_DIR, IT_VIDEO };
typedef struct {
	char *title, *key; /* key: path to list (dir) or ratingKey (video) */
	char *part;        /* video: path of the media file */
	int kind, srv;
	int dur, off; /* seconds */
	int watched, leaf, seen;
} Item;

typedef struct View {
	struct View *parent;
	Arena a;
	char *title;
	Item *items;
	int n, cap;
	int *vis, nvis; /* indices of items matching the filter */
	int sel, top;
	char filter[64];
} View;

static View *view;
static int filtering;

static Item *push_item(View *v)
{
	if (v->n == v->cap) {
		v->cap = v->cap ? v->cap * 2 : 64;
		v->items = realloc(v->items, sizeof(Item) * (size_t)v->cap);
		if (!v->items)
			die("out of memory");
	}
	Item *it = &v->items[v->n++];
	memset(it, 0, sizeof *it);
	return it;
}

static void refilter(View *v)
{
	if (!v->vis && v->n && !(v->vis = malloc(sizeof(int) * (size_t)v->n)))
		die("out of memory");
	v->nvis = 0;
	for (int i = 0; i < v->n; i++)
		if (!v->filter[0] || strcasestr(v->items[i].title, v->filter))
			v->vis[v->nvis++] = i;
	v->sel = v->top = 0;
}

static void free_view(View *v)
{
	afree(&v->a);
	free(v->items);
	free(v->vis);
	free(v);
}

static void add_item(View *v, JVal *m)
{
	const char *type = jstrv(m, "type"), *title = jstrv(m, "title"), *key = jstrv(m, "key");
	char tbuf[600], kbuf[300];

	if (!title || !key)
		return;
	if (type && (!strcmp(type, "artist") || !strcmp(type, "photo") || !strcmp(type, "album") ||
	             !strcmp(type, "track")))
		return;
	const char *rk = jstrv(m, "ratingKey"); /* absent on library sections, which share these types */
	if (rk && type && (!strcmp(type, "movie") || !strcmp(type, "episode") || !strcmp(type, "clip"))) {
		JVal *media = jget(m, "Media");
		JVal *parts = media && media->child ? jget(media->child, "Part") : NULL;
		const char *pk = parts && parts->child ? jstrv(parts->child, "key") : NULL;
		if (!pk)
			return;
		if (!strcmp(type, "episode") && jget(m, "index"))
			snprintf(tbuf, sizeof tbuf, "%2d. %s", (int)jnum(m, "index"), title);
		else if (jget(m, "year"))
			snprintf(tbuf, sizeof tbuf, "%s (%d)", title, (int)jnum(m, "year"));
		else
			snprintf(tbuf, sizeof tbuf, "%s", title);
		Item *it = push_item(v);
		it->kind = IT_VIDEO;
		it->title = astrdup(&v->a, tbuf);
		it->key = astrdup(&v->a, rk);
		it->part = astrdup(&v->a, pk);
		it->dur = (int)(jnum(m, "duration") / 1000);
		it->off = (int)(jnum(m, "viewOffset") / 1000);
		it->watched = jnum(m, "viewCount") > 0;
		return;
	}
	if (key[0] != '/') { /* library sections are listed by bare id */
		snprintf(kbuf, sizeof kbuf, "/library/sections/%s/all", key);
		key = kbuf;
	}
	Item *it = push_item(v);
	it->kind = IT_DIR;
	it->title = astrdup(&v->a, title);
	it->key = astrdup(&v->a, key);
	it->leaf = (int)jnum(m, "leafCount");
	it->seen = (int)jnum(m, "viewedLeafCount");
}

/* Fetch a server directory listing, PAGE items at a time. */
static View *load_view(const char *path, const char *title)
{
	View *v = calloc(1, sizeof *v);
	char url[2048];
	int start = 0, total = 0, count;

	if (!v)
		die("out of memory");
	v->title = astrdup(&v->a, title);
	do {
		Arena ja = {0};
		snprintf(url, sizeof url, "%s%s%cX-Plex-Container-Start=%d&X-Plex-Container-Size=%d", cur->base,
		         path, strchr(path, '?') ? '&' : '?', start, PAGE);
		long st = http("GET", url, cur->token, &resp, 60);
		JVal *root = st == 200 ? jparse(resp.p, &ja) : NULL;
		JVal *mc = jget(root, "MediaContainer");
		if (!mc) {
			if (st >= 0)
				snprintf(msg, sizeof msg, "Server error (HTTP %ld)", st);
			afree(&ja);
			free_view(v);
			return NULL;
		}
		JVal *arr = jget(mc, "Metadata");
		if (!arr)
			arr = jget(mc, "Directory");
		count = 0;
		for (JVal *m = arr ? arr->child : NULL; m; m = m->next, count++)
			add_item(v, m);
		total = (int)jnum(mc, jget(mc, "totalSize") ? "totalSize" : "size");
		start += count;
		afree(&ja);
	} while (count == PAGE && start < total);
	if (resp.cap > (1 << 20)) { /* don't hold on to a large response buffer */
		free(resp.p);
		resp = (Buf){0};
	}
	refilter(v);
	return v;
}

/* ---------- terminal ---------- */

static struct termios tio_orig;
static int tui_on, rows = 24;

static void tui_end(void)
{
	static const char s[] = "\x1b[?7h\x1b[?25h\x1b[?1049l";
	if (!tui_on)
		return;
	tui_on = 0;
	if (write(1, s, sizeof s - 1) < 0) {
	}
	tcsetattr(0, TCSAFLUSH, &tio_orig);
}

static void on_term(int sig)
{
	tui_end();
	_exit(128 + sig);
}

static void on_winch(int sig)
{
	(void)sig;
}

static void tui_init(void)
{
	static const char s[] = "\x1b[?1049h\x1b[?7l\x1b[?25l"; /* alt screen, no wrap, no cursor */
	struct termios t;
	struct sigaction sa = {0};

	if (!isatty(0) || !isatty(1))
		die("needs a terminal");
	tcgetattr(0, &tio_orig);
	t = tio_orig;
	cfmakeraw(&t);
	tcsetattr(0, TCSAFLUSH, &t);
	tui_on = 1;
	atexit(tui_end);
	sa.sa_handler = on_winch; /* no SA_RESTART: read() returns EINTR and we redraw */
	sigaction(SIGWINCH, &sa, NULL);
	sa.sa_handler = on_term;
	sigaction(SIGTERM, &sa, NULL);
	sigaction(SIGHUP, &sa, NULL);
	sigaction(SIGINT, &sa, NULL);
	signal(SIGPIPE, SIG_IGN);
	if (write(1, s, sizeof s - 1) < 0) {
	}
}

enum { KEY_UP = 1000, KEY_DOWN, KEY_LEFT, KEY_RIGHT, KEY_PGUP, KEY_PGDN, KEY_HOME, KEY_END, KEY_ESC, KEY_RESIZE };

static int readkey(void)
{
	unsigned char c, s[3];
	struct pollfd p = {0, POLLIN, 0};
	ssize_t r = read(0, &c, 1);

	if (r < 0)
		return errno == EINTR ? KEY_RESIZE : 'q';
	if (r == 0)
		return 'q';
	if (c != 27)
		return c;
	if (poll(&p, 1, 30) <= 0 || read(0, &s[0], 1) != 1)
		return KEY_ESC;
	if ((s[0] != '[' && s[0] != 'O') || read(0, &s[1], 1) != 1)
		return KEY_ESC;
	switch (s[1]) {
	case 'A': return KEY_UP;
	case 'B': return KEY_DOWN;
	case 'C': return KEY_RIGHT;
	case 'D': return KEY_LEFT;
	case 'H': return KEY_HOME;
	case 'F': return KEY_END;
	}
	if (s[1] >= '0' && s[1] <= '9') {
		while (read(0, &s[2], 1) == 1 && s[2] != '~' && (s[2] == ';' || (s[2] >= '0' && s[2] <= '9')))
			;
		switch (s[1]) {
		case '1': case '7': return KEY_HOME;
		case '4': case '8': return KEY_END;
		case '5': return KEY_PGUP;
		case '6': return KEY_PGDN;
		}
	}
	return KEY_ESC;
}

static void fmt_dur(char *out, size_t n, int sec)
{
	if (sec >= 3600)
		snprintf(out, n, "%dh %02dm", sec / 3600, sec % 3600 / 60);
	else
		snprintf(out, n, "%dm", sec / 60 > 0 ? sec / 60 : 1);
}

static void crumbs(Buf *o, View *v)
{
	if (v->parent) {
		crumbs(o, v->parent);
		bputs(o, " \xe2\x80\xba ");
	}
	bputs(o, v->title);
}

static void draw(void)
{
	static Buf o;
	struct winsize ws;
	View *v = view;

	if (ioctl(1, TIOCGWINSZ, &ws) == 0 && ws.ws_row > 0)
		rows = ws.ws_row;
	int body = rows > 3 ? rows - 2 : 1;
	if (v->sel >= v->nvis)
		v->sel = v->nvis ? v->nvis - 1 : 0;
	if (v->sel < v->top)
		v->top = v->sel;
	if (v->sel >= v->top + body)
		v->top = v->sel - body + 1;

	o.n = 0;
	bputs(&o, "\x1b[H\x1b[1m ");
	crumbs(&o, v);
	bputs(&o, "\x1b[0m");
	if (filtering || v->filter[0])
		bfmt(&o, "   /%s%s", v->filter, filtering ? "_" : "");
	bputs(&o, "\x1b[K\r\n");
	for (int i = 0; i < body; i++) {
		int k = v->top + i;
		if (k < v->nvis) {
			Item *it = &v->items[v->vis[k]];
			char d[32], e[32];
			const char *mark = " ";
			if (it->kind == IT_VIDEO)
				mark = it->off > 0 ? "\xe2\x97\x90" : it->watched ? " " : "\xe2\x97\x8f";
			else if (it->kind == IT_DIR && it->leaf > it->seen)
				mark = "\xe2\x97\x8f";
			if (k == v->sel)
				bputs(&o, "\x1b[7m");
			bfmt(&o, " %s %s", mark, it->title);
			if (it->kind == IT_VIDEO && it->dur) {
				fmt_dur(d, sizeof d, it->dur);
				if (it->off > 0) {
					fmt_dur(e, sizeof e, it->off);
					bfmt(&o, "\x1b[2m   %s of %s\x1b[22m", e, d);
				} else
					bfmt(&o, "\x1b[2m   %s\x1b[22m", d);
			} else if (it->kind == IT_DIR && it->leaf > it->seen)
				bfmt(&o, "\x1b[2m   %d unwatched\x1b[22m", it->leaf - it->seen);
			bputs(&o, " \x1b[0m");
		} else if (i == 0)
			bputs(&o, "\x1b[2m   (nothing here)\x1b[0m");
		bputs(&o, "\x1b[K\r\n");
	}
	if (msg[0])
		bfmt(&o, " %s", msg);
	else
		bfmt(&o,
		     "\x1b[2m %d/%d   enter open   \xe2\x86\x90 back   / filter   v quality: %s   b play from start   w watched"
		     "   q quit\x1b[0m",
		     v->nvis ? v->sel + 1 : 0, v->nvis, quals[quality].name);
	bputs(&o, "\x1b[K");
	msg[0] = 0;
	if (write(1, o.p, o.n) < 0) {
	}
}

static void status(const char *fmt, ...)
{
	char s[512];
	va_list ap;
	va_start(ap, fmt);
	vsnprintf(s, sizeof s, fmt, ap);
	va_end(ap);
	dprintf(1, "\x1b[%d;1H %s\x1b[K", rows, s);
}

/* ---------- playback ---------- */

static void timeline(Item *it, const char *state, double pos)
{
	char url[2048], keep[sizeof msg];
	snprintf(url, sizeof url,
	         "%s/:/timeline?ratingKey=%s&key=%%2Flibrary%%2Fmetadata%%2F%s&state=%s&time=%lld&duration=%lld"
	         "&identifier=com.plexapp.plugins.library",
	         cur->base, it->key, it->key, state, (long long)(pos * 1000), (long long)it->dur * 1000);
	memcpy(keep, msg, sizeof msg); /* progress reports fail silently */
	http("GET", url, cur->token, &resp, 5);
	memcpy(msg, keep, sizeof msg);
}

/*
 * Run mpv on the item and wait for it to exit. mpv is driven over a private
 * socketpair, so the tokenised URL never appears in a process listing.
 */
static void play(Item *it, int resume)
{
	int sv[2], started = 0, paused = 0;
	double pos = resume ? it->off : 0;
	Buf c = {0};
	char line[8192], session[96] = "";
	size_t ln = 0;

	if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) < 0) {
		snprintf(msg, sizeof msg, "socketpair: %s", strerror(errno));
		return;
	}
	pid_t pid = fork();
	if (pid < 0) {
		snprintf(msg, sizeof msg, "fork: %s", strerror(errno));
		close(sv[0]);
		close(sv[1]);
		return;
	}
	if (pid == 0) {
		close(sv[0]);
		if (sv[1] != 3) {
			dup2(sv[1], 3);
			close(sv[1]);
		}
		int nul = open("/dev/null", O_RDWR);
		dup2(nul, 0);
		dup2(nul, 1);
		dup2(nul, 2);
		for (int fd = 4; fd < 256; fd++)
			close(fd);
		execlp("mpv", "mpv", "--idle=once", "--force-window=immediate", "--no-terminal",
		       "--hwdec=auto-safe", "--input-ipc-client=fd://3", (char *)NULL);
		_exit(127);
	}
	close(sv[1]);

	bputs(&c, "{\"command\":[\"set_property\",\"options/force-media-title\",\"");
	bjson(&c, it->title + strspn(it->title, " "));
	bputs(&c, "\"]}\n");
	if (pos > 0)
		bfmt(&c, "{\"command\":[\"set_property\",\"options/start\",\"%d\"]}\n", (int)pos);
	/*
	 * The server refuses to transcode (HTTP 400) for a platform it has no
	 * client profile for, so transcode requests borrow Chrome's: HLS, H.264, AAC.
	 */
	if (quality) {
		snprintf(session, sizeof session, "%s-%lx", client_id, (unsigned long)time(NULL));
		bputs(&c, "{\"command\":[\"set_property\",\"options/http-header-fields\",\"X-Plex-Token: ");
		bjson(&c, cur->token);
		bfmt(&c, ",X-Plex-Client-Identifier: %s,X-Plex-Session-Identifier: %s,X-Plex-Product: pleck"
		         ",X-Plex-Platform: Chrome\"]}\n",
		     client_id, session);
	}
	if (quality) /* the server can take a while to start transcoding; say so in the player window */
		bputs(&c, "{\"command\":[\"show-text\",\"Waiting for the server to transcode...\",600000]}\n");
	bputs(&c, "{\"command\":[\"loadfile\",\"");
	bjson(&c, cur->base);
	if (quality)
		bfmt(&c,
		     "/video/:/transcode/universal/start.m3u8?path=%%2Flibrary%%2Fmetadata%%2F%s&mediaIndex=0&partIndex=0"
		     "&protocol=hls&directPlay=0&directStream=1&directStreamAudio=1&fastSeek=1&copyts=1&location=wan"
		     "&videoQuality=100&videoResolution=%s&maxVideoBitrate=%d&session=%s&X-Plex-Session-Identifier=%s"
		     "&X-Plex-Client-Identifier=%s&X-Plex-Product=pleck&X-Plex-Platform=Chrome&X-Plex-Token=",
		     it->key, quals[quality].res, quals[quality].kbps, session, session, client_id);
	else {
		bjson(&c, it->part);
		bputs(&c, "?X-Plex-Token=");
	}
	bjson(&c, cur->token);
	bputs(&c, "\"]}\n");
	if (write(sv[0], c.p, c.n) < 0) {
	}
	memset(c.p, 0, c.n);
	free(c.p);

	status("Playing %s (%s) \xe2\x80\x94 quit mpv to come back", it->title + strspn(it->title, " "),
	       quals[quality].name);

	static const char ask[] = "{\"command\":[\"get_property\",\"time-pos\"],\"request_id\":1}\n"
	                          "{\"command\":[\"get_property\",\"pause\"],\"request_id\":2}\n";
	struct pollfd pf = {sv[0], POLLIN, 0};
	time_t next = time(NULL) + TICK;
	for (;;) {
		time_t now = time(NULL);
		if (now >= next) {
			if (write(sv[0], ask, sizeof ask - 1) < 0) {
			}
			next = now + TICK;
		}
		int r = poll(&pf, 1, (int)(next - now) * 1000);
		if (r < 0 && errno != EINTR)
			break;
		if (r <= 0)
			continue;
		ssize_t n = read(sv[0], line + ln, sizeof line - 1 - ln);
		if (n <= 0)
			break; /* mpv exited */
		ln += (size_t)n;
		line[ln] = 0;
		char *s = line, *nl;
		while ((nl = strchr(s, '\n'))) {
			Arena ja = {0};
			*nl = 0;
			JVal *j = jparse(s, &ja);
			const char *err = jstrv(j, "error"), *ev = jstrv(j, "event"), *why = jstrv(j, "reason");
			if (ev && session[0] && !strcmp(ev, "playback-restart")) {
				static const char clear[] = "{\"command\":[\"show-text\",\"\",1]}\n";
				if (write(sv[0], clear, sizeof clear - 1) < 0) {
				}
			}
			if (ev && why && !strcmp(ev, "end-file") && !strcmp(why, "eof") && it->dur) {
				pos = it->dur; /* played to the end */
				started = 1;
			}
			int id = (int)jnum(j, "request_id");
			if (id == 1 && err && !strcmp(err, "success")) {
				pos = jnum(j, "data");
				started = 1;
			} else if (id == 2) {
				paused = jnum(j, "data") != 0;
				if (started)
					timeline(it, paused ? "paused" : "playing", pos);
			}
			afree(&ja);
			s = nl + 1;
		}
		ln = strlen(s);
		memmove(line, s, ln);
		if (ln == sizeof line - 1)
			ln = 0;
	}
	close(sv[0]);
	int ws = 0;
	waitpid(pid, &ws, 0);
	if (WIFEXITED(ws) && WEXITSTATUS(ws) == 127)
		snprintf(msg, sizeof msg, "Could not run mpv \xe2\x80\x94 is it installed and on PATH?");
	if (session[0]) { /* release the server's transcoder */
		char url[2048], keep[sizeof msg];
		snprintf(url, sizeof url, "%s/video/:/transcode/universal/stop?session=%s", cur->base, session);
		memcpy(keep, msg, sizeof msg);
		http("GET", url, cur->token, &resp, 5);
		memcpy(msg, keep, sizeof msg);
	}
	if (started) {
		timeline(it, "stopped", pos);
		if (it->dur && pos >= it->dur * 0.9) {
			it->watched = 1;
			it->off = 0;
		} else
			it->off = (int)pos;
	}
	tcflush(0, TCIFLUSH);
}

static void toggle_watched(Item *it)
{
	char url[2048];
	snprintf(url, sizeof url, "%s/:/%s?identifier=com.plexapp.plugins.library&key=%s", cur->base,
	         it->watched ? "unscrobble" : "scrobble", it->key);
	if (http("GET", url, cur->token, &resp, 10) == 200) {
		it->watched = !it->watched;
		it->off = 0;
	} else if (!msg[0])
		snprintf(msg, sizeof msg, "Could not update watched state");
}

/* ---------- main ---------- */

static Item *selected(void)
{
	return view->nvis ? &view->items[view->vis[view->sel]] : NULL;
}

static void open_selected(int resume)
{
	Item *it = selected();
	const char *path;

	if (!it)
		return;
	if (it->kind == IT_VIDEO) {
		play(it, resume);
		return;
	}
	if (it->kind == IT_SERVER) {
		cur = &srv[it->srv];
		if (!cur->base) {
			status("Connecting to %s...", cur->name);
			if (!connect_server(cur)) {
				snprintf(msg, sizeof msg, "Could not reach %s", cur->name);
				return;
			}
		}
		path = "/library/sections";
	} else
		path = it->key;
	status("Loading...");
	View *n = load_view(path, it->title + strspn(it->title, " "));
	if (!n) {
		if (it->kind == IT_SERVER)
			cur->base = NULL; /* reprobe connections next time */
		return;
	}
	n->parent = view;
	view = n;
	filtering = 0;
}

static void go_back(void)
{
	if (!view->parent)
		return;
	View *p = view->parent;
	free_view(view);
	view = p;
	filtering = 0;
}

int main(int argc, char **argv)
{
	if (getenv("PLECK_PLEXTV")) /* alternate plex.tv endpoint, for testing */
		plextv = getenv("PLECK_PLEXTV");
	cfg_load();
	if (argc == 2 && !strcmp(argv[1], "logout")) {
		token[0] = 0;
		cfg_save();
		puts("Signed out.");
		return 0;
	}
	if (argc > 1) {
		fputs("usage: pleck [logout]\n", stderr);
		return 2;
	}
	curl_global_init(CURL_GLOBAL_DEFAULT);
	if (!(curl = curl_easy_init()))
		die("cannot initialise libcurl");

	if (!token[0])
		login();
	long st = load_servers();
	if (st == 401) { /* stored token was revoked */
		login();
		st = load_servers();
	}
	if (st != 200)
		die("could not list servers (%s)", st < 0 ? msg : "unexpected response from plex.tv");
	if (!nsrv)
		die("no Plex servers are available to this account");
	msg[0] = 0;

	view = calloc(1, sizeof *view);
	if (!view)
		die("out of memory");
	view->title = "pleck";
	for (int i = 0; i < nsrv; i++) {
		Item *it = push_item(view);
		it->kind = IT_SERVER;
		it->srv = i;
		it->title = srv[i].name;
	}
	refilter(view);

	tui_init();
	if (nsrv == 1) {
		draw();
		open_selected(1);
	}
	for (;;) {
		draw();
		int k = readkey(), page = rows > 3 ? rows - 2 : 1;
		View *v = view;

		if (filtering) {
			size_t len = strlen(v->filter);
			if (k == '\r' || k == '\n') {
				filtering = 0;
				continue;
			}
			if (k == KEY_ESC) {
				filtering = 0;
				v->filter[0] = 0;
				refilter(v);
				continue;
			}
			if (k == 127 || k == 8) {
				if (!len)
					filtering = 0;
				else {
					do
						len--;
					while (len && ((unsigned char)v->filter[len] & 0xC0) == 0x80);
					v->filter[len] = 0;
					refilter(v);
				}
				continue;
			}
			if (k >= 32 && k < 256) {
				if (len + 1 < sizeof v->filter) {
					v->filter[len] = (char)k;
					v->filter[len + 1] = 0;
					refilter(v);
				}
				continue;
			}
		}
		switch (k) {
		case 'q':
		case 3: /* ^C */
			tui_end();
			return 0;
		case 'j':
		case KEY_DOWN:
			if (v->sel + 1 < v->nvis)
				v->sel++;
			break;
		case 'k':
		case KEY_UP:
			if (v->sel > 0)
				v->sel--;
			break;
		case ' ':
		case 6: /* ^F */
		case KEY_PGDN:
			v->sel += page;
			break;
		case 2: /* ^B */
		case KEY_PGUP:
			v->sel = v->sel > page ? v->sel - page : 0;
			break;
		case 'g':
		case KEY_HOME:
			v->sel = 0;
			break;
		case 'G':
		case KEY_END:
			v->sel = v->nvis;
			break;
		case '\r':
		case '\n':
		case 'l':
		case KEY_RIGHT:
			open_selected(1);
			break;
		case 'b':
			if (selected() && selected()->kind == IT_VIDEO)
				open_selected(0);
			break;
		case 'w':
			if (selected() && selected()->kind == IT_VIDEO)
				toggle_watched(selected());
			break;
		case 'h':
		case 127:
		case KEY_LEFT:
			go_back();
			break;
		case KEY_ESC:
			if (v->filter[0]) {
				v->filter[0] = 0;
				refilter(v);
			}
			break;
		case '/':
			filtering = 1;
			break;
		case 'v':
			quality = (quality + 1) % NQUAL;
			cfg_save();
			break;
		case 'V':
			quality = (quality + NQUAL - 1) % NQUAL;
			cfg_save();
			break;
		}
	}
}
