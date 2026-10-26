/*
 * ytv — a tiny YouTube client.
 *
 * Terminal browser for your subscriptions, playlists and liked videos on
 * YouTube's own web API (libcurl), signed in with your browser's cookies,
 * which yt-dlp reads out for us; playback is handed to mpv, which resolves the
 * stream with yt-dlp using the same cookies. The UI blocks in read() when idle
 * and in poll() during playback, so it uses no CPU unless a key is pressed.
 *
 * Playback isn't reported to YouTube, so watch progress is kept locally.
 *
 *   ytv            browse and play, signed in as you are in the browser
 *   ytv <browser>  use (and remember) another browser: firefox, chrome, ...
 */
#define _GNU_SOURCE
#include <curl/curl.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
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
#define PAGEMAX 500 /* videos fetched for a playlist or channel */
#define FEED_MAX 200 /* videos fetched for the feed */
#define TICK 5      /* seconds between position checks while playing */
#define ORIGIN "https://www.youtube.com"
#define CLIENT_VERSION "2.20260708.00.00" /* the web client's */
#ifdef __APPLE__
#define OPENER "open"
#define BROWSER "safari"
#else
#define OPENER "xdg-open"
#define BROWSER "firefox"
#endif

static void tui_end(void);
static void status(const char *fmt, ...);

static void die(const char *fmt, ...)
{
	va_list ap;
	tui_end();
	va_start(ap, fmt);
	fputs("ytv: ", stderr);
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

/* the first string under key k anywhere inside o, depth first */
static const char *jfindstr(JVal *o, const char *k)
{
	if (!o || (o->t != J_OBJ && o->t != J_ARR))
		return NULL;
	for (JVal *c = o->child; c; c = c->next) {
		const char *s = c->key && !strcmp(c->key, k) && c->t == J_STR ? c->str : jfindstr(c, k);
		if (s)
			return s;
	}
	return NULL;
}

/* YouTube text: {"simpleText": s}, {"runs": [{"text": s}, ...]} or {"content": s} */
static char *jtext(JVal *t, char *out, size_t n)
{
	JVal *runs = jget(t, "runs");
	const char *s = jstrv(t, "simpleText") ? jstrv(t, "simpleText") : jstrv(t, "content");
	size_t l = 0;
	out[0] = 0;
	if (s)
		l = (size_t)snprintf(out, n, "%s", s);
	for (JVal *r = runs ? runs->child : NULL; r && l + 1 < n; r = r->next)
		if (jstrv(r, "text"))
			l += (size_t)snprintf(out + l, n - l, "%s", jstrv(r, "text"));
	return out[0] ? out : NULL;
}

static char *adup(Arena *a, const char *s)
{
	return s ? astrdup(a, s) : NULL;
}

/* ---------- SHA-1, for the SAPISIDHASH that signs requests ---------- */

static uint32_t rol(uint32_t x, int n)
{
	return x << n | x >> (32 - n);
}

static void sha1_hex(const char *s, char out[41])
{
	uint32_t h[5] = {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0};
	size_t n = strlen(s), total = ((n + 8) / 64 + 1) * 64;
	uint64_t bits = (uint64_t)n * 8;
	unsigned char *m = calloc(1, total);
	if (!m)
		die("out of memory");
	memcpy(m, s, n);
	m[n] = 0x80;
	for (int i = 0; i < 8; i++)
		m[total - 1 - i] = (unsigned char)(bits >> 8 * i);
	for (size_t off = 0; off < total; off += 64) {
		uint32_t w[80], a = h[0], b = h[1], c = h[2], d = h[3], e = h[4];
		for (int i = 0; i < 16; i++)
			w[i] = (uint32_t)m[off + 4 * i] << 24 | (uint32_t)m[off + 4 * i + 1] << 16 |
			       (uint32_t)m[off + 4 * i + 2] << 8 | m[off + 4 * i + 3];
		for (int i = 16; i < 80; i++)
			w[i] = rol(w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16], 1);
		for (int i = 0; i < 80; i++) {
			uint32_t f, k;
			if (i < 20)
				f = (b & c) | (~b & d), k = 0x5A827999;
			else if (i < 40)
				f = b ^ c ^ d, k = 0x6ED9EBA1;
			else if (i < 60)
				f = (b & c) | (b & d) | (c & d), k = 0x8F1BBCDC;
			else
				f = b ^ c ^ d, k = 0xCA62C1D6;
			uint32_t t = rol(a, 5) + f + e + k + w[i];
			e = d;
			d = c;
			c = rol(b, 30);
			b = a;
			a = t;
		}
		h[0] += a;
		h[1] += b;
		h[2] += c;
		h[3] += d;
		h[4] += e;
	}
	free(m);
	for (int i = 0; i < 5; i++)
		snprintf(out + 8 * i, 9, "%08x", h[i]);
}

/* ---------- config ---------- */

static char cfg_dir[900], cfg_path[1024], hist_path[1024], cookie_path[1024];
static char browser[256] = BROWSER; /* anything yt-dlp's --cookies-from-browser takes */

/* yt-dlp format selectors, passed to mpv as ytdl-format */
static const struct {
	const char *name, *fmt;
} quals[] = {
	{"best", "bv*+ba/b"},
	{"1080p", "bv*[height<=1080]+ba/b[height<=1080]/b"},
	{"720p", "bv*[height<=720]+ba/b[height<=720]/b"},
	{"480p", "bv*[height<=480]+ba/b[height<=480]/b"},
	{"360p", "bv*[height<=360]+ba/b[height<=360]/b"},
	{"audio only", "ba/b"},
};
#define NQUAL ((int)(sizeof quals / sizeof *quals))
static int quality;
static const char *ytapi = ORIGIN "/youtubei/v1";

static void cfg_save(void)
{
	mkdir(cfg_dir, 0700);
	int fd = open(cfg_path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
	if (fd < 0)
		die("cannot write %s: %s", cfg_path, strerror(errno));
	dprintf(fd, "browser=%s\nquality=%d\n", browser, quality);
	close(fd);
}

static void cfg_load(void)
{
	const char *x = getenv("XDG_CONFIG_HOME"), *h = getenv("HOME");
	char base[800];
	if (x && *x)
		snprintf(base, sizeof base, "%s", x);
	else
		snprintf(base, sizeof base, "%s/.config", h ? h : ".");
	mkdir(base, 0700);
	snprintf(cfg_dir, sizeof cfg_dir, "%s/ytv", base);
	snprintf(cfg_path, sizeof cfg_path, "%s/config", cfg_dir);
	snprintf(hist_path, sizeof hist_path, "%s/history", cfg_dir);
	snprintf(cookie_path, sizeof cookie_path, "%s/cookies", cfg_dir);

	FILE *f = fopen(cfg_path, "r");
	char line[1024];
	while (f && fgets(line, sizeof line, f)) {
		line[strcspn(line, "\r\n")] = 0;
		if (!strncmp(line, "browser=", 8) && line[8])
			snprintf(browser, sizeof browser, "%s", line + 8);
		else if (!strncmp(line, "quality=", 8))
			quality = atoi(line + 8);
	}
	if (f)
		fclose(f);
	if (quality < 0 || quality >= NQUAL)
		quality = 0;
}

/* ---------- local watch history: "<video id> <seconds>", -1 for watched ---------- */

typedef struct {
	char id[16];
	int pos;
} Hist;
static Hist *hist;
static int nhist, hcap;

static void hist_load(void)
{
	FILE *f = fopen(hist_path, "r");
	char id[16];
	int pos;
	while (f && fscanf(f, "%15s %d", id, &pos) == 2) {
		if (nhist == hcap) {
			hcap = hcap ? hcap * 2 : 256;
			if (!(hist = realloc(hist, sizeof *hist * (size_t)hcap)))
				die("out of memory");
		}
		memcpy(hist[nhist].id, id, sizeof id);
		hist[nhist++].pos = pos;
	}
	if (f)
		fclose(f);
}

static Hist *hist_find(const char *id)
{
	for (int i = 0; i < nhist; i++)
		if (!strcmp(hist[i].id, id))
			return &hist[i];
	return NULL;
}

/* pos 0 forgets the video */
static void hist_set(const char *id, int pos)
{
	char tmp[1100];
	Hist *h = hist_find(id);
	if (!h && pos) {
		if (nhist == hcap) {
			hcap = hcap ? hcap * 2 : 256;
			if (!(hist = realloc(hist, sizeof *hist * (size_t)hcap)))
				die("out of memory");
		}
		h = &hist[nhist++];
		snprintf(h->id, sizeof h->id, "%s", id);
	}
	if (!h)
		return;
	if (pos)
		h->pos = pos;
	else
		*h = hist[--nhist];

	mkdir(cfg_dir, 0700);
	snprintf(tmp, sizeof tmp, "%s.tmp", hist_path);
	FILE *f = fopen(tmp, "w");
	if (!f)
		return;
	for (int i = 0; i < nhist; i++)
		fprintf(f, "%s %d\n", hist[i].id, hist[i].pos);
	if (fclose(f) == 0)
		rename(tmp, hist_path);
}

/* ---------- HTTP ---------- */

static CURL *curl;
static Buf resp;
static char msg[512]; /* one-shot message for the footer */
static Buf cookies;   /* "Cookie: ..." for youtube.com */
static char sapisid[256], sapisid1p[256], sapisid3p[256];

static size_t on_data(char *d, size_t sz, size_t nm, void *u)
{
	bput(u, d, sz * nm);
	return sz * nm;
}

/* append " <scheme> <time>_<sha1 of "<time> <sid> <origin>">", how the web client signs its requests */
static void sidhash(Buf *b, const char *scheme, const char *sid, time_t now)
{
	char in[512], hex[41];
	if (!sid[0])
		return;
	snprintf(in, sizeof in, "%ld %s " ORIGIN, (long)now, sid);
	sha1_hex(in, hex);
	bfmt(b, " %s %ld_%s", scheme, (long)now, hex);
}

static struct curl_slist *headers(void)
{
	static const char *fixed[] = {
		"Content-Type: application/json",
		"User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) "
		"Version/26.0 Safari/605.1.15",
		"Origin: " ORIGIN,
		"X-Origin: " ORIGIN,
		"X-Youtube-Client-Name: 1",
		"X-Youtube-Client-Version: " CLIENT_VERSION,
		"X-Goog-AuthUser: 0",
	};
	struct curl_slist *h = NULL;
	Buf auth = {0};
	time_t now = time(NULL);

	for (size_t i = 0; i < sizeof fixed / sizeof *fixed; i++)
		h = curl_slist_append(h, fixed[i]);
	bputs(&auth, "Authorization:");
	sidhash(&auth, "SAPISIDHASH", sapisid[0] ? sapisid : sapisid3p, now);
	sidhash(&auth, "SAPISID1PHASH", sapisid1p, now);
	sidhash(&auth, "SAPISID3PHASH", sapisid3p, now);
	h = curl_slist_append(h, auth.p);
	h = curl_slist_append(h, cookies.p);
	free(auth.p);
	return h;
}

/* POST a JSON body. Returns the HTTP status, or -1 on transport failure (msg is set). */
static long http(const char *url, const char *post, Buf *out, long timeout)
{
	char err[CURL_ERROR_SIZE] = "";
	struct curl_slist *h = headers();
	long code = -1;

	curl_easy_reset(curl); /* keeps the connection cache */
	out->n = 0;
	bput(out, "", 0);
	curl_easy_setopt(curl, CURLOPT_URL, url);
	curl_easy_setopt(curl, CURLOPT_HTTPHEADER, h);
	curl_easy_setopt(curl, CURLOPT_POSTFIELDS, post);
	curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, on_data);
	curl_easy_setopt(curl, CURLOPT_WRITEDATA, out);
	curl_easy_setopt(curl, CURLOPT_TIMEOUT, timeout);
	curl_easy_setopt(curl, CURLOPT_CONNECTTIMEOUT, 8L);
	curl_easy_setopt(curl, CURLOPT_NOSIGNAL, 1L);
	curl_easy_setopt(curl, CURLOPT_ACCEPT_ENCODING, "");
	curl_easy_setopt(curl, CURLOPT_ERRORBUFFER, err);
	CURLcode rc = curl_easy_perform(curl);
	if (rc == CURLE_OK)
		curl_easy_getinfo(curl, CURLINFO_RESPONSE_CODE, &code);
	else
		snprintf(msg, sizeof msg, "Network error: %s", err[0] ? err : curl_easy_strerror(rc));
	curl_slist_free_all(h);
	return code;
}

/* Put YouTube's explanation of a failed request in msg. */
static void api_error(long st, char *body)
{
	Arena a = {0};
	const char *text = jstrv(jget(jparse(body, &a), "error"), "message");

	if (st == 401 || st == 403)
		snprintf(msg, sizeof msg, "YouTube didn't take the sign-in from %s; sign in there again and restart ytv",
		         browser);
	else if (st >= 0)
		snprintf(msg, sizeof msg, "YouTube: %s (HTTP %ld)", text ? text : "request failed", st);
	afree(&a);
}

/* POST to the web client's API; fields are the request's members besides its context. NULL on failure (msg is set). */
static JVal *yt(const char *endpoint, const char *fields, Arena *a)
{
	char url[256];
	Buf body = {0};

	snprintf(url, sizeof url, "%s/%s?prettyPrint=false", ytapi, endpoint);
	bfmt(&body, "{\"context\":{\"client\":{\"clientName\":\"WEB\",\"clientVersion\":\"" CLIENT_VERSION
	            "\",\"hl\":\"en\"}},%s}",
	     fields);
	long st = http(url, body.p, &resp, 30);
	free(body.p);
	if (st != 200) {
		api_error(st, resp.p);
		return NULL;
	}
	JVal *r = jparse(resp.p, a);
	if (!r)
		snprintf(msg, sizeof msg, "Unexpected response from YouTube");
	else if (jnum(jget(jget(r, "responseContext"), "mainAppWebResponseContext"), "loggedOut"))
		snprintf(msg, sizeof msg, "YouTube says you're signed out; sign in with %s and restart ytv", browser);
	return r;
}

/* ---------- account ---------- */

static void forget_cookies(void)
{
	unlink(cookie_path);
}

/*
 * Have yt-dlp copy the browser's cookies to cookie_path, where mpv's yt-dlp
 * finds them too, and keep youtube.com's for our requests. Run without a URL,
 * yt-dlp saves the jar on its way out with a usage error and never touches
 * the network.
 */
static void load_cookies(void)
{
	int p[2], ws = 0, signed_in = 0;
	Buf out = {0};
	char buf[4096], line[8192];
	ssize_t n;

	mkdir(cfg_dir, 0700);
	unlink(cookie_path);
	if (pipe(p) < 0)
		die("pipe: %s", strerror(errno));
	pid_t pid = fork();
	if (pid < 0)
		die("fork: %s", strerror(errno));
	if (pid == 0) {
		int nul = open("/dev/null", O_RDWR);
		dup2(nul, 0);
		dup2(p[1], 1);
		dup2(p[1], 2);
		close(p[0]);
		umask(077);
		execlp("yt-dlp", "yt-dlp", "--ignore-config", "--cookies-from-browser", browser, "--cookies", cookie_path,
		       (char *)NULL);
		_exit(127);
	}
	close(p[1]);
	while ((n = read(p[0], buf, sizeof buf)) > 0 || (n < 0 && errno == EINTR))
		if (n > 0)
			bput(&out, buf, (size_t)n);
	close(p[0]);
	waitpid(pid, &ws, 0);
	atexit(forget_cookies);
	if (WIFEXITED(ws) && WEXITSTATUS(ws) == 127)
		die("needs yt-dlp on PATH");

	/* Netscape format: domain, subdomains, path, secure, expiry, name, value */
	FILE *f = fopen(cookie_path, "r");
	time_t now = time(NULL);
	cookies.n = 0;
	bputs(&cookies, "Cookie:");
	while (f && fgets(line, sizeof line, f)) {
		char *fld[7], *s = line;
		int k = 0;
		line[strcspn(line, "\r\n")] = 0;
		if (!strncmp(s, "#HttpOnly_", 10))
			s += 10;
		else if (*s == '#')
			continue;
		for (; k < 7 && s; k++)
			fld[k] = strsep(&s, "\t");
		if (k < 7 || (strcmp(fld[0], ".youtube.com") && strcmp(fld[0], "youtube.com") &&
		              strcmp(fld[0], "www.youtube.com")))
			continue;
		if (atoll(fld[4]) && atoll(fld[4]) < now)
			continue;
		bfmt(&cookies, "%s %s=%s", cookies.n > 7 ? ";" : "", fld[5], fld[6]);
		if (!strcmp(fld[5], "SAPISID"))
			snprintf(sapisid, sizeof sapisid, "%s", fld[6]);
		else if (!strcmp(fld[5], "__Secure-1PAPISID"))
			snprintf(sapisid1p, sizeof sapisid1p, "%s", fld[6]);
		else if (!strcmp(fld[5], "__Secure-3PAPISID"))
			snprintf(sapisid3p, sizeof sapisid3p, "%s", fld[6]);
		else if (!strcmp(fld[5], "LOGIN_INFO"))
			signed_in = 1;
	}
	if (f)
		fclose(f);
	if (signed_in && (sapisid[0] || sapisid3p[0])) {
		free(out.p);
		return;
	}

	/* the first complaint besides the missing URL */
	char *err = NULL;
	for (char *l = out.p, *e; l && *l && !err; l = e + !!*e) {
		e = l + strcspn(l, "\r\n");
		if (!strncasecmp(l, "ERROR: ", 7) && !strstr(l, "at least one URL"))
			err = l;
		else if (!strncmp(l, "yt-dlp: error: ", 15) && !strstr(l, "at least one URL"))
			err = l + 8;
		if (err)
			*e = 0;
	}
	if (err && strstr(err, "Operation not permitted") && !strncasecmp(browser, "safari", 6))
		die("cannot read Safari's cookies; give your terminal Full Disk Access in System Settings \xe2\x80\xba "
		    "Privacy & Security, or use another browser: ytv firefox");
	if (err)
		die("cannot read cookies from %s (%s)", browser, err + 7);
	die("not signed in to YouTube in %s; sign in there, or use another browser: ytv firefox", browser);
}

static void open_url(const char *url)
{
	pid_t pid = fork();
	if (pid == 0) {
		int nul = open("/dev/null", O_RDWR);
		dup2(nul, 0);
		dup2(nul, 1);
		dup2(nul, 2);
		execlp(OPENER, OPENER, url, (char *)NULL);
		_exit(127);
	}
	if (pid > 0)
		waitpid(pid, NULL, 0);
}

/* ---------- views ---------- */

enum { IT_DIR, IT_VIDEO };
enum { LIVE_NO, LIVE_NOW, LIVE_SOON };
typedef struct {
	char *title, *key; /* key: what to list (dir) or video id */
	char *chan, *chanid;
	time_t when;
	int kind, count;
	int dur, off, live; /* seconds */
	int watched;
} Item;

typedef struct View {
	struct View *parent;
	Arena a;
	char *title, *spec;
	Item *items;
	int n, cap;
	int *vis, nvis; /* indices of items matching the filter */
	int sel, top;
	int chans; /* show channel names */
	char filter[64];
} View;

static View *view;
static int input; /* what typed keys go to */
enum { IN_NONE, IN_FILTER, IN_SEARCH };
static char query[128];

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
	for (int i = 0; i < v->n; i++) {
		Item *it = &v->items[i];
		if (!v->filter[0] || strcasestr(it->title, v->filter) || (it->chan && strcasestr(it->chan, v->filter)))
			v->vis[v->nvis++] = i;
	}
	v->sel = v->top = 0;
}

static View *new_view(const char *title, const char *spec)
{
	View *v = calloc(1, sizeof *v);
	if (!v)
		die("out of memory");
	v->title = astrdup(&v->a, title);
	v->spec = adup(&v->a, spec);
	return v;
}

static void free_view(View *v)
{
	afree(&v->a);
	free(v->items);
	free(v->vis);
	free(v);
}

/* "3 days ago", "Streamed 2 weeks ago": roughly when */
static time_t ago(const char *s)
{
	static const struct {
		const char *unit;
		long sec;
	} units[] = {{"second", 1},      {"minute", 60},          {"hour", 3600},           {"day", 86400},
	             {"week", 7 * 86400}, {"month", 30 * 86400}, {"year", 365 * 86400}};
	if (!s || !strstr(s, " ago"))
		return 0;
	for (const char *p = s; *p; p++) {
		char *e;
		if (*p < '0' || *p > '9' || (p > s && p[-1] >= '0' && p[-1] <= '9'))
			continue;
		long n = strtol(p, &e, 10);
		e += strspn(e, " ");
		for (size_t i = 0; i < sizeof units / sizeof *units; i++)
			if (!strncmp(e, units[i].unit, strlen(units[i].unit)))
				return time(NULL) - n * units[i].sec;
	}
	return 0;
}

/* "1:02:03" in seconds, 0 if it isn't a clock */
static int clock_secs(const char *s)
{
	int t = 0, n = 0;
	if (!s || !strchr(s, ':') || strspn(s, "0123456789:") != strlen(s))
		return 0;
	for (; *s; s++)
		if (*s == ':') {
			t = (t + n) * 60;
			n = 0;
		} else
			n = n * 10 + *s - '0';
	return t + n;
}

/* NULL if the view has it already */
static Item *add_video_item(View *v, const char *id, const char *title, const char *chan, const char *chanid)
{
	if (!id || !title || !strcmp(title, "[Private video]") || !strcmp(title, "[Deleted video]"))
		return NULL;
	for (int i = 0; i < v->n; i++)
		if (v->items[i].kind == IT_VIDEO && !strcmp(v->items[i].key, id))
			return NULL;
	Item *it = push_item(v);
	it->kind = IT_VIDEO;
	it->key = astrdup(&v->a, id);
	it->title = astrdup(&v->a, title);
	it->chan = adup(&v->a, chan);
	it->chanid = adup(&v->a, chanid);
	Hist *h = hist_find(id);
	if (h && h->pos < 0)
		it->watched = 1;
	else if (h)
		it->off = h->pos;
	return it;
}

/* channels open on their uploads playlist, which is UU + the id after UC */
static void add_channel(View *v, const char *cid, const char *title)
{
	char key[128];
	if (!cid || !title || strncmp(cid, "UC", 2))
		return;
	snprintf(key, sizeof key, "pl:UU%s", cid + 2);
	Item *it = push_item(v);
	it->kind = IT_DIR;
	it->title = astrdup(&v->a, title);
	it->key = astrdup(&v->a, key);
	it->chanid = astrdup(&v->a, cid);
}

static void add_playlist(View *v, const char *id, const char *title, int count)
{
	char key[128];
	if (!id || !title || !strncmp(id, "RD", 2)) /* mixes aren't lists */
		return;
	snprintf(key, sizeof key, "pl:%s", id);
	Item *it = push_item(v);
	it->kind = IT_DIR;
	it->title = astrdup(&v->a, title);
	it->key = astrdup(&v->a, key);
	it->count = count;
}

/* videoRenderer and its relatives in search, playlists and older layouts */
static void add_renderer(View *v, JVal *m)
{
	char title[512], t[256];
	JVal *by = jget(m, "ownerText") ? jget(m, "ownerText") : jget(m, "shortBylineText");
	JVal *run = jget(by, "runs") ? jget(by, "runs")->child : NULL;
	JVal *ov = jget(m, "thumbnailOverlays"), *badges = jget(m, "badges");

	if (jget(m, "isPlayable") && !jnum(m, "isPlayable"))
		return;
	Item *it = add_video_item(v, jstrv(m, "videoId"), jtext(jget(m, "title"), title, sizeof title),
	                          jstrv(run, "text"), jfindstr(run, "browseId"));
	if (!it)
		return;
	it->dur = jstrv(m, "lengthSeconds") ? atoi(jstrv(m, "lengthSeconds"))
	                                    : clock_secs(jtext(jget(m, "lengthText"), t, sizeof t));
	it->when = ago(jtext(jget(m, "publishedTimeText"), t, sizeof t));
	if (!it->when)
		it->when = ago(jtext(jget(m, "videoInfo"), t, sizeof t));
	for (JVal *o = ov ? ov->child : NULL; o; o = o->next) {
		const char *st = jstrv(jget(o, "thumbnailOverlayTimeStatusRenderer"), "style");
		if (st && !strcmp(st, "LIVE"))
			it->live = LIVE_NOW;
		else if (st && !strcmp(st, "UPCOMING"))
			it->live = LIVE_SOON;
	}
	for (JVal *b = badges ? badges->child : NULL; b; b = b->next) {
		const char *st = jstrv(jget(b, "metadataBadgeRenderer"), "style");
		if (st && !strcmp(st, "BADGE_STYLE_TYPE_LIVE_NOW"))
			it->live = LIVE_NOW;
	}
	if (jget(m, "upcomingEventData"))
		it->live = LIVE_SOON;
}

/* the badges on a lockup's thumbnail: a duration, LIVE, or "12 videos" */
static void lockup_badges(JVal *o, Item *it)
{
	for (JVal *c = o && (o->t == J_OBJ || o->t == J_ARR) ? o->child : NULL; c; c = c->next) {
		const char *t = c->key && !strcmp(c->key, "thumbnailBadgeViewModel") ? jstrv(c, "text") : NULL;
		if (!t)
			lockup_badges(c, it);
		else if (!strcmp(t, "LIVE"))
			it->live = LIVE_NOW;
		else if (!strcmp(t, "UPCOMING"))
			it->live = LIVE_SOON;
		else if (clock_secs(t))
			it->dur = clock_secs(t);
		else if (*t >= '0' && *t <= '9') {
			for (it->count = 0; (*t >= '0' && *t <= '9') || *t == ','; t++)
				if (*t != ',')
					it->count = it->count * 10 + *t - '0';
		}
	}
}

/* lockupViewModel: what the current layouts use for videos and playlists alike */
static void add_lockup(View *v, JVal *m)
{
	JVal *md = jget(jget(m, "metadata"), "lockupMetadataViewModel");
	JVal *rows = jget(jget(jget(md, "metadata"), "contentMetadataViewModel"), "metadataRows");
	const char *id = jstrv(m, "contentId"), *type = jstrv(m, "contentType"), *title = jstrv(jget(md, "title"), "content");
	const char *chan = NULL, *chanid = NULL;
	time_t when = 0;
	int soon = 0;
	Item tmp = {0}, *it;

	if (!id || !type)
		return;
	if (strcmp(type, "LOCKUP_CONTENT_TYPE_VIDEO")) {
		if (!strncmp(id, "UC", 2))
			add_channel(v, id, title);
		else {
			lockup_badges(jget(m, "contentImage"), &tmp);
			add_playlist(v, id, title, tmp.count);
		}
		return;
	}
	/* rows of parts: the channel (linked to it), views, age, "Scheduled for ..." */
	for (JVal *r = rows ? rows->child : NULL; r; r = r->next) {
		JVal *parts = jget(r, "metadataParts");
		for (JVal *p = parts ? parts->child : NULL; p; p = p->next) {
			JVal *text = jget(p, "text");
			const char *s = jstrv(text, "content"), *cid = jfindstr(jget(text, "commandRuns"), "browseId");
			if (!s)
				continue;
			if (!chan && cid && !strncmp(cid, "UC", 2)) {
				chan = s;
				chanid = cid;
			} else if (!when)
				when = ago(s);
			if (!strncmp(s, "Scheduled for", 13) || !strncmp(s, "Premieres ", 10))
				soon = 1;
		}
	}
	if (!(it = add_video_item(v, id, title, chan, chanid)))
		return;
	it->when = when;
	lockup_badges(jget(m, "contentImage"), it);
	if (soon)
		it->live = LIVE_SOON;
}

/* Collect the items anywhere in a response, and the token for the next page. */
static void scan(View *v, JVal *o, char *tok, size_t ntok)
{
	for (JVal *c = o && (o->t == J_OBJ || o->t == J_ARR) ? o->child : NULL; c; c = c->next) {
		const char *k = c->key ? c->key : "";
		char t[512];
		if (!strcmp(k, "videoRenderer") || !strcmp(k, "gridVideoRenderer") || !strcmp(k, "playlistVideoRenderer"))
			add_renderer(v, c);
		else if (!strcmp(k, "lockupViewModel"))
			add_lockup(v, c);
		else if (!strcmp(k, "channelRenderer") || !strcmp(k, "gridChannelRenderer"))
			add_channel(v, jstrv(c, "channelId"), jtext(jget(c, "title"), t, sizeof t));
		else if (!strcmp(k, "playlistRenderer") || !strcmp(k, "gridPlaylistRenderer"))
			add_playlist(v, jstrv(c, "playlistId"), jtext(jget(c, "title"), t, sizeof t),
			             atoi(jstrv(c, "videoCount") ? jstrv(c, "videoCount") : "0"));
		else if (!strcmp(k, "continuationItemRenderer") || !strcmp(k, "continuationItemViewModel")) {
			if (!tok[0] && jfindstr(c, "token"))
				snprintf(tok, ntok, "%s", jfindstr(c, "token"));
		} else
			scan(v, c, tok, ntok);
	}
}

/* Fetch an endpoint's pages until there are max items; fields pick what (a browseId, a query). */
static int yt_pages(View *v, const char *endpoint, const char *fields, int max)
{
	char tok[4096] = "", cont[4200];
	int pages = 0;
	do {
		Arena a = {0};
		int had = v->n;
		snprintf(cont, sizeof cont, "\"continuation\":\"%s\"", tok);
		JVal *r = yt(endpoint, pages++ ? cont : fields, &a);
		if (!r) {
			afree(&a);
			return pages > 1; /* keep what came */
		}
		tok[0] = 0;
		if (pages == 1)
			scan(v, jget(r, "contents"), tok, sizeof tok);
		scan(v, jget(r, "onResponseReceivedActions"), tok, sizeof tok);
		scan(v, jget(r, "onResponseReceivedCommands"), tok, sizeof tok);
		scan(v, jget(r, "onResponseReceivedEndpoints"), tok, sizeof tok);
		afree(&a);
		if (v->n == had)
			break;
		if (tok[0])
			status("Loading... %d", v->n);
	} while (tok[0] && v->n < max);
	return 1;
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
	unlink(cookie_path);
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


static void status(const char *fmt, ...)
{
	char s[512];
	va_list ap;
	va_start(ap, fmt);
	vsnprintf(s, sizeof s, fmt, ap);
	va_end(ap);
	if (tui_on)
		dprintf(1, "\x1b[%d;1H %s\x1b[K", rows, s);
}

/* ---------- loading ---------- */

static int by_title(const void *a, const void *b)
{
	return strcasecmp(((const Item *)a)->title, ((const Item *)b)->title);
}

/*
 * spec is one of: feed, subs, browse:<browse id>, pl:<playlist id>, search:<query>
 */
static View *load_view(const char *spec, const char *title)
{
	View *v = new_view(title, spec);
	Buf q = {0};
	int ok;

	status("Loading...");
	if (!strcmp(spec, "feed")) {
		v->chans = 1;
		ok = yt_pages(v, "browse", "\"browseId\":\"FEsubscriptions\"", FEED_MAX);
	} else if (!strcmp(spec, "subs")) {
		ok = yt_pages(v, "browse", "\"browseId\":\"FEchannels\"", 1 << 20);
		qsort(v->items, (size_t)v->n, sizeof *v->items, by_title);
	} else if (!strncmp(spec, "browse:", 7)) {
		v->chans = 1;
		bputs(&q, "\"browseId\":\"");
		bjson(&q, spec + 7);
		bputs(&q, "\"");
		ok = yt_pages(v, "browse", q.p, PAGEMAX);
	} else if (!strncmp(spec, "pl:", 3)) {
		v->chans = strncmp(spec + 3, "UU", 2) != 0; /* not a channel's uploads */
		bputs(&q, "\"browseId\":\"VL");
		bjson(&q, spec + 3);
		bputs(&q, "\"");
		ok = yt_pages(v, "browse", q.p, PAGEMAX);
	} else if (!strncmp(spec, "search:", 7)) {
		v->chans = 1;
		bputs(&q, "\"params\":\"EgIQAQ%3D%3D\",\"query\":\""); /* videos only */
		bjson(&q, spec + 7);
		bputs(&q, "\"");
		ok = yt_pages(v, "search", q.p, 50);
	} else
		ok = 0;
	free(q.p);
	if (!ok) {
		free_view(v);
		return NULL;
	}
	if (resp.cap > (1 << 20)) { /* don't hold on to a large response buffer */
		free(resp.p);
		resp = (Buf){0};
	}
	refilter(v);
	return v;
}

/* ---------- drawing ---------- */

static void fmt_clock(char *out, size_t n, int sec)
{
	if (sec >= 3600)
		snprintf(out, n, "%d:%02d:%02d", sec / 3600, sec % 3600 / 60, sec % 60);
	else
		snprintf(out, n, "%d:%02d", sec / 60, sec % 60);
}

static void fmt_age(char *out, size_t n, time_t when)
{
	long d = (long)(time(NULL) - when);
	if (d < 3600)
		snprintf(out, n, "%ldm ago", d > 60 ? d / 60 : 1);
	else if (d < 86400)
		snprintf(out, n, "%ldh ago", d / 3600);
	else if (d < 86400 * 30)
		snprintf(out, n, "%ldd ago", d / 86400);
	else if (d < 86400 * 365)
		snprintf(out, n, "%ldmo ago", d / (86400 * 30));
	else
		snprintf(out, n, "%ldy ago", d / (86400 * 365));
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
	if (input == IN_SEARCH)
		bfmt(&o, "   search: %s_", query);
	else if (input == IN_FILTER || v->filter[0])
		bfmt(&o, "   /%s%s", v->filter, input == IN_FILTER ? "_" : "");
	bputs(&o, "\x1b[K\r\n");
	for (int i = 0; i < body; i++) {
		int k = v->top + i;
		if (k < v->nvis) {
			Item *it = &v->items[v->vis[k]];
			char d[32], e[32];
			const char *mark = " ", *sep = "   ";
			if (it->kind == IT_VIDEO)
				mark = it->live ? "\xe2\x97\x8b" : it->off > 0 ? "\xe2\x97\x90" : it->watched ? " " : "\xe2\x97\x8f";
			if (k == v->sel)
				bputs(&o, "\x1b[7m");
			bfmt(&o, " %s %s\x1b[2m", mark, it->title);
			if (it->kind == IT_VIDEO) {
				if (v->chans && it->chan) {
					bfmt(&o, "%s%s", sep, it->chan);
					sep = " \xc2\xb7 ";
				}
				if (it->live == LIVE_NOW)
					bfmt(&o, "%slive", sep);
				else if (it->live == LIVE_SOON)
					bfmt(&o, "%supcoming", sep);
				else if (it->dur) {
					fmt_clock(d, sizeof d, it->dur);
					if (it->off > 0) {
						fmt_clock(e, sizeof e, it->off);
						bfmt(&o, "%s%s of %s", sep, e, d);
					} else
						bfmt(&o, "%s%s", sep, d);
				}
				if (it->when) {
					fmt_age(d, sizeof d, it->when);
					bfmt(&o, " \xc2\xb7 %s", d);
				}
			} else if (it->count)
				bfmt(&o, "%s%d video%s", sep, it->count, it->count == 1 ? "" : "s");
			bputs(&o, " \x1b[0m");
		} else if (i == 0)
			bputs(&o, "\x1b[2m   (nothing here)\x1b[0m");
		bputs(&o, "\x1b[K\r\n");
	}
	if (msg[0])
		bfmt(&o, " %s", msg);
	else
		bfmt(&o,
		     "\x1b[2m %d/%d    enter open   \xe2\x86\x90 back   / filter   s search   c channel   r reload"
		     "   v quality: %s   b from start   w watched   o browser   q quit\x1b[0m",
		     v->nvis ? v->sel + 1 : 0, v->nvis, quals[quality].name);
	bputs(&o, "\x1b[K");
	msg[0] = 0;
	if (write(1, o.p, o.n) < 0) {
	}
}

/* ---------- playback ---------- */

static void tell(int fd, const char *s)
{
	if (write(fd, s, strlen(s)) < 0) {
	}
}

/* Run mpv on the video (it resolves YouTube URLs with yt-dlp) and wait for it to exit. */
static void play(Item *it, int resume)
{
	int sv[2], started = 0, failed = 0;
	double pos = resume && !it->live ? it->off : 0;
	Buf c = {0};
	char line[8192], jar[sizeof cookie_path + 40];
	size_t ln = 0;

	if (it->live == LIVE_SOON) {
		snprintf(msg, sizeof msg, "That hasn't started yet");
		return;
	}
	snprintf(jar, sizeof jar, "--ytdl-raw-options-append=cookies=%s", cookie_path);
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
		execlp("mpv", "mpv", "--idle=once", "--force-window=immediate", "--no-terminal", "--hwdec=auto-safe",
		       "--input-ipc-client=fd://3", jar, (char *)NULL);
		_exit(127);
	}
	close(sv[1]);

	bputs(&c, "{\"command\":[\"set_property\",\"options/force-media-title\",\"");
	bjson(&c, it->title);
	bputs(&c, "\"]}\n{\"command\":[\"set_property\",\"options/ytdl-format\",\"");
	bjson(&c, quals[quality].fmt);
	bputs(&c, "\"]}\n");
	if (pos > 0)
		bfmt(&c, "{\"command\":[\"set_property\",\"options/start\",\"%d\"]}\n", (int)pos);
	bputs(&c, "{\"command\":[\"show-text\",\"Loading...\",600000]}\n");
	bfmt(&c, "{\"command\":[\"loadfile\",\"https://www.youtube.com/watch?v=%s\"]}\n", it->key);
	tell(sv[0], c.p);
	free(c.p);

	status("Playing %s (%s) \xe2\x80\x94 quit mpv to come back", it->title, quals[quality].name);

	struct pollfd pf = {sv[0], POLLIN, 0};
	time_t next = time(NULL) + TICK;
	for (;;) {
		time_t now = time(NULL);
		if (now >= next) {
			tell(sv[0], "{\"command\":[\"get_property\",\"time-pos\"],\"request_id\":1}\n");
			if (!it->dur)
				tell(sv[0], "{\"command\":[\"get_property\",\"duration\"],\"request_id\":2}\n");
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
			if (ev && !strcmp(ev, "playback-restart"))
				tell(sv[0], "{\"command\":[\"show-text\",\"\",1]}\n");
			if (ev && why && !strcmp(ev, "end-file")) {
				if (!strcmp(why, "eof") && it->dur) {
					pos = it->dur; /* played to the end */
					started = 1;
				} else if (!strcmp(why, "error"))
					failed = 1;
			}
			int id = (int)jnum(j, "request_id");
			if (id && err && !strcmp(err, "success")) {
				if (id == 1) {
					pos = jnum(j, "data");
					started = 1;
				} else if (id == 2)
					it->dur = (int)jnum(j, "data");
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
	else if (failed && !started)
		snprintf(msg, sizeof msg, "mpv could not play it \xe2\x80\x94 is yt-dlp installed and up to date?");
	if (started && it->live == LIVE_NO) {
		if (it->dur && pos >= it->dur * 0.9) {
			it->watched = 1;
			it->off = 0;
			hist_set(it->key, -1);
		} else if (pos >= 10) {
			it->off = (int)pos;
			hist_set(it->key, it->off);
		}
	}
	tcflush(0, TCIFLUSH);
}

/* ---------- main ---------- */

static Item *selected(void)
{
	return view->nvis ? &view->items[view->vis[view->sel]] : NULL;
}

static void push_view(View *n)
{
	if (!n)
		return;
	n->parent = view;
	view = n;
	input = IN_NONE;
}

static void open_selected(int resume)
{
	Item *it = selected();
	if (!it)
		return;
	if (it->kind == IT_VIDEO)
		play(it, resume);
	else
		push_view(load_view(it->key, it->title));
}

static void open_channel(void)
{
	Item *it = selected();
	char spec[128];
	if (!it || !it->chanid || strncmp(it->chanid, "UC", 2))
		return;
	snprintf(spec, sizeof spec, "pl:UU%s", it->chanid + 2);
	push_view(load_view(spec, it->kind == IT_VIDEO && it->chan ? it->chan : it->title));
}

static void reload(void)
{
	if (!view->spec)
		return;
	View *n = load_view(view->spec, view->title);
	if (!n)
		return;
	n->parent = view->parent;
	snprintf(n->filter, sizeof n->filter, "%s", view->filter);
	free_view(view);
	view = n;
	if (n->filter[0])
		refilter(n);
}

static void go_back(void)
{
	if (!view->parent)
		return;
	View *p = view->parent;
	free_view(view);
	view = p;
	input = IN_NONE;
}

int main(int argc, char **argv)
{
	if (getenv("YTV_API")) /* alternate endpoint, for testing */
		ytapi = getenv("YTV_API");
	cfg_load();
	if (argc > 2 || (argc == 2 && (argv[1][0] == '-' || !argv[1][0]))) {
		fputs("usage: ytv [browser]\n", stderr);
		return 2;
	}
	if (argc == 2) {
		snprintf(browser, sizeof browser, "%s", argv[1]);
		cfg_save();
	}
	curl_global_init(CURL_GLOBAL_DEFAULT);
	if (!(curl = curl_easy_init()))
		die("cannot initialise libcurl");
	hist_load();
	load_cookies();

	static const char *root[][2] = {
		{"Subscriptions feed", "feed"},
		{"Subscriptions", "subs"},
		{"Playlists", "browse:FEplaylist_aggregation"},
		{"Watch later", "pl:WL"},
		{"Liked videos", "pl:LL"},
		{"History", "browse:FEhistory"},
	};
	view = new_view("ytv", NULL);
	for (size_t i = 0; i < sizeof root / sizeof *root; i++) {
		Item *it = push_item(view);
		it->kind = IT_DIR;
		it->title = (char *)root[i][0];
		it->key = (char *)root[i][1];
	}
	refilter(view);

	tui_init();
	for (;;) {
		draw();
		int k = readkey(), page = rows > 3 ? rows - 2 : 1;
		View *v = view;

		if (input) {
			char *buf = input == IN_FILTER ? v->filter : query;
			size_t cap = input == IN_FILTER ? sizeof v->filter : sizeof query, len = strlen(buf);
			if (k == '\r' || k == '\n') {
				int was = input;
				input = IN_NONE;
				if (was == IN_SEARCH && query[0]) {
					char spec[sizeof query + 8];
					snprintf(spec, sizeof spec, "search:%s", query);
					push_view(load_view(spec, query));
				}
				continue;
			}
			if (k == KEY_ESC) {
				buf[0] = 0;
				if (input == IN_FILTER)
					refilter(v);
				input = IN_NONE;
				continue;
			}
			if (k == 127 || k == 8) {
				if (!len)
					input = IN_NONE;
				else {
					do
						len--;
					while (len && ((unsigned char)buf[len] & 0xC0) == 0x80);
					buf[len] = 0;
					if (input == IN_FILTER)
						refilter(v);
				}
				continue;
			}
			if (k >= 32 && k < 256) {
				if (len + 1 < cap) {
					buf[len] = (char)k;
					buf[len + 1] = 0;
					if (input == IN_FILTER)
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
			if (selected() && selected()->kind == IT_VIDEO) {
				Item *it = selected();
				it->watched = !it->watched;
				it->off = 0;
				hist_set(it->key, it->watched ? -1 : 0);
			}
			break;
		case 'c':
			open_channel();
			break;
		case 'o':
			if (selected() && selected()->kind == IT_VIDEO) {
				char url[128];
				snprintf(url, sizeof url, "https://www.youtube.com/watch?v=%s", selected()->key);
				open_url(url);
			}
			break;
		case 'r':
			reload();
			break;
		case 's':
			query[0] = 0;
			input = IN_SEARCH;
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
			input = IN_FILTER;
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
