CFLAGS ?= -Os -Wall -Wextra
PREFIX ?= /usr/local

ytv: ytv.c
	$(CC) $(CFLAGS) -o $@ ytv.c -lcurl

install: ytv
	install -d $(PREFIX)/bin
	install -m 755 ytv $(PREFIX)/bin/ytv

clean:
	rm -f ytv

.PHONY: install clean
