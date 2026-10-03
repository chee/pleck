CFLAGS ?= -Os -Wall -Wextra
PREFIX ?= /usr/local

pleck: pleck.c
	$(CC) $(CFLAGS) -o $@ pleck.c -lcurl

install: pleck
	install -d $(PREFIX)/bin
	install -m 755 pleck $(PREFIX)/bin/pleck

clean:
	rm -f pleck

.PHONY: install clean
