#DEBUG=-g
DEBUG=
SCHEME_H_DIR=..
CC=gcc
CFLAGS=-DUSE_DL=1 -I$(SCHEME_H_DIR)

oops.so : oops.c Makefile
	$(CC) -shared -Wall -fPIC $(CFLAGS) -o $@ $(DEBUG) oops.c
	strip oops.so

.PHONY : clean
clean:
	rm -f *.so
	rm -f *~
