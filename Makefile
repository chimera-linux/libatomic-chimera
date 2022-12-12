CC ?= cc
AR ?= ar
CFLAGS ?= -O2

PREFIX ?= /usr/local
LIBDIR ?= $(PREFIX)/lib

SOBASE = libatomic.so
SONAME = $(SOBASE).1
SHAREDLIB = $(SONAME).69.0
STATICLIB = libatomic.a

EXTRA_CFLAGS = -std=c99 -Wall -Wextra -fPIC

OBJS = atomic.o

all: $(SHAREDLIB) $(STATICLIB)

.c.o:
	$(CC) $(EXTRA_CFLAGS) $(CFLAGS) -c -o $@ $<

$(SHAREDLIB): $(OBJS)
	$(CC) $(OBJS) $(EXTRA_CFLAGS) $(CFLAGS) $(LDFLAGS) \
		-nolibc -shared -Wl,-soname,$(SONAME) -o $(SHAREDLIB)

$(STATICLIB): $(OBJS)
	$(AR) -rcs $(STATICLIB) $(OBJS)

# no tests
check:
	:

clean:
	rm -f $(OBJS) $(SHAREDLIB) $(STATICLIB)

install: $(SHAREDLIB) $(STATICLIB)
	install -d $(DESTDIR)$(LIBDIR)
	install -m 755 $(SHAREDLIB) $(DESTDIR)$(LIBDIR)
	install -m 755 $(STATICLIB) $(DESTDIR)$(LIBDIR)
	ln -sf $(SHAREDLIB) $(DESTDIR)$(LIBDIR)/$(SOBASE)
	ln -sf $(SHAREDLIB) $(DESTDIR)$(LIBDIR)/$(SONAME)
