# Build the extracted UVC parser as a C-ABI shared and static library.
#
# The copied kernel code uses a few GNU C idioms (void* arithmetic,
# __alignof__, statement forms), so we build as gnu11. -Wno-unused is needed
# because a couple of copied locals (e.g. `alts`) are only referenced inside
# the now-stubbed logging macros.

CC      ?= cc
CFLAGS  ?= -O2 -g
CFLAGS  += -std=gnu11 -fPIC -Wall -Wextra \
           -Wno-unused-variable -Wno-unused-parameter -Wno-unused-but-set-variable
LDFLAGS ?=

# ASan build is what the differential fuzzer links against: it turns the
# parser's out-of-bounds writes on the kzalloc'd block into hard failures.
ASAN_FLAGS = -fsanitize=address,undefined -fno-omit-frame-pointer

.PHONY: all clean asan

all: libuvcparse_c.so libuvcparse_c.a

uvc_parse.o: uvc_parse.c uvc_parse.h
	$(CC) $(CFLAGS) -c uvc_parse.c -o uvc_parse.o

libuvcparse_c.so: uvc_parse.o
	$(CC) $(CFLAGS) -shared uvc_parse.o -o libuvcparse_c.so $(LDFLAGS)

libuvcparse_c.a: uvc_parse.o
	$(AR) rcs libuvcparse_c.a uvc_parse.o

# Object + static archive with sanitizers, for the fuzzing harness.
asan: uvc_parse.c uvc_parse.h
	$(CC) $(CFLAGS) $(ASAN_FLAGS) -c uvc_parse.c -o uvc_parse.asan.o
	$(AR) rcs libuvcparse_c_asan.a uvc_parse.asan.o

clean:
	rm -f uvc_parse.o uvc_parse.asan.o libuvcparse_c.so libuvcparse_c.a libuvcparse_c_asan.a
