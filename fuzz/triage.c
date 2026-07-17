// Triage driver: replay one fuzzer input file against the C parser and print
// the result (or let AddressSanitizer abort on an out-of-bounds access).
//
// Mirrors the harness input model: [4 bytes quirks LE][descriptor bytes],
// quirks masked to the bits the parser reads. Build two ways:
//
//   faithful + ASan:   gcc -fsanitize=address -I../c triage.c ../c/uvc_parse.c -o triage_c_asan
//   vulnerable + ASan: gcc -DSPIKE_VULN -fsanitize=address -I../c triage.c ../c/uvc_parse.c -o triage_c_vuln_asan
//
// (-DSPIKE_VULN reintroduces a CVE-2024-53104-class frame-count under-count in
// c/uvc_parse.c; it is a clearly-marked negative control, off by default.)

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include "uvc_parse.h"

#define QUIRK_MASK 0x00001a00u /* FORCE_Y8 | FORCE_BPP | RESTRICT_FRAME_RATE */

int main(int argc, char **argv)
{
	if (argc < 2) {
		fprintf(stderr, "usage: %s <input-file>\n", argv[0]);
		return 2;
	}
	FILE *f = fopen(argv[1], "rb");
	if (!f) { perror("fopen"); return 2; }
	static uint8_t data[1 << 20];
	size_t n = fread(data, 1, sizeof(data), f);
	fclose(f);

	uint32_t quirks = 0;
	const uint8_t *buf = data;
	int buflen = (int)n;
	if (n >= 4) {
		quirks = ((uint32_t)data[0] | ((uint32_t)data[1] << 8) |
			  ((uint32_t)data[2] << 16) | ((uint32_t)data[3] << 24)) & QUIRK_MASK;
		buf = data + 4;
		buflen = (int)n - 4;
	}

	struct uvc_parse_result r;
	int32_t ret = uvc_parse(buf, buflen, quirks, &r);

	printf("C: ret=%d nformats=%u nframes=%u nintervals=%u alloc(f=%u fr=%u iv=%u)\n",
	       ret, r.nformats, r.nframes, r.nintervals,
	       r.nformats_alloc, r.nframes_alloc, r.nintervals_alloc);
	for (unsigned i = 0; i < r.nframes && i < 8; i++)
		printf("C:   frame[%u] %ux%u maxbuf=%u defint=%u\n", i,
		       r.frames[i].wWidth, r.frames[i].wHeight,
		       r.frames[i].dwMaxVideoFrameBufferSize,
		       r.frames[i].dwDefaultFrameInterval);
	return 0;
}
