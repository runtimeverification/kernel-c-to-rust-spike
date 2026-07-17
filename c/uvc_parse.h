/* SPDX-License-Identifier: GPL-2.0 */
/*
 * Shared C ABI for the UVC format/frame descriptor parser spike.
 *
 * This header defines the entry point and the flat, pointer-free result
 * struct that BOTH the C extraction (c/) and the Rust reimplementation
 * (rust/) expose, so a single differential-fuzzing harness can drive both
 * and compare their outputs field-by-field.
 *
 * Nothing here is copied from the kernel; it is the spike's own comparison
 * surface. See uvc_parse.c for the byte-for-byte kernel logic.
 */
#ifndef UVC_PARSE_SPIKE_H
#define UVC_PARSE_SPIKE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Capacity of the flat result arrays. The internal parse allocates exactly
 * what the counting pass computes (that is where the memory-safety bugs
 * live); these caps only bound how much of the result we serialize out for
 * comparison. Both C and Rust clamp identically, so the differential test
 * stays valid. Chosen large enough that well-formed descriptors never clamp.
 */
#define UVC_MAX_FORMATS   64u
#define UVC_MAX_FRAMES    256u
#define UVC_MAX_INTERVALS 1024u

/* Flattened copy of the scalar fields the kernel writes into struct uvc_format. */
struct uvc_format_out {
	uint8_t  type;
	uint8_t  index;
	uint8_t  bpp;
	int32_t  colorspace;
	int32_t  xfer_func;
	int32_t  ycbcr_enc;
	uint32_t fcc;
	uint32_t flags;
	uint32_t nframes;
	int32_t  frame_base;   /* index into result.frames[] of this format's frames */
};

/* Flattened copy of the scalar fields the kernel writes into struct uvc_frame. */
struct uvc_frame_out {
	uint8_t  bFrameIndex;
	uint8_t  bmCapabilities;
	uint16_t wWidth;
	uint16_t wHeight;
	uint32_t dwMinBitRate;
	uint32_t dwMaxBitRate;
	uint32_t dwMaxVideoFrameBufferSize;
	uint8_t  bFrameIntervalType;
	uint32_t dwDefaultFrameInterval;
	int32_t  interval_base; /* index into result.intervals[] where dwFrameInterval points */
};

/*
 * Complete, comparable result of parsing one videostreaming format/frame
 * descriptor region. If C and Rust agree on every field of this struct for
 * a given input, they are behaviourally equivalent on that input.
 */
struct uvc_parse_result {
	int32_t  ret;             /* driving-loop return: #formats parsed, or negative errno */

	/* Sizing produced by the counting pass (the allocation the parse writes into). */
	uint32_t nformats_alloc;
	uint32_t nframes_alloc;
	uint32_t nintervals_alloc;

	/* How much of each array below is populated. */
	uint32_t nformats;
	uint32_t nframes;
	uint32_t nintervals;

	struct uvc_format_out formats[UVC_MAX_FORMATS];
	struct uvc_frame_out  frames[UVC_MAX_FRAMES];
	uint32_t              intervals[UVC_MAX_INTERVALS];
};

/*
 * Parse a UVC videostreaming class-specific descriptor region, starting at
 * the first FORMAT descriptor (i.e. after the VS INPUT/OUTPUT header).
 *
 *   buffer/buflen : the raw descriptor bytes (untrusted USB input)
 *   quirks        : the device quirk flags (dev->quirks), an input because
 *                   two branches of uvc_parse_format depend on it
 *   out           : caller-allocated, fully overwritten on every call
 *
 * Returns the driving loop's return value, also stored in out->ret.
 */
int32_t uvc_parse(const uint8_t *buffer, int32_t buflen, uint32_t quirks,
		  struct uvc_parse_result *out);

#ifdef __cplusplus
}
#endif

#endif /* UVC_PARSE_SPIKE_H */
