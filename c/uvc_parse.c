// SPDX-License-Identifier: GPL-2.0
/*
 * Standalone extraction of the Linux kernel UVC videostreaming
 * format/frame descriptor parser, for the C-to-Rust hardening spike.
 *
 * The parsing functions (uvc_parse_frame, uvc_parse_format), the pure
 * colorspace/xfer/ycbcr helpers, and uvc_format_by_guid + its table are
 * copied BYTE-FOR-BYTE from kernel v7.2-rc2. The counting pass, the
 * allocation, and the format-driving loop are copied byte-for-byte from
 * uvc_parse_streaming into the uvc_parse() entry point below.
 *
 * Everything the kernel environment would normally provide (types, macros,
 * the slab allocator, logging, the v4l2 core, the USB descriptor structs)
 * is replaced by a thin stub layer. Every stub is marked // SPIKE-STUB.
 * No parsing arithmetic or control flow is changed.
 *
 * Source (all v7.2-rc2):
 *   drivers/media/usb/uvc/uvc_driver.c   uvc_colorspace       62-77
 *                                        uvc_xfer_func        79-104
 *                                        uvc_ycbcr_enc       106-131
 *                                        uvc_parse_frame     227-333
 *                                        uvc_parse_format    335-530
 *                                        uvc_parse_streaming 532-792 (count/alloc/loop only)
 *   drivers/media/common/uvc.c           uvc_fmts / by_guid    14-193
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "uvc_parse.h"

/* ======================================================================
 * SPIKE-STUB: kernel environment
 * ====================================================================== */

/* SPIKE-STUB: fixed-width kernel type names. */
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;

/* SPIKE-STUB: kernel utility macros (semantics preserved exactly). */
#define ARRAY_SIZE(a)      (sizeof(a) / sizeof((a)[0]))
#define DIV_ROUND_UP(n, d) (((n) + (d) - 1) / (d))
#define ALIGN(x, a)        (((x) + ((a) - 1)) & ~((__typeof__(x))(a) - 1))
#define PTR_ALIGN(p, a)    ((__typeof__(p))ALIGN((uintptr_t)(p), (a)))

/*
 * SPIKE-STUB: kernel clamp() is min(max(val, lo), hi). Reproduced exactly,
 * including its behaviour when lo > hi (which malformed descriptors can
 * produce): max first, then min. A naive ternary would diverge there.
 */
static inline u32 uvc_max_u32(u32 a, u32 b) { return a > b ? a : b; }
static inline u32 uvc_min_u32(u32 a, u32 b) { return a < b ? a : b; }
#define clamp(val, lo, hi) uvc_min_u32(uvc_max_u32((val), (lo)), (hi))

/* SPIKE-STUB: <asm/unaligned.h> little-endian accessors. */
static inline u16 get_unaligned_le16(const void *p)
{
	const u8 *b = p;
	return (u16)b[0] | ((u16)b[1] << 8);
}
static inline u32 get_unaligned_le32(const void *p)
{
	const u8 *b = p;
	return (u32)b[0] | ((u32)b[1] << 8) | ((u32)b[2] << 16) |
	       ((u32)b[3] << 24);
}

/* SPIKE-STUB: dev_dbg/dev_info/dev_err logging -> no-ops (args unevaluated). */
#define uvc_dbg(dev, flag, fmt, ...) do { } while (0)
#define dev_info(dev, fmt, ...)      do { } while (0)
#define dev_err(dev, fmt, ...)       do { } while (0)

/* SPIKE-STUB: slab allocator -> libc malloc + zero. The size passed in is
 * computed by the byte-for-byte kernel sizing in uvc_parse(); ASan on this
 * block is what turns the parser's out-of-bounds writes into crashes. */
#define GFP_KERNEL 0
static void *kzalloc(size_t size, int flags)
{
	void *p;
	(void)flags;
	p = malloc(size ? size : 1);
	if (p)
		memset(p, 0, size);
	return p;
}

/* SPIKE-STUB: USB constant from include/uapi/linux/usb/ch9.h
 * (USB_TYPE_CLASS | USB_DT_INTERFACE = 0x20 | 0x04). */
#define USB_DT_CS_INTERFACE 0x24

/* SPIKE-STUB: UVC descriptor subtype constants, include/uapi/linux/usb/video.h. */
#define UVC_VS_FORMAT_UNCOMPRESSED 0x04
#define UVC_VS_FRAME_UNCOMPRESSED  0x05
#define UVC_VS_FORMAT_MJPEG        0x06
#define UVC_VS_FRAME_MJPEG         0x07
#define UVC_VS_FORMAT_MPEG2TS      0x0a
#define UVC_VS_FORMAT_DV           0x0c
#define UVC_VS_COLORFORMAT         0x0d
#define UVC_VS_FORMAT_FRAME_BASED  0x10
#define UVC_VS_FRAME_FRAME_BASED   0x11
#define UVC_VS_FORMAT_STREAM_BASED 0x12
#define UVC_VS_STILL_IMAGE_FRAME   0x03

/* SPIKE-STUB: quirk and format-flag bits, drivers/media/usb/uvc/uvcvideo.h. */
#define UVC_QUIRK_RESTRICT_FRAME_RATE 0x00000200
#define UVC_QUIRK_FORCE_Y8            0x00000800
#define UVC_QUIRK_FORCE_BPP           0x00001000
#define UVC_FMT_FLAG_COMPRESSED       0x00000001
#define UVC_FMT_FLAG_STREAM           0x00000002

/* SPIKE-STUB: enum v4l2_colorspace values used below, include/uapi/linux/videodev2.h. */
enum v4l2_colorspace {
	V4L2_COLORSPACE_SMPTE170M     = 1,
	V4L2_COLORSPACE_SMPTE240M     = 2,
	V4L2_COLORSPACE_470_SYSTEM_M  = 5,
	V4L2_COLORSPACE_470_SYSTEM_BG = 6,
	V4L2_COLORSPACE_SRGB          = 8,
};
/* SPIKE-STUB: enum v4l2_xfer_func values used below. */
enum v4l2_xfer_func {
	V4L2_XFER_FUNC_DEFAULT   = 0,
	V4L2_XFER_FUNC_709       = 1,
	V4L2_XFER_FUNC_SRGB      = 2,
	V4L2_XFER_FUNC_SMPTE240M = 4,
	V4L2_XFER_FUNC_NONE      = 5,
};
/* SPIKE-STUB: enum v4l2_ycbcr_encoding values used below. */
enum v4l2_ycbcr_encoding {
	V4L2_YCBCR_ENC_DEFAULT   = 0,
	V4L2_YCBCR_ENC_601       = 1,
	V4L2_YCBCR_ENC_709       = 2,
	V4L2_YCBCR_ENC_SMPTE240M = 8,
};

/* SPIKE-STUB: fourcc helper + the V4L2_PIX_FMT_* codes referenced by the
 * format table, include/uapi/linux/videodev2.h. */
#define v4l2_fourcc(a, b, c, d) \
	((u32)(a) | ((u32)(b) << 8) | ((u32)(c) << 16) | ((u32)(d) << 24))
#define V4L2_PIX_FMT_YUYV    v4l2_fourcc('Y', 'U', 'Y', 'V')
#define V4L2_PIX_FMT_NV12    v4l2_fourcc('N', 'V', '1', '2')
#define V4L2_PIX_FMT_MJPEG   v4l2_fourcc('M', 'J', 'P', 'G')
#define V4L2_PIX_FMT_YVU420  v4l2_fourcc('Y', 'V', '1', '2')
#define V4L2_PIX_FMT_YUV420  v4l2_fourcc('Y', 'U', '1', '2')
#define V4L2_PIX_FMT_M420    v4l2_fourcc('M', '4', '2', '0')
#define V4L2_PIX_FMT_P010    v4l2_fourcc('P', '0', '1', '0')
#define V4L2_PIX_FMT_UYVY    v4l2_fourcc('U', 'Y', 'V', 'Y')
#define V4L2_PIX_FMT_GREY    v4l2_fourcc('G', 'R', 'E', 'Y')
#define V4L2_PIX_FMT_Y10     v4l2_fourcc('Y', '1', '0', ' ')
#define V4L2_PIX_FMT_Y12     v4l2_fourcc('Y', '1', '2', ' ')
#define V4L2_PIX_FMT_Y16     v4l2_fourcc('Y', '1', '6', ' ')
#define V4L2_PIX_FMT_SBGGR8  v4l2_fourcc('B', 'A', '8', '1')
#define V4L2_PIX_FMT_SGBRG8  v4l2_fourcc('G', 'B', 'R', 'G')
#define V4L2_PIX_FMT_SGRBG8  v4l2_fourcc('G', 'R', 'B', 'G')
#define V4L2_PIX_FMT_SRGGB8  v4l2_fourcc('R', 'G', 'G', 'B')
#define V4L2_PIX_FMT_RGB565  v4l2_fourcc('R', 'G', 'B', 'P')
#define V4L2_PIX_FMT_BGR24   v4l2_fourcc('B', 'G', 'R', '3')
#define V4L2_PIX_FMT_XBGR32  v4l2_fourcc('X', 'R', '2', '4')
#define V4L2_PIX_FMT_H264    v4l2_fourcc('H', '2', '6', '4')
#define V4L2_PIX_FMT_HEVC    v4l2_fourcc('H', 'E', 'V', 'C')
#define V4L2_PIX_FMT_Y8I     v4l2_fourcc('Y', '8', 'I', ' ')
#define V4L2_PIX_FMT_Y12I    v4l2_fourcc('Y', '1', '2', 'I')
#define V4L2_PIX_FMT_Y16I    v4l2_fourcc('Y', '1', '6', 'I')
#define V4L2_PIX_FMT_Z16     v4l2_fourcc('Z', '1', '6', ' ')
#define V4L2_PIX_FMT_SRGGB10P v4l2_fourcc('p', 'R', 'A', 'A')
#define V4L2_PIX_FMT_SBGGR16 v4l2_fourcc('B', 'Y', 'R', '2')
#define V4L2_PIX_FMT_SGBRG16 v4l2_fourcc('G', 'B', '1', '6')
#define V4L2_PIX_FMT_SRGGB16 v4l2_fourcc('R', 'G', '1', '6')
#define V4L2_PIX_FMT_SGRBG16 v4l2_fourcc('G', 'R', '1', '6')
#define V4L2_PIX_FMT_DV      v4l2_fourcc('d', 'v', 's', 'd')
#define V4L2_PIX_FMT_INZI    v4l2_fourcc('I', 'N', 'Z', 'I')
#define V4L2_PIX_FMT_CNF4    v4l2_fourcc('C', 'N', 'F', '4')

/* SPIKE-STUB: UVC format GUIDs, include/linux/usb/uvc.h. */
#define UVC_GUID_FORMAT_MJPEG \
	{ 'M', 'J', 'P', 'G', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_YUY2 \
	{ 'Y', 'U', 'Y', '2', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_YUY2_ISIGHT \
	{ 'Y', 'U', 'Y', '2', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_NV12 \
	{ 'N', 'V', '1', '2', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_YV12 \
	{ 'Y', 'V', '1', '2', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_I420 \
	{ 'I', '4', '2', '0', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_UYVY \
	{ 'U', 'Y', 'V', 'Y', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y800 \
	{ 'Y', '8', '0', '0', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y8 \
	{ 'Y', '8', ' ', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y10 \
	{ 'Y', '1', '0', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y12 \
	{ 'Y', '1', '2', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y16 \
	{ 'Y', '1', '6', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_BY8 \
	{ 'B', 'Y', '8', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_BA81 \
	{ 'B', 'A', '8', '1', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_GBRG \
	{ 'G', 'B', 'R', 'G', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_GRBG \
	{ 'G', 'R', 'B', 'G', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_RGGB \
	{ 'R', 'G', 'G', 'B', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_BG16 \
	{ 'B', 'G', '1', '6', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_GB16 \
	{ 'G', 'B', '1', '6', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_RG16 \
	{ 'R', 'G', '1', '6', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_GR16 \
	{ 'G', 'R', '1', '6', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_RGBP \
	{ 'R', 'G', 'B', 'P', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_BGR3 \
	{ 0x7d, 0xeb, 0x36, 0xe4, 0x4f, 0x52, 0xce, 0x11, 0x9f, 0x53, 0x00, 0x20, 0xaf, 0x0b, 0xa7, 0x70}
#define UVC_GUID_FORMAT_BGR4 \
	{ 0x7e, 0xeb, 0x36, 0xe4, 0x4f, 0x52, 0xce, 0x11, 0x9f, 0x53, 0x00, 0x20, 0xaf, 0x0b, 0xa7, 0x70}
#define UVC_GUID_FORMAT_M420 \
	{ 'M', '4', '2', '0', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_P010 \
	{ 'P', '0', '1', '0', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_H264 \
	{ 'H', '2', '6', '4', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_H265 \
	{ 'H', '2', '6', '5', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y8I \
	{ 'Y', '8', 'I', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y12I \
	{ 'Y', '1', '2', 'I', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Y16I \
	{ 'Y', '1', '6', 'I', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_Z16 \
	{ 'Z', '1', '6', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_RW10 \
	{ 'R', 'W', '1', '0', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_INVZ \
	{ 'I', 'N', 'V', 'Z', 0x90, 0x2d, 0x58, 0x4a, 0x92, 0x0b, 0x77, 0x3f, 0x1f, 0x2c, 0x55, 0x6b}
#define UVC_GUID_FORMAT_INZI \
	{ 'I', 'N', 'Z', 'I', 0x66, 0x1a, 0x42, 0xa2, 0x90, 0x65, 0xd0, 0x18, 0x14, 0xa8, 0xef, 0x8a}
#define UVC_GUID_FORMAT_INVI \
	{ 'I', 'N', 'V', 'I', 0xdb, 0x57, 0x49, 0x5e, 0x8e, 0x3f, 0xf4, 0x79, 0x53, 0x2b, 0x94, 0x6f}
#define UVC_GUID_FORMAT_CNF4 \
	{ 'C', ' ', ' ', ' ', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_D3DFMT_L8 \
	{ 0x32, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_D3DFMT_R5G6B5 \
	{ 0x7b, 0xeb, 0x36, 0xe4, 0x4f, 0x52, 0xce, 0x11, 0x9f, 0x53, 0x00, 0x20, 0xaf, 0x0b, 0xa7, 0x70}
#define UVC_GUID_FORMAT_KSMEDIA_L8_IR \
	{ 0x32, 0x00, 0x00, 0x00, 0x02, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}
#define UVC_GUID_FORMAT_HEVC \
	{ 'H', 'E', 'V', 'C', 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xaa, 0x00, 0x38, 0x9b, 0x71}

/* SPIKE-STUB: struct uvc_format_desc, include/linux/usb/uvc.h. */
struct uvc_format_desc {
	u8 guid[16];
	u32 fcc;
};

/* SPIKE-STUB: struct v4l2_format_info (only fields touched under FORCE_BPP). */
struct v4l2_format_info {
	u32 hdiv;
	u32 vdiv;
	u8  comp_planes;
	u8  bpp[4];
};

/*
 * SPIKE-STUB: v4l2_format_info() lives in the v4l2 core (drivers/media/
 * v4l2-core/v4l2-common.c) and is unrelated to UVC parsing. We stub it to
 * return NULL, which is the common runtime case (the FORCE_BPP quirk only
 * fires for a handful of devices and quirks is an explicit input here).
 * Both C and Rust stub it identically, so the differential test stays valid;
 * the FORCE_BPP recompute branch is therefore inert in this spike.
 */
static const struct v4l2_format_info *v4l2_format_info(u32 format)
{
	(void)format;
	return NULL;
}

/* SPIKE-STUB: minimal stand-ins for the USB/UVC device structs. Only the
 * members the copied code dereferences are present; the rest lived only
 * inside logging calls, which are now no-ops. */
struct uvc_host_desc {
	u8 bInterfaceNumber;
};
struct usb_host_interface {
	struct uvc_host_desc desc;
};
struct usb_interface {
	struct usb_host_interface *cur_altsetting;
};
struct uvc_device {
	u32 quirks;
};

/* ======================================================================
 * Kernel structs, copied byte-for-byte
 * drivers/media/usb/uvc/uvcvideo.h:265-290
 * ====================================================================== */

struct uvc_frame {
	u8  bFrameIndex;
	u8  bmCapabilities;
	u16 wWidth;
	u16 wHeight;
	u32 dwMinBitRate;
	u32 dwMaxBitRate;
	u32 dwMaxVideoFrameBufferSize;
	u8  bFrameIntervalType;
	u32 dwDefaultFrameInterval;
	const u32 *dwFrameInterval;
};

struct uvc_format {
	u8 type;
	u8 index;
	u8 bpp;
	enum v4l2_colorspace colorspace;
	enum v4l2_xfer_func xfer_func;
	enum v4l2_ycbcr_encoding ycbcr_enc;
	u32 fcc;
	u32 flags;

	unsigned int nframes;
	const struct uvc_frame *frames;
};

/* SPIKE-STUB: struct uvc_streaming reduced to the members the copied
 * counting/allocation/driving code touches. */
struct uvc_streaming {
	struct usb_interface *intf;
	unsigned int nformats;
	struct uvc_format *formats;
};

/* ======================================================================
 * Copied byte-for-byte: drivers/media/common/uvc.c:14-193
 * ====================================================================== */

static const struct uvc_format_desc uvc_fmts[] = {
	{
		.guid		= UVC_GUID_FORMAT_YUY2,
		.fcc		= V4L2_PIX_FMT_YUYV,
	},
	{
		.guid		= UVC_GUID_FORMAT_YUY2_ISIGHT,
		.fcc		= V4L2_PIX_FMT_YUYV,
	},
	{
		.guid		= UVC_GUID_FORMAT_NV12,
		.fcc		= V4L2_PIX_FMT_NV12,
	},
	{
		.guid		= UVC_GUID_FORMAT_MJPEG,
		.fcc		= V4L2_PIX_FMT_MJPEG,
	},
	{
		.guid		= UVC_GUID_FORMAT_YV12,
		.fcc		= V4L2_PIX_FMT_YVU420,
	},
	{
		.guid		= UVC_GUID_FORMAT_I420,
		.fcc		= V4L2_PIX_FMT_YUV420,
	},
	{
		.guid		= UVC_GUID_FORMAT_M420,
		.fcc		= V4L2_PIX_FMT_M420,
	},
	{
		.guid		= UVC_GUID_FORMAT_P010,
		.fcc		= V4L2_PIX_FMT_P010,
	},
	{
		.guid		= UVC_GUID_FORMAT_UYVY,
		.fcc		= V4L2_PIX_FMT_UYVY,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y800,
		.fcc		= V4L2_PIX_FMT_GREY,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y8,
		.fcc		= V4L2_PIX_FMT_GREY,
	},
	{
		.guid		= UVC_GUID_FORMAT_D3DFMT_L8,
		.fcc		= V4L2_PIX_FMT_GREY,
	},
	{
		.guid		= UVC_GUID_FORMAT_KSMEDIA_L8_IR,
		.fcc		= V4L2_PIX_FMT_GREY,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y10,
		.fcc		= V4L2_PIX_FMT_Y10,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y12,
		.fcc		= V4L2_PIX_FMT_Y12,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y16,
		.fcc		= V4L2_PIX_FMT_Y16,
	},
	{
		.guid		= UVC_GUID_FORMAT_BY8,
		.fcc		= V4L2_PIX_FMT_SBGGR8,
	},
	{
		.guid		= UVC_GUID_FORMAT_BA81,
		.fcc		= V4L2_PIX_FMT_SBGGR8,
	},
	{
		.guid		= UVC_GUID_FORMAT_GBRG,
		.fcc		= V4L2_PIX_FMT_SGBRG8,
	},
	{
		.guid		= UVC_GUID_FORMAT_GRBG,
		.fcc		= V4L2_PIX_FMT_SGRBG8,
	},
	{
		.guid		= UVC_GUID_FORMAT_RGGB,
		.fcc		= V4L2_PIX_FMT_SRGGB8,
	},
	{
		.guid		= UVC_GUID_FORMAT_RGBP,
		.fcc		= V4L2_PIX_FMT_RGB565,
	},
	{
		.guid		= UVC_GUID_FORMAT_D3DFMT_R5G6B5,
		.fcc		= V4L2_PIX_FMT_RGB565,
	},
	{
		.guid		= UVC_GUID_FORMAT_BGR3,
		.fcc		= V4L2_PIX_FMT_BGR24,
	},
	{
		.guid		= UVC_GUID_FORMAT_BGR4,
		.fcc		= V4L2_PIX_FMT_XBGR32,
	},
	{
		.guid		= UVC_GUID_FORMAT_H264,
		.fcc		= V4L2_PIX_FMT_H264,
	},
	{
		.guid		= UVC_GUID_FORMAT_H265,
		.fcc		= V4L2_PIX_FMT_HEVC,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y8I,
		.fcc		= V4L2_PIX_FMT_Y8I,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y12I,
		.fcc		= V4L2_PIX_FMT_Y12I,
	},
	{
		.guid		= UVC_GUID_FORMAT_Y16I,
		.fcc		= V4L2_PIX_FMT_Y16I,
	},
	{
		.guid		= UVC_GUID_FORMAT_Z16,
		.fcc		= V4L2_PIX_FMT_Z16,
	},
	{
		.guid		= UVC_GUID_FORMAT_RW10,
		.fcc		= V4L2_PIX_FMT_SRGGB10P,
	},
	{
		.guid		= UVC_GUID_FORMAT_BG16,
		.fcc		= V4L2_PIX_FMT_SBGGR16,
	},
	{
		.guid		= UVC_GUID_FORMAT_GB16,
		.fcc		= V4L2_PIX_FMT_SGBRG16,
	},
	{
		.guid		= UVC_GUID_FORMAT_RG16,
		.fcc		= V4L2_PIX_FMT_SRGGB16,
	},
	{
		.guid		= UVC_GUID_FORMAT_GR16,
		.fcc		= V4L2_PIX_FMT_SGRBG16,
	},
	{
		.guid		= UVC_GUID_FORMAT_INVZ,
		.fcc		= V4L2_PIX_FMT_Z16,
	},
	{
		.guid		= UVC_GUID_FORMAT_INVI,
		.fcc		= V4L2_PIX_FMT_Y10,
	},
	{
		.guid		= UVC_GUID_FORMAT_INZI,
		.fcc		= V4L2_PIX_FMT_INZI,
	},
	{
		.guid		= UVC_GUID_FORMAT_CNF4,
		.fcc		= V4L2_PIX_FMT_CNF4,
	},
	{
		.guid		= UVC_GUID_FORMAT_HEVC,
		.fcc		= V4L2_PIX_FMT_HEVC,
	},
};

static const struct uvc_format_desc *uvc_format_by_guid(const u8 guid[16])
{
	unsigned int len = ARRAY_SIZE(uvc_fmts);
	unsigned int i;

	for (i = 0; i < len; ++i) {
		if (memcmp(guid, uvc_fmts[i].guid, 16) == 0)
			return &uvc_fmts[i];
	}

	return NULL;
}

/* ======================================================================
 * Copied byte-for-byte: drivers/media/usb/uvc/uvc_driver.c:62-131
 * ====================================================================== */

static enum v4l2_colorspace uvc_colorspace(const u8 primaries)
{
	static const enum v4l2_colorspace colorprimaries[] = {
		V4L2_COLORSPACE_SRGB,  /* Unspecified */
		V4L2_COLORSPACE_SRGB,
		V4L2_COLORSPACE_470_SYSTEM_M,
		V4L2_COLORSPACE_470_SYSTEM_BG,
		V4L2_COLORSPACE_SMPTE170M,
		V4L2_COLORSPACE_SMPTE240M,
	};

	if (primaries < ARRAY_SIZE(colorprimaries))
		return colorprimaries[primaries];

	return V4L2_COLORSPACE_SRGB;  /* Reserved */
}

static enum v4l2_xfer_func uvc_xfer_func(const u8 transfer_characteristics)
{
	/*
	 * V4L2 does not currently have definitions for all possible values of
	 * UVC transfer characteristics. If v4l2_xfer_func is extended with new
	 * values, the mapping below should be updated.
	 *
	 * Substitutions are taken from the mapping given for
	 * V4L2_XFER_FUNC_DEFAULT documented in videodev2.h.
	 */
	static const enum v4l2_xfer_func xfer_funcs[] = {
		V4L2_XFER_FUNC_DEFAULT,    /* Unspecified */
		V4L2_XFER_FUNC_709,
		V4L2_XFER_FUNC_709,        /* Substitution for BT.470-2 M */
		V4L2_XFER_FUNC_709,        /* Substitution for BT.470-2 B, G */
		V4L2_XFER_FUNC_709,        /* Substitution for SMPTE 170M */
		V4L2_XFER_FUNC_SMPTE240M,
		V4L2_XFER_FUNC_NONE,
		V4L2_XFER_FUNC_SRGB,
	};

	if (transfer_characteristics < ARRAY_SIZE(xfer_funcs))
		return xfer_funcs[transfer_characteristics];

	return V4L2_XFER_FUNC_DEFAULT;  /* Reserved */
}

static enum v4l2_ycbcr_encoding uvc_ycbcr_enc(const u8 matrix_coefficients)
{
	/*
	 * V4L2 does not currently have definitions for all possible values of
	 * UVC matrix coefficients. If v4l2_ycbcr_encoding is extended with new
	 * values, the mapping below should be updated.
	 *
	 * Substitutions are taken from the mapping given for
	 * V4L2_YCBCR_ENC_DEFAULT documented in videodev2.h.
	 *
	 * FCC is assumed to be close enough to 601.
	 */
	static const enum v4l2_ycbcr_encoding ycbcr_encs[] = {
		V4L2_YCBCR_ENC_DEFAULT,  /* Unspecified */
		V4L2_YCBCR_ENC_709,
		V4L2_YCBCR_ENC_601,      /* Substitution for FCC */
		V4L2_YCBCR_ENC_601,      /* Substitution for BT.470-2 B, G */
		V4L2_YCBCR_ENC_601,
		V4L2_YCBCR_ENC_SMPTE240M,
	};

	if (matrix_coefficients < ARRAY_SIZE(ycbcr_encs))
		return ycbcr_encs[matrix_coefficients];

	return V4L2_YCBCR_ENC_DEFAULT;  /* Reserved */
}

/* ======================================================================
 * Copied byte-for-byte: drivers/media/usb/uvc/uvc_driver.c:227-530
 * (uvc_dbg/dev_info calls now expand to no-ops; -EINVAL provided below)
 * ====================================================================== */

#define EINVAL 22

static int uvc_parse_frame(struct uvc_device *dev,
			   struct uvc_streaming *streaming,
			   struct uvc_format *format, struct uvc_frame *frame,
			   u32 **intervals, u8 ftype, int width_multiplier,
			   const unsigned char *buffer, int buflen)
{
	struct usb_host_interface *alts = streaming->intf->cur_altsetting;
	unsigned int maxIntervalIndex;
	unsigned int interval;
	unsigned int i, n;

	if (ftype != UVC_VS_FRAME_FRAME_BASED)
		n = buflen > 25 ? buffer[25] : 0;
	else
		n = buflen > 21 ? buffer[21] : 0;

	n = n ? n : 3;

	if (buflen < 26 + 4 * n) {
		uvc_dbg(dev, DESCR,
			"device %d videostreaming interface %d FRAME error\n",
			dev->udev->devnum, alts->desc.bInterfaceNumber);
		return -EINVAL;
	}

	frame->bFrameIndex = buffer[3];
	frame->bmCapabilities = buffer[4];
	frame->wWidth = get_unaligned_le16(&buffer[5]) * width_multiplier;
	frame->wHeight = get_unaligned_le16(&buffer[7]);
	frame->dwMinBitRate = get_unaligned_le32(&buffer[9]);
	frame->dwMaxBitRate = get_unaligned_le32(&buffer[13]);
	if (ftype != UVC_VS_FRAME_FRAME_BASED) {
		frame->dwMaxVideoFrameBufferSize =
			get_unaligned_le32(&buffer[17]);
		frame->dwDefaultFrameInterval =
			get_unaligned_le32(&buffer[21]);
		frame->bFrameIntervalType = buffer[25];
	} else {
		frame->dwMaxVideoFrameBufferSize = 0;
		frame->dwDefaultFrameInterval =
			get_unaligned_le32(&buffer[17]);
		frame->bFrameIntervalType = buffer[21];
	}

	/*
	 * Copy the frame intervals.
	 *
	 * Some bogus devices report dwMinFrameInterval equal to
	 * dwMaxFrameInterval and have dwFrameIntervalStep set to zero. Setting
	 * all null intervals to 1 fixes the problem and some other divisions
	 * by zero that could happen.
	 */
	frame->dwFrameInterval = *intervals;

	for (i = 0; i < n; ++i) {
		interval = get_unaligned_le32(&buffer[26 + 4 * i]);
		(*intervals)[i] = interval ? interval : 1;
	}

	/*
	 * Apply more fixes, quirks and workarounds to handle incorrect or
	 * broken descriptors.
	 */

	/*
	 * Several UVC chipsets screw up dwMaxVideoFrameBufferSize completely.
	 * Observed behaviours range from setting the value to 1.1x the actual
	 * frame size to hardwiring the 16 low bits to 0. This results in a
	 * higher than necessary memory usage as well as a wrong image size
	 * information. For uncompressed formats this can be fixed by computing
	 * the value from the frame size.
	 */
	if (!(format->flags & UVC_FMT_FLAG_COMPRESSED))
		frame->dwMaxVideoFrameBufferSize = format->bpp * frame->wWidth
						 * frame->wHeight / 8;

	/*
	 * Clamp the default frame interval to the boundaries. A zero
	 * bFrameIntervalType value indicates a continuous frame interval
	 * range, with dwFrameInterval[0] storing the minimum value and
	 * dwFrameInterval[1] storing the maximum value.
	 */
	maxIntervalIndex = frame->bFrameIntervalType ? n - 1 : 1;
	frame->dwDefaultFrameInterval =
		clamp(frame->dwDefaultFrameInterval,
		      frame->dwFrameInterval[0],
		      frame->dwFrameInterval[maxIntervalIndex]);

	/*
	 * Some devices report frame intervals that are not functional. If the
	 * corresponding quirk is set, restrict operation to the first interval
	 * only.
	 */
	if (dev->quirks & UVC_QUIRK_RESTRICT_FRAME_RATE) {
		frame->bFrameIntervalType = 1;
		(*intervals)[0] = frame->dwDefaultFrameInterval;
	}

	uvc_dbg(dev, DESCR, "- %ux%u (%u.%u fps)\n",
		frame->wWidth, frame->wHeight,
		10000000 / frame->dwDefaultFrameInterval,
		(100000000 / frame->dwDefaultFrameInterval) % 10);

	*intervals += n;

	return buffer[0];
}

static int uvc_parse_format(struct uvc_device *dev,
	struct uvc_streaming *streaming, struct uvc_format *format,
	struct uvc_frame *frames, u32 **intervals, const unsigned char *buffer,
	int buflen)
{
	struct usb_host_interface *alts = streaming->intf->cur_altsetting;
	const struct uvc_format_desc *fmtdesc;
	struct uvc_frame *frame;
	const unsigned char *start = buffer;
	unsigned int width_multiplier = 1;
	unsigned int i, n;
	u8 ftype;
	int ret;

	if (buflen < 4)
		return -EINVAL;

	format->type = buffer[2];
	format->index = buffer[3];
	format->frames = frames;

	switch (buffer[2]) {
	case UVC_VS_FORMAT_UNCOMPRESSED:
	case UVC_VS_FORMAT_FRAME_BASED:
		n = buffer[2] == UVC_VS_FORMAT_UNCOMPRESSED ? 27 : 28;
		if (buflen < n) {
			uvc_dbg(dev, DESCR,
				"device %d videostreaming interface %d FORMAT error\n",
				dev->udev->devnum,
				alts->desc.bInterfaceNumber);
			return -EINVAL;
		}

		/* Find the format descriptor from its GUID. */
		fmtdesc = uvc_format_by_guid(&buffer[5]);

		if (!fmtdesc) {
			/*
			 * Unknown video formats are not fatal errors, the
			 * caller will skip this descriptor.
			 */
			dev_info(&streaming->intf->dev,
				 "Unknown video format %pUl\n", &buffer[5]);
			return 0;
		}

		format->fcc = fmtdesc->fcc;
		format->bpp = buffer[21];

		/*
		 * Some devices report a format that doesn't match what they
		 * really send.
		 */
		if (dev->quirks & UVC_QUIRK_FORCE_Y8) {
			if (format->fcc == V4L2_PIX_FMT_YUYV) {
				format->fcc = V4L2_PIX_FMT_GREY;
				format->bpp = 8;
				width_multiplier = 2;
			}
		}

		/* Some devices report bpp that doesn't match the format. */
		if (dev->quirks & UVC_QUIRK_FORCE_BPP) {
			const struct v4l2_format_info *info =
				v4l2_format_info(format->fcc);

			if (info) {
				unsigned int div = info->hdiv * info->vdiv;

				n = info->bpp[0] * div;
				for (i = 1; i < info->comp_planes; i++)
					n += info->bpp[i];

				format->bpp = DIV_ROUND_UP(8 * n, div);
			}
		}

		if (buffer[2] == UVC_VS_FORMAT_UNCOMPRESSED) {
			ftype = UVC_VS_FRAME_UNCOMPRESSED;
		} else {
			ftype = UVC_VS_FRAME_FRAME_BASED;
			if (buffer[27])
				format->flags = UVC_FMT_FLAG_COMPRESSED;
		}
		break;

	case UVC_VS_FORMAT_MJPEG:
		if (buflen < 11) {
			uvc_dbg(dev, DESCR,
				"device %d videostreaming interface %d FORMAT error\n",
				dev->udev->devnum,
				alts->desc.bInterfaceNumber);
			return -EINVAL;
		}

		format->fcc = V4L2_PIX_FMT_MJPEG;
		format->flags = UVC_FMT_FLAG_COMPRESSED;
		format->bpp = 0;
		ftype = UVC_VS_FRAME_MJPEG;
		break;

	case UVC_VS_FORMAT_DV:
		if (buflen < 9) {
			uvc_dbg(dev, DESCR,
				"device %d videostreaming interface %d FORMAT error\n",
				dev->udev->devnum,
				alts->desc.bInterfaceNumber);
			return -EINVAL;
		}

		if ((buffer[8] & 0x7f) > 2) {
			uvc_dbg(dev, DESCR,
				"device %d videostreaming interface %d: unknown DV format %u\n",
				dev->udev->devnum,
				alts->desc.bInterfaceNumber, buffer[8]);
			return -EINVAL;
		}

		format->fcc = V4L2_PIX_FMT_DV;
		format->flags = UVC_FMT_FLAG_COMPRESSED | UVC_FMT_FLAG_STREAM;
		format->bpp = 0;
		ftype = 0;

		/* Create a dummy frame descriptor. */
		frame = &frames[0];
		memset(frame, 0, sizeof(*frame));
		frame->bFrameIntervalType = 1;
		frame->dwDefaultFrameInterval = 1;
		frame->dwFrameInterval = *intervals;
		*(*intervals)++ = 1;
		format->nframes = 1;
		break;

	case UVC_VS_FORMAT_MPEG2TS:
	case UVC_VS_FORMAT_STREAM_BASED:
		/* Not supported yet. */
	default:
		uvc_dbg(dev, DESCR,
			"device %d videostreaming interface %d unsupported format %u\n",
			dev->udev->devnum, alts->desc.bInterfaceNumber,
			buffer[2]);
		return -EINVAL;
	}

	uvc_dbg(dev, DESCR, "Found format %p4cc", &format->fcc);

	buflen -= buffer[0];
	buffer += buffer[0];

	/*
	 * Parse the frame descriptors. Only uncompressed, MJPEG and frame
	 * based formats have frame descriptors.
	 */
	if (ftype) {
		while (buflen > 2 && buffer[1] == USB_DT_CS_INTERFACE &&
		       buffer[2] == ftype) {
			frame = &frames[format->nframes];
			ret = uvc_parse_frame(dev, streaming, format, frame,
					      intervals, ftype, width_multiplier,
					      buffer, buflen);
			if (ret < 0)
				return ret;
			format->nframes++;
			buflen -= ret;
			buffer += ret;
		}
	}

	if (buflen > 2 && buffer[1] == USB_DT_CS_INTERFACE &&
	    buffer[2] == UVC_VS_STILL_IMAGE_FRAME) {
		buflen -= buffer[0];
		buffer += buffer[0];
	}

	if (buflen > 2 && buffer[1] == USB_DT_CS_INTERFACE &&
	    buffer[2] == UVC_VS_COLORFORMAT) {
		if (buflen < 6) {
			uvc_dbg(dev, DESCR,
				"device %d videostreaming interface %d COLORFORMAT error\n",
				dev->udev->devnum,
				alts->desc.bInterfaceNumber);
			return -EINVAL;
		}

		format->colorspace = uvc_colorspace(buffer[3]);
		format->xfer_func = uvc_xfer_func(buffer[4]);
		format->ycbcr_enc = uvc_ycbcr_enc(buffer[5]);

		buflen -= buffer[0];
		buffer += buffer[0];
	} else {
		format->colorspace = V4L2_COLORSPACE_SRGB;
	}

	return buffer - start;
}

/* ======================================================================
 * Entry point.
 *
 * The counting pass, the allocation, and the format-driving loop below are
 * copied byte-for-byte from uvc_parse_streaming (uvc_driver.c:657-764),
 * with the header parsing dropped (this entry takes the buffer already
 * positioned at the first FORMAT descriptor) and kzalloc stubbed. The final
 * block serializes the parsed structs into the flat result and is spike
 * scaffolding, not kernel code.
 * ====================================================================== */

int32_t uvc_parse(const uint8_t *buffer, int32_t buflen, uint32_t quirks,
		  struct uvc_parse_result *out)
{
	struct uvc_device dev_storage;
	struct uvc_host_desc desc_storage;
	struct usb_host_interface alts_storage;
	struct usb_interface intf_storage;
	struct uvc_streaming streaming_storage;
	struct uvc_device *dev = &dev_storage;
	struct uvc_streaming *streaming = &streaming_storage;

	struct uvc_format *format;
	struct uvc_frame *frame;
	const unsigned char *_buffer;
	int _buflen;
	unsigned int nformats = 0, nframes = 0, nintervals = 0;
	unsigned int size;
	u32 *interval;
	int ret = -EINVAL;

	/* SPIKE-STUB: assemble the device/interface/streaming context that the
	 * copied code dereferences. quirks is a fuzzable input. */
	desc_storage.bInterfaceNumber = 0;
	alts_storage.desc = desc_storage;
	intf_storage.cur_altsetting = &alts_storage;
	dev_storage.quirks = quirks;
	streaming_storage.intf = &intf_storage;
	streaming_storage.nformats = 0;
	streaming_storage.formats = NULL;

	memset(out, 0, sizeof(*out));

	_buffer = buffer;
	_buflen = buflen;

	/* Count the format and frame descriptors. */
	while (_buflen > 2 && _buffer[1] == USB_DT_CS_INTERFACE) {
		switch (_buffer[2]) {
		case UVC_VS_FORMAT_UNCOMPRESSED:
		case UVC_VS_FORMAT_MJPEG:
		case UVC_VS_FORMAT_FRAME_BASED:
			nformats++;
			break;

		case UVC_VS_FORMAT_DV:
			/*
			 * DV format has no frame descriptor. We will create a
			 * dummy frame descriptor with a dummy frame interval.
			 */
			nformats++;
			nframes++;
			nintervals++;
			break;

		case UVC_VS_FORMAT_MPEG2TS:
		case UVC_VS_FORMAT_STREAM_BASED:
			break;

		case UVC_VS_FRAME_UNCOMPRESSED:
		case UVC_VS_FRAME_MJPEG:
#ifndef SPIKE_VULN
			nframes++;
			if (_buflen > 25)
				nintervals += _buffer[25] ? _buffer[25] : 3;
#else
			/*
			 * SPIKE-VULN (negative control, NOT kernel code; enabled
			 * only with -DSPIKE_VULN): under-count uncompressed/MJPEG
			 * frames, reintroducing a CVE-2024-53104-class
			 * counting-vs-parsing mismatch. uvc_parse_format then
			 * writes frames/intervals past the under-sized allocation
			 * -> out-of-bounds write. This exists purely to show the
			 * differential harness catches the CVE class: the C
			 * corrupts memory (ASan aborts) while the Rust, sized by
			 * the identical bug, safely panics on the bounds check.
			 */
			(void)0;
#endif
			break;

		case UVC_VS_FRAME_FRAME_BASED:
			nframes++;
			if (_buflen > 21)
				nintervals += _buffer[21] ? _buffer[21] : 3;
			break;
		}

		_buflen -= _buffer[0];
		_buffer += _buffer[0];
	}

	if (nformats == 0) {
		/* No supported formats: nothing to parse. */
		out->ret = ret;
		return ret;
	}

	/*
	 * Allocate memory for the formats, the frames and the intervals,
	 * plus any required padding to guarantee that everything has the
	 * correct alignment.
	 */
	size = nformats * sizeof(*format);
	size = ALIGN(size, __alignof__(*frame)) + nframes * sizeof(*frame);
	size = ALIGN(size, __alignof__(*interval))
	     + nintervals * sizeof(*interval);

	format = kzalloc(size, GFP_KERNEL);
	if (!format) {
		ret = -12 /* -ENOMEM */;
		out->ret = ret;
		return ret;
	}
	/* SPIKE-STUB: keep the allocation base so we can free() it; the copied
	 * driving loop advances `format` as it goes. */
	struct uvc_format *alloc_base = format;

	frame = (void *)format + nformats * sizeof(*format);
	frame = PTR_ALIGN(frame, __alignof__(*frame));
	interval = (void *)frame + nframes * sizeof(*frame);
	interval = PTR_ALIGN(interval, __alignof__(*interval));

	streaming->formats = format;
	streaming->nformats = 0;

	/* Record the allocation bases for serialization. */
	out->nformats_alloc = nformats;
	out->nframes_alloc = nframes;
	out->nintervals_alloc = nintervals;
	{
		struct uvc_format *format_base = format;
		struct uvc_frame *frame_base = frame;
		u32 *interval_base = interval;

		/* Parse the format descriptors. */
		while (buflen > 2 && buffer[1] == USB_DT_CS_INTERFACE) {
			switch (buffer[2]) {
			case UVC_VS_FORMAT_UNCOMPRESSED:
			case UVC_VS_FORMAT_MJPEG:
			case UVC_VS_FORMAT_DV:
			case UVC_VS_FORMAT_FRAME_BASED:
				ret = uvc_parse_format(dev, streaming, format,
					frame, &interval, buffer, buflen);
				if (ret < 0)
					goto done;
				if (!ret)
					break;

				streaming->nformats++;
				frame += format->nframes;
				format++;

				buflen -= ret;
				buffer += ret;
				continue;

			default:
				break;
			}

			buflen -= buffer[0];
			buffer += buffer[0];
		}

		/*
		 * SPIKE scaffolding: serialize the parsed formats/frames/
		 * intervals into the flat result for differential comparison.
		 */
		if (ret >= 0)
			ret = (int)streaming->nformats;

done:
		out->ret = ret;

		{
			unsigned int nf = streaming->nformats;
			unsigned int total_frames = (unsigned int)(frame - frame_base);
			unsigned int total_intervals =
				(unsigned int)(interval - interval_base);
			unsigned int fi, gi;

			if (nf > UVC_MAX_FORMATS)
				nf = UVC_MAX_FORMATS;
			if (total_frames > UVC_MAX_FRAMES)
				total_frames = UVC_MAX_FRAMES;
			if (total_intervals > UVC_MAX_INTERVALS)
				total_intervals = UVC_MAX_INTERVALS;

			out->nformats = nf;
			out->nframes = total_frames;
			out->nintervals = total_intervals;

			for (fi = 0; fi < nf; fi++) {
				struct uvc_format *f = &format_base[fi];
				struct uvc_format_out *o = &out->formats[fi];

				o->type = f->type;
				o->index = f->index;
				o->bpp = f->bpp;
				o->colorspace = (int32_t)f->colorspace;
				o->xfer_func = (int32_t)f->xfer_func;
				o->ycbcr_enc = (int32_t)f->ycbcr_enc;
				o->fcc = f->fcc;
				o->flags = f->flags;
				o->nframes = f->nframes;
				o->frame_base =
					(int32_t)(f->frames - frame_base);
			}

			for (gi = 0; gi < total_frames; gi++) {
				struct uvc_frame *f = &frame_base[gi];
				struct uvc_frame_out *o = &out->frames[gi];

				o->bFrameIndex = f->bFrameIndex;
				o->bmCapabilities = f->bmCapabilities;
				o->wWidth = f->wWidth;
				o->wHeight = f->wHeight;
				o->dwMinBitRate = f->dwMinBitRate;
				o->dwMaxBitRate = f->dwMaxBitRate;
				o->dwMaxVideoFrameBufferSize =
					f->dwMaxVideoFrameBufferSize;
				o->bFrameIntervalType = f->bFrameIntervalType;
				o->dwDefaultFrameInterval =
					f->dwDefaultFrameInterval;
				o->interval_base = f->dwFrameInterval ?
					(int32_t)(f->dwFrameInterval - interval_base) :
					-1;
			}

			for (gi = 0; gi < total_intervals; gi++)
				out->intervals[gi] = interval_base[gi];
		}
	}

	free(alloc_base);
	return ret;
}
