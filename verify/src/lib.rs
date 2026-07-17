// SPDX-License-Identifier: GPL-2.0
//! Memory-safe Rust reimplementation of the Linux kernel UVC videostreaming
//! format/frame descriptor parser (`uvc_parse_format` + `uvc_parse_frame`
//! and the counting/allocation logic of `uvc_parse_streaming`), kernel
//! v7.2-rc2, `drivers/media/usb/uvc/`.
//!
//! This is the "rewrite the untrusted parser in a memory-safe language" step
//! of the hardening loop. It preserves the C control flow, the validation
//! checks, and the exact integer arithmetic (including the places the C
//! relies on 32-bit wraparound), but replaces raw pointers and a single
//! hand-sized `kzalloc` block with bounds-checked slices and `Vec`s. Where
//! the C would write out of bounds (the CVE class), this code panics instead
//! — which is precisely the observable difference the differential fuzzer is
//! meant to catch.
//!
//! The entry point `uvc_parse` has the same C ABI and the same flat result
//! struct as the C extraction in `../c`, so one harness drives both.
//!
//! Deviations from the C are collected in `rust/README.md`; each is also
//! tagged `// DEVIATION` at its site below.

// (FFI shell removed in the extraction copy; see VERIFY-REPORT.md)

// ======================================================================
// Flat C-ABI result types — identical layout to c/uvc_parse.h.
// ======================================================================

pub const UVC_MAX_FORMATS: usize = 64;
pub const UVC_MAX_FRAMES: usize = 256;
pub const UVC_MAX_INTERVALS: usize = 1024;

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct UvcFormatOut {
    pub type_: u8,
    pub index: u8,
    pub bpp: u8,
    pub colorspace: i32,
    pub xfer_func: i32,
    pub ycbcr_enc: i32,
    pub fcc: u32,
    pub flags: u32,
    pub nframes: u32,
    pub frame_base: i32,
}

#[repr(C)]
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct UvcFrameOut {
    pub b_frame_index: u8,
    pub bm_capabilities: u8,
    pub w_width: u16,
    pub w_height: u16,
    pub dw_min_bit_rate: u32,
    pub dw_max_bit_rate: u32,
    pub dw_max_video_frame_buffer_size: u32,
    pub b_frame_interval_type: u8,
    pub dw_default_frame_interval: u32,
    pub interval_base: i32,
}

// (The shipping crate's `const _: () = assert!(size_of::<UvcParseResult>() ==
// 14364)` ABI-drift guard is omitted here: Aeneas emits it as `def _`, which
// Lean rejects. It is a build-time layout check, not part of the parse leaf.)

#[repr(C)]
pub struct UvcParseResult {
    pub ret: i32,
    pub nformats_alloc: u32,
    pub nframes_alloc: u32,
    pub nintervals_alloc: u32,
    pub nformats: u32,
    pub nframes: u32,
    pub nintervals: u32,
    pub formats: [UvcFormatOut; UVC_MAX_FORMATS],
    pub frames: [UvcFrameOut; UVC_MAX_FRAMES],
    pub intervals: [u32; UVC_MAX_INTERVALS],
}

// ======================================================================
// Constants (values identical to the kernel headers).
// ======================================================================

const USB_DT_CS_INTERFACE: u8 = 0x24;

const UVC_VS_FORMAT_UNCOMPRESSED: u8 = 0x04;
const UVC_VS_FRAME_UNCOMPRESSED: u8 = 0x05;
const UVC_VS_FORMAT_MJPEG: u8 = 0x06;
const UVC_VS_FRAME_MJPEG: u8 = 0x07;
const UVC_VS_FORMAT_MPEG2TS: u8 = 0x0a;
const UVC_VS_FORMAT_DV: u8 = 0x0c;
const UVC_VS_COLORFORMAT: u8 = 0x0d;
const UVC_VS_FORMAT_FRAME_BASED: u8 = 0x10;
const UVC_VS_FRAME_FRAME_BASED: u8 = 0x11;
const UVC_VS_FORMAT_STREAM_BASED: u8 = 0x12;
const UVC_VS_STILL_IMAGE_FRAME: u8 = 0x03;

const UVC_QUIRK_RESTRICT_FRAME_RATE: u32 = 0x0000_0200;
const UVC_QUIRK_FORCE_Y8: u32 = 0x0000_0800;
const UVC_QUIRK_FORCE_BPP: u32 = 0x0000_1000;
const UVC_FMT_FLAG_COMPRESSED: u32 = 0x0000_0001;
const UVC_FMT_FLAG_STREAM: u32 = 0x0000_0002;

// enum v4l2_colorspace / xfer_func / ycbcr_encoding values used below.
const V4L2_COLORSPACE_SMPTE170M: i32 = 1;
const V4L2_COLORSPACE_SMPTE240M: i32 = 2;
const V4L2_COLORSPACE_470_SYSTEM_M: i32 = 5;
const V4L2_COLORSPACE_470_SYSTEM_BG: i32 = 6;
const V4L2_COLORSPACE_SRGB: i32 = 8;

const V4L2_XFER_FUNC_DEFAULT: i32 = 0;
const V4L2_XFER_FUNC_709: i32 = 1;
const V4L2_XFER_FUNC_SRGB: i32 = 2;
const V4L2_XFER_FUNC_SMPTE240M: i32 = 4;
const V4L2_XFER_FUNC_NONE: i32 = 5;

const V4L2_YCBCR_ENC_DEFAULT: i32 = 0;
const V4L2_YCBCR_ENC_601: i32 = 1;
const V4L2_YCBCR_ENC_709: i32 = 2;
const V4L2_YCBCR_ENC_SMPTE240M: i32 = 8;

const EINVAL: i32 = 22;
const ENOMEM: i32 = 12;

const fn fourcc(a: u8, b: u8, c: u8, d: u8) -> u32 {
    (a as u32) | ((b as u32) << 8) | ((c as u32) << 16) | ((d as u32) << 24)
}

const V4L2_PIX_FMT_YUYV: u32 = fourcc(b'Y', b'U', b'Y', b'V');
const V4L2_PIX_FMT_NV12: u32 = fourcc(b'N', b'V', b'1', b'2');
const V4L2_PIX_FMT_MJPEG: u32 = fourcc(b'M', b'J', b'P', b'G');
const V4L2_PIX_FMT_YVU420: u32 = fourcc(b'Y', b'V', b'1', b'2');
const V4L2_PIX_FMT_YUV420: u32 = fourcc(b'Y', b'U', b'1', b'2');
const V4L2_PIX_FMT_M420: u32 = fourcc(b'M', b'4', b'2', b'0');
const V4L2_PIX_FMT_P010: u32 = fourcc(b'P', b'0', b'1', b'0');
const V4L2_PIX_FMT_UYVY: u32 = fourcc(b'U', b'Y', b'V', b'Y');
const V4L2_PIX_FMT_GREY: u32 = fourcc(b'G', b'R', b'E', b'Y');
const V4L2_PIX_FMT_Y10: u32 = fourcc(b'Y', b'1', b'0', b' ');
const V4L2_PIX_FMT_Y12: u32 = fourcc(b'Y', b'1', b'2', b' ');
const V4L2_PIX_FMT_Y16: u32 = fourcc(b'Y', b'1', b'6', b' ');
const V4L2_PIX_FMT_SBGGR8: u32 = fourcc(b'B', b'A', b'8', b'1');
const V4L2_PIX_FMT_SGBRG8: u32 = fourcc(b'G', b'B', b'R', b'G');
const V4L2_PIX_FMT_SGRBG8: u32 = fourcc(b'G', b'R', b'B', b'G');
const V4L2_PIX_FMT_SRGGB8: u32 = fourcc(b'R', b'G', b'G', b'B');
const V4L2_PIX_FMT_RGB565: u32 = fourcc(b'R', b'G', b'B', b'P');
const V4L2_PIX_FMT_BGR24: u32 = fourcc(b'B', b'G', b'R', b'3');
const V4L2_PIX_FMT_XBGR32: u32 = fourcc(b'X', b'R', b'2', b'4');
const V4L2_PIX_FMT_H264: u32 = fourcc(b'H', b'2', b'6', b'4');
const V4L2_PIX_FMT_HEVC: u32 = fourcc(b'H', b'E', b'V', b'C');
const V4L2_PIX_FMT_Y8I: u32 = fourcc(b'Y', b'8', b'I', b' ');
const V4L2_PIX_FMT_Y12I: u32 = fourcc(b'Y', b'1', b'2', b'I');
const V4L2_PIX_FMT_Y16I: u32 = fourcc(b'Y', b'1', b'6', b'I');
const V4L2_PIX_FMT_Z16: u32 = fourcc(b'Z', b'1', b'6', b' ');
const V4L2_PIX_FMT_SRGGB10P: u32 = fourcc(b'p', b'R', b'A', b'A');
const V4L2_PIX_FMT_SBGGR16: u32 = fourcc(b'B', b'Y', b'R', b'2');
const V4L2_PIX_FMT_SGBRG16: u32 = fourcc(b'G', b'B', b'1', b'6');
const V4L2_PIX_FMT_SRGGB16: u32 = fourcc(b'R', b'G', b'1', b'6');
const V4L2_PIX_FMT_SGRBG16: u32 = fourcc(b'G', b'R', b'1', b'6');
const V4L2_PIX_FMT_DV: u32 = fourcc(b'd', b'v', b's', b'd');
const V4L2_PIX_FMT_INZI: u32 = fourcc(b'I', b'N', b'Z', b'I');
const V4L2_PIX_FMT_CNF4: u32 = fourcc(b'C', b'N', b'F', b'4');

// ======================================================================
// Format GUID table (drivers/media/common/uvc.c:14-193), values identical.
// ======================================================================

// `Copy` so the lookup can copy an entry to a local (`let fd = UVC_FMTS[i];`)
// and read `fd.guid[j]` without borrowing a field of a borrowed slice element
// (a nested borrow Aeneas rejects). FormatDesc is plain POD, so Copy is inert.
#[derive(Clone, Copy)]
struct FormatDesc {
    guid: [u8; 16],
    fcc: u32,
}

macro_rules! guid {
    ($($b:expr),* $(,)?) => { [$($b),*] };
}

// A fixed-size array (not `&[FormatDesc]`): indexing a slice-behind-a-
// reference is a nested borrow Aeneas rejects; indexing an array global is not.
#[rustfmt::skip]
static UVC_FMTS: [FormatDesc; 41] = [
    FormatDesc { guid: guid![b'Y',b'U',b'Y',b'2',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_YUYV },
    FormatDesc { guid: guid![b'Y',b'U',b'Y',b'2',0,0,0x10,0,0x80,0,0,0x00,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_YUYV },   // YUY2_ISIGHT
    FormatDesc { guid: guid![b'N',b'V',b'1',b'2',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_NV12 },
    FormatDesc { guid: guid![b'M',b'J',b'P',b'G',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_MJPEG },
    FormatDesc { guid: guid![b'Y',b'V',b'1',b'2',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_YVU420 },
    FormatDesc { guid: guid![b'I',b'4',b'2',b'0',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_YUV420 },
    FormatDesc { guid: guid![b'M',b'4',b'2',b'0',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_M420 },
    FormatDesc { guid: guid![b'P',b'0',b'1',b'0',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_P010 },
    FormatDesc { guid: guid![b'U',b'Y',b'V',b'Y',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_UYVY },
    FormatDesc { guid: guid![b'Y',b'8',b'0',b'0',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_GREY },   // Y800
    FormatDesc { guid: guid![b'Y',b'8',b' ',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_GREY },   // Y8
    FormatDesc { guid: guid![0x32,0,0,0,0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71],          fcc: V4L2_PIX_FMT_GREY },   // D3DFMT_L8
    FormatDesc { guid: guid![0x32,0,0,0,0x02,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71],       fcc: V4L2_PIX_FMT_GREY },   // KSMEDIA_L8_IR
    FormatDesc { guid: guid![b'Y',b'1',b'0',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Y10 },
    FormatDesc { guid: guid![b'Y',b'1',b'2',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Y12 },
    FormatDesc { guid: guid![b'Y',b'1',b'6',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Y16 },
    FormatDesc { guid: guid![b'B',b'Y',b'8',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SBGGR8 }, // BY8
    FormatDesc { guid: guid![b'B',b'A',b'8',b'1',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SBGGR8 }, // BA81
    FormatDesc { guid: guid![b'G',b'B',b'R',b'G',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SGBRG8 },
    FormatDesc { guid: guid![b'G',b'R',b'B',b'G',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SGRBG8 },
    FormatDesc { guid: guid![b'R',b'G',b'G',b'B',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SRGGB8 },
    FormatDesc { guid: guid![b'R',b'G',b'B',b'P',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_RGB565 }, // RGBP
    FormatDesc { guid: guid![0x7b,0xeb,0x36,0xe4,0x4f,0x52,0xce,0x11,0x9f,0x53,0,0x20,0xaf,0x0b,0xa7,0x70], fcc: V4L2_PIX_FMT_RGB565 }, // D3DFMT_R5G6B5
    FormatDesc { guid: guid![0x7d,0xeb,0x36,0xe4,0x4f,0x52,0xce,0x11,0x9f,0x53,0,0x20,0xaf,0x0b,0xa7,0x70], fcc: V4L2_PIX_FMT_BGR24 },  // BGR3
    FormatDesc { guid: guid![0x7e,0xeb,0x36,0xe4,0x4f,0x52,0xce,0x11,0x9f,0x53,0,0x20,0xaf,0x0b,0xa7,0x70], fcc: V4L2_PIX_FMT_XBGR32 }, // BGR4
    FormatDesc { guid: guid![b'H',b'2',b'6',b'4',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_H264 },
    FormatDesc { guid: guid![b'H',b'2',b'6',b'5',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_HEVC },   // H265
    FormatDesc { guid: guid![b'Y',b'8',b'I',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Y8I },
    FormatDesc { guid: guid![b'Y',b'1',b'2',b'I',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Y12I },
    FormatDesc { guid: guid![b'Y',b'1',b'6',b'I',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Y16I },
    FormatDesc { guid: guid![b'Z',b'1',b'6',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_Z16 },
    FormatDesc { guid: guid![b'R',b'W',b'1',b'0',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SRGGB10P }, // RW10
    FormatDesc { guid: guid![b'B',b'G',b'1',b'6',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SBGGR16 }, // BG16
    FormatDesc { guid: guid![b'G',b'B',b'1',b'6',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SGBRG16 }, // GB16
    FormatDesc { guid: guid![b'R',b'G',b'1',b'6',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SRGGB16 }, // RG16
    FormatDesc { guid: guid![b'G',b'R',b'1',b'6',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_SGRBG16 }, // GR16
    FormatDesc { guid: guid![b'I',b'N',b'V',b'Z',0x90,0x2d,0x58,0x4a,0x92,0x0b,0x77,0x3f,0x1f,0x2c,0x55,0x6b], fcc: V4L2_PIX_FMT_Z16 },  // INVZ
    FormatDesc { guid: guid![b'I',b'N',b'V',b'I',0xdb,0x57,0x49,0x5e,0x8e,0x3f,0xf4,0x79,0x53,0x2b,0x94,0x6f], fcc: V4L2_PIX_FMT_Y10 },  // INVI
    FormatDesc { guid: guid![b'I',b'N',b'Z',b'I',0x66,0x1a,0x42,0xa2,0x90,0x65,0xd0,0x18,0x14,0xa8,0xef,0x8a], fcc: V4L2_PIX_FMT_INZI }, // INZI
    FormatDesc { guid: guid![b'C',b' ',b' ',b' ',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_CNF4 },   // CNF4
    FormatDesc { guid: guid![b'H',b'E',b'V',b'C',0,0,0x10,0,0x80,0,0,0xaa,0,0x38,0x9b,0x71], fcc: V4L2_PIX_FMT_HEVC },
];

// EXTRACTION NOTE: the shipping crate writes `UVC_FMTS.iter().find(|f| f.guid
// == guid[..16])`. Three semantics-preserving changes make this translate
// under Aeneas (none change behaviour; the result is also closer to the kernel
// C's `for i in 0..len { if memcmp(...) }`):
//   1. explicit indexed loop instead of `Iterator::find` (not modelled);
//   2. return the fcc by value (`Option<u32>`) instead of `Option<&FormatDesc>`
//      (Aeneas rejects a borrow nested inside an Option);
//   3. compare bytes inline via `UVC_FMTS[i].guid[j]` (u8 copies read through
//      the slice) instead of taking `&UVC_FMTS[i].guid` (a borrow nested inside
//      the already-borrowed static slice, which Aeneas rejects).
// Single-loop byte compare, `a` taken by value (Copy array, no borrow). Split
// out of the lookup so each function has exactly one loop: Aeneas failed to
// compute a borrow fixed point for the two nested loops in a single function.
fn guid_eq16(a: [u8; 16], b: &[u8]) -> bool {
    let mut j = 0;
    let mut matched = true;
    while j < 16 {
        if a[j] != b[j] {
            matched = false;
        }
        j += 1;
    }
    matched
}

fn uvc_format_by_guid(guid: &[u8]) -> Option<u32> {
    // guid is a &buffer[5..], guaranteed >= 16 bytes by the caller's buflen
    // check (buflen >= 27 for uncompressed / 28 for frame-based).
    let mut i = 0;
    while i < UVC_FMTS.len() {
        let fd = UVC_FMTS[i]; // Copy the entry out; read fields from the local.
        if guid_eq16(fd.guid, guid) {
            return Some(fd.fcc);
        }
        i += 1;
    }
    None
}

// ======================================================================
// Pure helpers, uvc_driver.c:62-131 (table lookups, identical semantics).
// ======================================================================

fn uvc_colorspace(primaries: u8) -> i32 {
    const COLORPRIMARIES: [i32; 6] = [
        V4L2_COLORSPACE_SRGB,
        V4L2_COLORSPACE_SRGB,
        V4L2_COLORSPACE_470_SYSTEM_M,
        V4L2_COLORSPACE_470_SYSTEM_BG,
        V4L2_COLORSPACE_SMPTE170M,
        V4L2_COLORSPACE_SMPTE240M,
    ];
    match COLORPRIMARIES.get(primaries as usize) {
        Some(&c) => c,
        None => V4L2_COLORSPACE_SRGB,
    }
}

fn uvc_xfer_func(transfer_characteristics: u8) -> i32 {
    const XFER_FUNCS: [i32; 8] = [
        V4L2_XFER_FUNC_DEFAULT,
        V4L2_XFER_FUNC_709,
        V4L2_XFER_FUNC_709,
        V4L2_XFER_FUNC_709,
        V4L2_XFER_FUNC_709,
        V4L2_XFER_FUNC_SMPTE240M,
        V4L2_XFER_FUNC_NONE,
        V4L2_XFER_FUNC_SRGB,
    ];
    match XFER_FUNCS.get(transfer_characteristics as usize) {
        Some(&c) => c,
        None => V4L2_XFER_FUNC_DEFAULT,
    }
}

fn uvc_ycbcr_enc(matrix_coefficients: u8) -> i32 {
    const YCBCR_ENCS: [i32; 6] = [
        V4L2_YCBCR_ENC_DEFAULT,
        V4L2_YCBCR_ENC_709,
        V4L2_YCBCR_ENC_601,
        V4L2_YCBCR_ENC_601,
        V4L2_YCBCR_ENC_601,
        V4L2_YCBCR_ENC_SMPTE240M,
    ];
    match YCBCR_ENCS.get(matrix_coefficients as usize) {
        Some(&c) => c,
        None => V4L2_YCBCR_ENC_DEFAULT,
    }
}

/// DEVIATION: `v4l2_format_info()` is a v4l2-core helper unrelated to UVC
/// parsing; stubbed to `None` exactly as in the C extraction, so the
/// `UVC_QUIRK_FORCE_BPP` recompute branch is inert on both sides.
fn v4l2_format_info(_fcc: u32) -> Option<()> {
    None
}

// ======================================================================
// Internal parse state — the memory-safe replacement for the single
// kzalloc'd formats/frames/intervals block.
// ======================================================================

#[derive(Default, Clone)]
struct UvcFormat {
    type_: u8,
    index: u8,
    bpp: u8,
    colorspace: i32,
    xfer_func: i32,
    ycbcr_enc: i32,
    fcc: u32,
    flags: u32,
    nframes: u32,
    // Offset into ParseState.frames where this format's frames begin
    // (the C `format->frames` pointer, as an index).
    frame_base: usize,
}

#[derive(Default, Clone)]
struct UvcFrame {
    b_frame_index: u8,
    bm_capabilities: u8,
    w_width: u16,
    w_height: u16,
    dw_min_bit_rate: u32,
    dw_max_bit_rate: u32,
    dw_max_video_frame_buffer_size: u32,
    b_frame_interval_type: u8,
    dw_default_frame_interval: u32,
    // Offset into ParseState.intervals where dwFrameInterval points
    // (the C `frame->dwFrameInterval` pointer, as an index). -1 if unset.
    interval_base: i32,
}

/// Little-endian unaligned reads (asm/unaligned.h). Bounds-checked: the caller
/// has always validated `buflen` so these are in range for well-formed input;
/// an out-of-bounds read here is a real defect and panics (vs C's UB).
fn le16(buf: &[u8], at: usize) -> u16 {
    (buf[at] as u16) | ((buf[at + 1] as u16) << 8)
}
fn le32(buf: &[u8], at: usize) -> u32 {
    (buf[at] as u32)
        | ((buf[at + 1] as u32) << 8)
        | ((buf[at + 2] as u32) << 16)
        | ((buf[at + 3] as u32) << 24)
}

/// kernel `clamp(val, lo, hi) == min(max(val, lo), hi)`, reproduced exactly
/// including the `lo > hi` case malformed descriptors can produce.
fn clamp_u32(val: u32, lo: u32, hi: u32) -> u32 {
    val.max(lo).min(hi)
}

struct ParseState {
    frames: Vec<UvcFrame>,
    intervals: Vec<u32>,
    interval_cursor: usize,
}

impl ParseState {
    /// Port of `uvc_parse_frame` (uvc_driver.c:227-333).
    ///
    /// `frame_idx` is the absolute index into `self.frames` that the C code
    /// reaches via `&frames[format->nframes]`. Returns bytes consumed
    /// (`buffer[0]`) or `-EINVAL`.
    fn uvc_parse_frame(
        &mut self,
        dev_quirks: u32,
        format: &UvcFormat,
        frame_idx: usize,
        ftype: u8,
        width_multiplier: i32,
        buf: &[u8],
        pos: usize,
        buflen: i32,
    ) -> i32 {
        let n: u32 = if ftype != UVC_VS_FRAME_FRAME_BASED {
            if buflen > 25 { buf[pos + 25] as u32 } else { 0 }
        } else if buflen > 21 {
            buf[pos + 21] as u32
        } else {
            0
        };

        let n: u32 = if n != 0 { n } else { 3 };

        // Unsigned comparison, matching C's promotion of `buflen` (int) against
        // `26 + 4*n` (unsigned int).
        if (buflen as u32) < 26 + 4 * n {
            return -EINVAL;
        }

        // Build the frame into a local, then commit into self.frames. This
        // avoids borrowing self.frames and self.intervals simultaneously; the
        // written values are identical to the C field-by-field writes.
        let mut frame = UvcFrame::default();

        frame.b_frame_index = buf[pos + 3];
        frame.bm_capabilities = buf[pos + 4];
        // (u16 as i32) * (width_multiplier: i32), truncated back to u16 — same
        // as the C assignment to the u16 field.
        frame.w_width = (le16(buf, pos + 5) as i32).wrapping_mul(width_multiplier) as u16;
        frame.w_height = le16(buf, pos + 7);
        frame.dw_min_bit_rate = le32(buf, pos + 9);
        frame.dw_max_bit_rate = le32(buf, pos + 13);
        if ftype != UVC_VS_FRAME_FRAME_BASED {
            frame.dw_max_video_frame_buffer_size = le32(buf, pos + 17);
            frame.dw_default_frame_interval = le32(buf, pos + 21);
            frame.b_frame_interval_type = buf[pos + 25];
        } else {
            frame.dw_max_video_frame_buffer_size = 0;
            frame.dw_default_frame_interval = le32(buf, pos + 17);
            frame.b_frame_interval_type = buf[pos + 21];
        }

        // Copy the frame intervals. The C captures `*intervals` as the base
        // (here: interval_cursor), fills n slots, then advances by n.
        let iv_base = self.interval_cursor;
        frame.interval_base = iv_base as i32;

        for i in 0..n as usize {
            let interval = le32(buf, pos + 26 + 4 * i);
            // Bounds-checked write into the counting-pass-sized interval Vec;
            // an over-run here is the OOB-write CVE class -> panic (vs C UB).
            self.intervals[iv_base + i] = if interval != 0 { interval } else { 1 };
        }

        // Uncompressed: recompute the buffer size.
        //
        // DEVIATION (signed-overflow UB site). The C is
        // `bpp * wWidth * wHeight / 8` in 32-bit `int` arithmetic. The product
        // can exceed INT_MAX, which is signed-overflow *undefined behaviour* in
        // C, so the result is whatever the compiler emits. clang at -O1 (the
        // build the differential fuzzer links) assumes the operands are
        // non-negative and no overflow occurs, and emits `imul; imul; shrl $3`
        // — a 32-bit wrapping multiply followed by an UNSIGNED shift-right by 3.
        // We reproduce exactly that so the Rust faithfully models the compiled
        // C. (Phase 2 originally used a signed `/8`; the differential fuzzer
        // caught the mismatch on the first run — see fuzz/RESULTS.md.) The
        // value is only meaningful for well-formed, non-overflowing descriptors;
        // this convergence is with the clang-compiled C specifically.
        if format.flags & UVC_FMT_FLAG_COMPRESSED == 0 {
            let prod = (format.bpp as u32)
                .wrapping_mul(frame.w_width as u32)
                .wrapping_mul(frame.w_height as u32);
            frame.dw_max_video_frame_buffer_size = prod >> 3;
        }

        // Clamp the default interval. Reads dwFrameInterval[0] and
        // dwFrameInterval[maxIntervalIndex]; both indices are < n for
        // well-formed input, and bounds-checked otherwise.
        let max_interval_index: usize = if frame.b_frame_interval_type != 0 {
            (n - 1) as usize
        } else {
            1
        };
        frame.dw_default_frame_interval = clamp_u32(
            frame.dw_default_frame_interval,
            self.intervals[iv_base],
            self.intervals[iv_base + max_interval_index],
        );

        if dev_quirks & UVC_QUIRK_RESTRICT_FRAME_RATE != 0 {
            frame.b_frame_interval_type = 1;
            self.intervals[iv_base] = frame.dw_default_frame_interval;
        }

        // (uvc_dbg fps division is a no-op here, exactly as the stubbed C.)

        self.interval_cursor += n as usize;

        // Commit the frame. In C this write happened field-by-field directly
        // into frames[format->nframes]; same destination, same values.
        self.frames[frame_idx] = frame;

        buf[pos] as i32
    }

    /// Port of `uvc_parse_format` (uvc_driver.c:335-530).
    ///
    /// `format` is this format's fresh (zeroed) struct; `frame_base` is the
    /// absolute index into `self.frames` for its frames (the C `frames` arg).
    /// Returns bytes consumed, 0 for "unknown format, skip", or `-EINVAL`.
    // The final `buflen -=` in the color-format branch is a dead store, kept
    // to mirror the C (`buflen -= buffer[0]`) line-for-line.
    #[allow(unused_assignments)]
    fn uvc_parse_format(
        &mut self,
        dev_quirks: u32,
        format: &mut UvcFormat,
        frame_base: usize,
        buf: &[u8],
        start_pos: usize,
        start_buflen: i32,
    ) -> i32 {
        let mut pos = start_pos;
        let mut buflen = start_buflen;
        let mut width_multiplier: i32 = 1;
        let ftype: u8;

        if buflen < 4 {
            return -EINVAL;
        }

        format.type_ = buf[pos + 2];
        format.index = buf[pos + 3];
        format.frame_base = frame_base;

        match buf[pos + 2] {
            UVC_VS_FORMAT_UNCOMPRESSED | UVC_VS_FORMAT_FRAME_BASED => {
                let n: u32 = if buf[pos + 2] == UVC_VS_FORMAT_UNCOMPRESSED { 27 } else { 28 };
                if (buflen as u32) < n {
                    return -EINVAL;
                }

                let fmt_fcc = match uvc_format_by_guid(&buf[pos + 5..]) {
                    Some(fcc) => fcc,
                    None => {
                        // Unknown video formats are not fatal; caller skips.
                        return 0;
                    }
                };

                format.fcc = fmt_fcc;
                format.bpp = buf[pos + 21];

                if dev_quirks & UVC_QUIRK_FORCE_Y8 != 0 && format.fcc == V4L2_PIX_FMT_YUYV {
                    format.fcc = V4L2_PIX_FMT_GREY;
                    format.bpp = 8;
                    width_multiplier = 2;
                }

                if dev_quirks & UVC_QUIRK_FORCE_BPP != 0 {
                    // v4l2_format_info is stubbed to None (see above), so this
                    // branch never recomputes bpp in the spike.
                    if let Some(_info) = v4l2_format_info(format.fcc) {
                        unreachable!("v4l2_format_info is stubbed to None");
                    }
                }

                if buf[pos + 2] == UVC_VS_FORMAT_UNCOMPRESSED {
                    ftype = UVC_VS_FRAME_UNCOMPRESSED;
                } else {
                    ftype = UVC_VS_FRAME_FRAME_BASED;
                    if buf[pos + 27] != 0 {
                        format.flags = UVC_FMT_FLAG_COMPRESSED;
                    }
                }
            }

            UVC_VS_FORMAT_MJPEG => {
                if buflen < 11 {
                    return -EINVAL;
                }
                format.fcc = V4L2_PIX_FMT_MJPEG;
                format.flags = UVC_FMT_FLAG_COMPRESSED;
                format.bpp = 0;
                ftype = UVC_VS_FRAME_MJPEG;
            }

            UVC_VS_FORMAT_DV => {
                if buflen < 9 {
                    return -EINVAL;
                }
                if (buf[pos + 8] & 0x7f) > 2 {
                    return -EINVAL;
                }
                format.fcc = V4L2_PIX_FMT_DV;
                format.flags = UVC_FMT_FLAG_COMPRESSED | UVC_FMT_FLAG_STREAM;
                format.bpp = 0;
                ftype = 0;

                // Create a dummy frame descriptor at frames[frame_base + 0].
                let mut frame = UvcFrame::default();
                frame.b_frame_interval_type = 1;
                frame.dw_default_frame_interval = 1;
                frame.interval_base = self.interval_cursor as i32;
                // *(*intervals)++ = 1;
                self.intervals[self.interval_cursor] = 1;
                self.interval_cursor += 1;
                self.frames[frame_base] = frame;
                format.nframes = 1;
            }

            // MPEG2TS / STREAM_BASED / anything else: unsupported.
            UVC_VS_FORMAT_MPEG2TS | UVC_VS_FORMAT_STREAM_BASED | _ => {
                return -EINVAL;
            }
        }

        // buflen -= buffer[0]; buffer += buffer[0];
        buflen -= buf[pos] as i32;
        pos += buf[pos] as usize;

        // Parse the frame descriptors (uncompressed, MJPEG, frame-based only).
        //
        // EXTRACTION NOTE: the shipping crate does `if ret < 0 { return ret; }`
        // inside this loop. Aeneas does not support early `return` inside a
        // loop, so the verify copy records the error and `break`s, then returns
        // after the loop — control-flow identical (the loop does no further
        // work after a negative ret).
        if ftype != 0 {
            let mut frame_err: i32 = 0;
            while buflen > 2
                && buf[pos + 1] == USB_DT_CS_INTERFACE
                && buf[pos + 2] == ftype
            {
                let frame_idx = frame_base + format.nframes as usize;
                let ret = self.uvc_parse_frame(
                    dev_quirks,
                    format,
                    frame_idx,
                    ftype,
                    width_multiplier,
                    buf,
                    pos,
                    buflen,
                );
                if ret < 0 {
                    frame_err = ret;
                    break;
                }
                format.nframes += 1;
                buflen -= ret;
                pos += ret as usize;
            }
            if frame_err < 0 {
                return frame_err;
            }
        }

        if buflen > 2
            && buf[pos + 1] == USB_DT_CS_INTERFACE
            && buf[pos + 2] == UVC_VS_STILL_IMAGE_FRAME
        {
            buflen -= buf[pos] as i32;
            pos += buf[pos] as usize;
        }

        if buflen > 2
            && buf[pos + 1] == USB_DT_CS_INTERFACE
            && buf[pos + 2] == UVC_VS_COLORFORMAT
        {
            if buflen < 6 {
                return -EINVAL;
            }
            format.colorspace = uvc_colorspace(buf[pos + 3]);
            format.xfer_func = uvc_xfer_func(buf[pos + 4]);
            format.ycbcr_enc = uvc_ycbcr_enc(buf[pos + 5]);
            buflen -= buf[pos] as i32;
            pos += buf[pos] as usize;
        } else {
            format.colorspace = V4L2_COLORSPACE_SRGB;
        }

        (pos - start_pos) as i32
    }
}

// ======================================================================
// Entry point — counting pass, allocation, driving loop, serialization.
// Ports uvc_parse_streaming.c:657-764 (header parsing excluded).
// ======================================================================

/// Native (Rust-ABI) entry point. The `#[no_mangle] extern "C" fn uvc_parse`
/// below is a thin wrapper over this; the differential fuzzer calls `parse`
/// directly so that a bounds-check panic *unwinds* (catchable) instead of
/// aborting at the C-ABI boundary (Rust >= 1.81 aborts panics across
/// `extern "C"`). Both paths write the identical `#[repr(C)]` result.
pub fn parse(buf: &[u8], quirks: u32, out: &mut UvcParseResult) -> i32 {
    // Zero the result (mirrors the C memset).
    out.ret = 0;
    out.nformats_alloc = 0;
    out.nframes_alloc = 0;
    out.nintervals_alloc = 0;
    out.nformats = 0;
    out.nframes = 0;
    out.nintervals = 0;
    out.formats = [UvcFormatOut::zeroed(); UVC_MAX_FORMATS];
    out.frames = [UvcFrameOut::zeroed(); UVC_MAX_FRAMES];
    out.intervals = [0u32; UVC_MAX_INTERVALS];

    let total = buf.len() as i32;

    // --- Counting pass (uvc_driver.c:660-703). ---
    let mut nformats: u32 = 0;
    let mut nframes: u32 = 0;
    let mut nintervals: u32 = 0;
    {
        let mut pos: usize = 0;
        let mut buflen: i32 = total;
        while buflen > 2 && buf[pos + 1] == USB_DT_CS_INTERFACE {
            match buf[pos + 2] {
                UVC_VS_FORMAT_UNCOMPRESSED | UVC_VS_FORMAT_MJPEG | UVC_VS_FORMAT_FRAME_BASED => {
                    nformats += 1;
                }
                UVC_VS_FORMAT_DV => {
                    nformats += 1;
                    nframes += 1;
                    nintervals += 1;
                }
                UVC_VS_FORMAT_MPEG2TS | UVC_VS_FORMAT_STREAM_BASED => {}
                UVC_VS_FRAME_UNCOMPRESSED | UVC_VS_FRAME_MJPEG => {
                    // SPIKE-VULN (negative control, `--features vuln`): mirror
                    // the C's `-DSPIKE_VULN` under-count so both sides carry
                    // the identical CVE-2024-53104-class bug. The C then writes
                    // out of bounds (UB / ASan abort); this Rust indexes an
                    // under-sized Vec and panics (memory-safe). See
                    // fuzz/RESULTS.md.
                    #[cfg(not(feature = "vuln"))]
                    {
                        nframes += 1;
                        if buflen > 25 {
                            nintervals +=
                                if buf[pos + 25] != 0 { buf[pos + 25] as u32 } else { 3 };
                        }
                    }
                }
                UVC_VS_FRAME_FRAME_BASED => {
                    nframes += 1;
                    if buflen > 21 {
                        nintervals += if buf[pos + 21] != 0 { buf[pos + 21] as u32 } else { 3 };
                    }
                }
                _ => {}
            }
            buflen -= buf[pos] as i32;
            pos += buf[pos] as usize;
        }
    }

    if nformats == 0 {
        out.ret = -EINVAL;
        return -EINVAL;
    }

    // --- Allocation. The counting pass sizes these exactly; over-running
    // them is the CVE class and panics here (vs the C's silent OOB). ---
    if nformats as usize > (u32::MAX as usize) {
        out.ret = -ENOMEM;
        return -ENOMEM;
    }
    let mut state = ParseState {
        frames: vec![UvcFrame::default(); nframes as usize],
        intervals: vec![0u32; nintervals as usize],
        interval_cursor: 0,
    };
    let mut formats: Vec<UvcFormat> = Vec::with_capacity(nformats as usize);

    out.nformats_alloc = nformats;
    out.nframes_alloc = nframes;
    out.nintervals_alloc = nintervals;

    // --- Driving loop (uvc_driver.c:736-764). ---
    let mut pos: usize = 0;
    let mut buflen: i32 = total;
    let mut frame_base: usize = 0; // running total of committed frames
    let mut ret: i32 = -EINVAL;

    while buflen > 2 && buf[pos + 1] == USB_DT_CS_INTERFACE {
        match buf[pos + 2] {
            UVC_VS_FORMAT_UNCOMPRESSED
            | UVC_VS_FORMAT_MJPEG
            | UVC_VS_FORMAT_DV
            | UVC_VS_FORMAT_FRAME_BASED => {
                let mut format = UvcFormat::default();
                ret = state.uvc_parse_format(quirks, &mut format, frame_base, buf, pos, buflen);
                if ret < 0 {
                    break;
                }
                if ret == 0 {
                    // Unknown format: skip this descriptor (fall through).
                    buflen -= buf[pos] as i32;
                    pos += buf[pos] as usize;
                    continue;
                }
                frame_base += format.nframes as usize;
                formats.push(format);
                buflen -= ret;
                pos += ret as usize;
                continue;
            }
            _ => {}
        }
        buflen -= buf[pos] as i32;
        pos += buf[pos] as usize;
    }

    if ret >= 0 {
        ret = formats.len() as i32;
    }
    out.ret = ret;

    // --- Serialize into the flat result. ---
    let nf = formats.len().min(UVC_MAX_FORMATS);
    let total_frames = frame_base.min(UVC_MAX_FRAMES);
    let total_intervals = state.interval_cursor.min(UVC_MAX_INTERVALS);

    out.nformats = nf as u32;
    out.nframes = total_frames as u32;
    out.nintervals = total_intervals as u32;

    for (i, f) in formats.iter().take(nf).enumerate() {
        out.formats[i] = UvcFormatOut {
            type_: f.type_,
            index: f.index,
            bpp: f.bpp,
            colorspace: f.colorspace,
            xfer_func: f.xfer_func,
            ycbcr_enc: f.ycbcr_enc,
            fcc: f.fcc,
            flags: f.flags,
            nframes: f.nframes,
            frame_base: f.frame_base as i32,
        };
    }
    for i in 0..total_frames {
        let f = &state.frames[i];
        out.frames[i] = UvcFrameOut {
            b_frame_index: f.b_frame_index,
            bm_capabilities: f.bm_capabilities,
            w_width: f.w_width,
            w_height: f.w_height,
            dw_min_bit_rate: f.dw_min_bit_rate,
            dw_max_bit_rate: f.dw_max_bit_rate,
            dw_max_video_frame_buffer_size: f.dw_max_video_frame_buffer_size,
            b_frame_interval_type: f.b_frame_interval_type,
            dw_default_frame_interval: f.dw_default_frame_interval,
            interval_base: f.interval_base,
        };
    }
    out.intervals[..total_intervals].copy_from_slice(&state.intervals[..total_intervals]);

    ret
}

impl UvcFormatOut {
    const fn zeroed() -> Self {
        UvcFormatOut {
            type_: 0,
            index: 0,
            bpp: 0,
            colorspace: 0,
            xfer_func: 0,
            ycbcr_enc: 0,
            fcc: 0,
            flags: 0,
            nframes: 0,
            frame_base: 0,
        }
    }
}
impl UvcFrameOut {
    const fn zeroed() -> Self {
        UvcFrameOut {
            b_frame_index: 0,
            bm_capabilities: 0,
            w_width: 0,
            w_height: 0,
            dw_min_bit_rate: 0,
            dw_max_bit_rate: 0,
            dw_max_video_frame_buffer_size: 0,
            b_frame_interval_type: 0,
            dw_default_frame_interval: 0,
            interval_base: 0,
        }
    }
}

// NOTE: the `#[no_mangle] extern "C" fn uvc_parse` FFI shell and the
// `#[cfg(test)]` module from the shipping crate are omitted here: the shell is
// the one unsafe (raw-pointer) boundary, which Aeneas cannot model; its
// obligation is discharged by inspection in VERIFY-REPORT.md. The verified
// leaf is the safe `parse` above.
