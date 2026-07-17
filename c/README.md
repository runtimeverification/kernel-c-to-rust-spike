# C leaf: the UVC format/frame descriptor parser

This directory extracts the Linux kernel's UVC videostreaming descriptor
parser into a standalone C library that compiles without the kernel tree and
exposes a single C-ABI entry point. The parsing logic is copied **byte-for-
byte** from kernel **v7.2-rc2**; only the kernel *environment* is stubbed, in
the spirit of the Binder spike (`~/kernel-rust-verification-spike`). Every
stub is marked `// SPIKE-STUB`.

This is the target because `uvc_parse_format` had two independent
memory-safety CVEs sixteen years apart:

- **CVE-2008-3496** — buffer overflow in the format/frame descriptor parsing.
- **CVE-2024-53104** — out-of-bounds write from a frame-count / allocation
  mismatch (`uvc_parse_format` writing more `uvc_frame` entries than the
  counting pass in `uvc_parse_streaming` had allocated).

Because CVE-2024-53104 lives in the *relationship* between the counting pass
that sizes the allocation and the parse pass that writes into it, the leaf we
extract deliberately includes both: the entry point runs the counting pass,
does the single sized allocation, then drives `uvc_parse_format`. The bug
class is reachable here, not abstracted away.

## What was copied, byte-for-byte

All from kernel v7.2-rc2. Line ranges are from the original files.

| Symbol | Kernel file | Lines |
|---|---|---|
| `uvc_colorspace` | `drivers/media/usb/uvc/uvc_driver.c` | 62–77 |
| `uvc_xfer_func` | `drivers/media/usb/uvc/uvc_driver.c` | 79–104 |
| `uvc_ycbcr_enc` | `drivers/media/usb/uvc/uvc_driver.c` | 106–131 |
| `uvc_parse_frame` | `drivers/media/usb/uvc/uvc_driver.c` | 227–333 |
| `uvc_parse_format` | `drivers/media/usb/uvc/uvc_driver.c` | 335–530 |
| counting pass + allocation + driving loop | `drivers/media/usb/uvc/uvc_driver.c` (`uvc_parse_streaming`) | 657–764 |
| `uvc_format_by_guid` + `uvc_fmts[]` table | `drivers/media/common/uvc.c` | 14–193 |
| `struct uvc_frame`, `struct uvc_format` | `drivers/media/usb/uvc/uvcvideo.h` | 265–290 |

No parsing arithmetic or control flow was changed. The two signed/unsigned
comparison warnings the compiler emits (`buflen < 26 + 4 * n`, `buflen < n`)
are the kernel's own comparisons and are left intact — they are part of the
behaviour under test, not a porting artifact.

## The entry point

```c
int32_t uvc_parse(const uint8_t *buffer, int32_t buflen, uint32_t quirks,
                  struct uvc_parse_result *out);
```

Declared in [`uvc_parse.h`](uvc_parse.h), which also defines the flat,
pointer-free `struct uvc_parse_result` used to compare C and Rust outputs.

- **Input**: `buffer`/`buflen` are the raw class-specific videostreaming
  descriptor bytes *positioned at the first FORMAT descriptor* (i.e. after the
  VS INPUT/OUTPUT header — see scope note below). `quirks` is `dev->quirks`,
  an input because two branches of `uvc_parse_format` depend on it
  (`UVC_QUIRK_FORCE_Y8`, `UVC_QUIRK_FORCE_BPP`, and
  `UVC_QUIRK_RESTRICT_FRAME_RATE` in `uvc_parse_frame`).
- **Output**: `*out` is fully overwritten. It records the counting-pass sizing
  (`nformats_alloc` / `nframes_alloc` / `nintervals_alloc`) and a flat copy of
  every scalar field the kernel writes into the format, frame, and interval
  arrays, with `frame_base` / `interval_base` offsets linking them. Two runs
  that agree on every field of this struct are behaviourally equivalent.
- **Return**: number of formats parsed (≥ 0), or a negative errno.

## What was stubbed (`// SPIKE-STUB`)

The environment only — never the parsing logic:

- **Kernel types** `u8/u16/u32` → `<stdint.h>` typedefs.
- **Kernel macros** `ARRAY_SIZE`, `DIV_ROUND_UP`, `ALIGN`, `PTR_ALIGN`,
  `clamp`, `get_unaligned_le16/32` → local definitions with identical
  semantics. `clamp` in particular is reproduced as `min(max(val, lo), hi)`,
  including its behaviour when a malformed descriptor makes `lo > hi`.
- **Slab allocator** `kzalloc` → `malloc` + zero. The size argument is still
  computed by the byte-for-byte kernel sizing; running the library under
  AddressSanitizer (`make asan`) is what turns the parser's out-of-bounds
  writes into hard failures.
- **Logging** `uvc_dbg` / `dev_info` / `dev_err` → no-ops. Their arguments
  (device numbers, interface numbers, the fps division) are therefore not
  evaluated, exactly as when kernel dynamic-debug is disabled.
- **v4l2 core** `v4l2_format_info()` → returns `NULL`. It lives in the v4l2
  core, not the UVC driver, and only the `UVC_QUIRK_FORCE_BPP` branch uses it.
  Stubbed identically on the Rust side, so the branch is inert on both and the
  differential test stays valid. This is the one place the extraction is not
  behaviourally faithful to the running kernel; it is faithful to itself.
- **USB/UVC device structs** → minimal stand-ins holding only the members the
  copied code dereferences (`streaming->intf->cur_altsetting`, `dev->quirks`).
  Everything else lived only inside the now-stubbed logging calls.
- **Constants** (`UVC_VS_*`, `UVC_QUIRK_*`, `UVC_FMT_FLAG_*`, the format
  GUIDs, the `V4L2_PIX_FMT_*` fourccs, the `v4l2_colorspace/xfer_func/
  ycbcr_encoding` enum values) → copied from the kernel headers with their
  original values.

## Scope note

The VS header parse (`UVC_VS_INPUT_HEADER` / `UVC_VS_OUTPUT_HEADER`, lines
605–655 of `uvc_parse_streaming`) is intentionally **not** included: it writes
into `streaming->header` and is not part of `uvc_parse_format`'s logic. The
entry point takes the buffer already advanced to the first FORMAT descriptor,
which is exactly where the counting pass and driving loop begin.

## Build

```sh
make            # libuvcparse_c.so + libuvcparse_c.a
make asan       # libuvcparse_c_asan.a, ASan+UBSan, for the differential fuzzer
```

Requires a C11/GNU11 compiler (gcc or clang). The copied code uses a few GNU C
idioms (`void *` arithmetic, `__alignof__`), so it is built as `-std=gnu11`.
