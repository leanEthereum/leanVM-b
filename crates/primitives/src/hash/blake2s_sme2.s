// BLAKE2s-256 over sixteen inputs at once, in SME2 streaming mode.
//
// Sixteen 32-bit lanes fill one 512-bit streaming vector, so a whole batch is
// one register per state word. Against the NEON backend this trades three of
// the four issue slots for four times the width, which cancels; the win is
// `xar`, which fuses each xor with its rotation, so a G function is ten
// instructions instead of sixteen. ZA carries the two transposes: the message
// goes in as sixteen rows and comes out as sixteen columns, and the digests
// leave the same way.
//
// NEON is illegal inside streaming mode, so everything from the loads to the
// digest stores lives here.
//
// uint64_t blake2s_hash16_sme2(
//     const uint8_t *const *inputs,   // x0, sixteen pointers
//     const uint32_t *state,          // x1, the chaining value, splatted
//     uint64_t t_offset,              // x2
//     uint64_t len,                   // x3, bytes per input, a nonzero multiple of 64
//     uint8_t *out,                   // x4, sixteen 32-byte digests
//     const uint32_t *iv);            // x5, the eight BLAKE2s IV words
//
// Returns the streaming vector length in 32-bit lanes. The caller must treat
// anything other than 16 as "nothing was written".
//
// ZA use:
//     ZA0.S   the message block, rows in, columns out
//     ZA1.S   the digest transpose
//     ZA2.S   the chaining value across blocks, rows 0..7

.text
.arch armv9-a+sme2
.p2align 6

// One input's 64-byte block into a ZA row. Rows 0..15 are addressed as a
// selector holding 0, 4, 8 or 12 plus a slice of 0..3.
.macro LOAD_ROW ptr_off, selector, slice
    ldr     x8, [x0, #\ptr_off]
    add     x8, x8, x10
    ld1w    { za0h.s[\selector, \slice] }, p0/z, [x8]
.endm

.macro COLUMN_G4 mx0, my0, mx1, my1, mx2, my2, mx3, my3
    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s

    add     z0.s, z0.s, \mx0
    add     z1.s, z1.s, \mx1
    add     z2.s, z2.s, \mx2
    add     z3.s, z3.s, \mx3

    xar     z12.s, z12.s, z0.s, #16
    xar     z13.s, z13.s, z1.s, #16
    xar     z14.s, z14.s, z2.s, #16
    xar     z15.s, z15.s, z3.s, #16

    add     z8.s, z8.s, z12.s
    add     z9.s, z9.s, z13.s
    add     z10.s, z10.s, z14.s
    add     z11.s, z11.s, z15.s

    xar     z4.s, z4.s, z8.s, #12
    xar     z5.s, z5.s, z9.s, #12
    xar     z6.s, z6.s, z10.s, #12
    xar     z7.s, z7.s, z11.s, #12

    add     z0.s, z0.s, z4.s
    add     z1.s, z1.s, z5.s
    add     z2.s, z2.s, z6.s
    add     z3.s, z3.s, z7.s

    add     z0.s, z0.s, \my0
    add     z1.s, z1.s, \my1
    add     z2.s, z2.s, \my2
    add     z3.s, z3.s, \my3

    xar     z12.s, z12.s, z0.s, #8
    xar     z13.s, z13.s, z1.s, #8
    xar     z14.s, z14.s, z2.s, #8
    xar     z15.s, z15.s, z3.s, #8

    add     z8.s, z8.s, z12.s
    add     z9.s, z9.s, z13.s
    add     z10.s, z10.s, z14.s
    add     z11.s, z11.s, z15.s

    xar     z4.s, z4.s, z8.s, #7
    xar     z5.s, z5.s, z9.s, #7
    xar     z6.s, z6.s, z10.s, #7
    xar     z7.s, z7.s, z11.s, #7

.endm

.macro DIAG_G4 mx0, my0, mx1, my1, mx2, my2, mx3, my3
    add     z0.s, z0.s, z5.s
    add     z1.s, z1.s, z6.s
    add     z2.s, z2.s, z7.s
    add     z3.s, z3.s, z4.s

    add     z0.s, z0.s, \mx0
    add     z1.s, z1.s, \mx1
    add     z2.s, z2.s, \mx2
    add     z3.s, z3.s, \mx3

    xar     z15.s, z15.s, z0.s, #16
    xar     z12.s, z12.s, z1.s, #16
    xar     z13.s, z13.s, z2.s, #16
    xar     z14.s, z14.s, z3.s, #16

    add     z10.s, z10.s, z15.s
    add     z11.s, z11.s, z12.s
    add     z8.s, z8.s, z13.s
    add     z9.s, z9.s, z14.s

    xar     z5.s, z5.s, z10.s, #12
    xar     z6.s, z6.s, z11.s, #12
    xar     z7.s, z7.s, z8.s, #12
    xar     z4.s, z4.s, z9.s, #12

    add     z0.s, z0.s, z5.s
    add     z1.s, z1.s, z6.s
    add     z2.s, z2.s, z7.s
    add     z3.s, z3.s, z4.s

    add     z0.s, z0.s, \my0
    add     z1.s, z1.s, \my1
    add     z2.s, z2.s, \my2
    add     z3.s, z3.s, \my3

    xar     z15.s, z15.s, z0.s, #8
    xar     z12.s, z12.s, z1.s, #8
    xar     z13.s, z13.s, z2.s, #8
    xar     z14.s, z14.s, z3.s, #8

    add     z10.s, z10.s, z15.s
    add     z11.s, z11.s, z12.s
    add     z8.s, z8.s, z13.s
    add     z9.s, z9.s, z14.s

    xar     z5.s, z5.s, z10.s, #7
    xar     z6.s, z6.s, z11.s, #7
    xar     z7.s, z7.s, z8.s, #7
    xar     z4.s, z4.s, z9.s, #7

.endm

.macro ROUND s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15
    COLUMN_G4 \s0, \s1, \s2, \s3, \s4, \s5, \s6, \s7
    DIAG_G4   \s8, \s9, \s10, \s11, \s12, \s13, \s14, \s15
.endm

.globl _blake2s_hash16_sme2
_blake2s_hash16_sme2:
    // Entering streaming mode zeroes the vector registers, d8-d15 included.
    stp     d8, d9, [sp, #-64]!
    stp     d10, d11, [sp, #16]
    stp     d12, d13, [sp, #32]
    stp     d14, d15, [sp, #48]

    smstart
    cntw    x9
    cmp     x9, #16
    b.ne    Lwrong_vl

    ptrue   p0.s                        // all sixteen lanes
    ptrue   p1.s, vl8                   // the eight words of one digest
    mov     w12, #0
    mov     w13, #4
    mov     w14, #8
    mov     w15, #12

    // h starts as the caller's chaining value, one splat per word, in ZA2.
    ld1rw   { z0.s }, p0/z, [x1]
    ld1rw   { z1.s }, p0/z, [x1, #4]
    ld1rw   { z2.s }, p0/z, [x1, #8]
    ld1rw   { z3.s }, p0/z, [x1, #12]
    ld1rw   { z4.s }, p0/z, [x1, #16]
    ld1rw   { z5.s }, p0/z, [x1, #20]
    ld1rw   { z6.s }, p0/z, [x1, #24]
    ld1rw   { z7.s }, p0/z, [x1, #28]
    mov     za2h.s[w12, 0:3], { z0.s - z3.s }
    mov     za2h.s[w13, 0:3], { z4.s - z7.s }

    lsr     x6, x3, #6                  // block count
    mov     x7, #0                      // block index
    mov     x10, #0                     // byte offset into every input
    mov     x11, x2                     // running byte counter t

Lblock:
    LOAD_ROW    0, w12, 0
    LOAD_ROW    8, w12, 1
    LOAD_ROW   16, w12, 2
    LOAD_ROW   24, w12, 3
    LOAD_ROW   32, w13, 0
    LOAD_ROW   40, w13, 1
    LOAD_ROW   48, w13, 2
    LOAD_ROW   56, w13, 3
    LOAD_ROW   64, w14, 0
    LOAD_ROW   72, w14, 1
    LOAD_ROW   80, w14, 2
    LOAD_ROW   88, w14, 3
    LOAD_ROW   96, w15, 0
    LOAD_ROW  104, w15, 1
    LOAD_ROW  112, w15, 2
    LOAD_ROW  120, w15, 3

    // Vertical reads transpose: z(16+w) holds word w of every lane.
    mov     { z16.s - z19.s }, za0v.s[w12, 0:3]
    mov     { z20.s - z23.s }, za0v.s[w13, 0:3]
    mov     { z24.s - z27.s }, za0v.s[w14, 0:3]
    mov     { z28.s - z31.s }, za0v.s[w15, 0:3]

    mov     { z0.s - z3.s }, za2h.s[w12, 0:3]
    mov     { z4.s - z7.s }, za2h.s[w13, 0:3]
    ld1rw   { z8.s },  p0/z, [x5]
    ld1rw   { z9.s },  p0/z, [x5, #4]
    ld1rw   { z10.s }, p0/z, [x5, #8]
    ld1rw   { z11.s }, p0/z, [x5, #12]

    add     x11, x11, #64               // t counts bytes fed so far
    ldr     w8, [x5, #16]
    eor     w8, w8, w11
    dup     z12.s, w8
    lsr     x16, x11, #32
    ldr     w17, [x5, #20]
    eor     w8, w17, w16
    dup     z13.s, w8
    add     x16, x7, #1
    cmp     x16, x6
    csetm   w17, eq                     // the last block inverts IV[6]
    ldr     w8, [x5, #24]
    eor     w8, w8, w17
    dup     z14.s, w8
    ld1rw   { z15.s }, p0/z, [x5, #28]

    ROUND   z16.s, z17.s, z18.s, z19.s, z20.s, z21.s, z22.s, z23.s, z24.s, z25.s, z26.s, z27.s, z28.s, z29.s, z30.s, z31.s
    ROUND   z30.s, z26.s, z20.s, z24.s, z25.s, z31.s, z29.s, z22.s, z17.s, z28.s, z16.s, z18.s, z27.s, z23.s, z21.s, z19.s
    ROUND   z27.s, z24.s, z28.s, z16.s, z21.s, z18.s, z31.s, z29.s, z26.s, z30.s, z19.s, z22.s, z23.s, z17.s, z25.s, z20.s
    ROUND   z23.s, z25.s, z19.s, z17.s, z29.s, z28.s, z27.s, z30.s, z18.s, z22.s, z21.s, z26.s, z20.s, z16.s, z31.s, z24.s
    ROUND   z25.s, z16.s, z21.s, z23.s, z18.s, z20.s, z26.s, z31.s, z30.s, z17.s, z27.s, z28.s, z22.s, z24.s, z19.s, z29.s
    ROUND   z18.s, z28.s, z22.s, z26.s, z16.s, z27.s, z24.s, z19.s, z20.s, z29.s, z23.s, z21.s, z31.s, z30.s, z17.s, z25.s
    ROUND   z28.s, z21.s, z17.s, z31.s, z30.s, z29.s, z20.s, z26.s, z16.s, z23.s, z22.s, z19.s, z25.s, z18.s, z24.s, z27.s
    ROUND   z29.s, z27.s, z23.s, z30.s, z28.s, z17.s, z19.s, z25.s, z21.s, z16.s, z31.s, z20.s, z24.s, z22.s, z18.s, z26.s
    ROUND   z22.s, z31.s, z30.s, z25.s, z27.s, z19.s, z16.s, z24.s, z28.s, z18.s, z29.s, z23.s, z17.s, z20.s, z26.s, z21.s
    ROUND   z26.s, z18.s, z24.s, z20.s, z23.s, z22.s, z17.s, z21.s, z31.s, z27.s, z25.s, z30.s, z19.s, z28.s, z29.s, z16.s

    // h ^= v[i] ^ v[i + 8]
    mov     { z16.s - z19.s }, za2h.s[w12, 0:3]
    mov     { z20.s - z23.s }, za2h.s[w13, 0:3]
    eor3    z16.d, z16.d, z0.d, z8.d
    eor3    z17.d, z17.d, z1.d, z9.d
    eor3    z18.d, z18.d, z2.d, z10.d
    eor3    z19.d, z19.d, z3.d, z11.d
    eor3    z20.d, z20.d, z4.d, z12.d
    eor3    z21.d, z21.d, z5.d, z13.d
    eor3    z22.d, z22.d, z6.d, z14.d
    eor3    z23.d, z23.d, z7.d, z15.d
    mov     za2h.s[w12, 0:3], { z16.s - z19.s }
    mov     za2h.s[w13, 0:3], { z20.s - z23.s }

    add     x10, x10, #64
    add     x7, x7, #1
    cmp     x7, x6
    b.lo    Lblock

    // Writing h as columns of ZA1 makes row l lane l's eight digest words.
    mov     { z0.s - z3.s }, za2h.s[w12, 0:3]
    mov     { z4.s - z7.s }, za2h.s[w13, 0:3]
    mov     za1v.s[w12, 0:3], { z0.s - z3.s }
    mov     za1v.s[w13, 0:3], { z4.s - z7.s }
    st1w    { za1h.s[w12, 0] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w12, 1] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w12, 2] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w12, 3] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w13, 0] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w13, 1] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w13, 2] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w13, 3] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w14, 0] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w14, 1] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w14, 2] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w14, 3] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w15, 0] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w15, 1] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w15, 2] }, p1, [x4]
    add     x4, x4, #32
    st1w    { za1h.s[w15, 3] }, p1, [x4]

Lwrong_vl:
    mov     x0, x9
    smstop
    ldp     d10, d11, [sp, #16]
    ldp     d12, d13, [sp, #32]
    ldp     d14, d15, [sp, #48]
    ldp     d8, d9, [sp], #64
    ret
