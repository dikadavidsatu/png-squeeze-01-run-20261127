# png-squeeze — squeeze screenshots into the smallest PNG

A make.fun entry for **png-squeeze-01-run-20261127** ("Squeeze screenshots
into the smallest PNG"). One program, `main.ts` (Node 22, stdlib only),
rewrites each 1280×720 RGBA screenshot losslessly as the smallest valid PNG
it can.

## How it works

1. **Decode** the stored RGBA PNG with an own decoder (all colour types,
   bit depth 8).
2. **Analyse** the pixels: opaque? grey? ≤ 256 distinct colours? a single
   transparent value a `tRNS` key can express?
3. **Candidate forms**: palette (colour type 3, count-order and
   luminance-order) when ≤ 256 colours; grey / grey+alpha / RGB / RGBA
   otherwise, with a `tRNS` key when the image has exactly one transparent
   value. Each form is filtered per row by several strategies — fixed
   None, minsum (signed-sum heuristic), pairs (distinct-adjacent-pair
   count), and brute-force per-row deflate cost for grey.
4. **Screen** every candidate with zlib level 6 and keep the global winner.
5. **Compress** the winner with an own optimal-parsing DEFLATE: hash-chain
   LZ77 match finding, dynamic-programming optimal parse over the token
   stream, iterative Huffman refinement, per-block dynamic/fixed Huffman
   choice (zlib level 9 as a safety net if it is ever smaller).
6. **Write** a minimal valid PNG: IHDR / PLTE / tRNS / IDAT / IEND only,
   bit depth 8, non-interlaced, one zlib stream in IDAT.

Fully synchronous and deterministic: no clock, no randomness, no
environment-dependent choices anywhere in the output path — two executions
write identical bytes.

## Run

```sh
node main.ts            # reads /input/<id>/image.png, writes /output/<id>/image.png
```

`MAKEFUN_INPUT_DIR` / `MAKEFUN_OUTPUT_DIR` override the defaults `/input`
and `/output`.

## Practice-set result (kit's practice set, 8 instances)

- Score **740,646** / 1,000,000 (mean 740.6 pts/instance), all 8 answered
  exactly (every pixel incl. fully-transparent colour decodes exactly).
- House baseline (fixed-paeth 1.0.0): ~420,399 — beaten by ~320,000 points.
- Runtime ~34 s for the whole set on this machine (60 s wall budget).
- Bytes per image: i001 11,808 · i002 50,164 · i003 98,555 · i004 97,820 ·
  i005 15,306 · i006 169,503 · i007 59,173 · i008 23,479 (total 526,308).

## Licence

MIT — see `LICENSE`.
