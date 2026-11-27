# Reusable lemma families for formal verification (Lean 4)

**What this is.** Four machine-checked lemma families extracted from a sustained formalization campaign (Lean v4.34.1 / Mathlib `d13f23b7`), 93 declarations, sorry-free, every theorem under exactly `[propext, Classical.choice, Quot.sound]`:

1. **Spectral trapezoid quadrature** — `trapezoid_error_le_of_decay`: for `F` within `ε` of its `K`-th partial trigonometric sum with Fourier coefficients `|ĉ_k| ≤ M·q^{|k|}`, the trapezoid error is `≤ M·q^n·(2K+1) + 2ε`. The error functional *annihilates every character except the aliased ones* — spectral accuracy that Lipschitz-based bounds (e.g. Mathlib's `trapezoidal_error_le_of_c2`) cannot see. Includes `hdecay_of_strip` — the contour-shift derivation of coefficient decay for strip-analytic periodic functions (no annulus/Laurent machinery).
2. **Base-2^w carry exactness** — `sum_base_digits` (digits *are* the carries: exactness, not propagation), `placeValue_scale` (one shared denominator clears exactly), `placeValueAt_payloadStride` (a `F`-bit numerator is carried exactly by `⌈F/w⌉+1` words), and `numAt_not_word` (the negative: wide sums are not word-resident — which shapes every fixed-width machine design that reads them).
3. **Digitwise threshold decision** — `digHalf`: decide `(1/2:ℚ) ≤ |V−A|` from two stride-k digit blocks *without materialising either numerator*; the threshold lives at digit `(F−1)/w`, bit `(F−1)%w` (a naive first-difference walk is wrong — `miss_of_close` pins the one-digit common case).
4. **Envelope absorption** — `envelopeAbsorb_mul`/`_add`: charging word-operation costs into exponential time envelopes, with the charge degree/constant abstracted so one theorem serves every instantiation.

**Why it is up.** Each family's naive statement is false or exponentially worse — the note's defect table records five measured corrections (two false goals *proved* false, a rate-vs-constant misread worth 10¹⁸×, a wrong walk, an unsatisfiable amplitude form). The reusable content and the correction method are the point.

**What work can be done here.** (a) The ranked Mathlib PRs (`docs/PLACEMENT.md`): `hdecay_of_strip` and `trap_error_char` lead — the latter is the sharpest diff against Mathlib's Lipschitz-only trapezoid bounds; (b) porting the cited-not-ported pieces (see `docs/NOTE.md` §5); (c) the `HasProd`/infinite-product companion work lives in [BigO-Hunter/bochner-lane](https://github.com/BigO-Hunter/bochner-lane).

**Status.** Complete extraction: 93 declarations, sorry-free, exactly `[propext, Classical.choice, Quot.sound]`, pinned Lean v4.34.1 / Mathlib `d13f23b7`; recorded build/axiom receipts in `receipts/`.

**Reproduction.** Sources live in `src/` (root module `LemmaLibrary.lean`); this shelf carries no standalone lakefile. Drop `src/` into a Lake project at the campaign pins (Lean v4.34.1 / Mathlib `d13f23b7`) and `lake build LemmaLibrary`. `receipts/build-*.log` record exactly that build at rc=0 with the axiom gate; `receipts/gate.log` records the host-pressure gating.

**License.** Licensed under the **Apache License 2.0** — deliberately not CFSF: this library exists to be upstreamed to Mathlib (Apache-2.0), and compatibility with the upstream's licensing + patent grant is the point. We hold the copyright; the choice is ours and revisitable. See `LICENSE`.

**Attribution.** The quadrature family's classical roots are the trapezoidal rule and Fourier analysis as standard (e.g. Kahane, *Some Random Series of Functions*, 2nd ed., CUP 1985; Zygmund-class trigonometric series); the carry/numeral family is elementary number theory as used in fixed-width arithmetic; the digitwise family is ours. Extracted from the BigO-campaign lanes (`wip-kapila-row` SHAs in `docs/NOTE.md` §0; `bonifaci-lane@ee833d6` for the energy-perturbation citation). Formalizations and any errors are ours.
