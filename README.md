# LemmaLibrary

**Standalone, machine-checked lemma library extracted from a formalisation campaign —
four reusable families, with their proofs recompiled from source in this package.**

Pin: Lean `v4.34.1`, Mathlib `d13f23b7` (the campaign pin, so nothing needs a port).

---

## 1. What this is

Four lemma families that turned out to be reusable *outside* the campaign that produced
them, extracted verbatim (declaration-granular, proofs unedited) and recompiled here:

| Family | Module | The lemma |
|---|---|---|
| Character-annihilation quadrature | `LemmaLibrary.Quadrature.*` | `trapezoid_error_le_of_decay` — `‖mean_n F − ∫F‖ ≤ M qⁿ (2K+1) + 2ε`, because the periodic trapezoid rule is **exact on every character of degree `< n`** and errs only on aliased frequencies `n ∣ k`; `hdecay_of_strip` supplies the coefficient bound `|ĉ_k| ≤ M e^{−a|k|}` from strip analyticity by a contour shift in `θ`. |
| Base-`2^w` carry exactness | `LemmaLibrary.Carry.*` (incl. `Carry.ReaderScale`, the `numAt` ↔ `placeValueAt` bridge) | `sum_base_digits` (the digits **are** the carries), `placeValue_scale` (one denominator clears exactly), `placeValueAt_payloadStride` (a `fracBits`-bit numerator is carried exactly by `⌈fracBits/w⌉+1` words), and the negative that shapes the rest: `numAt_not_word` (a stride-`k` read is **not** word-resident). |
| Digitwise threshold decision | `LemmaLibrary.Digitwise.*` | `digHalf_eq_threshold` — decide `(1/2 : ℚ) ≤ |V̂ − Â|` from two stride-`k` digit blocks **without materialising either numerator**; the threshold sits at digit `p = (F−1)/w`, bit `r`, and `miss_of_close` proves the walk is one digit deep in the common case. |
| Envelope absorption | `LemmaLibrary.Envelope.Absorb` | `envelopeAbsorb_mul` / `envelopeAbsorb_add` — a multiplicative or additive polynomial charge is absorbed by an exponential-times-polynomial cost envelope, at the cost of raising the polynomial exponent by the charge's own degree. |

The full statements, the measured defects that shaped them, and the provenance commit
for each lemma are in **`docs/NOTE.md`**. Placement recommendations (what to send to
Mathlib, what to publish, whether a formalisation note is worth writing) are in
**`docs/PLACEMENT.md`**.

## 2. Why you can trust it

* **No `sorry`, no `native_decide`, no extra axioms.** `Axioms.lean` prints the axiom set
  of every headline declaration, and `receipts.py` fails the landing unless every banner
  line names only the house triple `{propext, Classical.choice, Quot.sound}`.
* **The banner is fail-closed.** An *errored* banner run is not a clean banner: a
  misspelled `#print axioms` prints nothing and exits non-zero, so a runner that only
  scans for bad lines would pass a broken gate. Exit status is checked.
* **Determinism double-compile.** Two independent full builds, olean sha256s compared.
  A proof that compiles once has demonstrated compilability, not determinism.

Reproduce everything:

```bash
lake exe cache get      # Mathlib oleans for the pinned rev
python3 receipts.py     # build + double-compile + axiom banner, fail-closed
```

Landed receipts are kept under `receipts/`. The authoritative one is
`receipts/lemmalib-20261111T062348Z/`:

```json
{"build_exit": 0, "determinism": "IDENTICAL", "axioms_exit": 0,
 "axiom_banner_house_triple_only": true, "named_oleans_present": true, "verdict": "DONE"}
```

(The one non-trivial field there is `"lock": "TIMEOUT 180s (proceeded; deviation
recorded)"` — the shared fleet build lock was held by another lane and the runner
proceeded after a bounded wait instead of blocking indefinitely, which is the documented
behaviour and is recorded rather than hidden.)

## 3. How to use it

```bash
lake build
```

Modules are independent apart from `Carry → Digitwise`; copy the one you need. Headline
entry points:

```lean
-- quadrature, with the coefficient bound derived rather than assumed
theorem trapezoid_error_le_of_strip (hn : 0 < n) (hM : 0 ≤ M) (ha : 0 < a) ... :
    ‖circleMean F - trapMean n F‖ ≤ M * Real.exp (-a) ^ n * (2 * (K : ℝ) + 1) + 2 * ε

-- the exactness core, standalone and five lines of proof
theorem trap_error_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    circleMean (charF m) - trapMean n (charF m)
      = if (n : ℤ) ∣ m ∧ m ≠ 0 then (-1 : ℂ) else 0

-- exact carry of a full numerator in ⌈fracBits/w⌉+1 words
theorem placeValueAt_payloadStride (hw : 0 < w) (hN : N < 2 ^ fracBits) ... :
    placeValueAt m addr (payloadStride w fracBits) fracBits
      = ((N : Nat) : ℚ) / (2 : ℚ) ^ fracBits

-- the digitwise 1/2 decision, no numerator formed
theorem digHalf_eq_threshold (hw : 1 ≤ w) (hF : 1 ≤ F) ... :
    (digHalf f g addrV addrA ((F - 1) / w) ((F - 1) % w) = true)
      ↔ 2 ^ (F - 1) ≤ wordDiff (numAt w f addrV stride) (numAt w g addrA stride)
```

## 4. What is *not* here, and why

Naming the boundary is what makes the rest credible. Cited, not ported (full table with
reasons in `docs/NOTE.md` §5):

* **The Bonifaci energy-perturbation Lipschitz estimate** (`bonifaci-lane@ee833d6`) —
  already published; its content is Thomson's principle against a *fixed* flow, which
  kills the potential term and avoids matrix inversion entirely.
* **The `cmpSeg` segment program with its tight fuel `14 + 9p`** — an `Instr`-list
  program with its own interpreter, entangled with the row's `scanProg`. The
  *arithmetic* it implements is ported (`Digitwise`); the program is not.
* **The row's own assembly** (`kapila_row`, guard coverage, the certifier
  instantiations) — nothing reusable survives extraction.

Provenance extraction tool: `tools/extract.py` (declaration-granular, preserves proof
bodies byte-for-byte so the ported lemma is the *same proof* recompiled).

## 5. Licence

Apache-2.0 (see `LICENSE`). Chosen because Mathlib is Apache-2.0 — so an upstream PR from
this repository is a technical question, not a licensing one — and because the explicit
patent grant is what makes a public-good verification artefact embeddable without legal
review.
