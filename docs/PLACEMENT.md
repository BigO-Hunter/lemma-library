# Placement recommendation

Where the four lemma families and their package should live, ranked by expected value
per unit of work. Three destinations, in descending order of value:

1. **Mathlib** — two of the lemmas are genuinely missing standard results. Highest
   value, highest cost (vocabulary port).
2. **A published `darkhipo/BigO-Hunter` repo** — the honest home for all of it,
   including what Mathlib will not take. Time-to-public: days, not months.
3. **An arXiv-style formalisation note** — worth writing **only** for §6 of `NOTE.md`
   (the method), not for the lemmas.

---

## 1. Mathlib PR candidates, ranked

### 1.1 `hdecay_of_strip` — geometric Fourier decay from strip analyticity. **Strongest.**

```lean
theorem hdecay_of_strip {g : ℂ → ℂ} {F : ℝ → ℂ} {M a : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + 2π) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ)) :
    ∀ k : ℤ, k ≠ 0 → ‖fourierCoeff F k‖ ≤ M * Real.exp (-a) ^ k.natAbs
```

**Why it belongs.** "Analytic and bounded in a strip of half-width `a` implies Fourier
coefficients decay like `e^{−a|k|}`" is textbook classical analysis (Katznelson;
Trefethen–Weideman for the numerical corollary), it is used constantly in numerical
analysis, and Mathlib has nothing equivalent. Verified absence at the campaign pin
(`d13f23b7`): Mathlib's `Analysis/Fourier/` carries `AddCircle`, Parseval, inversion,
`PoissonSummation`, `RiemannLebesgueLemma` — i.e. `L²` theory and *qualitative* decay —
and **no quantitative geometric coefficient bound**.

**Why it is cheap to review.** The proof is 5 real lemmas and ~250 lines, with no
analysis machinery beyond what Mathlib already has: a rectangle contour integral
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`), periodicity to cancel
the vertical sides, and `le_of_tendsto_of_tendsto` for the endpoint. There is no annulus,
no Laurent development, no Phragmén–Lindelöf.

**The one real port cost.** Our statement is over `ℝ → ℂ` with a local `fourierCoeff`.
Mathlib states Fourier theory on `AddCircle T` with its own `fourierCoeff`. A PR must be
restated in `AddCircle` vocabulary (or the rectangle-shift lemma contributed standalone
and the coefficient corollary added to `Analysis/Fourier/AddCircle.lean`). My
recommendation: **contribute the contour-shift identity and the coefficient corollary
separately** — the shift identity is the reusable piece and has no vocabulary problem,
while the corollary is a two-line composition once the vocabulary fits.

### 1.2 `trapezoid_error_le_of_decay` — exponential accuracy of the periodic trapezoid rule. **Strong, and the sharpest gap.**

```lean
theorem trapezoid_error_le_of_decay ... :
    ‖circleMean F - trapMean n F‖ ≤ M * q ^ n * (2 * (K : ℝ) + 1) + 2 * ε
```

**Why it belongs, stated as a diff against what Mathlib has.** Mathlib *does* have a
trapezoidal-rule error theorem, and it is precisely the route this campaign measured
closed:

| | Mathlib `MeasureTheory/.../TrapezoidalRule.lean` | this package |
|---|---|---|
| statement | `trapezoidal_error_le` (Lipschitz), `trapezoidal_error_le_of_c2` (C²) | `trapezoid_error_le_of_decay` |
| rate | `O(1/N)`, `O(1/N²)` | `O(q^N)`, `q < 1` |
| mechanism | modulus of continuity / second derivative | **exactness on characters** — the rule annihilates all but aliased frequencies |
| regime | any integrable-ish `f` | `f` periodic, analytic in a strip |

The gap is not stylistic; it is a different mathematical mechanism with a different
convergence class. A Mathlib reviewer will recognise `trapezoidal_error_le_of_c2` and
immediately see that the exponential case is the interesting one for periodic analytic
integrands — this is the standard reason spectral methods exist.

**Port cost: the highest of the four.** It needs (a) the `AddCircle` vocabulary, (b) a
decision about `2K+1` (a cardinality bound tied to how the user supplies the partial
sum, which reads as an implementation detail to a reviewer), and (c) `ε`-closeness to a
partial trigonometric sum, which is a statement shape Mathlib has no idiom for.

**Honest recommendation.** Contribute the **exactness core** as a separate, small,
vocabulary-free PR, and let the composite bound stand on it:

```lean
theorem trap_error_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    circleMean (charF m) - trapMean n (charF m)
      = if (n : ℤ) ∣ m ∧ m ≠ 0 then (-1 : ℂ) else 0
```

"`Σ_{j<n} e^{2πimj/n} = n` if `n ∣ m`, else `0`" is a fact Mathlib should have in the
`AddCircle`/character API, it is five lines of proof, and it is the load-bearing
ingredient for any spectral-accuracy result anyone writes later. Small PRs land; large
ones stall.

### 1.3 The `placeValue` family — exact multi-word fixed-point arithmetic. **Good, lower priority.**

`sum_base_digits` (`N % (a·b) = N % a + (N/a % b)·a` decomposed over `stride` digits),
`placeValue_scale` (one denominator clears exactly), `placeValueAt_payloadStride`
(a `fracBits`-bit numerator is carried exactly by `⌈fracBits/w⌉+1` words).

**Why it belongs.** These are generic facts about base-`2^w` numerals and dyadic
rationals, they are the kind of arithmetic bookkeeping Mathlib accumulates, and
`sum_base_digits` is a clean standalone statement about `Nat` that needs no library
vocabulary at all — the easiest of the six to review and merge.

**Why lower priority.** Mathlib is thin on fixed-point/bit-packing arithmetic and has no
natural home for `BitVec`-as-memory models; a reviewer may reasonably ask "why is this
here?" The negative, `numAt_not_word`, is a *design* fact about a specific memory model
and should **not** be proposed to Mathlib at all — it belongs in the CFSF repo where the
model lives.

### 1.4 `digHalf` — digitwise threshold decision. **Do not propose.**

The mathematics is thin (a four-way case split over a digit comparison) and the value is
entirely in the *engineering* fact that the `1/2` threshold sits at bit `F−1` rather than
at the top digit. That is a statement about a representation, not about mathematics.
Keep it in the CFSF repo.

### 1.5 Envelope absorption. **Do not propose.**

Formalisation-engineering bookkeeping for a runtime claim. Its reuse value is real
(abstracting the added charge's degree is a genuinely good generalisation) but it is
about cost models, not mathematics.

---

## 2. The CFSF / public-good repository

**Recommendation: publish as `darkhipo/BigO-Hunter`** — the public-good posture the
campaign already runs on. This is the home for *all* four families, including the parts
Mathlib will not take, and it is also where the `NOTE.md` belongs because the note is
mostly about the parts Mathlib will not take.

**Layout** (mirroring the package as built):

```
BigO-Hunter/
  README.md              four-element README, see below
  LICENSE                Apache-2.0 (see below)
  lean-toolchain         leanprover/lean4:v4.34.1
  lakefile.toml          Mathlib pinned to d13f23b7 (the campaign pin)
  lake-manifest.json
  src/LemmaLibrary/
    Quadrature/{Characters,Strip,Decay}.lean
    Carry/{Numerals,PlaceValue,NotWordResistant}.lean
    Digitwise/{Core,HalfTest}.lean
    Envelope/Absorb.lean
  docs/NOTE.md           the note (this directory)
  docs/PLACEMENT.md      this file
  receipts.py            build + determinism double-compile + axiom banner, fail-closed
  tools/extract.py       declaration-granular provenance extractor
```

**README four-element structure** (the campaign's convention — each element answers a
question a sceptical reader actually asks):

1. **What this is.** A standalone, machine-checked library of four reusable lemma
   families extracted from a formalisation of a subset-sum algorithm's runtime row:
   character-annihilation quadrature, base-`2^w` carry exactness, digitwise threshold
   decision, envelope absorption. Pin: Lean `v4.34.1`, Mathlib `d13f23b7`.
2. **Why you can trust it.** Every statement is proved, no `sorry`, no `native_decide`;
   the axiom banner is fail-closed on anything outside
   `{propext, Classical.choice, Quot.sound}` and refuses to read an errored banner as
   clean; every landing is compiled twice and the oleans compared. Reproduce with
   `python3 receipts.py`.
3. **How to use it.** `lake exe cache get && lake build`; the per-family entry points
   are named in `docs/NOTE.md` §0 (provenance table, with the source lane and commit for
   each lemma). Copy the module you need; there are no cross-family dependencies outside
   `Carry → Digitwise`.
4. **What is *not* here, and why.** Cited-not-ported table (`NOTE.md` §5): the Bonifaci
   energy-perturbation estimate (already published), the segment program, and the row's
   own assembly. Naming the boundary is what makes the rest credible.

**LICENSE: Apache-2.0.** Rationale, stated because it is a real choice:

- Mathlib is Apache-2.0, so *every* ported-and-to-be-ported lemma is already under
  Apache-2.0-compatible terms and a Mathlib PR from this repo is frictionless. Using a
  copyleft licence here would make the eventual upstream transfer a licensing question
  rather than a technical one.
- Apache-2.0 carries an explicit patent grant. For a public-good artefact that others
  may embed in production verification tooling, that grant is the difference between
  "usable" and "usable after legal review".
- MIT is the alternative and is simpler, but it lacks the patent grant and gives an
  upstream reviewer one more thing to check. Recommend **Apache-2.0**; if the sibling
  repos in this campaign already standardised on MIT, follow them instead — consistency
  across the published set beats the marginal patent clause, and this is a
  recommendation, not a finding.

**What must NOT be published blindly.** The lane's `PROGRESS.md`, `STMTS.md`, receipt
logs, and `.bak` files contain the campaign's internal working record — including
measurements of *other* challenges' statements. Publish `src/`, `docs/NOTE.md`,
`docs/PLACEMENT.md`, the receipt runner, and the extractor; leave the working record in
the lane. The note already carries every measured number that matters, in the form that
belongs in public.

---

## 3. Is an arXiv-style formalisation note worth writing?

**Yes — but only for the method section, and only as a short note. Not for the lemmas.**

The lemmas are not novel mathematics and should not be dressed as such. What *is*
transferable, and what I have not seen written up in this form, is the observation that
motivated this whole note:

> In this campaign, **six statement defects were caught before any proof was completed**,
> and four of them were statements that were *true and useless* rather than false. The
> defects were found by computing the quantity the lemma was supposed to bound — a bound
> at `n = 40`, a Fourier tail at `K = 32`, two amplitude weights at a certified point, a
> mean-square lower bound — rather than by discovering the problem mid-proof.

That is a claim about *formalisation methodology* with evidence attached: a table of six
defects, each with how it was caught and what the cure was (`NOTE.md` §6). The sellable
part is precisely the distinction between **truth** and **satisfiability** of a formal
statement, and the concrete observation that a hypothesis can be provable and still have
no witness — which is invisible to any proof assistant and visible to a 20-line
simulation.

**Scope and venue.** A 6–8 page note, not a paper. Candidate framings:

- A "formalisation pearls / lessons" venue or workshop (e.g. a CPP/ITP experience
  report, or a journal's formalisation section).
- Alternatively: publish it as `docs/NOTE.md` in the repo and submit only the method
  section (expanded to ~6 pages) if a workshop CFP fits. The repo submission is the
  default; the paper is the option.

**What to *not* write.** Not a quadrature paper (Trefethen–Weideman 2014 and the
classical literature own that ground, and our bound is deliberately pessimistic); not a
"formalised subset-sum runtime" paper (the row is one row of an assembly that is not
finished — §5 of the note names what is still a premise). Overclaiming here would be the
exact failure mode the note argues against: a true statement presented as a strong one.

**Cost estimate.** 2–3 days to expand §6 into a standalone note with the defect table as
its spine, if the campaign wants it. The alternative allocation of those days — porting
`hdecay` to `AddCircle` vocabulary for the Mathlib PR — is, in my judgement, the higher
value of the two. **Recommend: Mathlib PR first (§1.1), repo second, paper third.**

---

## 4. Summary verdict

| Destination | Content | Verdict |
|---|---|---|
| Mathlib | `hdecay_of_strip` + contour-shift identity | **Do it.** Real gap; clean proof; only vocabulary cost. |
| Mathlib | `trap_error_char` (exactness core, 5 lines) | **Do it.** Small PR, lands, unblocks all spectral-accuracy work. |
| Mathlib | `sum_base_digits`, `placeValue_scale` | **Do it if cheap.** Clean `Nat` statements; likely accepted. |
| Mathlib | full `trapezoid_error_le_of_decay`, `placeValueAt_payloadStride` | **Defer.** Port cost exceeds review value; keep in repo. |
| Repo `darkhipo/BigO-Hunter` | all four families + both docs | **Do it now.** Apache-2.0, four-element README. |
| arXiv-style note | method section only (defect table) | **Optional**, after the Mathlib PR. |
