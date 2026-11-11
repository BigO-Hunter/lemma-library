# Reusable lemmas from a machine-checked subset-sum row

**A note on four lemma families, and on the statement defects that had to be found
before any of them could be proved.**

This note accompanies the standalone Lean package in `../src` (`LemmaLibrary`,
Lean `v4.34.1` / Mathlib `d13f23b7` — the campaign pin). Every statement below is
quoted in its **proved** Lean form, and every quoted proof was recompiled from source
in that package, not merely cited. Provenance is a table, not prose: Lean citations are
`lane/Module.lean @ commit`.

What ties the four families together is not a subject but a *method*: in each one the
first plausible statement was wrong, and the error was found by measuring before
proving — by simulating the quantity, refuting the false version cheaply, or pricing the
constant — rather than by discovering it mid-proof. §6 collects the six defects this
saved, because they are the transferable part.

---

## 0. Provenance

| Lemma (as ported) | Source file | Commit (`wip-kapila-row`) |
|---|---|---|
| `trap_error_char`, `trapezoid_error_le_of_decay` | `SubsetSumL25/Row/JV1000Strip.lean` | `76f9fdc8012ae1914a9945cf0da8d26e4273c368` |
| `abs_fourierCoeff_le_decay`, `hdecay_of_strip`, `trapezoid_error_le_of_strip` | `SubsetSumL25/Row/JV1000Decay.lean` | `a40f54193ed873e26a6cfe94ab43b0244a9068cb` |
| `quadrature_at_256_of_strip_relaxed` (cited, not ported) | `SubsetSumL25/Row/JV1000Bounds.lean` | `b3d6a47226d801443a8bf8ce807c4128145f33a0` |
| `mod_mul_split`, `sum_base_digits`, `payloadStride`, `placeValue_scale`, `placeValueAt_payloadStride` | `SubsetSumL25/Row/KapilaEstimate.lean` | `c41d4e5a48ded7d2feb469d68f1c226bbbb2be77` |
| `numAt`, `numAt_not_word` | `SubsetSumL25/Row/KapilaWide.lean` | `f395f3c9bc001e895a8c29e74eab044db5da94dd` |
| `numAt_cast`, `numAt_eq_placeValueAt_scale`, `placeValue_eq_scale_numAt`, `memOf_toNat` (the `numAt` ↔ `placeValueAt` bridge) | `KapilaWide.lean` §W2 + `KapilaEstimate.lean` | `f395f3c` + `c41d4e5` |
| `miss_of_close`, `digHalf`, `digHalf_eq_threshold`, `digHalf_eq_ratTest` | `SubsetSumL25/Row/KapilaDigitwise.lean` | `3229cc3c537baa84cf5bc1b72f280e8b0d0eaefb` |
| `withinEnvelope_wordop_absorb` | `SubsetSumL25/Row/KapilaAlgo.lean` | `c946c900b4d0ad178ea415f7f0031f478bcc2370` |
| `withinEnvelope_add_absorb` | `SubsetSumL25/Row/KapilaLoop.lean` | `6b5963912ba9d61b8860e26ff752adc063871e87` |
| tight-fuel segment program (`cmpSegFuel p = 14 + 9p`) | `SubsetSumL25/Row/KapilaCmpSegStrideProg.lean` | `46cba797f24dcf09a9e12b5625a0c1252400baed` |
| Bonifaci energy-perturbation Lipschitz estimate (cited) | `Bonnifaci/M8.lean` | `bonifaci-lane@ee833d6e77a94306a49a7fe45f26aceb5e542c32` (`M8.lean` at `75c7e1e7b4a55f2c04ee320af4037e5135da1c89`) |

Reproduce: `lake build` in the package root (see `../README.md`). The receipt runner
(`../receipts.py`) reproduces the three landing receipts: build exit 0, determinism
double-compile, and the axiom banner fail-closed on anything outside
`{propext, Classical.choice, Quot.sound}`.

---

## 1. Character-annihilation quadrature

### 1.1 The exactness core, and why "spectral accuracy" is not "a better Lipschitz bound"

The `n`-point periodic trapezoid rule is **exact on every character of degree below
`n`**. That is the entire content of the family, and it is one identity:

```lean
theorem trap_error_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    circleMean (charF m) - trapMean n (charF m)
      = if (n : ℤ) ∣ m ∧ m ≠ 0 then (-1 : ℂ) else 0
```

with `trapMean n F = (1/n) Σ_{j<n} F(2πj/n)`, `circleMean F = (1/2π)∫₀^{2π} F`, and
`charF m x = e^{imx}`. Behind it sits the geometric sum that makes it true —

```lean
theorem char_sum (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ j ∈ Finset.range n, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ)))
      = if (n : ℤ) ∣ m then (n : ℂ) else 0
```

So the error functional `E_n = circleMean − trapMean n` **annihilates every character
except the aliased frequencies** `k ≠ 0` with `n ∣ k`. Given a geometric coefficient
bound, the error is geometric:

```lean
theorem trapezoid_error_le_of_decay
    {F : ℝ → ℂ} {c : ℤ → ℂ} {M q ε : ℝ} {K n : ℕ}
    (hn : 0 < n) (hM : 0 ≤ M) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hFint : IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi))
    (hdecay : ∀ k : ℤ, k ≠ 0 → ‖c k‖ ≤ M * q ^ k.natAbs)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖F x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), c k * charF k x‖ ≤ ε) :
    ‖circleMean F - trapMean n F‖ ≤ M * q ^ n * (2 * (K : ℝ) + 1) + 2 * ε
```

`q` is a **rate**; `M`, `K`, `ε` are **constants**. `2K+1` is a crude cardinality bound
on the frequencies that could alias (the sharper `qⁿ/(1−qⁿ)` of `geom_tail_le` is
available and costs nothing to state, but cardinality is what any `n` with real decay
needs).

**Why the naive route is not merely weaker — it is closed.** The same lane first proved
the Lipschitz route (`JV1000Quadrature`) and *measured it shut*: a `1.3·10⁻⁶` enclosure
needs `n ≥ 7.7·10¹⁷` panels. A Lipschitz modulus cannot see exactness on characters,
because exactness is a property of the rule's *nodes*, not of the integrand's smoothness.
The two routes differ by ~15 orders of magnitude at the node counts that matter, which is
the practical argument for stating the lemma in the annihilation form rather than as
"a better quadrature estimate".

### 1.2 The measured correction: `q₀` is a constant, not a rate

Round 17 cited `q₀ = 0.3708350894162912`, `q₀⁴⁰ = 5.9·10⁻¹⁸`, as "the certifier's strip
decay base". It is not a decay base. In the certifier, `q₀ = √((n_f−1)(n_g−1))` is the
**contour-split contraction of the strip correction** — it bounds how far the corrected
`u`, `v` can sit from the raw `r`, `s`, and it enters the *constant*.

The quadrature base is `q = e^{−a}` for `a` the strip half-width, and the certifier uses
`a = 2β = 0.2`. At `n = 40` the honest bound is

    2·(2 + 2cosh 0.2)·2^{11.4576}/(e⁸ − 1) ≈ 7.6,

i.e. **useless** — not `5.9·10⁻¹⁸`. Re-deriving feasible `n` from the certifier's own
reproduced run gives `n = 118` (moment 1) and `n = 150` (moment 2); `n = 256`, the
certifier's own inner grid, clears both with ~10 orders of slack. The true trapezoid
error is below float resolution at `n = 128`; the bound is ≥10⁹× pessimistic because it
knows only the `0.2`-wide strip while the integrand is entire. **Pessimism is not a
defect**: the bound is what has to be proved, and it is sufficient.

The lesson generalises past this row: a constant that appears in an error term and
*looks* like a base will be read as the base. The fix is to name the exponent's base in
the theorem statement — which is why `trapezoid_error_le_of_decay` takes `q` explicitly
and never derives it.

### 1.3 `hdecay`: the contour shift, and the endpoint that is a limit

The coefficient bound is supplied, not assumed:

```lean
theorem hdecay_of_strip {g : ℂ → ℂ} {F : ℝ → ℂ} {M a : ℝ}
    (ha : 0 < a) (hM : 0 ≤ M)
    (hdiff : DifferentiableOn ℂ g {z : ℂ | |z.im| < a})
    (hbdd : ∀ z : ℂ, |z.im| < a → ‖g z‖ ≤ M)
    (hper : ∀ z : ℂ, |z.im| < a → g (z + ((2 * Real.pi : ℝ) : ℂ)) = g z)
    (hF : ∀ x : ℝ, F x = g (x : ℂ)) :
    ∀ k : ℤ, k ≠ 0 → ‖fourierCoeff F k‖ ≤ M * Real.exp (-a) ^ k.natAbs
```

and its core is

```lean
theorem abs_fourierCoeff_le_decay ... (k : ℤ) :
    ‖fourierCoeff F k‖ ≤ M * Real.exp (-(a * (k.natAbs : ℝ)))
```

**The route, and the correction to the planned route.** The plan was Cauchy's theorem on
the closed annulus `e^{−a} ≤ |z| ≤ e^{a}` — the Laurent development of `G(z) = g(−i log z)`.
That development is not needed, and the honest statement does not need it: the elementary
route is a **contour shift in the θ variable**. For every `s` with `|s| < a`,

    ĉ_k = (1/2π)∫₀^{2π} g(x)e^{−ikx}dx = (1/2π)∫₀^{2π} g(x+is)e^{−ik(x+is)}dx

because the two vertical sides of the rectangle `[0,2π] × [0,s]` cancel **by
periodicity** (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`); the
surviving factor is `e^{ks}`, which is *real*, so

    ‖ĉ_k‖ ≤ M e^{ks}   for every |s| < a.        (†)

No Phragmén–Lindelöf, no three-lines, no annulus machinery — and the constant is the
certifier's own strip sup `M`, not something derived from a substitution.

The one trap is the endpoint. `e^{ks}` is **not** bounded by `e^{−a|k|}` at any interior
`s`, so "shift to the edge of the strip" is not valid as stated; (†) has to be consumed
by a limit. Mathlib's `le_of_tendsto_of_tendsto` does it in four lines per sign
(`nhds[>] (−a)` for `k > 0`, `nhds[<] a` for `k < 0`). The strip is *open*, the limit
takes the supremum over it, and nothing is lost or assumed at the boundary.

Composition discharges the hypothesis entirely:

```lean
theorem trapezoid_error_le_of_strip {g : ℂ → ℂ} {F : ℝ → ℂ} {M a ε : ℝ} {K n : ℕ}
    (hn : 0 < n) (hM : 0 ≤ M) (ha : 0 < a)
    (hdiff hbdd hper hF hFint happrox) :
    ‖circleMean F - trapMean n F‖
      ≤ M * Real.exp (-a) ^ n * (2 * (K : ℝ) + 1) + 2 * ε
```

The only remaining inputs are strip data (`M`, `a`, holomorphy, boundedness, periodicity
*on the strip*) and the partial-sum tail `ε`.

### 1.4 The fourth measured correction: `Σ√(a²+b²)` is not `Σ(|a|+|b|)`

The quadrature's `M` is the sup of the integrand on the strip, and the row's
"summing harmonic amplitudes" is what supplies it. Read literally, summing harmonic
amplitudes is the `ℓ¹` weight `Σ_j (|a_j| + |b_j|)`. At the certified point that is
`3.63121121` / `3.59861571` — both **above** the paper's `3.21`, so the interface's own
hypothesis `amp16 ≤ 3.21` is unsatisfiable there. The paper's phrase means the **modulus**
weight `Σ_j √(a_j² + b_j²)` — the amplitude of the `j`-th harmonic — which is
`3.1952756…` / `3.2026302…`, below 3.21.

The modulus form is strictly stronger (it is the true sup bound on `|r|`, `|s|`), and it
is also the shape the downstream residue wants (`Σ√(a²+b²)·cosh(jy)`). The `ℓ¹` value is
retained as a named constant so the mismatch stays checkable rather than becoming
folklore.

**Method point.** This defect was invisible in the proof: `amp16 ≤ 3.21` is a perfectly
provable *hypothesis*; it just has no witness. Truth and satisfiability are different
properties, and only the second one makes a lemma usable.

### 1.5 The fifth: a true lemma with no witness (`K ≤ 32`, `ε ≤ 10⁻²⁰`)

`quadrature_at_256_of_strip` (row-specific, cited not ported) fixed `K ≤ 32` and
`ε ≤ 10⁻²⁰`, and every number in it is true. It is also **vacuous for the functions it
was written for**: `F` is not a trigonometric polynomial, and the residual
`r_K = F − Σ_{|k|≤K} ĉ_k e^{ikx}` obeys `sup ≥` its mean square `= √(2Σ_{|k|>K}|c_k|²)` —
measured `2.09·10⁻⁵` at `K = 32`, fifteen orders above `10⁻²⁰`. The tail shrinks with `K`
(`6.38·10⁻⁵` at 32, `4.17·10⁻⁸` at 48, `1.43·10⁻¹¹` at 64) while the aliasing term
`M qⁿ (2K+1)` grows only linearly — so the `K` **cap** pointed the wrong way. The cure,
`quadrature_at_256_of_strip_relaxed` (`K ≤ 200`, `ε ≤ 10⁻⁷`, `M ≤ 8472775` gives
`≤ 2.0003·10⁻⁷ < 10⁻⁶`), is satisfiable at `K = 48`, `ε = 4.17·10⁻⁸`.

The defective version was left in place *with its defect recorded*, because a true
statement plus the measurement that it is unusable is worth more to the next mind than
its silent removal. This is the discipline the whole campaign runs on: **a named premise
with its size measured, never a `sorry` in disguise** — and a premise whose size makes it
uninstantiable is reported as such.

---

## 2. Base-`2^w` carry exactness

### 2.1 The statements

Four facts, two positive and one negative that shapes the rest.

**The digits *are* the carries.** No propagation step exists, and none is needed:

```lean
theorem sum_base_digits (N w stride : Nat) :
    ((List.range stride).map fun j => (N / 2 ^ (w * j) % 2 ^ w) * 2 ^ (w * j)).sum
      = N % 2 ^ (w * stride)
```

which rests on a single splitting identity, valid for all `a, b > 0`:

```lean
theorem mod_mul_split (N a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    N % (a * b) = N % a + (N / a % b) * a
```

**One denominator clears exactly:**

```lean
theorem placeValue_scale {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    placeValue m base stride fracBits s * (2 : ℚ) ^ fracBits
      = ((List.range stride).map fun j =>
          ((m (base + s * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum
```

No rounding, no second denominator, nothing dropped — so two estimates at the same
`fracBits` compare as **integers on one scale**.

**A full numerator is carried exactly by `⌈fracBits/w⌉ + 1` words:**

```lean
theorem placeValueAt_payloadStride {w fracBits N addr : Nat} (hw : 0 < w) (hN : N < 2 ^ fracBits)
    (m : Nat → BitVec w)
    (hm : ∀ j, j < payloadStride w fracBits → (m (addr + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValueAt m addr (payloadStride w fracBits) fracBits
      = ((N : Nat) : ℚ) / (2 : ℚ) ^ fracBits
```

with `payloadStride w fracBits = (fracBits + w − 1)/w + 1`, and the layout fact that makes
the `+1` a carry word rather than padding:

```lean
theorem payloadStride_mul_spec {w : Nat} (hw : 0 < w) (fracBits : Nat) :
    fracBits ≤ w * payloadStride w fracBits
      ∧ fracBits + w ≤ w * payloadStride w fracBits
```

### 2.2 The negative, and why the naive read fails

```lean
theorem numAt_not_word {w stride : Nat} (hs : 1 ≤ stride) (f : Nat → Nat) (addr : Nat)
    (hpos : 0 < f (addr + stride)) : 2 ^ w ≤ numAt w f addr (stride + 1)
```

A stride-`k` read's numerator **exceeds a word**, so it is not representable in the
`BitVec w` state; a per-iteration "read the k-word sum" is not implementable, whatever
the program does. The stride-1 contrast is `numAt_one_lt`.

This is the lemma that shapes everything downstream. It is not a gap in a proof; it is
the design fact that says the wide test must be **reshaped** (digitwise, §3) rather than
**widened**, and it is worth stating as a theorem precisely because a "missing lemma"
framing would have sent the next month of work at an impossible target.

**Why the naive (single-word) version is worse rather than false.** A single word at
`fracBits ≥ w+1` does not fail — it *truncates*, and the lane proves the consequence
(`abs_dAt_lt_half`): every estimate is forced below `1/2`. The failure is silent, which
is why the exactness layer has to be stated about a multi-word layout and why
`placeValue_one` records that the old one-word read is the `stride = 1` instance of the
new vocabulary. Nothing landed is displaced; only generalised.

---

## 3. Digitwise threshold decision

### 3.1 The decision, without the numerator

Since the numerator cannot be formed (§2.2), the `1/2` test must be decided from digits:

```lean
def digHalf (f g : Nat → Nat) (addrV addrA p r : Nat) : Bool :=
  if g (addrA + p) + 2 ^ r < f (addrV + p) then true
  else if f (addrV + p) + 2 ^ r < g (addrA + p) then true
  else if f (addrV + p) = g (addrA + p) + 2 ^ r then cmpDigitsFrom f g addrV addrA p
  else if g (addrA + p) = f (addrV + p) + 2 ^ r then cmpDigitsFrom g f addrA addrV p
  else false
```

and it is exact:

```lean
theorem digHalf_eq_threshold {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f addrV stride < 2 ^ F) (hAb : numAt w g addrA stride < 2 ^ F) :
    (digHalf f g addrV addrA ((F - 1) / w) ((F - 1) % w) = true)
      ↔ 2 ^ (F - 1) ≤ wordDiff (numAt w f addrV stride) (numAt w g addrA stride)
```

Cells touched: two digit reads and one add. **No numerator is ever materialised**, which
is exactly how `numAt_not_word`'s obstruction is evaded — the walk decides a comparison,
not a value. `digHalf_eq_ratTest` restates the same fact in the paper's own vocabulary
(`(1/2 : ℚ) ≤ |V̂ − Â|`).

The honest general form is stated first and needs less:

```lean
theorem digHalf_eq_threshold_pow {w p r : Nat} (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : p + 1 ≤ stride)
    (hV : numAt w f addrV stride < 2 ^ (w * (p + 1)))
    (hA : numAt w g addrA stride < 2 ^ (w * (p + 1))) :
    (digHalf f g addrV addrA p r = true)
      ↔ 2 ^ (w * p + r) ≤ wordDiff (numAt w f addrV stride) (numAt w g addrA stride)
```

No scale-fit, no `1 ≤ F`. The scale-fit buys exactly one thing — that the digits above
`p` are the carry word and vanish — and `digHalf_eq_threshold` derives `p = (F−1)/w`,
`r = (F−1) mod w` from `F`.

### 3.2 The measured correction: the threshold is not at the top digit

The natural walk — start at the top digit `stride−1` and compare digit by digit,
stopping at the first difference — is **wrong**. A first difference of `1` at any digit
can hide a whole-numerator difference as small as `1`, far below `2^{F−1}`. The
threshold is a *single bit* at bit `F−1`, i.e. inside digit `p = (F−1)/w` at bit
`r = (F−1) mod w`, and with `F ≤ w·stride` the digits above `p` are the carry word and
are zero for a fitting payload.

The walk is therefore one digit deep in the common case, and the lemma that makes that
true is the one that kills the first-difference route:

```lean
theorem miss_of_close {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (hVlo : Vlo < P) (hAlo : Alo < P) (h1 : vp < ap + 2 ^ r) (h2 : ap < vp + 2 ^ r) :
    ¬ (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo))
```

The digit gap is at most `2^r − 1`, so the whole difference is at most
`(2^r − 1)·P + (P − 1) = T − 1` — strictly below threshold, *whatever the low parts do*.
Only an exact tie at `p` descends into the low-digit walk. That is the correction stated
as a theorem rather than as a comment: **the predicate had to be re-specified, not the
read widened.**

The segment program that implements the walk (`Row/KapilaCmpSegStrideProg.lean`) has
friction `14 + 9p` per comparison — `cmpSegFuel` — and the lane's own tightness proof
confirms no smaller constant suffices. Cited here, not ported: it is a `List Instr`
program with its own interpreter, entangled with the row's `scanProg`.

---

## 4. Envelope absorption

Two charges, one alphabet. Multiplicative first (the row's `K + 3`):

```
cost · wordOpFactor  ≤  K₀ · 2^E · P^(K+3)      when  cost ≤ K₀ · 2^E · P^K
```

Additive second, with the charge's own degree and constant **abstracted** (the row's
`K + 4` at `C = 5, d = 4`):

```
cost + charge  ≤  (K₀ + C) · 2^E · P^(K+d)
```

`E = (τ₀ + 20η')·n + 2n^{0.7}` and `P = n + b + 2` in the row; the library states both
over an abstract cost model, which is the general form the row lemmas instantiate.

**Why the abstraction is the point.** The row had a lemma at `K + 3` and needed `K + 4`;
citing the first for the second would have been false. Abstracting the *added charge's
degree* `d` and constant `C` makes one theorem serve both, and it also turned a
three-exponent slack into a proved-tight one (`wordOpFactor n ≤ (n+b+2)²`, so the honest
cost is quartic; the `^7` figure the residual targeted is true but three exponents loose
and is kept, labelled, as `scanWordOps_le_pow7`). Naming a loose bound is fine. Passing
it off as the tight one is not.

---

## 5. What is cited, not ported

Ported lemmas were recompiled from source in this package. These were left in their
lanes, with reasons — the goal is a library, not a dump:

| Left in lane | Why |
|---|---|
| Bonifaci `M8` energy-perturbation Lipschitz estimate (`bonifaci-lane@ee833d6`) | Already published; reference, do not duplicate. Its content is Thomson's principle against a *fixed* flow, which kills the potential term and avoids matrix inversion entirely. |
| `cmpSeg` segment program + tight fuel (`14+9p`) | An `Instr`-list program with its own interpreter, entangled with `scanProg`. The *arithmetic* it implements is ported (`§3`); the program is not. |
| `quadrature_at_256_of_strip{,_relaxed}`, `stripA`, `exp_neg_fifth_pow_256_le` | Row-specific instantiation at the certifier's constants. The generic lemma is ported; the instantiation is cited (`b3d6a47`). |
| `kapila_row` assembly, `Routines`, guard coverage | The row's own claim. Depends on `Instance`, the scan, and the routing; nothing reusable survives extraction. |
| `PayloadConvention`, `dAt`, `hitWord` | Row data contracts. Their *mathematics* is in §2's `placeValue` family; the contracts are the row's. |

---

## 6. Method lessons

**Six statement defects, all caught before or without a completed proof.** Each is
cheap to find if you look before you prove, and expensive to find afterwards — the
families above would each have been a *true but useless* lemma had the defect survived
into the statement.

| # | Defect | How it was caught | Cure |
|---|---|---|---|
| 1 | Moment goals `m1`/`m2` as stated are **false** by 8.62 / 8.02 bits (raw-density shape vs the strip-corrected quantity the certifier computes) | Measured the two quantities; then **proved the refutation** (`jv_m1_stated_false`, `jv_m2_stated_false`) — a disproof needs one window's lower bound, a proof would need a 1.3·10⁻⁶ enclosure | Re-state against the certifier's actual quantity |
| 2 | `q₀` read as a decay **rate** when it is a **constant** (honest bound `≈7.6` at `n=40`, not `5.9·10⁻¹⁸`) | Re-derived feasible `n` by simulation before proving | Name `q` in the statement; take `q = e^{−a}` |
| 3 | First-difference digit walk is **wrong** (a digit gap of 1 hides a difference of 1) | Stating the predicate *first* forced the threshold's location into view | `miss_of_close`: walk is one digit deep; re-specify the predicate |
| 4 | "Summing harmonic amplitudes" is `Σ√(a²+b²)` (3.195), not `Σ(|a|+|b|)` (3.631 > 3.21, unsatisfiable) | Evaluated both weights at the certified point | Certify the modulus form; keep the `ℓ¹` value named for checkability |
| 5 | `K ≤ 32, ε ≤ 10⁻²⁰` is true and **vacuous** (measured tail `2.09·10⁻⁵` at `K=32`) | Measured the tail's mean-square lower bound | `K ≤ 200, ε ≤ 10⁻⁷` (relaxed form) |
| 6 | `e^{ks}` is not `≤ e^{−a|k|}` at any interior `s` — "shift to the strip edge" loses the round | Endpoint read as a limit rather than a substitution | `le_of_tendsto_of_tendsto`, four lines per sign |

Three habits did the work, and they are the transferable part of this note:

**(a) Simulate first.** Every one of the six was found by computing an actual number
from the certifier's own reproduced data — a bound at `n = 40`, a tail at `K = 32`, two
weights at a point, a mean-square lower bound — *before* the Lean statement was fixed.
The simulation scripts (`sim_strip.py`, `sim_decay.py`, `sim_bounds_enclosure.py`) are
part of the record, not scaffolding: they are what makes a statement's *satisfiability*
checkable, which is a different and earlier question than its truth.

**(b) Determinism double-compile.** A proof that compiles once has demonstrated
compilability, not determinism. Every landing is compiled twice and the two oleans
compared byte-for-byte, because the failure mode being excluded — a build that depends
on a stray `.olean` from a previous state, or on tactic-goal ordering that a re-run can
perturb — is invisible in a single green run and would be discovered by a downstream
consumer months later.

**(c) Trust the olean, never the trace.** A `lake build` success message, a progress
bar, a `#print axioms` line ending in the house triple — each is a *report*. The gate
reads the artifact: the named oleans' existence, their sha256, and their mtime *in this
run*; the axiom banner is fail-closed on anything outside
`{propext, Classical.choice, Quot.sound}`, and a banner that *errored* is not a clean
banner (a misspelled `#print axioms` prints nothing and exits non-zero — a run that
treats "no bad line" as success would pass a broken gate). One lane had exactly that
failure shape recorded: a banner run at exit 1 read as "DONE".

A fourth habit that is really a statement of this note's thesis: **a named premise with
its size measured beats a `sorry`**, and a premise whose measured size makes the lemma
uninstantiable must be reported as unusable rather than counted as progress. Two of the
six defects above (4 and 5) were statements that were *true and useless*; one (defect 1)
was *false*; the other three were invalid moves or misread constants. Only the second
category is invisible to a proof assistant — a false statement refuses to prove, and a
misread constant usually shows up as a stuck goal — which is why satisfiability is the
category worth measuring first.

---

*The four families are small: a few hundred lines each. The reason they are worth
writing down is §6 — the statements were the hard part, and the statements only became
right when someone computed the quantity first.*
