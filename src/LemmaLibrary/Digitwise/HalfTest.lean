/-
`LemmaLibrary.Digitwise.HalfTest` — **`digHalf`**: deciding `(1/2 : ℚ) ≤ |V̂ − Â|` from
two stride-`k` digit blocks, without materialising either numerator.

`numAt_not_word` forbids forming the numerator in a word, so the test cannot be a
subtraction.  It can still be a *decision*, because the threshold `2^{F−1}` is a single
bit at digit `p = (F−1)/w`, bit `r = (F−1) mod w`:

* read one digit from each side at `p`, compare against `2^r`;
* descend into `cmpDigitsFrom` only on an exact tie at `p`.

`digHalf_eq_threshold_pow` is the honest general form — the only hypotheses are that the
block contains digit `p` and that nothing sits above `p`; no scale-fit, no `1 ≤ F`.
`digHalf_eq_threshold` computes `p`, `r` from `F` and adds exactly the scale-fit
(`numV, numA < 2^F`) that makes the digits above `p` vanish.  `digHalf_eq_ratTest` is
the same statement in the paper's own `ℚ` vocabulary.

Provenance: `kapila-row-lane` `SubsetSumL25/Row/KapilaDigitwise.lean` §D1 (commit
`9972181` "the stride tail's exact instruction list, pinned by D7" and its parent).
The segment program with tight fuel (`14 + 9p`, tightness proved) lives in
`Row/KapilaCmpSegStrideProg.lean` and is **cited, not ported**: it is a `List Instr`
program with its own interpreter, entangled with the row's `scanProg`.
-/
import Mathlib
import LemmaLibrary.Digitwise.Core
import LemmaLibrary.Carry.PlaceValue
import LemmaLibrary.Carry.ReaderScale

namespace LemmaLibrary.Digitwise

open LemmaLibrary.Carry

set_option maxHeartbeats 1600000

/-- **The `1/2` test is an integer comparison.**  With `h = 2^(F−1)` and both
operands at `F` fractional bits, §7 step 7's test is `2^(F−1) ≤ |V − A|` — no
rounding, no second denominator.  Derived from the landed `hitWord_eq_ratTest`
composed with `hitWord_eq_one_iff`, so the predicate the walk decides is literally
the predicate `wideExit_eq_binSum` folds. -/
theorem halfTest_iff_wordDiff {F : Nat} (hF : 1 ≤ F) (V A : Nat) :
    ((1 / 2 : ℚ) ≤ |(V : ℚ) / (2 : ℚ) ^ F - (A : ℚ) / (2 : ℚ) ^ F|)
      ↔ 2 ^ (F - 1) ≤ wordDiff V A :=
  (hitWord_eq_ratTest hF V A).symm.trans (hitWord_eq_one_iff Nat.one_le_two_pow)

/-- **The reader over the one shared scale is the place value at an address.**
The `placeValue` case is landed (`placeValue_eq_scale_numAt`); this is the same
statement for the address-indexed read the carry chain and the walk both use. -/
theorem placeValueAt_eq_scale_numAt {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (addr stride fracBits : Nat) :
    placeValueAt (memOf w f) addr stride fracBits
      = (numAt w f addr stride : ℚ) / (2 : ℚ) ^ fracBits := by
  have h := numAt_eq_placeValueAt_scale f hfit addr stride fracBits
  rw [eq_div_iff (ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ fracBits))]
  exact h.symm

/-! ### §D2 — the two bounds the walk consumes

`numAt_lt_pow` is the digit bound (`stride` digits of `w` bits hold less than
`2^(w·stride)`), and `numAt_eq_of_lt` is the reason a scale-fitting numerator has
zeros above digit `p`: **a read that is below `2^(w·m)` cannot have a nonzero
digit at position `≥ m`**, so the whole block collapses to its first `m` digits.
`numAt_split` is the consequence the walk is built on — the reader *is* one digit
at place `p` plus a low read, and that is `sum_base_digits`' exactness seen from
the top instead of from the bottom. -/

/-- **The digitwise half test.**  One digit from each side at position `p` — the
digit holding the `1/2` bit — compared against `2^r`; the two exact ties descend
into the low-digit walk, and nothing else does.  Cells touched: the two digit
reads and one add.  No numerator is formed, so `numAt_not_word`'s obstruction does
not apply: `digHalf` decides a comparison, not a value. -/
def digHalf (f g : Nat → Nat) (addrV addrA p r : Nat) : Bool :=
  if g (addrA + p) + 2 ^ r < f (addrV + p) then true
  else if f (addrV + p) + 2 ^ r < g (addrA + p) then true
  else if f (addrV + p) = g (addrA + p) + 2 ^ r then cmpDigitsFrom f g addrV addrA p
  else if g (addrA + p) = f (addrV + p) + 2 ^ r then cmpDigitsFrom g f addrA addrV p
  else false

/-- **THE DECISION LEMMA, in its honest generality.**  The only hypotheses the
walk needs are: the block holds digit `p` (`p + 1 ≤ stride`), and **nothing sits
above `p`** (`numV, numA < 2^(w·(p+1))`).  No scale-fit, no `1 ≤ F`: with
`T = 2^(w·p+r)` the four branch facts consume only `Vlo, Alo < 2^(w·p)`, which the
digit bound supplies.  The threshold exponent is *given* here (`w·p + r`); the
`F`-indexed form below is the corollary that computes it from `fracBits`. -/
theorem digHalf_eq_threshold_pow {w p r : Nat} (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : p + 1 ≤ stride)
    (hV : numAt w f addrV stride < 2 ^ (w * (p + 1)))
    (hA : numAt w g addrA stride < 2 ^ (w * (p + 1))) :
    (digHalf f g addrV addrA p r = true)
      ↔ 2 ^ (w * p + r) ≤ wordDiff (numAt w f addrV stride) (numAt w g addrA stride) := by
  have hVs := numAt_split f hp hV
  have hAs := numAt_split g hp hA
  have hVlo : numAt w f addrV p < 2 ^ (w * p) := numAt_lt_pow w f hf addrV p
  have hAlo : numAt w g addrA p < 2 ^ (w * p) := numAt_lt_pow w g hg addrA p
  have hT : 2 ^ (w * p + r) = 2 ^ r * 2 ^ (w * p) := by
    rw [Nat.pow_add, Nat.mul_comm]
  rw [hVs, hAs, digHalf]
  by_cases h1 : g (addrA + p) + 2 ^ r < f (addrV + p)
  · rw [if_pos h1]
    exact ⟨fun _ => hit_of_above hT hAlo h1, fun _ => rfl⟩
  · rw [if_neg h1]
    by_cases h2 : f (addrV + p) + 2 ^ r < g (addrA + p)
    · rw [if_pos h2]
      exact ⟨fun _ => hit_of_below hT hVlo h2, fun _ => rfl⟩
    · rw [if_neg h2]
      by_cases h3 : f (addrV + p) = g (addrA + p) + 2 ^ r
      · rw [if_pos h3, cmpDigitsFrom_iff f g hf hg addrV addrA p]
        exact (tie_hit_iff hT hVlo hAlo h3).symm
      · rw [if_neg h3]
        by_cases h4 : g (addrA + p) = f (addrV + p) + 2 ^ r
        · rw [if_pos h4, cmpDigitsFrom_iff g f hg hf addrA addrV p]
          exact (tieA_hit_iff hT hVlo hAlo h4).symm
        · rw [if_neg h4]
          have hlt1 : f (addrV + p) < g (addrA + p) + 2 ^ r := by omega
          have hlt2 : g (addrA + p) < f (addrV + p) + 2 ^ r := by omega
          refine ⟨fun hc => (Bool.false_ne_true hc).elim,
            fun hbad => (miss_of_close hT hVlo hAlo hlt1 hlt2 hbad).elim⟩

/-- **THE DECISION LEMMA.**  For a scale-fitting stride-`k` read (`numV`,
`numA < 2^F`, `F ≥ 1`, `w ≥ 1`, and a block long enough to contain digit `p`
where the `1/2` bit lives), the digitwise walk decides §7 step 7's integer test —
**without materialising either numerator**.  The scale-fit buys exactly one thing:
that the digits above `p` are the carry word and vanish (`numAt_eq_of_lt`), which
is what lets `digHalf_eq_threshold_pow` read a single digit at `p`. -/
theorem digHalf_eq_threshold {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f addrV stride < 2 ^ F) (hAb : numAt w g addrA stride < 2 ^ F) :
    (digHalf f g addrV addrA ((F - 1) / w) ((F - 1) % w) = true)
      ↔ 2 ^ (F - 1) ≤ wordDiff (numAt w f addrV stride) (numAt w g addrA stride) := by
  have hrw : (F - 1) % w < w := Nat.mod_lt _ (by omega)
  have hFr : w * ((F - 1) / w) + (F - 1) % w = F - 1 := Nat.div_add_mod (F - 1) w
  have hWs : w * ((F - 1) / w + 1) = w * ((F - 1) / w) + w := Nat.mul_succ w _
  have hFle : F ≤ w * ((F - 1) / w + 1) := by omega
  have hV2 : numAt w f addrV stride < 2 ^ (w * ((F - 1) / w + 1)) :=
    lt_of_lt_of_le hVb (Nat.pow_le_pow_right (by norm_num) hFle)
  have hA2 : numAt w g addrA stride < 2 ^ (w * ((F - 1) / w + 1)) :=
    lt_of_lt_of_le hAb (Nat.pow_le_pow_right (by norm_num) hFle)
  have hkey := digHalf_eq_threshold_pow (w := w) (p := (F - 1) / w) (r := (F - 1) % w)
    f g hf hg hp hV2 hA2
  rwa [hFr] at hkey

/-- **The decision lemma in §7 step 7's own vocabulary.**  `true` exactly when
`(1/2 : ℚ) ≤ |V̂ − Â|` on the two place values — the walk decides the paper's test
itself, and `halfTest_iff_wordDiff` is the bridge that makes the statement literal
rather than an integer proxy. -/
theorem digHalf_eq_ratTest {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {addrV addrA stride : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f addrV stride < 2 ^ F) (hAb : numAt w g addrA stride < 2 ^ F) :
    (digHalf f g addrV addrA ((F - 1) / w) ((F - 1) % w) = true)
      ↔ (1 / 2 : ℚ) ≤ |placeValueAt (memOf w f) addrV stride F
          - placeValueAt (memOf w g) addrA stride F| := by
  rw [placeValueAt_eq_scale_numAt f hf, placeValueAt_eq_scale_numAt g hg,
    halfTest_iff_wordDiff hF]
  exact digHalf_eq_threshold hw hF f g hf hg hp hVb hAb

/-- **The decision lemma at estimate `s`.**  The walk on the two payload blocks
falls on §7 step 7's comparison of the estimates themselves — `placeV` and
`placeA` in the paper's own two-letter form, i.e. the objects `dAt_eq_reader`
names as `dAt`. -/
theorem digHalf_eq_placeValueTest {w F : Nat} (hw : 1 ≤ w) (hF : 1 ≤ F) (f g : Nat → Nat)
    (hf : ∀ z, f z < 2 ^ w) (hg : ∀ z, g z < 2 ^ w) {baseV baseA stride s : Nat}
    (hp : (F - 1) / w + 1 ≤ stride)
    (hVb : numAt w f (baseV + s * stride) stride < 2 ^ F)
    (hAb : numAt w g (baseA + s * stride) stride < 2 ^ F) :
    (digHalf f g (baseV + s * stride) (baseA + s * stride) ((F - 1) / w) ((F - 1) % w)
        = true)
      ↔ (1 / 2 : ℚ) ≤ |placeValue (memOf w f) baseV stride F s
          - placeValue (memOf w g) baseA stride F s| := by
  rw [placeValue_eq_placeValueAt, placeValue_eq_placeValueAt]
  exact digHalf_eq_ratTest hw hF f g hf hg hp hVb hAb

/-- **Spot checks, kernel-checked.**  Three concrete payloads at `w = 2`, `F = 4`
(so `p = 1`, `r = 1`, threshold `2^3 = 8`), reading `V` at address `0` and `A` at
address `10`: a decided hit (digits `3,3` vs `0,0` — `|15 − 0| = 15 ≥ 8`), a
decided miss (`3,1` vs `0,0` — `|7 − 0| = 7 < 8`), and an **exact tie at digit
`p`** (`0,2` vs `1,0` — `|8 − 1| = 7 < 8`, resolved by the low walk, which is the
only path that descends: `f 0 = 0 < 1 = g 10`, so the walk answers miss).
`decide`, not `native_decide`: the house banner admits no `Lean.ofReduceBool`. -/
theorem digHalf_spot_checks :
    digHalf (fun z => if z = 0 then 3 else if z = 1 then 3 else 0) (fun _ => 0) 0 10 1 1 = true ∧
    digHalf (fun z => if z = 0 then 3 else if z = 1 then 1 else 0) (fun _ => 0) 0 10 1 1 = false ∧
    digHalf (fun z => if z = 0 then 0 else if z = 1 then 2 else 0)
        (fun z => if z = 10 then 1 else 0) 0 10 1 1 = false := by
  decide

/-! ### §D5 — the program segment's shape, **stated**

The arithmetic above fixes what the segment has to compute; this fixes its
*shape*, in the vocabulary the row's `Instr` set speaks (`Statement.lean`: `load`,
`add`, `sub`, `rem`, `one`, `blt`).  What is stated is the skeleton and its fuel.
**What is deliberately not here is the segment proof** — that `exec` reaches the
stated cell values — because the arithmetic had to be settled first: a segment
proof against a wrong decision predicate would be a *new* `K + 3`-versus-`K + 7`
mistake wearing a loop.  The obligation it must meet is written out in this
section's docstring so the next mind inherits it exactly.

Register map (the segment's precondition, discharged by the caller):

| cell | meaning |
|---|---|
| 0 | address of V's digit `p`, advanced **down** by the walk |
| 1 | address of A's digit `p`, advanced down |
| 2 | digits still to compare |
| 3, 4 | the digit pair just read |
| 5 | scratch |
| 6 | **the verdict** (`1` = hit) |
| 7 | `0` (constant) |
| 8 | `1` (constant) |
| 9 | `2^r` (the `1/2` bit's value inside digit `p`) |
| 10 | swap scratch (the A-side tie enters the walk with the sides exchanged) |

The obligation, precisely: from that precondition and fuel `cmpSegFuel p`, the run
reaches `cont` with cell `6 = digHalf`'s verdict as a word (`1` for `true`, `0` for
`false`), touching no other cell of the caller's.  Three facts are proved below
because they are pure shape — the program's length, the fuel's linearity, and the
fuel's relation to the stride-`k` read charge; the reachability part is the
deferred segment proof (`KapilaCmpSeg`).

**Two defects the shape carried, both caught before the proof was attempted**
(by simulating this exact `Instr` list rather than reasoning about it).  They are
recorded here because the skeleton was *stated* before it was walked, and a stated
skeleton is a claim like any other:

1. **The `p = 0` tie descended into nothing.**  As first written, both tie
   instructions were unconditional jumps to the walk (`blt 7 8 19` / `blt 7 8 16`).
   A tie at `p = 0` then entered the walk with no digit below `p`: it decremented
   the two pointer cells to `addrV − 1`, `addrA − 1` and read *there* — addresses
   outside the digit block — and returned whatever those words happened to say.
   The tie at `p = 0` has no low part at all, and `cmpDigitsFrom … 0 = true`, so
   the correct verdict is `hit`; the program could answer `miss`.  The fix is
   **free**: the two tie jumps now test the digit counter (`blt 7 2 19`,
   `blt 7 2 16`) and only descend when `0 < p`, so the `p = 0` tie falls through
   into the hit exit (`12`).  It also makes position `7` live code — it was
   unreachable as first written.
2. **The fuel was one step short.**  The walk's terminal digit costs `10`
   instructions to reach the hit entry (`19 … 28`) and not `9`, so the worst case
   is `11 + (9p + 3) = 9p + 14`, not `13 + 9p`.  Corrected below; `14 + 9p` is
   *attained* (`p ≥ 1`, A-side tie, all low digits equal), so it is a bound and not
   slack.

A third hazard is a hypothesis rather than a defect: `add 5 4 9` sums a digit with
`2^r` in one word, so the segment needs `d + 2^r < 2^w` for the two digits `d` it
reads at `p`.  At `r ≤ w − 2` the scale-fit regime supplies it for free (a digit at
`p` is below `2^(r+1)`), so only the top bit of digit `p` (`r = w − 1`) is an
explicit premise; `KapilaCmpSeg` carries it as `hadA`/`hadV` and proves the free
case (`two_pow_add_fits`). -/
end LemmaLibrary.Digitwise
