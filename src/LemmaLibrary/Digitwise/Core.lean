/-
`LemmaLibrary.Digitwise.Core` — the comparison primitives the `1/2` test is built from.

`wordDiff` is the integer distance; `cmpDigitsFrom` is the top-down low-digit walk; and
the four branch lemmas (`hit_of_above`, `hit_of_below`, `tie_hit_iff`, `tieA_hit_iff`,
`miss_of_close`) are the exhaustive case analysis that makes a **one-digit-deep** test
correct.

`miss_of_close` is the lemma that carries the measured correction: a first-difference
walk over the digits would be *wrong*, because a digit gap of `1` can hide a whole
numerator difference as small as `1` — far below a threshold of `2^{F−1}`.  The walk is
one digit deep only because `miss_of_close` proves the gap bound `(2^r − 1)·P + (P−1) =
T − 1 < T`.

Provenance: `kapila-row-lane` `SubsetSumL25/Row/KapilaDigitwise.lean` §D1 (commit
`46cba79`/`9972181` layer).
-/
import Mathlib
import LemmaLibrary.Carry.Numerals
import LemmaLibrary.Carry.NotWordResident

namespace LemmaLibrary.Digitwise

open LemmaLibrary.Carry

set_option maxHeartbeats 1600000

/-- `|v − a|` on words: the branch the program takes at `pc 8`. -/
def wordDiff (v a : Nat) : Nat := if v < a then a - v else v - a

/-- The branch at `pc 8` splits `|v − a|` into its two cases, and `wordDiff` is
exactly the value the taken path produces. -/
theorem wordDiff_of_lt {v a : Nat} (h : v < a) : wordDiff v a = a - v := by
  unfold wordDiff
  exact if_pos h

theorem wordDiff_of_ge {v a : Nat} (h : ¬ v < a) : wordDiff v a = v - a := by
  unfold wordDiff
  exact if_neg h

/-- `1` iff `h ≤ d`, `0` otherwise — the branchless comparison, as two divisions. -/
def hitOf (d h : Nat) : Nat := (d / h) / (d / h)

/-- The per-pair hit: §7 step 7's test for one index, in words. -/
def hitWord (h v a : Nat) : Nat := hitOf (wordDiff v a) h

theorem hitOf_eq_one {d h : Nat} (hh : 1 ≤ h) (hd : h ≤ d) : hitOf d h = 1 := by
  unfold hitOf
  have h1 : 1 ≤ d / h := (Nat.one_le_div_iff (by omega)).mpr hd
  exact Nat.div_self (by omega)

theorem hitOf_eq_zero {d h : Nat} (hd : d < h) : hitOf d h = 0 := by
  unfold hitOf
  rw [Nat.div_eq_of_lt hd]

/-- **`hitWord` is the indicator of `h ≤ |v − a|`.** -/
theorem hitWord_eq_one_iff {h v a : Nat} (hh : 1 ≤ h) :
    hitWord h v a = 1 ↔ h ≤ wordDiff v a := by
  unfold hitWord
  by_cases hd : h ≤ wordDiff v a
  · exact ⟨fun _ => hd, fun _ => hitOf_eq_one hh hd⟩
  · have hlt : wordDiff v a < h := by omega
    exact ⟨fun h1 => by rw [hitOf_eq_zero hlt] at h1; exact absurd h1 (by decide), fun hc => absurd hc hd⟩

/-- **The computed hit is the paper's test**, in the fixed-point layout: with
`h = 2^{fracBits−1}` and both operands at `fracBits` fractional bits,
`hitWord = 1` exactly when `|V̂ − Â| ≥ 1/2`.  This is the equation that lets the
loop's `ℕ` arithmetic be stated in `payload_rules_iff`'s `ℚ` vocabulary. -/
theorem hitWord_eq_ratTest {fracBits : Nat} (hf : 1 ≤ fracBits) (V A : Nat) :
    hitWord (2 ^ (fracBits - 1)) V A = 1
      ↔ (1 / 2 : ℚ) ≤ |(V : ℚ) / (2 : ℚ) ^ fracBits - (A : ℚ) / (2 : ℚ) ^ fracBits| := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ fracBits := by positivity
  have hpc : (((2 : Nat) ^ (fracBits - 1) : Nat) : ℚ) = (2 : ℚ) ^ (fracBits - 1) := by
    push_cast
    rfl
  -- the ℚ side, reduced to the integer comparison at the scale `2^(fracBits-1)`
  have hkey : ((1 / 2 : ℚ) ≤
        |(V : ℚ) / (2 : ℚ) ^ fracBits - (A : ℚ) / (2 : ℚ) ^ fracBits|)
      ↔ ((2 : ℚ) ^ (fracBits - 1) ≤ ((wordDiff V A : Nat) : ℚ)) := by
    have hpow : (2 : ℚ) ^ fracBits = (2 : ℚ) ^ (fracBits - 1) * 2 := by
      conv_lhs => rw [show fracBits = (fracBits - 1) + 1 from by omega]
      rw [pow_succ]
    have hhalf : (1 / 2 : ℚ) * ((2 : ℚ) ^ (fracBits - 1) * 2) = (2 : ℚ) ^ (fracBits - 1) := by
      ring
    have habs : |(V : ℚ) / (2 : ℚ) ^ fracBits - (A : ℚ) / (2 : ℚ) ^ fracBits|
        = |(V : ℚ) - (A : ℚ)| / (2 : ℚ) ^ fracBits := by
      rw [← sub_div, abs_div, abs_of_pos hpos]
    rw [habs, le_div_iff₀ hpos, hpow, hhalf]
    rcases Nat.lt_or_ge V A with hlt | hge
    · have hcast : ((A - V : Nat) : ℚ) = (A : ℚ) - (V : ℚ) := by
        rw [Nat.cast_sub (le_of_lt hlt)]
      have hd : |(V : ℚ) - (A : ℚ)| = ((A - V : Nat) : ℚ) := by
        rw [hcast, abs_of_neg (by
          have hVQ : (V : ℚ) < (A : ℚ) := by exact_mod_cast hlt
          linarith)]
        ring
      rw [hd, wordDiff_of_lt hlt, ← hpc, Nat.cast_le]
    · have hcast : ((V - A : Nat) : ℚ) = (V : ℚ) - (A : ℚ) := by
        rw [Nat.cast_sub hge]
      have hd : |(V : ℚ) - (A : ℚ)| = ((V - A : Nat) : ℚ) := by
        rw [hcast, abs_of_nonneg (by
          have hAQ : (A : ℚ) ≤ (V : ℚ) := by exact_mod_cast hge
          linarith)]
      rw [hd, wordDiff_of_ge (by omega : ¬ V < A), ← hpc, Nat.cast_le]
  rw [hkey, hitWord_eq_one_iff Nat.one_le_two_pow, ← hpc, Nat.cast_le]

/-! ### §L4 — the loop's specification: the hit count over the remaining block

The accumulator is a *count*: the segment adds `1` per hit rather than OR-ing a
boolean, because `add` is the one word operation whose peeler the lane already
had.  The verdict is then `0 < count`, which is the same test. -/

/-- **`n` digits of `w` bits hold less than `2^(w·n)`.**  Stated with `+ 1` so the
induction never touches truncated subtraction. -/
theorem numAt_add_one_le (w : Nat) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (addr n : Nat) :
    numAt w f addr n + 1 ≤ 2 ^ (w * n) := by
  induction n with
  | zero => simp [numAt]
  | succ m ih =>
    have hf : f (addr + m) + 1 ≤ 2 ^ w := hfit (addr + m)
    rw [numAt_succ, Nat.mul_succ, Nat.pow_add]
    calc numAt w f addr m + f (addr + m) * 2 ^ (w * m) + 1
        ≤ (numAt w f addr m + 1) + f (addr + m) * 2 ^ (w * m) := by omega
      _ ≤ 2 ^ (w * m) + f (addr + m) * 2 ^ (w * m) := Nat.add_le_add_right ih _
      _ = (f (addr + m) + 1) * 2 ^ (w * m) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * m) := Nat.mul_le_mul_right _ hf
      _ = 2 ^ (w * m) * 2 ^ w := Nat.mul_comm _ _

/-- The digit bound, in the strict form the comparisons want. -/
theorem numAt_lt_pow (w : Nat) (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (addr n : Nat) :
    numAt w f addr n < 2 ^ (w * n) :=
  Nat.lt_of_succ_le (numAt_add_one_le w f hfit addr n)

/-- **A read below `2^(w·m)` has no digits above `m`.**  So it *is* its own
`m`-digit prefix — the collapse that puts the whole block inside digit `p`. -/
theorem numAt_eq_of_lt {w : Nat} (f : Nat → Nat) (addr : Nat) :
    ∀ (m stride : Nat), m ≤ stride → numAt w f addr stride < 2 ^ (w * m) →
      numAt w f addr stride = numAt w f addr m := by
  intro m stride
  induction stride with
  | zero =>
    intro hm _
    have hm0 : m = 0 := by omega
    subst hm0
    rfl
  | succ k ih =>
    intro hm hlt
    rcases Nat.eq_or_lt_of_le hm with heq | hltm
    · rw [← heq]
    · have hmk : m ≤ k := by omega
      have hzk : f (addr + k) = 0 := by
        by_contra hne
        have hge1 : 1 ≤ f (addr + k) := Nat.one_le_iff_ne_zero.mpr hne
        have h1 : 2 ^ (w * k) ≤ f (addr + k) * 2 ^ (w * k) := by
          calc 2 ^ (w * k) = 1 * 2 ^ (w * k) := (one_mul _).symm
            _ ≤ f (addr + k) * 2 ^ (w * k) := Nat.mul_le_mul_right _ hge1
        have h2 : 2 ^ (w * m) ≤ 2 ^ (w * k) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hmk)
        rw [numAt_succ] at hlt
        omega
      have hstep : numAt w f addr (k + 1) = numAt w f addr k := by
        rw [numAt_succ, hzk, Nat.zero_mul, Nat.add_zero]
      rw [hstep]
      exact ih hmk (by rw [hstep] at hlt; exact hlt)

/-- **The reader splits at digit `p`.**  Below `2^(w·(p+1))` the block is exactly
its digit at `p` times `2^(w·p)` plus the low `p`-digit read — the top-down
counterpart of the carry chain's `placeValueAt_succ`. -/
theorem numAt_split {w : Nat} (f : Nat → Nat) {addr stride p : Nat} (hp : p + 1 ≤ stride)
    (h : numAt w f addr stride < 2 ^ (w * (p + 1))) :
    numAt w f addr stride = f (addr + p) * 2 ^ (w * p) + numAt w f addr p := by
  have h1 : numAt w f addr stride = numAt w f addr (p + 1) :=
    numAt_eq_of_lt f addr (p + 1) stride hp h
  rw [h1, numAt_succ, Nat.add_comm]

/-! ### §D3 — the digit comparison, and the low-digit walk

`cmpDigitsFrom` is the top-down walk over the low digits: at each step it reads the
digit pair at the *next lower* address, and an equal pair defers to the walk
below it.  Its content is one arithmetic fact — comparing two numbers whose low
parts fit below `P` is comparing their quotients, and on equal quotients their
remainders (`mul_add_le_iff`).  That lemma is the walk's whole mechanism: no cell
ever holds a sum of two digits. -/

/-- **Comparing at digit granularity.**  If the two low parts are below `P`, then
`Y + b·P ≤ X + a·P` is decided by the high digits `b, a` and, only on `b = a`, by
the low parts.  This is the step rule of the walk — and of the *comparison*, not
of a subtraction: nothing here bounds `a` and `b` by `P`, so they may be any
digits the caller reads. -/
theorem mul_add_le_iff {P X Y a b : Nat} (hX : X < P) (hY : Y < P) :
    (Y + b * P ≤ X + a * P) ↔ (b < a ∨ (b = a ∧ Y ≤ X)) := by
  constructor
  · intro h
    have hba : b ≤ a := by
      by_contra hc
      have hab : a < b := by omega
      have h1 : a + 1 ≤ b := hab
      have h2 : (a + 1) * P ≤ b * P := Nat.mul_le_mul_right P h1
      rw [Nat.succ_mul] at h2
      omega
    rcases Nat.lt_or_eq_of_le hba with hlt | heq
    · exact Or.inl hlt
    · have hYX : Y ≤ X := by
        have h' := h
        rw [heq] at h'
        omega
      exact Or.inr ⟨heq, hYX⟩
  · rintro (hlt | ⟨heq, hYX⟩)
    · have h1 : b + 1 ≤ a := hlt
      have h2 : (b + 1) * P ≤ a * P := Nat.mul_le_mul_right P h1
      rw [Nat.succ_mul] at h2
      omega
    · subst heq
      omega

/-- **The low-digit walk.**  Reads the digit pair at `addrV + n` and `addrA + n`
for `n` descending from `stride-1` to `0`, and answers `true` iff the V-side low
block is at least the A-side one.  An equal pair defers to the walk below; the
first difference decides.  No accumulator: the state is the two digits just read. -/
def cmpDigitsFrom (f g : Nat → Nat) (addrV addrA : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    if f (addrV + n) = g (addrA + n) then cmpDigitsFrom f g addrV addrA n
    else decide (g (addrA + n) < f (addrV + n))

/-- **The walk decides the block comparison.**  `cmpDigitsFrom` returns `true`
exactly when the low block read is no smaller on the V side — i.e. it *is* the
digitwise form of `numAt w g addrA p ≤ numAt w f addrV p`, with no numerator ever
formed. -/
theorem cmpDigitsFrom_iff {w : Nat} (f g : Nat → Nat) (hf : ∀ z, f z < 2 ^ w)
    (hg : ∀ z, g z < 2 ^ w) (addrV addrA : Nat) :
    ∀ n, cmpDigitsFrom f g addrV addrA n = true
      ↔ numAt w g addrA n ≤ numAt w f addrV n := by
  intro n
  induction n with
  | zero => simp [cmpDigitsFrom, numAt]
  | succ m ih =>
    have hltV := numAt_lt_pow w f hf addrV m
    have hltA := numAt_lt_pow w g hg addrA m
    have hkey := mul_add_le_iff (P := 2 ^ (w * m)) (X := numAt w f addrV m)
      (Y := numAt w g addrA m) (a := f (addrV + m)) (b := g (addrA + m)) hltV hltA
    rw [cmpDigitsFrom, numAt_succ, numAt_succ]
    by_cases hc : f (addrV + m) = g (addrA + m)
    · rw [if_pos hc, ih]
      omega
    · have hfg : g (addrA + m) ≠ f (addrV + m) := fun hh => hc hh.symm
      rw [if_neg hc, decide_eq_true_iff, hkey]
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | ⟨he, _⟩)
        · exact h
        · exact absurd he.symm hc

/-! ### §D4 — the decision lemma

`digHalf` is the walk's first stage: one digit from each side at position `p`, the
position where the `1/2` bit lives, compared against `2^r`; the four outcomes are
*hit*, *miss*, and the two exact ties, which are the only cases that descend into
`cmpDigitsFrom`.  The four arithmetic facts it rests on are proved separately
(`hit_of_above`, `hit_of_below`, `tie_hit_iff`, `miss_of_close`) so each is
readable on its own. -/

/-- **V's digit is more than `2^r` above A's: hit.**  The digit gap alone exceeds
the threshold, whatever the low parts do. -/
theorem hit_of_above {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P) (hAlo : Alo < P)
    (h : ap + 2 ^ r < vp) :
    T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo) := by
  have hmul : (ap + 2 ^ r + 1) * P ≤ vp * P := Nat.mul_le_mul_right P (by omega)
  have hexp : (ap + 2 ^ r + 1) * P = ap * P + T + P := by
    rw [Nat.add_mul, Nat.add_mul, one_mul, ← hT]
  have hkey : ap * P + Alo + T ≤ vp * P + Vlo := by
    have h1 : ap * P + Alo + T ≤ ap * P + T + P := by omega
    calc ap * P + Alo + T ≤ ap * P + T + P := h1
      _ = (ap + 2 ^ r + 1) * P := hexp.symm
      _ ≤ vp * P := hmul
      _ ≤ vp * P + Vlo := Nat.le_add_right _ _
  rw [wordDiff_of_ge (by omega)]
  omega

/-- **A's digit is more than `2^r` above V's: hit**, by the same argument on the
other side. -/
theorem hit_of_below {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P) (hVlo : Vlo < P)
    (h : vp + 2 ^ r < ap) :
    T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo) := by
  have hmul : (vp + 2 ^ r + 1) * P ≤ ap * P := Nat.mul_le_mul_right P (by omega)
  have hexp : (vp + 2 ^ r + 1) * P = vp * P + T + P := by
    rw [Nat.add_mul, Nat.add_mul, one_mul, ← hT]
  have hkey : vp * P + Vlo + T ≤ ap * P + Alo := by
    have h1 : vp * P + Vlo + T ≤ vp * P + T + P := by omega
    calc vp * P + Vlo + T ≤ vp * P + T + P := h1
      _ = (vp + 2 ^ r + 1) * P := hexp.symm
      _ ≤ ap * P := hmul
      _ ≤ ap * P + Alo := Nat.le_add_right _ _
  rw [wordDiff_of_lt (by omega)]
  omega

/-- **V's digit is exactly `2^r` above A's.**  Then the difference is `T` plus the
low-part difference, whose magnitude is below `P ≤ T` — so the sign is fixed and
the test is exactly `Alo ≤ Vlo`: the tie is decided by the low walk. -/
theorem tie_hit_iff {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (_hVlo : Vlo < P) (hAlo : Alo < P) (h : vp = ap + 2 ^ r) :
    (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo)) ↔ Alo ≤ Vlo := by
  subst h
  have hPT : P ≤ T := by
    rw [hT]
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 2 ^ r * P := Nat.mul_le_mul_right P Nat.one_le_two_pow
  have hNV : (ap + 2 ^ r) * P + Vlo = ap * P + T + Vlo := by
    rw [Nat.add_mul, ← hT]
  rw [hNV, wordDiff_of_ge (by omega)]
  omega

/-- **A's digit is exactly `2^r` above V's**: the mirror tie, decided by the low
walk with the two sides exchanged (`cmpDigitsFrom g f`). -/
theorem tieA_hit_iff {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (hVlo : Vlo < P) (_hAlo : Alo < P) (h : ap = vp + 2 ^ r) :
    (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo)) ↔ Vlo ≤ Alo := by
  subst h
  have hPT : P ≤ T := by
    rw [hT]
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 2 ^ r * P := Nat.mul_le_mul_right P Nat.one_le_two_pow
  have hNA : (vp + 2 ^ r) * P + Alo = vp * P + T + Alo := by
    rw [Nat.add_mul, ← hT]
  rw [hNA, wordDiff_of_lt (by omega)]
  omega

/-- **Neither digit is `2^r` above the other: miss.**  The digit gap is at most
`2^r − 1`, so the whole difference is at most `(2^r−1)·P + (P−1) = T−1`, strictly
below the threshold — whatever the low parts do.  This is the branch that makes
the walk *one digit deep* in the common case. -/
theorem miss_of_close {P T r vp ap Vlo Alo : Nat} (hT : T = 2 ^ r * P)
    (hVlo : Vlo < P) (hAlo : Alo < P) (h1 : vp < ap + 2 ^ r) (h2 : ap < vp + 2 ^ r) :
    ¬ (T ≤ wordDiff (vp * P + Vlo) (ap * P + Alo)) := by
  have h1' : vp ≤ ap + (2 ^ r - 1) := by omega
  have h2' : ap ≤ vp + (2 ^ r - 1) := by omega
  have hPle : P ≤ 2 ^ r * P := by
    calc P = 1 * P := (one_mul P).symm
      _ ≤ 2 ^ r * P := Nat.mul_le_mul_right P Nat.one_le_two_pow
  have hsub : (2 ^ r - 1) * P = 2 ^ r * P - P := by rw [Nat.sub_mul, one_mul]
  have hTeq : (2 ^ r - 1) * P + P = T := by
    rw [hsub, hT]
    omega
  have hNVle : vp * P + Vlo + 1 ≤ ap * P + Alo + T := by
    have hmul : vp * P ≤ (ap + (2 ^ r - 1)) * P := Nat.mul_le_mul_right P h1'
    have hexp : (ap + (2 ^ r - 1)) * P = ap * P + (2 ^ r - 1) * P := Nat.add_mul _ _ _
    omega
  have hNAle : ap * P + Alo + 1 ≤ vp * P + Vlo + T := by
    have hmul : ap * P ≤ (vp + (2 ^ r - 1)) * P := Nat.mul_le_mul_right P h2'
    have hexp : (vp + (2 ^ r - 1)) * P = vp * P + (2 ^ r - 1) * P := Nat.add_mul _ _ _
    omega
  have hsmall : wordDiff (vp * P + Vlo) (ap * P + Alo) + 1 ≤ T := by
    by_cases hc : vp * P + Vlo < ap * P + Alo
    · rw [wordDiff_of_lt hc]
      omega
    · rw [wordDiff_of_ge hc]
      omega
  omega
end LemmaLibrary.Digitwise
