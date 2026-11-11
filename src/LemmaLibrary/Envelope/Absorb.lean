/-
`LemmaLibrary.Envelope.Absorb` — the **envelope absorption pair**.

A cost bound of the shape "exponential in `n` times a polynomial in the input size" is
robust in a specific, useful way: you may multiply it by any polynomial factor, or add
any polynomial charge, and stay inside the *same* envelope by raising the polynomial
exponent.  Both operations are proved here, over an abstract cost model, because the
abstraction is the point — the campaign had a multiplicative lemma at `K + 3` and needed
`K + 4`, and citing the first for the second would have been false.  Abstracting the
*added charge's degree* `d` and constant `C` makes one theorem serve both, and it also
exposes where a neighbouring bound was three exponents loose.

The row instantiations (cited, not ported):

* `kapila-row-lane` `Row/KapilaAlgo.lean` @ `c946c90` — `withinEnvelope_wordop_absorb`:
  `cost · wordOpFactor`, `K + 3`, because one dyadic operation on `n²`-bit operands in
  `w`-bit words costs `⌈n²/w⌉ + 1 ≤ n² + 1` word operations, and `n² + 1 ≤ (n+b+2)³`.
* `kapila-row-lane` `Row/KapilaLoop.lean` @ `6b59639` — `withinEnvelope_add_absorb`:
  the scan's charge is `blockLen · (2·wordOpFactor n + 3)`, **quartic** in `(n+b+2)`
  (`wordOpFactor n ≤ (n+b+2)²`, true and tight), so the honest pair is `K + 4`, not the
  `K + 7` the residual targeted.  The `^7` statement is kept in the lane, labelled as
  true-but-loose, because a named loose bound is fine — passing it off as tight is not.
-/
import Mathlib

namespace LemmaLibrary.Envelope

set_option maxHeartbeats 1600000

/-- **The envelope, abstractly.**  `cost n` is bounded by `K₀ · 2^{E n} · (P n)^K`: a
constant, an exponential factor, and a polynomial factor.  The row's `E` and `P` are
`E n = (τ₀ + 20η')·n + 2n^{0.7}` and `P n = n + b + 2`; nothing below uses their
particular shape. -/
def WithinEnvelope (cost : ℕ → ℕ) (E P : ℕ → ℝ) (K₀ K : ℕ) : Prop :=
  ∀ n, (cost n : ℝ) ≤ (K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K

/-- `0 ≤ E` gives `1 ≤ 2^E`, the only fact the additive side needs about the
exponential factor. -/
theorem one_le_two_rpow {E : ℝ} (h : 0 ≤ E) : (1 : ℝ) ≤ (2 : ℝ) ^ E :=
  Real.one_le_rpow (by norm_num) h

/-- **Multiplicative absorption.**  A cost inside the envelope stays inside it when
multiplied by any factor bounded by a power of the polynomial part; the exponent rises
by that power's degree and the constant is unchanged.

This is `withinEnvelope_wordop_absorb` with the word-operation factor abstracted to
`F` and its degree to `C` (`C = 3`, `F = wordOpFactor` recovers the row's lemma). -/
theorem envelopeAbsorb_mul {cost F : ℕ → ℕ} {E P : ℕ → ℝ} {K₀ K : ℕ}
    (h : WithinEnvelope cost E P K₀ K)
    (hE : ∀ n, 0 ≤ E n) (hP : ∀ n, 1 ≤ P n)
    {C : ℕ} (hF : ∀ n, (F n : ℝ) ≤ (P n) ^ C) :
    ∃ K₀' K' : ℕ, WithinEnvelope (fun n => cost n * F n) E P K₀' K' := by
  refine ⟨K₀, K + C, fun n => ?_⟩
  have h1 : (cost n : ℝ) ≤ (K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K := h n
  have hP0 : (0 : ℝ) ≤ P n := le_trans zero_le_one (hP n)
  have hf : (F n : ℝ) ≤ (P n) ^ C := hF n
  have hcast : ((cost n * F n : ℕ) : ℝ) = (cost n : ℝ) * (F n : ℝ) := by push_cast; ring
  rw [hcast]
  have hK0 : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg K₀
  have h2E : (0 : ℝ) ≤ (2 : ℝ) ^ E n := by positivity
  calc (cost n : ℝ) * (F n : ℝ)
      ≤ ((K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K) * (P n) ^ C := by
        refine mul_le_mul h1 hf (Nat.cast_nonneg _) ?_
        exact mul_nonneg (mul_nonneg hK0 h2E) (pow_nonneg hP0 K)
    _ = (K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + C) := by rw [pow_add]; ring

/-- **Additive absorption.**  A cost inside the envelope plus a charge bounded by
`C · (P n)^d` stays inside the envelope with the exponent raised by the charge's own
degree `d` and the constant raised by `C`.

`d` and `C` are the abstraction that matters: it is the *degree of the added charge*,
not a number copied from a neighbouring lemma, that sets the new exponent.  `C = 1,
d = 3` reproduces the row's linear charge shape `K + 3`; `C = 5, d = 4` its quartic scan
charge `K + 4`. -/
theorem envelopeAbsorb_add {cost charge : ℕ → ℕ} {E P : ℕ → ℝ} {K₀ K : ℕ}
    (h : WithinEnvelope cost E P K₀ K)
    (hE : ∀ n, 0 ≤ E n) (hP : ∀ n, 1 ≤ P n)
    {C d : ℕ} (hc : ∀ n, (charge n : ℝ) ≤ (C : ℝ) * (P n) ^ d) :
    ∃ K₀' K' : ℕ, WithinEnvelope (fun n => cost n + charge n) E P K₀' K' := by
  refine ⟨K₀ + C, K + d, fun n => ?_⟩
  have h1 : (cost n : ℝ) ≤ (K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K := h n
  have h2 : (charge n : ℝ) ≤ (C : ℝ) * (P n) ^ d := hc n
  have hP0 : (0 : ℝ) ≤ P n := le_trans zero_le_one (hP n)
  have hP1 : (1 : ℝ) ≤ P n := hP n
  have hE0 : (0 : ℝ) ≤ E n := hE n
  have h2E : (1 : ℝ) ≤ (2 : ℝ) ^ E n := one_le_two_rpow hE0
  have hcast : ((cost n + charge n : ℕ) : ℝ) = (cost n : ℝ) + (charge n : ℝ) := by push_cast; ring
  -- the cost term stays inside the *larger* exponent
  have hA : (K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K
      ≤ (K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d) := by
    have hK : (P n) ^ K ≤ (P n) ^ (K + d) := pow_le_pow_right₀ hP1 (by omega)
    exact mul_le_mul_of_nonneg_left hK (by positivity)
  -- the charge term absorbs the exponential factor entirely (it is ≥ 1)
  have hB : (C : ℝ) * (P n) ^ d ≤ (C : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d) := by
    have hPd : (P n) ^ d ≤ (2 : ℝ) ^ E n * (P n) ^ (K + d) := by
      have hK : (P n) ^ d ≤ (P n) ^ (K + d) := pow_le_pow_right₀ hP1 (by omega)
      calc (P n) ^ d ≤ (P n) ^ (K + d) := hK
        _ = 1 * (P n) ^ (K + d) := (one_mul _).symm
        _ ≤ (2 : ℝ) ^ E n * (P n) ^ (K + d) :=
            mul_le_mul_of_nonneg_right h2E (pow_nonneg hP0 _)
    calc (C : ℝ) * (P n) ^ d ≤ (C : ℝ) * ((2 : ℝ) ^ E n * (P n) ^ (K + d)) :=
          mul_le_mul_of_nonneg_left hPd (Nat.cast_nonneg C)
      _ = (C : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d) := by ring
  rw [hcast]
  have hsum : (cost n : ℝ) + (charge n : ℝ)
      ≤ ((K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K) + ((C : ℝ) * (P n) ^ d) :=
    add_le_add h1 h2
  have hpeak : ((K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ K) + ((C : ℝ) * (P n) ^ d)
      ≤ ((K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d))
        + ((C : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d)) :=
    add_le_add hA hB
  have hfin : ((K₀ : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d))
      + ((C : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d))
      = ((K₀ + C : ℕ) : ℝ) * (2 : ℝ) ^ E n * (P n) ^ (K + d) := by
    push_cast
    ring
  linarith [hsum, hpeak, hfin.le, hfin.ge]

end LemmaLibrary.Envelope
