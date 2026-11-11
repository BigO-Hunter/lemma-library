/-
`LemmaLibrary.Quadrature.Strip` — **the strip-analyticity quadrature lemma**.

`|trap_n F − ∫F| ≤ M·qⁿ·(2K+1) + 2ε` whenever `F` is within `ε` of its `K`-th partial
trigonometric sum on the circle and the coefficients obey `|ĉ_k| ≤ M q^{|k|}`.

`q` is the *rate* and `M`, `K`, `ε` are *constants*: the distinction is the measured
correction this family carries — see `docs/NOTE.md` §1.2 (a certifier constant `q₀ =
√((n_f−1)(n_g−1))` was read as a decay base for one round; the honest base is
`q = e^{−a}` for `a` the strip half-width, and at `n = 40` the honest bound is `≈ 7.6`,
i.e. useless, not `5.9·10⁻¹⁸`).

Provenance: ported from `kapila-row-lane` `SubsetSumL25/Row/JV1000Strip.lean` §6 (same
commit as above).
-/
import Mathlib
import LemmaLibrary.Quadrature.Characters

namespace LemmaLibrary.Quadrature

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

/-- **THE STRIP-ANALYTICITY QUADRATURE LEMMA.**

`|trap_n(H) − ∫H| ≤ C·qⁿ` for `H = Σ_k ĉ_k e^{ikx}` with geometric coefficients
`|ĉ_k| ≤ M q^{|k|}` (the content strip analyticity supplies), and `C = M(2K+1)`.

`K` is the partial-sum order of the enclosure: `F` is within `ε` of its `K`-th partial
trigonometric sum on the circle.  The `qⁿ` is the spectral-accuracy factor (§1–§3: the
rule is exact on every character of degree `< n`, so only the aliased frequencies `n ∣ k`
survive, and each of those carries `q^{|k|} ≤ qⁿ`), and `2K+1` is the crude cardinality
of the frequencies that could alias — a *cardinality* bound rather than the sharper
`qⁿ/(1−qⁿ)` of `geom_tail_le`, which is enough at any `n` where the decay is real and
costs nothing to state. -/
theorem trapezoid_error_le_of_decay
    {F : ℝ → ℂ} {c : ℤ → ℂ} {M q ε : ℝ} {K n : ℕ}
    (hn : 0 < n) (hM : 0 ≤ M) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hFint : IntervalIntegrable F volume (0 : ℝ) (2 * Real.pi))
    (hdecay : ∀ k : ℤ, k ≠ 0 → ‖c k‖ ≤ M * q ^ k.natAbs)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖F x - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), c k * charF k x‖ ≤ ε) :
    ‖circleMean F - trapMean n F‖ ≤ M * q ^ n * (2 * (K : ℝ) + 1) + 2 * ε := by
  classical
  set S : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hS
  set P : ℝ → ℂ := fun x => ∑ k ∈ S, c k * charF k x with hP
  -- `P` is continuous, hence interval-integrable
  have hPint : IntervalIntegrable P volume (0 : ℝ) (2 * Real.pi) := by
    have hc : Continuous P := by
      rw [hP]
      exact continuous_finset_sum _ fun k _ => by unfold charF; fun_prop
    exact hc.intervalIntegrable _ _
  -- the tail: `F` and `P` are pointwise `ε`-close
  have hclose : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖(F - P) x‖ ≤ ε := by
    intro x hx
    simpa [hP, hS, Pi.sub_apply] using happrox x hx
  -- the aliasing bound on `P`
  have hEP : circleMean P - trapMean n P
      = ∑ k ∈ S, c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0) := by
    rw [hP, circleMean_finset_sum, trapMean_finset_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      have h := trap_error_char n hn k
      linear_combination c k * h
  have hcard : (S.card : ℝ) ≤ 2 * (K : ℝ) + 1 := by
    have hN : S.card ≤ 2 * K + 1 := by
      rw [hS, Int.card_Icc]
      have hle : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hle, Int.toNat_natCast]
    calc (S.card : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by exact_mod_cast hN
      _ = 2 * (K : ℝ) + 1 := by push_cast; ring
  -- each aliased frequency carries `q^{|k|} ≤ qⁿ`; the rest carry nothing
  have hterm : ∀ k ∈ S, ‖c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0)‖ ≤ M * q ^ n := by
    intro k _
    by_cases hk : (n : ℤ) ∣ k ∧ k ≠ 0
    · have hkn : n ≤ k.natAbs := by
        obtain ⟨j, rfl⟩ := hk.1
        have hj : j ≠ 0 := fun h0 => hk.2 (by rw [h0, mul_zero])
        have hj1 : 1 ≤ j.natAbs := by have := Int.natAbs_pos.mpr hj; omega
        rw [Int.natAbs_mul]
        simp only [Int.natAbs_natCast]
        calc n = n * 1 := by ring
          _ ≤ n * j.natAbs := Nat.mul_le_mul_left n hj1
      simp only [if_pos hk]
      rw [show c k * (-1 : ℂ) = -c k by ring, norm_neg]
      refine le_trans (hdecay k hk.2) (mul_le_mul_of_nonneg_left ?_ hM)
      exact pow_le_pow_of_le_one hq0 hq1.le hkn
    · simp only [if_neg hk, mul_zero, norm_zero]
      exact mul_nonneg hM (pow_nonneg hq0 n)
  have hPbound : ‖circleMean P - trapMean n P‖ ≤ M * q ^ n * (2 * (K : ℝ) + 1) := by
    rw [hEP]
    calc ‖∑ k ∈ S, c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0)‖
        ≤ ∑ k ∈ S, ‖c k * (if (n : ℤ) ∣ k ∧ k ≠ 0 then (-1 : ℂ) else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ S, M * q ^ n := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (M * q ^ n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (K : ℝ) + 1) * (M * q ^ n) := by
          apply mul_le_mul_of_nonneg_right hcard
          exact mul_nonneg hM (pow_nonneg hq0 n)
      _ = M * q ^ n * (2 * (K : ℝ) + 1) := by ring
  -- reassemble
  have hsplit : circleMean F - trapMean n F
      = (circleMean (F - P) - trapMean n (F - P)) + (circleMean P - trapMean n P) := by
    have h1 : circleMean (F - P) = circleMean F - circleMean P := by
      exact circleMean_sub (h₁ := F) (h₂ := P) hFint hPint
    have h2 : trapMean n (F - P) = trapMean n F - trapMean n P := by
      exact trapMean_sub n F P
    rw [h1, h2]
    ring
  rw [hsplit]
  have htail : ‖circleMean (F - P) - trapMean n (F - P)‖ ≤ 2 * ε := by
    have h1 : ‖circleMean (F - P)‖ ≤ ε := circleMean_norm_le hclose
    have h2 : ‖trapMean n (F - P)‖ ≤ ε := trapMean_norm_le n hn hclose
    calc ‖circleMean (F - P) - trapMean n (F - P)‖
        ≤ ‖circleMean (F - P)‖ + ‖trapMean n (F - P)‖ := norm_sub_le _ _
      _ ≤ ε + ε := add_le_add h1 h2
      _ = 2 * ε := by ring
  calc ‖(circleMean (F - P) - trapMean n (F - P)) + (circleMean P - trapMean n P)‖
      ≤ ‖circleMean (F - P) - trapMean n (F - P)‖ + ‖circleMean P - trapMean n P‖ :=
        norm_add_le _ _
    _ ≤ 2 * ε + M * q ^ n * (2 * (K : ℝ) + 1) := add_le_add htail hPbound
    _ = M * q ^ n * (2 * (K : ℝ) + 1) + 2 * ε := by ring

end LemmaLibrary.Quadrature
