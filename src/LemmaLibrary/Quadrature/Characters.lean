/-
`LemmaLibrary.Quadrature.Characters` — the exactness core of the periodic trapezoid rule.

This is the mathematical content of the quadrature lemma and it is *not* a Lipschitz
bound: the `n`-point periodic trapezoid rule reproduces the mean of every character
`x ↦ e^{ikx}` with `|k| < n` **exactly**, so the error functional `E_n = circleMean −
trapMean n` annihilates every character except the aliased frequencies with `k ≠ 0` and
`n ∣ k`.  That exactness is what makes the error decay geometrically rather than like
`1/n²`, and it is invisible to any Lipschitz route (see `LemmaLibrary.Quadrature.Strip`
for the measurement that closes the Lipschitz route at `n ≥ 7.7·10¹⁷`).

Provenance: ported verbatim from `kapila-row-lane` `SubsetSumL25/Row/JV1000Strip.lean`
§0–§5 (commit `76f9fdc` "the strip-analyticity quadrature lemma, proved — and q0 was
never a decay base"), recompiled from source in this package.  Namespace renamed from
`SubsetSumL25.Row`; nothing else changed.
-/
import Mathlib

namespace LemmaLibrary.Quadrature

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000


/-! ### §0 — the two means

The `n`-point periodic trapezoid mean and the circle mean, stated over `ℂ` because the
characters are complex and the real case follows by `‖re z‖ ≤ ‖z‖`. -/

/-- The `n`-point periodic trapezoid mean on the circle of circumference `2π`. -/
noncomputable def trapMean (n : ℕ) (F : ℝ → ℂ) : ℂ :=
  (1 / (n : ℂ)) * ∑ j ∈ Finset.range n, F (2 * Real.pi * (j : ℝ) / (n : ℝ))

/-- The circle mean `(1/2π)∫_0^{2π}`. -/
noncomputable def circleMean (F : ℝ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ x in (0 : ℝ)..(2 * Real.pi), F x

/-- The character `x ↦ e^{i m x}`. -/
noncomputable def charF (m : ℤ) : ℝ → ℂ := fun x => Complex.exp ((m : ℂ) * x * Complex.I)

/-! ### §1 — the character sum: the trapezoid rule is exact on low frequencies

`Σ_{j<n} e^{2πi m j/n} = n` if `n ∣ m` and `0` otherwise.  This single identity is why
the periodic trapezoid rule is spectrally accurate: the rule reproduces every
character's mean exactly, so its error is carried entirely by the aliased frequencies
`m = n·k`. -/

theorem char_sum (n : ℕ) (hn : 0 < n) (m : ℤ) :
    ∑ j ∈ Finset.range n,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ)))
      = if (n : ℤ) ∣ m then (n : ℂ) else 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  set ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (n : ℂ)) with hω
  -- every summand is a power of `ω`
  have hterm : ∀ j : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ)))
        = ω ^ j := by
    intro j
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  -- `ω ^ n = 1` for every `m`
  have hωn : ω ^ n = 1 := by
    rw [hω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨m, by push_cast; field_simp⟩
  by_cases hdiv : (n : ℤ) ∣ m
  · -- every term is `1`, so the sum is `n`
    rw [if_pos hdiv]
    obtain ⟨q, hq⟩ := hdiv
    have hone : ∀ j : ℕ, ω ^ j = 1 := by
      intro j
      rw [hω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      refine ⟨q * (j : ℤ), ?_⟩
      rw [hq]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl fun j _ => hone j]
    simp
  · -- `ω ≠ 1`, so the sum is a geometric series whose ratio is off the root
    rw [if_neg hdiv]
    have hω1 : ω ≠ 1 := by
      intro h
      rw [hω] at h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨k, hk⟩ := h
      have hkey : (n : ℂ) * (k : ℂ) = (m : ℂ) := by
        have hk' := hk
        field_simp at hk'
        exact hk'.symm
      exact hdiv ⟨k, by exact_mod_cast hkey.symm⟩
    rw [geom_sum_eq hω1 n, hωn]
    simp

/-! ### §2 — the character's circle mean

`(1/2π)∫_0^{2π} e^{i m x} dx = 1` if `m = 0` and `0` otherwise — the fundamental
orthogonality, by the fundamental theorem of calculus with the explicit antiderivative
`e^{i m x}/(i m)`. -/

theorem integral_char (m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), charF m x
      = if m = 0 then (2 * (Real.pi : ℂ)) else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [charF]
  · have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero hmC Complex.I_ne_zero
    rw [if_neg hm]
    have hpt : ∀ x : ℝ, charF m x = Complex.exp (((m : ℂ) * Complex.I) * (x : ℂ)) := by
      intro x
      simp only [charF]
      congr 1
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_exp_mul_complex hc]
    have hz : Complex.exp (((m : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨m, by push_cast; ring⟩
    rw [hz]
    simp

/-! ### §3 — the error functional on characters

Putting §1 and §2 together: `E_n(e^{i m x})` is `−1` exactly on the aliased nonzero
frequencies and `0` everywhere else.  This is the whole content of "the trapezoid rule
is exact on low frequencies". -/

theorem trapMean_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    trapMean n (charF m) = if (n : ℤ) ∣ m then 1 else 0 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold trapMean
  have hpt : ∀ j : ℕ, charF m (2 * Real.pi * (j : ℝ) / (n : ℝ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m : ℂ) * (j : ℂ)) / (n : ℂ))) := by
    intro j
    simp only [charF]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hpt j, char_sum n hn m]
  by_cases h : (n : ℤ) ∣ m
  · rw [if_pos h, if_pos h]
    field_simp
  · rw [if_neg h, if_neg h, mul_zero]

theorem circleMean_char (m : ℤ) :
    circleMean (charF m) = if m = 0 then 1 else 0 := by
  unfold circleMean
  rw [integral_char m]
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : m = 0
  · rw [if_pos h, if_pos h]
    field_simp
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The error functional annihilates every character except the aliased frequencies.** -/
theorem trap_error_char (n : ℕ) (hn : 0 < n) (m : ℤ) :
    circleMean (charF m) - trapMean n (charF m)
      = if (n : ℤ) ∣ m ∧ m ≠ 0 then (-1 : ℂ) else 0 := by
  rw [circleMean_char m, trapMean_char n hn m]
  by_cases hm : m = 0
  · subst hm
    simp
  · rw [if_neg hm]
    by_cases h : (n : ℤ) ∣ m
    · rw [if_pos h, if_pos ⟨h, hm⟩]; ring
    · rw [if_neg h, if_neg (fun hc => h hc.1)]; ring

/-! ### §4 — the two norm bounds the assembly needs -/

/-- The trapezoid mean is bounded by the sup norm: a mean of `n` numbers. -/
theorem trapMean_norm_le (n : ℕ) (hn : 0 < n) {h : ℝ → ℂ} {ε : ℝ}
    (hε : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖h x‖ ≤ ε) : ‖trapMean n h‖ ≤ ε := by
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) (hε 0 ⟨le_rfl, by positivity⟩)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnode : ∀ j ∈ Finset.range n, ‖h (2 * Real.pi * (j : ℝ) / (n : ℝ))‖ ≤ ε := by
    intro j hj
    refine hε _ ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hnR]
    have hj' : (j : ℝ) < (n : ℝ) := by exact_mod_cast Finset.mem_range.1 hj
    nlinarith [Real.pi_pos]
  have hsum : ‖∑ j ∈ Finset.range n, h (2 * Real.pi * (j : ℝ) / (n : ℝ))‖ ≤ (n : ℝ) * ε := by
    calc ‖∑ j ∈ Finset.range n, h (2 * Real.pi * (j : ℝ) / (n : ℝ))‖
        ≤ ∑ j ∈ Finset.range n, ‖h (2 * Real.pi * (j : ℝ) / (n : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, ε := Finset.sum_le_sum hnode
      _ = (n : ℝ) * ε := by simp [Finset.sum_const, nsmul_eq_mul]
  unfold trapMean
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  calc (1 / (n : ℝ)) * ‖∑ j ∈ Finset.range n, h (2 * Real.pi * (j : ℝ) / (n : ℝ))‖
      ≤ (1 / (n : ℝ)) * ((n : ℝ) * ε) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = ε := by field_simp

/-- The circle mean is bounded by the sup norm: the integral is at most length × sup. -/
theorem circleMean_norm_le {h : ℝ → ℂ} {ε : ℝ}
    (hε : ∀ x ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖h x‖ ≤ ε) : ‖circleMean h‖ ≤ ε := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb : ‖∫ x in (0 : ℝ)..(2 * Real.pi), h x‖ ≤ 2 * Real.pi * ε := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := ε) (f := h) (fun x hx => by
        rw [Set.uIoc_of_le (le_of_lt h2pi)] at hx
        exact hε x ⟨le_of_lt hx.1, hx.2⟩)
    rw [sub_zero, abs_of_pos h2pi] at h
    linarith
  unfold circleMean
  rw [norm_mul]
  have hinv : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hinv]
  calc (1 / (2 * Real.pi)) * ‖∫ x in (0 : ℝ)..(2 * Real.pi), h x‖
      ≤ (1 / (2 * Real.pi)) * (2 * Real.pi * ε) := by
        apply mul_le_mul_of_nonneg_left hb; positivity
    _ = ε := by field_simp

/-! ### §5 — the elementary geometric tail

`Σ_{m<J} q^{m+1} ≤ q/(1−q)` for `0 ≤ q < 1`.  This is what turns a geometric bound on the
Fourier coefficients into the `qⁿ/(1−qⁿ)` of the quadrature error. -/

theorem geom_tail_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (J : ℕ) :
    ∑ m ∈ Finset.range J, q ^ (m + 1) ≤ q / (1 - q) := by
  have hq1' : (1 : ℝ) - q > 0 := by linarith
  have hgeom : ∀ J : ℕ, ∑ m ∈ Finset.range J, q ^ m = (1 - q ^ J) / (1 - q) := by
    intro J
    rw [geom_sum_eq (by linarith : q ≠ 1) J, div_eq_div_iff (by linarith) (by linarith)]
    ring
  have hsplit : ∑ m ∈ Finset.range J, q ^ (m + 1) = q * ∑ m ∈ Finset.range J, q ^ m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hsplit, hgeom]
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ hq1'.le
  nlinarith [pow_nonneg hq0 J]

/-! ### §6 — the assembly: the quadrature lemma

`E_n = circleMean − trapMean n` is additive and `ℂ`-homogeneous, so on a finite character
sum it is the sum of its values on the characters (§3), which vanish off the aliased
frequencies.  What remains is a `qⁿ` factor from the decay hypothesis and a cardinality
factor from the number of characters that CAN alias — which is exactly the `C` of a
`C·qⁿ` quadrature bound. -/

theorem trapMean_add (n : ℕ) (h₁ h₂ : ℝ → ℂ) :
    trapMean n (fun x => h₁ x + h₂ x) = trapMean n h₁ + trapMean n h₂ := by
  unfold trapMean
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem trapMean_smul (n : ℕ) (c : ℂ) (h : ℝ → ℂ) :
    trapMean n (fun x => c * h x) = c * trapMean n h := by
  unfold trapMean
  rw [← Finset.mul_sum]
  ring

theorem circleMean_add {h₁ h₂ : ℝ → ℂ}
    (hi₁ : IntervalIntegrable h₁ volume (0 : ℝ) (2 * Real.pi))
    (hi₂ : IntervalIntegrable h₂ volume (0 : ℝ) (2 * Real.pi)) :
    circleMean (fun x => h₁ x + h₂ x) = circleMean h₁ + circleMean h₂ := by
  unfold circleMean
  rw [intervalIntegral.integral_add hi₁ hi₂]
  ring

theorem circleMean_smul (c : ℂ) (h : ℝ → ℂ) :
    circleMean (fun x => c * h x) = c * circleMean h := by
  unfold circleMean
  rw [intervalIntegral.integral_const_mul]
  ring

theorem trapMean_sub (n : ℕ) (h₁ h₂ : ℝ → ℂ) :
    trapMean n (fun x => h₁ x - h₂ x) = trapMean n h₁ - trapMean n h₂ := by
  unfold trapMean
  rw [Finset.sum_sub_distrib]
  ring

theorem circleMean_sub {h₁ h₂ : ℝ → ℂ}
    (hi₁ : IntervalIntegrable h₁ volume (0 : ℝ) (2 * Real.pi))
    (hi₂ : IntervalIntegrable h₂ volume (0 : ℝ) (2 * Real.pi)) :
    circleMean (fun x => h₁ x - h₂ x) = circleMean h₁ - circleMean h₂ := by
  unfold circleMean
  rw [intervalIntegral.integral_sub hi₁ hi₂]
  ring

theorem trapMean_finset_sum (n : ℕ) (s : Finset ℤ) (c : ℤ → ℂ) :
    trapMean n (fun x => ∑ k ∈ s, c k * charF k x) = ∑ k ∈ s, c k * trapMean n (charF k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trapMean]
  | insert a s ha ih =>
    have hfun : (fun x => ∑ k ∈ insert a s, c k * charF k x)
        = fun x => c a * charF a x + ∑ k ∈ s, c k * charF k x := by
      funext x
      rw [Finset.sum_insert ha]
    rw [hfun, trapMean_add, trapMean_smul, ih, Finset.sum_insert ha]

theorem circleMean_finset_sum (s : Finset ℤ) (c : ℤ → ℂ) :
    circleMean (fun x => ∑ k ∈ s, c k * charF k x) = ∑ k ∈ s, c k * circleMean (charF k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleMean]
  | insert a s ha ih =>
    have hfun : (fun x => ∑ k ∈ insert a s, c k * charF k x)
        = fun x => c a * charF a x + ∑ k ∈ s, c k * charF k x := by
      funext x
      rw [Finset.sum_insert ha]
    have hi₁ : IntervalIntegrable (charF a) volume (0 : ℝ) (2 * Real.pi) := by
      have : Continuous (charF a) := by unfold charF; fun_prop
      exact this.intervalIntegrable _ _
    have hi₂ : IntervalIntegrable (fun x => ∑ k ∈ s, c k * charF k x) volume (0 : ℝ) (2 * Real.pi) := by
      have : Continuous (fun x => ∑ k ∈ s, c k * charF k x) := by
        refine continuous_finset_sum _ fun k _ => ?_
        unfold charF; fun_prop
      exact this.intervalIntegrable _ _
    rw [hfun, circleMean_add (by simpa using hi₁.const_mul (c a)) hi₂, circleMean_smul, ih,
      Finset.sum_insert ha]


end LemmaLibrary.Quadrature
