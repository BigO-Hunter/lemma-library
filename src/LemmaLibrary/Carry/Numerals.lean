/-
`LemmaLibrary.Carry.Numerals` — the arithmetic core of base-`2^w` exactness.

Two facts, and they are the whole story of why the carry chain needs no propagation
step: in base `2^w` the digits *are* the carries.

* `mod_mul_split` — `N % (a·b) = N % a + (N/a % b)·a`.  The low part and the carry
  digit, with no hypothesis beyond `a, b > 0`.
* `sum_base_digits` — reading `stride` base-`2^w` digits back and re-placing them sums
  to `N % 2^{w·stride}` **exactly**.  Losslessness, by induction on the split above.

`payloadStride w fracBits = ⌈fracBits/w⌉ + 1` and `payloadStride_mul_spec` record the
layout fact the exactness needs: `payloadStride` words hold `fracBits + w` bits, so the
`+1` word is a carry word with a full word of headroom, not padding.

Provenance: `kapila-row-lane` `SubsetSumL25/Row/KapilaEstimate.lean` §8.6 (commits
`faad906` / `7e6cc7d` / `6a1cfac` all touch this layer; the exactness layer is
`6a1cfac` "PayloadCarries is a data contract — the classification, and its seam
record").
-/
import Mathlib

namespace LemmaLibrary.Carry

set_option maxHeartbeats 1600000

/-- **Base decomposition.**  `N % (a·b)` split into its low part `N % a` and the
carry digit `(N / a) % b` at place `a`.  This is the only arithmetic fact the
carry chain needs, and it holds for every `a, b > 0`. -/
theorem mod_mul_split (N a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    N % (a * b) = N % a + (N / a % b) * a := by
  have hN : N = (a * b) * (N / (a * b)) + N % (a * b) := (Nat.div_add_mod N (a * b)).symm
  set r := N % (a * b) with hr
  have hlt : r < a * b := Nat.mod_lt _ (by positivity)
  have h1 : (a * b) * (N / (a * b)) + r = r + a * (b * (N / (a * b))) := by
    rw [Nat.mul_assoc a b (N / (a * b)), Nat.add_comm]
  have hdiv : N / a = r / a + b * (N / (a * b)) := by
    conv_lhs => rw [hN]
    rw [h1, Nat.add_mul_div_left _ _ ha]
  have hmodA : N % a = r % a := by
    conv_lhs => rw [hN]
    rw [Nat.mul_assoc a b (N / (a * b))]
    exact Nat.mul_add_mod_self_left a (b * (N / (a * b))) r
  have hmodB : N / a % b = r / a := by
    rw [hdiv, Nat.add_mul_mod_self_left (r / a) b (N / (a * b)), Nat.mod_eq_of_lt]
    exact Nat.div_lt_of_lt_mul hlt
  have hfin : r = r % a + (r / a) * a := by
    have h := Nat.div_add_mod r a
    rw [Nat.mul_comm a (r / a), Nat.add_comm] at h
    exact h.symm
  calc N % (a * b) = r := hr.symm
    _ = r % a + (r / a) * a := hfin
    _ = N % a + (N / a % b) * a := by rw [← hmodA, ← hmodB]

/-- **The digits of a numerator recover it.**  Reading `stride` base-`2^w` digits
`N / 2^{w·j} % 2^w` and placing them at `2^{w·j}` sums to `N` modulo
`2^{w·stride}` — the losslessness the one-word reading lacks. -/
theorem sum_base_digits (N w stride : Nat) :
    ((List.range stride).map fun j => (N / 2 ^ (w * j) % 2 ^ w) * 2 ^ (w * j)).sum
      = N % 2 ^ (w * stride) := by
  induction stride with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [List.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add]
    exact (mod_mul_split N (2 ^ (w * k)) (2 ^ w) (by positivity) (by positivity)).symm

/-- **Words per estimate at the paper's parameters**: §6.2's `⌈n²/w⌉ + 1`, i.e.
the estimate's place-value digits plus the carry word. -/
def payloadStride (w fracBits : Nat) : Nat := (fracBits + w - 1) / w + 1

/-- **`payloadStride` words hold `fracBits + w` bits.**  The first conjunct is the
fit that makes the digits lossless; the second is the headroom the `+ 1` word
buys, which is why it is a carry word rather than padding. -/
theorem payloadStride_mul_spec {w : Nat} (hw : 0 < w) (fracBits : Nat) :
    fracBits ≤ w * payloadStride w fracBits
      ∧ fracBits + w ≤ w * payloadStride w fracBits := by
  have h := Nat.div_add_mod (fracBits + w - 1) w
  have hlt : (fracBits + w - 1) % w < w := Nat.mod_lt _ hw
  have h1 : fracBits ≤ w * ((fracBits + w - 1) / w) := by omega
  have h2 : w * payloadStride w fracBits = w * ((fracBits + w - 1) / w) + w := by
    unfold payloadStride
    rw [Nat.mul_succ]
  constructor
  · rw [h2]; omega
  · rw [h2]; omega
end LemmaLibrary.Carry
