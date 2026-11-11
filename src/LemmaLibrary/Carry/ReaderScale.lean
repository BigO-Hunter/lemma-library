/-
`LemmaLibrary.Carry.ReaderScale` — the `numAt` ↔ `placeValueAt` bridge.

The exactness family (`placeValue*`) is stated over `BitVec w` memory; the decision
family (`numAt`, `wordDiff`) is stated over a `Nat`-valued state.  These four lemmas tie
them: `numAt_cast` lifts the reader's value to `ℚ`, `memOf_toNat` removes the `BitVec`
layer under a fit hypothesis, and `numAt_eq_placeValueAt_scale` /
`placeValue_eq_scale_numAt` are the two directions of the one-denominator identity —
*no rounding, no second denominator*.  Without this bridge `digHalf_eq_ratTest` could not
state the walk's correctness in the paper's own `ℚ` vocabulary.

Provenance: `kapila-row-lane` `Row/KapilaEstimate.lean` @ `c41d4e5` (`memOf_toNat`) and
`Row/KapilaWide.lean` @ `f395f3c` (§W2).
-/
import Mathlib
import LemmaLibrary.Carry.Numerals
import LemmaLibrary.Carry.PlaceValue
import LemmaLibrary.Carry.NotWordResident

namespace LemmaLibrary.Carry

set_option maxHeartbeats 1600000


/-- Reading a word back to `ℕ` under fit — the step that removes `BitVec`. -/
theorem memOf_toNat {w : Nat} (f : Nat → Nat) (hfit : ∀ i, f i < 2 ^ w) (i : Nat) :
    (memOf w f i).toNat = f i := by
  show (BitVec.ofNat w (f i)).toNat = f i
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfit i)]

/-- **The reader's value, cast to `ℚ`, is the place value's numerator.**  A
`ℕ`-level identity: the sum of the `2^{w·j}`-weighted words, cast, is the sum of
the casts.  Stated at top level so its induction does not drag the surrounding
`have`s into a reverted context. -/
theorem numAt_cast {w : Nat} (f : Nat → Nat) (addr stride : Nat) :
    (numAt w f addr stride : ℚ)
      = ((List.range stride).map
          fun j => ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
  induction stride with
  | zero => simp [numAt]
  | succ m ih =>
    rw [numAt_succ, Nat.cast_add, ih, List.sum_range_succ]
    congr 1
    push_cast
    ring

/-- **The reader's value, multiplied out, is the place value.**  `numAt` over the
`ℕ` state equals `placeValueAt` under the one shared `2^fracBits` — no rounding,
no second denominator.  This is `placeValue_scale` seen from the `ℕ` side. -/
theorem numAt_eq_placeValueAt_scale {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (addr stride fracBits : Nat) :
    (numAt w f addr stride : ℚ)
      = placeValueAt (memOf w f) addr stride fracBits * (2 : ℚ) ^ fracBits := by
  have hterm : ∀ j : Nat, ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)
      = ((f (addr + j) * 2 ^ (w * j) : Nat) : ℚ) := by
    intro j
    push_cast
    ring
  have hstep : ∀ j : Nat, ((memOf w f (addr + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)
      = ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j) := by
    intro j
    rw [memOf_toNat f hfit (addr + j)]
  have hkey : placeValueAt (memOf w f) addr stride fracBits * (2 : ℚ) ^ fracBits
      = ((List.range stride).map
          fun j => ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
    unfold placeValueAt
    rw [div_mul_cancel₀ _ (ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ fracBits))]
    rw [List.map_congr_left (fun j _ => hstep j)]
  have hnum : ((numAt w f addr stride : Nat) : ℚ)
      = ((List.range stride).map
          fun j => ((f (addr + j) : Nat) : ℚ) * (2 : ℚ) ^ (w * j)).sum :=
    numAt_cast f addr stride
  rw [hnum, hkey]

/-- **The place value *is* the scaled reader** — the direction a layout consumes. -/
theorem placeValue_eq_scale_numAt {w : Nat} (f : Nat → Nat) (hfit : ∀ x, f x < 2 ^ w)
    (base stride fracBits s : Nat) :
    placeValue (memOf w f) base stride fracBits s
      = (numAt w f (base + s * stride) stride : ℚ) / (2 : ℚ) ^ fracBits := by
  have h := numAt_eq_placeValueAt_scale f hfit (base + s * stride) stride fracBits
  rw [placeValue_eq_placeValueAt,
    eq_div_iff (ne_of_gt (by positivity : (0 : ℚ) < (2 : ℚ) ^ fracBits))]
  exact h.symm

end LemmaLibrary.Carry
