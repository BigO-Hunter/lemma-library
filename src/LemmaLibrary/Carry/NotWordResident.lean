/-
`LemmaLibrary.Carry.NotWordResident` — **the negative that shapes the digitwise family**.

`numAt w f addr stride` is the stride-`k` estimate numerator read from a `Nat`-valued
state.  `numAt_not_word` is the obstruction: at `stride ≥ 1` and a nonzero top digit the
numerator is `≥ 2^w`, so it is **not representable in a `BitVec w` cell** — a stride-`k`
read cannot be a single load, whatever the program does.  The stride-1 contrast is
`numAt_one_lt`.

This theorem is not a gap; it is the design fact that says the wide comparison must be
*reshaped* (digitwise, `LemmaLibrary.Digitwise.HalfTest`) rather than *widened*.

Provenance: `kapila-row-lane` `SubsetSumL25/Row/KapilaWide.lean` §W1–§W3 (commit
`7e6cc7d` "the stride-k payload read — the fold is numAt, and the charge is
stride-invariant").
-/
import Mathlib
import LemmaLibrary.Carry.Numerals

namespace LemmaLibrary.Carry

set_option maxHeartbeats 1600000

/-- **The stride-`k` estimate numerator.**  The `stride` words at `addr`, read
little-endian as a base-`2^w` integer: `Σ_{j<stride} f (addr + j) · 2^{w·j}`.
This is `placeValueAt`'s numerator with the memory's `BitVec` replaced by the
`ℕ`-valued state — §W2 proves the two agree. -/
def numAt (w : Nat) (f : Nat → Nat) (addr stride : Nat) : Nat :=
  ((List.range stride).map fun j => f (addr + j) * 2 ^ (w * j)).sum

/-- The empty read is zero — the reader's base case. -/
@[simp] theorem numAt_zero (w : Nat) (f : Nat → Nat) (addr : Nat) : numAt w f addr 0 = 0 := by
  simp [numAt]

/-- **The reader's carry step** (in `ℕ`): reading one more word at `addr + stride`
adds exactly its place value `word · 2^{w·stride}`.  This is `placeValueAt_succ`
without the shared denominator, and it is the reason a stride-`k` read composes
word by word. -/
theorem numAt_succ (w : Nat) (f : Nat → Nat) (addr stride : Nat) :
    numAt w f addr (stride + 1)
      = numAt w f addr stride + f (addr + stride) * 2 ^ (w * stride) := by
  unfold numAt
  rw [List.sum_range_succ]

/-- **The stride-1 read is the landed one-word read.** -/
theorem numAt_one (w : Nat) (f : Nat → Nat) (addr : Nat) : numAt w f addr 1 = f addr := by
  rw [show (1 : Nat) = 0 + 1 from rfl, numAt_succ, numAt_zero, Nat.zero_add]
  simp

/-- **A stride-1 read always fits a word** — the contrast with `numAt_not_word`
below, and the reason `wordList`/`memOf` could be stride-1 shapes at all. -/
theorem numAt_one_lt {w : Nat} (f : Nat → Nat) (hfit : ∀ z, f z < 2 ^ w) (addr : Nat) :
    numAt w f addr 1 < 2 ^ w := by
  rw [numAt_one]
  exact hfit addr

/-- **The top digit is a lower bound.**  Reading one more word adds its place
value to a nonnegative sum, so the last word read dominates from below. -/
theorem numAt_ge_top (w : Nat) (f : Nat → Nat) (addr stride : Nat) :
    f (addr + stride) * 2 ^ (w * stride) ≤ numAt w f addr (stride + 1) := by
  rw [numAt_succ]
  exact Nat.le_add_left _ _

/-- **The k-word sum overflows the word.**  At `stride ≥ 1`, a nonzero top digit
makes the reader's value at least `2^w`: the read is *not* representable in a
`BitVec w` cell, so `memOf` cannot hold it and `scanProg`'s `load` cannot produce
it.  The stride-1 contrast is `numAt_one_lt` — which is exactly why the landed
`wordList`/`memOf` shapes are stride 1.

**Consequence, and it is a design fact rather than a missing lemma.**  Residual
(i) as worded («the loop's per-iteration read becomes the k-word summing read»)
is not implementable in the `BitVec w` state.  A stride-`k` payload needs either
(a) a top-down **digitwise** comparison — `stride` word compares, no single cell
ever holding the numerator — or (b) a multi-word output block with its own carry
chain, which is the layout `KapilaEstimate` already proves exact
(`placeValueAt_payloadStride`) but which the scan's `load`/`add` sequence does
not yet write.  Either way the `hitWord` single-cell form cannot host the wide
test, so the remaining work is a *comparison* re-shaping, not a read widening. -/
theorem numAt_not_word {w stride : Nat} (hs : 1 ≤ stride) (f : Nat → Nat) (addr : Nat)
    (hpos : 0 < f (addr + stride)) : 2 ^ w ≤ numAt w f addr (stride + 1) := by
  have h1 := numAt_ge_top w f addr stride
  have h4 : 2 ^ w ≤ 2 ^ (w * stride) := by
    apply Nat.pow_le_pow_right (by norm_num)
    calc w = w * 1 := (Nat.mul_one w).symm
      _ ≤ w * stride := Nat.mul_le_mul_left w hs
  have h2 : 2 ^ w ≤ f (addr + stride) * 2 ^ (w * stride) := by
    calc 2 ^ w ≤ 2 ^ (w * stride) := h4
      _ = 1 * 2 ^ (w * stride) := (one_mul _).symm
      _ ≤ f (addr + stride) * 2 ^ (w * stride) := Nat.mul_le_mul_right _ hpos
  exact le_trans h2 h1

/-- **The overflow is not an artefact of the top digit being large**: one unit of
top digit suffices.  Stated separately so the obstruction cannot be read as a
bound that a smaller layout would dodge. -/
theorem numAt_not_word_one {w stride : Nat} (hs : 1 ≤ stride) (f : Nat → Nat) (addr : Nat)
    (hpos : 1 ≤ f (addr + stride)) : 2 ^ w ≤ numAt w f addr (stride + 1) :=
  numAt_not_word hs f addr (by omega)

/-! ### §W4 — the loop's step at stride `k`, and the exit fold

`scan_loop`'s induction consumes two facts per iteration: the head pair is the
address the loop's counter names, and the accumulator over `m+1` pairs is the head
pair plus the accumulator over `m`.  At stride `k` those are the same facts with
`stride` substituted for `1` — the address advances by a stride, and the block is
`numBlock`, not `wordList`.  Proved here at the loop's own granularity, so wiring
them in is a substitution rather than a re-derivation. -/
end LemmaLibrary.Carry
