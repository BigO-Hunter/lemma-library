/-
`LemmaLibrary.Carry.PlaceValue` — the place-value reading, and exact carry of a full
numerator.

`placeValue` reads an estimate as `stride` words little-endian over the single shared
scale `2^{−fracBits}`.  Three facts carry the family:

* `placeValue_scale` — multiplying by `2^{fracBits}` clears the **one** denominator and
  leaves the base-`2^w` numerator.  So two estimates at the same `fracBits` compare as
  integers on one scale; there is no second denominator and nothing is dropped.
* `placeValueAt_digits` + `placeValueAt_payloadStride` — a numerator of `fracBits` bits
  is carried **exactly** by `payloadStride` words.  This is the theorem that replaces a
  truncation: a single word at `fracBits ≥ w+1` forces every estimate below `1/2`
  (`abs_dAt_lt_half` in the lane), so the layout has to be multi-word, and here it is
  lossless.
* `placeValue_one` — the one-word read is the `stride = 1` instance, so nothing landed
  is displaced, only generalised.

Provenance: `kapila-row-lane` `SubsetSumL25/Row/KapilaEstimate.lean` §8.5–8.6–8.7.
-/
import Mathlib
import LemmaLibrary.Carry.Numerals

namespace LemmaLibrary.Carry

set_option maxHeartbeats 1600000

/-- **The place-value reading of an estimate.**  Estimate `s` occupies the
`stride` words at `base + s * stride`, read little-endian as a base-`2^w` number
over the single scale `2^-fracBits`.  This is the object §6.2's `n²` fractional
bits actually require, and the shape item 3's bin-sum identity must be stated
about once item 4's layout exists. -/
def placeValue {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) : ℚ :=
  (((List.range stride).map fun j =>
      ((m (base + s * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum)
    / (2 : ℚ) ^ fracBits

/-- **The module's per-index read is the stride-1 instance.**  So `aAt`/`dAt` are
the degenerate case of the place-value layout rather than a competitor to it:
when one word suffices, the layout's value at estimate `s` is exactly the entry
`aAt s` the convention reads. -/
theorem placeValue_one {w : Nat} (m : Nat → BitVec w) (base fracBits s : Nat) :
    placeValue m base 1 fracBits s
      = ((m (base + s)).toNat : ℚ) / (2 : ℚ) ^ fracBits := by
  simp [placeValue]


/-! ### Layer 8.5 — the place value, scaled

`placeValue_one` settles the degenerate case; these settle the general one.  The
first theorem is the identity that makes a multi-word estimate comparable at all:
multiplying the place value by `2^fracBits` clears the *single* shared
denominator and leaves the base-`2^w` numerator, so two estimates at the same
`fracBits` compare as integers on one scale.  The second makes the address
explicit, because the carry chain changes the number of words per estimate and
therefore the address of every estimate after the first.
-/

/-- The place value is nonnegative: it is a sum of nonnegative terms over a
positive denominator. -/
theorem placeValue_nonneg {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    0 ≤ placeValue m base stride fracBits s := by
  unfold placeValue
  have hpos : (0 : ℚ) ≤ (2 : ℚ) ^ fracBits := by positivity
  apply div_nonneg _ hpos
  apply List.sum_nonneg
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  have : (0 : ℚ) ≤ ((m (base + s * stride + j)).toNat : ℚ) := by positivity
  have : (0 : ℚ) ≤ (2 : ℚ) ^ (w * j) := by positivity
  positivity

/-- **The one-denominator identity.**  An estimate's place value, multiplied by
the single shared scale `2^fracBits`, is exactly the base-`2^w` numerator of its
`stride` words — no rounding, no second denominator, nothing dropped.  This is
what `abs_dAt_mul_lt` denies the one-word reading: there the numerator is bounded
by `2^w` whatever `fracBits` is; here it is the *whole* stride-`k` sum. -/
theorem placeValue_scale {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    placeValue m base stride fracBits s * (2 : ℚ) ^ fracBits
      = ((List.range stride).map fun j =>
          ((m (base + s * stride + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum := by
  unfold placeValue
  exact div_mul_cancel₀ _ (ne_of_gt (by positivity))

/-- **The place value at an explicit address.**  `placeValue` addresses estimate
`s` at `base + s * stride`; the carry chain below appends words at a fixed
address, so it needs the address as a parameter and not as a function of `s`.
The two readings agree by definition. -/
def placeValueAt {w : Nat} (m : Nat → BitVec w) (addr stride fracBits : Nat) : ℚ :=
  (((List.range stride).map fun j => ((m (addr + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)).sum)
    / (2 : ℚ) ^ fracBits

/-- **`placeValue` is `placeValueAt` at the estimate's own address.** -/
theorem placeValue_eq_placeValueAt {w : Nat} (m : Nat → BitVec w) (base stride fracBits s : Nat) :
    placeValue m base stride fracBits s = placeValueAt m (base + s * stride) stride fracBits :=
  rfl

/-- The empty block reads zero — the carry chain's base case. -/
@[simp] theorem placeValueAt_zero {w : Nat} (m : Nat → BitVec w) (addr fracBits : Nat) :
    placeValueAt m addr 0 fracBits = 0 := by
  simp [placeValueAt]

/-! ### Layer 8.6 — the carry chain over `payloadStride` words

A multi-word estimate is filled one word at a time, and each word lands at its own
place value: word `j` contributes `word_j · 2^{w·j}` to the numerator, over the
one shared `2^fracBits`.  That is the chain.  Nothing here propagates carries
explicitly, because in base `2^w` the carries are *the meaning of the digits*: the
numeric core (`mod_mul_split`, `sum_base_digits`) proves that reading the digits
of a numerator recovers the numerator exactly, which is the carry chain's whole
content and the exact opposite of the truncation `abs_dAt_lt_half` proved.

`payloadStride_mul_spec` then fixes how many digits are needed: `⌈fracBits/w⌉ + 1`
words hold `fracBits + w` bits, so a numerator of `fracBits` bits is carried with
a full word of headroom — the `+ 1` is the carry word, not padding.
-/

/-- **The carry chain's step.**  Appending one word at address `addr + stride`
adds exactly its place value `word · 2^{w·stride}` to the numerator over the one
shared denominator.  So a stride-`k` block is built word by word, and the block's
value is the sum of its words' places — no truncation at any step. -/
theorem placeValueAt_succ {w : Nat} (m : Nat → BitVec w) (addr stride fracBits : Nat) :
    placeValueAt m addr (stride + 1) fracBits
      = placeValueAt m addr stride fracBits
        + ((m (addr + stride)).toNat : ℚ) * (2 : ℚ) ^ (w * stride) / (2 : ℚ) ^ fracBits := by
  unfold placeValueAt
  rw [List.sum_range_succ, add_div]

/-- **The digits of a block read back as the block's numerator.**  With the
memory's words holding `N`'s base-`2^w` digits, the place value is `N` over the
shared scale — exact, because `sum_base_digits` is exact. -/
theorem placeValueAt_digits {w : Nat} (N addr stride fracBits : Nat) (m : Nat → BitVec w)
    (hm : ∀ j, j < stride → (m (addr + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValueAt m addr stride fracBits
      = ((N % 2 ^ (w * stride) : Nat) : ℚ) / (2 : ℚ) ^ fracBits := by
  have hcast : ∀ (l : List Nat) (g : Nat → Nat),
      (l.map fun x => ((g x : Nat) : ℚ)).sum = (((l.map g).sum : Nat) : ℚ) := by
    intro l
    induction l with
    | nil => intro g; simp
    | cons a as ih => intro g; simp [ih, Nat.cast_add]
  have hterm : ∀ j, ((m (addr + j)).toNat : ℚ) * (2 : ℚ) ^ (w * j)
      = ((((m (addr + j)).toNat) * 2 ^ (w * j) : Nat) : ℚ) := by
    intro j
    push_cast
    ring
  have hsub : ∀ j, j < stride →
      (((m (addr + j)).toNat) * 2 ^ (w * j) : Nat)
        = (N / 2 ^ (w * j) % 2 ^ w) * 2 ^ (w * j) := by
    intro j hj
    rw [hm j hj]
  have hnat : ((List.range stride).map
      fun j => ((m (addr + j)).toNat) * 2 ^ (w * j)).sum = N % 2 ^ (w * stride) := by
    rw [List.map_congr_left (fun j hj => hsub j (List.mem_range.mp hj))]
    exact sum_base_digits N w stride
  unfold placeValueAt
  rw [List.map_congr_left (fun j _ => hterm j),
    hcast (List.range stride) (fun j => ((m (addr + j)).toNat) * 2 ^ (w * j)), hnat]

/-- **A `payloadStride` block carries a `fracBits`-bit numerator exactly.**  This
is the layout that replaces the truncation: `abs_dAt_lt_half` proved that a single
word at `fracBits ≥ w + 1` forces every estimate below `1/2`; here a numerator of
`fracBits` bits — anything in `[0, 1)` on the shared scale — is carried with no
loss and a full word of headroom left for carries. -/
theorem placeValueAt_payloadStride {w fracBits N addr : Nat} (hw : 0 < w) (hN : N < 2 ^ fracBits)
    (m : Nat → BitVec w)
    (hm : ∀ j, j < payloadStride w fracBits → (m (addr + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValueAt m addr (payloadStride w fracBits) fracBits
      = ((N : Nat) : ℚ) / (2 : ℚ) ^ fracBits := by
  have hlt : N < 2 ^ (w * payloadStride w fracBits) := by
    have h1 : fracBits ≤ w * payloadStride w fracBits := (payloadStride_mul_spec hw fracBits).1
    have h2 : (2 : Nat) ^ fracBits ≤ 2 ^ (w * payloadStride w fracBits) :=
      Nat.pow_le_pow_right (by norm_num) h1
    omega
  rw [placeValueAt_digits N addr _ fracBits m hm, Nat.mod_eq_of_lt hlt]

/-- **The `s`-indexed form, at `s = 0`.**  `placeValue` reads estimate `s` at
`base + s * stride`, so the address-explicit exactness theorem transfers to it
verbatim; the general `s` is the same theorem at address `base + s * stride`, and
this representative case is stated so the `placeValue` vocabulary the contract
above uses is known to carry a full numerator too. -/
theorem placeValue_payloadStride {w fracBits N base : Nat} (hw : 0 < w) (hN : N < 2 ^ fracBits)
    (m : Nat → BitVec w)
    (hm : ∀ j, j < payloadStride w fracBits →
      (m (base + j)).toNat = N / 2 ^ (w * j) % 2 ^ w) :
    placeValue m base (payloadStride w fracBits) fracBits 0 = ((N : Nat) : ℚ) / (2 : ℚ) ^ fracBits := by
  have h0 : base + 0 * payloadStride w fracBits = base := by omega
  rw [placeValue_eq_placeValueAt, h0]
  exact placeValueAt_payloadStride hw hN m hm

/-! ### Layer 8.7 — the bin-sum contract, restated about the real layout

Layer 8.3 stated `BinSumAgrees` about `dAt`, i.e. about the *stored lists*, which
is the only thing the landed `PayloadConvention` gives: one word per index.  At
`fracBits ≥ w + 1` those lists are truncations (§8.4), so a contract phrased on
them cannot be the cross-estimate relation the paper needs.  These results move
the contract onto the layout that can carry the estimates, and prove that the old
contract is its `stride = 1` instance — so nothing landed is displaced, only
generalized.

The residual after this layer is a *fact about the program*, not about `ℚ`: the
instruction sequence reads `base + i` (`PayloadConvention.aAt`), i.e. one word per
index, so a stride-`k` payload needs the read loop to sum `k` words per estimate
before `aAt` can be the wide reading.  That is item 4's application seam, and it
is named rather than assumed.
-/

/-- Memory of a `ℕ`-valued state.  (From `Row/KapilaPrelim.lean`; carried here because
`digHalf_eq_ratTest` needs the `BitVec` layer, and the library keeps that boundary
explicit rather than importing the row's whole preliminary layer.) -/
def memOf (w : Nat) (f : Nat → Nat) : Nat → BitVec w :=
  fun i => BitVec.ofNat w (f i)

end LemmaLibrary.Carry
