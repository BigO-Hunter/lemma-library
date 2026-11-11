#!/usr/bin/env python3
"""Extract families 2–4 of the lemma library from the kapila-row lane."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from extract import extract  # noqa: E402

SRC = Path("/Volumes/Substrate-1/bigo/kapila-row-lane/SubsetSumL25/Row")
OUT = Path("/Volumes/Substrate-1/bigo/lemma-library/src/LemmaLibrary")

# ---------------------------------------------------------------- family 2
NUM_HEAD = '''/-
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

'''

NUM_NAMES = ["mod_mul_split", "sum_base_digits", "payloadStride", "payloadStride_mul_spec"]

PV_HEAD = '''/-
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

'''

MEMOF = """
/-- Memory of a `ℕ`-valued state.  (From `Row/KapilaPrelim.lean`; carried here because
`digHalf_eq_ratTest` needs the `BitVec` layer, and the library keeps that boundary
explicit rather than importing the row's whole preliminary layer.) -/
def memOf (w : Nat) (f : Nat → Nat) : Nat → BitVec w :=
  fun i => BitVec.ofNat w (f i)

"""

PV_NAMES = ["placeValue", "placeValue_one", "placeValue_nonneg", "placeValue_scale",
            "placeValueAt", "placeValue_eq_placeValueAt", "placeValueAt_zero",
            "placeValueAt_succ", "placeValueAt_digits", "placeValueAt_payloadStride",
            "placeValue_payloadStride"]

NW_HEAD = '''/-
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

'''

NW_NAMES = ["numAt", "numAt_zero", "numAt_succ", "numAt_one", "numAt_one_lt",
            "numAt_ge_top", "numAt_not_word", "numAt_not_word_one"]

RS_HEAD = """/-
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
"""

RS_NAMES_EST = ["memOf_toNat"]
RS_NAMES_WIDE = ["numAt_cast", "numAt_eq_placeValueAt_scale", "placeValue_eq_scale_numAt"]

# the comparison vocabulary `hitWord` lives in, needed by halfTest_iff_wordDiff
HIT_NAMES = ["hitOf", "hitWord", "hitOf_eq_one", "hitOf_eq_zero", "hitWord_eq_one_iff",
             "hitWord_eq_ratTest"]

# ---------------------------------------------------------------- family 3
DIG_HEAD = '''/-
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

'''

WORDDIFF_NAMES = ["wordDiff", "wordDiff_of_lt", "wordDiff_of_ge"]

DIG_NAMES = ["numAt_add_one_le",
             "numAt_lt_pow", "numAt_eq_of_lt", "numAt_split", "mul_add_le_iff",
             "cmpDigitsFrom", "cmpDigitsFrom_iff", "hit_of_above", "hit_of_below",
             "tie_hit_iff", "tieA_hit_iff", "miss_of_close"]

HT_HEAD = '''/-
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

'''

HT_NAMES = ["halfTest_iff_wordDiff", "placeValueAt_eq_scale_numAt", "digHalf",
            "digHalf_eq_threshold_pow", "digHalf_eq_threshold", "digHalf_eq_ratTest",
            "digHalf_eq_placeValueTest", "digHalf_spot_checks"]


def main():
    extract(SRC / "KapilaEstimate.lean", NUM_NAMES, OUT / "Carry" / "Numerals.lean",
            NUM_HEAD, "end LemmaLibrary.Carry\n")
    extract(SRC / "KapilaEstimate.lean", PV_NAMES, OUT / "Carry" / "PlaceValue.lean",
            PV_HEAD, MEMOF + "end LemmaLibrary.Carry\n")
    extract(SRC / "KapilaWide.lean", NW_NAMES, OUT / "Carry" / "NotWordResident.lean",
            NW_HEAD, "end LemmaLibrary.Carry\n")
    tmp = OUT / "Digitwise" / ".worddiff.tmp"
    extract(SRC / "KapilaLoop.lean", WORDDIFF_NAMES, tmp, "")
    wd = tmp.read_text().strip()
    tmp.unlink()
    hit_tmp = OUT / "Digitwise" / ".hit.tmp"
    extract(SRC / "KapilaLoop.lean", HIT_NAMES, hit_tmp, "")
    hit = hit_tmp.read_text().strip()
    hit_tmp.unlink()
    extract(SRC / "KapilaDigitwise.lean", DIG_NAMES, OUT / "Digitwise" / "Core.lean",
            DIG_HEAD + wd + "\n\n" + hit + "\n\n", "end LemmaLibrary.Digitwise\n")
    # reader scale: the numAt <-> placeValueAt bridge (two source files)
    a = OUT / "Carry" / ".rs-est.tmp"
    b = OUT / "Carry" / ".rs-wide.tmp"
    extract(SRC / "KapilaEstimate.lean", RS_NAMES_EST, a, "")
    extract(SRC / "KapilaWide.lean", RS_NAMES_WIDE, b, "")
    body = a.read_text().strip() + "\n\n" + b.read_text().strip()
    a.unlink(); b.unlink()
    (OUT / "Carry" / "ReaderScale.lean").write_text(RS_HEAD + "\n\n" + body +
                                                    "\n\nend LemmaLibrary.Carry\n")
    print("ReaderScale.lean written")
    extract(SRC / "KapilaDigitwise.lean", HT_NAMES, OUT / "Digitwise" / "HalfTest.lean",
            HT_HEAD, "end LemmaLibrary.Digitwise\n")


if __name__ == "__main__":
    main()
