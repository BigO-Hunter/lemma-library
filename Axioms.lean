import LemmaLibrary.Quadrature.Decay
import LemmaLibrary.Carry.PlaceValue
import LemmaLibrary.Carry.NotWordResident
import LemmaLibrary.Digitwise.HalfTest
import LemmaLibrary.Envelope.Absorb

/-! # Axiom banner — fail-closed

Every declaration this library claims must report only the house triple
`[propext, Classical.choice, Quot.sound]`.  No `sorryAx`, no `native_decide`
(which appears in the banner as `Lean.ofReduceBool`).

The banner is a *gate*, not a report: `receipts.py` fails the landing when this file
exits non-zero, when the word `sorryAx` appears, when `native_decide` /
`Lean.ofReduceBool` appears, or when any `depends on axioms:` line names anything
outside the house triple.  An **errored** banner run is not a clean banner — a
misspelled `#print axioms` prints nothing and exits non-zero, and a runner that only
scans for bad lines would call that a pass.
-/

open LemmaLibrary.Quadrature

-- family 1 — character-annihilation quadrature
#print axioms trap_error_char
#print axioms trapezoid_error_le_of_decay
#print axioms abs_fourierCoeff_le_decay
#print axioms hdecay_of_strip
#print axioms trapezoid_error_le_of_strip

-- family 2 — base-2^w carry exactness
#print axioms LemmaLibrary.Carry.sum_base_digits
#print axioms LemmaLibrary.Carry.placeValue_scale
#print axioms LemmaLibrary.Carry.placeValueAt_payloadStride
#print axioms LemmaLibrary.Carry.numAt_not_word

-- family 3 — digitwise threshold decision
#print axioms LemmaLibrary.Digitwise.miss_of_close
#print axioms LemmaLibrary.Digitwise.digHalf_eq_threshold
#print axioms LemmaLibrary.Digitwise.digHalf_eq_ratTest

-- family 4 — envelope absorption
#print axioms LemmaLibrary.Envelope.envelopeAbsorb_mul
#print axioms LemmaLibrary.Envelope.envelopeAbsorb_add
