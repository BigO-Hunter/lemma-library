/-
`LemmaLibrary` — the reusable lemmas extracted from the kapila-row / jv1000
formalisation campaign, ported as standalone modules with their own proofs.

Four families, each with the file that carries its statement:

  1. **Character-annihilation quadrature** (`LemmaLibrary.Quadrature.*`).
     `trapezoid_error_le_of_decay` — the periodic trapezoid rule is *exact* on every
     character of degree `< n`, so its error functional annihilates all but the aliased
     frequencies `n ∣ k`; given `|ĉ_k| ≤ M q^{|k|}` the error is `M qⁿ (2K+1) + 2ε`.
     `hdecay_of_strip` — the coefficient bound, derived by shifting the contour in
     `θ` (periodicity kills the rectangle's vertical sides; the endpoint is a limit).

  2. **Base-`2^w` carry exactness** (`LemmaLibrary.Carry.*`).
     `sum_base_digits` — the digits *are* the carries.  `placeValue_scale` — one shared
     denominator clears exactly.  `placeValueAt_payloadStride` — a `fracBits`-bit
     numerator is carried exactly by `⌈fracBits/w⌉+1` words.  `numAt_not_word` — the
     negative that shapes everything: a stride-`k` read is not word-resident.

  3. **Digitwise threshold decision** (`LemmaLibrary.Digitwise.*`).
     `digHalf_eq_threshold` — decide `(1/2 : ℚ) ≤ |V̂ − Â|` from two stride-`k` digit
     blocks *without materialising either numerator*; the threshold lives at digit
     `p = (F−1)/w`, bit `r = (F−1) mod w`, and `miss_of_close` shows the walk is one
     digit deep in the common case.

  4. **Envelope absorption** (`LemmaLibrary.Envelope.Absorb`).
     `envelopeAbsorb_mul` and `envelopeAbsorb_add` — multiplicative and additive cost
     charges are absorbed by raising the envelope's polynomial exponent.  Stated over
     an abstract cost model, which is the general form the row lemmas instantiate.

Not ported, cited: the Bonifaci energy-perturbation Lipschitz estimate
(`bonifaci-lane@e317bfe`, `Bonnifaci/M8.lean`) — already published; reference, do not
duplicate.  The row-specific instantiations (`quadrature_at_256_of_strip`,
`quadrature_at_256_of_strip_relaxed`, the `kapila_row` assembly) stay in the lane.
-/
import LemmaLibrary.Quadrature.Characters
import LemmaLibrary.Quadrature.Strip
import LemmaLibrary.Quadrature.Decay
import LemmaLibrary.Carry.Numerals
import LemmaLibrary.Carry.PlaceValue
import LemmaLibrary.Carry.NotWordResident
import LemmaLibrary.Digitwise.Core
import LemmaLibrary.Digitwise.HalfTest
import LemmaLibrary.Envelope.Absorb
