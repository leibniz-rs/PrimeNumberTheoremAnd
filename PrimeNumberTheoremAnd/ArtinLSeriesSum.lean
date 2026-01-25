import Mathlib

import PrimeNumberTheoremAnd.ArtinRepresentationSum
import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffsSum

/-!
## Artin L-series: direct sums (algebraic layer)

This file packages the algebra needed for handling direct sums of Artin representations:

- `ArtinRepresentationSum`: the block-diagonal direct sum `ρ₁ ⊕ ρ₂`,
- `ArtinLSeriesLocalCoeffsSum`: compatibility of local coefficients with direct sums.

At this stage we only record algebraic identities (Euler factors / coefficients); no analytic
statement about multiplying the global L-series is asserted here.
-/

