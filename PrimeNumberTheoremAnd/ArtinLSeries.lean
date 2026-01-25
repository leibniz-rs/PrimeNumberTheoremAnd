import Mathlib

import PrimeNumberTheoremAnd.ArtinLikeLSeries
import PrimeNumberTheoremAnd.ArtinLSeriesEulerFactor
import PrimeNumberTheoremAnd.ArtinLSeriesConjugation
import PrimeNumberTheoremAnd.ArtinRepresentation
import PrimeNumberTheoremAnd.ArtinCharacter
import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffs
import PrimeNumberTheoremAnd.ArtinLSeriesNat
import PrimeNumberTheoremAnd.ArtinLSeriesNatPrimePowSum
import PrimeNumberTheoremAnd.ArtinLSeriesNatConvolutionSum

-- Direct sums (block diagonal)
import PrimeNumberTheoremAnd.ArtinRepresentationSum
import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffsSum

/-!
## Artin L-series (project entry point)

This file is the local “barrel” module for the Artin L-series development in this repository.

It only re-exports the algebraic infrastructure (Euler factors, conjugation invariance, local
coefficients, and the naive `ℕ`-Dirichlet-series package). No analytic continuation or nonvanishing
is asserted here.
-/

