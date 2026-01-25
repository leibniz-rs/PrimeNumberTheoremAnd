import PrimeNumberTheoremAnd.ArtinLSeriesNat
import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffsSum

import Mathlib.Data.Finset.NatAntidiagonal

/-!
## Artin L-series: direct sums on prime powers (algebraic coefficient identity)

This file records the prime-power specialization of “Euler factors multiply under direct sums” at
the level of the induced coefficient function `coeffNat : ℕ → ℂ`.

Concretely, for a prime `p` and `k : ℕ`, the coefficient at `p^k` for `ρ₁ ⊕ ρ₂` is the Cauchy
convolution (over `Finset.antidiagonal k`) of the coefficients at `p^i` and `p^j` for `ρ₁` and
`ρ₂`.

No analytic summability or rearrangement is used here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators

namespace ArtinLSeries

namespace ArtinRep

open PrimeNumberTheoremAnd.ArtinLike

variable {G : Type*} [Group G]

variable (ρ₁ ρ₂ : ArtinLSeries.ArtinRep G)
variable (c : Nat.Primes → ConjClasses G)

/--
Prime-power coefficient identity for direct sums.
-/
theorem coeffNat_sum_prime_pow (p : Nat.Primes) (k : ℕ) :
    coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c (p.1 ^ k)
      =
    ∑ x ∈ Finset.antidiagonal k,
      coeffNat (ρ := ρ₁) c (p.1 ^ x.1) * coeffNat (ρ := ρ₂) c (p.1 ^ x.2) := by
  classical
  -- Abbreviate the three local coefficient systems.
  let A₁ : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ρ₁) c
  let A₂ : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ρ₂) c
  let As : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
  have hAs : As = LocalCoeffs.mul A₁ A₂ := by
    -- This is `localCoeffsOfConj_sum`, rewritten into the `localCoeffs` abbreviation.
    simpa [ArtinLSeries.localCoeffs] using
      (localCoeffsOfConj_sum (ρ₁ := ρ₁) (ρ₂ := ρ₂) (c := c))
  -- Evaluate both sides using `LocalCoeffs.coeff_prime_pow`.
  -- Left: coefficient for `ρ₁ ⊕ ρ₂` at `p^k`.
  have hp : (p.1).Prime := p.2
  -- `coeffNat` is `As.coeff`, and `As.coeff (p^k)` is `As.a p k`.
  -- Then unfold `LocalCoeffs.mul`.
  simp [ArtinLSeries.coeffNat, A₁, A₂, As, hAs, LocalCoeffs.mul, LocalCoeffs.coeff_prime_pow, hp]

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd

