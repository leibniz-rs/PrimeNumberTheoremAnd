import PrimeNumberTheoremAnd.ArtinRepresentationSum
import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffs

/-!
## Artin local coefficients: direct sums

For a fixed conjugacy-class assignment `c(p)`, the local coefficient system attached to the direct
sum representation `ρ₁ ⊕ ρ₂` is the pointwise Cauchy product of the local coefficient systems
attached to `ρ₁` and `ρ₂`.

This is purely algebraic: it is the statement that Euler factors multiply under direct sums.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators

namespace ArtinLSeries

namespace ArtinRep

variable {G : Type*} [Group G]

variable (ρ₁ ρ₂ : ArtinLSeries.ArtinRep G)
variable (c : Nat.Primes → ConjClasses G)

/--
Local coefficients for the direct sum representation are the product of local coefficients.
-/
theorem localCoeffsOfConj_sum :
    ArtinRep.localCoeffsOfConj (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
      =
    PrimeNumberTheoremAnd.ArtinLike.LocalCoeffs.mul
      (ArtinRep.localCoeffsOfConj (ρ := ρ₁) c)
      (ArtinRep.localCoeffsOfConj (ρ := ρ₂) c) := by
  classical
  -- Two `LocalCoeffs` are equal if their `a` agree (and `a_zero` is proof-irrelevant).
  ext p e
  -- Reduce to the coefficient identity for products of Euler factors.
  cases e with
  | zero =>
      simp [PrimeNumberTheoremAnd.ArtinLike.LocalCoeffs.mul, ArtinRep.localCoeffsOfConj]
  | succ e =>
      -- For `e > 0`, both sides are computed by the Cauchy product over `antidiagonal`.
      -- We use the `eulerCoeffClass` definition and the coefficient formula from `ArtinRep.sum`.
      refine Quotient.inductionOn (c p) (fun g => ?_) <;> clear g
      intro g
      -- Unfold both sides down to `eulerCoeffAt`, then apply `eulerCoeffAt_sum`.
      simp [PrimeNumberTheoremAnd.ArtinLike.LocalCoeffs.mul, ArtinRep.localCoeffsOfConj,
        ArtinRep.eulerCoeffClass, ArtinRep.eulerCoeffAt, ArtinRep.eulerFactorAt,
        ArtinRep.eulerCoeffAt_sum (ρ₁ := ρ₁) (ρ₂ := ρ₂) (g := g) (e := e.succ)]

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd
