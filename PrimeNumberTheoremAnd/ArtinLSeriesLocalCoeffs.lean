import PrimeNumberTheoremAnd.ArtinRepresentation
import PrimeNumberTheoremAnd.ArtinLikeLSeries

/-!
## Artin L-series (algebraic layer): local coefficients from conjugacy-class data

Given:
- a group `G`,
- an Artin representation `ρ : G → GL(n, ℂ)`,
- an assignment of conjugacy classes `c(p) : ConjClasses G` to primes `p`,

we define the resulting local prime-power coefficients
\[
  a_p(e) := [X^e] \det(I - X ρ(c(p)))^{-1},
\]
as an `ArtinLike.LocalCoeffs`.

This is purely algebraic: no convergence is asserted here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ArtinLSeries

open Matrix

section

variable {G : Type*} [Group G]
variable (ρ : ArtinLSeries.ArtinRep G)

namespace ArtinRep

lemma eulerCoeffAt_zero (g : G) : ρ.eulerCoeffAt g 0 = 1 := by
  -- Unfold to the matrix-level lemma `ArtinLSeries.eulerCoeff_zero`.
  simp [ArtinRep.eulerCoeffAt, ArtinRep.eulerFactorAt, ArtinLSeries.eulerFactor, ArtinRep.mat]

lemma eulerCoeffClass_zero (C : ConjClasses G) : ρ.eulerCoeffClass 0 C = 1 := by
  refine Quotient.inductionOn C (fun g => ?_)
  -- `eulerCoeffClass` is defined by quotient-lift, so this reduces to `eulerCoeffAt_zero`.
  simpa [ArtinRep.eulerCoeffClass] using (ρ.eulerCoeffAt_zero (g := g))

/--
Build `ArtinLike.LocalCoeffs` from an Artin representation and a prime-indexed conjugacy-class
assignment.
-/
noncomputable def localCoeffsOfConj (c : Nat.Primes → ConjClasses G) : ArtinLike.LocalCoeffs where
  a p e := ρ.eulerCoeffClass e (c p)
  a_zero p := by
    simpa using (ρ.eulerCoeffClass_zero (C := c p))

end ArtinRep

end

end ArtinLSeries

end PrimeNumberTheoremAnd

