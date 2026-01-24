import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import PrimeNumberTheoremAnd.ArtinLSeriesConjugation

/-!
## Artin L-series (algebraic layer): from representations to class functions

This file packages the fundamental fact that the Euler factor
\[
  \det(I - X ρ(g))^{-1}
\]
depends only on the conjugacy class of `g`, for a representation `ρ : G → GL(n, ℂ)`.

This is a prerequisite for connecting Artin Euler factors to the Frobenius *conjugacy class*
appearing in Chebotarev.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ArtinLSeries

open Matrix

section

variable (G : Type*) [Group G]

/-- An (algebraic) Artin representation into `GL(n, ℂ)`. -/
structure ArtinRep where
  n : Type*
  instFintype : Fintype n
  instDecEq : DecidableEq n
  ρ : G →* Matrix.GL n ℂ

attribute [instance] ArtinRep.instFintype ArtinRep.instDecEq

namespace ArtinRep

variable {G} (ρ : ArtinRep G)

/-- The underlying matrix of `ρ g`. -/
noncomputable def mat (g : G) : Matrix ρ.n ρ.n ℂ :=
  (ρ.ρ g : Matrix ρ.n ρ.n ℂ)

/-- The Euler polynomial at `g`: `det(I - X ρ(g))`. -/
noncomputable def eulerPolyAt (g : G) : ℂ⟦X⟧ :=
  ArtinLSeries.eulerPoly (n := ρ.n) (ρ.mat g)

/-- The Euler factor at `g`: `(det(I - X ρ(g)))⁻¹` as a power series. -/
noncomputable def eulerFactorAt (g : G) : ℂ⟦X⟧ :=
  ArtinLSeries.eulerFactor (n := ρ.n) (ρ.mat g)

/-- The `e`-th coefficient of the Euler factor at `g`. -/
noncomputable def eulerCoeffAt (g : G) (e : ℕ) : ℂ :=
  ArtinLSeries.eulerCoeff (n := ρ.n) (ρ.mat g) e

lemma eulerPolyAt_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.eulerPolyAt g = ρ.eulerPolyAt h := by
  classical
  rcases hg with ⟨x, rfl⟩
  -- Reduce to conjugation invariance at the matrix level.
  have hunit : IsUnit (ρ.mat x) := by
    -- `ρ.ρ x` is a unit in the matrix ring, hence its value is a unit.
    simpa [ArtinRep.mat] using (ρ.ρ x).isUnit
  -- `ρ.mat (x * g * x⁻¹)` is conjugate to `ρ.mat g` by `ρ.mat x`.
  -- Use `eulerPoly_conj`.
  simpa [ArtinRep.eulerPolyAt, ArtinRep.mat, map_mul, mul_assoc] using
    (ArtinLSeries.eulerPoly_conj (n := ρ.n) (M := ρ.mat x) (A := ρ.mat g) hunit)

lemma eulerFactorAt_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.eulerFactorAt g = ρ.eulerFactorAt h := by
  -- `eulerFactor` is definitional from `eulerPoly`, so this follows by rewriting.
  classical
  rcases hg with ⟨x, rfl⟩
  have hunit : IsUnit (ρ.mat x) := by
    simpa [ArtinRep.mat] using (ρ.ρ x).isUnit
  -- unfold and reduce to `eulerPoly_conj`
  simp [ArtinRep.eulerFactorAt, ArtinRep.mat, ArtinLSeries.eulerFactor,
    ArtinLSeries.eulerPoly_conj (n := ρ.n) (M := ρ.mat x) (A := ρ.mat g) hunit]

lemma eulerCoeffAt_eq_of_isConj {g h : G} (hg : IsConj g h) (e : ℕ) :
    ρ.eulerCoeffAt g e = ρ.eulerCoeffAt h e := by
  simp [ArtinRep.eulerCoeffAt, ρ.eulerFactorAt_eq_of_isConj hg]

/-- The Euler polynomial as a class function `ConjClasses G → ℂ⟦X⟧`. -/
noncomputable def eulerPolyClass : ConjClasses G → ℂ⟦X⟧ :=
  Quotient.lift (fun g => ρ.eulerPolyAt g) (by
    intro g h hgh
    exact ρ.eulerPolyAt_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hgh))

/-- The Euler factor as a class function `ConjClasses G → ℂ⟦X⟧`. -/
noncomputable def eulerFactorClass : ConjClasses G → ℂ⟦X⟧ :=
  Quotient.lift (fun g => ρ.eulerFactorAt g) (by
    intro g h hgh
    exact ρ.eulerFactorAt_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hgh))

/-- The `e`-th Euler-factor coefficient as a class function `ConjClasses G → ℂ`. -/
noncomputable def eulerCoeffClass (e : ℕ) : ConjClasses G → ℂ :=
  Quotient.lift (fun g => ρ.eulerCoeffAt g e) (by
    intro g h hgh
    exact ρ.eulerCoeffAt_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp hgh) e)

end ArtinRep

end

end ArtinLSeries

end PrimeNumberTheoremAnd

