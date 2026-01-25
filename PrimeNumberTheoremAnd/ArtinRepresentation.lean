import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.PowerSeries.Inverse
import PrimeNumberTheoremAnd.ArtinLSeriesConjugation

/-!
## Artin L-series (algebraic layer): representations and class functions

We define, for a representation `ρ : G → Matrix.GeneralLinearGroup n ℂ`, the Euler polynomial
`det(I - X ρ(g))` and Euler factor `(det(I - X ρ(g)))⁻¹` as formal power series, and prove they
depend only on the conjugacy class of `g`.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ArtinLSeries

open Matrix

section

variable (G : Type*) [Group G]

/-- An (algebraic) Artin representation into invertible matrices over `ℂ`. -/
structure ArtinRep where
  n : Type*
  instFintype : Fintype n
  instDecEq : DecidableEq n
  ρ : G →* Matrix.GeneralLinearGroup n ℂ

attribute [instance] ArtinRep.instFintype ArtinRep.instDecEq

namespace ArtinRep

variable {G} (ρ : ArtinRep G)

/-- The underlying matrix of `ρ g`. -/
noncomputable def mat (g : G) : Matrix ρ.n ρ.n ℂ :=
  (ρ.ρ g : Matrix ρ.n ρ.n ℂ)

/-- The Euler polynomial at `g`: `det(I - X ρ(g))`. -/
noncomputable def eulerPolyAt (g : G) : PowerSeries ℂ :=
  ArtinLSeries.eulerPoly (n := ρ.n) (ρ.mat g)

/-- The Euler factor at `g`: `(det(I - X ρ(g)))⁻¹`. -/
noncomputable def eulerFactorAt (g : G) : PowerSeries ℂ :=
  ArtinLSeries.eulerFactor (n := ρ.n) (ρ.mat g)

/-- The `e`-th coefficient of the Euler factor at `g`. -/
noncomputable def eulerCoeffAt (g : G) (e : ℕ) : ℂ :=
  PowerSeries.coeff e (ρ.eulerFactorAt g)

lemma eulerPolyAt_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.eulerPolyAt g = ρ.eulerPolyAt h := by
  classical
  rcases hg with ⟨c, hc⟩
  -- Turn semiconjugation into the usual conjugation formula.
  have hconj : (↑c : G) * g * (↑c : G)⁻¹ = h := by
    have := congrArg (fun t : G => t * (↑(c⁻¹) : G)) hc
    simp [mul_assoc] at this
    simpa [mul_assoc] using this
  have hunit : IsUnit (ρ.mat (↑c : G)) := by
    simpa [ArtinRep.mat] using (ρ.ρ (↑c : G)).isUnit
  -- Rewrite `h` as a conjugate and use the matrix-level lemma `eulerPoly_conj`.
  -- The homomorphism property gives `ρ(h) = ρ(c) ρ(g) ρ(c)⁻¹` inside the matrix ring.
  have hmat :
      ρ.mat h = ρ.mat (↑c : G) * ρ.mat g * (ρ.mat (↑c : G))⁻¹ := by
    calc
      ρ.mat h = ρ.mat ((↑c : G) * g * (↑c : G)⁻¹) := by simpa [hconj]
      _ = ρ.mat (↑c : G) * ρ.mat g * (ρ.mat (↑c : G))⁻¹ := by
            simp [ArtinRep.mat, map_mul, mul_assoc]
  -- `eulerPoly` only depends on the matrix up to conjugation.
  simpa [ArtinRep.eulerPolyAt, hmat, mul_assoc] using
    (ArtinLSeries.eulerPoly_conj (n := ρ.n) (M := ρ.mat (↑c : G)) (A := ρ.mat g) hunit).symm

lemma eulerFactorAt_eq_of_isConj {g h : G} (hg : IsConj g h) :
    ρ.eulerFactorAt g = ρ.eulerFactorAt h := by
  classical
  -- `eulerFactor` is definitional from `eulerPoly`.
  -- So this is just `congrArg` along the proven `eulerPolyAt` equality.
  have hpoly : ρ.eulerPolyAt g = ρ.eulerPolyAt h :=
    ρ.eulerPolyAt_eq_of_isConj (g := g) (h := h) hg
  -- Unfold both sides to the same `invOfUnit` expression.
  simpa [ArtinRep.eulerFactorAt, ArtinRep.eulerPolyAt, ArtinLSeries.eulerFactor] using
    congrArg (fun p : PowerSeries ℂ => PowerSeries.invOfUnit p (1 : ℂˣ)) hpoly

lemma eulerCoeffAt_eq_of_isConj {g h : G} (hg : IsConj g h) (e : ℕ) :
    ρ.eulerCoeffAt g e = ρ.eulerCoeffAt h e := by
  simp [ArtinRep.eulerCoeffAt, ρ.eulerFactorAt_eq_of_isConj hg]

/-- The Euler polynomial as a class function `ConjClasses G → PowerSeries ℂ`. -/
noncomputable def eulerPolyClass : ConjClasses G → PowerSeries ℂ :=
  Quotient.lift (fun g => ρ.eulerPolyAt g) (by
    intro g h hgh
    exact ρ.eulerPolyAt_eq_of_isConj hgh)

/-- The Euler factor as a class function `ConjClasses G → PowerSeries ℂ`. -/
noncomputable def eulerFactorClass : ConjClasses G → PowerSeries ℂ :=
  Quotient.lift (fun g => ρ.eulerFactorAt g) (by
    intro g h hgh
    exact ρ.eulerFactorAt_eq_of_isConj hgh)

/-- The `e`-th Euler-factor coefficient as a class function `ConjClasses G → ℂ`. -/
noncomputable def eulerCoeffClass (e : ℕ) : ConjClasses G → ℂ :=
  Quotient.lift (fun g => ρ.eulerCoeffAt g e) (by
    intro g h hgh
    exact ρ.eulerCoeffAt_eq_of_isConj hgh e)

end ArtinRep

end

end ArtinLSeries

end PrimeNumberTheoremAnd
