import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import PrimeNumberTheoremAnd.ArtinLSeriesEulerFactor

/-!
## Artin L-series (algebraic layer): conjugation invariance

To make Artin Euler factors depend only on conjugacy classes, we need the basic fact that
`det (1 - X • A)` (and hence its inverse power series) is invariant under conjugation.

This file provides the minimal matrix-ring lemmas needed for that, in a way suitable for later
use with representations `ρ : G →* GL n ℂ`.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ArtinLSeries

open Matrix PowerSeries

section MapInv

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n : Type*} [Fintype n] [DecidableEq n]

namespace RingHom

/--
For a ring hom `f`, `f.mapMatrix` sends the (nonsingular) inverse of a *unit* matrix to the inverse
of the image matrix.

This is a small but crucial bridge between unit inverses and the `Matrix` `Inv` instance.
-/
lemma mapMatrix_inv_of_isUnit (f : R →+* S) (M : Matrix n n R) (hM : IsUnit M) :
    (f.mapMatrix : Matrix n n R →+* Matrix n n S) (M⁻¹) =
      ((f.mapMatrix : Matrix n n R →+* Matrix n n S) M)⁻¹ := by
  classical
  rcases hM with ⟨u, rfl⟩
  -- Convert the matrix inverse to the unit inverse (`Matrix.coe_units_inv`),
  -- then use functoriality of `Units.map`.
  let F : Matrix n n R →+* Matrix n n S := (f.mapMatrix : Matrix n n R →+* Matrix n n S)
  let Fu : (Matrix n n S)ˣ := Units.map (RingHom.toMonoidHom F) u
  have hinvR : ((↑u : Matrix n n R)⁻¹) = (↑(u⁻¹) : Matrix n n R) := by
    -- `Matrix.coe_units_inv` is `↑u⁻¹ = (↑u)⁻¹`.
    simpa using (Matrix.coe_units_inv u).symm
  have hinvS : ((↑Fu : Matrix n n S)⁻¹) = (↑(Fu⁻¹) : Matrix n n S) := by
    simpa using (Matrix.coe_units_inv Fu).symm
  -- Now both sides reduce to `↑(Fu⁻¹)`.
  calc
    F ((↑u : Matrix n n R)⁻¹)
        = F (↑(u⁻¹) : Matrix n n R) := by simp_rw [hinvR]
    _ = (↑(Units.map (RingHom.toMonoidHom F) (u⁻¹)) : Matrix n n S) := rfl
    _ = (↑(Fu⁻¹) : Matrix n n S) := by
          -- `Units.map` preserves inverses.
          simpa [Fu] using congrArg (fun x => (↑x : Matrix n n S)) (Units.map_inv (RingHom.toMonoidHom F) u)
    _ = (↑Fu : Matrix n n S)⁻¹ := by simp_rw [hinvS]
    _ = (F (↑u : Matrix n n R))⁻¹ := by rfl


end RingHom

end MapInv

section ConjInvariance

variable {n : Type*} [Fintype n] [DecidableEq n]

open PrimeNumberTheoremAnd.ArtinLSeries

lemma eulerPoly_conj (M A : Matrix n n ℂ) (hM : IsUnit M) :
    eulerPoly (n := n) (M * A * M⁻¹) = eulerPoly (n := n) A := by
  classical
  -- Work in `ℂ⟦X⟧` and use `Matrix.det_conj` there.
  let f : ℂ →+* ℂ⟦X⟧ := PowerSeries.C
  let F : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧ := (f.mapMatrix : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧)
  let Mc : Matrix n n ℂ⟦X⟧ := F M
  have hMc : IsUnit Mc := hM.map F
  let Ac : Matrix n n ℂ⟦X⟧ := F A
  have hFinv : F (M⁻¹) = (F M)⁻¹ :=
    PrimeNumberTheoremAnd.ArtinLSeries.RingHom.mapMatrix_inv_of_isUnit (f := f) (M := M) hM
  have hFinv' : (M⁻¹).map f = (M.map f)⁻¹ := by
    simpa [F] using hFinv
  have hconj :
      F (M * A * M⁻¹) = Mc * Ac * Mc⁻¹ := by
    -- unfold `Mc`/`Ac` only at the end
    calc
      F (M * A * M⁻¹) = F M * F A * F (M⁻¹) := by simp [mul_assoc]
      _ = F M * F A * (F M)⁻¹ := by simp [hFinv]
      _ = Mc * Ac * Mc⁻¹ := by rfl
  have hx :
      (1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (Mc * Ac * Mc⁻¹) =
        Mc * ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) * Mc⁻¹ := by
    -- Expand and simplify using `Mc * Mc⁻¹ = 1`.
    have hdet : IsUnit (Matrix.det Mc) := (Matrix.isUnit_iff_isUnit_det (A := Mc)).1 hMc
    have hmul : Mc * Mc⁻¹ = (1 : Matrix n n ℂ⟦X⟧) := Matrix.mul_nonsing_inv (A := Mc) hdet
    ext i j
    simp [hmul, Mc, Ac, mul_assoc, mul_add, add_mul, sub_eq_add_neg]
  have hdet :
      Matrix.det ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (Mc * Ac * Mc⁻¹)) =
        Matrix.det ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) := by
    simpa [hx] using (Matrix.det_conj (M := Mc) hMc
      ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac))
  -- The extra `hFinv` rewrite is essential: it replaces `(M⁻¹).map f` by `(M.map f)⁻¹`,
  -- avoiding a spurious mismatch between “map then invert” vs “invert then map”.
  simpa [ArtinLSeries.eulerPoly, f, F, Mc, Ac, hconj, hFinv'] using hdet

end ConjInvariance

end ArtinLSeries

end PrimeNumberTheoremAnd
