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
  -- Rewrite everything in terms of units and use that `Units.map` preserves inverses.
  -- `Matrix.coe_units_inv` connects unit inverse with matrix inverse.
  simp [Matrix.coe_units_inv]

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
  let Mc : Matrix n n ℂ⟦X⟧ := (f.mapMatrix : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧) M
  have hMc : IsUnit Mc := hM.map (f.mapMatrix : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧)
  let Ac : Matrix n n ℂ⟦X⟧ := (f.mapMatrix : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧) A
  -- First, rewrite the `mapMatrix` of `M * A * M⁻¹` as a conjugate.
  have hconj :
      (f.mapMatrix : Matrix n n ℂ →+* Matrix n n ℂ⟦X⟧) (M * A * M⁻¹) = Mc * Ac * Mc⁻¹ := by
    -- Multiplicativity plus the inverse-compatibility lemma for unit matrices.
    simp [Mc, Ac, mul_assoc, RingHom.mapMatrix_inv_of_isUnit (f := f) (M := M) hM]
  -- Now compute the determinant polynomial and apply conjugation invariance of `det`.
  -- The scalar `X` commutes with matrices since the coefficient ring is commutative.
  have hmain :
      ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (f.mapMatrix A)) =
        Mc⁻¹ * ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) * Mc := by
    -- This is just reassociation/commutativity; we keep it explicit to avoid `simp` loops.
    -- (We don't actually need this direction; it's here as a “normal form” helper.)
    simp [Ac, Mc, mul_assoc]
  -- Use `Matrix.det_conj` with the unit `Mc` on the matrix `1 - X•Ac`.
  have : Matrix.det ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (Mc * Ac * Mc⁻¹)) =
      Matrix.det ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) := by
    -- Rewrite the left-hand matrix as a conjugate and apply `det_conj`.
    -- `Matrix.det_conj` is in `Matrix.NonsingularInverse`.
    -- We use `hMc` to justify the conjugation.
    -- The key algebraic identity:
    --   1 - X•(Mc*Ac*Mc⁻¹) = Mc * (1 - X•Ac) * Mc⁻¹
    -- since scalars commute in the commutative coefficient ring.
    have hx :
        (1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • (Mc * Ac * Mc⁻¹) =
          Mc * ((1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • Ac) * Mc⁻¹ := by
      ext i j
      -- entrywise expansion; `simp` is safe here (no recursion) thanks to commutativity.
      simp [Mc, Ac, mul_assoc, mul_add, add_mul, sub_eq_add_neg, smul_mul_assoc, mul_smul_comm,
        mul_comm, mul_left_comm, mul_assoc]
    -- Now apply determinant conjugation.
    simpa [hx] using (Matrix.det_conj (M := Mc) hMc ((1 : Matrix n n ℂ⟦X⟧) -
      (PowerSeries.X : ℂ⟦X⟧) • Ac)).symm
  -- Finally, unwrap `eulerPoly`.
  -- `eulerPoly` is defined as `det (1 - X•C.mapMatrix _)`.
  -- Use `hconj` and `this`.
  simpa [ArtinLSeries.eulerPoly, f, Mc, Ac, hconj] using this

end ConjInvariance

end ArtinLSeries

end PrimeNumberTheoremAnd

