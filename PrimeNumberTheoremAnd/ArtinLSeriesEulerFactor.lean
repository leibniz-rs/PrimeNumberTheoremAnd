import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import PrimeNumberTheoremAnd.ArtinLikeLSeries

/-!
## Artin L-series (algebraic layer): Euler factors from matrices

This file begins a **fully principled** Artin L-series development by defining the *local Euler
factor* attached to a matrix \(A\) over `ℂ` as the formal power series
\[
  \frac{1}{\det(I - X A)} \in \mathbb{C}⟦X⟧,
\]
and extracting its coefficients.

No analytic statements are made here. In particular:
- no meromorphic continuation is assumed or postulated;
- no nonvanishing is assumed or postulated;
- no convergence of the resulting Dirichlet series is claimed without explicit hypotheses.

The goal is to connect, later, the Frobenius element (as an element of a finite Galois group) to a
matrix via a representation, and then use `ArtinLikeLSeries` to relate the global Dirichlet series
to the Euler product under explicit summability/convergence assumptions.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators

namespace ArtinLSeries

open Matrix PowerSeries

section EulerFactor

variable {n : Type*} [Fintype n]

/-- The polynomial (in the power-series variable `X`) whose inverse is the Euler factor. -/
noncomputable def eulerPoly (A : Matrix n n ℂ) : ℂ⟦X⟧ := by
  classical
  exact Matrix.det
    ((1 : Matrix n n ℂ⟦X⟧) -
      (PowerSeries.X : ℂ⟦X⟧) • (PowerSeries.C : ℂ →+* ℂ⟦X⟧).mapMatrix A)

/--
The Euler factor as a power series:
\[
  ( \det(I - X A) )^{-1}.
\]

We implement the inverse via `PowerSeries.invOfUnit` with unit `1`, using the lemma
`eulerPoly_constantCoeff` below.
-/
noncomputable def eulerFactor (A : Matrix n n ℂ) : ℂ⟦X⟧ :=
  PowerSeries.invOfUnit (eulerPoly (n := n) A) (1 : ℂˣ)

/-- The `e`-th coefficient of the Euler factor power series. -/
noncomputable def eulerCoeff (A : Matrix n n ℂ) (e : ℕ) : ℂ :=
  PowerSeries.coeff e (eulerFactor (n := n) A)

lemma eulerPoly_constantCoeff (A : Matrix n n ℂ) :
    PowerSeries.constantCoeff (eulerPoly (n := n) A) = (1 : ℂ) := by
  classical
  -- Use `RingHom.map_det` for `constantCoeff : ℂ⟦X⟧ →+* ℂ`.
  let M : Matrix n n ℂ⟦X⟧ :=
    (1 : Matrix n n ℂ⟦X⟧) -
      (PowerSeries.X : ℂ⟦X⟧) • (PowerSeries.C : ℂ →+* ℂ⟦X⟧).mapMatrix A
  have :
      PowerSeries.constantCoeff (Matrix.det
          M) =
        Matrix.det
          (PowerSeries.constantCoeff.mapMatrix
            M) := by
    simpa using (PowerSeries.constantCoeff.map_det (M := M))
  have hmap : PowerSeries.constantCoeff.mapMatrix M = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [M]
    · simp [M, hij]
  -- Now simplify the mapped matrix: `constantCoeff X = 0`, `constantCoeff (C a) = a`.
  -- This gives `det(1) = 1`.
  simpa [eulerPoly, M, hmap] using this.trans (by simp [hmap])

@[simp] lemma eulerCoeff_zero (A : Matrix n n ℂ) : eulerCoeff (n := n) A 0 = 1 := by
  classical
  -- `coeff 0` is `constantCoeff`, and `constantCoeff (invOfUnit _ 1) = 1`.
  simp [eulerCoeff, eulerFactor, eulerPoly_constantCoeff (n := n) A]

end EulerFactor

section Assemble

variable {n : Type*} [Fintype n]

/--
Build `ArtinLike.LocalCoeffs` from a family of matrices indexed by primes,
using coefficients of the Euler factor power series.
-/
noncomputable def localCoeffsOfMatrix (A : Nat.Primes → Matrix n n ℂ) :
    ArtinLike.LocalCoeffs where
  a p e := eulerCoeff (n := n) (A p) e
  a_zero p := by
    classical
    simp [eulerCoeff_zero (n := n) (A p)]

end Assemble

end ArtinLSeries

end PrimeNumberTheoremAnd
