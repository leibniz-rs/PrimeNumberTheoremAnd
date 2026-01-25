import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
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

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The polynomial (in the power-series variable `X`) whose inverse is the Euler factor. -/
noncomputable def eulerPoly (A : Matrix n n ℂ) : ℂ⟦X⟧ :=
  Matrix.det
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

section Block

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped BigOperators

/-!
### Block-diagonal multiplicativity

These are the core algebraic lemmas needed later to relate Artin Euler factors to direct sums of
representations (block diagonal matrices).
-/

lemma eulerPoly_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    eulerPoly (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
      =
    eulerPoly (n := m) A * eulerPoly (n := n) D := by
  classical
  -- Work with the coefficient embedding `ℂ →+* ℂ⟦X⟧`.
  let c : ℂ →+* ℂ⟦X⟧ := (PowerSeries.C : ℂ →+* ℂ⟦X⟧)
  -- Abbreviate the block matrices appearing inside the determinant.
  let MA : Matrix m m ℂ⟦X⟧ :=
    (1 : Matrix m m ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • A.map (⇑c)
  let MD : Matrix n n ℂ⟦X⟧ :=
    (1 : Matrix n n ℂ⟦X⟧) - (PowerSeries.X : ℂ⟦X⟧) • D.map (⇑c)
  have hblock :
      ((1 : Matrix (m ⊕ n) (m ⊕ n) ℂ⟦X⟧) -
            (PowerSeries.X : ℂ⟦X⟧) •
              (Matrix.fromBlocks A 0 0 D).map (⇑c))
        =
      Matrix.fromBlocks MA 0 0 MD := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            by_cases h : i = j <;>
              simp [MA, MD, h, Matrix.fromBlocks_apply₁₁, Matrix.map_apply]
        | inr j =>
            simp [MA, MD, Matrix.fromBlocks_apply₁₂, Matrix.map_apply]
    | inr i =>
        cases j with
        | inl j =>
            simp [MA, MD, Matrix.fromBlocks_apply₂₁, Matrix.map_apply]
        | inr j =>
            by_cases h : i = j <;>
              simp [MA, MD, h, Matrix.fromBlocks_apply₂₂, Matrix.map_apply]
  -- Now compute the determinant using the block-triangular determinant lemma.
  -- The only subtlety is that `eulerPoly` uses `RingHom.mapMatrix`; we rewrite it to `Matrix.map`.
  simp [eulerPoly, hblock, MA, MD, c, RingHom.mapMatrix_apply]

lemma eulerFactor_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    eulerFactor (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
      =
    eulerFactor (n := m) A * eulerFactor (n := n) D := by
  classical
  set φ : ℂ⟦X⟧ := eulerPoly (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
  set b : ℂ⟦X⟧ := eulerFactor (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D)
  set c : ℂ⟦X⟧ := eulerFactor (n := m) A * eulerFactor (n := n) D
  have hb : φ * b = 1 := by
    -- `eulerFactor` is defined as `invOfUnit`, and `eulerPoly` has unit constant coefficient.
    simp [φ, b, eulerFactor, eulerPoly_constantCoeff]
  have hb' : b * φ = 1 := by
    simpa [mul_comm, φ, b] using hb
  have hc : φ * c = 1 := by
    -- Use multiplicativity of `eulerPoly` on block diagonals, then the defining inverse identities.
    simp [φ, c, eulerPoly_fromBlocks (A := A) (D := D), eulerFactor, eulerPoly_constantCoeff,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    b = b * 1 := by simp
    _ = b * (φ * c) := by simp [hc]
    _ = (b * φ) * c := by simp [mul_assoc]
    _ = 1 * c := by simp [hb']
    _ = c := by simp

lemma eulerCoeff_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) (e : ℕ) :
    eulerCoeff (n := (m ⊕ n)) (Matrix.fromBlocks A 0 0 D) e
      =
    ∑ p ∈ Finset.antidiagonal e,
      eulerCoeff (n := m) A p.1 * eulerCoeff (n := n) D p.2 := by
  classical
  simp [eulerCoeff, eulerFactor_fromBlocks (A := A) (D := D), PowerSeries.coeff_mul]

end Block

section Assemble

variable {n : Type*} [Fintype n] [DecidableEq n]

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
