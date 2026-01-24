import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffs
import PrimeNumberTheoremAnd.ArtinLikeLSeries

/-!
## Artin L-series (algebraic layer): a naive ℕ-Dirichlet series package

This file is **pure glue**: it turns

- an Artin representation `ρ : G → Matrix.GeneralLinearGroup n ℂ`, and
- an assignment of conjugacy classes to rational primes `c : Nat.Primes → ConjClasses G`,

into a coefficient function `ℕ → ℂ` via `ArtinLike.LocalCoeffs.coeff`.

It then restates the Euler-product theorem (`ArtinLike.LSeries_eulerProduct_hasProd`) for this
specialized coefficient function, under the explicit summability hypothesis
`LSeriesSummable`.

No analytic continuation, no nonvanishing, and **no hidden summability assumptions** appear here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators
open scoped LSeries.notation

namespace ArtinLSeries

section

variable {G : Type*} [Group G]
variable (ρ : ArtinLSeries.ArtinRep G)
variable (c : Nat.Primes → ConjClasses G)

/-- The local prime-power coefficients coming from `ρ` and `c`. -/
noncomputable def localCoeffs : ArtinLike.LocalCoeffs :=
  ArtinRep.localCoeffsOfConj (ρ := ρ) c

/-- The induced global coefficient function on `ℕ`. -/
noncomputable def coeffNat : ℕ → ℂ :=
  (localCoeffs (ρ := ρ) c).coeff

@[simp] lemma coeffNat_zero : coeffNat (ρ := ρ) c 0 = 0 := by
  simp [coeffNat, localCoeffs, ArtinLike.LocalCoeffs.coeff_zero]

@[simp] lemma coeffNat_one : coeffNat (ρ := ρ) c 1 = 1 := by
  simp [coeffNat, localCoeffs, ArtinLike.LocalCoeffs.coeff_one]

open ArtinLike

/--
Euler product for the naive ℕ-Dirichlet series attached to `ρ` and `c`,
under an explicit `LSeriesSummable` hypothesis.
-/
theorem LSeries_eulerProduct_hasProd {s : ℂ} (hsum : LSeriesSummable (coeffNat (ρ := ρ) c) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (coeffNat (ρ := ρ) c) s (p.1 ^ e))
      (LSeries (coeffNat (ρ := ρ) c) s) := by
  -- This is exactly `ArtinLike.LSeries_eulerProduct_hasProd` for `A := localCoeffs ρ c`.
  simpa [coeffNat, localCoeffs, ArtinLike.term] using
    (ArtinLike.LSeries_eulerProduct_hasProd (A := localCoeffs (ρ := ρ) c) (s := s) hsum)

end

end ArtinLSeries

end PrimeNumberTheoremAnd

