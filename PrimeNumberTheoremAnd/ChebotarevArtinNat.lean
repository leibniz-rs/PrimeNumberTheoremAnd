import PrimeNumberTheoremAnd.ChebotarevNatConjAssignment
import PrimeNumberTheoremAnd.ArtinLSeriesNat

/-!
## Chebotarev × Artin (algebraic glue): ℕ-Dirichlet series from Frobenius classes

This file composes two *choice-free* constructions:

- `Chebotarev.frobClassOverNat`: a `Nat.Primes → ConjClasses G` assignment produced from any
  `Nat.Primes → Ideal R` together with finiteness witnesses needed to define Frobenius, and
- `ArtinLSeries.coeffNat`: the induced coefficient function `ℕ → ℂ` attached to an Artin
  representation and a `Nat.Primes → ConjClasses G`.

It then restates the Euler-product theorem for the resulting `ℕ`-Dirichlet series, under the
explicit summability hypothesis `LSeriesSummable`.

No arithmetic identification of `Nat.Primes` with prime ideals is made here; that is a separate,
deeper step.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (ρ : PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep G)

/-- The `Nat.Primes → ConjClasses G` assignment coming from Frobenius data. -/
noncomputable def conjAssignment (P : Nat.Primes → Ideal R)
    (hP : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) :
    Nat.Primes → ConjClasses G :=
  Chebotarev.frobClassOverNat (R := R) (S := S) (G := G) P hP

theorem conjAssignment_congr (P : Nat.Primes → Ideal R)
    (hP hP' : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) :
    conjAssignment (R := R) (S := S) (G := G) P hP =
      conjAssignment (R := R) (S := S) (G := G) P hP' := by
  classical
  simpa [conjAssignment] using
    (Chebotarev.frobClassOverNat_congr (R := R) (S := S) (P := P) hP hP')

/-- The induced global coefficient function on `ℕ` for Chebotarev–Artin data. -/
noncomputable def artinCoeffNat (P : Nat.Primes → Ideal R)
    (hP : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) : ℕ → ℂ :=
  PrimeNumberTheoremAnd.ArtinLSeries.coeffNat (ρ := ρ) (conjAssignment (R := R) (S := S) (G := G) P hP)

theorem artinCoeffNat_congr (P : Nat.Primes → Ideal R)
    (hP hP' : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) :
    artinCoeffNat (R := R) (S := S) (G := G) ρ P hP =
      artinCoeffNat (R := R) (S := S) (G := G) ρ P hP' := by
  classical
  -- Reduce to `coeffNat` congruence under pointwise equality of the `c : Nat.Primes → ConjClasses G`.
  simpa [artinCoeffNat] using
    congrArg (PrimeNumberTheoremAnd.ArtinLSeries.coeffNat (ρ := ρ))
      (conjAssignment_congr (R := R) (S := S) (G := G) (ρ := ρ) P hP hP')

/--
Euler product for the naive ℕ-Dirichlet series attached to `ρ` and a Frobenius-produced
conjugacy-class assignment, under an explicit `LSeriesSummable` hypothesis.
-/
theorem LSeries_eulerProduct_hasProd {P : Nat.Primes → Ideal R}
    {hP : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)}
    {s : ℂ} (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s (p.1 ^ e))
      (LSeries (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) := by
  -- This is just `ArtinLSeries.LSeries_eulerProduct_hasProd` for the composed coefficient function.
  simpa [artinCoeffNat, conjAssignment] using
    (PrimeNumberTheoremAnd.ArtinLSeries.LSeries_eulerProduct_hasProd
      (ρ := ρ) (c := conjAssignment (R := R) (S := S) (G := G) P hP) hsum)

theorem LSeries_eulerProduct_hasProd_congr (P : Nat.Primes → Ideal R)
    (hP hP' : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1))
    {s : ℂ}
    (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP') s (p.1 ^ e))
      (LSeries (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP') s) := by
  classical
  -- Rewrite summability along `artinCoeffNat_congr`, then apply the Euler-product theorem.
  have hsum' :
      LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP') s := by
    simpa [artinCoeffNat_congr (R := R) (S := S) (G := G) (ρ := ρ) (P := P) hP hP'] using hsum
  simpa using (LSeries_eulerProduct_hasProd (R := R) (S := S) (G := G) (ρ := ρ) (P := P)
    (hP := hP') (s := s) hsum')

end

end Chebotarev

end PrimeNumberTheoremAnd
