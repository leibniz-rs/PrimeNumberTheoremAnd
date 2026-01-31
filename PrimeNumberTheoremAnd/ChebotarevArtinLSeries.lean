import PrimeNumberTheoremAnd.ChebotarevArtinNat

/-!
## Chebotarev × Artin: the naive Artin L-series (algebraic package)

This file defines the **naive Artin L-series** attached to:

- a group `G`,
- an Artin representation `ρ : G → GL(n, ℂ)`,
- a `Nat.Primes`-indexed family of base ideals `P p : Ideal R`,
- finiteness witnesses `hP` enabling Frobenius at each `P p`,

as the Dirichlet series `LSeries (artinCoeffNat ρ P hP) s`.

It also records the Euler-product theorem (under the explicit summability hypothesis
`LSeriesSummable`), and the fact that the resulting series is independent of the witness `hP`
(thanks to earlier `*_congr` lemmas).

No analytic continuation or nonvanishing input appears here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open scoped LSeries.notation

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (ρ : PrimeNumberTheoremAnd.ArtinLSeries.ArtinRep G)

/-- The naive Artin L-series (Dirichlet series) attached to `ρ`, `P`, and `hP`. -/
noncomputable def artinLSeries (P : Nat.Primes → Ideal R)
    (hP : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1))
    (s : ℂ) : ℂ :=
  LSeries (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s

theorem artinLSeries_congr (P : Nat.Primes → Ideal R)
    (hP hP' : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) (s : ℂ) :
    artinLSeries (R := R) (S := S) (G := G) ρ P hP s =
      artinLSeries (R := R) (S := S) (G := G) ρ P hP' s := by
  classical
  simp [artinLSeries, artinCoeffNat_congr (R := R) (S := S) (G := G) (ρ := ρ) (P := P) hP hP']

/--
Euler product for the naive Artin L-series, under an explicit summability hypothesis.
-/
theorem artinLSeries_eulerProduct_hasProd {P : Nat.Primes → Ideal R}
    {hP : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)}
    {s : ℂ} (hsum : LSeriesSummable (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s) :
    HasProd (fun p : Nat.Primes =>
      ∑' e : ℕ, LSeries.term (artinCoeffNat (R := R) (S := S) (G := G) ρ P hP) s (p.1 ^ e))
      (artinLSeries (R := R) (S := S) (G := G) ρ P hP s) := by
  simpa [artinLSeries] using
    (LSeries_eulerProduct_hasProd (R := R) (S := S) (G := G) (ρ := ρ) (P := P) (hP := hP)
      (s := s) hsum)

end

end Chebotarev

end PrimeNumberTheoremAnd

