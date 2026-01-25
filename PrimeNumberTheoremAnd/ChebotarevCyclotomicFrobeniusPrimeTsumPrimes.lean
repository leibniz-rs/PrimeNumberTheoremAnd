import PrimeNumberTheoremAnd.ChebotarevDirichletDensityTsumPrimes
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusPrimeSet

/-!
## Cyclotomic case: Frobenius prime series as a `tsum` over `Nat.Primes`

This file specializes the general `series_eq_tsum_primes` lemma to the cyclotomic Frobenius prime
set, and rewrites the term at a prime using the character-sum coefficient identity.

This is the prime-indexed form that the analytic `log L` machinery naturally consumes.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n : ℕ} [NeZero n]
variable [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod n)ˣ)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

open Nat.Primes in
theorem series_frobPrimeSet_eq_tsum_primes_character {s : ℝ} (σ : Gal(L/ℚ)) (hs : 1 < s) :
    series (frobPrimeSet (n := n) (L := L) σ) s =
      ∑' p : Nat.Primes,
        (((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n,
              χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n)) /
          ((p : ℂ) ^ (s : ℂ)) := by
  classical
  -- Start from the general prime-indexed expansion.
  have h := (PrimeNumberTheoremAnd.DirichletDensity.series_eq_tsum_primes
    (S := frobPrimeSet (n := n) (L := L) σ) hs)
  -- Rewrite each term at a prime using `coeff_frobPrimeSet_eq_prime`.
  refine h.trans ?_
  refine tsum_congr (fun p ↦ ?_)
  have hp : (p.1).Prime := p.2
  -- Expand `term` at a prime and substitute the coefficient formula.
  have hn0 : (p.1 : ℕ) ≠ 0 := p.2.ne_zero
  simp [LSeries.term, hn0, coeff_frobPrimeSet_eq_prime (n := n) (L := L) (σ := σ) hp, div_eq_mul_inv,
    mul_comm]

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd

