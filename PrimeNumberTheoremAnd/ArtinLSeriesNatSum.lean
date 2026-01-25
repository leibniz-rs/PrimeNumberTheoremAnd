import PrimeNumberTheoremAnd.ArtinLSeriesNat
import PrimeNumberTheoremAnd.ArtinLSeriesLocalCoeffsSum

import Mathlib.NumberTheory.LSeries.Convolution

/-!
## Artin L-series: direct sums and Dirichlet convolution

This file upgrades the purely local “Euler factors multiply under direct sums” statement to the
global Dirichlet series level:

- the coefficient function of the naive Artin L-series attached to `ρ₁ ⊕ ρ₂` is the Dirichlet
  convolution (in the sense of `Mathlib.NumberTheory.LSeries.Convolution`) of the coefficient
  functions for `ρ₁` and `ρ₂`;
- consequently, under explicit `LSeriesSummable` hypotheses, the corresponding L-series multiply.

No analytic continuation is asserted.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical BigOperators
open scoped LSeries.notation

namespace ArtinLSeries

namespace ArtinRep

open PrimeNumberTheoremAnd.ArtinLike

variable {G : Type*} [Group G]

variable (ρ₁ ρ₂ : ArtinLSeries.ArtinRep G)
variable (c : Nat.Primes → ConjClasses G)

private lemma toArithmeticFunction_coeffNat_eq (ρ : ArtinLSeries.ArtinRep G) :
    LSeries.toArithmeticFunction (coeffNat (ρ := ρ) c) =
      ⟨coeffNat (ρ := ρ) c, by simp [ArtinLSeries.coeffNat_zero]⟩ := by
  ext n
  by_cases hn : n = 0
  · subst hn; simp [LSeries.toArithmeticFunction, ArtinLSeries.coeffNat_zero]
  · simp [LSeries.toArithmeticFunction, hn]

private lemma isMultiplicative_toArithmeticFunction_coeffNat (ρ : ArtinLSeries.ArtinRep G) :
    (LSeries.toArithmeticFunction (coeffNat (ρ := ρ) c)).IsMultiplicative := by
  -- Use the `LocalCoeffs` multiplicativity lemma.
  classical
  let A : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ρ) c
  -- `coeffNat` is `A.coeff`.
  have hA : coeffNat (ρ := ρ) c = A.coeff := rfl
  -- Now show multiplicativity of the arithmetic function derived from `A.coeff`.
  refine (ArithmeticFunction.IsMultiplicative.iff_ne_zero).2 ?_
  refine ⟨by simpa [LSeries.toArithmeticFunction, hA] using (A.coeff_one), ?_⟩
  intro m n hm hn hcop
  have : A.coeff (m * n) = A.coeff m * A.coeff n :=
    A.coeff_mul_of_coprime (m := m) (n := n) hm hn hcop
  simpa [LSeries.toArithmeticFunction, hA, hm, hn, mul_ne_zero hm hn] using this

/-!
### Coefficients: `ρ₁ ⊕ ρ₂` corresponds to Dirichlet convolution
-/

theorem coeffNat_sum_eq_convolution :
    coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
      =
    (coeffNat (ρ := ρ₁) c) ⍟ (coeffNat (ρ := ρ₂) c) := by
  classical
  -- Work in `ArithmeticFunction ℂ` and use the “agree on prime powers” criterion.
  let f₁ : ArithmeticFunction ℂ := LSeries.toArithmeticFunction (coeffNat (ρ := ρ₁) c)
  let f₂ : ArithmeticFunction ℂ := LSeries.toArithmeticFunction (coeffNat (ρ := ρ₂) c)
  let fsum : ArithmeticFunction ℂ :=
    LSeries.toArithmeticFunction (coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c)
  have hf₁ : f₁.IsMultiplicative := isMultiplicative_toArithmeticFunction_coeffNat (ρ := ρ₁) (c := c)
  have hf₂ : f₂.IsMultiplicative := isMultiplicative_toArithmeticFunction_coeffNat (ρ := ρ₂) (c := c)
  have hfsum : fsum.IsMultiplicative :=
    isMultiplicative_toArithmeticFunction_coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) (c := c)
  have hmul : fsum = f₁ * f₂ := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hfsum _ ?_).2 ?_
    · exact ArithmeticFunction.IsMultiplicative.mul hf₁ hf₂
    intro p k hp
    have hp' : Nat.Prime p := hp
    have hp0 : p ^ k ≠ 0 := pow_ne_zero k hp'.ne_zero
    -- Rewrite all coefficient functions via `LocalCoeffs`.
    let A₁ : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ρ₁) c
    let A₂ : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ρ₂) c
    let As : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
    have hAs : As = LocalCoeffs.mul A₁ A₂ := by
      -- This is exactly `localCoeffsOfConj_sum`, rewritten into the `localCoeffs` abbreviation.
      simpa [ArtinLSeries.localCoeffs] using
        (localCoeffsOfConj_sum (ρ₁ := ρ₁) (ρ₂ := ρ₂) (c := c))
    -- LHS: `fsum (p^k)` is `As.coeff (p^k)`, and we use `coeff_prime_pow`.
    have hL :
        fsum (p ^ k) =
          ∑ x ∈ Finset.antidiagonal k, A₁.a ⟨p, hp'⟩ x.1 * A₂.a ⟨p, hp'⟩ x.2 := by
      -- unfold `fsum` and reduce to `As.coeff (p^k)`, then rewrite `As` as `A₁.mul A₂`.
      simp [fsum, LSeries.toArithmeticFunction, hp0, ArtinLSeries.coeffNat, ArtinLSeries.localCoeffs,
        hAs, LocalCoeffs.mul, LocalCoeffs.coeff_prime_pow (A := LocalCoeffs.mul A₁ A₂) hp']
    -- RHS: compute `(f₁ * f₂) (p^k)` via divisors of a prime power.
    have hR :
        (f₁ * f₂) (p ^ k) =
          ∑ x ∈ Finset.antidiagonal k, A₁.a ⟨p, hp'⟩ x.1 * A₂.a ⟨p, hp'⟩ x.2 := by
      -- Rewrite the convolution sum over `divisorsAntidiagonal` as a sum over divisors.
      have :
          (f₁ * f₂) (p ^ k) =
            ∑ d ∈ (p ^ k).divisors, f₁ d * f₂ ((p ^ k) / d) := by
        simpa [ArithmeticFunction.mul_apply, Nat.map_div_right_divisors, Finset.sum_map,
          Function.Embedding.coeFn_mk, Prod.fst, Prod.snd]
      -- Enumerate divisors as `p^i`.
      rw [this, Nat.divisors_prime_pow hp' k, Finset.sum_map]
      -- Now it is a range sum; translate to `antidiagonal k`.
      -- Each term is `A₁.a p i * A₂.a p (k-i)` by `coeff_prime_pow`.
      simp only [Finset.sum_range, Finset.sum_map, Function.Embedding.coeFn_mk]
      -- use the definitional parametrization of `antidiagonal`.
      simpa [Finset.antidiagonal_eq_map, f₁, f₂, LSeries.toArithmeticFunction,
        ArtinLSeries.coeffNat, ArtinLSeries.localCoeffs,
        LocalCoeffs.coeff_prime_pow (A := A₁) hp', LocalCoeffs.coeff_prime_pow (A := A₂) hp',
        Nat.pow_div (le_of_lt_succ (Nat.lt_succ_self _)) hp'.pos] using rfl
    simpa [hL, hR]
  -- Convert the arithmetic-function identity back to an identity of functions, i.e. coefficients.
  -- `f ⍟ g` is defined as `⇑(toArithmeticFunction f * toArithmeticFunction g)`.
  funext n
  simpa [LSeries.convolution, f₁, f₂, fsum, hmul]

/-!
### L-series: `L(ρ₁ ⊕ ρ₂) = L(ρ₁) * L(ρ₂)` under summability
-/

theorem LSeries_coeffNat_sum_eq_mul {s : ℂ}
    (h₁ : LSeriesSummable (coeffNat (ρ := ρ₁) c) s)
    (h₂ : LSeriesSummable (coeffNat (ρ := ρ₂) c) s) :
    LSeries (coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c) s
      =
    LSeries (coeffNat (ρ := ρ₁) c) s * LSeries (coeffNat (ρ := ρ₂) c) s := by
  -- Rewrite the LHS as the L-series of a convolution, then apply the general multiplication lemma.
  have hcoeff :
      coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
        =
      (coeffNat (ρ := ρ₁) c) ⍟ (coeffNat (ρ := ρ₂) c) :=
    coeffNat_sum_eq_convolution (ρ₁ := ρ₁) (ρ₂ := ρ₂) (c := c)
  -- Now use `LSeries_convolution'`.
  simpa [hcoeff] using (LSeries_convolution' (f := coeffNat (ρ := ρ₁) c) (g := coeffNat (ρ := ρ₂) c)
    (s := s) h₁ h₂)

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd
