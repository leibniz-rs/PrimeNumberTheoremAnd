import PrimeNumberTheoremAnd.ArtinLSeriesNatPrimePowSum

import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.NatAntidiagonal

/-!
## Artin L-series: direct sums and Dirichlet convolution (coefficients)

This file upgrades the prime-power coefficient identity for direct sums to an identity of the
global coefficient functions:

`coeffNat (ρ₁ ⊕ ρ₂) = coeffNat ρ₁ ⍟ coeffNat ρ₂`,

where `⍟` is the Dirichlet convolution defined in `Mathlib.NumberTheory.LSeries.Convolution`.

The proof is purely algebraic: it uses
- multiplicativity of `coeffNat` (as an arithmetic function), and
- the explicit description of the convolution on prime powers as a Cauchy sum over exponents.

No summability, analytic continuation, or rearrangement of infinite sums is used here.
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

private lemma isMultiplicative_toArithmeticFunction_coeffNat (ρ : ArtinLSeries.ArtinRep G) :
    (toArithmeticFunction (coeffNat (ρ := ρ) c)).IsMultiplicative := by
  classical
  -- `coeffNat` is `LocalCoeffs.coeff` for `localCoeffs ρ c`.
  let A : LocalCoeffs := ArtinLSeries.localCoeffs (ρ := ρ) c
  have hA : coeffNat (ρ := ρ) c = A.coeff := rfl
  -- Use the “nonzero” reformulation of multiplicativity.
  refine (ArithmeticFunction.IsMultiplicative.iff_ne_zero).2 ?_
  refine ⟨by simp [toArithmeticFunction, hA, A.coeff_one], ?_⟩
  intro m n hm hn hcop
  have : A.coeff (m * n) = A.coeff m * A.coeff n :=
    A.coeff_mul_of_coprime (m := m) (n := n) hm hn hcop
  simpa [toArithmeticFunction, hA, hm, hn, mul_ne_zero hm hn] using this

private lemma toArithmeticFunction_coe_of_map_zero (f : ℕ → ℂ) (hf : f 0 = 0) :
    (toArithmeticFunction f : ℕ → ℂ) = f := by
  funext n
  by_cases hn : n = 0
  · subst hn; simp [toArithmeticFunction, hf]
  · simp [toArithmeticFunction, hn]

private lemma divisorsAntidiagonal_prime_pow_eq_map_antidiagonal (p : ℕ) (k : ℕ) (hp : p.Prime) :
    (p ^ k).divisorsAntidiagonal =
      (Finset.antidiagonal k).map
        ⟨fun x : ℕ × ℕ => (p ^ x.1, p ^ x.2), by
          -- injective on exponent pairs since `p ≥ 2`
          have hp2 : 2 ≤ p := hp.two_le
          have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp2
          intro x y hxy
          have h1 : x.1 = y.1 := hinj (by simpa using congrArg Prod.fst hxy)
          have h2 : x.2 = y.2 := hinj (by simpa using congrArg Prod.snd hxy)
          exact Prod.ext h1 h2⟩ := by
  classical
  have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  ext y
  constructor
  · intro hy
    have hy' : y.1 * y.2 = p ^ k ∧ p ^ k ≠ 0 := (Nat.mem_divisorsAntidiagonal).1 hy
    have ha : y.1 ∣ p ^ k := ⟨y.2, by simp [hy'.1]⟩
    have hb : y.2 ∣ p ^ k := ⟨y.1, by simp [hy'.1, mul_comm]⟩
    rcases (Nat.dvd_prime_pow hp).1 ha with ⟨i, hi, hiEq⟩
    rcases (Nat.dvd_prime_pow hp).1 hb with ⟨j, hj, hjEq⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hinj : Function.Injective (fun n : ℕ => p ^ n) := Nat.pow_right_injective hp2
    have hij : i + j = k := by
      apply hinj
      -- turn the product equality into `p^(i+j)=p^k`
      -- using `hiEq`, `hjEq`, and `pow_add`.
      calc
        p ^ (i + j) = p ^ i * p ^ j := by simp [pow_add]
        _ = y.1 * y.2 := by simp [hiEq, hjEq]
        _ = p ^ k := hy'.1
    -- membership in the mapped antidiagonal
    refine (Finset.mem_map).2 ?_
    refine ⟨(i, j), ?_, ?_⟩
    · exact Finset.mem_antidiagonal.2 hij
    · -- map evaluates to `y`
      ext <;> simp [hiEq, hjEq]
  · intro hy
    rcases (Finset.mem_map).1 hy with ⟨x, hx, rfl⟩
    have hx' : x.1 + x.2 = k := by
      simpa using (Finset.mem_antidiagonal.mp hx)
    refine (Nat.mem_divisorsAntidiagonal).2 ?_
    refine ⟨?_, hpk0⟩
    calc
      p ^ x.1 * p ^ x.2 = p ^ (x.1 + x.2) := by
        simpa using (pow_add p x.1 x.2).symm
      _ = p ^ k := by simp [hx']

private lemma sum_divisorsAntidiagonal_prime_pow (p : ℕ) (k : ℕ) (hp : p.Prime)
    (f g : ℕ → ℂ) :
    (∑ x ∈ (p ^ k).divisorsAntidiagonal, f x.1 * g x.2)
      =
    ∑ x ∈ Finset.antidiagonal k, f (p ^ x.1) * g (p ^ x.2) := by
  classical
  -- rewrite the indexing finset
  rw [divisorsAntidiagonal_prime_pow_eq_map_antidiagonal (p := p) (k := k) hp]
  -- evaluate the sum over the `map`
  simp [Finset.sum_map, Function.Embedding.coeFn_mk]

/--
Coefficient function of the direct sum representation is the Dirichlet convolution of the
coefficient functions.
-/
theorem coeffNat_sum_eq_convolution :
    coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c
      =
    (coeffNat (ρ := ρ₁) c) ⍟ (coeffNat (ρ := ρ₂) c) := by
  classical
  -- Work in `ArithmeticFunction ℂ`.
  let f₁ : ArithmeticFunction ℂ := toArithmeticFunction (coeffNat (ρ := ρ₁) c)
  let f₂ : ArithmeticFunction ℂ := toArithmeticFunction (coeffNat (ρ := ρ₂) c)
  let fsum : ArithmeticFunction ℂ := toArithmeticFunction (coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c)
  have hf₁ : f₁.IsMultiplicative := isMultiplicative_toArithmeticFunction_coeffNat (ρ := ρ₁) (c := c)
  have hf₂ : f₂.IsMultiplicative := isMultiplicative_toArithmeticFunction_coeffNat (ρ := ρ₂) (c := c)
  have hfsum : fsum.IsMultiplicative :=
    isMultiplicative_toArithmeticFunction_coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) (c := c)
  have hmul : fsum = f₁ * f₂ := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hfsum _ ?_).2 ?_
    · exact ArithmeticFunction.IsMultiplicative.mul hf₁ hf₂
    intro p k hp
    have hp0 : (p ^ k) ≠ 0 := pow_ne_zero k hp.ne_zero
    -- Left side: prime-power coefficient identity for direct sums.
    have hL :
        fsum (p ^ k) =
          ∑ x ∈ Finset.antidiagonal k,
            coeffNat (ρ := ρ₁) c (p ^ x.1) * coeffNat (ρ := ρ₂) c (p ^ x.2) := by
      -- `toArithmeticFunction` is identity on nonzero inputs.
      -- `Nat.Primes` packaging for the prime-power lemma.
      let pp : Nat.Primes := ⟨p, hp⟩
      simpa [fsum, toArithmeticFunction, hp.ne_zero, pp] using
        (coeffNat_sum_prime_pow (ρ₁ := ρ₁) (ρ₂ := ρ₂) (c := c) pp k)
    -- Right side: expand Dirichlet convolution on the prime power, then reindex.
    have hR :
        (f₁ * f₂) (p ^ k) =
          ∑ x ∈ Finset.antidiagonal k,
            coeffNat (ρ := ρ₁) c (p ^ x.1) * coeffNat (ρ := ρ₂) c (p ^ x.2) := by
      -- Expand `mul_apply`, remove the `toArithmeticFunction` wrappers on nonzero divisor factors,
      -- then reindex `divisorsAntidiagonal(p^k)` to `antidiagonal k`.
      have hterm :
          ∀ x ∈ (p ^ k).divisorsAntidiagonal,
            (toArithmeticFunction (coeffNat (ρ := ρ₁) c)) x.1 *
                (toArithmeticFunction (coeffNat (ρ := ρ₂) c)) x.2
              =
            coeffNat (ρ := ρ₁) c x.1 * coeffNat (ρ := ρ₂) c x.2 := by
        intro x hx
        have hx0 : x.1 ≠ 0 ∧ x.2 ≠ 0 := Nat.ne_zero_of_mem_divisorsAntidiagonal (n := p ^ k) hx
        simp [toArithmeticFunction, hx0.1, hx0.2]
      calc
        (f₁ * f₂) (p ^ k)
            = ∑ x ∈ (p ^ k).divisorsAntidiagonal,
                (toArithmeticFunction (coeffNat (ρ := ρ₁) c)) x.1 *
                  (toArithmeticFunction (coeffNat (ρ := ρ₂) c)) x.2 := by
                  simp [f₁, f₂, ArithmeticFunction.mul_apply]
        _ = ∑ x ∈ (p ^ k).divisorsAntidiagonal,
                coeffNat (ρ := ρ₁) c x.1 * coeffNat (ρ := ρ₂) c x.2 := by
                  refine Finset.sum_congr rfl (fun x hx => ?_)
                  exact hterm x hx
        _ = ∑ x ∈ Finset.antidiagonal k,
                coeffNat (ρ := ρ₁) c (p ^ x.1) * coeffNat (ρ := ρ₂) c (p ^ x.2) := by
                  simp [sum_divisorsAntidiagonal_prime_pow (p := p) (k := k) (hp := hp)
                    (f := fun n => coeffNat (ρ := ρ₁) c n) (g := fun n => coeffNat (ρ := ρ₂) c n)]
    simp [hL, hR]
  -- Convert back to functions: `f ⍟ g` is definitionally the coercion of the product of the
  -- corresponding `toArithmeticFunction`s.
  have hcoeSum :
      (fsum : ℕ → ℂ) = coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c :=
    toArithmeticFunction_coe_of_map_zero (f := coeffNat (ρ := ArtinRep.sum (ρ₁ := ρ₁) (ρ₂ := ρ₂)) c) (by simp)
  have hcoeConv :
      ((f₁ * f₂ : ArithmeticFunction ℂ) : ℕ → ℂ) =
        (coeffNat (ρ := ρ₁) c) ⍟ (coeffNat (ρ := ρ₂) c) := by
    -- unfold `⍟` and the local abbreviations `f₁`, `f₂`
    rfl
  -- Take coercions of `hmul`, then rewrite with `hcoeSum`/`hcoeConv`.
  have hmul' := congrArg (fun F : ArithmeticFunction ℂ => (F : ℕ → ℂ)) hmul
  funext n
  -- LHS: `coeffNat` is `fsum` as a function; RHS: convolution is `(f₁*f₂)` as a function.
  simpa [hcoeSum, hcoeConv] using congrArg (fun h : ℕ → ℂ => h n) hmul'

end ArtinRep

end ArtinLSeries

end PrimeNumberTheoremAnd
