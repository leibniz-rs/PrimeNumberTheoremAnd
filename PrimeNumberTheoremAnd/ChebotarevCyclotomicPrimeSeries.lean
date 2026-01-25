import PrimeNumberTheoremAnd.ChebotarevDirichletDensity
import PrimeNumberTheoremAnd.ChebotarevCyclotomicOrthogonality
import PrimeNumberTheoremAnd.ChebotarevEnoughRootsOfUnityComplex
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Complex.Basic

/-!
## Cyclotomic case: prime Dirichlet series decomposition via orthogonality

This file packages the purely algebraic decomposition of the prime Dirichlet series for a
congruence class modulo `n` into a normalized finite sum over Dirichlet characters.

This is the step in Sharifi’s cyclotomic argument **before** introducing analytic limits:
we rewrite the indicator of a congruence class as a normalized character sum, then sum over primes.

Analytic input (e.g. limits of `log L(s,χ)` as `s → 1⁺`) is not used here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical
open scoped LSeries.notation

namespace Chebotarev

namespace Cyclotomic

section

variable {n : ℕ} [NeZero n]

open PrimeNumberTheoremAnd.DirichletDensity

/-- The set of natural primes congruent to a given unit `a` modulo `n`. -/
def congrPrimeSet (a : (ZMod n)ˣ) : Set ℕ :=
  {m | m.Prime ∧ (m : ZMod n) = (a : ZMod n)}

/-- Prime-filtered coefficient attached to a Dirichlet character. -/
noncomputable def primeCoeff (χ : DirichletCharacter ℂ n) : ℕ → ℂ :=
  fun m => if m.Prime then χ m else 0

lemma coeff_congrPrimeSet_eq (a : (ZMod n)ˣ) (m : ℕ) :
    coeff (congrPrimeSet (n := n) a) m =
      ((1 : ℂ) / (n.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ n,
          χ ((a : ZMod n)⁻¹) * primeCoeff (n := n) χ m := by
  classical
  by_cases hm : m.Prime
  · -- reduce to the indicator relation in `ZMod n`
    have ha : IsUnit (a : ZMod n) := (a : (ZMod n)ˣ).isUnit
    -- `coeff` is the prime indicator of membership in the congruence set.
    have hcoeff :
        coeff (congrPrimeSet (n := n) a) m =
          (if (m : ZMod n) = (a : ZMod n) then (1 : ℂ) else 0) := by
      simp [coeff, congrPrimeSet, hm]
    -- use orthogonality for `a` (a unit) and `b := (m : ZMod n)`
    have hind :
        (if (m : ZMod n) = (a : ZMod n) then (1 : ℂ) else 0) =
          ((1 : ℂ) / (n.totient : ℂ)) *
            ∑ χ : DirichletCharacter ℂ n, χ ((a : ZMod n)⁻¹) * χ (m : ZMod n) := by
      -- `sum_char_inv_mul_char_eq_indicator` is normalized as `(...)/φ = if a=b then 1 else 0`.
      -- We rewrite it to match our `if` and our preferred `((1:ℂ)/φ) * ...` normalization.
      have := Dirichlet.sum_char_inv_mul_char_eq_indicator (n := n) (a := (a : ZMod n)) ha (m : ZMod n)
      -- swap the `if`-condition and move `φ(n)` to a multiplicative inverse.
      simpa [div_eq_mul_inv, eq_comm, one_div, mul_assoc, mul_left_comm, mul_comm] using this.symm
    -- finalize: primeCoeff is χ(m) for prime m
    simp [hcoeff, hind, primeCoeff, hm, mul_comm]
  · -- non-prime: both sides are zero
    simp [coeff, congrPrimeSet, primeCoeff, hm]

end

end Cyclotomic

end Chebotarev

end PrimeNumberTheoremAnd

