import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusPrimeSet
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusCongruence
import PrimeNumberTheoremAnd.ChebotarevEnoughRootsOfUnityComplex

/-!
## Cyclotomic case: Frobenius indicator equals the prime-set coefficient

This is the precise bridge between:

- the **ideal-theoretic** Frobenius event `arithFrobAt(Q) = σ`, and
- the **prime-set** formulation (a congruence class modulo `n`) used to form prime Dirichlet series.

It is purely algebraic (no analytic limits).
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension NumberField
open PrimeNumberTheoremAnd.DirichletDensity

section

variable {n p : ℕ} [NeZero n] [Fact (Nat.Prime p)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

-- Ensure `arithFrobAt` is elaborated with the same instance choices as in
-- `ChebotarevCyclotomicFrobeniusCongruence`.
attribute [local instance] FractionRing.liftAlgebra

noncomputable
local instance instMulSemiringAction' : MulSemiringAction Gal(L/ℚ) (𝓞 L) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ L (𝓞 L)

local instance instSMulCommClass' : SMulCommClass Gal(L/ℚ) ℤ (𝓞 L) := by
  infer_instance

local instance instIsInvariant' [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) Gal(L/ℚ) := by
  simpa using (Algebra.isInvariant_of_isGalois (A := ℤ) (K := ℚ) (L := L) (B := (𝓞 L)))

variable (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite ((𝓞 L) ⧸ Q)]
variable [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] [IsGalois ℚ L]
variable (σ : Gal(L/ℚ))

/--
For `p ∤ n`, the indicator of `arithFrobAt(Q) = σ` agrees with the Dirichlet-density coefficient
of the congruence-class prime set `frobPrimeSet σ` evaluated at `p`.
-/
theorem frob_indicator_eq_coeff_frobPrimeSet (hn : ¬ p ∣ n) :
    (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
      =
    coeff (frobPrimeSet (n := n) (L := L) σ) p := by
  classical
  have hp : p.Prime := Fact.out
  -- Rewrite the LHS condition using the `autToPow` characterization.
  have hiff :=
    (arithFrobAt_eq_iff_autToPow_eq_natCast (n := n) (p := p) (L := L) (Q := Q) (σ := σ) hn)
  have hcond :
      (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ) =
        (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n)) :=
    propext hiff
  -- Expand the coefficient of the congruence-class set.
  simp [coeff, frobPrimeSet, congrPrimeSet, hp, hcond, eq_comm]

/-!
### Character-sum form (prime specialization)
-/

theorem frob_indicator_eq_character_sum (hn : ¬ p ∣ n) :
    (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
      =
    ((1 : ℂ) / (n.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ n,
        χ ((((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹) * χ (p : ZMod n) := by
  classical
  have hp : p.Prime := Fact.out
  -- Use the prime-set bridge, then rewrite the coefficient at a prime via orthogonality.
  simpa [coeff_frobPrimeSet_eq_prime (n := n) (L := L) (σ := σ) hp] using
    (frob_indicator_eq_coeff_frobPrimeSet (n := n) (p := p) (L := L) (Q := Q) (σ := σ) hn)

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd
