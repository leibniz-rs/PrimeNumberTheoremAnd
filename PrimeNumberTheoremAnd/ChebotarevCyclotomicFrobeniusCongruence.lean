import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusZeta

/-!
## Cyclotomic case: identifying Frobenius via `autToPow`

In a cyclotomic extension, an automorphism is determined by the exponent by which it sends
`ζₙ`.  In particular, for an (arithmetic) Frobenius element at a prime ideal `Q` lying over `p`,
we can characterize the equality `arithFrobAt Q = σ` in terms of the congruence class
`((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = p`.

This is the “set-theoretic” form of the bridge used in Sharifi’s Step 1.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev
namespace Cyclotomic

open scoped Classical Cyclotomic NumberField

open IsCyclotomicExtension NumberField

section

variable {n p : ℕ} [NeZero n] [Fact (Nat.Prime p)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

-- We use the canonical Galois action on `𝓞 L` coming from `galRestrict`.
attribute [local instance] FractionRing.liftAlgebra

-- Match the `MulSemiringAction` instance used in `ChebotarevCyclotomicFrobeniusZeta`.
noncomputable
local instance instMulSemiringAction : MulSemiringAction Gal(L/ℚ) (𝓞 L) :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ L (𝓞 L)

-- This `SMulCommClass` is available in the AKLB setup; keep it local.
local instance instSMulCommClass : SMulCommClass Gal(L/ℚ) ℤ (𝓞 L) := by
  infer_instance

-- For Frobenius existence, we also need invariance; in the cyclotomic case `L/ℚ` is Galois.
local instance instIsInvariant [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ (𝓞 L) Gal(L/ℚ) := by
  simpa using (Algebra.isInvariant_of_isGalois (A := ℤ) (K := ℚ) (L := L) (B := (𝓞 L)))

variable (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite ((𝓞 L) ⧸ Q)]
variable [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] [IsGalois ℚ L]

variable (σ : Gal(L/ℚ))

/--
For primes `p ∤ n`, equality with the Frobenius element at `Q` is equivalent to equality of the
associated exponents in `ZMod n`.
-/
theorem arithFrobAt_eq_iff_autToPow_eq_natCast :
    (hn : ¬ p ∣ n) →
    arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ ↔
      ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n) := by
  classical
  intro hn
  -- Let `σF` be the (chosen) Frobenius element at `Q`.
  let σF : Gal(L/ℚ) := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q
  have hFrobZMod :
      ((zeta_spec n ℚ L).autToPow ℚ σF : ZMod n) = p := by
    simpa [σF] using
      (arithFrobAt_autToPow_eq_natCast (L := L) (n := n) (p := p) (Q := Q) hn)
  -- Use injectivity of `autToPow` to characterize equality in the Galois group.
  have hinj : Function.Injective ((zeta_spec n ℚ L).autToPow ℚ) :=
    (zeta_spec n ℚ L).autToPow_injective (K := ℚ)
  constructor
  · intro h
    subst h
    simpa [σF] using hFrobZMod
  · intro hZ
    -- Upgrade equality in `ZMod n` to equality in units, then use injectivity.
    have hU :
        (zeta_spec n ℚ L).autToPow ℚ σF = (zeta_spec n ℚ L).autToPow ℚ σ := by
      apply Units.ext
      simpa [hFrobZMod] using hZ.symm
    have : σF = σ := hinj hU
    simpa [σF] using this

end

end Cyclotomic
end Chebotarev

end PrimeNumberTheoremAnd

