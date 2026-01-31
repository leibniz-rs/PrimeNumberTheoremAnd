import PrimeNumberTheoremAnd.ChebotarevUnramifiedNat
import PrimeNumberTheoremAnd.ChebotarevCyclotomicOverPrime
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.SetTheory.Cardinal.Finite
import PrimeNumberTheoremAnd.ChebotarevCyclotomicOrthogonality
import PrimeNumberTheoremAnd.ChebotarevEnoughRootsOfUnityComplex

/-!
## Cyclotomic step: Frobenius sends `ζₙ ↦ ζₙ^p` (algebraic core)

Sharifi’s Step 1 (cyclotomic base case) uses that for `p ∤ n`, the arithmetic Frobenius at a
prime above `(p)` acts on `ζₙ` by `ζₙ ↦ ζₙ^p`.

This file proves that statement in a **mathlib-native** way, using:

- `arithFrobAt` / `IsArithFrobAt` from `Mathlib/RingTheory/Frobenius.lean`,
- the “unramified-at-`n`” lemma `ChebotarevUnramifiedNat.natCast_not_mem_of_liesOver_span_prime`,
- the computation `Nat.card (ℤ/(p)) = p`.

We state it for a general cyclotomic extension `L/ℚ` (as a number field), and for its ring of
integers `𝓞 L`.
-/

namespace PrimeNumberTheoremAnd

namespace Chebotarev

open scoped Classical Cyclotomic

open IsCyclotomicExtension NumberField

section

variable {n p : ℕ} [NeZero n] [Fact (Nat.Prime p)]

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {n} ℚ L]

local notation "𝓞L" => (𝓞 L)

-- We use the canonical Galois action of `Gal(L/ℚ)` on `𝓞L` coming from `galRestrict`.
attribute [local instance] FractionRing.liftAlgebra

noncomputable
local instance instMulSemiringAction : MulSemiringAction Gal(L/ℚ) 𝓞L :=
  IsIntegralClosure.MulSemiringAction ℤ ℚ L 𝓞L

-- This `SMulCommClass` is available in the AKLB setup; we keep it local.
local instance instSMulCommClass : SMulCommClass Gal(L/ℚ) ℤ 𝓞L := by
  infer_instance

-- For Frobenius existence, we also need invariance; in the cyclotomic case `L/ℚ` is Galois.
local instance instIsInvariant [IsGalois ℚ L] :
    Algebra.IsInvariant ℤ 𝓞L Gal(L/ℚ) := by
  simpa using (Algebra.isInvariant_of_isGalois (A := ℤ) (K := ℚ) (L := L) (B := 𝓞L))

/--
Let `Q` be a prime ideal of `𝓞L` lying over `(p)` with finite residue field.
If `p ∤ n`, then the arithmetic Frobenius at `Q` sends the integral cyclotomic generator `ζₙ`
to `ζₙ^p`.
-/
theorem arithFrobAt_zeta_toInteger_eq_pow (Q : Ideal 𝓞L)
    [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (hn : ¬ p ∣ n) :
    let ζ₀ : 𝓞L := (zeta_spec n ℚ L).toInteger
    (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) • (ζ₀ : 𝓞L) = (ζ₀ : 𝓞L) ^ p := by
  classical
  intro ζ₀
  -- First: `n ∉ Q` since `Q` lies over `(p)` and `p ∤ n`.
  have hnQ : (n : 𝓞L) ∉ Q :=
    natCast_not_mem_of_liesOver_span_prime (S := 𝓞L) (p := p) (n := n) Q hn
  -- Apply `IsArithFrobAt.smul_of_pow_eq_one` to the Frobenius at `Q`.
  have hF : IsArithFrobAt (R := ℤ) (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) Q :=
    IsArithFrobAt.arithFrobAt (R := ℤ) (S := 𝓞L) (G := Gal(L/ℚ)) (Q := Q)
  have hz_pow : (ζ₀ : 𝓞L) ^ n = 1 := by
    -- `ζ₀` is a primitive `n`-th root of unity in `𝓞L`.
    simpa using (zeta_spec n ℚ L).toInteger_isPrimitiveRoot.pow_eq_one
  have hpow :=
    IsArithFrobAt.smul_of_pow_eq_one (R := ℤ) (S := 𝓞L) (σ := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q)
      (Q := Q) hF hz_pow (by simpa using hnQ)
  -- Rewrite the residue field size `Nat.card (ℤ ⧸ Q.under ℤ)` as `p` using `LiesOver`.
  have hunder : Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) := by
    simpa [Ideal.under_def] using (Q.over_def (Ideal.span ({(p : ℤ)} : Set ℤ))).symm
  -- Now finish by rewriting the exponent.
  simpa [hunder, nat_card_int_quot_span_prime (p := p)] using hpow

/-!
### Transport to the field: `σ(ζₙ) = ζₙ^p`
-/

/--
The previous lemma transported to the field `L`: the arithmetic Frobenius at `Q` sends
`zeta n ℚ L` to its `p`-th power (for `p ∤ n`).
-/
theorem arithFrobAt_zeta_eq_pow (Q : Ideal 𝓞L)
    [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (hn : ¬ p ∣ n) :
    (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) (zeta n ℚ L) = (zeta n ℚ L) ^ p := by
  classical
  -- Work with the integral version `ζ₀ : 𝓞L` and map to `L`.
  let ζ₀ : 𝓞L := (zeta_spec n ℚ L).toInteger
  have hζ₀ : (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) • (ζ₀ : 𝓞L) = (ζ₀ : 𝓞L) ^ p :=
    arithFrobAt_zeta_toInteger_eq_pow (L := L) (n := n) (p := p) (Q := Q) hn
  -- Apply `algebraMap 𝓞L L`.
  have hmap := congrArg (algebraMap 𝓞L L) hζ₀
  -- Rewrite the action on `𝓞L` as `galRestrict`, then use compatibility with `algebraMap`.
  -- (`σ • x` is definitional for our `instMulSemiringAction`.)
  have hleft :
      algebraMap 𝓞L L ((arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) • ζ₀) =
        (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) (algebraMap 𝓞L L ζ₀) := by
    -- `algebraMap_galRestrict_apply` is the compatibility lemma.
    simpa [instMulSemiringAction, IsIntegralClosure.MulSemiringAction, MulSemiringAction.compHom] using
      (algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := L) (B := 𝓞L)
        (σ := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) (x := ζ₀))
  have hzeta : algebraMap 𝓞L L ζ₀ = zeta n ℚ L := by
    simp [ζ₀]
  have := hmap
  simpa [hleft, hzeta, map_pow] using this

/-!
### `autToPow` identifies Frobenius with `p (mod n)`
-/

/--
In the cyclotomic setup above, the powering exponent of the Frobenius at `Q` (as an element of
`ZMod n`) is `p`.

This is the algebraic content behind the statement “Frobenius corresponds to `p mod n`”.
-/
theorem arithFrobAt_autToPow_eq_natCast (Q : Ideal 𝓞L)
    [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (hn : ¬ p ∣ n) :
    ((zeta_spec n ℚ L).autToPow ℚ (arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q) : ZMod n) = p := by
  classical
  let σ : Gal(L/ℚ) := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q
  -- `autToPow_spec` gives the characterizing powering formula on `ζₙ`.
  have hspec :
      (zeta n ℚ L) ^ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val = σ (zeta n ℚ L) := by
    simp [σ]
  -- Substitute the Frobenius action `σ(ζₙ) = ζₙ^p`.
  have hfrob : σ (zeta n ℚ L) = (zeta n ℚ L) ^ p := by
    simpa [σ] using (arithFrobAt_zeta_eq_pow (L := L) (n := n) (p := p) (Q := Q) hn)
  have hpows :
      (zeta n ℚ L) ^ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val = (zeta n ℚ L) ^ p := by
    simp [hfrob]
  -- Work in the unit group to use cancellation (`pow_eq_pow_iff_modEq`).
  have hn0 : n ≠ 0 := NeZero.ne n
  let ζu : Lˣ := (zeta_spec n ℚ L).isUnit hn0 |>.unit
  have hζu : IsPrimitiveRoot ζu n :=
    (zeta_spec n ℚ L).isUnit_unit hn0
  have hpowsU :
      ζu ^ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val = ζu ^ p := by
    ext
    -- reduce to the previously proved equality in `L`
    -- and use that `ζu` coerces to `zeta`.
    simpa [ζu, Units.val_pow_eq_pow_val] using hpows
  have hnord : orderOf ζu = n := by
    simpa using hζu.eq_orderOf.symm
  have hmod :
      (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val ≡ p [MOD n] := by
    simpa [hnord] using (pow_eq_pow_iff_modEq.mp hpowsU)
  -- Turn the congruence into equality in `ZMod n`.
  have : (((((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)).val : ℕ) : ZMod n) = (p : ZMod n) :=
    (ZMod.natCast_eq_natCast_iff ..).2 hmod
  -- Replace `natCast` of `.val` by the element itself.
  simpa [σ] using (by
    -- `ZMod.natCast_zmod_val` says `((a.val : ZMod n)) = a`.
    simpa using (ZMod.natCast_zmod_val (n := n) ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n)) ▸ this)

/-!
### Cyclotomic indicator as a character sum (orthogonality bridge)
-/

/--
In the cyclotomic case, the indicator function of the event `arithFrobAt(Q) = σ` is a normalized
Dirichlet-character sum detecting the congruence class `p` in `ZMod n`.

This is the algebraic bridge in Sharifi’s Step 1, prior to taking analytic limits.
-/
theorem frob_indicator_eq_character_sum
    (Q : Ideal 𝓞L) [Q.IsPrime] [Finite (𝓞L ⧸ Q)] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    [IsGalois ℚ L] (σ : Gal(L/ℚ)) (hn : ¬ p ∣ n) :
    (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
      =
    (∑ χ : DirichletCharacter ℂ n,
        χ (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹ *
          χ (p : ZMod n)) / (n.totient : ℂ) := by
  classical
  -- Let `σF` be the (chosen) Frobenius element at `Q`.
  let σF : Gal(L/ℚ) := arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q
  -- `σF` corresponds to `p (mod n)` via `autToPow`.
  have hFrobZMod :
      ((zeta_spec n ℚ L).autToPow ℚ σF : ZMod n) = p := by
    simpa [σF] using (arithFrobAt_autToPow_eq_natCast (L := L) (n := n) (p := p) (Q := Q) hn)
  -- Convert `arithFrobAt(Q)=σ` to an equality in `ZMod n` using injectivity of `autToPow`.
  have hinj : Function.Injective ((zeta_spec n ℚ L).autToPow ℚ) :=
    (zeta_spec n ℚ L).autToPow_injective (K := ℚ)
  have hiff :
      (σF = σ) ↔ (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n)) := by
    constructor
    · intro h
      subst h
      simpa using hFrobZMod
    · intro hZ
      -- Upgrade equality in `ZMod n` to equality in units, then use injectivity.
      have hU :
          (zeta_spec n ℚ L).autToPow ℚ σF = (zeta_spec n ℚ L).autToPow ℚ σ := by
        apply Units.ext
        -- Both sides are units, so equality in `ZMod n` suffices.
        simpa [hFrobZMod] using hZ.symm
      exact hinj hU
  -- Reduce to the orthogonality indicator form.
  have ha : IsUnit (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n) := by
    exact ((zeta_spec n ℚ L).autToPow ℚ σ).isUnit
  -- Now compute the indicator via orthogonality.
  have hind :
      (if σF = σ then (1 : ℂ) else 0) =
        (if (((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n)) then (1 : ℂ) else 0) := by
    by_cases hσ : σF = σ
    · have : ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n) := (hiff.1 hσ)
      simp [hσ, this]
    · have : ¬ ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n) := by
        intro hZ
        exact hσ (hiff.2 hZ)
      simp [hσ, this]
  -- Finish with the orthogonality lemma (indicator form).
  have horth :=
    (Dirichlet.sum_char_inv_mul_char_eq_indicator (n := n)
      (a := (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)) ha (p : ZMod n))
  -- Put it together, rewriting `σF` back to `arithFrobAt`.
  have hLHS : (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
      = (if σF = σ then (1 : ℂ) else 0) := by
    simp [σF]
  calc
    (if arithFrobAt (R := ℤ) (G := Gal(L/ℚ)) Q = σ then (1 : ℂ) else 0)
        = (if σF = σ then (1 : ℂ) else 0) := hLHS
    _ = if ((zeta_spec n ℚ L).autToPow ℚ σ : ZMod n) = (p : ZMod n) then (1 : ℂ) else 0 := hind
    _ = (∑ χ : DirichletCharacter ℂ n,
            χ (((zeta_spec n ℚ L).autToPow ℚ σ : (ZMod n)ˣ) : ZMod n)⁻¹ *
              χ (p : ZMod n)) / (n.totient : ℂ) := by
          -- Rearrange `horth`.
          simpa using horth.symm

end

end Chebotarev

end PrimeNumberTheoremAnd
