import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Ideal.Pointwise

/-!
## Decomposition and inertia; Frobenius in the quotient `D(Q)/I(Q)`

This file develops a **purely algebraic** prerequisite for Chebotarev arguments:

* the decomposition subgroup `D(Q)` of a prime ideal `Q` as the stabilizer under the pointwise
  action on ideals;
* the inertia subgroup `I(Q)` (already in mathlib as `Q.toAddSubgroup.inertia G`);
* the canonical Frobenius element as an element of the quotient `D(Q) ⧸ I(Q)`.

Crucially, we prove that **any two** arithmetic Frobenius elements at `Q` define the same element
of `D(Q) ⧸ I(Q)` (using `IsArithFrobAt.mul_inv_mem_inertia`), so the construction is canonical.

No analytic input is used.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical Pointwise

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

open MulAction

/-- The decomposition subgroup at an ideal `Q` is the stabilizer of `Q` under the action on ideals. -/
abbrev decomposition (Q : Ideal S) : Subgroup G :=
  stabilizer G Q

/-- The inertia subgroup at an ideal `Q` (already in mathlib). -/
abbrev inertia (Q : Ideal S) : Subgroup G :=
  Q.toAddSubgroup.inertia G

@[simp] lemma inertia_le_decomposition (Q : Ideal S) :
    inertia (G := G) Q ≤ decomposition (G := G) Q :=
  Ideal.inertia_le_stabilizer (M := G) Q

namespace IsArithFrobAt

variable {Q : Ideal S} {σ : G}

lemma smul_ideal_eq [Q.IsPrime] [Finite (S ⧸ Q)] (hσ : IsArithFrobAt (R := R) σ Q) : σ • Q = Q := by
  classical
  -- Let `φ` be the `R`-algebra endomorphism induced by the action of `σ`.
  let φ : S →ₐ[R] S := MulSemiringAction.toAlgHom R S σ
  have hcomap : Q.comap φ = Q := by
    -- This is `AlgHom.IsArithFrobAt.comap_eq`, specialized to `φ`.
    simpa [IsArithFrobAt, φ] using (AlgHom.IsArithFrobAt.comap_eq (φ := φ) (Q := Q) hσ)
  -- Turn `comap φ Q = Q` into `map e Q = Q` using the underlying ring equivalence `e`.
  let e : S ≃+* S := MulSemiringAction.toRingEquiv G S σ
  have hcomap' : Q.comap (e : S →+* S) = Q := by
    -- `φ` and `e` have the same underlying ring hom.
    simpa [φ, e] using hcomap
  have hcomapEq : Ideal.comap e Q = Q := by
    simpa using hcomap'
  have hmap : Ideal.map e Q = Q := by
    -- `map e (comap e Q) = Q`, and `comap e Q = Q`.
    simpa [hcomapEq] using (Ideal.map_comap_eq_self_of_equiv (e := e) Q)
  -- Finally, rewrite pointwise smul on ideals as `map` under the action.
  simpa [Ideal.pointwise_smul_def, e] using hmap

lemma mem_decomposition [Q.IsPrime] [Finite (S ⧸ Q)] (hσ : IsArithFrobAt (R := R) σ Q) :
    σ ∈ decomposition (G := G) Q := by
  classical
  -- `σ ∈ stabilizer G Q ↔ σ • Q = Q`.
  simpa [decomposition, MulAction.mem_stabilizer_iff] using
    (smul_ideal_eq (R := R) (S := S) (G := G) (σ := σ) (Q := Q) hσ)

end IsArithFrobAt

section frobQuot

variable {Q : Ideal S}

/-- The inertia subgroup viewed inside the decomposition subgroup. -/
abbrev inertiaSubgroupOf (Q : Ideal S) : Subgroup (decomposition (G := G) Q) :=
  (inertia (G := G) Q).subgroupOf (decomposition (G := G) Q)

/-- The inertia subgroup is normal in the decomposition subgroup (as a kernel). -/
instance inertiaSubgroupOf_normal (Q : Ideal S) :
    (inertiaSubgroupOf (G := G) Q).Normal := by
  classical
  -- Direct proof: inertia is stable under conjugation by the stabilizer.
  refine ⟨?_⟩
  intro n hn g
  change (g.1 * n.1 * g.1⁻¹) ∈ inertia (G := G) Q
  intro x
  have hn' : n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x) ∈ Q := by
    have : n.1 ∈ inertia (G := G) Q := by
      simpa [inertiaSubgroupOf] using hn
    exact this (g.1⁻¹ • x)
  have : g.1 • (n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x)) ∈ Q := by
    have hmem : g.1 • (n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x)) ∈ g.1 • Q :=
      (Ideal.smul_mem_pointwise_smul_iff (a := g.1) (S := Q)
        (x := (n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x)))).2 hn'
    have h : g.1 • (n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x)) ∈ Q := by
      have h' := hmem
      rw [g.2] at h'
      exact h'
    exact h
  have hcalc :
      g.1 • (n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x)) = (g.1 * n.1 * g.1⁻¹) • x - x := by
    calc
      g.1 • (n.1 • (g.1⁻¹ • x) - (g.1⁻¹ • x))
          = g.1 • (n.1 • (g.1⁻¹ • x)) - g.1 • (g.1⁻¹ • x) := by
              simp [sub_eq_add_neg, smul_add, smul_neg]
      _ = (g.1 * n.1) • (g.1⁻¹ • x) - x := by
              have h1 :
                  g.1 • (n.1 • (g.1⁻¹ • x)) = (g.1 * n.1) • (g.1⁻¹ • x) := by
                simpa using (mul_smul g.1 n.1 (g.1⁻¹ • x)).symm
              have h2 : g.1 • (g.1⁻¹ • x) = x := by
                simp [smul_smul]
              simp [h1, h2]
      _ = (g.1 * n.1 * g.1⁻¹) • x - x := by
              simp [smul_smul, mul_assoc]
  simpa [hcalc] using this

/--
Given an arithmetic Frobenius element `σ` at `Q`, its image in the quotient `D(Q) ⧸ I(Q)`.
-/
noncomputable def frobQuotOf (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (σ : G) (hσ : IsArithFrobAt (R := R) σ Q) :
    (decomposition (G := G) Q) ⧸ inertiaSubgroupOf (G := G) Q :=
  QuotientGroup.mk ⟨σ, IsArithFrobAt.mem_decomposition (R := R) (S := S) (G := G) (Q := Q) hσ⟩

theorem frobQuotOf_eq_of_isArithFrobAt (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    {σ σ' : G} (hσ : IsArithFrobAt (R := R) σ Q) (hσ' : IsArithFrobAt (R := R) σ' Q) :
    frobQuotOf (R := R) (S := S) (G := G) Q σ hσ =
      frobQuotOf (R := R) (S := S) (G := G) Q σ' hσ' := by
  classical
  -- Build the stabilizer elements.
  let a : decomposition (G := G) Q :=
    ⟨σ, IsArithFrobAt.mem_decomposition (R := R) (S := S) (G := G) (Q := Q) hσ⟩
  let b : decomposition (G := G) Q :=
    ⟨σ', IsArithFrobAt.mem_decomposition (R := R) (S := S) (G := G) (Q := Q) hσ'⟩
  -- Unfold the definition and rewrite the goal in terms of coercions to the quotient.
  unfold frobQuotOf
  change ((a : (decomposition (G := G) Q) ⧸ inertiaSubgroupOf (G := G) Q) =
      (b : (decomposition (G := G) Q) ⧸ inertiaSubgroupOf (G := G) Q))
  -- Use the `div`-form so we can apply `mul_inv_mem_inertia` directly.
  -- In the quotient, `a = b` iff `a / b ∈ inertiaSubgroupOf Q`.
  rw [QuotientGroup.eq_iff_div_mem]
  -- `a / b` is `a * b⁻¹`, whose value in `G` is `σ * σ'⁻¹`.
  have : σ * σ'⁻¹ ∈ inertia (G := G) Q :=
    IsArithFrobAt.mul_inv_mem_inertia (R := R) (Q := Q) hσ hσ'
  -- Translate to `inertiaSubgroupOf`.
  simpa [a, b, inertiaSubgroupOf, inertia, decomposition, div_eq_mul_inv] using this

/--
The canonical Frobenius element in `D(Q) ⧸ I(Q)`, using mathlib's choice `arithFrobAt`.
-/
noncomputable def frobQuot (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite G]
    [Algebra.IsInvariant R S G] :
    (decomposition (G := G) Q) ⧸ inertiaSubgroupOf (G := G) Q :=
  frobQuotOf (R := R) (S := S) (G := G) Q (arithFrobAt (R := R) (G := G) Q)
    (IsArithFrobAt.arithFrobAt (R := R) (S := S) (G := G) (Q := Q))

end frobQuot

end

end Chebotarev

end PrimeNumberTheoremAnd
