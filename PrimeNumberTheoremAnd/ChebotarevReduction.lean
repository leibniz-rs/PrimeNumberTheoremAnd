import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
## Chebotarev reduction: group-theoretic infrastructure (WIP)

Sharifi’s reduction steps eventually require moving Frobenius conjugacy classes along maps of
Galois groups (restriction to intermediate fields, quotienting by normal subgroups, etc.).

This file collects **pure group-theoretic** lemmas about `ConjClasses` and its functoriality.

No number-field input appears here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace ChebotarevReduction

section ConjClasses

variable {G H K : Type*} [Group G] [Group H] [Group K]

@[simp] lemma conjClasses_map_mk (f : G →* H) (g : G) :
    ConjClasses.map f (ConjClasses.mk g) = ConjClasses.mk (f g) := by
  rfl

lemma conjClasses_map_id (C : ConjClasses G) :
    ConjClasses.map (MonoidHom.id G) C = C := by
  refine Quotient.inductionOn C (fun g => ?_) 
  rfl

lemma conjClasses_map_comp (f : G →* H) (g : H →* K) (C : ConjClasses G) :
    ConjClasses.map (g.comp f) C = ConjClasses.map g (ConjClasses.map f C) := by
  refine Quotient.inductionOn C (fun x => ?_)
  rfl

end ConjClasses

end ChebotarevReduction

end PrimeNumberTheoremAnd

