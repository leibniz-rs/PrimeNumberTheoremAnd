import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.Group.Conj
import Mathlib.RingTheory.Ideal.Over

/-!
## Frobenius conjugacy classes (algebraic prerequisite for Chebotarev)

This file packages the **Frobenius conjugacy class** attached to a prime lying over a base prime,
using the existing mathlib Frobenius API in `Mathlib/RingTheory/Frobenius.lean`.

### Design principles

* We never redefine Frobenius: we use `arithFrobAt` and `IsArithFrobAt`.
* The correct object for Chebotarev is a **conjugacy class** in the Galois group, so we work in
  `ConjClasses G`.
* Statements are proved with explicit hypotheses (`Finite G`, invariance, finiteness of residue
  rings where needed); we do not rely on default values of `Nat.card` for infinite types.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (R G)

/--
The Frobenius element at a prime ideal `Q` of `S`, packaged as a conjugacy class in `G`.

This is the object that is stable under replacing `Q` by another prime over the same base prime.
-/
noncomputable def frobClass (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : ConjClasses G :=
  ConjClasses.mk (arithFrobAt (R := R) (G := G) Q)

variable {R G}

@[simp]
theorem frobClass_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')] (h : Q.under R = Q'.under R) :
    frobClass (R := R) (G := G) Q = frobClass (R := R) (G := G) Q' := by
  classical
  apply (ConjClasses.mk_eq_mk_iff_isConj).2
  simpa using (_root_.isConj_arithFrobAt (R := R) (S := S) (G := G) (Q := Q) (Q' := Q') h)

end

section primesOver

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

/--
The Frobenius conjugacy class attached to a *base* prime `P : Ideal R`,
defined by choosing a prime `Q` of `S` lying over `P` with finite residue ring.

The output does not depend on the choice of `Q`.
-/
noncomputable def frobClassOver (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) : ConjClasses G :=
  by
    classical
    let Q0 : Ideal.primesOver P S := Classical.choose hP
    letI : Finite (S ⧸ (Q0.1 : Ideal S)) := Classical.choose_spec hP
    exact frobClass (R := R) (G := G) (Q := (Q0.1 : Ideal S))

theorem frobClassOver_eq_frobClass (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) (Q : Ideal.primesOver P S)
    [Finite (S ⧸ (Q.1 : Ideal S))] :
    frobClassOver (R := R) (S := S) (G := G) P hP =
      frobClass (R := R) (G := G) (Q := (Q.1 : Ideal S)) := by
  classical
  -- Introduce the chosen prime over `P` carrying the finiteness witness.
  let Q0 : Ideal.primesOver P S := Classical.choose hP
  letI : Finite (S ⧸ (Q0.1 : Ideal S)) := Classical.choose_spec hP
  have hQ0_under : (Q0.1 : Ideal S).under R = P := by
    simpa using (Q0.2.2.over (A := R) (B := S) (p := P) (P := Q0.1)).symm
  have hQ_under : (Q.1 : Ideal S).under R = P := by
    simpa using (Q.2.2.over (A := R) (B := S) (p := P) (P := Q.1)).symm
  have hunder : (Q0.1 : Ideal S).under R = (Q.1 : Ideal S).under R := by
    simp [hQ0_under, hQ_under]
  -- `frobClassOver` is definitionally `frobClass` at `Q0`, and `frobClass` is invariant
  -- under changing to another prime over the same base prime.
  have : frobClassOver (R := R) (S := S) (G := G) P hP =
      frobClass (R := R) (G := G) (Q := (Q0.1 : Ideal S)) := by
    -- unfold the definition and discharge definitional equalities
    simp [frobClassOver, Q0]
  -- now transport along the under-equality
  simpa [this] using (frobClass_eq_of_under_eq (R := R) (S := S) (G := G)
    (Q := (Q0.1 : Ideal S)) (Q' := (Q.1 : Ideal S)) hunder)

end primesOver

end Chebotarev

end PrimeNumberTheoremAnd

