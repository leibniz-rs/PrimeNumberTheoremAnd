import PrimeNumberTheoremAnd.ChebotarevFrobenius

/-!
## Chebotarev sets (algebraic prerequisite)

This file defines the *Chebotarev set* attached to a conjugacy class, in a way that is:

* **choice-free** at the definition level (we define the predicate by the existence of a prime
  above a base prime with the right Frobenius class);
* accompanied by lemmas showing that the Frobenius class is independent of the choice of prime
  above the base prime, once the finiteness hypotheses needed to define `arithFrobAt` are present.

No analytic input is used here.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

open Ideal

/--
`HasFiniteResidueOver P` means: there exists a prime ideal of `S` lying over `P` whose residue ring
is finite.

This is exactly the amount of finiteness needed to talk about `arithFrobAt`.
-/
def HasFiniteResidueOver (P : Ideal R) : Prop :=
  ∃ Q : Ideal.primesOver P S, Finite (S ⧸ (Q.1 : Ideal S))

/--
Choice-free predicate: `HasFrobClass P C` means that *some* prime ideal above `P` (with finite
residue ring) has Frobenius conjugacy class equal to `C`.
-/
def HasFrobClass (P : Ideal R) (C : ConjClasses G) : Prop :=
  ∃ Q : Ideal.primesOver P S,
    ∃ _ : Finite (S ⧸ (Q.1 : Ideal S)),
      PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := (Q.1 : Ideal S)) = C

lemma hasFiniteResidueOver_iff (P : Ideal R) :
    HasFiniteResidueOver (R := R) (S := S) P ↔
      ∃ Q : Ideal.primesOver P S, Finite (S ⧸ (Q.1 : Ideal S)) :=
  Iff.rfl

/--
The Chebotarev set attached to a conjugacy class `C`: the set of *prime* ideals `P` of `R`
for which `C` occurs as the Frobenius conjugacy class above `P` (with finite residue ring).
-/
def chebotarevSet (C : ConjClasses G) : Set (Ideal R) :=
  {P | P.IsPrime ∧ HasFrobClass (R := R) (S := S) (G := G) P C}

/--
When a base ideal `P` admits a prime above it with finite residue ring, the “chosen” Frobenius
class `frobClassOver P hP` agrees with the existence-based predicate `HasFrobClass P`.
-/
theorem hasFrobClass_iff_frobClassOver_eq (P : Ideal R) (C : ConjClasses G)
    (hP : HasFiniteResidueOver (R := R) (S := S) P) :
    HasFrobClass (R := R) (S := S) (G := G) P C ↔
      PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) P hP = C := by
  classical
  -- Extract a witness prime `Q0` above `P` while keeping `hP` available (it appears in the goal).
  let Q0 : Ideal.primesOver P S := Classical.choose hP
  let hfin : Finite (S ⧸ (Q0.1 : Ideal S)) := Classical.choose_spec hP
  letI : Finite (S ⧸ (Q0.1 : Ideal S)) := hfin
  constructor
  · intro h
    rcases h with ⟨Q, hfinQ, hQ⟩
    letI : Finite (S ⧸ (Q.1 : Ideal S)) := hfinQ
    -- `frobClassOver` agrees with `frobClass` at the witness `Q`.
    have hOver :
        PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) P hP =
          PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := (Q.1 : Ideal S)) := by
      simpa using
        (PrimeNumberTheoremAnd.Chebotarev.frobClassOver_eq_frobClass (R := R) (S := S) (G := G)
          (P := P) (hP := hP) (Q := Q))
    simpa [hOver] using hQ
  · intro h
    -- Use the witness `Q0` to show `HasFrobClass`.
    have hQ0 :
        PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := (Q0.1 : Ideal S)) = C := by
      have hOver :
          PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) P hP =
            PrimeNumberTheoremAnd.Chebotarev.frobClass (R := R) (G := G) (Q := (Q0.1 : Ideal S)) := by
        simpa using
          (PrimeNumberTheoremAnd.Chebotarev.frobClassOver_eq_frobClass (R := R) (S := S) (G := G)
            (P := P) (hP := hP) (Q := Q0)).symm
      simpa [hOver] using h
    exact ⟨Q0, hfin, hQ0⟩

end

end Chebotarev

end PrimeNumberTheoremAnd

