import PrimeNumberTheoremAnd.ChebotarevFrobenius

/-!
## Chebotarev: producing a Nat-prime indexed conjugacy-class assignment

This file is a small adaptor: given any map `P : Nat.Primes → Ideal R` together with finiteness
witnesses for Frobenius at each `P p`, we get a map

`Nat.Primes → ConjClasses G`

by sending `p` to `frobClassOver (P p)`.

This is intentionally abstract: we do **not** assume `P p` is prime, or that it is the prime ideal
`(p)` in a specific arithmetic ring. Those specializations should be built later, as genuine
mathematics, not as ad hoc definitions.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical

namespace Chebotarev

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

/--
From a `Nat.Primes`-indexed family of base ideals `P p : Ideal R` and a finiteness witness at each,
produce the corresponding Frobenius conjugacy class assignment.
-/
noncomputable def frobClassOverNat (P : Nat.Primes → Ideal R)
    (hP : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) :
    Nat.Primes → ConjClasses G :=
  fun p => PrimeNumberTheoremAnd.Chebotarev.frobClassOver (R := R) (S := S) (G := G) (P p) (hP p)

theorem frobClassOverNat_congr (P : Nat.Primes → Ideal R)
    (hP hP' : ∀ p : Nat.Primes, ∃ Q : Ideal.primesOver (P p) S, Finite (S ⧸ Q.1)) :
    frobClassOverNat (R := R) (S := S) (G := G) P hP =
      frobClassOverNat (R := R) (S := S) (G := G) P hP' := by
  classical
  funext p
  -- Pointwise, this is exactly `frobClassOver_congr`.
  simpa [frobClassOverNat] using
    (PrimeNumberTheoremAnd.Chebotarev.frobClassOver_congr (R := R) (S := S) (G := G)
      (P := P p) (hP := hP p) (hP' := hP' p))

end

end Chebotarev

end PrimeNumberTheoremAnd
