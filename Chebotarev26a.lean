import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Group.Conj
import PrimeNumberTheoremAnd.ChebotarevDirichletDensity

/-!
## Chebotarev density theorem (work in progress)

This file is an **algebraic** scaffold for a Chebotarev density theorem development following
Sharifi (Ch. 7) / the standard Annals-style strategy, written to mathlib standards.

### Key review notes about the previous draft
- Re-defining Frobenius is unnecessary and risky: mathlib has a principled API in
  `Mathlib/RingTheory/Frobenius.lean`.
- Defining Dirichlet density via `tsum` without explicit summability hypotheses is a
  **misformalization**: in mathlib `tsum f` is defined as `0` when `f` is not summable, which can
  silently trivialize the ratio near \(s \to 1^+\).

Accordingly, we:
- use `IsArithFrobAt` / `AlgHom.IsArithFrobAt` from mathlib;
- re-express the “Frobenius on roots of unity” lemma by invoking
  `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`;
- keep Dirichlet density as an *assumption-driven* definition that cannot collapse to `0` by
  definition.
-/

set_option linter.unusedSectionVars false

namespace Chebotarev

open scoped Classical BigOperators

/-! ### 1. Frobenius elements: use mathlib’s API -/

section Frobenius

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {σ : G} {Q : Ideal S}

/--
If `σ` is an arithmetic Frobenius at `Q`, then `σ` acts on any `m`-th root of unity by raising to
the residue field cardinality \(q = \#(R / (Q \cap R))\), provided \(m \notin Q\).

This is `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` specialized to the action-induced algebra hom.
-/
theorem smul_eq_pow_of_isArithFrobAt
    [IsDomain S]
    (hσ : IsArithFrobAt (R := R) σ Q)
    {ζ : S} {m : ℕ} (hζ : ζ ^ m = 1) (hm : (m : S) ∉ Q) :
    σ • ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  simpa using
    (AlgHom.IsArithFrobAt.apply_of_pow_eq_one
      (φ := MulSemiringAction.toAlgHom R S σ) (Q := Q) (H := hσ) hζ hm)

/-- Convenience: apply the previous lemma when `ζ` is an `m`-primitive root. -/
theorem smul_eq_pow_of_isArithFrobAt_of_isPrimitiveRoot
    [IsDomain S]
    (hσ : IsArithFrobAt (R := R) σ Q)
    {ζ : S} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : (m : S) ∉ Q) :
    σ • ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  exact smul_eq_pow_of_isArithFrobAt (R := R) (S := S) (σ := σ) (Q := Q) hσ hζ.pow_eq_one hm

end Frobenius

/-! ### 2. Dirichlet density: developed as its own foundational file -/

/-!
We deliberately keep Dirichlet density out of this scaffold file.

The foundational definition (as a limit of prime Dirichlet series, with summability proved on
`s > 1` so no `tsum`-trivialization can occur) lives in
`PrimeNumberTheoremAnd.ChebotarevDirichletDensity`.
-/

/-! ### 3. Group theory scaffold: conjugacy-class size via centralizers -/

section ConjugacyCounting

open MulAction

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical

/--
Sharifi’s counting lemma: the size of the conjugacy class of `g` is the index of its centralizer.

We state this in a way that **cannot** silently collapse to `0`:
we assume `G` is finite (`[Fintype G]`) rather than using `Nat.card`/`Set.ncard` with no finiteness
hypotheses.

The proof is orbit–stabilizer for the conjugation action.
-/
theorem ncard_conjugatesOf_eq_index_centralizer (g : G) :
    (conjugatesOf g).ncard = (Subgroup.centralizer ({g} : Set G)).index := by
  classical
  have horbit : orbit (ConjAct G) g = conjugatesOf g := by
    ext x
    -- `ConjAct.mem_orbit_conjAct` gives `x ∈ orbit ↔ IsConj x g`.
    -- `conjugatesOf g` is `{x | IsConj g x}`, and `IsConj` is symmetric.
    simpa [conjugatesOf] using
      (ConjAct.mem_orbit_conjAct (g := x) (h := g) (G := G)).trans (isConj_comm (g := x) (h := g))
  calc
    (conjugatesOf g).ncard = (orbit (ConjAct G) g).ncard := by simp [horbit]
    _ = (MulAction.stabilizer (ConjAct G) g).index := by
          simpa using (MulAction.index_stabilizer (G := ConjAct G) (x := g)).symm
    _ = (Subgroup.centralizer ({ConjAct.toConjAct g} : Set (ConjAct G))).index := by
          -- `ConjAct.stabilizer_eq_centralizer` identifies the stabilizer with the centralizer.
          simp [ConjAct.stabilizer_eq_centralizer]
    _ = (Subgroup.centralizer ({g} : Set G)).index := by
          -- `ConjAct G` is a type alias for `G`, and `toConjAct` is the identity.
          rfl

end ConjugacyCounting

/-! ### 4. Frobenius elements: conjugacy over a fixed base prime -/

section FrobeniusConjugacy

open scoped Classical

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]
variable {Q Q' : Ideal S} [Q.IsPrime] [Q'.IsPrime]
variable [Finite (S ⧸ Q)] [Finite (S ⧸ Q')]

/--
In the Galois setting (finite group action, invariant base), Frobenius elements at primes lying
over the same base prime are conjugate.

This is exactly mathlib’s `_root_.isConj_arithFrobAt`, restated with explicit parameters.
-/
theorem isConj_arithFrobAt_of_under_eq (h : Q.under R = Q'.under R) :
    IsConj (arithFrobAt (R := R) (G := G) Q) (arithFrobAt (R := R) (G := G) Q') := by
  simpa using (_root_.isConj_arithFrobAt (R := R) (S := S) (G := G) (Q := Q) (Q' := Q') h)

end FrobeniusConjugacy

/-! ### 5. Frobenius conjugacy class attached to a prime -/

section FrobeniusClass

open scoped Classical

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {G : Type*} [Group G] [Finite G]
  [MulSemiringAction G S] [SMulCommClass G R S] [Algebra.IsInvariant R S G]

variable (R G)

/--
Given a prime ideal `Q` of `S` with finite residue ring, define the Frobenius element at `Q`
as a conjugacy class in `G`.

This is the right object for Chebotarev: it is invariant under replacing `Q` by another prime
lying over the same prime of `R`.
-/
noncomputable def frobClass (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] : ConjClasses G :=
  ConjClasses.mk (arithFrobAt (R := R) (G := G) Q)

variable {R G}

@[simp]
theorem frobClass_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')] (h : Q.under R = Q'.under R) :
    frobClass (R := R) (G := G) Q = frobClass (R := R) (G := G) Q' := by
  classical
  -- `arithFrobAt`'s are conjugate above the same base prime, hence define the same class.
  apply (ConjClasses.mk_eq_mk_iff_isConj).2
  simpa using (isConj_arithFrobAt_of_under_eq (R := R) (S := S) (G := G) (Q := Q) (Q' := Q') h)

end FrobeniusClass

/-! ### 5. Analytic prerequisites: what mathlib has (Dirichlet), and what it doesn’t (Artin) -/

section DirichletAnalytic

/-!
Mathlib currently has a substantial analytic theory of *Dirichlet* L-functions (analytic
continuation, functional equation, nonvanishing on `re s ≥ 1`, etc.), developed in
`Mathlib.NumberTheory.LSeries.*`.

By contrast, **Artin** L-functions are not (yet) defined in mathlib; for Chebotarev one should
therefore either:
- reduce analytic input to the Dirichlet (cyclotomic / abelian-over-ℚ) case where possible; or
- package the Artin-L-function properties needed by Sharifi as explicit hypotheses/axioms.
-/

open scoped Real Topology
open Filter Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

lemma LFunction_eq_LSeries_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LSeries (χ ·) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

lemma LFunction_ne_zero_of_one_le_re {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) hχs hs

end DirichletCharacter

end DirichletAnalytic

/-!
### 3. Next steps (to reach Chebotarev density)

To match Sharifi Thm 7.2.2 in a principled way, we still need:
- the number-field specialization of the `Frobenius` API (via `Algebra.IsInvariant` and `arithFrobAt`);
- the unramified condition and conjugacy-class formulation (`IsArithFrobAt.conj`, inertia subgroup);
- analytic input (Artin \(L\)-functions / Dedekind zeta asymptotics) as assumptions or imported facts.
-/

end Chebotarev
