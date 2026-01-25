import Mathlib.RingTheory.Frobenius
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Group.Conj
import PrimeNumberTheoremAnd.ChebotarevDirichletDensity
import PrimeNumberTheoremAnd.ChebotarevFrobenius
import PrimeNumberTheoremAnd.ChebotarevSets
import PrimeNumberTheoremAnd.ChebotarevDecomposition
import PrimeNumberTheoremAnd.ArtinLikeLSeries
import PrimeNumberTheoremAnd.ArtinLSeriesEulerFactor
import PrimeNumberTheoremAnd.ChebotarevReduction
import PrimeNumberTheoremAnd.ArtinLSeriesNat
import PrimeNumberTheoremAnd.ChebotarevArtinEuler
import PrimeNumberTheoremAnd.ChebotarevNatConjAssignment
import PrimeNumberTheoremAnd.ChebotarevArtinNat
import PrimeNumberTheoremAnd.ChebotarevArtinLSeries
import PrimeNumberTheoremAnd.ChebotarevConjugacyCounting
import PrimeNumberTheoremAnd.ArtinCharacter
import PrimeNumberTheoremAnd.ChebotarevCyclotomicPower
import PrimeNumberTheoremAnd.ChebotarevCyclotomicAbelian
import PrimeNumberTheoremAnd.ChebotarevFrobeniusRootsOfUnity
import PrimeNumberTheoremAnd.ChebotarevFrobeniusCyclotomic
import PrimeNumberTheoremAnd.ChebotarevUnramifiedNat
import PrimeNumberTheoremAnd.ChebotarevCyclotomicOverPrime
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusZeta
import PrimeNumberTheoremAnd.ChebotarevCyclotomicOrthogonality
import PrimeNumberTheoremAnd.ChebotarevEnoughRootsOfUnityComplex
import PrimeNumberTheoremAnd.ChebotarevCyclotomicPrimeSeries
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusCongruence
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusPrimeSet
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusPrimeSetBridge
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusDensityRatio
import PrimeNumberTheoremAnd.ChebotarevPrimeCoeffTsumPrimes
import PrimeNumberTheoremAnd.ChebotarevDirichletDensityTsumPrimes
import PrimeNumberTheoremAnd.ChebotarevDirichletDensityLimitCriterion
import PrimeNumberTheoremAnd.ChebotarevSeriesAllDivergesNearOne
import PrimeNumberTheoremAnd.ChebotarevPrimeSeriesSummable
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusPrimeTsumPrimes
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusRatioTsumPrimes
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusMainTerm
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusInfinite
import PrimeNumberTheoremAnd.ChebotarevFinitePrimeCorrection
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFiniteCorrectionBound
import PrimeNumberTheoremAnd.ChebotarevCyclotomicFrobeniusDensity

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

/-!
### 4. Frobenius elements and classes

These are developed as a standalone prerequisite file:
`PrimeNumberTheoremAnd.ChebotarevFrobenius`.
-/

/-! ### 5. Analytic prerequisites: what mathlib has (Dirichlet), and what it doesn’t (Artin) -/

section DirichletAnalytic

/-!
Mathlib currently has a substantial analytic theory of *Dirichlet* L-functions (analytic
continuation, functional equation, nonvanishing on `re s ≥ 1`, etc.), developed in
`Mathlib.NumberTheory.LSeries.*`.

By contrast, **Artin** L-functions are not (yet) defined in mathlib; for Chebotarev one should
therefore either:
- reduce analytic input to the Dirichlet (cyclotomic / abelian-over-ℚ) case where possible; or
- build Artin \(L\)-functions as a library development.

As a first, purely foundational step toward the latter, the file
`PrimeNumberTheoremAnd.ArtinLikeLSeries` packages the *naive Euler product ↔ Dirichlet series*
identity for L-series assembled from local prime-power data, under explicit summability hypotheses.
-/

open scoped Real Topology
open Filter Complex

section

variable {N : ℕ} [NeZero N] (χ : _root_.DirichletCharacter ℂ N)

lemma LFunction_eq_LSeries_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    _root_.DirichletCharacter.LFunction χ s = LSeries (χ ·) s :=
  _root_.DirichletCharacter.LFunction_eq_LSeries χ hs

lemma LFunction_ne_zero_of_one_le_re {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  _root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) hχs hs

end

end DirichletAnalytic

/-!
### 3. Next steps (to reach Chebotarev density)

To match Sharifi Thm 7.2.2 in a principled way, we still need:
- the number-field specialization of the `Frobenius` API (via `Algebra.IsInvariant` and `arithFrobAt`);
- the unramified condition and conjugacy-class formulation (`IsArithFrobAt.conj`, inertia subgroup);
- analytic input (Artin \(L\)-functions / Dedekind zeta asymptotics) as assumptions or imported facts.
-/

end Chebotarev
