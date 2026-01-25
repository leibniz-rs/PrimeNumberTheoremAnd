import Mathlib.NumberTheory.LSeries.Basic

/-!
## Dirichlet density (foundational, non-trivializing)

This file introduces a **safe** definition of Dirichlet density for sets of rational primes,
in a form suitable for later use in Chebotarev-style arguments.

### Design principles

* We define the relevant Dirichlet series using mathlib's `LSeries` API.
* We **prove** summability on the half-plane `s > 1` using
  `LSeriesSummable_of_bounded_of_one_lt_real`.
  This avoids any risk of misformalization stemming from the fact that `LSeries f s` is *defined*
  to be `0` when the series does not converge.
* Density is then a statement about `Tendsto` along `nhdsWithin 1 (Set.Ioi 1)`, so it only probes
  values at `s > 1`, where summability has been established.
-/

namespace PrimeNumberTheoremAnd

open scoped Topology Real
open scoped LSeries.notation

open Filter

namespace DirichletDensity

open Complex

/-- The Dirichlet coefficient sequence of a set of primes `S`. -/
noncomputable def coeff (S : Set ℕ) : ℕ → ℂ :=
  by
    classical
    exact fun n ↦ if n.Prime ∧ n ∈ S then 1 else 0

@[simp] lemma coeff_zero (S : Set ℕ) : coeff S 0 = 0 := by
  classical
  -- `Nat.Prime 0` is false, so the indicator is `0`.
  simp [coeff, Nat.not_prime_zero]

lemma norm_coeff_le_one (S : Set ℕ) {n : ℕ} (_hn : n ≠ 0) : ‖coeff S n‖ ≤ (1 : ℝ) := by
  classical
  by_cases h : n.Prime ∧ n ∈ S
  · simp [coeff, h]
  · simp [coeff, h]

/--
The prime Dirichlet series attached to `S` (as a function of a real variable `s`).

By construction this is the `LSeries` of `coeff S` evaluated at the real point `s`.
-/
noncomputable def series (S : Set ℕ) (s : ℝ) : ℂ :=
  LSeries (coeff S) (s : ℂ)

lemma summable_series (S : Set ℕ) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (coeff S) (s : ℂ) := by
  -- bounded coefficients ⇒ absolute convergence for `s > 1`
  refine LSeriesSummable_of_bounded_of_one_lt_real (f := coeff S) (m := (1 : ℝ))
    (fun n hn ↦ norm_coeff_le_one S hn) hs

/-- The denominator series: sum over all primes. -/
noncomputable abbrev seriesAll (s : ℝ) : ℂ :=
  series (S := (Set.univ : Set ℕ)) s

/-- The Dirichlet-density ratio function for a set of primes `S`. -/
noncomputable def ratio (S : Set ℕ) (s : ℝ) : ℂ :=
  series S s / seriesAll s

/--
`HasDensity S δ` means that the Dirichlet density of `S` exists and equals `δ`,
defined as a limit as `s → 1⁺` of the ratio of prime Dirichlet series.

We take values in `ℂ` because `LSeries` is `ℂ`-valued; later developments can show the value is
real when `S` is a set of primes.
-/
def HasDensity (S : Set ℕ) (delta : ℂ) : Prop :=
  Tendsto (ratio S) (nhdsWithin 1 (Set.Ioi 1)) (nhds delta)

end DirichletDensity

end PrimeNumberTheoremAnd

