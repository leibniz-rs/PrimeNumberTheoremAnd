import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HolomorphicLog

import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import PrimeNumberTheoremAnd.ChebotarevPrimeSeriesSummable

/-!
## Boundedness of prime Dirichlet series for nontrivial characters near `s = 1⁺`

This file provides the analytic input needed in the cyclotomic Chebotarev density argument:
for a nontrivial Dirichlet character `χ`, the prime series `∑' p, χ p / p^s` is **bounded**
as `s → 1⁺` (real).

We structure the proof in a mathlib-friendly way:
- introduce the prime-log series `Hχ(s) = ∑'p -log(1 - χ(p) p^{-s})`;
- show `exp(Hχ(s)) = LFunction χ s` for `1 < re s` using `EulerProduct.exp_tsum_primes_log_eq_tsum`
  and `DirichletCharacter.LFunction_eq_LSeries`;
- use existence of a holomorphic logarithm of `LFunction χ` on a small rectangular neighborhood of
  `1` (since `LFunction χ 1 ≠ 0` for `χ ≠ 1`);
- deduce `Hχ` differs from this holomorphic log by an integer multiple of `2π i`, hence is bounded;
- transfer boundedness to `∑'p χ(p)/p^s` using Taylor bounds for `log(1+z)`.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical Real Topology

open Filter Complex

namespace Chebotarev

namespace DirichletCharacterPrime

open Nat.Primes

variable {N : ℕ} [NeZero N]

/-!
### A rectangular neighborhood of `1`

We use a small open rectangle around `1` so that we can apply our holomorphic-log theorem
(`DifferentiableOn.exists_log_of_rectangularConvex`).
-/

def rect (δ : ℝ) : Set ℂ :=
  {z : ℂ | (1 - δ) < z.re} ∩
    ({z : ℂ | z.re < (1 + δ)} ∩
      ({z : ℂ | (-δ) < z.im} ∩
        {z : ℂ | z.im < δ}))

lemma isOpen_rect (δ : ℝ) : IsOpen (rect δ) := by
  -- A finite intersection of open half-spaces in `re` and `im`.
  -- We keep it explicit to avoid definitional unfolding timeouts.
  have h1 : IsOpen {z : ℂ | (1 - δ) < z.re} := isOpen_lt continuous_const continuous_re
  have h2 : IsOpen {z : ℂ | z.re < (1 + δ)} := isOpen_lt continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | (-δ) < z.im} := isOpen_lt continuous_const continuous_im
  have h4 : IsOpen {z : ℂ | z.im < δ} := isOpen_lt continuous_im continuous_const
  simpa [rect, Set.inter_assoc] using h1.inter (h2.inter (h3.inter h4))

lemma mem_rect_one {δ : ℝ} (hδ : 0 < δ) : (1 : ℂ) ∈ rect δ := by
  simp [rect, hδ]

lemma convex_rect {δ : ℝ} : Convex ℝ (rect δ) := by
  intro x hx y hy a b ha hb hab
  have hx' :
      (1 - δ) < x.re ∧ x.re < (1 + δ) ∧ (-δ) < x.im ∧ x.im < δ := by
    simpa [rect, Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hx
  have hy' :
      (1 - δ) < y.re ∧ y.re < (1 + δ) ∧ (-δ) < y.im ∧ y.im < δ := by
    simpa [rect, Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hy
  rcases hx' with ⟨hxreL, hxrest⟩
  rcases hxrest with ⟨hxreU, hximrest⟩
  rcases hximrest with ⟨hximL, hximU⟩
  rcases hy' with ⟨hyreL, hyrest⟩
  rcases hyrest with ⟨hyreU, hyimrest⟩
  rcases hyimrest with ⟨hyimL, hyimU⟩
  -- Build membership in `rect δ` (nested intersections).
  refine ⟨?_, ?_⟩
  · -- lower bound on `re`
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hyreL
    · by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa [hb0, ha1] using hxreL
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hxa : a * (1 - δ) < a * x.re := mul_lt_mul_of_pos_left hxreL ha_pos
        have hyb : b * (1 - δ) < b * y.re := mul_lt_mul_of_pos_left hyreL hb_pos
        have hsum : a * (1 - δ) + b * (1 - δ) < a * x.re + b * y.re := add_lt_add hxa hyb
        have hleft : a * (1 - δ) + b * (1 - δ) = (a + b) * (1 - δ) := by ring
        have : (1 - δ) < a * x.re + b * y.re := by
          have : (a + b) * (1 - δ) < a * x.re + b * y.re := by simpa [hleft] using hsum
          simpa [hab] using this
        simpa [rect, Set.mem_inter_iff, smul_eq_mul, add_re, mul_re, mul_assoc, add_assoc,
          add_left_comm, add_comm] using this
  · refine ⟨?_, ?_⟩
    · -- upper bound on `re`
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hyreU
      · by_cases hb0 : b = 0
        · have ha1 : a = 1 := by linarith
          simpa [hb0, ha1] using hxreU
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
          have hxa : a * x.re < a * (1 + δ) := mul_lt_mul_of_pos_left hxreU ha_pos
          have hyb : b * y.re < b * (1 + δ) := mul_lt_mul_of_pos_left hyreU hb_pos
          have hsum : a * x.re + b * y.re < a * (1 + δ) + b * (1 + δ) := add_lt_add hxa hyb
          have hright : a * (1 + δ) + b * (1 + δ) = (a + b) * (1 + δ) := by ring
          have : a * x.re + b * y.re < (a + b) * (1 + δ) := by simpa [hright] using hsum
          have : a * x.re + b * y.re < (1 + δ) := by simpa [hab] using this
          simpa [rect, Set.mem_inter_iff, smul_eq_mul, add_re, mul_re, mul_assoc, add_assoc,
            add_left_comm, add_comm] using this
    · refine ⟨?_, ?_⟩
      · -- lower bound on `im`
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [ha0, hb1] using hyimL
        · by_cases hb0 : b = 0
          · have ha1 : a = 1 := by linarith
            simpa [hb0, ha1] using hximL
          · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
            have hxa : a * (-δ) < a * x.im := mul_lt_mul_of_pos_left hximL ha_pos
            have hyb : b * (-δ) < b * y.im := mul_lt_mul_of_pos_left hyimL hb_pos
            have hsum : a * (-δ) + b * (-δ) < a * x.im + b * y.im := add_lt_add hxa hyb
            have : (-δ) < a * x.im + b * y.im := by
              have hEq : (a + b) * (-δ) = a * (-δ) + b * (-δ) := by ring
              have h' : (a + b) * (-δ) < a * x.im + b * y.im := by
                -- rewrite the LHS to match `hsum`
                simpa [hEq] using hsum
              simpa [hab] using h'
            simpa [rect, Set.mem_inter_iff, smul_eq_mul, add_im, mul_im, mul_assoc, add_assoc,
              add_left_comm, add_comm] using this
      · -- upper bound on `im`
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simpa [ha0, hb1] using hyimU
        · by_cases hb0 : b = 0
          · have ha1 : a = 1 := by linarith
            simpa [hb0, ha1] using hximU
          · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
            have hxa : a * x.im < a * δ := mul_lt_mul_of_pos_left hximU ha_pos
            have hyb : b * y.im < b * δ := mul_lt_mul_of_pos_left hyimU hb_pos
            have hsum : a * x.im + b * y.im < a * δ + b * δ := add_lt_add hxa hyb
            have hright : a * δ + b * δ = (a + b) * δ := by ring
            have : a * x.im + b * y.im < (a + b) * δ := by simpa [hright] using hsum
            have : a * x.im + b * y.im < δ := by simpa [hab] using this
            simpa [rect, Set.mem_inter_iff, smul_eq_mul, add_im, mul_im, mul_assoc, add_assoc,
              add_left_comm, add_comm] using this

lemma rectangularConvex_rect {δ : ℝ} : Complex.RectangularConvex (rect δ) := by
  intro x y hx hy
  have hx' :
      (1 - δ) < x.re ∧ x.re < (1 + δ) ∧ (-δ) < x.im ∧ x.im < δ := by
    simpa [rect, Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hx
  have hy' :
      (1 - δ) < y.re ∧ y.re < (1 + δ) ∧ (-δ) < y.im ∧ y.im < δ := by
    simpa [rect, Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hy
  rcases hx' with ⟨hxreL, hxrest⟩
  rcases hxrest with ⟨hxreU, hximrest⟩
  rcases hximrest with ⟨hximL, hximU⟩
  rcases hy' with ⟨hyreL, hyrest⟩
  rcases hyrest with ⟨hyreU, hyimrest⟩
  rcases hyimrest with ⟨hyimL, hyimU⟩
  refine ⟨?_, ?_⟩
  · -- `x.re + y.im * I`
    have : (x.re + y.im * Complex.I : ℂ) ∈ rect δ := by
      -- `simp` reduces this to the four inequalities for `x.re` and `y.im`.
      simp [rect, Set.mem_inter_iff, hxreL, hxreU, hyimL, hyimU]
    exact this
  · -- `y.re + x.im * I`
    have : (y.re + x.im * Complex.I : ℂ) ∈ rect δ := by
      simp [rect, Set.mem_inter_iff, hyreL, hyreU, hximL, hximU]
    exact this

/-!
### A neighborhood where `LFunction χ` is nonzero

For `χ ≠ 1`, we use nonvanishing at `s = 1` and continuity to get a small rectangle around `1`
on which `LFunction χ` does not vanish.
-/

lemma rect_subset_ball {δ ε : ℝ} (hδε : 2 * δ < ε) :
    rect δ ⊆ Metric.ball (1 : ℂ) ε := by
  intro z hz
  have hz' :
      (1 - δ) < z.re ∧ z.re < (1 + δ) ∧ (-δ) < z.im ∧ z.im < δ := by
    simpa [rect, Set.mem_inter_iff, and_assoc, and_left_comm, and_comm] using hz
  rcases hz' with ⟨hzreL, hzrest⟩
  rcases hzrest with ⟨hzreU, hzimrest⟩
  rcases hzimrest with ⟨hzimL, hzimU⟩

  have hre : |z.re - 1| < δ := by
    refine abs_lt.2 ?_
    constructor <;> linarith
  have him : |z.im| < δ := by
    refine abs_lt.2 ?_
    constructor <;> linarith

  have hnorm : ‖z - (1 : ℂ)‖ < ε := by
    have hzdecomp : z - (1 : ℂ) = ((z.re : ℂ) - (1 : ℂ)) + z.im * Complex.I := by
      -- write `z = z.re + z.im * I` and rearrange
      calc
        z - (1 : ℂ) = ((z.re : ℂ) + z.im * Complex.I) - (1 : ℂ) := by
          simp [Complex.re_add_im]
        _ = ((z.re : ℂ) - (1 : ℂ)) + z.im * Complex.I := by
          ring
    have hle : ‖z - (1 : ℂ)‖ ≤ |z.re - 1| + |z.im| := by
      -- triangle inequality
      rw [hzdecomp]
      have h' :
          ‖((z.re : ℂ) - (1 : ℂ)) + z.im * Complex.I‖ ≤
            ‖(z.re : ℂ) - (1 : ℂ)‖ + ‖z.im * Complex.I‖ :=
        norm_add_le _ _
      -- simplify norms: `‖(t : ℂ)‖ = |t|` and `‖(u : ℂ) * I‖ = |u|`
      have hreCast : ((z.re : ℂ) - (1 : ℂ)) = ((z.re - 1 : ℝ) : ℂ) := by
        simp
      have hReNorm : ‖(z.re : ℂ) - (1 : ℂ)‖ = |z.re - 1| := by
        -- rewrite as a real number embedded in `ℂ`
        have h₁ : ‖(z.re : ℂ) - (1 : ℂ)‖ = ‖((z.re - 1 : ℝ) : ℂ)‖ := by
          exact congrArg (fun w : ℂ => ‖w‖) hreCast
        -- and simplify the norm of a real complex number
        calc
          ‖(z.re : ℂ) - (1 : ℂ)‖ = ‖((z.re - 1 : ℝ) : ℂ)‖ := h₁
          _ = ‖(z.re - 1 : ℝ)‖ := by
            simpa using (norm_real (z.re - 1))
          _ = |z.re - 1| := by
            simp [Real.norm_eq_abs]
      have hImNorm : ‖z.im * Complex.I‖ = |z.im| := by
        -- `‖(z.im : ℂ) * I‖ = ‖(z.im : ℂ)‖`
        calc
          ‖(z.im : ℂ) * Complex.I‖ = ‖(z.im : ℂ)‖ * ‖(Complex.I : ℂ)‖ := by
            exact norm_mul (z.im : ℂ) (Complex.I : ℂ)
          _ = ‖(z.im : ℂ)‖ := by simp
          _ = |z.im| := by
            simp [norm_real, Real.norm_eq_abs]
      -- rewrite RHS of `h'` using these identities
      simpa [hReNorm, hImNorm] using h'
    have hsumlt : |z.re - 1| + |z.im| < 2 * δ := by
      have : |z.re - 1| + |z.im| < δ + δ := add_lt_add hre him
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using this
    exact lt_of_le_of_lt hle (hsumlt.trans hδε)
  -- translate to `Metric.ball`
  simpa [Metric.mem_ball, dist_eq_norm] using hnorm

lemma exists_delta_LFunction_ne_zero_on_rect (χ : _root_.DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ rect δ, _root_.DirichletCharacter.LFunction χ z ≠ 0 := by
  let f : ℂ → ℂ := fun z ↦ _root_.DirichletCharacter.LFunction χ z
  have hfcont : Continuous f :=
    (_root_.DirichletCharacter.differentiable_LFunction (χ := χ) hχ).continuous
  have hopen : IsOpen {z : ℂ | f z ≠ 0} := by
    simpa [f] using (isOpen_ne.preimage hfcont)
  have h1 : f 1 ≠ 0 := by
    simpa [f] using (_root_.DirichletCharacter.LFunction_apply_one_ne_zero (χ := χ) hχ)
  have hnhds : {z : ℂ | f z ≠ 0} ∈ 𝓝 (1 : ℂ) := hopen.mem_nhds (by simpa [Set.mem_setOf_eq] using h1)
  rcases (Metric.mem_nhds_iff.mp hnhds) with ⟨ε, hεpos, hball⟩
  refine ⟨ε / 4, by nlinarith, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (1 : ℂ) ε := by
    have : rect (ε / 4) ⊆ Metric.ball (1 : ℂ) ε := by
      have : 2 * (ε / 4) < ε := by nlinarith
      exact rect_subset_ball (δ := ε / 4) (ε := ε) this
    exact this hz
  exact hball hzball

theorem exists_log_LFunction_on_rect (χ : _root_.DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (rect δ) ∧
        ∀ z ∈ rect δ, Complex.exp (g z) = _root_.DirichletCharacter.LFunction χ z := by
  rcases exists_delta_LFunction_ne_zero_on_rect (N := N) χ hχ with ⟨δ, hδpos, hne⟩
  have hopen : IsOpen (rect δ) := isOpen_rect δ
  have hconv : Convex ℝ (rect δ) := convex_rect (δ := δ)
  have hrect : Complex.RectangularConvex (rect δ) := rectangularConvex_rect (δ := δ)
  have hneU : (rect δ).Nonempty := ⟨1, mem_rect_one (δ := δ) hδpos⟩
  have hf : DifferentiableOn ℂ (fun z : ℂ ↦ _root_.DirichletCharacter.LFunction χ z) (rect δ) :=
    (_root_.DirichletCharacter.differentiable_LFunction (χ := χ) hχ).differentiableOn
  obtain ⟨g, hg, hexp⟩ :=
    Complex.DifferentiableOn.exists_log_of_rectangularConvex (U := rect δ)
      hopen hconv hrect hneU hf (by intro z hz; exact hne z hz)
  exact ⟨δ, hδpos, g, hg, hexp⟩

noncomputable
def primeLogSeries (χ : _root_.DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - χ p * (p : ℂ) ^ (-s))

noncomputable
def primeSeries (χ : _root_.DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, χ p * (p : ℂ) ^ (-s)

omit [NeZero N] in
lemma exp_primeLogSeries_eq_LSeries (χ : _root_.DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (primeLogSeries (N := N) χ s) = LSeries ((χ ·) : ℕ → ℂ) s := by
  -- Use the Euler-product logarithm lemma for Dirichlet L-series.
  -- This is stated for `L ↗χ`; unfold to the same `LSeries` we use.
  simpa [primeLogSeries] using
    (_root_.DirichletCharacter.LSeries_eulerProduct_exp_log (χ := χ) (s := s) hs)

lemma exp_primeLogSeries_eq_LFunction (χ : _root_.DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (primeLogSeries (N := N) χ s) = _root_.DirichletCharacter.LFunction χ s := by
  -- Combine the previous lemma with the identity `LFunction = LSeries` on `re s > 1`.
  simpa [(_root_.DirichletCharacter.LFunction_eq_LSeries (χ := χ) hs).symm] using
    (exp_primeLogSeries_eq_LSeries (N := N) χ hs)

/-!
### Local constancy and boundedness near `s = 1`

We now complete the analytic argument:

* prove `primeLogSeries` is continuous on half-planes `{s | 1 + ε < re s}` using uniform bounds and
  `continuousOn_tsum`,
* on a small interval `(1, 1+ε)` the difference between `primeLogSeries` and a holomorphic log of
  `LFunction` is locally constant (since `exp` is locally injective),
* deduce boundedness of `primeLogSeries` near `1` along the real axis,
* transfer to `primeSeries` using the standard Taylor bound for `log (1+z) - z`.
-/

section BoundedNearOne

open scoped Topology

omit [NeZero N] in
private lemma norm_chi_mul_cpow_le {ε : ℝ} (hε : 0 < ε) (χ : _root_.DirichletCharacter ℂ N)
    (p : Nat.Primes) {s : ℂ} (hs : 1 + ε < s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + ε)) := by
  have hne : (-s).re ≠ 0 := by
    -- `(-s).re = -s.re` and `s.re > 0` since `1 + ε < s.re`.
    have : 0 < s.re := (lt_trans (by linarith [hε]) hs)
    simpa using (ne_of_gt (show 0 < s.re by exact this))
  have hchi : ‖χ p‖ ≤ (1 : ℝ) := by simpa using (_root_.DirichletCharacter.norm_le_one (χ := χ) p)
  have hcpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + ε)) := by
    -- `‖p ^ (-s)‖ = p ^ (-re s)` and use monotonicity in the exponent.
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp p.2.pos)
    have hmono : (p : ℝ) ^ ((-s).re) ≤ (p : ℝ) ^ (-(1 + ε)) := by
      apply Real.rpow_le_rpow_of_exponent_le hp1
      -- `(-s).re = -s.re`
      have : (-s).re ≤ -(1 + ε) := by
        -- from `1 + ε < s.re`
        refine le_of_lt ?_
        have : -(s.re) < -(1 + ε) := neg_lt_neg hs
        simpa [Complex.neg_re] using this
      exact this
    -- rewrite the LHS norm and conclude by monotonicity
    calc
      ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ ((-s).re) := by
        simp [norm_natCast_cpow_of_re_ne_zero _ hne]
      _ ≤ (p : ℝ) ^ (-(1 + ε)) := hmono
  -- combine
  calc
    ‖χ p * (p : ℂ) ^ (-s)‖
        ≤ ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ := by simp
    _ ≤ 1 * (p : ℝ) ^ (-(1 + ε)) := by gcongr
    _ = (p : ℝ) ^ (-(1 + ε)) := by simp

omit [NeZero N] in
private lemma norm_chi_mul_cpow_le_half {ε : ℝ} (hε : 0 < ε) (χ : _root_.DirichletCharacter ℂ N)
    (p : Nat.Primes) {s : ℂ} (hs : 1 + ε < s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) := by
  have h₁ : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 + ε)) :=
    norm_chi_mul_cpow_le (N := N) hε χ p hs
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.2.two_le
  have hneg : (-(1 + ε) : ℝ) ≤ 0 := by linarith
  have h₂ : (p : ℝ) ^ (-(1 + ε)) ≤ (2 : ℝ) ^ (-(1 + ε)) := by
    -- for nonpositive exponent, `x ≤ y` gives `y^z ≤ x^z`.
    simpa using (Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (2 : ℝ)) hp2 hneg)
  have h₃ : (2 : ℝ) ^ (-(1 + ε)) < (1 / 2 : ℝ) := by
    -- strict since `-(1+ε) < -1`
    have : (-(1 + ε) : ℝ) < (-1 : ℝ) := by linarith
    -- monotonic in the exponent for base > 1
    have h' : (2 : ℝ) ^ (-(1 + ε)) < (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
    simpa [Real.rpow_neg, Real.rpow_one] using h'
  exact h₁.trans (h₂.trans (le_of_lt h₃))

omit [NeZero N] in
private lemma norm_primeLogSeries_term_le {ε : ℝ} (hε : 0 < ε) (χ : _root_.DirichletCharacter ℂ N)
    (p : Nat.Primes) {s : ℂ} (hs : 1 + ε < s.re) :
    ‖-Complex.log (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε)) := by
  set w : ℂ := χ p * (p : ℂ) ^ (-s)
  have hw : ‖w‖ ≤ (1 / 2 : ℝ) := by
    simpa [w] using norm_chi_mul_cpow_le_half (N := N) hε χ p hs
  -- `‖log(1-w)‖ ≤ (3/2)‖w‖` for `‖w‖ ≤ 1/2`
  have hlog : ‖Complex.log (1 - w)‖ ≤ (3 / 2 : ℝ) * ‖w‖ := by
    -- use the `1+z` lemma with `z = -w`
    have : ‖Complex.log (1 + (-w))‖ ≤ (3 / 2 : ℝ) * ‖-w‖ :=
      Complex.norm_log_one_add_half_le_self (z := -w) (by simpa [norm_neg] using hw)
    simpa [sub_eq_add_neg, norm_neg] using this
  -- put everything together and replace `‖w‖` by `p^(-(1+ε))`
  have hw' : ‖w‖ ≤ (p : ℝ) ^ (-(1 + ε)) :=
    (norm_chi_mul_cpow_le (N := N) hε χ p hs) |> (by simpa [w] using ·)
  calc
    ‖-Complex.log (1 - w)‖ = ‖Complex.log (1 - w)‖ := by simp
    _ ≤ (3 / 2 : ℝ) * ‖w‖ := hlog
    _ ≤ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε)) := by gcongr

omit [NeZero N] in
private lemma continuousOn_primeLogSeries_halfPlane (χ : _root_.DirichletCharacter ℂ N)
    {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (primeLogSeries (N := N) χ) {s : ℂ | 1 + ε < s.re} := by
  -- Apply `continuousOn_tsum` with uniform domination by `p^(-(1+ε))`.
  classical
  -- summable bound
  have hsumm : Summable (fun p : Nat.Primes ↦ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε))) := by
    have : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-(1 + ε))) := by
      -- `-(1+ε) < -1`
      have : (-(1 + ε) : ℝ) < (-1 : ℝ) := by linarith
      exact (Nat.Primes.summable_rpow (r := (-(1 + ε) : ℝ))).2 this
    simpa [mul_assoc] using this.mul_left (3 / 2 : ℝ)
  refine continuousOn_tsum
      (u := fun p : Nat.Primes ↦ (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 + ε)))
      (f := fun p s ↦ -Complex.log (1 - χ p * (p : ℂ) ^ (-s)))
      (s := {s : ℂ | 1 + ε < s.re}) ?_ hsumm ?_
  · intro p s hs
    -- continuity of the summand: all pieces are continuous, and the log is taken in `slitPlane`
    -- since `‖χ(p) p^{-s}‖ < 1`.
    have hs' : 1 + ε < s.re := hs
    have hw_le : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) :=
      norm_chi_mul_cpow_le_half (N := N) hε χ p hs'
    have hw_lt : ‖-(χ p * (p : ℂ) ^ (-s))‖ < (1 : ℝ) := by
      simpa [norm_neg] using (lt_of_le_of_lt hw_le one_half_lt_one)
    have hslit : (1 - χ p * (p : ℂ) ^ (-s)) ∈ slitPlane := by
      -- `1 - w = 1 + (-w)` with `‖-w‖ < 1`
      simpa [sub_eq_add_neg] using (mem_slitPlane_of_norm_lt_one hw_lt)
    -- assemble continuity
    have hpow : ContinuousWithinAt (fun z : ℂ ↦ (p : ℂ) ^ (-z)) {z : ℂ | 1 + ε < z.re} s := by
      -- `z ↦ (p:ℂ) ^ (-z)` is a composition of continuous maps
      have h1 : ContinuousAt (fun t : ℂ ↦ (p : ℂ) ^ t) (-s) :=
        continuousAt_const_cpow (a := (p : ℂ)) (b := -s) (by exact_mod_cast p.2.ne_zero)
      have h2 : ContinuousWithinAt (fun z : ℂ ↦ -z) {z : ℂ | 1 + ε < z.re} s :=
        (continuous_neg.continuousAt).continuousWithinAt
      exact h1.comp_continuousWithinAt h2
    have hinner :
        ContinuousWithinAt (fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) {z : ℂ | 1 + ε < z.re} s := by
      exact continuousWithinAt_const.sub (continuousWithinAt_const.mul hpow)
    -- now compose with `log` on `slitPlane` and negate
    have hlog :
        ContinuousWithinAt (fun z : ℂ ↦ Complex.log (1 - χ p * (p : ℂ) ^ (-z)))
          {z : ℂ | 1 + ε < z.re} s := hinner.clog hslit
    simpa using hlog.neg
  · intro p s hs
    exact norm_primeLogSeries_term_le (N := N) hε χ p hs

omit [NeZero N] in
private lemma continuousAt_primeLogSeries (χ : _root_.DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : ContinuousAt (primeLogSeries (N := N) χ) s := by
  -- Choose `ε = (re s - 1)/2`, so that `s` lies in `{z | 1 + ε < re z}`.
  set ε : ℝ := (s.re - 1) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hs' : 1 + ε < s.re := by
    dsimp [ε]
    linarith
  have hopen : IsOpen {z : ℂ | 1 + ε < z.re} := isOpen_lt continuous_const continuous_re
  have hcontOn : ContinuousOn (primeLogSeries (N := N) χ) {z : ℂ | 1 + ε < z.re} :=
    continuousOn_primeLogSeries_halfPlane (N := N) (χ := χ) hε
  exact hcontOn.continuousAt (hopen.mem_nhds hs')

private lemma eq_of_exp_eq_exp_of_norm_sub_lt_pi {x y : ℂ}
    (hxy : Complex.exp x = Complex.exp y) (hπ : ‖x - y‖ < Real.pi) : x = y := by
  rcases (Complex.exp_eq_exp_iff_exists_int).1 hxy with ⟨n, hn⟩
  -- `x - y = n * (2πi)`, so the norm bound forces `n = 0`.
  have hsub : x - y = n * (2 * Real.pi * Complex.I) := by
    have hn' : x = (n * (2 * Real.pi * Complex.I)) + y := by
      simpa [add_comm, add_left_comm, add_assoc] using hn
    exact (sub_eq_iff_eq_add).2 hn'
  by_cases hn0 : n = 0
  · simpa [hn0] using hn
  · have hnabs : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      -- `‖(n : ℂ)‖ = ‖n‖ = |(n : ℝ)| ≥ 1`
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      have hR : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℝ) ≤ (|n| : ℝ) := by exact_mod_cast this
        simpa [Int.cast_abs] using this
      have : (1 : ℝ) ≤ ‖(n : ℤ)‖ := by simpa [Int.norm_eq_abs] using hR
      simpa [norm_intCast] using this
    have hnorm2pi : ‖(2 * Real.pi * (Complex.I : ℂ))‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le, mul_assoc]
    have hge : Real.pi ≤ ‖n * (2 * Real.pi * Complex.I : ℂ)‖ := by
      -- `‖n * (2πi)‖ = ‖n‖ * 2π ≥ 1 * 2π ≥ π`
      calc
        Real.pi ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
        _ ≤ ‖(n : ℂ)‖ * (2 * Real.pi) := by
              -- multiply `hnabs : 1 ≤ ‖n‖` by the positive constant `2π`
              have hpos : (0 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
              have := mul_le_mul_of_nonneg_right hnabs hpos
              simpa [one_mul] using this
        _ = ‖(n : ℂ)‖ * ‖(2 * Real.pi * (Complex.I : ℂ))‖ := by
              -- multiply the identity `‖2πi‖ = 2π` without cancellation
              simpa using congrArg (fun r : ℝ => ‖(n : ℂ)‖ * r) hnorm2pi.symm
        _ = ‖(n : ℂ) * (2 * Real.pi * (Complex.I : ℂ))‖ := (norm_mul _ _).symm
        _ = ‖n * (2 * Real.pi * (Complex.I : ℂ))‖ := by simp
    have : False := (not_lt_of_ge (by simpa [hsub] using hge)) hπ
    exact this.elim

private lemma mem_rect_of_one_lt_lt {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht1 : 1 < t)
    (ht2 : t < 1 + δ) : (t : ℂ) ∈ rect δ := by
  -- `t` real implies `im = 0`, and inequalities are immediate.
  have ht0 : (-(δ : ℝ)) < (0 : ℝ) := by linarith
  have ht0' : (0 : ℝ) < δ := hδ
  have hlow : (1 - δ) < t := by linarith
  simp [rect, hlow, ht2, ht0, ht0']

theorem bounded_primeLogSeries_near_one (χ : _root_.DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ M : ℝ,
      (fun s : ℝ ↦ ‖primeLogSeries (N := N) χ (s : ℂ)‖) ≤ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        fun _ ↦ M := by
  -- Get a holomorphic logarithm `g` on a small rectangle around `1`.
  rcases exists_log_LFunction_on_rect (N := N) χ hχ with ⟨δ, hδ, g, hg, hexp⟩
  -- Work on the open interval `I = (1, 1 + δ/2)`.
  set I : Set ℝ := Set.Ioo 1 (1 + δ / 2)
  have hδ2 : 0 < δ / 2 := by nlinarith
  have hI_mem : I ∈ nhdsWithin 1 (Set.Ioi 1) := by
    -- `I` is a basic member of the right-neighborhood filter at `1`.
    simpa [I, nhdsWithin] using (Ioo_mem_nhdsGT (a := (1 : ℝ)) (b := (1 + δ / 2 : ℝ)) (by linarith))
  have hIpre : IsPreconnected I := isPreconnected_Ioo
  -- Define `F = primeLogSeries - g` on the subtype `I`.
  let F : I → ℂ := fun t ↦ primeLogSeries (N := N) χ (t.1 : ℂ) - g (t.1 : ℂ)
  have hExpF : ∀ t : I, Complex.exp (F t) = 1 := by
    intro t
    have ht1 : (1 : ℝ) < t.1 := t.2.1
    have ht2 : t.1 < 1 + δ := by
      have : t.1 < 1 + δ / 2 := t.2.2
      linarith
    have htrect : (t.1 : ℂ) ∈ rect δ := mem_rect_of_one_lt_lt (δ := δ) hδ ht1 ht2
    have hA : Complex.exp (primeLogSeries (N := N) χ (t.1 : ℂ)) =
        _root_.DirichletCharacter.LFunction χ (t.1 : ℂ) :=
      exp_primeLogSeries_eq_LFunction (N := N) χ (hs := by simpa using ht1)
    have hB : Complex.exp (g (t.1 : ℂ)) =
        _root_.DirichletCharacter.LFunction χ (t.1 : ℂ) :=
      hexp (t.1 : ℂ) htrect
    have hne : _root_.DirichletCharacter.LFunction χ (t.1 : ℂ) ≠ 0 := by
      -- `exp (g z)` is never zero.
      have : Complex.exp (g (t.1 : ℂ)) ≠ 0 := Complex.exp_ne_zero _
      simpa [hB] using this
    calc
      Complex.exp (F t) = Complex.exp (primeLogSeries (N := N) χ (t.1 : ℂ)) /
          Complex.exp (g (t.1 : ℂ)) := by simp [F, Complex.exp_sub]
      _ = _root_.DirichletCharacter.LFunction χ (t.1 : ℂ) /
          _root_.DirichletCharacter.LFunction χ (t.1 : ℂ) := by simp [hA, hB]
      _ = 1 := by simp [hne]
  have hF_loc : IsLocallyConstant F := by
    -- Show eventual equality at each point using continuity + the `π` injectivity radius for `exp`.
    refine (IsLocallyConstant.iff_eventually_eq (f := F)).2 (fun t0 => ?_)
    have ht0 : (1 : ℝ) < t0.1 := t0.2.1
    have ht0' : t0.1 < 1 + δ := by
      have : t0.1 < 1 + δ / 2 := t0.2.2
      linarith
    have ht0rect : (t0.1 : ℂ) ∈ rect δ := mem_rect_of_one_lt_lt (δ := δ) hδ ht0 ht0'
    have hcontAt : ContinuousAt F t0 := by
      -- continuity of `primeLogSeries` at `t0`, and continuity of `g` on `rect δ`.
      have hH : ContinuousAt (fun z : ℂ ↦ primeLogSeries (N := N) χ z) (t0.1 : ℂ) :=
        continuousAt_primeLogSeries (N := N) (χ := χ) (s := (t0.1 : ℂ)) (by simpa using ht0)
      have hG : ContinuousAt g (t0.1 : ℂ) := by
        have hx : rect δ ∈ 𝓝 (t0.1 : ℂ) := (isOpen_rect δ).mem_nhds ht0rect
        exact (hg.continuousOn.continuousAt hx)
      have hval : ContinuousAt (fun t : I ↦ (t.1 : ℂ)) t0 :=
        (Complex.continuous_ofReal.continuousAt).comp continuous_subtype_val.continuousAt
      have hH' : ContinuousAt (fun t : I ↦ primeLogSeries (N := N) χ (t.1 : ℂ)) t0 := by
        -- unfold `ContinuousAt` and use `Tendsto.comp`
        simpa using (hH.tendsto.comp hval.tendsto)
      have hG' : ContinuousAt (fun t : I ↦ g (t.1 : ℂ)) t0 := by
        simpa using (hG.tendsto.comp hval.tendsto)
      simpa [F, sub_eq_add_neg] using hH'.sub hG'
    have hball :
        {t : I | ‖F t - F t0‖ < Real.pi} ∈ 𝓝 t0 := by
      have : Metric.ball (F t0) Real.pi ∈ 𝓝 (F t0) :=
        Metric.ball_mem_nhds (x := F t0) Real.pi_pos
      have : {t : I | F t ∈ Metric.ball (F t0) Real.pi} ∈ 𝓝 t0 :=
        hcontAt.preimage_mem_nhds this
      simpa [Metric.mem_ball, dist_eq_norm] using this
    have hball' : ∀ᶠ t in 𝓝 t0, ‖F t - F t0‖ < Real.pi := hball
    refine hball'.mono ?_
    intro t ht
    -- Both exponentials are `1`, so `exp (F t) = exp (F t0)`, and the norm bound forces equality.
    have hExp : Complex.exp (F t) = Complex.exp (F t0) := by simp [hExpF t, hExpF t0]
    have : F t = F t0 := eq_of_exp_eq_exp_of_norm_sub_lt_pi hExp (by simpa [sub_eq_add_neg] using ht)
    simp [this]
  -- On the preconnected subtype `I`, a locally constant function is constant.
  haveI : PreconnectedSpace I := Subtype.preconnectedSpace hIpre
  -- `I` is nonempty since `δ > 0`.
  have hInonempty : I.Nonempty := by
    refine ⟨1 + δ / 4, ?_⟩
    have hδ4 : 0 < δ / 4 := by nlinarith
    constructor
    · linarith [hδ4]
    · have : δ / 4 < δ / 2 := by nlinarith
      linarith
  classical
  -- pick a basepoint and constant value `C`.
  let t0 : I := ⟨(hInonempty.choose), hInonempty.choose_spec⟩
  let C : ℂ := F t0
  have hC : ∀ t : I, F t = C := by
    intro t
    simpa [C] using (hF_loc.apply_eq_of_preconnectedSpace t t0)
  -- Bound `g` on the compact interval `K = [1, 1+δ/2]`, hence also on `I`.
  set K : Set ℝ := Set.Icc 1 (1 + δ / 2)
  have hKcompact : IsCompact K := isCompact_Icc
  have hcontK : ContinuousOn (fun x : ℝ ↦ g (x : ℂ)) K := by
    intro x hx
    have hxrect : (x : ℂ) ∈ rect δ := by
      have hx2 : x < 1 + δ := by
        have : x ≤ 1 + δ / 2 := hx.2
        linarith
      have hx1 : (1 - δ) < x := by
        have : (1 : ℝ) ≤ x := hx.1
        linarith
      have hxim : (-(δ : ℝ)) < (0 : ℝ) := by linarith
      have hxim' : (0 : ℝ) < δ := hδ
      simp [rect, hx1, hx2, hxim, hxim']
    have hxnhds : rect δ ∈ 𝓝 (x : ℂ) := (isOpen_rect δ).mem_nhds hxrect
    have hG : ContinuousAt g (x : ℂ) := (hg.continuousOn.continuousAt hxnhds)
    have hf : ContinuousWithinAt (fun r : ℝ ↦ (r : ℂ)) K x :=
      (Complex.continuous_ofReal.continuousAt).continuousWithinAt
    exact hG.comp_continuousWithinAt hf
  have hbdd : Bornology.IsBounded ((fun x : ℝ ↦ g (x : ℂ)) '' K) :=
    (hKcompact.image_of_continuousOn hcontK).isBounded
  rcases ((Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hbdd) with ⟨R, hR⟩
  -- Final bound on `primeLogSeries` on `I`, hence eventually near `1⁺`.
  refine ⟨R + ‖C‖, ?_⟩
  have hEv : (∀ᶠ s in nhdsWithin 1 (Set.Ioi 1), s ∈ I) := hI_mem
  refine hEv.mono ?_
  intro s hsI
  have hsK : s ∈ K := by
    constructor
    · exact le_of_lt hsI.1
    · exact le_of_lt hsI.2
  have hgs : ‖g (s : ℂ)‖ ≤ R := by
    have : g (s : ℂ) ∈ Metric.closedBall (0 : ℂ) R := hR ⟨s, hsK, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hEq : primeLogSeries (N := N) χ (s : ℂ) = g (s : ℂ) + C := by
    have hF : primeLogSeries (N := N) χ (s : ℂ) - g (s : ℂ) = C := by
      simpa [F] using (hC ⟨s, hsI⟩)
    have : primeLogSeries (N := N) χ (s : ℂ) = C + g (s : ℂ) := (sub_eq_iff_eq_add).1 hF
    simpa [add_comm, add_left_comm, add_assoc] using this
  calc
    ‖primeLogSeries (N := N) χ (s : ℂ)‖ = ‖g (s : ℂ) + C‖ := by simp [hEq]
    _ ≤ ‖g (s : ℂ)‖ + ‖C‖ := norm_add_le _ _
    _ ≤ R + ‖C‖ := by gcongr

end BoundedNearOne

end DirichletCharacterPrime

end Chebotarev

end PrimeNumberTheoremAnd
