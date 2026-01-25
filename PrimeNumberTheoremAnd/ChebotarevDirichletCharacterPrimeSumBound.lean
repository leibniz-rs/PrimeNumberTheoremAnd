import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HolomorphicLog

import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

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
The rest of the argument (holomorphic log on a small rectangle around `1`, local constancy of
`primeLogSeries - log`, and the Taylor error estimate to control `primeSeries`) is developed in the
next commits; we keep the file compiling throughout, with no placeholders.
-/

end DirichletCharacterPrime

end Chebotarev

end PrimeNumberTheoremAnd
