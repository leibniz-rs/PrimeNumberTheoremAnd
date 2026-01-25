import PrimeNumberTheoremAnd.ChebotarevDirichletCharacterPrimeSumBound
import PrimeNumberTheoremAnd.ChebotarevPrimeSeriesSummable

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
## Boundedness of `∑' p, χ p / p^s` near `s = 1⁺`

This file upgrades the boundedness of the *prime-log* series (proved in
`ChebotarevDirichletCharacterPrimeSumBound`) to boundedness of the *prime* series
`∑' p, χ p / p^s`, using the Taylor bound for `log (1+z) - z` and summability of `∑ p⁻²`.
-/

namespace PrimeNumberTheoremAnd

open scoped Classical Real Topology

open Filter Complex

namespace Chebotarev.DirichletCharacterPrime

open Nat.Primes

variable {N : ℕ} [NeZero N]

private lemma norm_dirichletSummand_le_half (χ : _root_.DirichletCharacter ℂ N) {s : ℝ} (hs : 1 < s)
    (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-(s : ℂ))‖ ≤ (1 / 2 : ℝ) := by
  -- `‖χ p‖ ≤ 1` and `‖p^{-s}‖ = p^{-s}`, and `p ≥ 2`.
  have hchi : ‖χ p‖ ≤ (1 : ℝ) := by simpa using (_root_.DirichletCharacter.norm_le_one (χ := χ) p)
  have hspos : 0 < s := by linarith
  have hnere : (s : ℂ).re ≠ 0 := by
    simpa using (ne_of_gt hspos)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hnorm_pows : ‖(p : ℂ) ^ (-(s : ℂ))‖ = (p : ℝ) ^ (-s) := by
    -- `‖p^(-s)‖ = p^(-re s)` and `re(s)=s`.
    have hne' : (-(s : ℂ)).re ≠ 0 := by simpa using hnere
    calc
      ‖(p : ℂ) ^ (-(s : ℂ))‖ = (p : ℝ) ^ ((-(s : ℂ)).re) := by
        simp [norm_natCast_cpow_of_re_ne_zero _ hne']
      _ = (p : ℝ) ^ (-s) := by simp
  have hpow_le : (p : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (2 : ℝ)) hp2 (by linarith)
  have hpow_lt : (2 : ℝ) ^ (-s) < (1 / 2 : ℝ) := by
    have : (-s : ℝ) < (-1 : ℝ) := by linarith
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) this
    simpa [Real.rpow_neg, Real.rpow_one] using this
  calc
    ‖χ p * (p : ℂ) ^ (-(s : ℂ))‖ = ‖χ p‖ * ‖(p : ℂ) ^ (-(s : ℂ))‖ := by simp
    _ ≤ 1 * ‖(p : ℂ) ^ (-(s : ℂ))‖ := by gcongr
    _ = (p : ℝ) ^ (-s) := by simp [hnorm_pows]
    _ ≤ (2 : ℝ) ^ (-s) := hpow_le
    _ ≤ (1 / 2 : ℝ) := le_of_lt hpow_lt

private lemma norm_log_term_sub_self_le_sq {w : ℂ} (hw : ‖w‖ ≤ (1 / 2 : ℝ)) :
    ‖-Complex.log (1 - w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hw' : ‖-w‖ < (1 : ℝ) :=
    (lt_of_le_of_lt (by simpa [norm_neg] using hw) one_half_lt_one)
  have h := Complex.norm_log_one_add_sub_self_le (z := -w) hw'
  -- turn the RHS into `‖w‖^2` using `‖w‖ ≤ 1/2`
  have hle : ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - ‖-w‖ := by
      have : ‖-w‖ ≤ (1 / 2 : ℝ) := by simpa [norm_neg] using hw
      linarith
    have hinv : (1 - ‖-w‖)⁻¹ ≤ (2 : ℝ) := by
      -- `1 / (1 - ‖-w‖) ≤ 1 / (1/2) = 2`
      have ha : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      have : (1 : ℝ) / (1 - ‖-w‖) ≤ (1 : ℝ) / (1 / 2 : ℝ) :=
        one_div_le_one_div_of_le ha hhalf
      simpa [one_div] using this
    have hfac : (1 - ‖-w‖)⁻¹ / 2 ≤ (1 : ℝ) := by
      have : (1 - ‖-w‖)⁻¹ / 2 ≤ (2 : ℝ) / 2 := div_le_div_of_nonneg_right hinv (by positivity)
      simpa using this
    calc
      ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 = ‖-w‖ ^ 2 * ((1 - ‖-w‖)⁻¹ / 2) := by ring
      _ ≤ ‖-w‖ ^ 2 * 1 := by gcongr
      _ = ‖w‖ ^ 2 := by simp [norm_neg]
  have h' : ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
    -- rewrite the left side into the form `log(1+z) - z`.
    have : ‖Complex.log (1 + (-w)) - (-w)‖ ≤ ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 := h
    have : ‖Complex.log (1 - w) + w‖ ≤ ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    exact this.trans hle
  -- finish
  have h'' : ‖-Complex.log (1 - w) - w‖ = ‖Complex.log (1 - w) + w‖ := by
    have hswap : ‖-Complex.log (1 - w) - w‖ = ‖-w + -Complex.log (1 - w)‖ := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hw' : -w + -Complex.log (1 - w) = -(Complex.log (1 - w) + w) := by ring
    calc
      ‖-Complex.log (1 - w) - w‖ = ‖-w + -Complex.log (1 - w)‖ := hswap
      _ = ‖-(Complex.log (1 - w) + w)‖ := by
            simpa using congrArg (fun z : ℂ => ‖z‖) hw'
      _ = ‖Complex.log (1 - w) + w‖ := by
            simpa using (norm_neg (Complex.log (1 - w) + w))
  simpa [h''] using h'

end Chebotarev.DirichletCharacterPrime

end PrimeNumberTheoremAnd
