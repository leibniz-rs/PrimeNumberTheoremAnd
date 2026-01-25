import PrimeNumberTheoremAnd.ChebotarevDirichletDensityTsumPrimes
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
## Divergence of `seriesAll` near `s = 1`

To apply the Dirichlet-density limit criterion, we need that the denominator `seriesAll s`
blows up as `s → 1⁺`.

We prove this in a way that is robust and avoids misformalization:

- use `Nat.Primes.not_summable_one_div` to get arbitrarily large *finite* prime sums `∑ 1/p`;
- by continuity of `p ↦ p^{-s}` in `s`, the corresponding finite sum `∑ 1/p^s` is still large for
  `s` close to `1`;
- since `s > 1` implies summability of `∑ 1/p^s`, each finite sum is bounded above by the `tsum`.

Finally we transfer this to the complex-valued denominator `seriesAll s` (and its norm) using that
for `s > 1` the term `1 / (p : ℂ)^(s : ℂ)` is real and equals `(1 / (p : ℝ)^s : ℂ)`.
-/

namespace PrimeNumberTheoremAnd
namespace DirichletDensity

open scoped Classical Topology

open Filter

open Nat.Primes

open Complex

noncomputable def seriesAllReal (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (1 : ℝ) / ((p : ℝ) ^ s)

lemma seriesAllReal_nonneg (s : ℝ) : 0 ≤ seriesAllReal s := by
  refine tsum_nonneg ?_
  intro p
  have : 0 ≤ ((p : ℝ) ^ s) := by positivity
  positivity

lemma summable_seriesAllReal {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ (1 : ℝ) / ((p : ℝ) ^ s)) := by
  -- rewrite as `p ^ (-s)` and use `Nat.Primes.summable_rpow`
  have : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)) :=
    (Nat.Primes.summable_rpow (r := (-s : ℝ))).2 (by linarith)
  simpa [one_div, Real.rpow_neg] using this

lemma exists_finset_primes_sum_one_div_gt (M : ℝ) :
    ∃ u : Finset Nat.Primes, M < ∑ p ∈ u, (1 : ℝ) / (p : ℝ) := by
  classical
  -- If all finite sums were bounded by `M`, then the series would be summable, contradiction.
  by_contra h
  have h' : ∀ u : Finset Nat.Primes, ∑ p ∈ u, (1 : ℝ) / (p : ℝ) ≤ M := by
    intro u
    have : ¬ M < ∑ p ∈ u, (1 : ℝ) / (p : ℝ) := by
      intro hm
      exact h ⟨u, hm⟩
    exact le_of_not_gt this
  have hsum : Summable (fun p : Nat.Primes ↦ (1 : ℝ) / (p : ℝ)) := by
    refine summable_of_sum_le (ι := Nat.Primes)
      (f := fun p : Nat.Primes ↦ (1 : ℝ) / (p : ℝ)) (c := M) ?_ h'
    intro p
    positivity
  exact Nat.Primes.not_summable_one_div hsum

lemma tendsto_seriesAllReal_atTop :
    Tendsto seriesAllReal (nhdsWithin 1 (Set.Ioi 1)) atTop := by
  -- We show: for any `M`, eventually `M ≤ seriesAllReal s`.
  refine Filter.tendsto_atTop.2 ?_
  intro M
  by_cases hM0 : M ≤ 0
  · refine Filter.Eventually.of_forall fun s ↦ hM0.trans (seriesAllReal_nonneg s)
  -- Choose a finite prime set with `∑ 1/p > 2M`.
  have hMpos : 0 < M := lt_of_not_ge hM0
  obtain ⟨u, hu⟩ := exists_finset_primes_sum_one_div_gt (2 * M)
  -- For each `p ∈ u`, `s ↦ 1/p^s` tends to `1/p` at `s = 1`.
  have hterm (p : Nat.Primes) :
      Tendsto (fun s : ℝ ↦ (1 : ℝ) / ((p : ℝ) ^ s)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((1 : ℝ) / (p : ℝ))) := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hcont : ContinuousAt (fun s : ℝ ↦ (p : ℝ) ^ s) 1 :=
      Real.continuousAt_const_rpow (a := (p : ℝ)) (b := 1) hp0
    have hcont' : ContinuousAt (fun s : ℝ ↦ ((p : ℝ) ^ s)⁻¹) 1 :=
      hcont.inv₀ (by simpa [Real.rpow_one] using hp0)
    simpa [seriesAllReal, one_div, Real.rpow_one] using (hcont'.tendsto.mono_left nhdsWithin_le_nhds)
  -- Build an eventual lower bound on all terms for `p ∈ u`.
  have hforall :
      ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
        ∀ p ∈ u, (1 / 2 : ℝ) * ((1 : ℝ) / (p : ℝ)) < (1 : ℝ) / ((p : ℝ) ^ s) := by
    classical
    -- finite intersection over `u`
    refine u.induction_on ?h0 ?hstep
    · simp
    · intro p u hpnotmem ih
      have hpI :
          ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
            (1 / 2 : ℝ) * ((1 : ℝ) / (p : ℝ)) < (1 : ℝ) / ((p : ℝ) ^ s) := by
        have hp_pos : 0 < (1 : ℝ) / (p : ℝ) := by
          have : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
          positivity
        have hmem : Set.Ioi ((1 / 2 : ℝ) * ((1 : ℝ) / (p : ℝ))) ∈
            𝓝 ((1 : ℝ) / (p : ℝ)) := by
          exact Ioi_mem_nhds (by nlinarith)
        exact (hterm p).eventually hmem
      filter_upwards [ih, hpI] with s hs hup
      intro q hq
      by_cases hqp : q = p
      · subst hqp; simpa using hup
      · have : q ∈ u := by
          simpa [Finset.mem_insert, hqp] using hq
        exact hs q this
  -- Along `nhdsWithin 1 (Ioi 1)` we are eventually in `Ioi 1`, hence `1 < s`.
  have hs_gt : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1), 1 < s := by
    simpa [Set.mem_Ioi] using (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin 1 (Set.Ioi 1))
  -- Put everything together.
  filter_upwards [hforall, hs_gt] with s hsall hs1
  set f : Nat.Primes → ℝ := fun p ↦ (1 : ℝ) / ((p : ℝ) ^ s)
  have hf_summable : Summable f := summable_seriesAllReal (s := s) hs1
  -- Lower bound the finite sum over `u` by `(1/2) * ∑ 1/p`.
  have hfin_lower :
      (1 / 2 : ℝ) * (∑ p ∈ u, (1 : ℝ) / (p : ℝ)) ≤ ∑ p ∈ u, f p := by
    have : (1 / 2 : ℝ) * (∑ p ∈ u, (1 : ℝ) / (p : ℝ)) =
        ∑ p ∈ u, (1 / 2 : ℝ) * ((1 : ℝ) / (p : ℝ)) := by
      simp [Finset.mul_sum]
    refine this ▸ Finset.sum_le_sum ?_
    intro p hp
    exact le_of_lt (hsall p hp)
  -- From `2M < ∑ 1/p` we get `M < (1/2) * ∑ 1/p`.
  have hMlt : M < (1 / 2 : ℝ) * (∑ p ∈ u, (1 : ℝ) / (p : ℝ)) := by
    have hmul : (1 / 2 : ℝ) * (2 * M) < (1 / 2 : ℝ) * (∑ p ∈ u, (1 : ℝ) / (p : ℝ)) := by
      have : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
      exact mul_lt_mul_of_pos_left hu this
    -- simplify the LHS `(1/2) * (2*M)` to `M`
    simpa [mul_assoc] using hmul
  have hfinM : M < ∑ p ∈ u, f p := lt_of_lt_of_le hMlt hfin_lower
  -- finite sum ≤ `tsum` since `f` is nonnegative and summable
  have hsum_le : ∑ p ∈ u, f p ≤ ∑' p : Nat.Primes, f p := by
    refine Summable.sum_le_tsum u (fun p _ ↦ ?_) hf_summable
    have : 0 ≤ (p : ℝ) ^ s := by positivity
    positivity
  have : M < ∑' p : Nat.Primes, f p := lt_of_lt_of_le hfinM hsum_le
  exact le_of_lt (by simpa [seriesAllReal, f] using this)

lemma seriesAll_eq_ofReal_seriesAllReal {s : ℝ} (hs : 1 < s) :
    seriesAll s = (seriesAllReal s : ℂ) := by
  have h := seriesAll_eq_tsum_primes (s := s) hs
  have hterm (p : Nat.Primes) :
      (1 : ℂ) / Complex.cpow (p : ℂ) (Complex.ofReal s) =
        ((Real.exp (Real.log (p : ℝ) * s))⁻¹ : ℂ) := by
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    have hp0c : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
      have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.zero_le p.1)
      -- `Complex.ofReal_log` gives `(Real.log p : ℂ) = log p`.
      simp [Complex.ofReal_log (x := (p : ℝ)) hp_nonneg]
    calc
      (1 : ℂ) / Complex.cpow (p : ℂ) (Complex.ofReal s)
          = (Complex.cpow (p : ℂ) (Complex.ofReal s))⁻¹ := by simp [one_div]
      _ = (Complex.exp (Complex.log (p : ℂ) * Complex.ofReal s))⁻¹ := by
            -- `cpow` is `exp (log x * y)` when `x ≠ 0`
            simp [Complex.cpow, hp0c]
      _ = (Complex.exp ((Real.log (p : ℝ) : ℂ) * Complex.ofReal s))⁻¹ := by
            rw [hlog]
      _ = (Complex.exp ((Real.log (p : ℝ) * s : ℝ) : ℂ))⁻¹ := by simp [Complex.ofReal_mul]
      _ = ((Real.exp (Real.log (p : ℝ) * s) : ℂ))⁻¹ := by
            -- `exp (t : ℂ) = (Real.exp t : ℂ)` for real `t`
            simp [Complex.ofReal_exp]
      _ = ((Real.exp (Real.log (p : ℝ) * s))⁻¹ : ℂ) := by simp
  refine h.trans ?_
  calc
    (∑' p : Nat.Primes, (1 : ℂ) / ((p : ℂ) ^ (s : ℂ)))
        = ∑' p : Nat.Primes, (1 : ℂ) / Complex.cpow (p : ℂ) (Complex.ofReal s) := by
            refine tsum_congr ?_
            intro p
            rfl
    _ = ∑' p : Nat.Primes, ((Real.exp (Real.log (p : ℝ) * s))⁻¹ : ℂ) := by
            exact tsum_congr hterm
    _ = (seriesAllReal s : ℂ) := by
          -- First rewrite `seriesAllReal` in terms of `exp (log p * s)`.
          have hrew : seriesAllReal s = ∑' p : Nat.Primes, (Real.exp (Real.log (p : ℝ) * s))⁻¹ := by
            classical
            -- pointwise rewrite `1 / p^s`
            have : (fun p : Nat.Primes ↦ (1 : ℝ) / ((p : ℝ) ^ s)) =
                fun p : Nat.Primes ↦ (Real.exp (Real.log (p : ℝ) * s))⁻¹ := by
              funext p
              have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
              have : (p : ℝ) ^ s = Real.exp (Real.log (p : ℝ) * s) := by
                simp [Real.rpow_def_of_pos hp_pos, mul_comm]
              simp [one_div, this]
            -- transport pointwise equality across `tsum`
            simpa [seriesAllReal] using congrArg (fun f ↦ ∑' p : Nat.Primes, f p) this
          -- Now use `ofReal_tsum`.
          have hofReal :
              (∑' p : Nat.Primes, ((Real.exp (Real.log (p : ℝ) * s))⁻¹ : ℂ)) =
                (↑(∑' p : Nat.Primes, (Real.exp (Real.log (p : ℝ) * s))⁻¹) : ℂ) := by
            simpa using
              (Complex.ofReal_tsum (f := fun p : Nat.Primes ↦ (Real.exp (Real.log (p : ℝ) * s))⁻¹)).symm
          -- finish
          calc
            (∑' p : Nat.Primes, ((Real.exp (Real.log (p : ℝ) * s))⁻¹ : ℂ))
                = (↑(∑' p : Nat.Primes, (Real.exp (Real.log (p : ℝ) * s))⁻¹) : ℂ) := hofReal
            _ = (seriesAllReal s : ℂ) := by simp [hrew]

theorem tendsto_norm_seriesAll_atTop :
    Tendsto (fun s : ℝ ↦ ‖seriesAll s‖) (nhdsWithin 1 (Set.Ioi 1)) atTop := by
  have hs_gt : ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1), 1 < s := by
    simpa [Set.mem_Ioi] using (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin 1 (Set.Ioi 1))
  have hEv :
      (fun s : ℝ ↦ ‖seriesAll s‖) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] fun s ↦ seriesAllReal s := by
    filter_upwards [hs_gt] with s hs
    have hn : 0 ≤ seriesAllReal s := seriesAllReal_nonneg s
    -- rewrite `seriesAll` as `ofReal (seriesAllReal s)`
    have h := seriesAll_eq_ofReal_seriesAllReal (s := s) hs
    calc
      ‖seriesAll s‖ = ‖(seriesAllReal s : ℂ)‖ := by simp [h]
      _ = seriesAllReal s := Complex.norm_of_nonneg hn
  exact (tendsto_seriesAllReal_atTop.congr' hEv.symm)

end DirichletDensity
end PrimeNumberTheoremAnd
