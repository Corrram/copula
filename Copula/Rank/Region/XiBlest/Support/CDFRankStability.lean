import Copula.Rank.Region.XiBlest.Support.PermutationApproximation
import Copula.Rank.SpearmanCDF

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem integral_sub_abs_le_uniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (ε : ℝ) (h : ∀ x, |f x-g x| ≤ ε) : |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)| ≤ ε := by
  rw [← integral_sub hf hg]
  calc
    _ ≤ ∫ x, |f x-g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω, ε ∂μ := integral_mono (hf.sub hg).abs (integrable_const ε) h
    _ = ε := by simp

theorem spearmanRho_cdf_stability (C D : Copula 2) (ε : ℝ)
    (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε) :
    |C.spearmanRho-D.spearmanRho| ≤ 12*ε := by
  have hb := integral_sub_abs_le_uniform (independence 2).toMeasure C.cdf D.cdf
    (Copula.integrable_continuous_cube _ C.continuous_cdf) (Copula.integrable_continuous_cube _ D.continuous_cdf) ε
    (fun x => by have he : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
                 rw [he]; exact h _ _)
  rw [C.spearmanRho_eq_integral_cdf,D.spearmanRho_eq_integral_cdf]
  rw [show 12*(∫ x, C.cdf x ∂(independence 2).toMeasure)-3-(12*(∫ x, D.cdf x ∂(independence 2).toMeasure)-3)=
    12*((∫ x, C.cdf x ∂(independence 2).toMeasure)-(∫ x, D.cdf x ∂(independence 2).toMeasure)) by ring,
    abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<12)]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

theorem spearmanFootrule_cdf_stability (C D : Copula 2) (ε : ℝ)
    (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε) :
    |C.spearmanFootrule-D.spearmanFootrule| ≤ 6*ε := by
  have hb := integral_sub_abs_le_uniform volume (fun t => C.cdf ![t,t]) (fun t => D.cdf ![t,t])
    C.integrable_diagonal_cdf D.integrable_diagonal_cdf ε (fun t => h t t)
  unfold Copula.spearmanFootrule
  rw [show 6*(∫ t : I, C.cdf ![t,t])-2-(6*(∫ t : I, D.cdf ![t,t])-2)=
    6*((∫ t : I, C.cdf ![t,t])-(∫ t : I, D.cdf ![t,t])) by ring,
    abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<6)]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

theorem empiricalCDFRadius_tendsto : Tendsto empiricalCDFRadius atTop (𝓝 0) := by
  apply squeeze_zero empiricalCDFRadius_nonneg (fun n => ?_) empiricalCDFRadius_scaled_tendsto
  have hR : 1 ≤ ((n : ℝ)+2)^(1/3 : ℝ) := Real.one_le_rpow (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num)
  nlinarith [empiricalCDFRadius_nonneg n]

theorem permutationApproximationRate_tendsto :
    Tendsto (fun n : ℕ => 3*empiricalCDFRadius n+10/((n : ℝ)+1)) atTop (𝓝 0) := by
  convert (empiricalCDFRadius_tendsto.const_mul 3).add
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 10) using 1 <;> simp [div_eq_mul_inv]

/-- Equal-width permutation shuffles approximate both rank coefficients of every copula. -/
theorem exists_permutationShuffle_rank_limits (C : Copula 2) :
    ∃ π : (n : ℕ) → Equiv.Perm (Fin (n+1)),
      Tendsto (fun n => (PermutationShuffle.copula n (π n)).spearmanRho) atTop (𝓝 C.spearmanRho) ∧
      Tendsto (fun n => (PermutationShuffle.copula n (π n)).spearmanFootrule) atTop (𝓝 C.spearmanFootrule) := by
  obtain ⟨π,hπ⟩ := exists_permutationShuffle_approximation C
  refine ⟨π,?_,?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_
      (show Tendsto (fun n : ℕ => 12*(3*empiricalCDFRadius n+10/((n : ℝ)+1))) atTop (𝓝 0) by
        simpa using permutationApproximationRate_tendsto.const_mul 12)
    filter_upwards [hπ] with n hn
    exact spearmanRho_cdf_stability _ _ _ hn
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_
      (show Tendsto (fun n : ℕ => 6*(3*empiricalCDFRadius n+10/((n : ℝ)+1))) atTop (𝓝 0) by
        simpa using permutationApproximationRate_tendsto.const_mul 6)
    filter_upwards [hπ] with n hn
    exact spearmanFootrule_cdf_stability _ _ _ hn

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
