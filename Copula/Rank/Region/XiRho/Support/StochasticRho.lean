import Copula.Rank.Region.XiRho.Support.StochasticBounds

/-! # Spearman rho dominates xi under stochastic monotonicity

The scalar estimate compares squared differences with absolute differences
of an antitone function taking values in [0,1].
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

private theorem integrable_lower_kernel {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    Integrable (fun p : I × I => if p.2 ≤ p.1 then g p.2 else 0)
      ((volume : Measure I).prod volume) := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((hg.comp measurable_snd).ite (measurableSet_le measurable_snd measurable_fst)
      measurable_const).aestronglyMeasurable
  · split_ifs
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (hb p.2).1] using (hb p.2).2
    · norm_num

theorem integral_lower_integral {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, ∫ w in Iic u, g w) = ∫ w : I, (1 - (w : ℝ)) * g w := by
  classical
  calc
    _ = ∫ u : I, ∫ w : I, if w ≤ u then g w else 0 := by
      simp_rw [← integral_indicator measurableSet_Iic]
      rfl
    _ = ∫ w : I, ∫ u : I, if w ≤ u then g w else 0 :=
      integral_integral_swap (integrable_lower_kernel hg hb)
    _ = _ := by
      congr 1
      funext w
      have he : (fun u : I => if w ≤ u then g w else 0) =
          fun u : I => (if w ≤ u then (1 : ℝ) else 0) * g w := by
        funext u; split_ifs <;> simp
      rw [he, integral_mul_const, Copula.integral_unit_upper_indicator]

theorem integrable_lower_integral {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) : Integrable (fun u : I => ∫ w in Iic u, g w) := by
  have h := (integrable_lower_kernel hg hb).integral_prod_left
  simpa only [← integral_indicator measurableSet_Iic, indicator, mem_Iic] using h

theorem integral_abs_sub_of_antitone {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) (u : I) :
    (∫ w : I, |g u - g w|) =
      2 * (∫ w in Iic u, g w) - (∫ w : I, g w) + g u - 2 * (u : ℝ) * g u := by
  classical
  have hi := integrable_unit_bounded hg.measurable hb
  let e : I → ℝ := (Iic u).indicator (fun _ => 1)
  let f : I → ℝ := (Iic u).indicator g
  have he : Integrable e := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hf : Integrable f := hi.indicator measurableSet_Iic
  have hid : (fun w : I => |g u - g w|) =
      fun w => 2 * f w - g w + g u - (2 * g u) * e w := by
    funext w
    by_cases hw : w ≤ u
    · simp only [e, f, indicator_of_mem (mem_Iic.mpr hw),
        abs_of_nonpos (sub_nonpos.mpr (hg hw))]
      ring
    · simp only [e, f, indicator_of_notMem (show w ∉ Iic u from hw),
        abs_of_nonneg (sub_nonneg.mpr (hg (le_of_not_ge hw)))]
      ring
  have hsub : Integrable (fun w => 2 * f w - g w) := (hf.const_mul 2).sub hi
  have hadd : Integrable (fun w => 2 * f w - g w + g u) := hsub.add (integrable_const _)
  rw [hid, integral_sub hadd (he.const_mul _), integral_add hsub (integrable_const _),
    integral_sub (hf.const_mul 2) hi, integral_const_mul, integral_const_mul]
  simp [f, e, integral_indicator measurableSet_Iic, integral_const, Measure.real,
    unitInterval.volume_Iic, ENNReal.toReal_ofReal u.property.1]
  ring

theorem integral_sq_le_twice_lower_integral {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, g u ^ 2) ≤ 2 * (∫ u : I, ∫ w in Iic u, g w) -
      (∫ u : I, g u) + (∫ u : I, g u) ^ 2 := by
  have hi := integrable_unit_bounded hg.measurable hb
  have hsq := integrable_unit_bounded (hg.measurable.pow_const 2)
    (fun u => (show g u ^ 2 ∈ Icc 0 1 from
      ⟨sq_nonneg _, by nlinarith [(hb u).1, (hb u).2]⟩))
  have hF := integrable_lower_integral hg.measurable hb
  have hw : Integrable (fun u : I => (u : ℝ) * g u) :=
    integrable_unit_bounded (measurable_subtype_coe.mul hg.measurable)
      (fun u => ⟨mul_nonneg u.property.1 (hb u).1,
        (mul_le_mul_of_nonneg_right u.property.2 (hb u).1).trans (by simpa using (hb u).2)⟩)
  have hp (u : I) : g u ^ 2 - 2 * g u * (∫ w : I, g w) + (∫ w : I, g w ^ 2) ≤
      2 * (∫ w in Iic u, g w) - (∫ w : I, g w) + g u - 2 * ((u : ℝ) * g u) := by
    have ha (w : I) : |g u - g w| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hb u).1, (hb w).2], by linarith [(hb u).2, (hb w).1]⟩
    have haI : Integrable (fun w => |g u - g w|) := integrable_unit_bounded (continuous_abs.measurable.comp (measurable_const.sub hg.measurable))
      (fun w => ⟨abs_nonneg _, ha w⟩)
    have hqI : Integrable (fun w => (g u - g w) ^ 2) := integrable_unit_bounded ((measurable_const.sub hg.measurable).pow_const 2)
      (fun w => ⟨sq_nonneg _, (sq_le_one_iff_abs_le_one _).mpr (ha w)⟩)
    have hle := integral_mono hqI haI (fun w => by
      nlinarith [sq_abs (g u - g w), abs_nonneg (g u - g w), ha w])
    have hid : (fun w : I => (g u - g w) ^ 2) =
        fun w => g u ^ 2 - (2 * g u) * g w + g w ^ 2 := by funext w; ring
    have hsub : Integrable (fun w => g u ^ 2 - (2 * g u) * g w) :=
      (integrable_const _).sub (hi.const_mul _)
    rw [hid, integral_add hsub hsq,
      integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul,
      integral_abs_sub_of_antitone hg hb u] at hle
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_assoc] using hle
  have hl : Integrable (fun u => g u ^ 2 - 2 * g u * (∫ w : I, g w)) :=
    hsq.sub ((hi.const_mul 2).mul_const _)
  have hr : Integrable (fun u => 2 * (∫ w in Iic u, g w) - (∫ w : I, g w)) :=
    (hF.const_mul 2).sub (integrable_const _)
  have hra : Integrable (fun u => 2 * (∫ w in Iic u, g w) - (∫ w : I, g w) + g u) :=
    hr.add hi
  have h := integral_mono (hl.add (integrable_const _)) (hra.sub (hw.const_mul 2)) hp
  simp only [Pi.add_apply, Pi.sub_apply] at h
  rw [integral_add hl (integrable_const _),
    integral_sub hsq ((hi.const_mul 2).mul_const _), integral_mul_const, integral_const_mul,
    integral_sub hra (hw.const_mul 2), integral_add hr hi,
    integral_sub (hF.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const_mul] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hA := integral_lower_integral hg.measurable hb
  have hid : (fun u : I => (1 - (u : ℝ)) * g u) = fun u => g u - (u : ℝ) * g u := by
    funext u; ring
  rw [hid, integral_sub hi hw] at hA
  nlinarith

theorem conditionalCDF_sq_le_cdf_integral (C : Copula 2) (hC : C.IsSI) (v : I) :
    (∫ u : I, C.conditionalCDF u v ^ 2) ≤
      2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ) + (v : ℝ) ^ 2 := by
  obtain ⟨g, hg, hb, he⟩ := conditionalCDF_antitone_version C hC v
  have hm : (∫ u : I, g u) = (v : ℝ) :=
    (integral_congr_ae he).symm.trans (C.integral_conditionalCDF v)
  have hF (u : I) : (∫ w in Iic u, g w) = C.cdf ![u, v] := by
    rw [C.cdf_eq_integral_conditionalCDF]
    exact integral_congr_ae (ae_restrict_of_ae he.symm)
  have h := integral_sq_le_twice_lower_integral hg hb
  simp_rw [hF, hm] at h
  have hsq : (∫ u : I, C.conditionalCDF u v ^ 2) = ∫ u : I, g u ^ 2 :=
    integral_congr_ae (he.fun_comp (fun z : ℝ => z ^ 2))
  rwa [hsq]

theorem spearmanRho_eq_iterated_cdf (C : Copula 2) :
    C.spearmanRho = 12 * (∫ v : I, ∫ u : I, C.cdf ![u, v]) - 3 := by
  rw [C.spearmanRho_eq_integral_cdf, Copula.toMeasure_independence]
  have hm := ((volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow).integral_comp
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding C.cdf
  have hi : Integrable (fun p : I × I => C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (C.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : (∫ x : Fin 2 → I, C.cdf x) = ∫ v : I, ∫ u : I, C.cdf ![u, v] := by
    rw [← hm]
    exact integral_prod_symm _ hi
  change 12 * (∫ x : Fin 2 → I, C.cdf x) - 3 = _
  rw [he]

theorem xi_le_rho_of_isSI (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ≤ C.spearmanRho := by
  have hi : Integrable (fun p : I × I => C.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (C.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv : Integrable (fun v : I => (v : ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  have hs : Integrable (fun v : I => (v : ℝ) ^ 2) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have hd : Integrable (fun v : I => 2 * (∫ u : I, C.cdf ![u, v]) - (v : ℝ)) :=
    (hi.integral_prod_right.const_mul 2).sub hv
  have h := integral_mono C.integrable_integral_conditionalCDF_sq
    (hd.add hs) (conditionalCDF_sq_le_cdf_integral C hC)
  simp only [Pi.add_apply] at h
  rw [integral_add hd hs, integral_sub (hi.integral_prod_right.const_mul 2) hv,
    integral_const_mul, Copula.integral_unit_id, Copula.integral_unit_pow] at h
  rw [spearmanRho_eq_iterated_cdf]
  unfold Copula.chatterjeeXi
  norm_num at h
  linarith

theorem xi_le_neg_rho_of_isSD (C : Copula 2) (hC : C.IsSD) :
    C.chatterjeeXi ≤ -C.spearmanRho := by
  have h := xi_le_rho_of_isSI (C.reflect {1}) ((Copula.isSI_reflect_second_iff C).mpr hC)
  simpa only [xi_reflect_second, Copula.spearmanRho_reflect_second] using h

theorem xi_le_abs_rho_of_stochastically_monotone (C : Copula 2) (hC : C.IsSI ∨ C.IsSD) :
    C.chatterjeeXi ≤ |C.spearmanRho| := by
  rcases hC with h | h
  · exact (xi_le_rho_of_isSI C h).trans (le_abs_self _)
  · exact (xi_le_neg_rho_of_isSD C h).trans (neg_le_abs _)

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
