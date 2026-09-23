import Copula.Dependence.Density
import Mathlib.MeasureTheory.Integral.Prod
import Copula.Rank.Symmetry
import Copula.Rank.ConditionalDerivative
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Kendall tau as the product of the two conditional CDFs

The identity uses disintegration and Fubini, so it applies to singular copulas
as well as those admitting a Lebesgue density.
-/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_copula_conditionalKernel (C : Copula 2)
    (f : (Fin 2 → I) → ℝ) (hf : Continuous f) :
    (∫ x,f x ∂C.toMeasure) = ∫ u : I,∫ v,f ![u,v] ∂C.conditionalKernel u := by
  have hm := compProd_map_condDistrib (μ := C.toMeasure) (mα := inferInstance)
    (mβ := inferInstance) (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  rw [C.map_eval] at hm
  change (volume : Measure I) ⊗ₘ C.conditionalKernel = _ at hm
  have hg : Continuous (fun p : I × I => f ![p.1,p.2]) := hf.comp (by fun_prop)
  have hi := hg.integrable_of_hasCompactSupport (μ := (volume : Measure I) ⊗ₘ C.conditionalKernel)
    (HasCompactSupport.of_compactSpace _)
  have he := congrArg (fun μ : Measure (I × I) => ∫ p,f ![p.1,p.2] ∂μ) hm
  rw [Measure.integral_compProd hi,integral_map (by fun_prop) hg.measurable.aestronglyMeasurable] at he
  have hh : (fun x : Fin 2 → I => f ![x 0,x 1])=f := by
    funext x
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [hh] using he.symm

/-- Integrating a bounded nonnegative primitive against a probability law. -/
theorem integral_unit_primitive (μ : Measure I) [IsProbabilityMeasure μ]
    (g : I → ℝ) (hg : Measurable g) (hb : ∀ t, g t ∈ Icc (0:ℝ) 1) :
    (∫ v, (∫ t in Iic v,g t) ∂μ) = ∫ t : I,g t*(1-μ.real (Iic t)) := by
  classical
  have hi : Integrable (fun p : I × I => if p.2<p.1 then g p.2 else 0)
      (μ.prod volume) := by
    refine (integrable_const (1:ℝ)).mono'
      (((hg.comp measurable_snd).ite (measurableSet_lt measurable_snd measurable_fst) measurable_const).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun p => by
      split_ifs
      · simpa only [Real.norm_eq_abs,abs_of_nonneg (hb _).1] using (hb p.2).2
      · norm_num
  calc
    _ = ∫ v,(∫ t : I,if t<v then g t else 0) ∂μ := by
      simp_rw [integral_Iic_eq_integral_Iio,← integral_indicator measurableSet_Iio]
      simp only [indicator,mem_Iio]
    _ = ∫ t : I,∫ v,if t<v then g t else 0 ∂μ := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        have he : (fun v : I => if t<v then g t else 0)=(Ioi t).indicator (fun _ => g t) := rfl
        change (∫ v : I,if t<v then g t else 0 ∂μ)=g t*(1-μ.real (Iic t))
        rw [he,integral_indicator measurableSet_Ioi,integral_const]
        have hm : μ.real (Ioi t)=1-μ.real (Iic t) := by
          rw [← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ]
        simp only [Measure.restrict_apply_univ,smul_eq_mul,Measure.real] at hm ⊢
        rw [hm,mul_comm]

theorem crossConditional_integrable (C : Copula 2) :
    Integrable (fun p : I × I => C.conditionalCDF p.1 p.2*C.transpose.conditionalCDF p.2 p.1) := by
  refine (integrable_const (1:ℝ)).mono'
    (((C.measurable_conditionalCDF.comp measurable_swap).mul C.transpose.measurable_conditionalCDF).aestronglyMeasurable) ?_
  exact Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (C.conditionalCDF_nonneg _ _) (C.transpose.conditionalCDF_nonneg _ _))]
    exact (mul_le_of_le_one_left (C.transpose.conditionalCDF_nonneg _ _) (C.conditionalCDF_le_one _ _)).trans (C.transpose.conditionalCDF_le_one _ _)

theorem kendallTau_conditional_product (C : Copula 2) :
    C.kendallTau=1-4*(∫ u : I,∫ v : I,C.conditionalCDF u v*C.transpose.conditionalCDF v u) := by
  have he (u : I) : (∫ v,C.cdf ![u,v] ∂C.conditionalKernel u) =
      (u:ℝ)-(∫ v : I,C.conditionalCDF u v*C.transpose.conditionalCDF v u) := by
    have hg := C.transpose.measurable_conditionalCDF_left u
    have hb (v : I) : C.transpose.conditionalCDF v u ∈ Icc (0:ℝ) 1 :=
      ⟨C.transpose.conditionalCDF_nonneg _ _,C.transpose.conditionalCDF_le_one _ _⟩
    have hh := integral_unit_primitive (C.conditionalKernel u) _ hg hb
    have he' (v : I) : C.cdf ![u,v] = ∫ t in Iic v,C.transpose.conditionalCDF t u := by
      rw [← C.transpose.cdf_eq_integral_conditionalCDF,Copula.cdf_transpose]
    simp_rw [he']
    rw [hh]
    change (∫ v : I,C.transpose.conditionalCDF v u*(1-C.conditionalCDF u v))=_
    have hm : Measurable (fun v : I => C.conditionalCDF u v) :=
      C.measurable_conditionalCDF.comp (measurable_id.prodMk measurable_const)
    have hi : Integrable (fun v : I => C.conditionalCDF u v*C.transpose.conditionalCDF v u) := by
      refine (integrable_const (1:ℝ)).mono' (hm.mul hg).aestronglyMeasurable ?_
      exact Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (C.conditionalCDF_nonneg _ _) (hb v).1)]
        exact (mul_le_of_le_one_left (hb v).1 (C.conditionalCDF_le_one _ _)).trans (hb v).2
    have he'' : (fun v : I => C.transpose.conditionalCDF v u*(1-C.conditionalCDF u v)) =
        fun v => C.transpose.conditionalCDF v u-C.conditionalCDF u v*C.transpose.conditionalCDF v u := by
      funext v
      ring
    rw [he'',integral_sub (C.transpose.integrable_conditionalCDF u) hi,C.transpose.integral_conditionalCDF]
  unfold Copula.kendallTau
  rw [integral_copula_conditionalKernel C C.cdf C.continuous_cdf]
  simp_rw [he]
  rw [integral_sub (Copula.integrable_continuous_unit volume continuous_subtype_val)
    (crossConditional_integrable C).integral_prod_left,Copula.integral_unit_id]
  ring

end ProbabilityTheory.Copula
