import Copula.Rank.Region.XiBlest.Support.PartitionPiece
import Copula.Rank.ConditionalCDF
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {n : ℕ} (P : IntervalPartition n)

theorem partition_indicator_embed (i r : Fin n) (f : I → ℝ) :
    (fun u => (Ioc (P.point i.castSucc) (P.point i.succ)).indicator f (partitionEmbed P r u)) =ᵐ[volume]
      fun u => if r=i then f (partitionEmbed P i u) else 0 := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  have hu' : 0 < u := lt_of_le_of_ne u.property.1 (Ne.symm hu)
  by_cases hr : r=i
  · subst r
    simp only [ite_true,Set.indicator,Set.mem_Ioc,partitionEmbed_strict_lower P i u hu',partitionEmbed_upper,and_self]
  · have hb := partitionPiece_embed P i r (fun _ => (1 : ℝ)) u hu'
    have hn : ¬ (P.point i.castSucc < partitionEmbed P r u ∧ partitionEmbed P r u ≤ P.point i.succ) := by
      intro h
      simp [partitionPiece,h,hr] at hb
    simp only [hr,ite_false,Set.indicator,Set.mem_Ioc,hn]

theorem integral_partition_cell (i : Fin n) {f : I → ℝ} (hf : Measurable f)
    (hi : Integrable (fun u => f (partitionEmbed P i u))) :
    (∫ u in Ioc (P.point i.castSucc) (P.point i.succ), f u) =
      P.width i * ∫ u : I, f (partitionEmbed P i u) := by
  have hm := hf.indicator (measurableSet_Ioc (a := P.point i.castSucc) (b := P.point i.succ))
  have he := partition_indicator_embed P i
  have hj (r : Fin n) : Integrable (fun u =>
      (Ioc (P.point i.castSucc) (P.point i.succ)).indicator f (partitionEmbed P r u)) := by
    by_cases h : r=i
    · exact hi.congr (by simpa only [h,ite_true] using (he r f).symm)
    · exact (integrable_const (0 : ℝ)).congr (by simpa only [h,ite_false] using (he r f).symm)
  rw [← integral_indicator measurableSet_Ioc,integral_partition P _ hm hj]
  have heint (r : Fin n) : (∫ u : I,
      (Ioc (P.point i.castSucc) (P.point i.succ)).indicator f (partitionEmbed P r u)) =
      if r=i then ∫ u : I, f (partitionEmbed P i u) else 0 := by
    rw [integral_congr_ae (he r f)]
    by_cases h : r=i <;> simp [h]
  simp_rw [heint]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem conditionalCDF_embed_integrable (C : Copula 2) (i : Fin n) (v : I) :
    Integrable (fun u => C.conditionalCDF (partitionEmbed P i u) v) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((C.measurable_conditionalCDF_left v).comp (partitionEmbed_continuous P i).measurable).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (C.conditionalCDF_nonneg _ _)]
    exact C.conditionalCDF_le_one _ _

theorem conditionalCDF_embed_sq_integrable (C : Copula 2) (i : Fin n) (v : I) :
    Integrable (fun u => C.conditionalCDF (partitionEmbed P i u) v^2) := by
  refine (integrable_const (1 : ℝ)).mono'
    (((C.measurable_conditionalCDF_left v).comp (partitionEmbed_continuous P i).measurable).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    nlinarith [C.conditionalCDF_nonneg (partitionEmbed P i u) v,C.conditionalCDF_le_one (partitionEmbed P i u) v]

noncomputable def copulaRowMean (C : Copula 2) (i : Fin n) (v : I) : ℝ :=
  (C.cdf ![P.point i.succ,v]-C.cdf ![P.point i.castSucc,v])/P.width i

theorem copulaRowMean_integral (C : Copula 2) (i : Fin n) (v : I) :
    copulaRowMean P C i v = ∫ u : I, C.conditionalCDF (partitionEmbed P i u) v := by
  have h := Copula.integral_Iic_add_Ioc_unit (C.integrable_conditionalCDF v)
    (P.strictMono.monotone (le_of_lt (Fin.castSucc_lt_succ (i := i))))
  rw [← C.cdf_eq_integral_conditionalCDF,← C.cdf_eq_integral_conditionalCDF,
    integral_partition_cell P i (C.measurable_conditionalCDF_left v) (conditionalCDF_embed_integrable P C i v)] at h
  unfold copulaRowMean
  apply (div_eq_iff (P.width_pos i).ne').mpr
  linarith

theorem copulaRowMean_energy_le (C : Copula 2) (v : I) :
    (∑ i, P.width i * copulaRowMean P C i v^2) ≤ ∫ u : I, C.conditionalCDF u v^2 := by
  rw [integral_partition P _ ((C.measurable_conditionalCDF_left v).pow_const 2)
    (fun i => conditionalCDF_embed_sq_integrable P C i v)]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (P.width_pos i).le
  rw [copulaRowMean_integral]
  exact ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hx => hx.1) (convex_Icc (0 : ℝ) 1)).map_integral_le
    (by fun_prop : Continuous (fun x : ℝ => x^2)).continuousOn isClosed_Icc
    (Filter.Eventually.of_forall fun u => ⟨C.conditionalCDF_nonneg _ _,C.conditionalCDF_le_one _ _⟩)
    (conditionalCDF_embed_integrable P C i v) (conditionalCDF_embed_sq_integrable P C i v)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
