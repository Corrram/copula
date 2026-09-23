import Copula.Rank.Region.XiBlest.Support.PartitionAverage
import Copula.Rank.Region.XiBlest.Support.CheckerboardStability

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def rowMeanEnergy {n : ℕ} (P : IntervalPartition n) (C : Copula 2) (v : I) : ℝ :=
  ∑ i, P.width i*copulaRowMean P C i v^2

theorem copulaRowMean_mem {n : ℕ} (P : IntervalPartition n) (C : Copula 2) (i : Fin n) (v : I) :
    copulaRowMean P C i v ∈ Icc (0 : ℝ) 1 := by
  rw [copulaRowMean_integral]
  constructor
  · exact integral_nonneg fun _ => C.conditionalCDF_nonneg _ _
  · calc
      _ ≤ ∫ _u : I, (1 : ℝ) := integral_mono (conditionalCDF_embed_integrable P C i v) (integrable_const _)
        (fun _ => C.conditionalCDF_le_one _ _)
      _ = 1 := by simp

theorem rowMeanEnergy_error {n : ℕ} (P : IntervalPartition n) (C : Copula 2) (v : I) :
    conditionalEnergy C v-rowMeanEnergy P C v ≤ 2*partitionAverageError P (fun u => C.conditionalCDF u v) := by
  have he (i : Fin n) : copulaRowMean P C i v=partitionAverage P (fun u => C.conditionalCDF u v) i :=
    copulaRowMean_integral P C i v
  have hi (i : Fin n) : (∫ u : I, C.conditionalCDF (partitionEmbed P i u) v^2) ≤
      copulaRowMean P C i v^2+2*(∫ u : I, |copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|) := by
    have hp (u : I) : C.conditionalCDF (partitionEmbed P i u) v^2 ≤
        copulaRowMean P C i v^2+2*|copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v| :=
      sq_sub_le_of_mem_unit ⟨C.conditionalCDF_nonneg _ _,C.conditionalCDF_le_one _ _⟩
        (copulaRowMean_mem P C i v) (by rw [abs_sub_comm])
    have hh := integral_mono (conditionalCDF_embed_sq_integrable P C i v)
      ((integrable_const _).add (((integrable_const _).sub (conditionalCDF_embed_integrable P C i v)).abs.const_mul 2)) hp
    simp only [Pi.add_apply,Pi.sub_apply] at hh
    rw [integral_add (g := fun u => 2*|copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|)
      (integrable_const _) (((integrable_const _).sub (conditionalCDF_embed_integrable P C i v)).abs.const_mul 2),integral_const_mul] at hh
    simpa using hh
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hi i) (P.width_pos i).le)
  unfold conditionalEnergy
  rw [integral_partition P _ ((C.measurable_conditionalCDF_left v).pow_const 2)
    (fun i => conditionalCDF_embed_sq_integrable P C i v)]
  unfold rowMeanEnergy partitionAverageError
  simp only [mul_add,Finset.sum_add_distrib] at hh
  simp_rw [← he]
  rw [Finset.mul_sum]
  have ht : (∑ i, P.width i*(2*∫ u : I, |copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|)) =
      ∑ i, 2*(P.width i*∫ u : I, |copulaRowMean P C i v-C.conditionalCDF (partitionEmbed P i u) v|) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ht] at hh
  linarith

theorem rowMeanEnergy_tendsto (C : Copula 2) (v : I) :
    Tendsto (fun k => rowMeanEnergy (IntervalPartition.uniform (k+1) (by omega)) C v) atTop (𝓝 (conditionalEnergy C v)) := by
  have he := partitionAverageError_tendsto (fun u => C.conditionalCDF u v)
    (C.measurable_conditionalCDF_left v) (C.integrable_conditionalCDF v)
    (fun k i => conditionalCDF_embed_integrable _ C i v)
  have hd : Tendsto (fun k => conditionalEnergy C v-rowMeanEnergy (IntervalPartition.uniform (k+1) (by omega)) C v)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sub_nonneg.mpr (copulaRowMean_energy_le _ C v))
      (fun k => rowMeanEnergy_error _ C v)
    simpa only [mul_zero] using he.const_mul 2
  simpa only [sub_sub_cancel,sub_zero] using (tendsto_const_nhds (x := conditionalEnergy C v)).sub hd

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
