import Copula.Rank.Region.XiBlest.Support.PatchworkLaw
import Copula.Rank.Region.XiBlest.Support.PartitionCoordEmbed

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {n : ℕ} (P : IntervalPartition n)

theorem volume_partition : (volume : Measure I) =
    ∑ i, ENNReal.ofReal (P.width i) • volume.map (partitionEmbed P i) := by
  have hm : Measurable (fun x : Fin 2 → I => x 0) := measurable_pi_apply 0
  let Q := IntervalPartition.uniform 1 (by omega)
  let A := CellMass.product P Q
  let C := fun (_ : Fin n) (_ : Fin 1) => Copula.independence 2
  have h := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (fun x => x 0))
    (toMeasure_patchworkLaw A C)
  rw [Copula.map_eval] at h
  simp only [patchworkLaw,Measure.map_finset_sum' hm.aemeasurable,
    Measure.map_smul _ hm.aemeasurable,
    partitionCellLaw,Measure.map_map hm (partitionCellMap_continuous _ _ _ _).measurable] at h
  have he (i : Fin n) (j : Fin 1) :
      ((fun x : Fin 2 → I => x 0) ∘ partitionCellMap P Q i j) = partitionEmbed P i ∘ (fun x => x 0) := by rfl
  simp_rw [he] at h
  simp_rw [← Measure.map_map (partitionEmbed_continuous P _).measurable hm] at h
  simp only [C,Copula.map_eval,A,CellMass.product,Q,IntervalPartition.width_uniform] at h
  simpa using h


theorem integrable_partition {f : I → ℝ} (hf : Measurable f)
    (hi : ∀ i, Integrable (fun u => f (partitionEmbed P i u))) : Integrable f := by
  rw [volume_partition P]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact ((integrable_map_measure hf.aestronglyMeasurable
    (partitionEmbed_continuous P i).measurable.aemeasurable).mpr (hi i)).smul_measure ENNReal.ofReal_ne_top

theorem integral_partition (f : I → ℝ) (hf : Measurable f)
    (hi : ∀ i, Integrable (fun u => f (partitionEmbed P i u))) :
    (∫ u : I, f u) = ∑ i, P.width i * ∫ u : I, f (partitionEmbed P i u) := by
  conv_lhs => rw [volume_partition P]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure,ENNReal.toReal_ofReal (P.width_pos i).le,smul_eq_mul,
      integral_map (partitionEmbed_continuous P i).measurable.aemeasurable hf.aestronglyMeasurable]
  · intro i _
    exact ((integrable_map_measure hf.aestronglyMeasurable
      (partitionEmbed_continuous P i).measurable.aemeasurable).mpr (hi i)).smul_measure ENNReal.ofReal_ne_top

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
