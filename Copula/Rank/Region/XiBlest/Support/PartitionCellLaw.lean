import Copula.Rank.Region.XiBlest.Support.PartitionEmbed

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} (P : IntervalPartition m) (Q : IntervalPartition n)

def partitionCellMap (i : Fin m) (j : Fin n) (x : Fin 2 → I) : Fin 2 → I :=
  ![partitionEmbed P i (x 0),partitionEmbed Q j (x 1)]

theorem partitionCellMap_continuous (i : Fin m) (j : Fin n) :
    Continuous (partitionCellMap P Q i j) := by
  apply continuous_pi
  intro a
  fin_cases a
  · exact (partitionEmbed_continuous P i).comp (continuous_apply 0)
  · exact (partitionEmbed_continuous Q j).comp (continuous_apply 1)

noncomputable def partitionCellLaw (i : Fin m) (j : Fin n) (C : Copula 2) : Measure (Fin 2 → I) :=
  C.toMeasure.map (partitionCellMap P Q i j)

instance (i : Fin m) (j : Fin n) (C : Copula 2) : IsProbabilityMeasure (partitionCellLaw P Q i j C) := by
  unfold partitionCellLaw
  infer_instance

theorem partitionCellLaw_Iic (i : Fin m) (j : Fin n) (C : Copula 2) (u : Fin 2 → I) :
    partitionCellLaw P Q i j C (Iic u) = ENNReal.ofReal (C.cdf ![P.coord i (u 0),Q.coord j (u 1)]) := by
  rw [partitionCellLaw,Measure.map_apply (partitionCellMap_continuous P Q i j).measurable measurableSet_Iic]
  by_cases h0 : P.point i.castSucc ≤ u 0
  · by_cases h1 : Q.point j.castSucc ≤ u 1
    · have he : (partitionCellMap P Q i j) ⁻¹' Iic u = Iic ![P.coord i (u 0),Q.coord j (u 1)] := by
        ext x
        simp only [mem_preimage,mem_Iic,Pi.le_def,Fin.forall_fin_two,partitionCellMap,
          Matrix.cons_val_zero,Matrix.cons_val_one,partitionEmbed_le_iff P i _ _ h0,
          partitionEmbed_le_iff Q j _ _ h1]
      rw [he]
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    · have he : (partitionCellMap P Q i j) ⁻¹' Iic u = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact h1 ((partitionEmbed_lower Q j (x 1)).trans (hx 1))
      rw [he,measure_empty,Q.coord_of_le j (u 1) (le_of_not_ge h1)]
      simp
  · have he : (partitionCellMap P Q i j) ⁻¹' Iic u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h0 ((partitionEmbed_lower P i (x 0)).trans (hx 0))
    rw [he,measure_empty,P.coord_of_le i (u 0) (le_of_not_ge h0)]
    simp

theorem integral_partitionCellLaw (i : Fin m) (j : Fin n) (C : Copula 2)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂partitionCellLaw P Q i j C) = ∫ x, f (partitionCellMap P Q i j x) ∂C.toMeasure :=
  integral_map (partitionCellMap_continuous P Q i j).measurable.aemeasurable hf.measurable.aestronglyMeasurable

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
