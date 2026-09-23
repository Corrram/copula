import Copula.Rank.Region.XiBlest.Support.PartitionPiece
import Copula.Rank.Region.XiBlest.Support.NormalizedConditionalCDF
import Copula.Rank.ConditionalCDF

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

noncomputable def patchworkRow (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    (i : Fin m) (v u : I) : ℝ :=
  ∑ j, A.mass i j / P.width i * normalizedCDF (C i j) u (Q.coord j v)

noncomputable def patchworkKernel (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    (v u : I) : ℝ := ∑ i, partitionPiece P i (patchworkRow A C i v) u

theorem patchworkRow_measurable (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) (v : I) :
    Measurable (patchworkRow A C i v) := by
  apply Finset.measurable_sum
  intro j _
  exact ((normalizedCDF_measurable (C i j)).comp (measurable_const.prodMk measurable_id)).const_mul _

theorem patchworkRow_integrable (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) (v : I) :
    Integrable (patchworkRow A C i v) := by
  apply integrable_finsetSum
  intro j _
  exact (normalizedCDF_integrable (C i j) (Q.coord j v)).const_mul _

theorem patchworkKernel_integrable (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (v : I) :
    Integrable (patchworkKernel A C v) := by
  apply integrable_finsetSum
  intro i _
  exact partitionPiece_integrable P i (patchworkRow_measurable A C i v) (patchworkRow_integrable A C i v)

theorem patchworkKernel_nonneg (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (v u : I) :
    0 ≤ patchworkKernel A C v u := by
  apply Finset.sum_nonneg
  intro i _
  unfold partitionPiece
  split_ifs
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (div_nonneg (A.nonneg i j) (P.width_pos i).le)
      (normalizedCDF_mem (C i j) _ _).1)
  · rfl

theorem integral_patchworkRow_Iic (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    (i : Fin m) (v t : I) :
    (∫ u in Iic t, patchworkRow A C i v u) =
      ∑ j, A.mass i j / P.width i * (C i j).cdf ![t,Q.coord j v] := by
  unfold patchworkRow
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul,integral_congr_ae (ae_restrict_of_ae (normalizedCDF_ae (C i j) (Q.coord j v))),
      ← Copula.cdf_eq_integral_conditionalCDF]
  · intro j _
    exact ((normalizedCDF_integrable (C i j) _).const_mul _).integrableOn

theorem patchwork_conditionalCDF (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (v : I) :
    (fun u => (A.patchwork C).conditionalCDF u v) =ᵐ[volume] patchworkKernel A C v := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v (patchworkKernel_integrable A C v)
    (fun u => patchworkKernel_nonneg A C v u)
  intro t
  unfold patchworkKernel
  rw [integral_finsetSum]
  · simp_rw [integral_partitionPiece_Iic P _ (patchworkRow_measurable A C _ v)
      (patchworkRow_integrable A C _ v),integral_patchworkRow_Iic]
    rw [CellMass.cdf_patchwork]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp [(P.width_pos i).ne']
  · intro i _
    exact (partitionPiece_integrable P i (patchworkRow_measurable A C i v)
      (patchworkRow_integrable A C i v)).integrableOn

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
