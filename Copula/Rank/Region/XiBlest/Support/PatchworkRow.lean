import Copula.Rank.Region.XiBlest.Support.PatchworkConditional

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchworkRow_joint_measurable (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) :
    Measurable (fun p : I × I => patchworkRow A C i p.1 p.2) := by
  apply Finset.measurable_sum
  intro j _
  exact ((normalizedCDF_measurable (C i j)).comp
    (((partition_coord_continuous Q j).measurable.comp measurable_fst).prodMk measurable_snd)).const_mul _

theorem patchworkRow_mem (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) (v u : I) :
    patchworkRow A C i v u ∈ Icc (0 : ℝ) 1 := by
  have hw := (P.width_pos i).le
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (div_nonneg (A.nonneg i j) hw) (normalizedCDF_mem _ _ _).1)
  · calc
      _ ≤ ∑ j, A.mass i j / P.width i * 1 := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (normalizedCDF_mem _ _ _).2 (div_nonneg (A.nonneg i j) hw))
      _ = 1 := by simp only [mul_one,← Finset.sum_div,A.row_sum,div_self (P.width_pos i).ne']

theorem patchworkRow_sq_integrable (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (i : Fin m) (v : I) :
    Integrable (fun u => patchworkRow A C i v u^2) := by
  refine (integrable_const (1 : ℝ)).mono' ((patchworkRow_measurable A C i v).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have h := patchworkRow_mem A C i v u
    nlinarith [h.1,h.2]

noncomputable def cellPrefix (A : CellMass P Q) (i : Fin m) (j : Fin n) : ℝ :=
  ∑ s, if s < j then A.mass i s else 0

theorem patchworkRow_embed (A : CellMass P Q) (C : Fin m → Fin n → Copula 2)
    (i : Fin m) (j : Fin n) (v u : I) :
    patchworkRow A C i (partitionEmbed Q j v) u =
      cellPrefix A i j / P.width i + A.mass i j / P.width i * normalizedCDF (C i j) u v := by
  unfold patchworkRow
  simp_rw [partition_coord_embed]
  have he (s : Fin n) :
      A.mass i s / P.width i * normalizedCDF (C i s) u (if s < j then 1 else if s=j then v else 0) =
      (if s < j then A.mass i s / P.width i else 0) +
        (if s=j then A.mass i s / P.width i * normalizedCDF (C i s) u v else 0) := by
    rcases lt_trichotomy s j with h | rfl | h
    · simp [h,ne_of_lt h,normalizedCDF_one]
    · simp
    · simp [not_lt_of_gt h,ne_of_gt h,normalizedCDF_zero]
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  congr 1
  simp only [cellPrefix,Finset.sum_div,ite_div,zero_div]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
