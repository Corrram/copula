import Copula.Rank.Region.XiBlest.Support.PartitionCellIntegral
import Copula.Patchwork.Approximation

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

noncomputable def checkerboardRow (A : CellMass P Q) (i : Fin m) (v : I) : ℝ :=
  ∑ j, A.mass i j / P.width i * (Q.coord j v : ℝ)

theorem cellMass_row_prefix (C : Copula 2) (P : IntervalPartition m) (Q : IntervalPartition n)
    (i : Fin m) (k : Fin (n+1)) :
    (∑ j, if j.val < k.val then (C.cellMass P Q).mass i j else 0) =
      C.cdf ![P.point i.succ,Q.point k]-C.cdf ![P.point i.castSucc,Q.point k] := by
  have ht := IntervalPartition.sum_prefix_differences
    (fun j => C.cdf ![P.point i.succ,Q.point j]-C.cdf ![P.point i.castSucc,Q.point j]) k
  simp only [Q.zero,Copula.cdf_two_zero_right,sub_self,sub_zero] at ht
  rw [← ht]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · dsimp [Copula.cellMass]
    ring
  · rfl

theorem checkerboardRow_grid (C : Copula 2) (P : IntervalPartition m) (Q : IntervalPartition n)
    (i : Fin m) (k : Fin (n+1)) :
    checkerboardRow (C.cellMass P Q) i (Q.point k) = copulaRowMean P C i (Q.point k) := by
  unfold checkerboardRow copulaRowMean
  simp only [IntervalPartition.coord_point,apply_ite,show ((1 : I) : ℝ)=1 from rfl,show ((0 : I) : ℝ)=0 from rfl,
    mul_one,mul_zero]
  have he (j : Fin n) : (if j.val < k.val then (C.cellMass P Q).mass i j / P.width i else 0) =
      (if j.val < k.val then (C.cellMass P Q).mass i j else 0)/P.width i := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_div,cellMass_row_prefix]

theorem partition_coord_embed_affine (Q : IntervalPartition n) (j s : Fin n) (v : I) :
    (Q.coord s (partitionEmbed Q j v) : ℝ) =
      (1-(v : ℝ))*(Q.coord s (Q.point j.castSucc) : ℝ)+(v : ℝ)*(Q.coord s (Q.point j.succ) : ℝ) := by
  rw [partition_coord_embed,IntervalPartition.coord_point,IntervalPartition.coord_point]
  rcases lt_trichotomy s j with h | rfl | h
  · have hj : s.val < j.val := h
    have hj' : s.val < j.val+1 := by omega
    simp only [h,ite_true,Fin.val_castSucc,Fin.val_succ,hj,hj',show ((1 : I) : ℝ)=1 from rfl]
    ring
  · simp
  · have hj : ¬ s.val < j.val := by exact not_lt_of_gt h
    have hj' : ¬ s.val < j.val+1 := by have : j.val < s.val := h; omega
    simp only [not_lt_of_gt h,ne_of_gt h,ite_false,Fin.val_castSucc,Fin.val_succ,hj,hj',
      show ((0 : I) : ℝ)=0 from rfl,mul_zero,add_zero]

theorem checkerboardRow_embed (A : CellMass P Q) (i : Fin m) (j : Fin n) (v : I) :
    checkerboardRow A i (partitionEmbed Q j v) =
      (1-(v : ℝ))*checkerboardRow A i (Q.point j.castSucc)+(v : ℝ)*checkerboardRow A i (Q.point j.succ) := by
  unfold checkerboardRow
  simp_rw [partition_coord_embed_affine]
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro s _ <;> ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
