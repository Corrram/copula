import Copula.Rank.Region.XiBlest.Support.PartitionEmbed

open ProbabilityTheory
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def partitionCenter {n : ℕ} (P : IntervalPartition n) (i : Fin n) : ℝ :=
  (P.point i.castSucc : ℝ)+P.width i/2

theorem partition_center_mean {n : ℕ} (P : IntervalPartition n) :
    (∑ i, P.width i * partitionCenter P i) = 1/2 := by
  have he (i : Fin n) : P.width i * partitionCenter P i =
      ((P.point i.succ : ℝ)^2-(P.point i.castSucc : ℝ)^2)/2 := by
    unfold partitionCenter IntervalPartition.width
    ring
  simp_rw [he]
  rw [← Finset.sum_div,IntervalPartition.sum_differences (fun j => (P.point j : ℝ)^2)]
  simp [P.one,P.zero]

theorem cellMass_total {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n} (A : CellMass P Q) :
    (∑ i, ∑ j, A.mass i j) = 1 := by simp only [A.row_sum,P.sum_width]

theorem cellMass_first_center {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n} (A : CellMass P Q) :
    (∑ i, ∑ j, A.mass i j * partitionCenter P i) = 1/2 := by
  simp only [← Finset.sum_mul,A.row_sum]
  exact partition_center_mean P

theorem cellMass_second_center {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n} (A : CellMass P Q) :
    (∑ i, ∑ j, A.mass i j * partitionCenter Q j) = 1/2 := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul,A.col_sum]
  exact partition_center_mean Q

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
