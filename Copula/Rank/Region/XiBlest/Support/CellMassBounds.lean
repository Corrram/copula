import Copula.Rank.Region.XiBlest.Support.PartitionMoments
import Copula.Rank.Region.XiBlest.Support.RectangularTau

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem cellMass_le_row (A : CellMass P Q) (i : Fin m) (j : Fin n) : A.mass i j ≤ P.width i := by
  rw [← A.row_sum i]
  exact Finset.single_le_sum (fun s _ => A.nonneg i s) (Finset.mem_univ j)

theorem cellMass_le_col (A : CellMass P Q) (i : Fin m) (j : Fin n) : A.mass i j ≤ Q.width j := by
  rw [← A.col_sum j]
  exact Finset.single_le_sum (fun r _ => A.nonneg r j) (Finset.mem_univ i)

theorem cellMass_square_bound (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    (∑ i, ∑ j, A.mass i j^2) ≤ min (1/(m : ℝ)) (1/(n : ℝ)) := by
  have h (i : Fin m) (j : Fin n) : A.mass i j^2 ≤ A.mass i j * min (1/(m : ℝ)) (1/(n : ℝ)) := by
    rw [pow_two]
    apply mul_le_mul_of_nonneg_left _ (A.nonneg i j)
    exact le_min (by simpa only [IntervalPartition.width_uniform] using cellMass_le_row A i j)
      (by simpa only [IntervalPartition.width_uniform] using cellMass_le_col A i j)
  calc
    _ ≤ ∑ i, ∑ j, A.mass i j * min (1/(m : ℝ)) (1/(n : ℝ)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h i j))
    _ = _ := by simp_rw [← Finset.sum_mul]; rw [cellMass_total,one_mul]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
