import Copula.Rank.Region.XiBlest.Support.PatchworkXi
import Copula.Rank.Region.XiBlest.Support.CheckerboardXiMatrix
import Copula.Rank.Region.XiBlest.Support.CellMassBounds

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m n : ℕ}

theorem rectangular_checkerboard_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkerboard.chatterjeeXi = (6*(m : ℝ)/(n : ℝ))*
      Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass * checkerboardXiMatrix n)-2 := by
  rw [checkerboardXi_trace,CellMass.checkerboard,patchwork_xi_formula]
  simp only [Copula.chatterjeeXi_independence,zero_add,IntervalPartition.width_uniform,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  ring

theorem uniform_patchwork_xi_correction (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn))
    (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * ∑ i, ∑ j, A.mass i j^2*(C i j).chatterjeeXi := by
  rw [patchwork_xi_correction]
  simp only [IntervalPartition.width_uniform]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp

theorem rectangular_perfect_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn))
    (C : Fin m → Fin n → Copula 2) (hC : ∀ i j, (C i j).chatterjeeXi=1) :
    (A.patchwork C).chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) := by
  rw [uniform_patchwork_xi_correction hm hn,cellMass_frobenius]
  simp only [hC,mul_one]

theorem rectangular_checkMin_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkMin.chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  rectangular_perfect_xi hm hn A _ (fun _ _ => Copula.chatterjeeXi_comonotonic)

theorem rectangular_checkW_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkW.chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  rectangular_perfect_xi hm hn A _ (fun _ _ => Copula.chatterjeeXi_countermonotonic)

/-- Corollary 3.4, in fact valid for every choice of local copulas. -/
theorem rectangular_xi_error_bound (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn))
    (C : Fin m → Fin n → Copula 2) :
    |(A.patchwork C).chatterjeeXi-A.checkerboard.chatterjeeXi| ≤
      if m ≤ n then (m : ℝ)/(n : ℝ)^2 else 1/(n : ℝ) := by
  have hm' : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnon : 0 ≤ ∑ i, ∑ j, A.mass i j^2*(C i j).chatterjeeXi :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (C i j).chatterjeeXi_nonneg))
  have hsum : (∑ i, ∑ j, A.mass i j^2*(C i j).chatterjeeXi) ≤ ∑ i, ∑ j, A.mass i j^2 :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (C i j).chatterjeeXi_le_one (sq_nonneg (A.mass i j))))
  rw [uniform_patchwork_xi_correction hm hn,add_sub_cancel_left,abs_of_nonneg (mul_nonneg (div_nonneg hm'.le hn'.le) hnon)]
  have hb := cellMass_square_bound hm hn A
  split_ifs
  · calc
      _ ≤ (m : ℝ)/(n : ℝ)*(1/(n : ℝ)) := mul_le_mul_of_nonneg_left
        (hsum.trans (hb.trans (min_le_right _ _))) (div_nonneg hm'.le hn'.le)
      _ = _ := by ring
  · calc
      _ ≤ (m : ℝ)/(n : ℝ)*(1/(m : ℝ)) := mul_le_mul_of_nonneg_left
        (hsum.trans (hb.trans (min_le_left _ _))) (div_nonneg hm'.le hn'.le)
      _ = _ := by field_simp

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
