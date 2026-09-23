import Copula.Rank.Region.XiBlest.Support.PatchworkTau
import Copula.Rank.Region.XiBlest.Support.PartitionMoments
import Copula.Rank.Region.XiBlest.Support.ConstantTrace

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- The source Xi matrix has 2 below the diagonal, 1 on it and 0 above it. -/
noncomputable def checkerXiMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i r => if r < i then 2 else if r=i then 1 else 0

private theorem checkerXiMatrix_eq (n : ℕ) (i r : Fin n) : checkerXiMatrix n i r=2*orderHalf r i := by
  unfold checkerXiMatrix orderHalf
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

private theorem checkerXiMatrix_boundary (n : ℕ) :
    checkerXiMatrix n+(checkerXiMatrix n)ᵀ = (2 : ℝ) • constantOneMatrix (Fin n) := by
  ext i r
  simp only [checkerXiMatrix,constantOneMatrix,Matrix.add_apply,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,mul_one]
  rcases lt_trichotomy r i with h | rfl | h
  · simp [h,not_lt_of_gt h,ne_of_gt h]
  · norm_num
  · simp [h,not_lt_of_gt h,ne_of_gt h]

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchwork_tau_correction (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).kendallTau = A.checkerboard.kendallTau +
      ∑ i, ∑ j, A.mass i j^2*(C i j).kendallTau := by
  rw [patchwork_tau_formula,CellMass.checkerboard,patchwork_tau_formula]
  simp only [Copula.kendallTau_independence,mul_zero,Finset.sum_const_zero,add_zero]

theorem rectangular_checkerboard_tau (A : CellMass P Q) :
    A.checkerboard.kendallTau = 1-Matrix.trace
      (checkerXiMatrix m * Matrix.of A.mass * checkerXiMatrix n * (Matrix.of A.mass)ᵀ) := by
  let D : Matrix (Fin m) (Fin n) ℝ := Matrix.of A.mass
  have ht := constant_trace_identity (checkerXiMatrix m) (checkerXiMatrix n) D
    (checkerXiMatrix_boundary m) (checkerXiMatrix_boundary n) (cellMass_total A)
  have hs : Matrix.trace (checkerXiMatrix m * D * (checkerXiMatrix n)ᵀ * Dᵀ) =
      4*(∑ i, ∑ j, ∑ r, ∑ s, A.mass i j*A.mass r s*orderHalf r i*orderHalf s j) := by
    rw [trace_tensor_contraction]
    simp only [checkerXiMatrix_eq,D,Matrix.of_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [CellMass.checkerboard,patchwork_tau_formula]
  simp only [Copula.kendallTau_independence,mul_zero,Finset.sum_const_zero,add_zero]
  rw [← hs]
  linarith

theorem cellMass_frobenius (A : CellMass P Q) :
    Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) = ∑ i, ∑ j, A.mass i j^2 := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,pow_two]
  rw [Finset.sum_comm]

theorem rectangular_checkMin_tau (A : CellMass P Q) :
    A.checkMin.kendallTau = A.checkerboard.kendallTau + Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) := by
  rw [CellMass.checkMin,patchwork_tau_correction,cellMass_frobenius]
  simp only [Copula.kendallTau_comonotonic,mul_one]

theorem rectangular_checkW_tau (A : CellMass P Q) :
    A.checkW.kendallTau = A.checkerboard.kendallTau - Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) := by
  rw [CellMass.checkW,patchwork_tau_correction,cellMass_frobenius]
  simp only [Copula.kendallTau_countermonotonic,mul_neg,mul_one,Finset.sum_neg_distrib,sub_eq_add_neg]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
