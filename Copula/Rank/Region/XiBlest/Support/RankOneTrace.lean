import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open Matrix
open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- The trace identity behind the Bernstein Kendall formula; only the symmetric boundary parts matter. -/
theorem boundary_trace_identity {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) (D : Matrix α β ℝ) (a : α) (b : β)
    (hA : A+Aᵀ = (2 : ℝ) • Matrix.single a a (1 : ℝ))
    (hB : B+Bᵀ = (2 : ℝ) • Matrix.single b b (1 : ℝ)) (hD : D a b=1) :
    Matrix.trace (A*D*B*Dᵀ) + Matrix.trace (A*D*Bᵀ*Dᵀ) = 2 := by
  let X : Matrix α α ℝ := D * Matrix.single b b (1 : ℝ) * Dᵀ
  have hX : Xᵀ=X := by simp [X,Matrix.transpose_mul,Matrix.mul_assoc]
  have hs : Matrix.trace (Aᵀ*X) = Matrix.trace (A*X) := by
    rw [← Matrix.trace_transpose,Matrix.transpose_mul,hX,Matrix.transpose_transpose,Matrix.trace_mul_comm]
  have hb : Matrix.trace (A*D*B*Dᵀ) + Matrix.trace (A*D*Bᵀ*Dᵀ) =
      2 * Matrix.trace (A*X) := by
    rw [← Matrix.trace_add,← Matrix.add_mul,← Matrix.mul_add,hB]
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]
    congr 1
    simp only [X,Matrix.mul_assoc]
  have ha : 2 * Matrix.trace (A*X) = 2 * Matrix.trace (Matrix.single a a (1 : ℝ) * X) := by
    have h := congrArg (fun M : Matrix α α ℝ => Matrix.trace (M*X)) hA
    simp only [Matrix.add_mul,Matrix.trace_add,hs,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul] at h
    linarith
  rw [hb,ha]
  rw [Matrix.trace_single_mul]
  simp [X,Matrix.mul_apply,Matrix.single,Matrix.transpose_apply,ite_and,hD]

theorem trace_tensor_contraction {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) (D : Matrix α β ℝ) :
    Matrix.trace (A*D*Bᵀ*Dᵀ) =
      ∑ i, ∑ j, ∑ r, ∑ s, D i j * D r s * A i r * B j s := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
