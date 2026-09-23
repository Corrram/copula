import Copula.Rank.Region.XiBlest.Support.RankOneTrace

open Matrix
open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

def constantOneMatrix (α : Type*) : Matrix α α ℝ := Matrix.of fun _ _ => 1

/-- The checkerboard trace identity uses all-ones symmetric parts and total mass one. -/
theorem constant_trace_identity {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) (D : Matrix α β ℝ)
    (hA : A+Aᵀ = (2 : ℝ) • constantOneMatrix α)
    (hB : B+Bᵀ = (2 : ℝ) • constantOneMatrix β) (hD : (∑ i, ∑ j, D i j)=1) :
    Matrix.trace (A*D*B*Dᵀ) + Matrix.trace (A*D*Bᵀ*Dᵀ) = 2 := by
  let X : Matrix α α ℝ := D * constantOneMatrix β * Dᵀ
  have hJ : (constantOneMatrix β)ᵀ=constantOneMatrix β := rfl
  have hX : Xᵀ=X := by simp only [X,Matrix.transpose_mul,hJ,Matrix.transpose_transpose,Matrix.mul_assoc]
  have hs : Matrix.trace (Aᵀ*X) = Matrix.trace (A*X) := by
    rw [← Matrix.trace_transpose,Matrix.transpose_mul,hX,Matrix.transpose_transpose,Matrix.trace_mul_comm]
  have hb : Matrix.trace (A*D*B*Dᵀ) + Matrix.trace (A*D*Bᵀ*Dᵀ) =
      2 * Matrix.trace (A*X) := by
    rw [← Matrix.trace_add,← Matrix.add_mul,← Matrix.mul_add,hB]
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]
    congr 1
    simp only [X,Matrix.mul_assoc]
  have ha : 2 * Matrix.trace (A*X) = 2 * Matrix.trace (constantOneMatrix α * X) := by
    have h := congrArg (fun M : Matrix α α ℝ => Matrix.trace (M*X)) hA
    simp only [Matrix.add_mul,Matrix.trace_add,hs,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul] at h
    linarith
  have hXval (r i : α) : X r i = (∑ j, D r j)*(∑ s, D i s) := by
    simp only [X,Matrix.mul_apply,constantOneMatrix,Matrix.of_apply,mul_one,Matrix.transpose_apply]
    rw [← Finset.mul_sum]
  rw [hb,ha]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,constantOneMatrix,Matrix.of_apply,one_mul,hXval]
  simp only [← Finset.sum_mul,← Finset.mul_sum,hD,mul_one]

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
