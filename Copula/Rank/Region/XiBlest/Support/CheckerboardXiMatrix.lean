import Copula.Rank.Region.XiBlest.Support.PatchworkRow
import Copula.Rank.Region.XiBlest.Support.RectangularTau

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def strictUpperMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i < j then 1 else 0

/-- The exact source matrix T T^T + T^T + I/3. -/
noncomputable def checkerboardXiMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  strictUpperMatrix n * (strictUpperMatrix n)ᵀ + (strictUpperMatrix n)ᵀ + (1/3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)

theorem trace_transpose_self_sum {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Dᵀ*D) = ∑ i, ∑ j, D i j^2 := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,pow_two]
  rw [Finset.sum_comm]

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem mass_mul_strictUpper (A : CellMass P Q) (i : Fin m) (j : Fin n) :
    (Matrix.of A.mass * strictUpperMatrix n) i j = cellPrefix A i j := by
  simp only [Matrix.mul_apply,strictUpperMatrix,Matrix.of_apply,mul_ite,mul_one,mul_zero,cellPrefix]

theorem checkerboardXi_trace (A : CellMass P Q) :
    Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass * checkerboardXiMatrix n) =
      ∑ i, ∑ j, ((cellPrefix A i j)^2+cellPrefix A i j*A.mass i j+A.mass i j^2/3) := by
  let D := Matrix.of A.mass
  let T := strictUpperMatrix n
  have h1 : Matrix.trace (Dᵀ*D*(T*Tᵀ)) = ∑ i, ∑ j, (cellPrefix A i j)^2 := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_comm _ Tᵀ]
    have he : Tᵀ*(Dᵀ*D*T)=(D*T)ᵀ*(D*T) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    rw [he,trace_transpose_self_sum]
    simp only [D,T,mass_mul_strictUpper]
  have h2 : Matrix.trace (Dᵀ*D*Tᵀ) = ∑ i, ∑ j, cellPrefix A i j*A.mass i j := by
    rw [Matrix.trace_mul_comm (Dᵀ*D) Tᵀ]
    have he : Tᵀ*(Dᵀ*D)=(D*T)ᵀ*D := by rw [Matrix.transpose_mul,Matrix.mul_assoc]
    rw [he]
    change (∑ j, ∑ i, (D*T) i j * D i j) = _
    rw [Finset.sum_comm]
    simp only [D,T,mass_mul_strictUpper,Matrix.of_apply]
  change Matrix.trace (Dᵀ*D*(T*Tᵀ+Tᵀ+(1/3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) = _
  rw [Matrix.mul_add,Matrix.mul_add,Matrix.trace_add,Matrix.trace_add,h1,h2,
    Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul,smul_eq_mul,trace_transpose_self_sum]
  simp only [D,Matrix.of_apply,Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
