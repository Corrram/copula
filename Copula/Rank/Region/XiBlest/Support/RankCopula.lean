import Copula.Rank.Region.XiBlest.Support.CheckerboardConvergence

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Fine empirical checkerboard from two rank permutations. Ranks are zero based. -/
noncomputable def rankCellMass (n : ℕ) (hn : 0<n) (rx ry : Equiv.Perm (Fin n)) :
    CellMass (IntervalPartition.uniform n hn) (IntervalPartition.uniform n hn) where
  mass i j := if ry (rx.symm i)=j then 1/(n : ℝ) else 0
  nonneg i j := by split_ifs <;> positivity
  row_sum i := by simp [IntervalPartition.width_uniform]
  col_sum j := by
    have he (i : Fin n) : ry (rx.symm i)=j ↔ i=rx (ry.symm j) := by
      constructor
      · intro h
        simpa only [Equiv.apply_symm_apply] using congrArg rx (ry.injective (h.trans (ry.apply_symm_apply j).symm))
      · intro h
        simp [h]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,IntervalPartition.width_uniform]

noncomputable def rankCopula (n : ℕ) (hn : 0<n) (rx ry : Equiv.Perm (Fin n)) : Copula 2 :=
  (rankCellMass n hn rx ry).checkerboard

theorem rankCopula_cdf (n : ℕ) (hn : 0<n) (rx ry : Equiv.Perm (Fin n)) (u v : I) :
    (rankCopula n hn rx ry).cdf ![u,v] = (1/(n : ℝ))*∑ k,
      ((IntervalPartition.uniform n hn).coord (rx k) u : ℝ)*((IntervalPartition.uniform n hn).coord (ry k) v : ℝ) := by
  rw [rankCopula,CellMass.cdf_checkerboard]
  simp only [rankCellMass,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [← Finset.mul_sum]
  congr 1
  have h := Equiv.sum_comp rx (fun i =>
    ((IntervalPartition.uniform n hn).coord i u : ℝ)*((IntervalPartition.uniform n hn).coord (ry (rx.symm i)) v : ℝ))
  simpa only [Equiv.symm_apply_apply] using h.symm

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
