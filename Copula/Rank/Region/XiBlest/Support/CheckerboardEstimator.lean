import Copula.Rank.Region.XiBlest.Support.RectangularXi
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory ProbabilityTheory Set Filter Matrix
open Copula
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def checkerboardEstimator {n : ℕ}
    (A : CellMass (IntervalPartition.uniform (n+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega))) : ℝ :=
  6*Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass * checkerboardXiMatrix (n+1)) +
    Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass)/2-2

variable {n : ℕ}
variable (A : CellMass (IntervalPartition.uniform (n+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega)))

theorem checkerboardEstimator_eq_average :
    checkerboardEstimator A = (A.checkerboard.chatterjeeXi+A.checkMin.chatterjeeXi)/2 := by
  rw [rectangular_checkMin_xi (by omega) (by omega),rectangular_checkerboard_xi (by omega) (by omega)]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_self hn]
  unfold checkerboardEstimator
  field_simp
  ring

theorem checkerboardEstimator_mem : checkerboardEstimator A ∈ Icc (0 : ℝ) 1 := by
  rw [checkerboardEstimator_eq_average]
  constructor
  · linarith [A.checkerboard.chatterjeeXi_nonneg,A.checkMin.chatterjeeXi_nonneg]
  · linarith [A.checkerboard.chatterjeeXi_le_one,A.checkMin.chatterjeeXi_le_one]

theorem checkerboardEstimator_correction :
    checkerboardEstimator A-A.checkerboard.chatterjeeXi =
      Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass)/2 := by
  rw [checkerboardEstimator_eq_average,rectangular_checkMin_xi (by omega) (by omega),
    div_self (show ((n+1 : ℕ) : ℝ) ≠ 0 by positivity),one_mul]
  ring

theorem checkerboardEstimator_correction_bounds :
    0 ≤ checkerboardEstimator A-A.checkerboard.chatterjeeXi ∧
      checkerboardEstimator A-A.checkerboard.chatterjeeXi ≤ (1/((n : ℝ)+1))/2 := by
  rw [checkerboardEstimator_correction,cellMass_frobenius]
  constructor
  · positivity
  · have h := cellMass_square_bound (by omega) (by omega) A
    simp only [min_self,Nat.cast_add,Nat.cast_one] at h
    exact div_le_div_of_nonneg_right h (by norm_num)

/-- The finite-sample correction vanishes for every refining sequence of square matrices. -/
theorem checkerboardEstimator_correction_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (A : ∀ k, CellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega))) :
    Tendsto (fun k => checkerboardEstimator (A k)-(A k).checkerboard.chatterjeeXi) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => (checkerboardEstimator_correction_bounds (A k)).1)
    (fun k => (checkerboardEstimator_correction_bounds (A k)).2)
  simpa only [zero_div,Function.comp_def] using
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hN).div_const 2

/-- Conditional transfer lemma; the statistical consistency hypothesis remains explicit. -/
theorem checkerboardEstimator_tendsto_iff (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (A : ∀ k, CellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega))) (l : ℝ) :
    Tendsto (fun k => checkerboardEstimator (A k)) atTop (𝓝 l) ↔
      Tendsto (fun k => (A k).checkerboard.chatterjeeXi) atTop (𝓝 l) := by
  have hc := checkerboardEstimator_correction_tendsto N hN A
  constructor
  · intro h
    have ht := h.sub hc
    simpa only [sub_sub_cancel,sub_zero] using ht
  · intro h
    have ht := hc.add h
    simpa only [sub_add_cancel,zero_add] using ht

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
