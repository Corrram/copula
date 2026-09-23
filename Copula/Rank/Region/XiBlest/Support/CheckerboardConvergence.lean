import Copula.Rank.Region.XiBlest.Support.CheckerboardInterpolationError
import Copula.Rank.Region.XiBlest.Support.CheckerboardEstimator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Population checkerboard conditional energies converge at every response threshold. -/
theorem checkerboard_energy_tendsto (C : Copula 2) (v : I) :
    Tendsto (fun k => conditionalEnergy (C.cellMass (IntervalPartition.uniform (k+1) (by omega))
      (IntervalPartition.uniform (k+1) (by omega))).checkerboard v) atTop (𝓝 (conditionalEnergy C v)) := by
  have he : Tendsto (fun k => conditionalEnergy (C.cellMass (IntervalPartition.uniform (k+1) (by omega))
      (IntervalPartition.uniform (k+1) (by omega))).checkerboard v-
      rowMeanEnergy (IntervalPartition.uniform (k+1) (by omega)) C v) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq,sub_zero]
    apply squeeze_zero (fun _ => abs_nonneg _) (fun k => checkerboard_energy_interpolation_error _ C k v)
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simpa only [mul_one_div,mul_zero] using hh
  have hh := he.add (rowMeanEnergy_tendsto C v)
  simpa only [sub_add_cancel,zero_add] using hh

/-- Every copula, including singular laws, is approximated in xi by its population
checkerboards. This is distinct from consistency of empirical checkerboards. -/
theorem checkerboard_xi_tendsto (C : Copula 2) :
    Tendsto (fun k => (C.cellMass (IntervalPartition.uniform (k+1) (by omega))
      (IntervalPartition.uniform (k+1) (by omega))).checkerboard.chatterjeeXi) atTop (𝓝 C.chatterjeeXi) := by
  have he := tendsto_integral_of_dominated_convergence (μ := (volume : Measure I)) (fun _ : I => (1 : ℝ))
    (fun k => (conditionalEnergy_measurable (C.cellMass (IntervalPartition.uniform (k+1) (by omega))
      (IntervalPartition.uniform (k+1) (by omega))).checkerboard).aestronglyMeasurable)
    (integrable_const 1)
    (fun k => Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (conditionalEnergy_mem _ v).1]
      exact (conditionalEnergy_mem _ v).2)
    (Filter.Eventually.of_forall (checkerboard_energy_tendsto C))
  exact (he.const_mul 6).sub_const 2

/-- CDF approximation at a rate faster than the reciprocal grid order implies xi
consistency after rebinning. The input rate remains an explicit hypothesis. -/
theorem checkerboard_xi_tendsto_of_cdf_error (C : Copula 2) (D : ℕ → Copula 2)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (ε : ℕ → ℝ)
    (hCDF : ∀ᶠ k in atTop, ∀ u v, |(D k).cdf ![u,v]-C.cdf ![u,v]| ≤ ε k)
    (hε : Tendsto (fun k => ((N k : ℝ)+1)*ε k) atTop (𝓝 0)) :
    Tendsto (fun k => ((D k).cellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega))).checkerboard.chatterjeeXi) atTop (𝓝 C.chatterjeeXi) := by
  have he : Tendsto (fun k =>
      ((D k).cellMass (IntervalPartition.uniform (N k+1) (by omega))
        (IntervalPartition.uniform (N k+1) (by omega))).checkerboard.chatterjeeXi-
      (C.cellMass (IntervalPartition.uniform (N k+1) (by omega))
        (IntervalPartition.uniform (N k+1) (by omega))).checkerboard.chatterjeeXi) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq,sub_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (hCDF.mono fun k hk => checkerboard_xi_stability (D k) C _ _ (ε k) hk)
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_zero] using hε.const_mul 24
  have hh := he.add ((checkerboard_xi_tendsto C).comp hN)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hh

theorem checkerboardEstimator_tendsto_of_cdf_error (C : Copula 2) (D : ℕ → Copula 2)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (ε : ℕ → ℝ)
    (hCDF : ∀ᶠ k in atTop, ∀ u v, |(D k).cdf ![u,v]-C.cdf ![u,v]| ≤ ε k)
    (hε : Tendsto (fun k => ((N k : ℝ)+1)*ε k) atTop (𝓝 0)) :
    Tendsto (fun k => checkerboardEstimator ((D k).cellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega)))) atTop (𝓝 C.chatterjeeXi) :=
  (checkerboardEstimator_tendsto_iff N hN _ _).mpr
    (checkerboard_xi_tendsto_of_cdf_error C D N hN ε hCDF hε)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
