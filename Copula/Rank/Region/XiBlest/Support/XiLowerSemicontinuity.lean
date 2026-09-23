import Copula.Rank.Region.XiBlest.Support.RowEnergyConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

variable {m : ℕ}

theorem rowMeanEnergy_continuous (P : IntervalPartition m) (C : Copula 2) : Continuous (rowMeanEnergy P C) := by
  have hc := C.continuous_cdf
  unfold rowMeanEnergy copulaRowMean
  fun_prop

theorem rowMeanEnergy_mem (P : IntervalPartition m) (C : Copula 2) (v : I) : rowMeanEnergy P C v ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (P.width_pos i).le (sq_nonneg _)
  · exact (copulaRowMean_energy_le P C v).trans (conditionalEnergy_mem C v).2

theorem rowMeanEnergy_integrable (P : IntervalPartition m) (C : Copula 2) : Integrable (rowMeanEnergy P C) :=
  Copula.integrable_continuous_unit volume (rowMeanEnergy_continuous P C)

/-- Predictor-bin averaging gives a lower approximation to xi, with no response binning. -/
noncomputable def rowMeanXi (P : IntervalPartition m) (C : Copula 2) : ℝ :=
  6*(∫ v : I, rowMeanEnergy P C v)-2

theorem rowMeanXi_le (P : IntervalPartition m) (C : Copula 2) : rowMeanXi P C ≤ C.chatterjeeXi := by
  have h := integral_mono (rowMeanEnergy_integrable P C) C.integrable_integral_conditionalCDF_sq
    (fun v => copulaRowMean_energy_le P C v)
  unfold rowMeanXi Copula.chatterjeeXi
  linarith

theorem rowMeanXi_tendsto (C : Copula 2) :
    Tendsto (fun k => rowMeanXi (IntervalPartition.uniform (k+1) (by omega)) C) atTop (𝓝 C.chatterjeeXi) := by
  have he := tendsto_integral_of_dominated_convergence (μ := (volume : Measure I)) (fun _ : I => (1 : ℝ))
    (fun k => (rowMeanEnergy_continuous (IntervalPartition.uniform (k+1) (by omega)) C).measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun k => Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rowMeanEnergy_mem _ C v).1]
      exact (rowMeanEnergy_mem _ C v).2)
    (Eventually.of_forall (rowMeanEnergy_tendsto C))
  exact (he.const_mul 6).sub_const 2

/-- A fixed predictor-bin energy is continuous under pointwise copula-CDF convergence. -/
theorem rowMeanXi_tendsto_of_cdf (P : IntervalPartition m) (C : ℕ → Copula 2) (D : Copula 2)
    (hC : ∀ u v : I, Tendsto (fun k => (C k).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v]))) :
    Tendsto (fun k => rowMeanXi P (C k)) atTop (𝓝 (rowMeanXi P D)) := by
  have hp (v : I) : Tendsto (fun k => rowMeanEnergy P (C k) v) atTop (𝓝 (rowMeanEnergy P D v)) := by
    unfold rowMeanEnergy copulaRowMean
    apply tendsto_finsetSum
    intro i _
    exact (((hC (P.point i.succ) v).sub (hC (P.point i.castSucc) v)).div_const (P.width i)).pow 2 |>.const_mul (P.width i)
  have he := tendsto_integral_of_dominated_convergence (μ := (volume : Measure I)) (fun _ : I => (1 : ℝ))
    (fun k => (rowMeanEnergy_continuous P (C k)).measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun k => Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rowMeanEnergy_mem P (C k) v).1]
      exact (rowMeanEnergy_mem P (C k) v).2)
    (Eventually.of_forall hp)
  exact (he.const_mul 6).sub_const 2

/-- Xi cannot jump upward at a pointwise CDF limit. Singular copulas are included. -/
theorem xi_le_limit_of_cdf (C : ℕ → Copula 2) (D : Copula 2) (x : ℝ)
    (hC : ∀ u v : I, Tendsto (fun k => (C k).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v])))
    (hx : Tendsto (fun k => (C k).chatterjeeXi) atTop (𝓝 x)) : D.chatterjeeXi ≤ x := by
  apply le_of_tendsto (rowMeanXi_tendsto D)
  filter_upwards with n
  exact le_of_tendsto_of_tendsto (rowMeanXi_tendsto_of_cdf _ C D hC) hx
    (Eventually.of_forall fun k => rowMeanXi_le _ (C k))

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
