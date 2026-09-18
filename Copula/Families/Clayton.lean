/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Sklar.Continuous
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi

/-! # The positive-parameter Clayton construction

Take independent rate-one exponentials `E i` and an independent gamma variable
`G` with shape `1/θ` and rate one. The joint law of `-E i / G` has atomless
marginals; its unique Sklar copula is the gamma-frailty construction of Clayton.
This module supplies the stochastic construction and its Sklar factorization.
The closed-form Archimedean CDF is not yet proved here.
-/

open MeasureTheory Set Filter

namespace ProbabilityTheory.Copula

private noncomputable def frailtySource (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ProbabilityMeasure ((Fin d → ℝ) × ℝ) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (gammaMeasure θ⁻¹ 1) :=
    isProbabilityMeasure_gammaMeasure (inv_pos.mpr hθ) zero_lt_one
  exact ⟨(Measure.pi fun _ : Fin d => expMeasure 1).prod (gammaMeasure θ⁻¹ 1), inferInstance⟩

/-- The joint negative exponential/gamma ratios used in the Clayton construction. -/
noncomputable def claytonLaw (d : ℕ) (θ : ℝ) (hθ : 0 < θ) : ProbabilityMeasure (Fin d → ℝ) :=
  (frailtySource d θ hθ).map (fun p i => -(p.1 i / p.2))

theorem atomless_claytonLaw_marginal (d : ℕ) (θ : ℝ) (hθ : 0 < θ) (i : Fin d) :
    NullSingletonClass (marginal (claytonLaw d θ hθ) i) := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  let : IsProbabilityMeasure (gammaMeasure θ⁻¹ 1) :=
    isProbabilityMeasure_gammaMeasure (inv_pos.mpr hθ) zero_lt_one
  let : NullSingletonClass (expMeasure 1) := by
    unfold expMeasure gammaMeasure
    infer_instance
  let : NullSingletonClass (gammaMeasure θ⁻¹ 1) := by
    unfold gammaMeasure
    infer_instance
  let P := (Measure.pi fun _ : Fin d => expMeasure 1).prod (gammaMeasure θ⁻¹ 1)
  have hs : Measurable (fun p : (Fin d → ℝ) × ℝ => -(p.1 i / p.2)) := by fun_prop
  have hm : marginal (claytonLaw d θ hθ) i = P.map (fun p => -(p.1 i / p.2)) := by
    exact Measure.map_map (measurable_pi_apply i) (by fun_prop)
  constructor
  intro a
  rw [hm, Measure.map_apply hs (measurableSet_singleton a)]
  change P {p | -(p.1 i / p.2) = a} = 0
  rw [Measure.prod_apply_symm (measurableSet_eq_fun hs measurable_const)]
  apply lintegral_eq_zero_of_ae_zero
  filter_upwards [(gammaMeasure θ⁻¹ 1).ae_ne 0] with t ht
  have he : {x : Fin d → ℝ | -(x i / t) = a} = (fun x => x i) ⁻¹' {-a * t} := by
    ext x
    simp [neg_eq_iff_eq_neg, div_eq_iff ht]
  change (Measure.pi fun _ : Fin d => expMeasure 1) {x | -(x i / t) = a} = 0
  rw [he, ← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _),
    (MeasureTheory.measurePreserving_eval (fun _ : Fin d => expMeasure 1) i).map_eq,
    measure_singleton]

theorem continuous_claytonLaw_marginal (d : ℕ) (θ : ℝ) (hθ : 0 < θ) (i : Fin d) :
    Continuous (ProbabilityTheory.cdf (marginal (claytonLaw d θ hθ) i)) := by
  let : NullSingletonClass (marginal (claytonLaw d θ hθ) i) := atomless_claytonLaw_marginal d θ hθ i
  exact continuous_cdf_of_atomless _

/-- The positive-parameter Clayton copula, constructed from gamma frailty. -/
noncomputable def clayton (d : ℕ) (θ : ℝ) (hθ : 0 < θ) : Copula d :=
  ofContinuousMarginals (claytonLaw d θ hθ) (continuous_claytonLaw_marginal d θ hθ)

theorem isSklarCopula_clayton (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    IsSklarCopula (claytonLaw d θ hθ) (clayton d θ hθ) :=
  isSklarCopula_ofContinuousMarginals _ _

end ProbabilityTheory.Copula
