/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gaussian
import Copula.Sklar.Continuous

/-! # Gaussian scale mixture copulas

A centered Gaussian vector, multiplied by an independent, almost surely positive
scalar, has atomless marginals even when its correlation matrix is singular.
Its unique Sklar copula is therefore available without a density or moments.
This is a useful subclass of elliptical distributions, not a characterization
of every elliptical distribution.
-/

open MeasureTheory Set Filter

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The law of `s(T) • Z`, with independent `T ~ μ` and `Z ~ N(0,R)`. -/
noncomputable def gaussianScaleMixtureLaw (R : Matrix (Fin d) (Fin d) ℝ)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) : ProbabilityMeasure (Fin d → ℝ) :=
  ProbabilityMeasure.map
    (⟨(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).prod μ.toMeasure,
      inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d) × ℝ))
    (fun p i => s p.2 * p.1 i)

theorem atomless_gaussianScaleMixtureLaw_marginal
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) (i : Fin d) :
    NullSingletonClass (marginal (gaussianScaleMixtureLaw R μ s) i) := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).prod μ.toMeasure
  have hmarg : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map
      (fun x => x i) = gaussianReal 0 1 := by
    have h := (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin d))) hR (i := i)).map_eq
    have hz : (0 : EuclideanSpace ℝ (Fin d)) i = (0 : ℝ) := rfl
    rw [hz, hdiag, Real.toNNReal_one] at h
    exact h
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin d) × ℝ => s p.2 * p.1 i) := by
    fun_prop
  have he : marginal (gaussianScaleMixtureLaw R μ s) i =
      P.map (fun p => s p.2 * p.1 i) :=
    Measure.map_map (measurable_pi_apply i) (Measurable.of_eval fun j => by fun_prop)
  constructor
  intro a
  rw [he, Measure.map_apply hm (measurableSet_singleton a)]
  change P {p | s p.2 * p.1 i = a} = 0
  rw [Measure.prod_apply_symm (measurableSet_eq_fun hm measurable_const)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hpos] with t ht
  have heq : {x : EuclideanSpace ℝ (Fin d) | s t * x i = a} =
      (fun x => x i) ⁻¹' {a / s t} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    rw [eq_div_iff ht.ne', mul_comm]
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)
    {x | s t * x i = a} = 0
  rw [heq, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    hmarg, measure_singleton]

theorem continuous_gaussianScaleMixtureLaw_marginal
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) (i : Fin d) :
    Continuous (ProbabilityTheory.cdf (marginal (gaussianScaleMixtureLaw R μ s) i)) := by
  let : NullSingletonClass (marginal (gaussianScaleMixtureLaw R μ s) i) :=
    atomless_gaussianScaleMixtureLaw_marginal R hR hdiag μ s hs hpos i
  exact continuous_cdf_of_atomless _

/-- A copula from an independent positive Gaussian scale mixture. -/
noncomputable def gaussianScaleMixture
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) : Copula d :=
  ofContinuousMarginals (gaussianScaleMixtureLaw R μ s)
    (continuous_gaussianScaleMixtureLaw_marginal R hR hdiag μ s hs hpos)

theorem isSklarCopula_gaussianScaleMixture
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) :
    IsSklarCopula (gaussianScaleMixtureLaw R μ s)
      (gaussianScaleMixture R hR hdiag μ s hs hpos) :=
  isSklarCopula_ofContinuousMarginals _ _

end ProbabilityTheory.Copula
