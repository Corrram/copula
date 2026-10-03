/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Elliptical.ScaleMixtureConcordance
import Copula.RandomVariable.Symmetry

/-! # Symmetries of bivariate Gaussian scale mixture copulas

A bivariate Gaussian scale mixture `S · (G₁, G₂)` with `G ~ N(0, !![1, r; r, 1])` has a law that
is invariant under swapping the coordinates and under `x ↦ −x`. By the random-vector criteria of
`Copula.RandomVariable.Symmetry` (Nelsen 2006, §2.7), its copula is exchangeable and radially
symmetric. This applies to the Student-t, Cauchy, variance-gamma, Laplace, slash and
normal–lognormal copulas.

## Main results
* `gaussianScaleMixtureLaw_corrMatrix_eq`: the mixture law is the law of `s(T) · (X, Y)` with
  `(X, Y) ~ bivariateNormal r` independent of `T`.
* `isExchangeable_gaussianScaleMixture`, `isRadiallySymmetric_gaussianScaleMixture`, and the
  Student-t instances.
-/

open MeasureTheory Set Real
open scoped unitInterval ENNReal NNReal

namespace ProbabilityTheory.Copula

/-- The coordinates of `N(0, corrMatrix r)` have the law `bivariateNormal r`. -/
theorem map_multivariateGaussian_corrMatrix {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).map
      (fun g => (g 0, g 1)) = bivariateNormal r :=
  eq_bivariateNormal_of_linear_laws hr fun a b => by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact map_linear_multivariateGaussian_corrMatrix hr a b

/-- The scaling map `((x, y), t) ↦ (s(t) x, s(t) y)`. -/
noncomputable def scalePair (s : ℝ → ℝ) (p : (ℝ × ℝ) × ℝ) : Fin 2 → ℝ :=
  ![s p.2 * p.1.1, s p.2 * p.1.2]

theorem measurable_scalePair {s : ℝ → ℝ} (hs : Measurable s) : Measurable (scalePair s) := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact (hs.comp measurable_snd).mul (measurable_fst.comp measurable_fst)
  · exact (hs.comp measurable_snd).mul (measurable_snd.comp measurable_fst)

/-- The bivariate Gaussian scale mixture law, written with the explicit bivariate normal law. -/
theorem gaussianScaleMixtureLaw_corrMatrix_eq {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) {s : ℝ → ℝ} (hs : Measurable s) :
    (gaussianScaleMixtureLaw (corrMatrix r) μ s).toMeasure =
      ((bivariateNormal r).prod μ.toMeasure).map (scalePair s) := by
  change ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).prod
    μ.toMeasure).map (fun p i => s p.2 * p.1 i) = _
  rw [← map_multivariateGaussian_corrMatrix hr, ← Measure.map_id (μ := μ.toMeasure),
    Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    Measure.map_map (measurable_scalePair hs) (by fun_prop), Measure.map_id]
  congr 1
  funext p i
  fin_cases i <;> rfl

/-- A bivariate Gaussian scale mixture law is exchangeable. -/
theorem gaussianScaleMixtureLaw_map_swapCoord {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) {s : ℝ → ℝ} (hs : Measurable s) :
    (gaussianScaleMixtureLaw (corrMatrix r) μ s).map swapCoord =
      gaussianScaleMixtureLaw (corrMatrix r) μ s := by
  apply Subtype.ext
  change (gaussianScaleMixtureLaw (corrMatrix r) μ s).toMeasure.map swapCoord =
    (gaussianScaleMixtureLaw (corrMatrix r) μ s).toMeasure
  rw [gaussianScaleMixtureLaw_corrMatrix_eq hr μ hs,
    Measure.map_map measurable_swapCoord (measurable_scalePair hs)]
  calc ((bivariateNormal r).prod μ.toMeasure).map (swapCoord ∘ scalePair s)
      = ((bivariateNormal r).prod μ.toMeasure).map (scalePair s ∘ Prod.map Prod.swap id) := by
        congr 1
        funext p i
        fin_cases i <;> rfl
    _ = (((bivariateNormal r).prod μ.toMeasure).map (Prod.map Prod.swap id)).map
          (scalePair s) :=
        (Measure.map_map (measurable_scalePair hs) (by fun_prop)).symm
    _ = ((bivariateNormal r).prod μ.toMeasure).map (scalePair s) := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, bivariateNormal_map_swap hr,
          Measure.map_id]

/-- A bivariate Gaussian scale mixture law is symmetric about the origin. -/
theorem gaussianScaleMixtureLaw_map_reflectAbout {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) {s : ℝ → ℝ} (hs : Measurable s) :
    (gaussianScaleMixtureLaw (corrMatrix r) μ s).map (reflectAbout 0 0) =
      gaussianScaleMixtureLaw (corrMatrix r) μ s := by
  have hrefl : Measurable (reflectAbout 0 0) :=
    measurable_coordMap (Fin.forall_fin_two.2 ⟨(strictAnti_two_mul_sub 0).antitone.measurable,
      (strictAnti_two_mul_sub 0).antitone.measurable⟩)
  apply Subtype.ext
  change (gaussianScaleMixtureLaw (corrMatrix r) μ s).toMeasure.map (reflectAbout 0 0) =
    (gaussianScaleMixtureLaw (corrMatrix r) μ s).toMeasure
  rw [gaussianScaleMixtureLaw_corrMatrix_eq hr μ hs,
    Measure.map_map hrefl (measurable_scalePair hs)]
  calc ((bivariateNormal r).prod μ.toMeasure).map (reflectAbout 0 0 ∘ scalePair s)
      = ((bivariateNormal r).prod μ.toMeasure).map
          (scalePair s ∘ Prod.map (fun q : ℝ × ℝ => (-q.1, -q.2)) id) := by
        congr 1
        funext p i
        fin_cases i <;>
          simp [scalePair, reflectAbout, coordMap]
    _ = (((bivariateNormal r).prod μ.toMeasure).map
          (Prod.map (fun q : ℝ × ℝ => (-q.1, -q.2)) id)).map (scalePair s) :=
        (Measure.map_map (measurable_scalePair hs) (by fun_prop)).symm
    _ = ((bivariateNormal r).prod μ.toMeasure).map (scalePair s) := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, bivariateNormal_map_neg hr,
          Measure.map_id]

/-- Bivariate Gaussian scale mixture copulas are exchangeable. -/
theorem isExchangeable_gaussianScaleMixture {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) :
    (gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) μ s hs
      hpos).IsExchangeable :=
  isExchangeable_of_map_swapCoord_eq
    (continuous_gaussianScaleMixtureLaw_marginal _ (posSemidef_corrMatrix hr) (corrMatrix_diag r)
      μ s hs hpos)
    (isSklarCopula_gaussianScaleMixture _ _ _ _ _ _ _)
    (gaussianScaleMixtureLaw_map_swapCoord hr μ hs)

/-- Bivariate Gaussian scale mixture copulas are radially symmetric. -/
theorem isRadiallySymmetric_gaussianScaleMixture {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hpos : ∀ᵐ t ∂μ.toMeasure, 0 < s t) :
    (gaussianScaleMixture (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) μ s hs
      hpos).IsRadiallySymmetric :=
  isRadiallySymmetric_of_map_reflectAbout_eq
    (continuous_gaussianScaleMixtureLaw_marginal _ (posSemidef_corrMatrix hr) (corrMatrix_diag r)
      μ s hs hpos)
    (isSklarCopula_gaussianScaleMixture _ _ _ _ _ _ _)
    (gaussianScaleMixtureLaw_map_reflectAbout hr μ hs)

/-- The bivariate Student-t copula is exchangeable. -/
theorem isExchangeable_studentT {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (ν : ℝ) (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν hν).IsExchangeable :=
  isExchangeable_gaussianScaleMixture hr _ _ _ _

/-- The bivariate Student-t copula is radially symmetric. -/
theorem isRadiallySymmetric_studentT {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (ν : ℝ) (hν : 0 < ν) :
    (studentT (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r) ν
      hν).IsRadiallySymmetric :=
  isRadiallySymmetric_gaussianScaleMixture hr _ _ _ _

end ProbabilityTheory.Copula
