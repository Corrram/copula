/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion, Marcus Rockel
-/
import Copula.Families.Gaussian
import Copula.Independence
import Copula.Comonotonic
import Copula.Transform
import Copula.Unique

/-! # Gaussian copula identities

Identity correlation gives independence. Selecting, permuting, or repeating
coordinates selects the corresponding rows and columns of the correlation matrix.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d e : ℕ}

/-- Independent standard normal coordinates give the independence copula. -/
@[simp]
theorem gaussian_one (d : ℕ) :
    gaussian (1 : Matrix (Fin d) (Fin d) ℝ) Matrix.PosSemidef.one (by simp) =
      independence d := by
  apply ext
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) 1).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i)) = _
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i)) = _
  rw [Measure.pi_map_pi (fun _ => (measurable_cdfUnit _).aemeasurable)]
  simp only [map_cdfUnit _ continuous_standardNormalCDF, toMeasure_independence]

/-- Coordinate selection as a continuous linear map between Euclidean spaces. -/
private noncomputable def selectCLM (ρ : Fin e → Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin e) :=
  (EuclideanSpace.equiv (Fin e) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => EuclideanSpace.proj (ρ i))

-- Generalizes mathlib's `measurePreserving_restrict₂_multivariateGaussian`:
-- the same mean/covariance comparison also permits repeated coordinates.
private theorem map_select_multivariateGaussian (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) (ρ : Fin e → Fin d) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map (selectCLM ρ) =
      multivariateGaussian 0 (R.submatrix ρ ρ) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian,
      map_zero, integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin e) ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have hh (i : Fin e) :
        (fun u => inner (𝕜 := ℝ) ((EuclideanSpace.basisFun (Fin e) ℝ).toBasis i) u) ∘
          selectCLM ρ = fun u => u (ρ i) := by
      ext u
      simp [selectCLM, PiLp.inner_apply]
    simp_rw [hh, covariance_eval_multivariateGaussian hR,
      covarianceBilin_multivariateGaussian (hR.submatrix ρ)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

/-- Gaussian copulas commute with coordinate selection, including repeated coordinates. -/
theorem gaussian_reindex (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef)
    (hdiag : ∀ i, R i i = 1) (ρ : Fin e → Fin d) :
    (gaussian R hR hdiag).reindex ρ =
      gaussian (R.submatrix ρ ρ) (hR.submatrix ρ) (fun i => hdiag (ρ i)) := by
  apply ext
  rw [toMeasure_reindex]
  change ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i))).map (fun x i => x (ρ i)) =
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin e)) (R.submatrix ρ ρ)).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i))
  rw [← map_select_multivariateGaussian R hR ρ,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Repeating a single coordinate produces the all-ones correlation matrix. -/
theorem posSemidef_allOnes (d : ℕ) :
    Matrix.PosSemidef (Matrix.of (fun (_ _ : Fin d) => (1 : ℝ))) := by
  simpa only [Matrix.submatrix, Matrix.one_apply_eq] using
    (Matrix.PosSemidef.one (n := Fin 1) (R := ℝ)).submatrix
    (fun _ : Fin d => (0 : Fin 1))

/-- Perfect positive correlation gives the comonotonic copula, including dimension zero. -/
@[simp]
theorem gaussian_allOnes (d : ℕ) :
    gaussian (Matrix.of (fun (_ _ : Fin d) => (1 : ℝ))) (posSemidef_allOnes d) (fun _ => rfl) =
      comonotonic d := by
  have h := gaussian_reindex (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosSemidef.one
    (by simp) (fun _ : Fin d => (0 : Fin 1))
  simp only [Matrix.submatrix, Matrix.one_apply_eq] at h
  rw [← h, gaussian_one]
  apply ext
  rw [toMeasure_reindex, toMeasure_comonotonic]
  rw [independence_eq_comonotonic_dim_one, toMeasure_comonotonic,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end ProbabilityTheory.Copula
