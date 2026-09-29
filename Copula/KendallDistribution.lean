/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Basic
import Copula.Reflection.Bivariate
import Mathlib.Probability.CDF

/-! # Kendall distributions

The Kendall distribution is the law of `C(U)` when `U` has copula `C`.
It is defined in every finite dimension, including zero. Its CDF uses closed
lower intervals, so an atom at zero is retained (as for countermonotonicity).
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The probability law of the copula CDF evaluated at a draw from the copula. -/
noncomputable def kendallDistribution (C : Copula d) : ProbabilityMeasure ℝ :=
  C.measure.map C.cdf

@[simp] theorem toMeasure_kendallDistribution (C : Copula d) :
    C.kendallDistribution.toMeasure = C.toMeasure.map C.cdf := rfl

/-- Kendall's distribution function `K_C(t) = P(C(U) ≤ t)`. -/
noncomputable def kendallCDF (C : Copula d) : ℝ → ℝ :=
  ProbabilityTheory.cdf C.kendallDistribution.toMeasure

theorem kendallCDF_eq (C : Copula d) (t : ℝ) :
    C.kendallCDF t = C.toMeasure.real {x | C.cdf x ≤ t} := by
  rw [kendallCDF, ProbabilityTheory.cdf_eq_real, Measure.real, toMeasure_kendallDistribution,
    Measure.map_apply C.continuous_cdf.measurable measurableSet_Iic]
  rfl

theorem kendallCDF_nonneg (C : Copula d) (t : ℝ) : 0 ≤ C.kendallCDF t :=
  ProbabilityTheory.cdf_nonneg _ t

theorem kendallCDF_le_one (C : Copula d) (t : ℝ) : C.kendallCDF t ≤ 1 :=
  ProbabilityTheory.cdf_le_one _ t

theorem monotone_kendallCDF (C : Copula d) : Monotone C.kendallCDF :=
  ProbabilityTheory.monotone_cdf _

theorem right_continuous_kendallCDF (C : Copula d) (t : ℝ) :
    ContinuousWithinAt C.kendallCDF (Ici t) t :=
  (ProbabilityTheory.cdf C.kendallDistribution.toMeasure).right_continuous t

theorem kendallCDF_of_neg (C : Copula d) {t : ℝ} (ht : t < 0) : C.kendallCDF t = 0 := by
  rw [C.kendallCDF_eq]
  have he : {x | C.cdf x ≤ t} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_le.mpr (ht.trans_le (C.cdf_nonneg x))
  rw [he, measureReal_empty]

theorem kendallCDF_of_one_le (C : Copula d) {t : ℝ} (ht : 1 ≤ t) : C.kendallCDF t = 1 := by
  rw [C.kendallCDF_eq]
  have he : {x | C.cdf x ≤ t} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact (C.cdf_le_one x).trans ht
  rw [he, probReal_univ]

@[simp] theorem kendallCDF_one (C : Copula d) : C.kendallCDF 1 = 1 :=
  C.kendallCDF_of_one_le le_rfl

/-- A nonempty copula's Kendall distribution stochastically lies below uniform. -/
theorem le_kendallCDF [NeZero d] (C : Copula d) (t : I) : (t : ℝ) ≤ C.kendallCDF t := by
  calc
    (t : ℝ) = C.toMeasure.real {x | x 0 ≤ t} := (C.measureReal_eval_le 0 t).symm
    _ ≤ C.toMeasure.real {x | C.cdf x ≤ t} :=
      measureReal_mono (fun x hx => (C.cdf_le_coord x 0).trans hx)
    _ = C.kendallCDF t := (C.kendallCDF_eq t).symm

/-- Integration against the Kendall law is integration of the CDF transform. -/
theorem integral_kendallDistribution (C : Copula d) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂C.kendallDistribution.toMeasure) = ∫ x, f (C.cdf x) ∂C.toMeasure := by
  rw [toMeasure_kendallDistribution]
  exact integral_map C.continuous_cdf.measurable.aemeasurable hf.aestronglyMeasurable

theorem kendallTau_eq_integral_kendallDistribution (C : Copula 2) :
    C.kendallTau = 4 * (∫ t, t ∂C.kendallDistribution.toMeasure) - 1 := by
  rw [C.integral_kendallDistribution (fun t => t) measurable_id]
  rfl

@[simp] theorem kendallDistribution_comonotonic [NeZero d] :
    (comonotonic d).kendallDistribution.toMeasure = (volume : Measure I).map (fun u : I => (u : ℝ)) := by
  rw [toMeasure_kendallDistribution, toMeasure_comonotonic,
    Measure.map_map (comonotonic d).continuous_cdf.measurable (by fun_prop)]
  congr 1
  funext u
  simp

@[simp] theorem kendallCDF_comonotonic [NeZero d] (t : I) : (comonotonic d).kendallCDF t = t := by
  rw [kendallCDF, ProbabilityTheory.cdf_eq_real, kendallDistribution_comonotonic, Measure.real,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  change ((volume : Measure I) (Iic t)).toReal = _
  rw [unitInterval.volume_Iic, ENNReal.toReal_ofReal t.property.1]

/-- Dimension zero gives the constant CDF value one, rather than a uniform Kendall law. -/
@[simp] theorem kendallDistribution_dim_zero (C : Copula 0) :
    C.kendallDistribution.toMeasure = Measure.dirac 1 := by
  have he : C.cdf = fun _ => 1 := funext C.cdf_dim_zero
  rw [toMeasure_kendallDistribution, he, Measure.map_const, measure_univ, one_smul]

/-- All natural moments of the independent copula's Kendall law, including dimension zero. -/
theorem integral_pow_kendallDistribution_independence (d n : ℕ) :
    (∫ t, t ^ n ∂(independence d).kendallDistribution.toMeasure) = (1 / (n + 1 : ℝ)) ^ d := by
  rw [integral_kendallDistribution _ _ (by fun_prop)]
  simp only [cdf_independence, ← Finset.prod_pow, toMeasure_independence]
  have h := integral_fin_nat_prod_eq_prod (μ := fun _ : Fin d => (volume : Measure I))
    (fun _ (u : I) => (u : ℝ) ^ n)
  simpa using h

@[simp] theorem kendallDistribution_countermonotonic :
    countermonotonic.kendallDistribution.toMeasure = Measure.dirac 0 := by
  rw [toMeasure_kendallDistribution, toMeasure_countermonotonic,
    Measure.map_map countermonotonic.continuous_cdf.measurable (by fun_prop)]
  have he : countermonotonic.cdf ∘ (fun u : I => ![u, unitInterval.symm u]) = fun _ => 0 := by
    funext u
    simp [cdf_countermonotonic, unitInterval.coe_symm_eq]
  rw [he, Measure.map_const, measure_univ, one_smul]

/-- Countermonotonicity has an atom of mass one at zero, not `K_W(0) = 0`. -/
@[simp] theorem kendallCDF_countermonotonic (t : I) : countermonotonic.kendallCDF t = 1 := by
  rw [kendallCDF, ProbabilityTheory.cdf_eq_real, kendallDistribution_countermonotonic]
  simp [Measure.real, Measure.dirac_apply' _ measurableSet_Iic, t.property.1]

@[simp] theorem kendallDistribution_transpose (C : Copula 2) :
    C.transpose.kendallDistribution = C.kendallDistribution := by
  apply ProbabilityMeasure.toMeasure_injective
  have ht : C.transpose.toMeasure = C.toMeasure.map (fun x => ![x 1, x 0]) := by
    rw [transpose, toMeasure_reindex]
    congr 1
    ext x i
    fin_cases i <;> rfl
  rw [toMeasure_kendallDistribution, ht,
    Measure.map_map C.transpose.continuous_cdf.measurable (by fun_prop), toMeasure_kendallDistribution]
  congr 1
  funext x
  simp only [Function.comp_def, cdf_transpose]
  congr 1
  ext i
  fin_cases i <;> rfl

@[simp] theorem kendallCDF_transpose (C : Copula 2) : C.transpose.kendallCDF = C.kendallCDF := by
  simp [kendallCDF]

end ProbabilityTheory.Copula
