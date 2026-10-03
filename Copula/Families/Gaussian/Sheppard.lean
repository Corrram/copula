/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gaussian.Bivariate
import Copula.Rank.Basic

/-! # Rank correlations of the bivariate Gaussian copula

For the bivariate Gaussian copula `C_r` with correlation `r ∈ [-1, 1]`:

* `blomqvistBeta_bivariateGaussian`: `β(C_r) = (2/π) arcsin r` (Sheppard's formula
  `P(X ≤ 0, Y ≤ 0) = 1/4 + arcsin r / (2π)`);
* `kendallTau_bivariateGaussian`: `τ(C_r) = (2/π) arcsin r`;
* `spearmanRho_bivariateGaussian`: `ρ_S(C_r) = (6/π) arcsin (r/2)`.

All three reduce to Sheppard's orthant formula (`orthant_nonpos_of_linear_laws`): Kendall's tau
is `4 P(X' ≤ X, Y' ≤ Y) − 1` for an independent copy `(X', Y')`, and `(X − X', Y − Y')` is
bivariate normal with correlation `r`; Spearman's rho is `12 P(X' ≤ X, Y'' ≤ Y) − 3` for
independent `X', Y'' ~ N(0, 1)`, and `(X − X', Y − Y'')` is bivariate normal with correlation
`r/2`.

## References
* W. F. Sheppard (1899); K. Pearson (1907) for `ρ_S`; W. H. Kruskal, *Ordinal measures of
  association*, J. Amer. Statist. Assoc. 53 (1958), 814–861.
* R. B. Nelsen, *An Introduction to Copulas*, 2nd ed., Springer 2006, §5.1.
* H. Joe, *Dependence Modeling with Copulas*, CRC Press 2014, §4.3.
-/

open MeasureTheory Set Real
open scoped unitInterval ENNReal NNReal

namespace ProbabilityTheory.Copula

/-- The variance `a² + 2abr + b²` of `aX + bY` is nonnegative for `|r| ≤ 1`. -/
theorem corr_quadratic_nonneg {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (a b : ℝ) :
    0 ≤ a ^ 2 + 2 * a * b * r + b ^ 2 := by
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  nlinarith [sq_nonneg (a + b * r), mul_nonneg (sq_nonneg b) h1]

/-- The integral of a section measure is the measure of the set in the product. -/
theorem integral_measureReal_prodMk {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (α × β)} (hS : MeasurableSet S) :
    ∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ = (μ.prod ν).real S := by
  rw [measureReal_def, Measure.prod_apply hS, ← integral_toReal
    (measurable_measure_prodMk_left hS).aemeasurable
    (ae_of_all _ fun x => measure_lt_top _ _)]
  rfl

/-- If `L(p) = a p₁ + b p₂` has centered Gaussian laws `N(0, v)` under `μ` and `N(0, w)` under
`ν`, then `L(q) − L(p)` has law `N(0, v + w)` under `μ ⊗ ν` (for `(p, q) ~ μ ⊗ ν`). -/
theorem map_linear_sub_prod {μ ν : Measure (ℝ × ℝ)} [SFinite μ] [SFinite ν] (a b : ℝ)
    {v w : ℝ≥0} (hμ : μ.map (fun p => a * p.1 + b * p.2) = gaussianReal 0 v)
    (hν : ν.map (fun p => a * p.1 + b * p.2) = gaussianReal 0 w) :
    (μ.prod ν).map (fun z => a * (z.2.1 - z.1.1) + b * (z.2.2 - z.1.2)) =
      gaussianReal 0 ((v : ℝ) + w).toNNReal := by
  have h : (fun z : (ℝ × ℝ) × (ℝ × ℝ) => a * (z.2.1 - z.1.1) + b * (z.2.2 - z.1.2)) =
      (fun t : ℝ × ℝ => (-1) * t.1 + 1 * t.2) ∘
        Prod.map (fun p : ℝ × ℝ => a * p.1 + b * p.2) (fun p : ℝ × ℝ => a * p.1 + b * p.2) := by
    funext z
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
    ring
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hμ, hν,
    map_linear_prod_gaussianReal]
  congr 2
  ring

/-- **Blomqvist's beta of the Gaussian copula** (Sheppard's formula):
`β(C_r) = (2/π) arcsin r`. -/
theorem blomqvistBeta_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).blomqvistBeta = 2 / π * arcsin r := by
  have h : ![unitHalf, unitHalf] = normalCDFPair (0, 0) := by
    funext i
    fin_cases i <;> simp [normalCDFPair, standardNormalCDFUnit_zero]
  have hcdf := cdf_bivariateGaussian hr (0, 0)
  rw [← h] at hcdf
  rw [blomqvistBeta, hcdf, bivariateNormal_orthant hr]
  field_simp
  ring

/-- **Kendall's tau of the Gaussian copula**: `τ(C_r) = (2/π) arcsin r`. -/
theorem kendallTau_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).kendallTau = 2 / π * arcsin r := by
  set ν := bivariateNormal r
  set C := bivariateGaussian r hr
  have hS : MeasurableSet {z : (ℝ × ℝ) × (ℝ × ℝ) | z.2.1 - z.1.1 ≤ 0 ∧ z.2.2 - z.1.2 ≤ 0} :=
    (measurableSet_le (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.1 - z.1.1) (by fun_prop)
      measurable_const).inter
      (measurableSet_le (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.2 - z.1.2) (by fun_prop)
        measurable_const)
  have hint : ∫ x, C.cdf x ∂C.toMeasure =
      (ν.prod ν).real {z | z.2.1 - z.1.1 ≤ 0 ∧ z.2.2 - z.1.2 ≤ 0} := by
    rw [toMeasure_bivariateGaussian, integral_map (by fun_prop)
      (continuous_cdf C).aestronglyMeasurable, ← integral_measureReal_prodMk _ _ hS]
    congr 1
    funext p
    rw [cdf_bivariateGaussian]
    congr 1
    ext q
    simp only [mem_ofPred_eq, mem_preimage, sub_nonpos]
  have horth := orthant_nonpos_of_linear_laws (ν.prod ν)
    (X := fun z => z.2.1 - z.1.1) (Y := fun z => z.2.2 - z.1.2) (by fun_prop) (by fun_prop) hr
    two_pos fun a b => by
      rw [map_linear_sub_prod a b (map_linear_bivariateNormal hr a b)
        (map_linear_bivariateNormal hr a b), Real.coe_toNNReal _ (corr_quadratic_nonneg hr a b)]
      congr 2
      ring
  rw [kendallTau, hint, horth]
  field_simp
  ring

/-- **Spearman's rho of the Gaussian copula**: `ρ_S(C_r) = (6/π) arcsin (r/2)`. -/
theorem spearmanRho_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).spearmanRho = 6 / π * arcsin (r / 2) := by
  set ν := bivariateNormal r
  set G := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hS : MeasurableSet {z : (ℝ × ℝ) × (ℝ × ℝ) | z.2.1 - z.1.1 ≤ 0 ∧ z.2.2 - z.1.2 ≤ 0} :=
    (measurableSet_le (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.1 - z.1.1) (by fun_prop)
      measurable_const).inter
      (measurableSet_le (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.2.2 - z.1.2) (by fun_prop)
        measurable_const)
  have hint : ∫ x, ((x 0 : I) : ℝ) * (x 1 : ℝ) ∂(bivariateGaussian r hr).toMeasure =
      (ν.prod G).real {z | z.2.1 - z.1.1 ≤ 0 ∧ z.2.2 - z.1.2 ≤ 0} := by
    rw [toMeasure_bivariateGaussian, integral_map (by fun_prop) (by fun_prop),
      ← integral_measureReal_prodMk _ _ hS]
    congr 1
    funext p
    have hpre : Prod.mk p ⁻¹' {z : (ℝ × ℝ) × (ℝ × ℝ) | z.2.1 - z.1.1 ≤ 0 ∧ z.2.2 - z.1.2 ≤ 0} =
        Iic p.1 ×ˢ Iic p.2 := by
      ext q
      simp only [mem_preimage, mem_ofPred_eq, sub_nonpos, mem_prod, mem_Iic]
    rw [hpre, measureReal_prod_prod, ← cdf_eq_real, ← cdf_eq_real]
    rfl
  have hr2 : r / 2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hG : ∀ a b : ℝ, G.map (fun p => a * p.1 + b * p.2) =
      gaussianReal 0 (a ^ 2 + b ^ 2).toNNReal := fun a b => by
    rw [map_linear_prod_gaussianReal]
    congr 2
    simp
  have horth := orthant_nonpos_of_linear_laws (ν.prod G)
    (X := fun z => z.2.1 - z.1.1) (Y := fun z => z.2.2 - z.1.2) (by fun_prop) (by fun_prop) hr2
    two_pos fun a b => by
      rw [map_linear_sub_prod a b (map_linear_bivariateNormal hr a b) (hG a b),
        Real.coe_toNNReal _ (corr_quadratic_nonneg hr a b),
        Real.coe_toNNReal _ (by positivity)]
      congr 2
      ring
  rw [spearmanRho, hint, horth]
  field_simp
  ring

/-- Kendall's tau and Blomqvist's beta coincide for Gaussian copulas. -/
theorem kendallTau_eq_blomqvistBeta_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).kendallTau = (bivariateGaussian r hr).blomqvistBeta := by
  rw [kendallTau_bivariateGaussian, blomqvistBeta_bivariateGaussian]

/-- The correlation parameter is recovered from Kendall's tau: `r = sin(π τ / 2)`. -/
theorem sin_kendallTau_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    sin (π * (bivariateGaussian r hr).kendallTau / 2) = r := by
  rw [kendallTau_bivariateGaussian]
  have hπ := pi_pos
  rw [show π * (2 / π * arcsin r) / 2 = arcsin r by field_simp, sin_arcsin hr.1 hr.2]

/-- Spearman's rho as a function of Kendall's tau for Gaussian copulas:
`ρ_S = (6/π) arcsin (sin(π τ / 2) / 2)`. -/
theorem spearmanRho_eq_kendallTau_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).spearmanRho =
      6 / π * arcsin (sin (π * (bivariateGaussian r hr).kendallTau / 2) / 2) := by
  rw [sin_kendallTau_bivariateGaussian, spearmanRho_bivariateGaussian]

/-- Kendall's tau is strictly increasing in the correlation. -/
theorem kendallTau_bivariateGaussian_lt {r r' : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) (h : r < r') :
    (bivariateGaussian r hr).kendallTau < (bivariateGaussian r' hr').kendallTau := by
  rw [kendallTau_bivariateGaussian, kendallTau_bivariateGaussian]
  exact mul_lt_mul_of_pos_left (arcsin_lt_arcsin hr.1 h hr'.2) (by positivity)

/-- Spearman's rho is strictly increasing in the correlation. -/
theorem spearmanRho_bivariateGaussian_lt {r r' : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) (h : r < r') :
    (bivariateGaussian r hr).spearmanRho < (bivariateGaussian r' hr').spearmanRho := by
  rw [spearmanRho_bivariateGaussian, spearmanRho_bivariateGaussian]
  exact mul_lt_mul_of_pos_left
    (arcsin_lt_arcsin (by linarith [hr.1]) (by linarith) (by linarith [hr'.2])) (by positivity)

end ProbabilityTheory.Copula
