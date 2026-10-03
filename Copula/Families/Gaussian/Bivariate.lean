/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gaussian.Identities
import Copula.Elliptical.GaussianOrthant
import Copula.Reflection.Bivariate
import Copula.Symmetry

/-! # The bivariate Gaussian copula

For a correlation `r ∈ [-1, 1]` let `bivariateNormal r` be the law of
`(Z₁, r Z₁ + √(1 − r²) Z₂)` for independent standard normal `Z₁, Z₂`: the centered bivariate
normal law with unit variances and correlation `r`. It is characterized by its linear forms
(`eq_bivariateNormal_of_linear_laws`, a Cramér–Wold argument).

The bivariate Gaussian copula `bivariateGaussian r hr` is the library's `gaussian` copula for the
correlation matrix `!![1, r; r, 1]`. We show:

* `toMeasure_bivariateGaussian`: it is the law of `(Φ(X), Φ(Y))` for `(X, Y) ~ bivariateNormal r`;
* `cdf_bivariateGaussian`: `C_r(Φ(x), Φ(y)) = P(X ≤ x, Y ≤ y)`, the classical formula
  `C_r(u, v) = Φ_r(Φ⁻¹(u), Φ⁻¹(v))` given by Sklar's theorem (Joe 2014, §4.3);
* endpoint cases `r = 0, 1, −1` give `Π`, `M`, `W`;
* `C_r` is exchangeable and radially symmetric, and reflecting one coordinate turns `r` into `−r`.

Standard normal CDF facts (`strictMono_standardNormalCDF`, `standardNormalCDF_neg`) are proved on
the way.

## References
* R. B. Nelsen, *An Introduction to Copulas*, 2nd ed., Springer 2006.
* H. Joe, *Dependence Modeling with Copulas*, CRC Press 2014, §4.3.
-/

open MeasureTheory Set Real
open scoped unitInterval ENNReal NNReal

namespace ProbabilityTheory.Copula

/-! ### The standard normal CDF -/

/-- The standard normal CDF `Φ` is strictly increasing. -/
theorem strictMono_standardNormalCDF : StrictMono (ProbabilityTheory.cdf (gaussianReal 0 1)) := by
  intro a b hab
  have h := (ProbabilityTheory.cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at h
  have hpos : 0 < gaussianReal 0 1 (Ioc a b) := by
    apply pos_of_ne_zero
    intro h0
    have h1 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h1
    linarith
  rw [h, ENNReal.ofReal_pos] at hpos
  linarith

/-- Symmetry of the standard normal CDF: `Φ(−x) = 1 − Φ(x)`. -/
theorem standardNormalCDF_neg (x : ℝ) :
    ProbabilityTheory.cdf (gaussianReal 0 1) (-x) =
      1 - ProbabilityTheory.cdf (gaussianReal 0 1) x := by
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hmap : (gaussianReal 0 1).map (fun t => -t) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  rw [cdf_eq_real, cdf_eq_real]
  conv_lhs => rw [← hmap]
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun t : ℝ => -t) ⁻¹' Iic (-x) = (Iio x)ᶜ := by
    ext t
    simp
  rw [hpre, probReal_compl_eq_one_sub measurableSet_Iio, measureReal_congr Iio_ae_eq_Iic]

/-- `Φ(0) = 1/2`. -/
theorem standardNormalCDF_zero : ProbabilityTheory.cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have h := standardNormalCDF_neg 0
  rw [neg_zero] at h
  linarith

/-- `Φ(−x) = 1 − Φ(x)` as points of the unit interval. -/
theorem standardNormalCDFUnit_neg (x : ℝ) :
    cdfUnit (gaussianReal 0 1) (-x) = unitInterval.symm (cdfUnit (gaussianReal 0 1) x) := by
  apply Subtype.ext
  simp [standardNormalCDF_neg]

/-- `Φ(0) = 1/2` as a point of the unit interval. -/
theorem standardNormalCDFUnit_zero : cdfUnit (gaussianReal 0 1) 0 = unitHalf := by
  apply Subtype.ext
  simp [standardNormalCDF_zero, unitHalf]

theorem standardNormalCDFUnit_le_iff {x y : ℝ} :
    cdfUnit (gaussianReal 0 1) x ≤ cdfUnit (gaussianReal 0 1) y ↔ x ≤ y := by
  rw [← Subtype.coe_le_coe, coe_cdfUnit, coe_cdfUnit, strictMono_standardNormalCDF.le_iff_le]

/-! ### The standard bivariate normal law -/

/-- The centered bivariate normal law with unit variances and correlation `r`, realized as the law
of `(Z₁, r Z₁ + √(1 − r²) Z₂)` for independent standard normal `Z₁, Z₂`. -/
noncomputable def bivariateNormal (r : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p => (p.1, r * p.1 + √(1 - r ^ 2) * p.2))

instance (r : ℝ) : IsProbabilityMeasure (bivariateNormal r) :=
  by unfold bivariateNormal; infer_instance

/-- Linear forms of the bivariate normal law: `aX + bY ~ N(0, a² + 2abr + b²)`. -/
theorem map_linear_bivariateNormal {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (a b : ℝ) :
    (bivariateNormal r).map (fun p => a * p.1 + b * p.2) =
      gaussianReal 0 (a ^ 2 + 2 * a * b * r + b ^ 2).toNNReal := by
  have hs2 : √(1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith [hr.1, hr.2])
  rw [bivariateNormal, Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 : ((fun p : ℝ × ℝ => a * p.1 + b * p.2) ∘
      fun p : ℝ × ℝ => (p.1, r * p.1 + √(1 - r ^ 2) * p.2)) =
      fun p => (a + b * r) * p.1 + (b * √(1 - r ^ 2)) * p.2 := by
    funext p
    simp only [Function.comp_apply]
    ring
  rw [h2, map_linear_prod_gaussianReal]
  congr 2
  simp only [NNReal.coe_one, mul_one]
  linear_combination b ^ 2 * hs2

/-- **Cramér–Wold characterization** of the bivariate normal law. -/
theorem eq_bivariateNormal_of_linear_laws {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h : ∀ a b : ℝ, μ.map (fun p => a * p.1 + b * p.2) =
      gaussianReal 0 (a ^ 2 + 2 * a * b * r + b ^ 2).toNNReal) :
    μ = bivariateNormal r :=
  measure_prod_eq_of_map_linear_eq fun a b =>
    (h a b).trans (map_linear_bivariateNormal hr a b).symm

/-- Sheppard's orthant formula for the bivariate normal law. -/
theorem bivariateNormal_orthant {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateNormal r).real {p | p.1 ≤ 0 ∧ p.2 ≤ 0} = 1 / 4 + arcsin r / (2 * π) :=
  orthant_nonpos_of_linear_laws _ measurable_fst measurable_snd hr one_pos fun a b => by
    rw [map_linear_bivariateNormal hr]
    congr 2
    ring

/-- The bivariate normal law is exchangeable. -/
theorem bivariateNormal_map_swap {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateNormal r).map Prod.swap = bivariateNormal r := by
  refine eq_bivariateNormal_of_linear_laws hr fun a b => ?_
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h : ((fun p : ℝ × ℝ => a * p.1 + b * p.2) ∘ Prod.swap) = fun p => b * p.1 + a * p.2 := by
    funext p
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [h, map_linear_bivariateNormal hr]
  congr 2
  ring

/-- Changing the sign of the second coordinate changes the correlation `r` into `−r`. -/
theorem bivariateNormal_map_neg_snd {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateNormal r).map (fun p => (p.1, -p.2)) = bivariateNormal (-r) := by
  refine eq_bivariateNormal_of_linear_laws ⟨by linarith [hr.2], by linarith [hr.1]⟩
    fun a b => ?_
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h : ((fun p : ℝ × ℝ => a * p.1 + b * p.2) ∘ fun p : ℝ × ℝ => (p.1, -p.2)) =
      fun p => a * p.1 + (-b) * p.2 := by
    funext p
    simp only [Function.comp_apply]
    ring
  rw [h, map_linear_bivariateNormal hr]
  congr 2
  ring

/-- Changing the sign of both coordinates preserves the bivariate normal law. -/
theorem bivariateNormal_map_neg {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateNormal r).map (fun p => (-p.1, -p.2)) = bivariateNormal r := by
  refine eq_bivariateNormal_of_linear_laws hr fun a b => ?_
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have h : ((fun p : ℝ × ℝ => a * p.1 + b * p.2) ∘ fun p : ℝ × ℝ => (-p.1, -p.2)) =
      fun p => (-a) * p.1 + (-b) * p.2 := by
    funext p
    simp only [Function.comp_apply]
    ring
  rw [h, map_linear_bivariateNormal hr]
  congr 2
  ring

/-! ### The correlation matrix and the Gaussian copula -/

/-- The `2 × 2` correlation matrix with off-diagonal entry `r`. -/
def corrMatrix (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, r; r, 1]

theorem corrMatrix_diag (r : ℝ) (i : Fin 2) : corrMatrix r i i = 1 := by
  fin_cases i <;> rfl

theorem posSemidef_corrMatrix {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) : (corrMatrix r).PosSemidef := by
  have hs2 : √(1 - r ^ 2) * √(1 - r ^ 2) = 1 - r ^ 2 :=
    Real.mul_self_sqrt (by nlinarith [hr.1, hr.2])
  have h : corrMatrix r =
      Matrix.conjTranspose !![1, r; 0, √(1 - r ^ 2)] * !![1, r; 0, √(1 - r ^ 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [corrMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    linarith
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Linear forms of the multivariate normal law with correlation matrix `corrMatrix r`. -/
theorem map_linear_multivariateGaussian_corrMatrix {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1)
    (a b : ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).map
        (fun x => a * x 0 + b * x 1) =
      gaussianReal 0 (a ^ 2 + 2 * a * b * r + b ^ 2).toNNReal := by
  set c : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![a, b] with hc
  have hL : (fun x : EuclideanSpace ℝ (Fin 2) => a * x 0 + b * x 1) = innerSL ℝ c := by
    funext x
    simp [c, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rw [hL, IsGaussian.map_eq_gaussianReal]
  congr 1
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  · congr 1
    have hcov := covarianceBilin_apply_eq_cov
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r))
      IsGaussian.memLp_two_id c c
    rw [covariance_self (by fun_prop), covarianceBilin_multivariateGaussian
      (posSemidef_corrMatrix hr)] at hcov
    have hfun : (⇑(innerSL ℝ c) : EuclideanSpace ℝ (Fin 2) → ℝ) = fun u => inner ℝ c u := by
      funext u
      simp
    rw [hfun, ← hcov]
    simp [c, corrMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The coordinate map `(x, y) ↦ (Φ(x), Φ(y))` into the unit square. -/
noncomputable def normalCDFPair (p : ℝ × ℝ) : Fin 2 → I :=
  ![cdfUnit (gaussianReal 0 1) p.1, cdfUnit (gaussianReal 0 1) p.2]

@[fun_prop]
theorem measurable_normalCDFPair : Measurable normalCDFPair := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact (measurable_cdfUnit _).comp measurable_fst
  · exact (measurable_cdfUnit _).comp measurable_snd

theorem normalCDFPair_le_iff (p q : ℝ × ℝ) :
    normalCDFPair p ≤ normalCDFPair q ↔ p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  rw [Pi.le_def, Fin.forall_fin_two]
  simp [normalCDFPair, standardNormalCDFUnit_le_iff]

/-- The bivariate Gaussian copula with correlation `r ∈ [-1, 1]`. -/
noncomputable def bivariateGaussian (r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1) : Copula 2 :=
  gaussian (corrMatrix r) (posSemidef_corrMatrix hr) (corrMatrix_diag r)

/-- The bivariate Gaussian copula is the law of `(Φ(X), Φ(Y))` for `(X, Y) ~ bivariateNormal r`. -/
theorem toMeasure_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).toMeasure = (bivariateNormal r).map normalCDFPair := by
  have h1 : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).map
      (fun x => (x 0, x 1)) = bivariateNormal r :=
    eq_bivariateNormal_of_linear_laws hr fun a b => by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      exact map_linear_multivariateGaussian_corrMatrix hr a b
  rw [← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (corrMatrix r)).map
      (fun x i => cdfUnit (gaussianReal 0 1) (x i)) = _
  congr 1
  funext x i
  fin_cases i <;> rfl

/-- **CDF of the bivariate Gaussian copula**: `C_r(Φ(x), Φ(y)) = P(X ≤ x, Y ≤ y)` for
`(X, Y) ~ bivariateNormal r`, i.e. `C_r(u, v) = Φ_r(Φ⁻¹(u), Φ⁻¹(v))`. -/
theorem cdf_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (q : ℝ × ℝ) :
    (bivariateGaussian r hr).cdf (normalCDFPair q) =
      (bivariateNormal r).real {p | p.1 ≤ q.1 ∧ p.2 ≤ q.2} := by
  rw [cdf, toMeasure_bivariateGaussian, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext p
  simp only [mem_preimage, mem_Iic, normalCDFPair_le_iff, mem_ofPred_eq]

/-- Every point of the open unit interval is a value of `Φ`. -/
theorem exists_standardNormalCDFUnit_eq {u : I} (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    ∃ x, cdfUnit (gaussianReal 0 1) x = u := by
  obtain ⟨x, hx⟩ := exists_cdf_eq_of_continuous _ continuous_standardNormalCDF hu0 hu1
  exact ⟨x, Subtype.ext hx⟩

/-! ### Endpoints and symmetries -/

theorem gaussian_congr {d : ℕ} {R R' : Matrix (Fin d) (Fin d) ℝ} (h : R = R')
    (hR : R.PosSemidef) (hd : ∀ i, R i i = 1) (hR' : R'.PosSemidef) (hd' : ∀ i, R' i i = 1) :
    gaussian R hR hd = gaussian R' hR' hd' := by
  subst h
  rfl

theorem bivariateGaussian_congr {r r' : ℝ} (h : r = r') (hr : r ∈ Icc (-1 : ℝ) 1)
    (hr' : r' ∈ Icc (-1 : ℝ) 1) : bivariateGaussian r hr = bivariateGaussian r' hr' := by
  subst h
  rfl

theorem neg_mem_corrInterval {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) : -r ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [hr.2], by linarith [hr.1]⟩

/-- Zero correlation gives the independence copula. -/
@[simp]
theorem bivariateGaussian_zero (h : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) :
    bivariateGaussian 0 h = independence 2 := by
  rw [bivariateGaussian, ← gaussian_one 2]
  apply gaussian_congr
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Correlation one gives the comonotonic copula `M`. -/
@[simp]
theorem bivariateGaussian_one (h : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) :
    bivariateGaussian 1 h = comonotonic 2 := by
  rw [bivariateGaussian, ← gaussian_allOnes 2]
  apply gaussian_congr
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The bivariate Gaussian copula is exchangeable. -/
@[simp]
theorem transpose_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).transpose = bivariateGaussian r hr := by
  rw [transpose, bivariateGaussian, gaussian_reindex]
  apply gaussian_congr
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem isExchangeable_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).IsExchangeable :=
  transpose_bivariateGaussian hr

/-- Reflecting the second coordinate changes the correlation `r` into `−r`. -/
theorem reflect_second_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).reflect {1} = bivariateGaussian (-r) (neg_mem_corrInterval hr) := by
  apply ext
  rw [toMeasure_reflect, toMeasure_bivariateGaussian, toMeasure_bivariateGaussian,
    ← bivariateNormal_map_neg_snd hr, Measure.map_map (measurable_reflectPoint _) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p i
  fin_cases i
  · simp [reflectPoint, normalCDFPair]
  · simp [reflectPoint, normalCDFPair, standardNormalCDFUnit_neg]

/-- Reflecting the first coordinate changes the correlation `r` into `−r`. -/
theorem reflect_first_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).reflect {0} = bivariateGaussian (-r) (neg_mem_corrInterval hr) := by
  rw [← transpose_transpose ((bivariateGaussian r hr).reflect {0}), transpose_reflect_first,
    transpose_bivariateGaussian, reflect_second_bivariateGaussian, transpose_bivariateGaussian]

/-- Correlation `−1` gives the countermonotonic copula `W`. -/
@[simp]
theorem bivariateGaussian_neg_one (h : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1) :
    bivariateGaussian (-1) h = countermonotonic := by
  rw [← reflect_comonotonic_eq_countermonotonic,
    ← bivariateGaussian_one (right_mem_Icc.2 (by norm_num)),
    reflect_second_bivariateGaussian]

/-- The bivariate Gaussian copula is radially symmetric: `Ĉ_r = C_r`. -/
@[simp]
theorem survivalCopula_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).survivalCopula = bivariateGaussian r hr := by
  rw [← reflect_first_second, reflect_first_bivariateGaussian, reflect_second_bivariateGaussian]
  exact bivariateGaussian_congr (neg_neg r) _ _

theorem isRadiallySymmetric_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).IsRadiallySymmetric :=
  survivalCopula_bivariateGaussian hr

end ProbabilityTheory.Copula
