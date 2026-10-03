/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Gaussian.Slepian
import Copula.TailDependence.Examples

/-! # Tail independence of the Gaussian copula

The bivariate Gaussian copula with correlation `r < 1` is tail independent:
`λ_L = λ_U = 0` (Sibuya 1960). For `r = 1` it is `M` with `λ_L = λ_U = 1`.

## Proof
For `0 ≤ r < 1` and `x < 0`, `C_r(Φ(x), Φ(x)) = P(X ≤ x, Y ≤ x) ≤ P(X + Y ≤ 2x) = Φ(c x)` with
`c = 2/√(2 + 2r) > 1`. The Chernoff bound `Φ(y) ≤ exp(−y²/2)` and the density bound
`Φ(y) ≥ φ(y − 1)` for `y ≤ 0` give `Φ(c x)/Φ(x) → 0` as `x → −∞`. Negative correlations are
dominated by `Π` (Slepian), and the upper tail follows from radial symmetry.

## References
* M. Sibuya, *Bivariate extreme statistics I*, Ann. Inst. Statist. Math. 11 (1960).
* R. B. Nelsen, *An Introduction to Copulas*, 2nd ed., Springer 2006, §5.4.
* H. Joe, *Dependence Modeling with Copulas*, CRC Press 2014, §4.3.
-/

open MeasureTheory Set Real Filter
open scoped unitInterval ENNReal NNReal Topology

namespace ProbabilityTheory.Copula

/-- Chernoff bound for the standard normal lower tail: `Φ(y) ≤ exp(−y²/2)` for `y ≤ 0`. -/
theorem standardNormalCDF_le_exp {y : ℝ} (hy : y ≤ 0) :
    ProbabilityTheory.cdf (gaussianReal 0 1) y ≤ exp (-(y ^ 2) / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) y hy
    (integrable_exp_mul_gaussianReal y)
  rw [mgf_id_gaussianReal, ← exp_add] at h
  rw [cdf_eq_real]
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [NNReal.coe_one]
  ring

/-- Density lower bound for the standard normal lower tail: `Φ(y) ≥ φ(y − 1)` for `y ≤ 0`. -/
theorem gaussianPDFReal_sub_one_le_standardNormalCDF {y : ℝ} (hy : y ≤ 0) :
    gaussianPDFReal 0 1 (y - 1) ≤ ProbabilityTheory.cdf (gaussianReal 0 1) y := by
  rw [cdf_eq_real]
  have hsub : (gaussianReal 0 1).real (Ioc (y - 1) y) ≤ (gaussianReal 0 1).real (Iic y) :=
    measureReal_mono Ioc_subset_Iic_self
  refine le_trans ?_ hsub
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
      fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  have hconst : ∫ _ in Ioc (y - 1) y, gaussianPDFReal 0 1 (y - 1) =
      gaussianPDFReal 0 1 (y - 1) := by
    rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
    simp
  rw [← hconst]
  refine setIntegral_mono_on (integrableOn_const (by simp))
    (integrable_gaussianPDFReal 0 1).integrableOn measurableSet_Ioc fun s hs => ?_
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one]
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith [hs.1, hs.2])) (by positivity)

/-- For `0 ≤ r ≤ 1` and `σ = √(2 + 2r)`, `C_r(Φ(x), Φ(x)) ≤ Φ(2x/σ)`. -/
theorem cdf_bivariateGaussian_diag_le {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (hr0 : 0 ≤ r) (x : ℝ) :
    (bivariateGaussian r hr).cdf (normalCDFPair (x, x)) ≤
      ProbabilityTheory.cdf (gaussianReal 0 1) (2 * x / √(2 + 2 * r)) := by
  have hσ : 0 < √(2 + 2 * r) := Real.sqrt_pos.2 (by linarith)
  rw [cdf_bivariateGaussian]
  have hsub : {p : ℝ × ℝ | p.1 ≤ (x, x).1 ∧ p.2 ≤ (x, x).2} ⊆
      (fun p : ℝ × ℝ => 1 * p.1 + 1 * p.2) ⁻¹' Iic (2 * x) := by
    rintro p ⟨h1, h2⟩
    simp only [mem_preimage, mem_Iic]
    linarith
  refine (measureReal_mono hsub).trans (le_of_eq ?_)
  rw [← map_measureReal_apply (by fun_prop) measurableSet_Iic, map_linear_bivariateNormal hr]
  have h1 : (1 : ℝ) ^ 2 + 2 * 1 * 1 * r + 1 ^ 2 = √(2 + 2 * r) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]
    ring
  rw [h1, ← scaledNormalCDF_eq, scaledNormalCDF, cdf_eq_real]
  congr 1
  ext z
  simp only [mem_ofPred_eq, mem_Iic]
  rw [le_div_iff₀ hσ, mul_comm]

/-- The tail estimate: for `c > 1`, `Φ(c x) ≤ ε Φ(x)` for all sufficiently negative `x`. -/
theorem exists_standardNormalCDF_mul_le {c : ℝ} (hc : 1 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ < 0, ∀ x ≤ x₀, ProbabilityTheory.cdf (gaussianReal 0 1) (c * x) ≤
      ε * ProbabilityTheory.cdf (gaussianReal 0 1) x := by
  set k := c ^ 2 - 1 with hk
  have hk0 : 0 < k := by nlinarith
  set L := log (√(2 * π)) - log ε with hL
  have hLa := abs_nonneg L
  have hk4 : 0 < 4 / k := by positivity
  refine ⟨-(4 / k + |L| + 1), by linarith, fun x hx => ?_⟩
  have hx0 : x ≤ 0 := by linarith
  have hx4 : 4 / k ≤ -x := by linarith
  have hkx : 4 * (-x) ≤ k * x ^ 2 := by
    have h4 : 4 ≤ k * (-x) := by rwa [div_le_iff₀ hk0, mul_comm] at hx4
    nlinarith
  have hLx : L ≤ -x - 1 := by linarith [le_abs_self L]
  have hpi : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have hkey : exp (-((c * x) ^ 2) / 2) ≤ ε * ((√(2 * π))⁻¹ * exp (-(x - 1) ^ 2 / 2)) := by
    have hr : ε * ((√(2 * π))⁻¹ * exp (-(x - 1) ^ 2 / 2)) =
        exp (log ε - log (√(2 * π)) - (x - 1) ^ 2 / 2) := by
      rw [exp_sub, exp_sub, exp_log hε, exp_log hpi, neg_div, exp_neg]
      field_simp
    rw [hr]
    apply exp_le_exp.2
    nlinarith
  refine (standardNormalCDF_le_exp (by nlinarith)).trans (hkey.trans ?_)
  gcongr
  have h := gaussianPDFReal_sub_one_le_standardNormalCDF hx0
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one] at h
  exact h

/-- A criterion for vanishing lower tail dependence. -/
theorem hasLowerTailDependence_zero_of_forall {C : Copula 2}
    (h : ∀ ε > 0, ∃ δ > 0, ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < δ → C.diagonal t ≤ ε * t) :
    C.HasLowerTailDependence 0 := by
  rw [HasLowerTailDependence, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hC⟩ := h (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun {t} ht hdist => ?_⟩
  have ht0 : 0 < (t : ℝ) := ht
  rw [Subtype.dist_eq, Real.dist_eq, Icc.coe_zero, sub_zero, abs_of_pos ht0] at hdist
  rw [Real.dist_eq, sub_zero, lowerTailRatio, abs_of_nonneg (div_nonneg (C.diagonal_nonneg t)
    ht0.le), div_lt_iff₀ ht0]
  have := hC t ht0 hdist
  nlinarith

/-- **Tail independence of the Gaussian copula** (lower tail): `λ_L(C_r) = 0` for `r < 1`. -/
theorem hasLowerTailDependence_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (hr1 : r < 1) :
    (bivariateGaussian r hr).HasLowerTailDependence 0 := by
  apply hasLowerTailDependence_zero_of_forall
  intro ε hε
  rcases le_total 0 r with hr0 | hr0
  · -- main case `0 ≤ r < 1`
    set sg := √(2 + 2 * r) with hsg_def
    have hsg : 0 < sg := Real.sqrt_pos.2 (by linarith)
    have hsg2 : sg ^ 2 = 2 + 2 * r := Real.sq_sqrt (by linarith)
    have hc : 1 < 2 / sg := by
      rw [lt_div_iff₀ hsg, one_mul]
      nlinarith
    obtain ⟨x₀, hx₀, hx⟩ := exists_standardNormalCDF_mul_le hc hε
    have hδ : 0 < ProbabilityTheory.cdf (gaussianReal 0 1) x₀ :=
      (gaussianPDFReal_pos 0 1 _ one_ne_zero).trans_le
        (gaussianPDFReal_sub_one_le_standardNormalCDF hx₀.le)
    refine ⟨_, hδ, fun t ht0 htδ => ?_⟩
    have ht1 : (t : ℝ) < 1 := htδ.trans_le (ProbabilityTheory.cdf_le_one _ _)
    obtain ⟨x, hxt⟩ := exists_standardNormalCDFUnit_eq ht0 ht1
    have htx : (t : ℝ) = ProbabilityTheory.cdf (gaussianReal 0 1) x := by
      rw [← hxt, coe_cdfUnit]
    have hxx₀ : x ≤ x₀ := (strictMono_standardNormalCDF.lt_iff_lt.1 (htx ▸ htδ)).le
    have hdiag : (bivariateGaussian r hr).diagonal t =
        (bivariateGaussian r hr).cdf (normalCDFPair (x, x)) := by
      rw [diagonal, normalCDFPair, hxt]
    rw [hdiag, htx]
    refine (cdf_bivariateGaussian_diag_le hr hr0 x).trans ?_
    rw [show 2 * x / sg = 2 / sg * x by ring]
    exact hx x hxx₀
  · -- negative correlations are dominated by independence
    have h00 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    refine ⟨ε, hε, fun t ht0 htε => ?_⟩
    have hle := bivariateGaussian_lowerOrthantLE hr h00 hr0 ![t, t]
    rw [bivariateGaussian_zero, cdf_independence, Fin.prod_univ_two] at hle
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hle
    rw [diagonal]
    nlinarith

/-- **Tail independence of the Gaussian copula** (upper tail): `λ_U(C_r) = 0` for `r < 1`. -/
theorem hasUpperTailDependence_bivariateGaussian {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) (hr1 : r < 1) :
    (bivariateGaussian r hr).HasUpperTailDependence 0 := by
  unfold HasUpperTailDependence upperTailRatio
  rw [survivalCopula_bivariateGaussian]
  exact hasLowerTailDependence_bivariateGaussian hr hr1

/-- Tail dependence of the Gaussian copula: `λ_L(C_r) = 0` for `r < 1` and `λ_L(C_1) = 1`. -/
theorem hasLowerTailDependence_bivariateGaussian_iff {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    (bivariateGaussian r hr).HasLowerTailDependence 0 ↔ r < 1 := by
  refine ⟨fun h => lt_of_le_of_ne hr.2 fun h1 => ?_, hasLowerTailDependence_bivariateGaussian hr⟩
  subst h1
  rw [bivariateGaussian_one] at h
  exact zero_ne_one (h.unique hasLowerTailDependence_comonotonic)

end ProbabilityTheory.Copula
