/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.SpearmanCDF
import Copula.Order.Orthant
import Copula.CDF.Bounds

/-!
# Multivariate Kendall's tau and Spearman's rho

For a `d`-copula `C` (`d ≥ 2`) the multivariate versions of Kendall's tau and of Spearman's rho
(Joe 1990, "Multivariate concordance", J. Multivariate Anal. 35; Nelsen 1996, "Nonparametric
measures of multivariate association"; Schmid–Schmidt 2007, `ρ₁`) are

* `τ_d(C) = (2^d ∫ C dC - 1) / (2^{d-1} - 1)` (`multivariateKendallTau`),
* `ρ_d(C) = (d + 1) / (2^d - d - 1) · (2^d ∫ C dΠ - 1)` (`multivariateSpearmanRho`).

We prove:

* for `d = 2` they are Kendall's tau and Spearman's rho (`multivariateKendallTau_two`,
  `multivariateSpearmanRho_two`);
* the Fubini identity `∫ C dΠ = ∫ ∏ (1 - xᵢ) dC(x)` (`integral_cdf_independence_eq_prod`);
* both vanish at `Π_d` and equal `1` at `M_d` (`multivariateKendallTau_independence`,
  `multivariateKendallTau_comonotonic`, `multivariateSpearmanRho_independence`,
  `multivariateSpearmanRho_comonotonic`);
* the bounds `-1/(2^{d-1} - 1) ≤ τ_d ≤ 1` and `ρ_d ≤ 1`, and monotonicity of `ρ_d` in the
  lower-orthant order (`multivariateSpearmanRho_mono`).
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- **Multivariate Kendall's tau** `τ_d(C) = (2^d ∫ C dC - 1) / (2^{d-1} - 1)` (Joe 1990). -/
noncomputable def multivariateKendallTau (C : Copula d) : ℝ :=
  ((2 : ℝ) ^ d * (∫ x, C.cdf x ∂C.toMeasure) - 1) / ((2 : ℝ) ^ (d - 1) - 1)

/-- **Multivariate Spearman's rho** `ρ_d(C) = (d+1)/(2^d - d - 1) · (2^d ∫ C dΠ - 1)`
(Joe 1990; Schmid–Schmidt 2007). -/
noncomputable def multivariateSpearmanRho (C : Copula d) : ℝ :=
  ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) *
    ((2 : ℝ) ^ d * (∫ x, C.cdf x ∂(independence d).toMeasure) - 1)

/-- `2^d > d + 1` for `d ≥ 2`. -/
theorem dim_add_one_lt_two_pow (hd : 2 ≤ d) : (d : ℝ) + 1 < (2 : ℝ) ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    push_cast
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

private theorem two_pow_pred_sub_one_pos (hd : 2 ≤ d) : 0 < (2 : ℝ) ^ (d - 1) - 1 := by
  have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at h
  linarith

private theorem two_pow_eq_two_mul (hd : 2 ≤ d) : (2 : ℝ) ^ d = 2 * (2 : ℝ) ^ (d - 1) := by
  rw [← pow_succ', Nat.sub_add_cancel (by omega)]

/-! ### Dimension two -/

theorem multivariateKendallTau_two (C : Copula 2) : C.multivariateKendallTau = C.kendallTau := by
  rw [multivariateKendallTau, kendallTau]
  norm_num

theorem multivariateSpearmanRho_two (C : Copula 2) :
    C.multivariateSpearmanRho = C.spearmanRho := by
  rw [multivariateSpearmanRho, spearmanRho_eq_integral_cdf]
  norm_num
  ring

/-! ### A Fubini identity -/

/-- **`∫ C dΠ = ∫ ∏ (1 - xᵢ) dC(x)`**: both are `P(X ≤ V)` for `X ∼ C` independent of a uniform
vector `V`. -/
theorem integral_cdf_independence_eq_prod (C : Copula d) :
    (∫ x, C.cdf x ∂(independence d).toMeasure) =
      ∫ y, ∏ i, (1 - (y i : ℝ)) ∂C.toMeasure := by
  classical
  have hf : Integrable (fun p : (Fin d → I) × (Fin d → I) =>
      if p.2 ≤ p.1 then (1 : ℝ) else 0) ((independence d).toMeasure.prod C.toMeasure) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (measurable_const.ite (measurableSet_le measurable_snd measurable_fst)
        measurable_const).aestronglyMeasurable
    · split_ifs <;> norm_num
  have hc (x : Fin d → I) : C.cdf x =
      ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure := by
    symm
    simpa [Set.indicator, cdf] using
      integral_indicator_one (μ := C.toMeasure) (s := Iic x) measurableSet_Iic
  have hi (y : Fin d → I) :
      (∫ x, if y ≤ x then (1 : ℝ) else 0 ∂(independence d).toMeasure) =
        ∏ i, (1 - (y i : ℝ)) := by
    have he : (fun x : Fin d → I => if y ≤ x then (1 : ℝ) else 0) =
        fun x => ∏ i, (if y i ≤ x i then (1 : ℝ) else 0) := by
      funext x
      split_ifs with h
      · exact (Finset.prod_eq_one fun i _ => by simp [h i]).symm
      · rw [Pi.le_def] at h
        push Not at h
        obtain ⟨i, hi⟩ := h
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [not_le.mpr hi])).symm
    rw [he, toMeasure_independence,
      integral_fintype_prod_eq_prod (fun i (t : I) => if y i ≤ t then (1 : ℝ) else 0)]
    exact Finset.prod_congr rfl fun i _ => integral_unit_upper_indicator (y i)
  calc
    (∫ x, C.cdf x ∂(independence d).toMeasure) =
        ∫ x, ∫ y, if y ≤ x then (1 : ℝ) else 0 ∂C.toMeasure ∂(independence d).toMeasure := by
      simp_rw [hc]
    _ = ∫ y, ∫ x, if y ≤ x then (1 : ℝ) else 0 ∂(independence d).toMeasure ∂C.toMeasure :=
      integral_integral_swap hf
    _ = _ := by simp_rw [hi]

/-! ### Benchmarks -/

private theorem integral_prod_coe_independence :
    (∫ x, ∏ i, (x i : ℝ) ∂(independence d).toMeasure) = (1 / 2 : ℝ) ^ d := by
  rw [toMeasure_independence, integral_fintype_prod_eq_prod (fun _ (t : I) => (t : ℝ))]
  simp

theorem multivariateKendallTau_independence :
    (independence d).multivariateKendallTau = 0 := by
  rw [multivariateKendallTau]
  simp_rw [cdf_independence]
  rw [integral_prod_coe_independence, ← mul_pow]
  norm_num

theorem multivariateSpearmanRho_independence :
    (independence d).multivariateSpearmanRho = 0 := by
  rw [multivariateSpearmanRho]
  simp_rw [cdf_independence]
  rw [integral_prod_coe_independence, ← mul_pow]
  norm_num

theorem multivariateKendallTau_comonotonic (hd : 2 ≤ d) :
    (comonotonic d).multivariateKendallTau = 1 := by
  have hint : (∫ x, (comonotonic d).cdf x ∂(comonotonic d).toMeasure) = 1 / 2 := by
    rw [integral_comonotonic _ (comonotonic d).continuous_cdf.measurable]
    have h : ∀ u : I, (comonotonic d).cdf (fun _ => u) = (u : ℝ) := by
      intro u
      rw [cdf_comonotonic]
      have hne : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      rw [ciInf_const]
    simp_rw [h]
    exact integral_unit_id
  rw [multivariateKendallTau, hint, two_pow_eq_two_mul hd]
  have := two_pow_pred_sub_one_pos hd
  field_simp

theorem multivariateSpearmanRho_comonotonic (hd : 2 ≤ d) :
    (comonotonic d).multivariateSpearmanRho = 1 := by
  have hint : (∫ x, (comonotonic d).cdf x ∂(independence d).toMeasure) = 1 / (d + 1) := by
    rw [integral_cdf_independence_eq_prod,
      integral_comonotonic _ (by fun_prop)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [integral_unitInterval (fun t => (1 - t) ^ d), intervalIntegral.integral_comp_sub_left
      (fun t => t ^ d) 1]
    simp [integral_pow]
  have h := dim_add_one_lt_two_pow hd
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hne : (2 : ℝ) ^ d - d - 1 ≠ 0 := by linarith
  rw [multivariateSpearmanRho, hint,
    show (2 : ℝ) ^ d * (1 / ((d : ℝ) + 1)) - 1 = ((2 : ℝ) ^ d - d - 1) / ((d : ℝ) + 1) by
      field_simp; ring]
  field_simp

/-! ### Bounds and monotonicity -/

/-- `ρ_d` is nondecreasing in the lower-orthant order. -/
theorem multivariateSpearmanRho_mono (hd : 2 ≤ d) {C D : Copula d} (h : C.LowerOrthantLE D) :
    C.multivariateSpearmanRho ≤ D.multivariateSpearmanRho := by
  have hi := integral_mono (C.integrable_cdf (independence d).toMeasure)
    (D.integrable_cdf (independence d).toMeasure) h
  have hc : 0 ≤ ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) := by
    have := dim_add_one_lt_two_pow hd
    apply div_nonneg (by positivity)
    linarith
  rw [multivariateSpearmanRho, multivariateSpearmanRho]
  apply mul_le_mul_of_nonneg_left _ hc
  have : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

/-- **`ρ_d ≤ 1`**, with equality at `M_d`. -/
theorem multivariateSpearmanRho_le_one (hd : 2 ≤ d) (C : Copula d) :
    C.multivariateSpearmanRho ≤ 1 := by
  rw [← multivariateSpearmanRho_comonotonic hd]
  apply multivariateSpearmanRho_mono hd
  intro u
  rw [cdf_comonotonic]
  exact C.cdf_le_frechet_upper u

/-- **`τ_d ≤ 1`**, with equality at `M_d`. -/
theorem multivariateKendallTau_le_one (hd : 2 ≤ d) (C : Copula d) :
    C.multivariateKendallTau ≤ 1 := by
  have i0 : Fin d := ⟨0, by omega⟩
  have hle : (∫ x, C.cdf x ∂C.toMeasure) ≤ ∫ x, (x i0 : ℝ) ∂C.toMeasure :=
    integral_mono (C.integrable_cdf C.toMeasure)
      (integrable_continuous_cube C.toMeasure (by fun_prop)) fun x => C.cdf_le_coord x i0
  rw [C.integral_coe_eval] at hle
  have hp := two_pow_pred_sub_one_pos hd
  rw [multivariateKendallTau, div_le_one hp, two_pow_eq_two_mul hd]
  have : (0 : ℝ) ≤ 2 ^ (d - 1) := by positivity
  nlinarith

/-- **`τ_d ≥ -1/(2^{d-1} - 1)`**, the trivial lower bound (sharp for `d = 2`). -/
theorem neg_inv_le_multivariateKendallTau (hd : 2 ≤ d) (C : Copula d) :
    -1 / ((2 : ℝ) ^ (d - 1) - 1) ≤ C.multivariateKendallTau := by
  have hnn : 0 ≤ ∫ x, C.cdf x ∂C.toMeasure := integral_nonneg fun x => C.cdf_nonneg x
  have hp := two_pow_pred_sub_one_pos hd
  rw [multivariateKendallTau]
  apply div_le_div_of_nonneg_right _ hp.le
  have : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

end ProbabilityTheory.Copula
