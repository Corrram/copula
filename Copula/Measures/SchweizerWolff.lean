/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Measures.Deviation
import Copula.Dependence.Rank
import Copula.Dependence.Singular
import Copula.Rank.FGM

/-! # The Schweizer–Wolff measure of dependence

The Schweizer–Wolff measure is `σ(C) = 12 ∫∫ |C(u,v) - u v| du dv`
(Nelsen, *An Introduction to Copulas*, 2nd ed., Section 5.3).
We prove: `σ ≥ 0`, `σ(Π) = 0`, `σ(M) = σ(W) = 1`, `|ρ| ≤ σ`, invariance under
transposition and survival copulas, `σ = |ρ|` for quadrant dependent copulas
(Nelsen Section 5.3), `σ(C) = 0` if and only if `C = Π`, and the
value `|θ| / 3` on the Farlie–Gumbel–Morgenstern family.

The upper bound `σ ≤ 1` for all copulas is not proved here.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Schweizer–Wolff measure of dependence of a bivariate copula:
`σ(C) = 12 ∫∫ |C(u,v) - u v| du dv`. -/
noncomputable def schweizerWolff (C : Copula 2) : ℝ :=
  12 * ∫ x, |C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)| ∂(independence 2).toMeasure

theorem schweizerWolff_nonneg (C : Copula 2) : 0 ≤ C.schweizerWolff := by
  unfold schweizerWolff
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => abs_nonneg _)

/-- Spearman's rho is bounded in absolute value by the Schweizer–Wolff measure. -/
theorem abs_spearmanRho_le_schweizerWolff (C : Copula 2) : |C.spearmanRho| ≤ C.schweizerWolff := by
  have h : |∫ x, (C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure| ≤
      ∫ x, |C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)| ∂(independence 2).toMeasure :=
    abs_integral_le_integral_abs
  rw [spearmanRho_eq_twelve_integral_cdf_sub, abs_mul, abs_of_pos (show (0 : ℝ) < 12 by norm_num)]
  unfold schweizerWolff
  linarith

@[simp] theorem schweizerWolff_independence : (independence 2).schweizerWolff = 0 := by
  have hf : ∀ x : Fin 2 → I,
      |(independence 2).cdf x - (x 0 : ℝ) * (x 1 : ℝ)| = 0 := by
    intro x
    rw [cdf_independence_two, sub_self, abs_zero]
  unfold schweizerWolff
  simp only [hf, integral_zero, mul_zero]

@[simp] theorem schweizerWolff_transpose (C : Copula 2) :
    C.transpose.schweizerWolff = C.schweizerWolff := by
  unfold schweizerWolff
  exact congrArg (fun z : ℝ => 12 * z)
    (integral_comp_cdf_sub_transpose (fun t : ℝ => |t|) continuous_abs C)

@[simp] theorem schweizerWolff_survivalCopula (C : Copula 2) :
    C.survivalCopula.schweizerWolff = C.schweizerWolff := by
  unfold schweizerWolff
  exact congrArg (fun z : ℝ => 12 * z)
    (integral_comp_cdf_sub_survival (fun t : ℝ => |t|) continuous_abs C)

/-- `σ(C) = 0` forces `C` to be the independence copula. -/
theorem eq_independence_of_schweizerWolff_eq_zero {C : Copula 2} (h : C.schweizerWolff = 0) :
    C = independence 2 := by
  have h' : (∫ x, |C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)| ∂(independence 2).toMeasure) = 0 := by
    unfold schweizerWolff at h
    linarith
  exact eq_independence_of_integral_comp_eq_zero (φ := fun t : ℝ => |t|) (C := C)
    continuous_abs (fun t => abs_nonneg t) (fun t ht => abs_eq_zero.mp ht) h'

/-- The Schweizer–Wolff measure vanishes exactly at the independence copula. -/
theorem schweizerWolff_eq_zero_iff (C : Copula 2) : C.schweizerWolff = 0 ↔ C = independence 2 := by
  constructor
  · exact eq_independence_of_schweizerWolff_eq_zero
  · rintro rfl
    exact schweizerWolff_independence

theorem IsPQD.mul_le_cdf {C : Copula 2} (h : C.IsPQD) (x : Fin 2 → I) :
    (x 0 : ℝ) * (x 1 : ℝ) ≤ C.cdf x := by
  have he : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  have h2 := h (x 0) (x 1)
  rwa [he] at h2

theorem IsNQD.cdf_le_mul {C : Copula 2} (h : C.IsNQD) (x : Fin 2 → I) :
    C.cdf x ≤ (x 0 : ℝ) * (x 1 : ℝ) := by
  have he : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  have h2 := h (x 0) (x 1)
  rwa [he] at h2

/-- For positive quadrant dependent copulas, `σ = ρ`. -/
theorem IsPQD.schweizerWolff_eq_spearmanRho {C : Copula 2} (h : C.IsPQD) :
    C.schweizerWolff = C.spearmanRho := by
  rw [spearmanRho_eq_twelve_integral_cdf_sub]
  unfold schweizerWolff
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact abs_of_nonneg (sub_nonneg.mpr (h.mul_le_cdf x))

/-- For negative quadrant dependent copulas, `σ = -ρ`. -/
theorem IsNQD.schweizerWolff_eq_neg_spearmanRho {C : Copula 2} (h : C.IsNQD) :
    C.schweizerWolff = -C.spearmanRho := by
  rw [spearmanRho_eq_twelve_integral_cdf_sub]
  unfold schweizerWolff
  have hi : (∫ x, |C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)| ∂(independence 2).toMeasure) =
      ∫ x, -(C.cdf x - (x 0 : ℝ) * (x 1 : ℝ)) ∂(independence 2).toMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    exact abs_of_nonpos (sub_nonpos.mpr (h.cdf_le_mul x))
  rw [hi, integral_neg]
  ring

/-- For positive quadrant dependent copulas, `σ = |ρ|`. -/
theorem IsPQD.schweizerWolff_eq_abs_spearmanRho {C : Copula 2} (h : C.IsPQD) :
    C.schweizerWolff = |C.spearmanRho| := by
  have h1 := h.schweizerWolff_eq_spearmanRho
  have h0 := C.schweizerWolff_nonneg
  rw [h1] at h0
  rw [h1, abs_of_nonneg h0]

/-- For negative quadrant dependent copulas, `σ = |ρ|`. -/
theorem IsNQD.schweizerWolff_eq_abs_spearmanRho {C : Copula 2} (h : C.IsNQD) :
    C.schweizerWolff = |C.spearmanRho| := by
  have h1 := h.schweizerWolff_eq_neg_spearmanRho
  have h0 := C.schweizerWolff_nonneg
  rw [h1] at h0
  have h2 : C.spearmanRho ≤ 0 := by linarith
  rw [h1, abs_of_nonpos h2]

@[simp] theorem schweizerWolff_comonotonic : (comonotonic 2).schweizerWolff = 1 := by
  have hM : (comonotonic 2).IsPQD :=
    (isPQD_iff_independence_le _).mpr fun x => cdf_le_comonotonic (independence 2) x
  rw [hM.schweizerWolff_eq_spearmanRho, spearmanRho_comonotonic]

@[simp] theorem schweizerWolff_countermonotonic : countermonotonic.schweizerWolff = 1 := by
  rw [isNQD_countermonotonic.schweizerWolff_eq_neg_spearmanRho,
    spearmanRho_countermonotonic, neg_neg]

/-- The Schweizer–Wolff measure of the Farlie–Gumbel–Morgenstern copula is `|θ| / 3`. -/
theorem schweizerWolff_fgm (θ : ℝ) (hθ : |θ| ≤ 1) : (fgm θ hθ).schweizerWolff = |θ| / 3 := by
  have hf : ∀ x : Fin 2 → I, |(fgm θ hθ).cdf x - (x 0 : ℝ) * (x 1 : ℝ)| =
      |θ| * (((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ)))) := by
    intro x
    have h0 : 0 ≤ (x 0 : ℝ) * (1 - (x 0 : ℝ)) :=
      mul_nonneg (x 0).property.1 (sub_nonneg.mpr (x 0).property.2)
    have h1 : 0 ≤ (x 1 : ℝ) * (1 - (x 1 : ℝ)) :=
      mul_nonneg (x 1).property.1 (sub_nonneg.mpr (x 1).property.2)
    have h2 : (fgm θ hθ).cdf x - (x 0 : ℝ) * (x 1 : ℝ) =
        θ * (((x 0 : ℝ) * (1 - (x 0 : ℝ))) * ((x 1 : ℝ) * (1 - (x 1 : ℝ)))) := by
      rw [cdf_fgm]
      unfold fgmCDF
      ring
    rw [h2, abs_mul, abs_of_nonneg (mul_nonneg h0 h1)]
  unfold schweizerWolff
  simp only [hf]
  rw [integral_const_mul, integral_independence_mul (fun t : I => (t : ℝ) * (1 - (t : ℝ)))
    (fun t : I => (t : ℝ) * (1 - (t : ℝ))), integral_unit_mul_one_sub]
  ring

end ProbabilityTheory.Copula
