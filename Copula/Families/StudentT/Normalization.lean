/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.StudentT.Distribution
import Copula.Elliptical.StudentTTail.Polar

/-! # The normalizing constant of the Student-t density

We compute the Wallis-type integral

`∫_{−π/2}^{π/2} cos^p θ dθ = √π Γ((p+1)/2) / Γ(p/2 + 1)`,  `p > −1`,

by evaluating `E[Z^p ; Z > 0]` for a standard normal `Z` in two ways: directly through the
Gamma integral, and in polar coordinates (`integral_gaussianReal_prod_of_polar`). With the tan
substitution of `Copula.Families.StudentT.Distribution` this gives the classical density

`t_n(x) = Γ((n+1)/2) / (√(nπ) Γ(n/2)) · (1 + x²/n)^{−(n+1)/2}`.

## Main results
* `integral_cos_rpow_symm_eq_Gamma`: the Wallis integral for real exponents `p > −1`.
* `integral_studentTKernel_eq_Gamma`: `∫ (1 + y²/n)^{−(n+1)/2} dy = √(nπ) Γ(n/2)/Γ((n+1)/2)`.
* `studentTPDF_eq`: the closed form of the Student-t density.
-/

open MeasureTheory Set Real

namespace ProbabilityTheory

open Copula

private theorem gaussian_exp_rewrite (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-(1 / 2) * x ^ (2 : ℝ)) := by
  simp only [gaussianPDFReal, sub_zero, NNReal.coe_one, mul_one, rpow_two]
  congr 2
  ring

/-- `E[Z^p ; Z > 0] = (2π)^{−1/2} 2^{(p+1)/2} Γ((p+1)/2) / 2` for a standard normal `Z`. -/
theorem integral_Ioi_rpow_gaussianReal {p : ℝ} (hp : -1 < p) :
    ∫ x, (Ioi (0 : ℝ)).indicator (fun x => x ^ p) x ∂gaussianReal 0 1 =
      (√(2 * π))⁻¹ * ((1 / 2) ^ (-(p + 1) / 2) * (1 / 2) * Gamma ((p + 1) / 2)) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, ← indicator_mul_right]
  rw [integral_indicator measurableSet_Ioi]
  simp_rw [gaussian_exp_rewrite, mul_comm ((√(2 * π))⁻¹ * _) _, mul_left_comm _ (√(2 * π))⁻¹]
  rw [integral_const_mul, _root_.integral_rpow_mul_exp_neg_mul_rpow two_pos hp one_half_pos]

/-- The angular integral of `θ ↦ cos^p θ` restricted to `cos θ > 0`. -/
private theorem integral_Ioo_indicator_cos {p : ℝ} :
    ∫ θ in Ioo (-π) π, (Ioi (0 : ℝ)).indicator (fun x => x ^ p) (cos θ) =
      ∫ θ in -(π / 2)..π / 2, cos θ ^ p := by
  have hπ := pi_pos
  have hzero : ∀ θ ∈ Ioo (-π) π \ Ioo (-(π / 2)) (π / 2),
      (Ioi (0 : ℝ)).indicator (fun x => x ^ p) (cos θ) = 0 := by
    intro θ hθ
    have hc : cos θ ≤ 0 := by
      rcases le_or_gt θ (-(π / 2)) with h | h
      · rw [← cos_neg]
        exact cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hθ.1.1])
      · have h2 : π / 2 ≤ θ := by
          by_contra h3
          exact hθ.2 ⟨h, not_le.1 h3⟩
        exact cos_nonpos_of_pi_div_two_le_of_le h2 (by linarith [hθ.1.2])
    simp [not_lt.2 hc]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
    (Ioo_subset_Ioo (by linarith) (by linarith)) hzero,
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  simp [cos_pos_of_mem_Ioo hθ]

/-- **Wallis integral** for real exponents:
`∫_{−π/2}^{π/2} cos^p θ dθ = √π Γ((p+1)/2) / Γ(p/2 + 1)` for `p > −1`. -/
theorem integral_cos_rpow_symm_eq_Gamma {p : ℝ} (hp : -1 < p) :
    ∫ θ in -(π / 2)..π / 2, cos θ ^ p = √π * Gamma ((p + 1) / 2) / Gamma (p / 2 + 1) := by
  have hπ := pi_pos
  -- polar coordinates
  have hpolar := integral_gaussianReal_prod_of_polar (ν := p)
    (fun z : ℝ × ℝ => (Ioi (0 : ℝ)).indicator (fun x => x ^ p) z.1)
    (fun θ => (Ioi (0 : ℝ)).indicator (fun x => x ^ p) (cos θ)) (fun ρ θ hρ _ => by
      simp only
      by_cases hc : 0 < cos θ
      · rw [indicator_of_mem (show ρ * cos θ ∈ Ioi (0 : ℝ) from mul_pos hρ hc),
          indicator_of_mem (show cos θ ∈ Ioi (0 : ℝ) from hc), mul_rpow hρ.le hc.le]
      · rw [indicator_of_notMem (show ρ * cos θ ∉ Ioi (0 : ℝ) from
            fun h => hc (pos_of_mul_pos_right h hρ.le)),
          indicator_of_notMem (show cos θ ∉ Ioi (0 : ℝ) from hc), mul_zero])
  have hfst := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : ℝ => (Ioi (0 : ℝ)).indicator (fun x => x ^ p) x)
  rw [probReal_univ, one_smul] at hfst
  rw [hfst, integral_Ioi_rpow_gaussianReal hp, integral_Ioo_indicator_cos] at hpolar
  -- the radial moment
  have hR : gaussianRadialMoment p =
      (2 * π)⁻¹ * ((1 / 2) ^ (-(p + 1 + 1) / 2) * (1 / 2) * Gamma ((p + 1 + 1) / 2)) := by
    rw [gaussianRadialMoment]
    simp_rw [gaussianPDFReal_mul_gaussianPDFReal_zero, mul_left_comm _ (2 * π)⁻¹]
    rw [integral_const_mul, _root_.integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith)
      one_half_pos]
  have hRpos := gaussianRadialMoment_pos (by linarith : -2 < p)
  have hW : ∫ θ in -(π / 2)..π / 2, cos θ ^ p =
      (√(2 * π))⁻¹ * ((1 / 2) ^ (-(p + 1) / 2) * (1 / 2) * Gamma ((p + 1) / 2)) /
        gaussianRadialMoment p := by
    rw [hpolar, mul_div_cancel_left₀ _ hRpos.ne']
  rw [hW, hR]
  have hsplit : (1 / 2 : ℝ) ^ (-(p + 1) / 2) =
      (1 / 2) ^ (-(p + 1 + 1) / 2) * (1 / 2) ^ (1 / 2 : ℝ) := by
    rw [← rpow_add (by norm_num)]
    congr 1
    ring
  have hhalf : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = √(1 / 2) := (Real.sqrt_eq_rpow _).symm
  have hsq : √(2 * π) * √(1 / 2) = √π := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hG1 : 0 < Gamma ((p + 1 + 1) / 2) := Gamma_pos_of_pos (by linarith)
  have hG2 : (p + 1 + 1) / 2 = p / 2 + 1 := by ring
  have hpow : 0 < (1 / 2 : ℝ) ^ (-(p + 1 + 1) / 2) := by positivity
  have hsqrt : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  rw [hsplit, hhalf, ← hG2, ← hsq]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- The total mass of the Student-t kernel:
`∫ (1 + y²/n)^{−(n+1)/2} dy = √(nπ) Γ(n/2) / Γ((n+1)/2)`. -/
theorem integral_studentTKernel_eq_Gamma {n : ℝ} (hn : 0 < n) :
    ∫ y, studentTKernel n y = √(n * π) * Gamma (n / 2) / Gamma ((n + 1) / 2) := by
  rw [integral_studentTKernel hn, integral_cos_rpow_symm_eq_Gamma (by linarith),
    Real.sqrt_mul hn.le]
  have h1 : (n - 1 + 1) / 2 = n / 2 := by ring
  have h2 : (n - 1) / 2 + 1 = (n + 1) / 2 := by ring
  rw [h1, h2]
  ring

/-- **The Student-t density**: `t_n(x) = Γ((n+1)/2) / (√(nπ) Γ(n/2)) (1 + x²/n)^{−(n+1)/2}`. -/
theorem studentTPDF_eq {n : ℝ} (hn : 0 < n) (x : ℝ) :
    studentTPDF n x = Gamma ((n + 1) / 2) / (√(n * π) * Gamma (n / 2)) *
      (1 + x ^ 2 / n) ^ (-(n + 1) / 2) := by
  rw [studentTPDF, integral_studentTKernel_eq_Gamma hn, studentTKernel]
  have : 0 < Gamma ((n + 1) / 2) := Gamma_pos_of_pos (by linarith)
  have : 0 < Gamma (n / 2) := Gamma_pos_of_pos (by linarith)
  have : 0 < √(n * π) := Real.sqrt_pos.2 (by positivity)
  field_simp

end ProbabilityTheory
