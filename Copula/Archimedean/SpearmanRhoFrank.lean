/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.SpearmanRhoFrankCore
import Copula.Archimedean.SpearmanRhoGenerator
import Copula.Families.FrankNegative

/-! # Spearman's rho of the Frank family in Debye form

Nelsen, *An Introduction to Copulas*, second edition, Example 5.8 and Table 4.1 (family 4.2.5);
Genest (1987): for Frank's copula with parameter `θ ≠ 0`,
`ρ_θ = 1 − (12/θ) (D₁(θ) − D₂(θ))`, where `D₁ = debyeOne` and `D₂ = debyeTwo` are the Debye
functions of orders one and two.

The proof does not differentiate in `θ` under the integral sign. Writing Frank's cdf as
`θ⁻¹ L θ (θ u) (θ v)` (`FrankRho.L`), the double integral is evaluated in
`Copula.Archimedean.SpearmanRhoFrankCore` by expressing `L θ x y` as
`min x y + ∫_{max x y}^θ ∂_s L s x y ds` and exchanging the order of integration.
The case `θ < 0` follows from `ρ(C^{σ₂}) = −ρ(C)` and the reflection identities
`D₁(−x) = D₁(x) + x/2`, `D₂(−x) = D₂(x) + 2x/3`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace FrankRho

theorem L_comm (θ x y : ℝ) : L θ x y = L θ y x := by
  unfold L; rw [mul_comm (w x)]

/-- Frank's cdf on the whole closed unit square, as `θ⁻¹ L θ (θ u) (θ v)`. -/
theorem frank_cdf_eq_L (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (frank θ hθ).cdf ![u, v] = θ⁻¹ * L θ (θ * u) (θ * v) := by
  have hL : L θ (θ * u) (θ * v) =
      -Real.log (1 - (1 - Real.exp (-θ * (u : ℝ))) * (1 - Real.exp (-θ * (v : ℝ))) /
        (1 - Real.exp (-θ))) := by
    unfold L w
    simp only [neg_mul]
  rw [frank_cdf_full, hL]
  split_ifs with h
  · rcases h with h | h
    · have : (u : ℝ) = 0 := by rw [h]; rfl
      simp [this]
    · have : (v : ℝ) = 0 := by rw [h]; rfl
      simp [this]
  · ring

end FrankRho

/-- Double-integral form of Spearman's rho of Frank's copula (`θ > 0`):
`ρ = 12 θ⁻³ ∫₀^θ ∫₀^θ (-log (1 - (1 - e^{-x})(1 - e^{-y}) / (1 - e^{-θ}))) dy dx - 3`. -/
theorem spearmanRho_frank_integral (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).spearmanRho = 12 * (θ⁻¹ ^ 3 *
      ∫ x in (0 : ℝ)..θ, ∫ y in (0 : ℝ)..θ, FrankRho.L θ x y) - 3 := by
  rw [RankRegion.Common.spearmanRho_eq_iterated_cdf]
  congr 2
  simp_rw [FrankRho.frank_cdf_eq_L θ hθ]
  have h1 : ∀ v : ℝ, (∫ u : I, θ⁻¹ * FrankRho.L θ (θ * u) (θ * v)) =
      θ⁻¹ * (θ⁻¹ * ∫ x in (0 : ℝ)..θ, FrankRho.L θ x (θ * v)) := by
    intro v
    rw [integral_const_mul,
      integral_unitInterval (fun u : ℝ => FrankRho.L θ (θ * u) (θ * v)),
      intervalIntegral.integral_comp_mul_left (fun x => FrankRho.L θ x (θ * v)) hθ.ne']
    simp
  simp_rw [h1]
  rw [integral_const_mul,
    integral_unitInterval (fun v : ℝ => θ⁻¹ * ∫ x in (0 : ℝ)..θ, FrankRho.L θ x (θ * v)),
    intervalIntegral.integral_const_mul]
  have h2 := intervalIntegral.integral_comp_mul_left
    (fun y => ∫ x in (0 : ℝ)..θ, FrankRho.L θ x y) (a := 0) (b := 1) hθ.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at h2
  rw [h2]
  simp_rw [FrankRho.L_comm θ _ _] at *
  ring

/-- **Spearman's rho of Frank's copula** (Nelsen, Example 5.8; Genest 1987), `θ > 0`:
`ρ = 1 − (12/θ)(D₁(θ) − D₂(θ))`. -/
theorem spearmanRho_frank_debye (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).spearmanRho = 1 - 12 / θ * (debyeOne θ - debyeTwo θ) := by
  rw [spearmanRho_frank_integral, FrankRho.H_eq hθ]
  have hS : FrankRho.S θ = θ * debyeOne θ := by
    unfold FrankRho.S debyeOne; field_simp
  have hT : FrankRho.T θ = θ ^ 2 / 2 * debyeTwo θ := by
    unfold FrankRho.T debyeTwo; field_simp
  rw [hS, hT]
  field_simp
  ring

/-- **Spearman's rho of Frank's copula** for negative parameters, `θ < 0`:
`ρ = 1 − (12/θ)(D₁(θ) − D₂(θ))`. -/
theorem spearmanRho_frankNegative_debye (θ : ℝ) (hθ : θ < 0) :
    (frankNegative θ hθ).spearmanRho = 1 - 12 / θ * (debyeOne θ - debyeTwo θ) := by
  have hx : 0 < -θ := neg_pos.mpr hθ
  rw [frankNegative, spearmanRho_reflect_second, spearmanRho_frank_debye (-θ) hx]
  have h1 := debyeOne_neg hx
  have h2 := debyeTwo_neg hx
  rw [neg_neg] at h1 h2
  rw [h1, h2]
  have hθ0 : θ ≠ 0 := hθ.ne
  field_simp
  ring

end ProbabilityTheory.Copula
