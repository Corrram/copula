/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Bivariate

/-! # The bivariate Farlie–Gumbel–Morgenstern family -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The FGM polynomial, including its boundary values. -/
def fgmCDF (θ : ℝ) (u v : I) : ℝ :=
  (u : ℝ) * (v : ℝ) * (1 + θ * (1 - (u : ℝ)) * (1 - (v : ℝ)))

theorem isClassical_fgmCDF (θ : ℝ) (hθ : |θ| ≤ 1) :
    IsClassical (fun u : Fin 2 → I => fgmCDF θ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate _ (by intro v; simp [fgmCDF])
    (by intro u; simp [fgmCDF]) (by intro v; simp [fgmCDF]) (by intro u; simp [fgmCDF])
  intro a b c e hab hce
  have h₁ : |1 - (a : ℝ) - (b : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [a.property.1, a.property.2, b.property.1, b.property.2]
  have h₂ : |1 - (c : ℝ) - (e : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [c.property.1, c.property.2, e.property.1, e.property.2]
  have hp : |θ * (1 - (a : ℝ) - (b : ℝ)) * (1 - (c : ℝ) - (e : ℝ))| ≤ 1 := by
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg θ, abs_nonneg (1 - (a : ℝ) - (b : ℝ)),
      abs_nonneg (1 - (c : ℝ) - (e : ℝ)),
      mul_le_mul hθ h₁ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  have hlast : 0 ≤ 1 + θ * (1 - (a : ℝ) - (b : ℝ)) * (1 - (c : ℝ) - (e : ℝ)) := by
    linarith [(abs_le.mp hp).1]
  have heq : fgmCDF θ b e - fgmCDF θ a e - fgmCDF θ b c + fgmCDF θ a c =
      ((b : ℝ) - (a : ℝ)) * ((e : ℝ) - (c : ℝ)) *
        (1 + θ * (1 - (a : ℝ) - (b : ℝ)) * (1 - (c : ℝ) - (e : ℝ))) := by
    unfold fgmCDF; ring
  rw [heq]
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hce)) hlast

/-- FGM copulas for the full parameter interval `[-1,1]`. -/
noncomputable def fgm (θ : ℝ) (hθ : |θ| ≤ 1) : Copula 2 :=
  ofClassical _ (isClassical_fgmCDF θ hθ)

@[simp] theorem cdf_fgm (θ : ℝ) (hθ : |θ| ≤ 1) (u : Fin 2 → I) :
    (fgm θ hθ).cdf u = fgmCDF θ (u 0) (u 1) := congrFun (cdf_ofClassical _ _) u

@[simp] theorem fgm_zero : fgm 0 (by norm_num) = independence 2 := by
  apply ext_cdf; intro u
  simp [fgmCDF, cdf_independence, Fin.prod_univ_two]

end ProbabilityTheory.Copula
