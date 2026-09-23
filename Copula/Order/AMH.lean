/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.AMH
import Copula.Order.Rank

/-! # Exact lower-orthant parameter ordering of Ali–Mikhail–Haq copulas -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem amh_rational_den_pos (θ : ℝ) (hθ : θ ≤ 1) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    0 < 1 - θ * (1 - (u : ℝ)) * (1 - (v : ℝ)) := by
  have huc : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
  have hvc : 0 ≤ 1 - (v : ℝ) := sub_nonneg.mpr v.property.2
  have hp : 0 ≤ (1 - (u : ℝ)) * (1 - (v : ℝ)) := mul_nonneg huc hvc
  have hple : (1 - (u : ℝ)) * (1 - (v : ℝ)) < 1 := by
    have h := mul_le_mul_of_nonneg_left
      (show 1 - (v : ℝ) ≤ 1 by linarith) huc
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hθ hp
  nlinarith

private theorem cdf_amh_half (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).cdf ![unitHalf, unitHalf] = 1 / (4 - θ) := by
  rw [cdf_amh]
  norm_num [unitHalf]
  have hd : 4 - θ ≠ 0 := by linarith
  field_simp [hd]
  calc
    _ = 4 * ((4 - θ) * (4 - θ)⁻¹) := by ring
    _ = 4 := by rw [mul_inv_cancel₀ hd]; ring

/-- AMH copulas are ordered by their parameters, with no missing comparisons. -/
theorem lowerOrthantLE_amh_iff {θ η : ℝ}
    (hθmin : -1 ≤ θ) (hθmax : θ ≤ 1)
    (hηmin : -1 ≤ η) (hηmax : η ≤ 1) :
    (amh θ hθmin hθmax).LowerOrthantLE (amh η hηmin hηmax) ↔ θ ≤ η := by
  constructor
  · intro h
    have hh := h ![unitHalf, unitHalf]
    rw [cdf_amh_half θ hθmin hθmax, cdf_amh_half η hηmin hηmax] at hh
    have hdθ : 0 < 4 - θ := by linarith
    have hdη : 0 < 4 - η := by linarith
    have hh' := (div_le_div_iff₀ hdθ hdη).mp hh
    nlinarith
  · intro h u
    by_cases hu : u 0 = 0
    · have hzθ := (amh θ hθmin hθmax).cdf_eq_zero_of_coord_eq_zero u 0 hu
      have hzη := (amh η hηmin hηmax).cdf_eq_zero_of_coord_eq_zero u 0 hu
      rw [hzθ, hzη]
    by_cases hv : u 1 = 0
    · have hzθ := (amh θ hθmin hθmax).cdf_eq_zero_of_coord_eq_zero u 1 hv
      have hzη := (amh η hηmin hηmax).cdf_eq_zero_of_coord_eq_zero u 1 hv
      rw [hzθ, hzη]
    have hup : 0 < (u 0 : ℝ) :=
      lt_of_le_of_ne (u 0).property.1 (Ne.symm (by
        intro he; exact hu (Subtype.ext he)))
    have hvp : 0 < (u 1 : ℝ) :=
      lt_of_le_of_ne (u 1).property.1 (Ne.symm (by
        intro he; exact hv (Subtype.ext he)))
    have hdη := amh_rational_den_pos η hηmax (u 0) (u 1) hup hvp
    have hp : 0 ≤ (1 - (u 0 : ℝ)) * (1 - (u 1 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr (u 0).property.2)
        (sub_nonneg.mpr (u 1).property.2)
    have hden : 1 - η * (1 - (u 0 : ℝ)) * (1 - (u 1 : ℝ)) ≤
        1 - θ * (1 - (u 0 : ℝ)) * (1 - (u 1 : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_right h hp]
    have hdiv := div_le_div_of_nonneg_left
      (mul_nonneg (u 0).property.1 (u 1).property.1) hdη hden
    have huvec : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [huvec, cdf_amh, cdf_amh]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using hdiv

end ProbabilityTheory.Copula
