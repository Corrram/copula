/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Diagonal
import Copula.Families.MarshallOlkin
import Copula.Families.Gumbel

/-! # Explicit extreme-value tail coefficients

Power diagonals give the extremal coefficient and tail limits for
Marshall–Olkin, Cuadras–Augé, Gumbel–Hougaard and Tawn. Singular parameter endpoints
are included; in particular the lower tail of `M` is one.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem hasPowerDiagonal_marshallOlkin (α β : I) :
    (marshallOlkin α β).HasPowerDiagonal (2 - min (α : ℝ) (β : ℝ)) := by
  intro t
  by_cases ht : t = 0
  · have hn : 2 - min (α : ℝ) (β : ℝ) ≠ 0 := by
      have h := min_le_left (α : ℝ) (β : ℝ)
      have ha := α.property.2
      linarith
    simp [ht, Real.zero_rpow hn]
  have htp : (0 : ℝ) < t := lt_of_le_of_ne t.property.1
    (Ne.symm (fun h => ht (Subtype.ext h)))
  simp only [diagonal, cdf_marshallOlkin, Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases le_total (α : ℝ) (β : ℝ) with hab | hba
  · rw [min_eq_right (Real.rpow_le_rpow_of_exponent_ge htp t.property.2 hab),
      min_eq_left hab, ← Real.rpow_add htp, ← Real.rpow_add htp]
    congr 1
    ring
  · rw [min_eq_left (Real.rpow_le_rpow_of_exponent_ge htp t.property.2 hba),
      min_eq_right hba, ← Real.rpow_add htp, ← Real.rpow_add htp]
    congr 1
    ring

theorem extremalCoefficient_marshallOlkin (α β : I) :
    (marshallOlkin α β).extremalCoefficient = 2 - min (α : ℝ) (β : ℝ) :=
  (hasPowerDiagonal_marshallOlkin α β).extremalCoefficient_eq

theorem hasUpperTailDependence_marshallOlkin (α β : I) :
    (marshallOlkin α β).HasUpperTailDependence (min (α : ℝ) (β : ℝ)) := by
  simpa using (hasPowerDiagonal_marshallOlkin α β).hasUpperTailDependence

theorem hasLowerTailDependence_marshallOlkin (α β : I) :
    (marshallOlkin α β).HasLowerTailDependence (if α = 1 ∧ β = 1 then 1 else 0) := by
  have he : 2 - min (α : ℝ) (β : ℝ) = 1 ↔ α = 1 ∧ β = 1 := by
    constructor
    · intro h
      have hm : 1 ≤ min (α : ℝ) (β : ℝ) := by linarith
      exact ⟨Subtype.ext (le_antisymm α.property.2 (le_min_iff.1 hm).1),
        Subtype.ext (le_antisymm β.property.2 (le_min_iff.1 hm).2)⟩
    · rintro ⟨rfl, rfl⟩
      norm_num
  simpa only [he] using (hasPowerDiagonal_marshallOlkin α β).hasLowerTailDependence

theorem hasPowerDiagonal_cuadrasAuge (α : I) :
    (cuadrasAuge α).HasPowerDiagonal (2 - (α : ℝ)) := by
  simpa only [cuadrasAuge, min_self] using hasPowerDiagonal_marshallOlkin α α

theorem extremalCoefficient_cuadrasAuge (α : I) :
    (cuadrasAuge α).extremalCoefficient = 2 - (α : ℝ) :=
  (hasPowerDiagonal_cuadrasAuge α).extremalCoefficient_eq

theorem hasUpperTailDependence_cuadrasAuge (α : I) :
    (cuadrasAuge α).HasUpperTailDependence (α : ℝ) := by
  simpa only [cuadrasAuge, min_self] using hasUpperTailDependence_marshallOlkin α α

theorem hasLowerTailDependence_cuadrasAuge (α : I) :
    (cuadrasAuge α).HasLowerTailDependence (if α = 1 then 1 else 0) := by
  simpa only [cuadrasAuge, and_self] using hasLowerTailDependence_marshallOlkin α α

theorem hasPowerDiagonal_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).HasPowerDiagonal ((2 : ℝ) ^ θ⁻¹) := by
  intro t
  by_cases ht : t = 0
  · simp [ht, Real.zero_rpow (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) θ⁻¹))]
  have htp : (0 : ℝ) < t := lt_of_le_of_ne t.property.1
    (Ne.symm (fun h => ht (Subtype.ext h)))
  have hl : 0 ≤ -Real.log (t : ℝ) := neg_nonneg.mpr (Real.log_nonpos t.property.1 t.property.2)
  have hne : θ ≠ 0 := by linarith
  rw [diagonal, cdf_gumbel θ hθ _ (by intro i; fin_cases i <;> exact ht)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← two_mul]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hl _),
    Real.rpow_rpow_inv hl hne, Real.rpow_def_of_pos htp]
  congr 1
  ring

theorem extremalCoefficient_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).extremalCoefficient = (2 : ℝ) ^ θ⁻¹ :=
  (hasPowerDiagonal_gumbel θ hθ).extremalCoefficient_eq

theorem hasUpperTailDependence_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  (hasPowerDiagonal_gumbel θ hθ).hasUpperTailDependence

theorem hasLowerTailDependence_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).HasLowerTailDependence 0 := by
  apply (hasPowerDiagonal_gumbel θ hθ).hasLowerTailDependence_zero
  simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (inv_pos.mpr (by linarith : 0 < θ))

private theorem tawn_exponent_gt_one (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    1 < 2 - (α : ℝ) - (β : ℝ) + ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹ := by
  have hθ0 : 0 < θ := by linarith
  have ha : (α : ℝ) ≤ ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹ := by
    calc
      (α : ℝ) = ((α : ℝ) ^ θ) ^ θ⁻¹ := (Real.rpow_rpow_inv α.property.1 hθ0.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg α.property.1 _)
        (le_add_of_nonneg_right (Real.rpow_nonneg β.property.1 _)) (inv_nonneg.mpr hθ0.le)
  have hb : (β : ℝ) ≤ ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹ := by
    calc
      (β : ℝ) = ((β : ℝ) ^ θ) ^ θ⁻¹ := (Real.rpow_rpow_inv β.property.1 hθ0.ne').symm
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg β.property.1 _)
        (le_add_of_nonneg_left (Real.rpow_nonneg α.property.1 _)) (inv_nonneg.mpr hθ0.le)
  by_cases ha1 : α = 1
  · by_cases hb1 : β = 1
    · simp only [ha1, hb1]
      have hp := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (inv_pos.mpr hθ0)
      norm_num at hp ⊢
      exact hp
    · have hbl : (β : ℝ) < 1 := lt_of_le_of_ne β.property.2 (fun h => hb1 (Subtype.ext h))
      linarith
  · have hal : (α : ℝ) < 1 := lt_of_le_of_ne α.property.2 (fun h => ha1 (Subtype.ext h))
    linarith

theorem hasPowerDiagonal_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).HasPowerDiagonal
      (2 - (α : ℝ) - (β : ℝ) + ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) := by
  intro t
  by_cases ht : t = 0
  · simp [ht, Real.zero_rpow (show
        2 - (α : ℝ) - (β : ℝ) + ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹ ≠ 0 by
          linarith [tawn_exponent_gt_one θ hθ α β])]
  have htp : (0 : ℝ) < t := lt_of_le_of_ne t.property.1
    (Ne.symm (fun h => ht (Subtype.ext h)))
  have hl : 0 ≤ -Real.log (t : ℝ) := neg_nonneg.mpr (Real.log_nonpos t.property.1 t.property.2)
  have hne : θ ≠ 0 := by linarith
  have hu (i : Fin 2) : unitPower (![t, t] i) (![α, β] i) (![α, β] i).property.1 ≠ 0 := by
    intro he
    have hz := congrArg (fun x : I => (x : ℝ)) he
    have hi : (0 : ℝ) < (![t, t] i : I) := by fin_cases i <;> exact htp
    exact (Real.rpow_pos_of_pos hi _).ne' hz
  rw [diagonal, tawn, cdf_maxProduct, cdf_gumbel θ hθ _ hu, cdf_independence]
  simp only [Fin.prod_univ_two, coe_unitPower, Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq, Real.log_rpow htp, neg_mul_eq_mul_neg]
  rw [Real.mul_rpow α.property.1 hl, Real.mul_rpow β.property.1 hl, ← add_mul,
    Real.mul_rpow (add_nonneg (Real.rpow_nonneg α.property.1 _) (Real.rpow_nonneg β.property.1 _))
      (Real.rpow_nonneg hl _), Real.rpow_rpow_inv hl hne]
  have he : Real.exp (-(((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹ * -Real.log (t : ℝ))) =
      (t : ℝ) ^ (((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) := by
    rw [Real.rpow_def_of_pos htp]
    congr 1
    ring
  rw [he, ← Real.rpow_add htp, ← Real.rpow_add htp]
  congr 1
  ring

theorem extremalCoefficient_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).extremalCoefficient =
      2 - (α : ℝ) - (β : ℝ) + ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹ :=
  (hasPowerDiagonal_tawn θ hθ α β).extremalCoefficient_eq

theorem hasUpperTailDependence_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).HasUpperTailDependence
      ((α : ℝ) + (β : ℝ) - ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) := by
  convert (hasPowerDiagonal_tawn θ hθ α β).hasUpperTailDependence using 1
  ring

theorem hasLowerTailDependence_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (tawn θ hθ α β).HasLowerTailDependence 0 :=
  (hasPowerDiagonal_tawn θ hθ α β).hasLowerTailDependence_zero (tawn_exponent_gt_one θ hθ α β)

end ProbabilityTheory.Copula
