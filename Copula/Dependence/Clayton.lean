/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Clayton.CDF
import Copula.Families.Clayton.Negative
import Copula.Dependence.Basic

/-! # Positive quadrant dependence for the Clayton family -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The bivariate Clayton CDF for positive parameters at positive coordinates. -/
theorem cdf_clayton_two_pos (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    (Copula.clayton 2 θ hθ).cdf ![u, v] =
      ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) ^ (-1 / θ) := by
  have h : ∀ i : Fin 2, 0 < (![u, v] i : ℝ) := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  convert Copula.cdf_clayton θ hθ ![u, v] h using 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ring

/-- Positive Clayton parameters are positively quadrant dependent. -/
theorem isPQD_clayton_positive (θ : ℝ) (hθ : 0 < θ) :
    (Copula.clayton 2 θ hθ).IsPQD := by
  intro u v
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · simp only [hv0, Set.Icc.coe_zero, mul_zero]
    exact (Copula.clayton 2 θ hθ).cdf_nonneg ![u, 0]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  let x := (u : ℝ) ^ (-θ)
  let y := (v : ℝ) ^ (-θ)
  have hx : 1 ≤ x := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hu u.property.2 (neg_nonpos.mpr hθ.le)
  have hy : 1 ≤ y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hv v.property.2 (neg_nonpos.mpr hθ.le)
  have hxy : x + y - 1 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hb : 0 < x + y - 1 := by linarith
  have hpow (w : I) (hw : 0 < (w : ℝ)) :
      ((w : ℝ) ^ (-θ)) ^ (-1 / θ) = (w : ℝ) := by
    rw [← Real.rpow_mul hw.le]
    have he : (-θ) * (-1 / θ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hmult : (x * y) ^ (-1 / θ) = (u : ℝ) * (v : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _),
      hpow u hu, hpow v hv]
  have hr : -1 / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hθ.le
  have hle := Real.rpow_le_rpow_of_nonpos hb hxy hr
  rw [hmult] at hle
  rw [cdf_clayton_two_pos θ hθ u v hu hv]
  exact hle

/-- Every admissible negative bivariate Clayton copula is negatively quadrant dependent. -/
theorem isNQD_clayton_negative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).IsNQD := by
  intro u v
  by_cases hu0 : u = 0
  · simp [hu0]
  by_cases hv0 : v = 0
  · subst v
    simp only [Set.Icc.coe_zero, mul_zero]
    rw [(claytonNegative θ hθ hn).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl]
  have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv0 (Subtype.ext h)))
  let x := (u : ℝ) ^ (-θ)
  let y := (v : ℝ) ^ (-θ)
  have hp : 0 < -θ := by linarith
  have hx0 : 0 ≤ x := Real.rpow_nonneg hu.le _
  have hy0 : 0 ≤ y := Real.rpow_nonneg hv.le _
  have hx1 : x ≤ 1 := Real.rpow_le_one hu.le u.property.2 (by linarith)
  have hy1 : y ≤ 1 := Real.rpow_le_one hv.le v.property.2 (by linarith)
  have hxy : x + y - 1 ≤ x * y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
  have hbase : max 0 (x + y - 1) ≤ x * y := max_le (mul_nonneg hx0 hy0) hxy
  have hpow (w : I) (hw : 0 < (w : ℝ)) :
      ((w : ℝ) ^ (-θ)) ^ (-θ)⁻¹ = (w : ℝ) := by
    rw [← Real.rpow_mul hw.le]
    rw [mul_inv_cancel₀ (ne_of_gt hp), Real.rpow_one]
  have hmult : (x * y) ^ (-θ)⁻¹ = (u : ℝ) * (v : ℝ) := by
    rw [Real.mul_rpow hx0 hy0, hpow u hu, hpow v hv]
  have hr : 0 ≤ (-θ)⁻¹ := inv_nonneg.mpr hp.le
  have hle := Real.rpow_le_rpow (by positivity : 0 ≤ max 0 (x + y - 1)) hbase hr
  rw [hmult] at hle
  rw [cdf_claytonNegative θ hθ hn ![u, v] (by
    intro i
    fin_cases i
    · simpa using hu0
    · simpa using hv0)]
  exact hle

end ProbabilityTheory.Copula
