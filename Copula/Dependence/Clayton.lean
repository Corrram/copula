/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Clayton.CDF
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

end ProbabilityTheory.Copula
