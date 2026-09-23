/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.AMH
import Copula.Dependence.Basic

/-! # Quadrant dependence of Ali–Mikhail–Haq copulas -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem amh_complement_nonneg (u : I) : 0 ≤ 1 - (u : ℝ) :=
  sub_nonneg.mpr u.property.2

private theorem amh_complement_product_le_one (u v : I) :
    (1 - (u : ℝ)) * (1 - (v : ℝ)) ≤ 1 := by
  have hu := amh_complement_nonneg u
  have hv := amh_complement_nonneg v
  have h := mul_le_mul_of_nonneg_left (show 1 - (v : ℝ) ≤ 1 by
    linarith [v.property.1]) hu
  nlinarith [u.property.1]

/-- Nonnegative AMH parameters are positively quadrant dependent. -/
theorem isPQD_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (hθ : 0 ≤ θ) :
    (amh θ hmin hmax).IsPQD := by
  rcases lt_or_eq_of_le hmax with hlt | heq
  · intro u v
    rw [cdf_amh]
    have hp := amh_complement_product_le_one u v
    have hD : 0 < 1 - θ * (1 - (u : ℝ)) * (1 - (v : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hp hθ]
    apply (le_div_iff₀ hD).mpr
    have hn : 0 ≤ (u : ℝ) * (v : ℝ) * θ *
        ((1 - (u : ℝ)) * (1 - (v : ℝ))) := by
      exact mul_nonneg (mul_nonneg (mul_nonneg u.property.1 v.property.1) hθ)
        (mul_nonneg (amh_complement_nonneg u) (amh_complement_nonneg v))
    nlinarith
  · subst θ
    simpa [amh] using isPQD_clayton_positive 1 zero_lt_one

/-- Nonpositive AMH parameters are negatively quadrant dependent. -/
theorem isNQD_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (hθ : θ ≤ 0) :
    (amh θ hmin hmax).IsNQD := by
  intro u v
  rw [cdf_amh]
  have hp : 0 ≤ (1 - (u : ℝ)) * (1 - (v : ℝ)) :=
    mul_nonneg (amh_complement_nonneg u) (amh_complement_nonneg v)
  have hD : 0 < 1 - θ * (1 - (u : ℝ)) * (1 - (v : ℝ)) := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hθ hp]
  apply (div_le_iff₀ hD).mpr
  have hn : θ * ((1 - (u : ℝ)) * (1 - (v : ℝ))) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hθ hp
  have huv : 0 ≤ (u : ℝ) * (v : ℝ) :=
    mul_nonneg u.property.1 v.property.1
  nlinarith [mul_nonpos_of_nonneg_of_nonpos huv hn]


private noncomputable def amhMid : I := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem amh_mid_cdf (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).cdf ![amhMid, amhMid] = 1 / (4 - θ) := by
  rw [cdf_amh]
  norm_num [amhMid]
  have hd : 4 - θ ≠ 0 := by linarith
  field_simp [hd]
  calc
    _ = 4 * ((4 - θ) * (4 - θ)⁻¹) := by ring
    _ = 4 := by rw [mul_inv_cancel₀ hd]; ring

/-- AMH is PQD exactly for nonnegative parameters. -/
theorem isPQD_amh_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).IsPQD ↔ 0 ≤ θ := by
  constructor
  · intro h
    have hm := h amhMid amhMid
    rw [amh_mid_cdf θ hmin hmax] at hm
    have hd : 0 < 4 - θ := by linarith
    norm_num [amhMid] at hm
    have hm' : (1 / 4 : ℝ) ≤ 1 / (4 - θ) := by simpa only [one_div] using hm
    have hq := (le_div_iff₀ hd).mp hm'
    nlinarith
  · exact isPQD_amh θ hmin hmax

/-- AMH is NQD exactly for nonpositive parameters. -/
theorem isNQD_amh_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).IsNQD ↔ θ ≤ 0 := by
  constructor
  · intro h
    have hm := h amhMid amhMid
    rw [amh_mid_cdf θ hmin hmax] at hm
    have hd : 0 < 4 - θ := by linarith
    norm_num [amhMid] at hm
    have hm' : 1 / (4 - θ) ≤ (1 / 4 : ℝ) := by simpa only [one_div] using hm
    have hq := (div_le_iff₀ hd).mp hm'
    nlinarith
  · exact isNQD_amh θ hmin hmax

end ProbabilityTheory.Copula
