/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Basic
import Copula.Dependence.Clayton
import Mathlib.Analysis.Convex.Deriv

/-! # Ali–Mikhail–Haq copulas on the full bivariate parameter interval -/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem amh_den_pos (θ t : ℝ) (hθ : θ < 1) (ht : 0 ≤ t) :
    0 < Real.exp t - θ := by
  have he := Real.add_one_le_exp t
  linarith

private theorem amh_exp_plus_nonneg (θ t : ℝ) (hθ : -1 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ Real.exp t + θ := by
  have he := Real.add_one_le_exp t
  linarith

private theorem amh_hasDerivAt (θ t : ℝ) (hθ : θ < 1) (ht : 0 ≤ t) :
    HasDerivAt (fun x => (1 - θ) / (Real.exp x - θ))
      (-(1 - θ) * Real.exp t / (Real.exp t - θ) ^ 2) t := by
  have hd := amh_den_pos θ t hθ ht
  have h := (hasDerivAt_const t (1 - θ)).div
    ((Real.hasDerivAt_exp t).sub_const θ) hd.ne'
  convert h using 1
  · ring

private theorem amh_deriv_hasDerivAt (θ t : ℝ) (hθ : θ < 1) (ht : 0 ≤ t) :
    HasDerivAt (fun x => -(1 - θ) * Real.exp x / (Real.exp x - θ) ^ 2)
      ((1 - θ) * Real.exp t * (Real.exp t + θ) / (Real.exp t - θ) ^ 3) t := by
  have hd := amh_den_pos θ t hθ ht
  have hn := (hasDerivAt_const t (-(1 - θ))).mul (Real.hasDerivAt_exp t)
  have hd' := ((Real.hasDerivAt_exp t).sub_const θ).pow 2
  have h := hn.div hd' (pow_ne_zero 2 hd.ne')
  convert h using 1
  dsimp
  field_simp [hd.ne']
  ring

private theorem amh_convex (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ < 1) :
    ConvexOn ℝ (Ici 0) (fun t => (1 - θ) / (Real.exp t - θ)) := by
  let f : ℝ → ℝ := fun t => (1 - θ) / (Real.exp t - θ)
  let f' : ℝ → ℝ := fun t => -(1 - θ) * Real.exp t / (Real.exp t - θ) ^ 2
  let f'' : ℝ → ℝ := fun t =>
    (1 - θ) * Real.exp t * (Real.exp t + θ) / (Real.exp t - θ) ^ 3
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht
    exact (amh_hasDerivAt θ t hmax ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      exact (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    exact (amh_hasDerivAt θ t hmax ht0).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      exact (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    exact (amh_deriv_hasDerivAt θ t hmax ht0).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      exact (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    have hn : 0 ≤ (1 - θ) * Real.exp t * (Real.exp t + θ) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos t).le)
        (amh_exp_plus_nonneg θ t hmin ht0)
    exact div_nonneg hn (pow_nonneg (amh_den_pos θ t hmax ht0).le _)


private theorem amh_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (by
    intro h
    exact hu (Subtype.ext h)))

private theorem amh_base_ge_one (θ : ℝ) (hθ : θ < 1) (u : I) (hu : u ≠ 0) :
    1 ≤ θ + (1 - θ) / (u : ℝ) := by
  have hp := amh_u_pos u hu
  have h : 1 - θ ≤ (1 - θ) / (u : ℝ) :=
    (le_div_iff₀ hp).mpr (by nlinarith [u.property.2])
  linarith

/-- The Ali–Mikhail–Haq inverse generator for parameters below one. -/
noncomputable def amhGenerator (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ < 1) :
    BivariateGenerator where
  toFun t := (1 - θ) / (Real.exp t - θ)
  invFun u := Real.log (θ + (1 - θ) / (u : ℝ))
  nonneg t ht := div_nonneg (by linarith) (amh_den_pos θ t hmax ht).le
  antitone x hx y hy hxy := by
    apply div_le_div_of_nonneg_left (by linarith) (amh_den_pos θ x hmax hx)
    exact sub_le_sub_right (Real.exp_le_exp.mpr hxy) θ
  convex := amh_convex θ hmin hmax
  inv_nonneg u hu := Real.log_nonneg (amh_base_ge_one θ hmax u hu)
  inv_antitone u v hu huv := by
    have hv : v ≠ 0 := by
      intro hv
      exact hu (le_antisymm (hv ▸ huv) unitInterval.nonneg')
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (amh_base_ge_one θ hmax v hv))
    have hd : (1 - θ) / (v : ℝ) ≤ (1 - θ) / (u : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) (amh_u_pos u hu) (by exact_mod_cast huv)
    linarith
  inv_one := by simp
  right_inv u hu := by
    have hb := amh_base_ge_one θ hmax u hu
    have hp := amh_u_pos u hu
    simp only [Real.exp_log (lt_of_lt_of_le zero_lt_one hb)]
    field_simp [show 1 - θ ≠ 0 by linarith, hp.ne']
    ring


/-- The Ali–Mikhail–Haq family on its complete bivariate parameter interval. -/
noncomputable def amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) : Copula 2 :=
  if h : θ = 1 then clayton 2 1 zero_lt_one
  else (amhGenerator θ hmin (lt_of_le_of_ne hmax h)).copula

@[simp] theorem amh_one (hmin : (-1 : ℝ) ≤ 1) :
    amh 1 hmin le_rfl = clayton 2 1 zero_lt_one := by
  simp [amh]

theorem amh_isArchimedean_of_lt_one (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1)
    (hθ : θ < 1) : IsArchimedean (amh θ hmin hmax) := by
  simp only [amh, ne_of_lt hθ, dite_false]
  exact (amhGenerator θ hmin hθ).isArchimedean


/-- The standard rational AMH CDF on positive coordinates. -/
theorem amhGenerator_cdf (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ < 1)
    (a b : I) (ha : a ≠ 0) (hb : b ≠ 0) :
    (amhGenerator θ hmin hmax).cdf a b =
      (a : ℝ) * (b : ℝ) /
        (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
  have hap := amh_u_pos a ha
  have hbp := amh_u_pos b hb
  let A : ℝ := θ + (1 - θ) / (a : ℝ)
  let B : ℝ := θ + (1 - θ) / (b : ℝ)
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (amh_base_ge_one θ hmax a ha)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (amh_base_ge_one θ hmax b hb)
  have ht : 0 ≤ Real.log A + Real.log B :=
    add_nonneg (Real.log_nonneg (amh_base_ge_one θ hmax a ha))
      (Real.log_nonneg (amh_base_ge_one θ hmax b hb))
  have hd : 0 < A * B - θ := by
    convert amh_den_pos θ (Real.log A + Real.log B) hmax ht using 1
    rw [Real.exp_add, Real.exp_log hA, Real.exp_log hB]
  have hid : (A * B - θ) * (a : ℝ) * (b : ℝ) =
      (1 - θ) * (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
    dsimp [A, B]
    field_simp [hap.ne', hbp.ne']
    ring
  have he : 0 < 1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ)) := by
    have hprod : 0 < (A * B - θ) * (a : ℝ) * (b : ℝ) := by positivity
    rw [hid] at hprod
    nlinarith
  simp only [BivariateGenerator.cdf, ha, hb, or_false, ite_false]
  change (1 - θ) / (Real.exp (Real.log A + Real.log B) - θ) = _
  rw [Real.exp_add, Real.exp_log hA, Real.exp_log hB]
  field_simp [hd.ne', he.ne', hap.ne', hbp.ne']
  nlinarith [hid]


/-- The rational AMH formula for every parameter strictly below one. -/
theorem cdf_amh_of_lt_one (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1)
    (hθ : θ < 1) (a b : I) (ha : a ≠ 0) (hb : b ≠ 0) :
    (amh θ hmin hmax).cdf ![a, b] =
      (a : ℝ) * (b : ℝ) /
        (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
  rw [amh, dite_eq_right (ne_of_lt hθ), BivariateGenerator.cdf_copula]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
    amhGenerator_cdf θ hmin hθ a b ha hb


/-- The rational AMH CDF on the entire closed square below the endpoint. -/
theorem cdf_amh_lt_one (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1)
    (hθ : θ < 1) (a b : I) :
    (amh θ hmin hmax).cdf ![a, b] =
      (a : ℝ) * (b : ℝ) /
        (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
  by_cases ha : a = 0
  · rw [ha]
    simp [amh, ne_of_lt hθ]
  by_cases hb : b = 0
  · rw [hb]
    simp [amh, ne_of_lt hθ]
  exact cdf_amh_of_lt_one θ hmin hmax hθ a b ha hb


/-- The AMH endpoint θ=1 has the Clayton(1) rational CDF on positive coordinates. -/
theorem cdf_amh_one_of_pos (a b : I) (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) :
    (amh 1 (by norm_num) le_rfl).cdf ![a, b] =
      (a : ℝ) * (b : ℝ) /
        (1 - (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
  have heq : 1 - (1 - (a : ℝ)) * (1 - (b : ℝ)) =
      (a : ℝ) + (b : ℝ) - (a : ℝ) * (b : ℝ) := by ring
  rw [heq, amh_one, cdf_clayton_two_pos 1 zero_lt_one a b ha hb]
  norm_num
  rw [Real.rpow_neg_one, Real.rpow_neg_one, Real.rpow_neg_one]
  have hden : 0 < (a : ℝ) + (b : ℝ) - (a : ℝ) * (b : ℝ) := by
    have h := mul_nonneg ha.le (sub_nonneg.mpr b.property.2)
    nlinarith
  field_simp [ha.ne', hb.ne', hden.ne']
  have hq : ((a : ℝ) + (b : ℝ) - (a : ℝ) * (b : ℝ)) *
      ((a : ℝ) + (b : ℝ) - (a : ℝ) * (b : ℝ))⁻¹ = 1 := by
    exact mul_inv_cancel₀ hden.ne'
  convert hq using 1; ring


/-- The rational AMH endpoint formula on the closed square. -/
theorem cdf_amh_one (a b : I) :
    (amh 1 (by norm_num) le_rfl).cdf ![a, b] =
      (a : ℝ) * (b : ℝ) /
        (1 - (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
  by_cases ha : a = 0
  · rw [ha]
    simp [amh]
  by_cases hb : b = 0
  · rw [hb]
    have hc := (amh 1 (by norm_num) le_rfl).cdf_eq_zero_of_coord_eq_zero ![a, 0] 1 rfl
    simpa [amh] using hc
  exact cdf_amh_one_of_pos a b (amh_u_pos a ha) (amh_u_pos b hb)

/-- The exact AMH CDF for the full bivariate parameter interval and closed square. -/
theorem cdf_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (a b : I) :
    (amh θ hmin hmax).cdf ![a, b] =
      (a : ℝ) * (b : ℝ) /
        (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) := by
  rcases lt_or_eq_of_le hmax with hθ | hθ
  · exact cdf_amh_lt_one θ hmin hmax hθ a b
  · subst θ
    simpa using cdf_amh_one a b


/-- Every bivariate AMH member is Archimedean, including the Clayton endpoint. -/
theorem isArchimedean_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    IsArchimedean (amh θ hmin hmax) := by
  rcases lt_or_eq_of_le hmax with hθ | hθ
  · exact amh_isArchimedean_of_lt_one θ hmin hmax hθ
  · subst θ
    simpa [amh] using isArchimedean_clayton 2 1 zero_lt_one

end ProbabilityTheory.Copula
