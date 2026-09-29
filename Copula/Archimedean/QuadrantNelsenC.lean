/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantTails
import Copula.Families.Nelsen8
import Copula.Families.NelsenTable.N18
import Copula.Families.NelsenTable.N21
import Copula.Families.NelsenTable.N22

/-! # Quadrant dependence of Nelsen's families 8, 18, 21, 22

* #8: NQD iff `θ ≤ 2` (for `θ > 2` the copula is neither PQD nor NQD: the printed CDF exceeds
  `u v` at `u = v = θ / (2 (θ - 1))`);
* #18, #21: never PQD (non-strict generators); #18 never NQD (`λ_U = 1`), #21 NQD iff `θ = 1`;
* #22: NQD for all `θ ∈ (0, 1]` (inner power of the `θ = 1` member) and never PQD.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ### Family 8 -/

/-- Nelsen's family 8 is NQD for `1 ≤ θ ≤ 2`. -/
theorem isNQD_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) (h2 : θ ≤ 2) : (nelsen8 θ hθ).IsNQD := by
  intro u v
  rw [nelsen8_cdf_full]
  have hu := u.property
  have hv := v.property
  have hD := n8_source_den_pos θ u v hθ hu.1 hu.2 hv.1 hv.2
  apply max_le (mul_nonneg hu.1 hv.1)
  rw [div_le_iff₀ hD]
  have h1 : (θ - 1) ^ 2 ≤ 1 := by nlinarith
  have h3 : (u : ℝ) * v ≤ 1 := by nlinarith [hu.1, hv.1, hu.2, hv.2, mul_nonneg hu.1 (sub_nonneg.mpr hv.2)]
  have h4 : (θ - 1) ^ 2 * ((u : ℝ) * v) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul h1 h3 (mul_nonneg hu.1 hv.1) zero_le_one
      _ = 1 := one_mul 1
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2))
    (sub_nonneg.mpr h4)]

/-- Nelsen's family 8 is not NQD for `θ > 2`. -/
theorem not_isNQD_nelsen8 (θ : ℝ) (hθ : 2 < θ) : ¬ (nelsen8 θ (by linarith)).IsNQD := by
  intro h
  set d := θ - 1 with hd
  have hd1 : 1 < d := by rw [hd]; linarith
  set w : ℝ := (d + 1) / (2 * d) with hw
  have hd0 : 0 < d := by linarith
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw, div_le_one (by positivity)]; linarith
  let p : I := ⟨w, hw0, hw1⟩
  have hcd := h p p
  rw [nelsen8_cdf_full] at hcd
  have hθ' : θ = d + 1 := by rw [hd]; ring
  have hD := n8_source_den_pos θ w w (by linarith) hw0 hw1 hw0 hw1
  have hle := le_max_right 0 ((θ ^ 2 * w * w - (1 - w) * (1 - w)) /
    (θ ^ 2 - (θ - 1) ^ 2 * (1 - w) * (1 - w)))
  have hkey : w * w < (θ ^ 2 * w * w - (1 - w) * (1 - w)) /
      (θ ^ 2 - (θ - 1) ^ 2 * (1 - w) * (1 - w)) := by
    rw [lt_div_iff₀ hD]
    have hdw : d * w = (d + 1) / 2 := by rw [hw]; field_simp
    have hpos : 0 < (1 - w) * (1 - w) * ((d * w) ^ 2 - 1) := by
      apply mul_pos (mul_pos (by
        rw [sub_pos, hw, div_lt_one (by positivity)]; linarith) (by
        rw [sub_pos, hw, div_lt_one (by positivity)]; linarith))
      rw [hdw]; nlinarith
    have : θ ^ 2 * w * w - (1 - w) * (1 - w) - w * w * (θ ^ 2 - (θ - 1) ^ 2 * (1 - w) * (1 - w))
        = (1 - w) * (1 - w) * ((d * w) ^ 2 - 1) := by
      rw [hθ']; simp only [hd]; ring
    linarith
  simp only [p] at hcd
  linarith

/-- Nelsen's family 8 is NQD iff `θ ≤ 2`. -/
theorem isNQD_nelsen8_iff (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen8 θ hθ).IsNQD ↔ θ ≤ 2 := by
  constructor
  · intro h
    by_contra hc
    exact not_isNQD_nelsen8 θ (not_le.mp hc) h
  · exact fun h => isNQD_nelsen8 θ hθ h

/-! ### Families 18 and 21 (non-strict generators) -/

/-- Nelsen's family 18 is never PQD. -/
theorem not_isPQD_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).IsPQD := by
  refine BivariateGenerator.not_isPQD_of_not_isStrict _ fun h => ?_
  have := h (Real.exp (-θ)) (Real.exp_pos _).le
  rw [nelsen18Generator_toFun_of_le θ hθ le_rfl] at this
  exact lt_irrefl _ this

/-- Nelsen's family 21 is never PQD. -/
theorem not_isPQD_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) : ¬ (nelsen21 θ hθ).IsPQD := by
  refine BivariateGenerator.not_isPQD_of_not_isStrict _ fun h => ?_
  have := h 1 zero_le_one
  rw [show (nelsen21Generator θ hθ).toFun 1 = 0 from
    BivariateGenerator.ofClamp_toFun_of_le le_rfl] at this
  exact lt_irrefl _ this

/-! ### Family 22 -/

private theorem psi_base_nqd (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    nelsen22BaseGenerator.toFun (x + y) ≤
      nelsen22BaseGenerator.toFun x * nelsen22BaseGenerator.toFun y := by
  show 1 - Real.sin (min (x + y) (Real.pi / 2)) ≤
    (1 - Real.sin (min x (Real.pi / 2))) * (1 - Real.sin (min y (Real.pi / 2)))
  have hpi := Real.pi_pos
  have hs1 : ∀ z, Real.sin z ≤ 1 := Real.sin_le_one
  rcases le_or_gt (Real.pi / 2) (x + y) with hxy | hxy
  · rw [min_eq_right hxy, Real.sin_pi_div_two, sub_self]
    exact mul_nonneg (by linarith [hs1 (min x (Real.pi / 2))]) (by linarith [hs1 (min y (Real.pi / 2))])
  · rw [min_eq_left hxy.le, min_eq_left (by linarith : x ≤ Real.pi / 2),
      min_eq_left (by linarith : y ≤ Real.pi / 2), Real.sin_add]
    set a := Real.sin x with ha
    set b := Real.sin y with hb
    set cx := Real.cos x with hcx
    set cy := Real.cos y with hcy
    have ha0 : 0 ≤ a := Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith)
    have hb0 : 0 ≤ b := Real.sin_nonneg_of_nonneg_of_le_pi hy (by linarith)
    have hcx1 : cx ≤ 1 := Real.cos_le_one x
    have hcy1 : cy ≤ 1 := Real.cos_le_one y
    have hcxb : b ≤ cx := by
      have := Real.cos_le_cos_of_nonneg_of_le_pi hx (by linarith : Real.pi / 2 - y ≤ Real.pi)
        (by linarith : x ≤ Real.pi / 2 - y)
      rw [Real.cos_pi_div_two_sub] at this
      exact this
    have hcya : a ≤ cy := by
      have := Real.cos_le_cos_of_nonneg_of_le_pi hy (by linarith : Real.pi / 2 - x ≤ Real.pi)
        (by linarith : y ≤ Real.pi / 2 - x)
      rw [Real.cos_pi_div_two_sub] at this
      exact this
    have hx2 : cx ^ 2 = 1 - a ^ 2 := by rw [hcx, ha]; linarith [Real.sin_sq_add_cos_sq x]
    have hy2 : cy ^ 2 = 1 - b ^ 2 := by rw [hcy, hb]; linarith [Real.sin_sq_add_cos_sq y]
    have hab : a ^ 2 + b ^ 2 ≤ 1 := by nlinarith
    have h1 : (1 - cy) * (1 + a) ≤ b ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 + a ≤ 1 + cy) (by linarith : 0 ≤ 1 - cy)]
    have h2 : (1 - cx) * (1 + b) ≤ a ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 + b ≤ 1 + cx) (by linarith : 0 ≤ 1 - cx)]
    have hP : 0 < (1 + a) * (1 + b) := by positivity
    have key : a * (1 - cy) + b * (1 - cx) ≤ a * b := by
      refine le_of_mul_le_mul_right ?_ hP
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ a * (1 + b)),
        mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ b * (1 + a)),
        mul_nonneg ha0 hb0]
    nlinarith

/-- Nelsen's family 22 is NQD for every `θ ∈ (0, 1]`. -/
theorem isNQD_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : (nelsen22 θ hθ h1).IsNQD := by
  refine BivariateGenerator.isNQD_innerPower _ _ _ ?_
  exact BivariateGenerator.isNQD_of_psi _ psi_base_nqd

/-- Nelsen's family 22 is never PQD. -/
theorem not_isPQD_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : ¬ (nelsen22 θ hθ h1).IsPQD := by
  refine BivariateGenerator.not_isPQD_of_not_isStrict _ fun h => ?_
  have := h (Real.pi / 2) (by linarith [Real.pi_pos])
  rw [nelsen22Generator_toFun, min_self, Real.sin_pi_div_two, sub_self,
    Real.zero_rpow (inv_ne_zero hθ.ne')] at this
  exact lt_irrefl _ this

end ProbabilityTheory.Copula
