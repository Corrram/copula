/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.Transport

/-! # Feasibility of the glued magnitude potential

The proof separates the lower square, the upper square, and the mixed
rectangles. This is the global inequality in Lemma 4.1 of
Ansari–Rockel–Steinmassl, including points outside the attaining support.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

noncomputable def gluedPotential (a t : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ a then x * (t - x) / 2 else F x

theorem gluedPotential_of_le {a t x : ℝ} (F : ℝ → ℝ) (hx : x ≤ a) :
    gluedPotential a t F x = x * (t - x) / 2 := by simp only [gluedPotential, hx, ite_true]

theorem gluedPotential_of_ge {a t x : ℝ} (F : ℝ → ℝ)
    (hjoin : F a = a * (t - a) / 2) (hx : a ≤ x) :
    gluedPotential a t F x = F x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp only [gluedPotential, le_refl, ite_true, hjoin]
  · simp only [gluedPotential, not_le.mpr hx, ite_false]

theorem upper_square_feasible {a t : ℝ} {F : ℝ → ℝ}
    (ha0 : 0 ≤ a) (hat : a ≤ t) (hta : t ≤ 2 * a)
    (hjoin : F a = a * (t - a) / 2)
    (hmono : MonotoneOn F (Set.Icc a 1))
    (hpositive : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ 1 → x * (y - t) ≤ F x + F y)
    {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    x * |y - t| ≤ F x + F y := by
  by_cases hyt : t ≤ y
  · rw [abs_of_nonneg (sub_nonneg.mpr hyt)]
    exact hpositive x y hax hxy hy1
  · rw [abs_of_nonpos (by linarith)]
    have hFa : 0 ≤ F a := by rw [hjoin]; positivity
    have hFx := hmono ⟨le_rfl, hax.trans (hxy.trans hy1)⟩ ⟨hax, hxy.trans hy1⟩ hax
    have hFy := hmono ⟨le_rfl, hax.trans (hxy.trans hy1)⟩ ⟨hax.trans hxy, hy1⟩ (hax.trans hxy)
    have hprod := mul_nonneg (sub_nonneg.mpr hax) (show 0 ≤ x + a - t by linarith)
    have hdist := mul_nonneg (show 0 ≤ x by linarith) (sub_nonneg.mpr hxy)
    nlinarith only [hFx, hFy, hjoin, hprod, hdist]

theorem gluedPotential_feasible {a t : ℝ} {F : ℝ → ℝ}
    (ha0 : 0 ≤ a) (hat : a ≤ t) (hta : t ≤ 2 * a)
    (hjoin : F a = a * (t - a) / 2)
    (hmono : MonotoneOn F (Set.Icc a 1))
    (hpositive : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ 1 → x * (y - t) ≤ F x + F y)
    (x y : I) :
    min (x : ℝ) y * |max (x : ℝ) y - t| ≤
      gluedPotential a t F x + gluedPotential a t F y := by
  wlog hxy : (x : ℝ) ≤ y generalizing x y
  · simpa only [min_comm, max_comm, add_comm] using this y x (le_of_not_ge hxy)
  rw [min_eq_left hxy, max_eq_right hxy]
  by_cases hya : (y : ℝ) ≤ a
  · rw [gluedPotential_of_le F (hxy.trans hya), gluedPotential_of_le F hya,
      abs_of_nonpos (by linarith)]
    have hp := mul_nonneg (sub_nonneg.mpr hxy)
      (show 0 ≤ t - ((y : ℝ) - x) by linarith [x.property.1])
    nlinarith only [hp]
  · have hay : a ≤ (y : ℝ) := le_of_not_ge hya
    rw [gluedPotential_of_ge F hjoin hay]
    by_cases hax : a ≤ (x : ℝ)
    · rw [gluedPotential_of_ge F hjoin hax]
      exact upper_square_feasible ha0 hat hta hjoin hmono hpositive hax hxy y.property.2
    · have hxa : (x : ℝ) ≤ a := le_of_not_ge hax
      rw [gluedPotential_of_le F hxa]
      have hFa : 0 ≤ F a := by rw [hjoin]; positivity
      have hFy : 0 ≤ F (y : ℝ) := hFa.trans (hmono ⟨le_rfl, hay.trans y.property.2⟩
        ⟨hay, y.property.2⟩ hay)
      have hedge := upper_square_feasible ha0 hat hta hjoin hmono hpositive le_rfl hay y.property.2
      have ha : 0 < a := lt_of_le_of_lt x.property.1 (lt_of_not_ge hax)
      have h0 := mul_nonneg (sub_nonneg.mpr hxa) hFy
      have h1 := mul_nonneg x.property.1 (sub_nonneg.mpr hedge)
      have h2 := mul_nonneg (mul_nonneg ha.le x.property.1) (sub_nonneg.mpr hxa)
      have hh : 0 ≤ a * ((x : ℝ) * (t - x) / 2 + F (y : ℝ) - (x : ℝ) * |(y : ℝ) - t|) := by
        nlinarith only [h0, h1, h2, congrArg (fun r : ℝ => r * (x : ℝ)) hjoin]
      have := nonneg_of_mul_nonneg_right hh ha
      linarith


@[fun_prop] theorem continuous_gluedPotential {a t : ℝ} {F : ℝ → ℝ}
    (hF : Continuous F) (hjoin : F a = a * (t - a) / 2) :
    Continuous (gluedPotential a t F) := by
  apply Continuous.if_le (by fun_prop) hF continuous_id continuous_const
  intro x hx
  change x = a at hx
  subst x
  exact hjoin.symm

noncomputable def upperPotential (a t z : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (x ^ 2 - t * x) / 2 - z ^ 2 / 2 * h ((x - a) / z)

@[fun_prop] theorem continuous_upperPotential (a t z : ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    Continuous (upperPotential a t z h) := by
  unfold upperPotential
  fun_prop

theorem upperPotential_join {a t z : ℝ} {h : ℝ → ℝ}
    (hmatch : z ^ 2 * h 0 = 2 * a * (a - t)) :
    upperPotential a t z h a = a * (t - a) / 2 := by
  simp only [upperPotential, sub_self, zero_div]
  nlinarith only [hmatch]

theorem upperPotential_monotone {a t z w : ℝ} {h : ℝ → ℝ}
    (hz : 0 < z) (hw : 0 ≤ w) (hL : LipschitzWith ⟨w, hw⟩ h)
    (ha : t + z * w ≤ 2 * a) :
    MonotoneOn (upperPotential a t z h) (Set.Ici a) := by
  intro x hx y hy hxy
  have huv : 0 ≤ (y - a) / z - (x - a) / z :=
    sub_nonneg.mpr (div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hz.le)
  have hh := hL.dist_le_mul ((y - a) / z) ((x - a) / z)
  simp only [Real.dist_eq, abs_of_nonneg huv] at hh
  change |h ((y - a) / z) - h ((x - a) / z)| ≤ w * ((y - a) / z - (x - a) / z) at hh
  have hdiff := (le_abs_self (h ((y - a) / z) - h ((x - a) / z))).trans hh
  have hscaled := mul_le_mul_of_nonneg_left hdiff (sq_nonneg z)
  have he : z ^ 2 * (w * ((y - a) / z - (x - a) / z)) = z * w * (y - x) := by
    field_simp
    ring
  rw [he] at hscaled
  have hp := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x + y - t - z * w by
    have hax : a ≤ x := hx
    have hay : a ≤ y := hy
    linarith)
  dsimp [upperPotential]
  nlinarith only [hscaled, hp]

theorem upperPotential_positive_cost {a t z s : ℝ} {h : ℝ → ℝ}
    (hz : 0 < z) (haz : a + z = 1) (ht : t = z * s)
    (hdual : ∀ u v : I, h u + h v ≤ ((u : ℝ) - v) ^ 2 - s * |(u : ℝ) - v|)
    (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    x * (y - t) ≤ upperPotential a t z h x + upperPotential a t z h y := by
  let u : I := ⟨(x - a) / z, div_nonneg (sub_nonneg.mpr hax) hz.le,
    (div_le_one hz).mpr (by linarith)⟩
  let v : I := ⟨(y - a) / z, div_nonneg (sub_nonneg.mpr (hax.trans hxy)) hz.le,
    (div_le_one hz).mpr (by linarith)⟩
  have hu : x = a + z * (u : ℝ) := by dsimp [u]; field_simp; ring
  have hv : y = a + z * (v : ℝ) := by dsimp [v]; field_simp; ring
  have huv : (u : ℝ) ≤ v := div_le_div_of_nonneg_right (sub_le_sub_right hxy a) hz.le
  have hh := hdual u v
  rw [abs_of_nonpos (sub_nonpos.mpr huv)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg z)
  change x * (y - t) ≤ (x ^ 2 - t * x) / 2 - z ^ 2 / 2 * h u +
    ((y ^ 2 - t * y) / 2 - z ^ 2 / 2 * h v)
  rw [hu, hv, ht]
  nlinarith only [hm]

end ProbabilityTheory.Copula.RankRegion.RhoGamma
