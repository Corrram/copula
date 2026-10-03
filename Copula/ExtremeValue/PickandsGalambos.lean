/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.PickandsCoefficients
import Copula.ExtremeValue.PickandsKendall

/-! # The Galambos (negative logistic) extreme-value copula

For `θ > 0` the Galambos Pickands function is

`A(t) = 1 - (t^{-θ} + (1-t)^{-θ})^{-1/θ} = 1 - t (1 - t) / (t^θ + (1-t)^θ)^{1/θ}`

(the second form is used as the definition, `galambosPickands`, since it is also correct at the
endpoints). It is a Pickands function (`isPickandsFunction_galambosPickands`): the bounds follow
from `(t^θ + (1-t)^θ)^{1/θ} ≥ max(t, 1-t)`, and convexity of `A` from the superadditivity of the
negative-order power mean `(x^{-θ} + y^{-θ})^{-1/θ}` (reverse Minkowski inequality, proved from
the convexity of `s ↦ s^{-θ}`). The resulting copula `galambos θ hθ` has the classical CDF

`C(u,v) = u v exp(((-log u)^{-θ} + (-log v)^{-θ})^{-1/θ})`   (`cdf_galambos`),

and upper tail dependence coefficient `λ_U = 2^{-1/θ}` (`hasUpperTailDependence_galambos`).

References: J. Galambos, *Order statistics of samples from multivariate distributions* (1975);
H. Joe, *Dependence Modeling with Copulas* (2014); G. Gudendorf and J. Segers,
*Extreme-value copulas* (2010).
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- A continuous function on `[a,b]` that is convex on `(a,b)` is convex on `[a,b]`. -/
theorem convexOn_Icc_of_convexOn_Ioo {f : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn f (Icc a b))
    (h : ConvexOn ℝ (Ioo a b) f) : ConvexOn ℝ (Icc a b) f := by
  refine convexOn_Icc_of_local hc fun c hc' ε hε => ?_
  obtain ⟨hac, hcb⟩ := hc'
  set δ := min (ε / 2) (min (c - a) (b - c) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by
    have := lt_min (sub_pos.2 hac) (sub_pos.2 hcb)
    linarith)
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ min (c - a) (b - c) / 2 := min_le_right _ _
  have hδ3 : min (c - a) (b - c) ≤ c - a := min_le_left _ _
  have hδ4 : min (c - a) (b - c) ≤ b - c := min_le_right _ _
  refine ⟨c - δ, c + δ, by linarith, by linarith, by linarith, by linarith, ?_⟩
  have hs := h.slope_mono_adjacent (x := c - δ) (y := c) (z := c + δ)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith) (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hs
  nlinarith

private theorem convexOn_rpow_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ p) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hm : 0 < min x y := lt_min hx' hy'
  have hxy : 0 < a * x + b * y := by
    nlinarith [mul_le_mul_of_nonneg_left (min_le_left x y) ha,
      mul_le_mul_of_nonneg_left (min_le_right x y) hb]
  rw [Real.rpow_def_of_pos hxy, Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hy']
  have hlog := (strictConcaveOn_log_Ioi.concaveOn).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hlog
  have h1 : Real.exp (Real.log (a * x + b * y) * p) ≤
      Real.exp (a * (Real.log x * p) + b * (Real.log y * p)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonpos_right hlog hp
    linarith
  have h2 := convexOn_exp.2 (mem_univ (Real.log x * p)) (mem_univ (Real.log y * p)) ha hb hab
  simp only [smul_eq_mul] at h2
  exact h1.trans h2

namespace Galambos

/-- The negative-order power mean `(x^{-θ} + y^{-θ})^{-1/θ}`. -/
noncomputable def negMean (θ x y : ℝ) : ℝ := (x ^ (-θ) + y ^ (-θ)) ^ (-θ⁻¹)

theorem negMean_pos {θ x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < negMean θ x y :=
  Real.rpow_pos_of_pos (add_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)) _

theorem negMean_rpow {θ x y : ℝ} (hθ : 0 < θ) (hx : 0 < x) (hy : 0 < y) :
    negMean θ x y ^ (-θ) = x ^ (-θ) + y ^ (-θ) := by
  rw [negMean, ← Real.rpow_mul (add_pos (Real.rpow_pos_of_pos hx _)
    (Real.rpow_pos_of_pos hy _)).le, show -θ⁻¹ * -θ = 1 by field_simp, Real.rpow_one]

/-- Reverse Minkowski: the negative-order power mean is superadditive. -/
theorem negMean_superadditive {θ : ℝ} (hθ : 0 < θ) {x1 y1 x2 y2 : ℝ} (hx1 : 0 < x1)
    (hy1 : 0 < y1) (hx2 : 0 < x2) (hy2 : 0 < y2) :
    negMean θ x1 y1 + negMean θ x2 y2 ≤ negMean θ (x1 + x2) (y1 + y2) := by
  set a := negMean θ x1 y1 with ha
  set b := negMean θ x2 y2 with hb
  have ha0 : 0 < a := negMean_pos hx1 hy1
  have hb0 : 0 < b := negMean_pos hx2 hy2
  have hab : 0 < a + b := add_pos ha0 hb0
  have hS1 : 0 < x1 ^ (-θ) + y1 ^ (-θ) := add_pos (Real.rpow_pos_of_pos hx1 _)
    (Real.rpow_pos_of_pos hy1 _)
  have hS2 : 0 < x2 ^ (-θ) + y2 ^ (-θ) := add_pos (Real.rpow_pos_of_pos hx2 _)
    (Real.rpow_pos_of_pos hy2 _)
  have hconv := convexOn_rpow_nonpos (p := -θ) (by linarith)
  have hw0 : 0 ≤ a / (a + b) := (div_pos ha0 hab).le
  have hw1 : 0 ≤ b / (a + b) := (div_pos hb0 hab).le
  have hw : a / (a + b) + b / (a + b) = 1 := by field_simp
  have key (z1 z2 : ℝ) (hz1 : 0 < z1) (hz2 : 0 < z2) :
      ((z1 + z2) / (a + b)) ^ (-θ) ≤
        a / (a + b) * (z1 ^ (-θ) / a ^ (-θ)) + b / (a + b) * (z2 ^ (-θ) / b ^ (-θ)) := by
    have h := hconv.2 (mem_Ioi.2 (div_pos hz1 ha0)) (mem_Ioi.2 (div_pos hz2 hb0)) hw0 hw1 hw
    simp only [smul_eq_mul] at h
    rw [Real.div_rpow hz1.le ha0.le, Real.div_rpow hz2.le hb0.le] at h
    have he : a / (a + b) * (z1 / a) + b / (a + b) * (z2 / b) = (z1 + z2) / (a + b) := by
      field_simp
    rw [he] at h
    exact h
  have k1 := key x1 x2 hx1 hx2
  have k2 := key y1 y2 hy1 hy2
  rw [ha, hb, negMean_rpow hθ hx1 hy1, negMean_rpow hθ hx2 hy2, ← ha, ← hb] at k1 k2
  have hsum : ((x1 + x2) / (a + b)) ^ (-θ) + ((y1 + y2) / (a + b)) ^ (-θ) ≤ 1 := by
    have e1 : a / (a + b) * (x1 ^ (-θ) / (x1 ^ (-θ) + y1 ^ (-θ))) +
        a / (a + b) * (y1 ^ (-θ) / (x1 ^ (-θ) + y1 ^ (-θ))) = a / (a + b) := by
      field_simp
    have e2 : b / (a + b) * (x2 ^ (-θ) / (x2 ^ (-θ) + y2 ^ (-θ))) +
        b / (a + b) * (y2 ^ (-θ) / (x2 ^ (-θ) + y2 ^ (-θ))) = b / (a + b) := by
      field_simp
    linarith
  rw [Real.div_rpow (by linarith) hab.le, Real.div_rpow (by linarith) hab.le, ← add_div,
    div_le_one (Real.rpow_pos_of_pos hab _)] at hsum
  have hX : 0 < (x1 + x2) ^ (-θ) + (y1 + y2) ^ (-θ) :=
    add_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (by linarith) _)
  have hmono := Real.rpow_le_rpow_of_nonpos hX hsum (by
    have := inv_pos.2 hθ
    linarith : -θ⁻¹ ≤ 0)
  rw [← Real.rpow_mul hab.le, show -θ * -θ⁻¹ = 1 by field_simp, Real.rpow_one] at hmono
  exact hmono

theorem negMean_eq {θ x y : ℝ} (hθ : 0 < θ) (hx : 0 < x) (hy : 0 < y) :
    negMean θ x y = x * y / (x ^ θ + y ^ θ) ^ θ⁻¹ := by
  have hxθ := Real.rpow_pos_of_pos hx θ
  have hyθ := Real.rpow_pos_of_pos hy θ
  rw [negMean, Real.rpow_neg hx.le, Real.rpow_neg hy.le,
    show (x ^ θ)⁻¹ + (y ^ θ)⁻¹ = (x ^ θ + y ^ θ) / (x ^ θ * y ^ θ) by field_simp; ring,
    Real.rpow_neg (div_pos (add_pos hxθ hyθ) (mul_pos hxθ hyθ)).le,
    Real.div_rpow (add_pos hxθ hyθ).le (mul_pos hxθ hyθ).le, Real.mul_rpow hxθ.le hyθ.le,
    Real.rpow_rpow_inv hx.le hθ.ne', Real.rpow_rpow_inv hy.le hθ.ne', inv_div]

theorem negMean_smul {θ c x y : ℝ} (hθ : 0 < θ) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    negMean θ (c * x) (c * y) = c * negMean θ x y := by
  rw [negMean_eq hθ (mul_pos hc hx) (mul_pos hc hy), negMean_eq hθ hx hy,
    Real.mul_rpow hc.le hx.le, Real.mul_rpow hc.le hy.le, ← mul_add,
    Real.mul_rpow (Real.rpow_pos_of_pos hc _).le
      (add_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)).le,
    Real.rpow_rpow_inv hc.le hθ.ne']
  have : 0 < (x ^ θ + y ^ θ) ^ θ⁻¹ :=
    Real.rpow_pos_of_pos (add_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)) _
  field_simp

end Galambos

open Galambos

/-- The Galambos (negative logistic) Pickands function
`1 - t (1-t) / (t^θ + (1-t)^θ)^{1/θ}`. -/
noncomputable def galambosPickands (θ t : ℝ) : ℝ :=
  1 - t * (1 - t) / (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹

private theorem norm_ge {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc (0 : ℝ) 1) :
    t ≤ (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹ ∧ 1 - t ≤ (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹ := by
  have h0 : 0 ≤ t := ht.1
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have hp0 := Real.rpow_nonneg h0 θ
  have hp1 := Real.rpow_nonneg h1 θ
  constructor
  · calc t = (t ^ θ) ^ θ⁻¹ := (Real.rpow_rpow_inv h0 hθ.ne').symm
      _ ≤ _ := Real.rpow_le_rpow hp0 (by linarith) (inv_nonneg.2 hθ.le)
  · calc 1 - t = ((1 - t) ^ θ) ^ θ⁻¹ := (Real.rpow_rpow_inv h1 hθ.ne').symm
      _ ≤ _ := Real.rpow_le_rpow hp1 (by linarith) (inv_nonneg.2 hθ.le)

private theorem norm_pos {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹ := by
  obtain ⟨h1, h2⟩ := norm_ge hθ ht
  rcases le_total t (1 / 2) with h | h <;> linarith

theorem galambosPickands_eq {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    galambosPickands θ t = 1 - negMean θ t (1 - t) := by
  rw [galambosPickands, negMean_eq hθ ht.1 (by linarith [ht.2])]

/-- The Galambos function is a Pickands dependence function for every `θ > 0`. -/
theorem isPickandsFunction_galambosPickands {θ : ℝ} (hθ : 0 < θ) :
    IsPickandsFunction (galambosPickands θ) := by
  have hcont : ContinuousOn (galambosPickands θ) (Icc 0 1) := by
    refine continuousOn_const.sub (ContinuousOn.div (by fun_prop) ?_ fun t ht =>
      (norm_pos hθ ht).ne')
    refine ((Real.continuous_rpow_const hθ.le).add
      ((Real.continuous_rpow_const hθ.le).comp (continuous_const.sub continuous_id))
      |>.continuousOn).rpow_const fun t _ => Or.inr (inv_nonneg.2 hθ.le)
  have hconvIoo : ConvexOn ℝ (Ioo 0 1) (galambosPickands θ) := by
    refine ⟨convex_Ioo 0 1, fun t ht s hs a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have hts : a * t + b * s ∈ Ioo (0 : ℝ) 1 := (convex_Ioo 0 1) ht hs ha hb hab
    rw [galambosPickands_eq hθ ht, galambosPickands_eq hθ hs, galambosPickands_eq hθ hts]
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simp
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp
    have h1t : 0 < 1 - t := by linarith [ht.2]
    have h1s : 0 < 1 - s := by linarith [hs.2]
    have hsup := negMean_superadditive hθ (mul_pos ha0 ht.1) (mul_pos ha0 h1t)
      (mul_pos hb0 hs.1) (mul_pos hb0 h1s)
    rw [negMean_smul hθ ha0 ht.1 h1t, negMean_smul hθ hb0 hs.1 h1s,
      show a * (1 - t) + b * (1 - s) = 1 - (a * t + b * s) by linear_combination hab] at hsup
    nlinarith
  refine ⟨convexOn_Icc_of_convexOn_Ioo hcont hconvIoo, fun t ht => ?_, fun t ht => ?_⟩
  · have hN := norm_pos hθ ht
    have : 0 ≤ t * (1 - t) / (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹ :=
      div_nonneg (mul_nonneg ht.1 (by linarith [ht.2])) hN.le
    rw [galambosPickands]
    linarith
  · obtain ⟨hn1, hn2⟩ := norm_ge hθ ht
    have hN := norm_pos hθ ht
    have h1 : t * (1 - t) / (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹ ≤ t := by
      rw [div_le_iff₀ hN]
      exact mul_le_mul_of_nonneg_left hn2 ht.1
    have h2 : t * (1 - t) / (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹ ≤ 1 - t := by
      rw [div_le_iff₀ hN, mul_comm t]
      exact mul_le_mul_of_nonneg_left hn1 (by linarith [ht.2])
    rw [galambosPickands]
    exact max_le (by linarith) (by linarith)

/-- The Galambos copula, `θ > 0`. -/
noncomputable def galambos (θ : ℝ) (hθ : 0 < θ) : Copula 2 :=
  pickandsCopula (galambosPickands θ) (isPickandsFunction_galambosPickands hθ)

theorem isExtremeValue_galambos {θ : ℝ} (hθ : 0 < θ) : (galambos θ hθ).IsExtremeValue :=
  isExtremeValue_pickandsCopula _

/-- The classical Galambos CDF `u v exp(((-log u)^{-θ} + (-log v)^{-θ})^{-1/θ})` on `(0,1)²`. -/
theorem cdf_galambos {θ : ℝ} (hθ : 0 < θ) {u v : I} (hu : (u : ℝ) ∈ Ioo (0 : ℝ) 1)
    (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    (galambos θ hθ).cdf ![u, v] = (u : ℝ) * v *
      Real.exp (((-Real.log u) ^ (-θ) + (-Real.log v) ^ (-θ)) ^ (-θ⁻¹)) := by
  have hu0 : u ≠ 0 := fun h => by simp [h] at hu
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hx : 0 < -Real.log u := neg_pos.2 (Real.log_neg hu.1 hu.2)
  have hy : 0 < -Real.log v := neg_pos.2 (Real.log_neg hv.1 hv.2)
  have hs : 0 < -Real.log u + -Real.log v := add_pos hx hy
  have hr : -Real.log v / (-Real.log u + -Real.log v) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hy hs, (div_lt_one hs).2 (by linarith)⟩
  rw [galambos, cdf_pickandsCopula_two, pickandsCDF, ite_eq_right (not_or.2 ⟨hu0, hv0⟩),
    pickandsTail, galambosPickands_eq hθ hr]
  have hsne : -Real.log u + -Real.log v ≠ 0 := hs.ne'
  have e1 : -Real.log v / (-Real.log u + -Real.log v) =
      (-Real.log u + -Real.log v)⁻¹ * -Real.log v := by rw [div_eq_inv_mul]
  have e2 : 1 - -Real.log v / (-Real.log u + -Real.log v) =
      (-Real.log u + -Real.log v)⁻¹ * -Real.log u := by
    field_simp
    ring
  have hcomm : negMean θ (-Real.log v) (-Real.log u) = negMean θ (-Real.log u) (-Real.log v) := by
    rw [negMean, negMean, add_comm]
  rw [e2, e1, negMean_smul hθ (inv_pos.2 hs) hy hx, hcomm]
  have he : -((-Real.log u + -Real.log v) * (1 - (-Real.log u + -Real.log v)⁻¹ *
      negMean θ (-Real.log u) (-Real.log v))) =
      Real.log u + Real.log v + negMean θ (-Real.log u) (-Real.log v) := by
    field_simp
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_log hu.1, Real.exp_log hv.1, negMean]

/-- Upper tail dependence of the Galambos copula: `λ_U = 2^{-1/θ}`. -/
theorem hasUpperTailDependence_galambos {θ : ℝ} (hθ : 0 < θ) :
    (galambos θ hθ).HasUpperTailDependence ((2 : ℝ) ^ (-θ⁻¹)) := by
  have h := hasUpperTailDependence_pickandsCopula (isPickandsFunction_galambosPickands hθ)
  have hval : 2 * (1 - galambosPickands θ (1 / 2)) = (2 : ℝ) ^ (-θ⁻¹) := by
    rw [galambosPickands_eq hθ ⟨by norm_num, by norm_num⟩, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      negMean, ← two_mul, Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), show -θ * -θ⁻¹ = 1 by field_simp,
      Real.rpow_one]
    ring
  rw [← hval]
  exact h

end ProbabilityTheory.Copula
