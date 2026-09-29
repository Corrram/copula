/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.NelsenTable.N17
import Copula.Families.NelsenTable.N21
import Copula.Families.Nelsen7
import Copula.Rank.Integration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Limits at `θ → ∞` of Nelsen's families 17 and 21

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1 lists the limiting case
`C_∞ = M` for families 17 and 21. Both are proved here as pointwise convergence of the CDFs
along any filter on which the parameter tends to `+∞` (`tendsto_nelsen21_atTop`,
`tendsto_nelsen17_atTop`). Since every copula lies below `M`, only a lower bound is needed:

* family 21: with `s = 1 − u`, `t = 1 − v`, `w = max(s, t)`, Bernoulli's inequality gives
  `C_θ(u, v) ≥ 1 − (2θ)^{1/θ} w`, and `(2θ)^{1/θ} → 1`;
* family 17: with `z = min(u, v)`, `C_θ(u, v) ≥ (2 / (1 − 2^{−θ}))^{−1/θ} (1 + z) − 1`, and the
  factor tends to `1`.

For family 17 at `θ → −∞` the limit is **not** `W`: it is
`max(0, ((1 + u)(1 + v) − 2)/2) = max(0, (uv + u + v − 1)/2)`, the member `θ = 1/2` of family 7
(`tendsto_nelsen17_atBot`). With `κ = −θ`, `r = (1 + u)(1 + v)/2` and
`P = (1 − (1 + u)^{−κ})(1 − (1 + v)^{−κ})`, the CDF satisfies
`max(1, rP) − 1 ≤ C_θ(u, v) ≤ 3^{1/κ} max(1, r) − 1` (`nelsen17_bounds_neg`).
-/

open Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem fin2_eq'' (u : Fin 2 → I) : u = ![u 0, u 1] := by
  funext i
  fin_cases i <;> rfl

private theorem coe_pos_of_ne' {u : I} (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

/-- `(2r)^{1/r} → 1` as `r → ∞`. -/
theorem tendsto_two_mul_rpow_inv_atTop :
    Tendsto (fun r : ℝ => (2 * r) ^ r⁻¹) atTop (𝓝 1) := by
  have h1 : Tendsto (fun r : ℝ => r ^ r⁻¹) atTop (𝓝 1) := by
    simpa only [one_div] using tendsto_rpow_div
  have h2 : Tendsto (fun r : ℝ => (2 : ℝ) ^ r⁻¹) atTop (𝓝 1) := by
    have h := ((Real.continuousAt_const_rpow (a := 2) (b := 0) (by norm_num)).tendsto).comp
      tendsto_inv_atTop_zero
    rwa [Real.rpow_zero] at h
  have h := h2.mul h1
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  exact (Real.mul_rpow (by norm_num) hr.le).symm

/-- The copula bound `C ≤ M` in the coordinates of a CDF evaluation. -/
private theorem cdf_le_min (C : Copula 2) (u : Fin 2 → I) : C.cdf u ≤ min (u 0 : ℝ) (u 1) := by
  have h := C.cdf_le_comonotonic u
  rwa [cdf_comonotonic_two] at h

/-- The lower bound `C_θ(u, v) ≥ 1 − (2θ)^{1/θ} max(1 − u, 1 − v)` for family 21. -/
theorem nelsen21_lower_bound (θ : ℝ) (hθ : 1 ≤ θ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - (2 * θ) ^ θ⁻¹ * max (1 - x) (1 - y) ≤
      1 - (1 - (max ((1 - (1 - x) ^ θ) ^ θ⁻¹ + (1 - (1 - y) ^ θ) ^ θ⁻¹ - 1) 0) ^ θ) ^ θ⁻¹ := by
  have hθ0 : 0 < θ := by linarith
  have hq0 : 0 < θ⁻¹ := inv_pos.mpr hθ0
  have hq1 : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
  set s := 1 - x with hs
  set t := 1 - y with ht
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hs1 : s ≤ 1 := by linarith
  have ht1 : t ≤ 1 := by linarith
  set w := max s t with hw
  have hw0 : 0 ≤ w := le_max_of_le_left hs0
  have hsθ : s ^ θ ≤ 1 := Real.rpow_le_one hs0 hs1 hθ0.le
  have htθ : t ^ θ ≤ 1 := Real.rpow_le_one ht0 ht1 hθ0.le
  -- `A ≥ 1 − s^θ`, `B ≥ 1 − t^θ`
  have hA : 1 - s ^ θ ≤ (1 - s ^ θ) ^ θ⁻¹ :=
    Real.self_le_rpow_of_le_one (by linarith) (by linarith [Real.rpow_nonneg hs0 θ]) hq1
  have hB : 1 - t ^ θ ≤ (1 - t ^ θ) ^ θ⁻¹ :=
    Real.self_le_rpow_of_le_one (by linarith) (by linarith [Real.rpow_nonneg ht0 θ]) hq1
  have hA1 : (1 - s ^ θ) ^ θ⁻¹ ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith [Real.rpow_nonneg hs0 θ]) hq0.le
  have hB1 : (1 - t ^ θ) ^ θ⁻¹ ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith [Real.rpow_nonneg ht0 θ]) hq0.le
  set m := max ((1 - s ^ θ) ^ θ⁻¹ + (1 - t ^ θ) ^ θ⁻¹ - 1) 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  have hm1 : m ≤ 1 := max_le (by linarith) zero_le_one
  set ε := s ^ θ + t ^ θ with hε
  have hmε : 1 - ε ≤ m := le_max_of_le_left (by linarith)
  -- Bernoulli: `m^θ ≥ 1 − θ ε`
  have hmθ : 1 - θ * ε ≤ m ^ θ := by
    rcases le_or_gt ε 1 with hε1 | hε1
    · have hb := one_add_mul_self_le_rpow_one_add (show -1 ≤ -ε by linarith) hθ
      have hmono : (1 + -ε) ^ θ ≤ m ^ θ :=
        Real.rpow_le_rpow (by linarith) (by linarith) hθ0.le
      linarith
    · have : 1 - θ * ε ≤ 0 := by nlinarith
      linarith [Real.rpow_nonneg hm0 θ]
  have hεw : ε ≤ 2 * w ^ θ := by
    have h1 : s ^ θ ≤ w ^ θ := Real.rpow_le_rpow hs0 (le_max_left _ _) hθ0.le
    have h2 : t ^ θ ≤ w ^ θ := Real.rpow_le_rpow ht0 (le_max_right _ _) hθ0.le
    linarith
  have hD0 : 0 ≤ 1 - m ^ θ := by linarith [Real.rpow_le_one hm0 hm1 hθ0.le]
  have hD : 1 - m ^ θ ≤ 2 * θ * w ^ θ := by nlinarith
  have hpow : (1 - m ^ θ) ^ θ⁻¹ ≤ (2 * θ * w ^ θ) ^ θ⁻¹ := Real.rpow_le_rpow hD0 hD hq0.le
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hw0 θ),
    Real.rpow_rpow_inv hw0 hθ0.ne'] at hpow
  linarith

/-- The limit `M` of Nelsen's family 21 as `θ → ∞` (Table 4.1), pointwise on the unit square. -/
theorem tendsto_nelsen21_atTop {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, 1 ≤ θ a)
    (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen21 (θ a) (hθ a)).cdf u) l (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx0 : 0 ≤ x := (u 0).property.1
  have hy0 : 0 ≤ y := (u 1).property.1
  have hx1 : x ≤ 1 := (u 0).property.2
  have hy1 : y ≤ 1 := (u 1).property.2
  rw [cdf_comonotonic_two, ← hxdef, ← hydef]
  have hlow : Tendsto (fun a => 1 - (2 * θ a) ^ (θ a)⁻¹ * max (1 - x) (1 - y)) l
      (𝓝 (min x y)) := by
    have h := ((tendsto_two_mul_rpow_inv_atTop.comp hlim).mul_const
      (max (1 - x) (1 - y))).const_sub 1
    rw [one_mul] at h
    have he : 1 - max (1 - x) (1 - y) = min x y := by
      rcases le_total x y with hxy | hxy
      · rw [max_eq_left (by linarith), min_eq_left hxy]; ring
      · rw [max_eq_right (by linarith), min_eq_right hxy]; ring
    rw [he] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun a => ?_)
    (fun a => cdf_le_min _ u)
  change _ ≤ (nelsen21 (θ a) (hθ a)).cdf u
  rw [fin2_eq'' u, cdf_nelsen21 (θ a) (hθ a) (u 0) (u 1) hu hv]
  exact nelsen21_lower_bound (θ a) (hθ a) hx0 hx1 hy0 hy1

/-- The lower bound `C_θ(u, v) ≥ (2 / (1 − 2^{−θ}))^{−1/θ} (1 + min(u, v)) − 1` for family 17,
`θ > 0`, `u, v ∈ (0, 1]`. -/
theorem nelsen17_lower_bound (θ : ℝ) (hθ : 0 < θ) {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    (2 / (1 - (2 : ℝ) ^ (-θ))) ^ (-θ⁻¹) * (1 + min x y) - 1 ≤
      (1 + ((1 + x) ^ (-θ) - 1) * ((1 + y) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) - 1 := by
  set a := (1 + x) ^ (-θ) with ha
  set b := (1 + y) ^ (-θ) with hb
  set c := (2 : ℝ) ^ (-θ) with hc
  have hnθ : -θ < 0 := by linarith
  have ha0 : 0 < a := Real.rpow_pos_of_pos (by linarith) _
  have hb0 : 0 < b := Real.rpow_pos_of_pos (by linarith) _
  have hc0 : 0 < c := Real.rpow_pos_of_pos two_pos _
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hnθ
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hnθ
  have hca : c ≤ a := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hnθ.le
  have hcb : c ≤ b := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) hnθ.le
  have hc1 : c < 1 := lt_of_le_of_lt hca ha1
  set z := min x y with hz
  have hz0 : 0 < z := lt_min hx0 hy0
  set e := (1 + z) ^ (-θ) with he
  have hae : a ≤ e := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [min_le_left x y])
    hnθ.le
  have hbe : b ≤ e := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [min_le_right x y])
    hnθ.le
  have he0 : 0 < e := Real.rpow_pos_of_pos (by linarith) _
  -- the base of the power
  set β := 1 + (a - 1) * (b - 1) / (c - 1) with hβ
  have hc1' : c - 1 ≠ 0 := by linarith
  have h1c : 1 - c ≠ 0 := by linarith
  have hβeq : β = (a + b - a * b - c) / (1 - c) := by
    rw [hβ, eq_div_iff h1c]
    field_simp
    ring
  have hβpos : 0 < β := by
    rw [hβeq]
    apply div_pos _ (by linarith)
    nlinarith [mul_pos (sub_pos.mpr ha1) hb0]
  have hβle : β ≤ 2 * e / (1 - c) := by
    rw [hβeq]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [mul_pos ha0 hb0]
  have hq : -θ⁻¹ ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr hθ.le)
  have hmono : (2 * e / (1 - c)) ^ (-θ⁻¹) ≤ β ^ (-θ⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hβpos hβle hq
  have hsplit : (2 * e / (1 - c)) ^ (-θ⁻¹) = (2 / (1 - c)) ^ (-θ⁻¹) * (1 + z) := by
    rw [mul_div_right_comm, Real.mul_rpow (div_pos two_pos (by linarith)).le he0.le, he,
      ← Real.rpow_mul (by linarith), show -θ * -θ⁻¹ = 1 by field_simp, Real.rpow_one]
  linarith

/-- The limit `M` of Nelsen's family 17 as `θ → ∞` (Table 4.1), pointwise on the unit square. -/
theorem tendsto_nelsen17_atTop {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen17 (θ a) (hθ a).ne').cdf u) l (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx0 := coe_pos_of_ne' hu
  have hy0 := coe_pos_of_ne' hv
  have hx1 : x ≤ 1 := (u 0).property.2
  have hy1 : y ≤ 1 := (u 1).property.2
  rw [cdf_comonotonic_two, ← hxdef, ← hydef]
  -- the factor `(2 / (1 − 2^{−θ}))^{−1/θ} → 1`
  have h2 : Tendsto (fun r : ℝ => (2 : ℝ) ^ (-r)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_neg_atTop_atBot).const_mul_atBot (Real.log_pos one_lt_two))
    refine h.congr' (Eventually.of_forall fun r => ?_)
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos two_pos]
  have hbase : Tendsto (fun r : ℝ => 2 / (1 - (2 : ℝ) ^ (-r))) atTop (𝓝 2) := by
    have h := (h2.const_sub 1)
    rw [sub_zero] at h
    have h' := (tendsto_const_nhds (x := (2 : ℝ))).div h one_ne_zero
    rwa [div_one] at h'
  have hexp : Tendsto (fun r : ℝ => -r⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg
    rwa [neg_zero] at h
  have hfac : Tendsto (fun r : ℝ => (2 / (1 - (2 : ℝ) ^ (-r))) ^ (-r⁻¹)) atTop (𝓝 1) := by
    have h := hbase.rpow hexp (Or.inl two_ne_zero)
    rwa [Real.rpow_zero] at h
  have hlow : Tendsto (fun a => (2 / (1 - (2 : ℝ) ^ (-θ a))) ^ (-(θ a)⁻¹) * (1 + min x y) - 1) l
      (𝓝 (min x y)) := by
    have h := ((hfac.comp hlim).mul_const (1 + min x y)).sub_const 1
    rw [one_mul, add_sub_cancel_left] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun a => ?_)
    (fun a => cdf_le_min _ u)
  change _ ≤ (nelsen17 (θ a) (hθ a).ne').cdf u
  rw [fin2_eq'' u, cdf_nelsen17 (θ a) (hθ a).ne' (u 0) (u 1) hu hv]
  exact nelsen17_lower_bound (θ a) (hθ a) hx0 hx1 hy0 hy1

/-- Two-sided bounds for family 17 at negative parameters `θ ≤ −1` (with `κ = −θ`):
`max(1, r P) − 1 ≤ C_θ(u, v) ≤ 3^{1/κ} max(1, r) − 1`, `r = (1 + u)(1 + v)/2`,
`P = (1 − (1 + u)^{−κ})(1 − (1 + v)^{−κ})`. -/
theorem nelsen17_bounds_neg (θ : ℝ) (hθ : θ ≤ -1) {x y : ℝ} (hx0 : 0 < x) (hy0 : 0 < y) :
    max 1 ((1 + x) * (1 + y) / 2 * ((1 - ((1 + x) ^ (-θ))⁻¹) * (1 - ((1 + y) ^ (-θ))⁻¹))) - 1 ≤
      (1 + ((1 + x) ^ (-θ) - 1) * ((1 + y) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) - 1 ∧
    (1 + ((1 + x) ^ (-θ) - 1) * ((1 + y) ^ (-θ) - 1) / ((2 : ℝ) ^ (-θ) - 1)) ^ (-θ⁻¹) - 1 ≤
      (3 : ℝ) ^ (-θ)⁻¹ * max 1 ((1 + x) * (1 + y) / 2) - 1 := by
  set κ := -θ with hκ
  have hκ1 : 1 ≤ κ := by linarith
  have hκ0 : 0 < κ := by linarith
  have hexp : -θ⁻¹ = κ⁻¹ := by rw [hκ, inv_neg]
  rw [hexp]
  set a := (1 + x) ^ κ with ha
  set b := (1 + y) ^ κ with hb
  set c := (2 : ℝ) ^ κ with hc
  have ha1 : 1 < a := Real.one_lt_rpow (by linarith) hκ0
  have hb1 : 1 < b := Real.one_lt_rpow (by linarith) hκ0
  have hc2 : 2 ≤ c := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hκ1
    rwa [Real.rpow_one] at this
  set r := (1 + x) * (1 + y) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrκ : r ^ κ = a * b / c := by
    rw [hr, Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by linarith) (by linarith)]
  set β := 1 + (a - 1) * (b - 1) / (c - 1) with hβ
  have hc1 : 0 < c - 1 := by linarith
  have hq0 : 0 < κ⁻¹ := inv_pos.mpr hκ0
  have hq1 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ1
  have hβ1 : 1 ≤ β := by
    have : 0 ≤ (a - 1) * (b - 1) / (c - 1) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) hc1.le
    linarith
  have hβ0 : 0 < β := by linarith
  constructor
  · -- lower bound
    set P := (1 - a⁻¹) * (1 - b⁻¹) with hP
    have hP0 : 0 ≤ P := mul_nonneg (by have := inv_lt_one_of_one_lt₀ ha1; linarith)
      (by have := inv_lt_one_of_one_lt₀ hb1; linarith)
    have hP1 : P ≤ 1 := by
      have h1 : 0 < a⁻¹ := inv_pos.mpr (by linarith)
      have h2 : 0 < b⁻¹ := inv_pos.mpr (by linarith)
      have h3 : 1 - a⁻¹ ≤ 1 := by linarith
      have h4 : 1 - b⁻¹ ≤ 1 := by linarith
      have h5 : 0 ≤ 1 - a⁻¹ := by have := inv_lt_one_of_one_lt₀ ha1; linarith
      calc P = (1 - a⁻¹) * (1 - b⁻¹) := rfl
        _ ≤ 1 * 1 := mul_le_mul h3 h4 (by have := inv_lt_one_of_one_lt₀ hb1; linarith) zero_le_one
        _ = 1 := one_mul 1
    have hβP : r ^ κ * P ≤ β := by
      have heq : r ^ κ * P = (a - 1) * (b - 1) / c := by
        rw [hrκ, hP]
        field_simp
      rw [heq, hβ]
      have : (a - 1) * (b - 1) / c ≤ (a - 1) * (b - 1) / (c - 1) :=
        div_le_div_of_nonneg_left (mul_nonneg (by linarith) (by linarith)) hc1 (by linarith)
      linarith
    have hlow1 : 1 ≤ β ^ κ⁻¹ := Real.one_le_rpow hβ1 hq0.le
    have hlow2 : r * P ≤ β ^ κ⁻¹ := by
      have h1 : (r ^ κ * P) ^ κ⁻¹ ≤ β ^ κ⁻¹ :=
        Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hr0.le _) hP0) hβP hq0.le
      rw [Real.mul_rpow (Real.rpow_nonneg hr0.le _) hP0, Real.rpow_rpow_inv hr0.le hκ0.ne'] at h1
      have h2 : P ≤ P ^ κ⁻¹ := Real.self_le_rpow_of_le_one hP0 hP1 hq1
      nlinarith
    have := max_le hlow1 hlow2
    linarith
  · -- upper bound
    set M := max 1 r with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hβle : β ≤ 3 * M ^ κ := by
      have h1 : (a - 1) * (b - 1) / (c - 1) ≤ 2 * (a * b / c) := by
        rw [div_le_iff₀ hc1]
        have hab : (a - 1) * (b - 1) ≤ a * b := by nlinarith
        have : 2 * (a * b / c) * (c - 1) = a * b * (2 - 2 / c) := by field_simp
        rw [this]
        have h2c : 2 / c ≤ 1 := by rw [div_le_one (by linarith)]; exact hc2
        nlinarith [mul_pos (by linarith : (0 : ℝ) < a) (by linarith : (0 : ℝ) < b)]
      have h2 : r ^ κ ≤ M ^ κ := Real.rpow_le_rpow hr0.le (le_max_right _ _) hκ0.le
      have h3 : 1 ≤ M ^ κ := Real.one_le_rpow hM1 hκ0.le
      rw [hβ]
      rw [← hrκ] at h1
      linarith
    have h1 : β ^ κ⁻¹ ≤ (3 * M ^ κ) ^ κ⁻¹ := Real.rpow_le_rpow hβ0.le hβle hq0.le
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by linarith) _),
      Real.rpow_rpow_inv (by linarith) hκ0.ne'] at h1
    linarith

/-- The limit of Nelsen's family 17 as `θ → −∞`: pointwise convergence to
`max(0, (uv + u + v − 1)/2)`, the member `θ = 1/2` of Nelsen's family 7 (not `W`). -/
theorem tendsto_nelsen17_atBot {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, θ a < 0)
    (hlim : Tendsto θ l atBot) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen17 (θ a) (hθ a).ne).cdf u) l
      (𝓝 ((nelsen7 ⟨1 / 2, by norm_num, by norm_num⟩).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx0 := coe_pos_of_ne' hu
  have hy0 := coe_pos_of_ne' hv
  have hx1 : x ≤ 1 := (u 0).property.2
  have hy1 : y ≤ 1 := (u 1).property.2
  set r := (1 + x) * (1 + y) / 2 with hr
  have htarget : (nelsen7 ⟨1 / 2, by norm_num, by norm_num⟩).cdf u = max 1 r - 1 := by
    rw [fin2_eq'' u, cdf_nelsen7]
    change max 0 (1 / 2 * x * y + (1 - 1 / 2) * (x + y - 1)) = max 1 r - 1
    rw [hr, ← max_sub_sub_right, sub_self]
    congr 1
    ring
  rw [htarget]
  have hκ : Tendsto (fun a => -θ a) l atTop := tendsto_neg_atBot_atTop.comp hlim
  -- auxiliary limits
  have hpow : ∀ z : ℝ, 0 < z → Tendsto (fun k : ℝ => ((1 + z) ^ k)⁻¹) atTop (𝓝 0) := by
    intro z hz
    have hlog : 0 < Real.log (1 + z) := Real.log_pos (by linarith)
    have h := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hlog)
    refine h.inv_tendsto_atTop.congr' (Eventually.of_forall fun k => ?_)
    simp only [Function.comp_apply, id, Pi.inv_apply]
    rw [Real.rpow_def_of_pos (by linarith)]
  have hP : Tendsto (fun a => (1 - ((1 + x) ^ (-θ a))⁻¹) * (1 - ((1 + y) ^ (-θ a))⁻¹)) l (𝓝 1) := by
    have h := (((hpow x hx0).comp hκ).const_sub 1).mul (((hpow y hy0).comp hκ).const_sub 1)
    simp only [sub_zero, mul_one] at h
    exact h
  have hlowT : Tendsto (fun a => max 1 (r * ((1 - ((1 + x) ^ (-θ a))⁻¹) *
      (1 - ((1 + y) ^ (-θ a))⁻¹))) - 1) l (𝓝 (max 1 r - 1)) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).max (hP.const_mul r)).sub_const 1
    rwa [mul_one] at h
  have h3 : Tendsto (fun k : ℝ => (3 : ℝ) ^ k⁻¹) atTop (𝓝 1) := by
    have h := ((Real.continuousAt_const_rpow (a := 3) (b := 0) (by norm_num)).tendsto).comp
      tendsto_inv_atTop_zero
    rwa [Real.rpow_zero] at h
  have hupT : Tendsto (fun a => (3 : ℝ) ^ (-θ a)⁻¹ * max 1 r - 1) l (𝓝 (max 1 r - 1)) := by
    have h := ((h3.comp hκ).mul_const (max 1 r)).sub_const 1
    rwa [one_mul] at h
  have hev : ∀ᶠ a in l, θ a ≤ -1 := hlim.eventually (eventually_le_atBot (-1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT hupT ?_ ?_
  · filter_upwards [hev] with a ha
    rw [fin2_eq'' u, cdf_nelsen17 (θ a) (hθ a).ne (u 0) (u 1) hu hv]
    exact (nelsen17_bounds_neg (θ a) ha hx0 hy0).1
  · filter_upwards [hev] with a ha
    rw [fin2_eq'' u, cdf_nelsen17 (θ a) (hθ a).ne (u 0) (u 1) hu hv]
    exact (nelsen17_bounds_neg (θ a) ha hx0 hy0).2

end ProbabilityTheory.Copula
