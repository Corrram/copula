/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.NelsenTable.N16
import Copula.Families.NelsenTable.N18
import Copula.Dependence.Clayton
import Copula.Rank.Integration

/-! # Limiting cases of Nelsen's families 16 and 18

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1 lists the limiting cases
`C_∞ = Π / (Σ - Π)` for family 16 and `C_∞ = M` for family 18. Both are proved here as
pointwise convergence of the CDFs on the closed unit square along any filter on which the
parameter tends to `+∞`. The limit `Π / (Σ - Π)`, i.e. `uv / (u + v - uv)`, is the Clayton
copula with parameter one.

For family 16 the CDF is rewritten, with `q = 1/θ`, as `2 / (√(T² + 4q) - T)` where
`T = q (u + v - 1) - (1/u + 1/v - 1)`, which is continuous at `q = 0`. For family 18 one has
`θ / ln (e^(θ/(u-1)) + e^(θ/(v-1))) → -(1 - min(u, v))` by squeezing the logarithm between
`-θ/(1 - min(u, v))` and that value plus `ln 2`.
-/

open Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem nelsenTable_clayton_one_rational (u v : I) (hu : 0 < (u : ℝ))
    (hv : 0 < (v : ℝ)) :
    (clayton 2 1 (by norm_num)).cdf ![u, v] =
      (u : ℝ) * (v : ℝ) / ((u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ)) := by
  rw [cdf_clayton_two_pos 1 (by norm_num) u v hu hv]
  norm_num
  rw [Real.rpow_neg_one, Real.rpow_neg_one, Real.rpow_neg_one]
  have hden : 0 < (u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ) := by
    have h := mul_nonneg hu.le (sub_nonneg.mpr v.property.2)
    nlinarith
  field_simp
  rw [show (v : ℝ) + (u : ℝ) - (u : ℝ) * (v : ℝ) = (u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ) by ring,
    div_self hden.ne']

private theorem fin2_eq (u : Fin 2 → I) : u = ![u 0, u 1] := by
  funext i
  fin_cases i <;> rfl

/-- `C_∞ = Π / (Σ - Π)`: as `θ → ∞`, Nelsen's family 16 converges pointwise to the Clayton
copula with parameter one, `uv / (u + v - uv)`. -/
theorem tendsto_nelsen16_atTop {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen16 (θ a) (hθ a)).cdf u) l
      (𝓝 ((clayton 2 1 (by norm_num)).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx : 0 < x := lt_of_le_of_ne (u 0).property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hy : 0 < y := lt_of_le_of_ne (u 1).property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hx1 : x ≤ 1 := (u 0).property.2
  have hy1 : y ≤ 1 := (u 1).property.2
  set k : ℝ := 1 / x + 1 / y - 1 with hk
  have hk0 : 0 < k := by
    have h1 : 1 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
    have h2 : 1 ≤ 1 / y := by rw [le_div_iff₀ hy]; linarith
    linarith
  set s₀ : ℝ := x + y - 1 with hs₀
  let G : ℝ → ℝ := fun q => 2 / (√((q * s₀ - k) ^ 2 + 4 * q) - (q * s₀ - k))
  have hG0 : G 0 = 1 / k := by
    simp only [G, zero_mul, zero_sub, mul_zero, add_zero, neg_sq, Real.sqrt_sq hk0.le, sub_neg_eq_add]
    field_simp
    ring
  have hcont : ContinuousAt G 0 := by
    apply continuousAt_const.div (by fun_prop)
    simp only [zero_mul, zero_sub, mul_zero, add_zero, neg_sq, Real.sqrt_sq hk0.le, sub_neg_eq_add]
    linarith
  have hpos : ∀ᶠ a in l, 0 < θ a := hlim.eventually (eventually_gt_atTop 0)
  have hformula : ∀ᶠ a in l, G (θ a)⁻¹ = (nelsen16 (θ a) (hθ a)).cdf u := by
    filter_upwards [hpos] with a ha
    set t := θ a with ht
    set q := t⁻¹ with hq
    have htq : t * q = 1 := mul_inv_cancel₀ ha.ne'
    have hq0 : 0 < q := inv_pos.mpr ha
    rw [fin2_eq u, cdf_nelsen16 t (hθ a) (u 0) (u 1) hu hv]
    set T := q * s₀ - k with hT
    set R := √(T ^ 2 + 4 * q) with hR
    have hR2 : R ^ 2 = T ^ 2 + 4 * q := Real.sq_sqrt (by positivity)
    have hR0 : 0 ≤ R := Real.sqrt_nonneg _
    have hRT : T < R := by
      rcases lt_or_ge T 0 with h | h
      · linarith
      · exact (Real.lt_sqrt h).mpr (by linarith)
    have hS : x + y - 1 - t * (1 / x + 1 / y - 1) = t * T := by
      rw [hT, hs₀, hk]
      linear_combination (-(x + y - 1)) * htq
    have hsq : (t * T) ^ 2 + 4 * t = t ^ 2 * (T ^ 2 + 4 * q) := by
      linear_combination (-4 * t) * htq
    rw [← hxdef, ← hydef, hS, hsq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ha.le, ← hR]
    show 2 / (R - T) = (t * T + t * R) / 2
    rw [div_eq_div_iff (by linarith) two_ne_zero]
    linear_combination (-t) * hR2 - 4 * htq
  have hlim' : Tendsto (fun a => G (θ a)⁻¹) l (𝓝 (G 0)) :=
    hcont.tendsto.comp (tendsto_inv_atTop_zero.comp hlim)
  have htarget : G 0 = (clayton 2 1 (by norm_num)).cdf u := by
    rw [hG0, fin2_eq u, nelsenTable_clayton_one_rational (u 0) (u 1) hx hy, ← hxdef, ← hydef]
    have hden : 0 < x + y - x * y := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hy1)]
    have hk' : k = (x + y - x * y) / (x * y) := by
      rw [hk]
      field_simp
      ring
    rw [hk', one_div_div]
  rw [← htarget]
  exact hlim'.congr' hformula

private theorem nelsen18_log_bounds {θ x y : ℝ} (hθ : 0 < θ) (hxy : x ≤ y)
    (hy1 : y < 1) :
    -θ / (1 - x) ≤ Real.log (Real.exp (θ / (x - 1)) + Real.exp (θ / (y - 1))) ∧
      Real.log (Real.exp (θ / (x - 1)) + Real.exp (θ / (y - 1))) ≤
        Real.log 2 + -θ / (1 - x) := by
  have hex : θ / (x - 1) = -θ / (1 - x) := by rw [← neg_sub, div_neg, neg_div]
  have hle : θ / (y - 1) ≤ -θ / (1 - x) := by
    have e : θ / (y - 1) = -θ / (1 - y) := by rw [← neg_sub, div_neg, neg_div]
    rw [e, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hθ.le (by linarith) (by linarith)
  rw [hex]
  have hE := Real.exp_pos (-θ / (1 - x))
  have hF := Real.exp_pos (θ / (y - 1))
  have hFle := Real.exp_le_exp.mpr hle
  constructor
  · calc -θ / (1 - x) = Real.log (Real.exp (-θ / (1 - x))) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log hE (by linarith)
  · calc Real.log (Real.exp (-θ / (1 - x)) + Real.exp (θ / (y - 1)))
        ≤ Real.log (2 * Real.exp (-θ / (1 - x))) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + -θ / (1 - x) := by
        rw [Real.log_mul two_ne_zero hE.ne', Real.log_exp]

/-- `C_∞ = M`: as `θ → ∞`, Nelsen's family 18 converges pointwise to the upper Fréchet bound. -/
theorem tendsto_nelsen18_atTop {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, 2 ≤ θ a)
    (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen18 (θ a) (hθ a)).cdf u) l (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  by_cases hu1 : u 0 = 1
  · rw [fin2_eq u, hu1]
    simp only [cdf_two_one_left]
    exact tendsto_const_nhds
  by_cases hv1 : u 1 = 1
  · rw [fin2_eq u, hv1]
    simp only [cdf_two_one_right]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx1 : x < 1 := lt_of_le_of_ne (u 0).property.2 (fun h => hu1 (Subtype.ext h))
  have hy1 : y < 1 := lt_of_le_of_ne (u 1).property.2 (fun h => hv1 (Subtype.ext h))
  set m : ℝ := min x y with hm
  have hm1 : m < 1 := lt_of_le_of_lt (min_le_left _ _) hx1
  let L : ℝ → ℝ := fun t => Real.log (Real.exp (t / (x - 1)) + Real.exp (t / (y - 1)))
  have hbounds : ∀ t, 0 < t → -t / (1 - m) ≤ L t ∧ L t ≤ Real.log 2 + -t / (1 - m) := by
    intro t ht
    rcases le_total x y with h | h
    · rw [hm, min_eq_left h]
      exact nelsen18_log_bounds ht h hy1
    · rw [hm, min_eq_right h]
      have hb := nelsen18_log_bounds ht h hx1
      simp only [L]
      rwa [add_comm (Real.exp (t / (x - 1)))]
  have hpos : ∀ᶠ a in l, 0 < θ a := hlim.eventually (eventually_gt_atTop 0)
  -- `L θ / θ → -1/(1 - m)` by squeezing.
  have hratio : Tendsto (fun a => L (θ a) / θ a) l (𝓝 (-1 / (1 - m))) := by
    have hup : Tendsto (fun a => Real.log 2 * (θ a)⁻¹ + -1 / (1 - m)) l
        (𝓝 (Real.log 2 * 0 + -1 / (1 - m))) :=
      ((tendsto_inv_atTop_zero.comp hlim).const_mul _).add_const _
    rw [mul_zero, zero_add] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hpos] with a ha
      rw [le_div_iff₀ ha, show -1 / (1 - m) * θ a = -θ a / (1 - m) by ring]
      exact (hbounds _ ha).1
    · filter_upwards [hpos] with a ha
      rw [div_le_iff₀ ha]
      have := (hbounds _ ha).2
      have e : (Real.log 2 * (θ a)⁻¹ + -1 / (1 - m)) * θ a = Real.log 2 + -θ a / (1 - m) := by
        field_simp
      rw [e]
      exact this
  have hne : -1 / (1 - m) ≠ 0 := div_ne_zero (by norm_num) (by linarith)
  have hinv : Tendsto (fun a => 1 + (L (θ a) / θ a)⁻¹) l (𝓝 (1 + (-1 / (1 - m))⁻¹)) :=
    (hratio.inv₀ hne).const_add 1
  have hval : 1 + (-1 / (1 - m))⁻¹ = m := by
    rw [inv_div]
    field_simp
    ring
  rw [hval] at hinv
  have hmax : Tendsto (fun a => max (1 + (L (θ a) / θ a)⁻¹) 0) l (𝓝 (max m 0)) :=
    hinv.max tendsto_const_nhds
  have hm0 : max m 0 = (comonotonic 2).cdf u := by
    rw [cdf_comonotonic_two, ← hxdef, ← hydef, ← hm]
    exact max_eq_left (le_min (u 0).property.1 (u 1).property.1)
  rw [← hm0]
  refine hmax.congr' ?_
  filter_upwards [hpos] with a ha
  rw [fin2_eq u, cdf_nelsen18 (θ a) (hθ a) (u 0) (u 1) hu hu1 hv hv1, ← hxdef, ← hydef, inv_div]

end ProbabilityTheory.Copula
