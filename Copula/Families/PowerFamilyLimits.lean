/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen
import Copula.Families.Nelsen12Limits
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter
open scoped unitInterval Topology

/-! # Infinite-parameter limits for Nelsen 14 and Genest–Ghoudi

The reciprocal-parameter power expansion and a variable-input two-coordinate
power-norm squeeze yield full-square pointwise convergence to comonotonicity.
-/

namespace ProbabilityTheory.Copula

private theorem tendsto_scaled_inverse_power {α : Type*} {l : Filter α}
    (θ : α → ℝ) (hlim : Tendsto θ l atTop) (u : ℝ) (hu : 0 < u) :
    Tendsto (fun z => θ z * (u ^ (-(θ z)⁻¹) - 1)) l (𝓝 (-Real.log u)) := by
  have hd : HasDerivAt (fun t : ℝ => u ^ (-t)) (-Real.log u) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).neg.const_rpow hu
    convert h using 1 <;> simp
  have hs := hd.tendsto_slope_zero_right.comp
    (tendsto_inv_atTop_nhdsGT_zero.comp hlim)
  simpa [Function.comp_def, Real.rpow_zero, smul_eq_mul] using hs


private theorem powerNorm_ge_max (p a b : ℝ) (hp : 0 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ (a ^ p + b ^ p) ^ p⁻¹ := by
  have hpa : a ^ p ≤ a ^ p + b ^ p := le_add_of_nonneg_right (Real.rpow_nonneg hb _)
  have hpb : b ^ p ≤ a ^ p + b ^ p := le_add_of_nonneg_left (Real.rpow_nonneg ha _)
  have hia := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hpa (inv_nonneg.mpr hp.le)
  have hib := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hpb (inv_nonneg.mpr hp.le)
  rw [Real.rpow_rpow_inv ha hp.ne'] at hia
  rw [Real.rpow_rpow_inv hb hp.ne'] at hib
  exact max_le hia hib

private theorem tendsto_scaled_powerNorm {α : Type*} {l : Filter α}
    (θ : α → ℝ) (hθ : ∀ᶠ z in l, 1 ≤ θ z) (hlim : Tendsto θ l atTop)
    (x y : α → ℝ) (hx : ∀ᶠ z in l, 0 ≤ x z) (hy : ∀ᶠ z in l, 0 ≤ y z)
    (X Y : ℝ)
    (hX : Tendsto (fun z => θ z * x z) l (𝓝 X))
    (hY : Tendsto (fun z => θ z * y z) l (𝓝 Y)) :
    Tendsto (fun z => θ z * ((x z ^ θ z + y z ^ θ z) ^ (θ z)⁻¹))
      l (𝓝 (max X Y)) := by
  have hm : Tendsto (fun z => max (θ z * x z) (θ z * y z)) l
      (𝓝 (max X Y)) := hX.max hY
  have hq : Tendsto (fun z => (2 : ℝ) ^ (θ z)⁻¹) l (𝓝 1) := by
    have hi := tendsto_inv_atTop_zero.comp hlim
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2)).rpow hi
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have hu : Tendsto (fun z => (2 : ℝ) ^ (θ z)⁻¹ *
      max (θ z * x z) (θ z * y z)) l (𝓝 (max X Y)) := by
    simpa only [one_mul] using hq.mul hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hm hu
  · filter_upwards [hθ, hx, hy] with z hθz hxz hyz
    have hz : 0 < θ z := by linarith
    have hn := powerNorm_ge_max (θ z) (x z) (y z) hz hxz hyz
    calc
      max (θ z * x z) (θ z * y z) = θ z * max (x z) (y z) :=
        (mul_max_of_nonneg (x z) (y z) hz.le).symm
      _ ≤ θ z * ((x z ^ θ z + y z ^ θ z) ^ (θ z)⁻¹) :=
        mul_le_mul_of_nonneg_left hn hz.le
  · filter_upwards [hθ, hx, hy] with z hθz hxz hyz
    have hz : 0 < θ z := by linarith
    have hn := twoTermPowerNorm_le (θ z) (x z) (y z) hz hxz hyz
    calc
      θ z * ((x z ^ θ z + y z ^ θ z) ^ (θ z)⁻¹) ≤
          θ z * ((2 : ℝ) ^ (θ z)⁻¹ * max (x z) (y z)) :=
        mul_le_mul_of_nonneg_left hn hz.le
      _ = (2 : ℝ) ^ (θ z)⁻¹ *
          max (θ z * x z) (θ z * y z) := by
        rw [← mul_max_of_nonneg (x z) (y z) hz.le]
        ring


private theorem tendsto_nelsen14_scaled_norm (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    Tendsto (fun p : ℝ =>
      p * ((((u : ℝ) ^ (-p⁻¹) - 1) ^ p +
        ((v : ℝ) ^ (-p⁻¹) - 1) ^ p) ^ p⁻¹))
      atTop (𝓝 (max (-Real.log u) (-Real.log v))) := by
  let x : ℝ → ℝ := fun p => (u : ℝ) ^ (-p⁻¹) - 1
  let y : ℝ → ℝ := fun p => (v : ℝ) ^ (-p⁻¹) - 1
  have hp : ∀ᶠ p : ℝ in atTop, 1 ≤ p := eventually_ge_atTop 1
  have hx : ∀ᶠ p : ℝ in atTop, 0 ≤ x p := by
    filter_upwards [hp] with p hp
    have hneg : -p⁻¹ ≤ 0 := by
      have hh : 0 < p := by linarith
      exact neg_nonpos.mpr (inv_nonneg.mpr hh.le)
    have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu u.property.2 hneg
    dsimp [x]
    linarith
  have hy : ∀ᶠ p : ℝ in atTop, 0 ≤ y p := by
    filter_upwards [hp] with p hp
    have hneg : -p⁻¹ ≤ 0 := by
      have hh : 0 < p := by linarith
      exact neg_nonpos.mpr (inv_nonneg.mpr hh.le)
    have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv v.property.2 hneg
    dsimp [y]
    linarith
  have hX : Tendsto (fun p : ℝ => p * x p) atTop (𝓝 (-Real.log u)) := by
    simpa only [x] using
      tendsto_scaled_inverse_power (fun p : ℝ => p) tendsto_id (u : ℝ) hu
  have hY : Tendsto (fun p : ℝ => p * y p) atTop (𝓝 (-Real.log v)) := by
    simpa only [y] using
      tendsto_scaled_inverse_power (fun p : ℝ => p) tendsto_id (v : ℝ) hv
  simpa only [x, y] using
    tendsto_scaled_powerNorm (fun p : ℝ => p) hp tendsto_id x y hx hy
      (-Real.log u) (-Real.log v) hX hY


private theorem exp_neg_max_neg_log_eq_min (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    Real.exp (-(max (-Real.log u) (-Real.log v))) =
      min (u : ℝ) (v : ℝ) := by
  rcases le_total (u : ℝ) (v : ℝ) with h | h
  · have hl : Real.log u ≤ Real.log v := Real.log_le_log hu h
    rw [max_eq_left (by linarith : -Real.log v ≤ -Real.log u), min_eq_left h]
    simpa using Real.exp_log hu
  · have hl : Real.log v ≤ Real.log u := Real.log_le_log hv h
    rw [max_eq_right (by linarith : -Real.log u ≤ -Real.log v), min_eq_right h]
    simpa using Real.exp_log hv

private theorem tendsto_nelsen14_analytic (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    Tendsto (fun p : ℝ =>
      (1 + ((((u : ℝ) ^ (-p⁻¹) - 1) ^ p +
        ((v : ℝ) ^ (-p⁻¹) - 1) ^ p) ^ p⁻¹)) ^ (-p))
      atTop (𝓝 (min (u : ℝ) (v : ℝ))) := by
  let g : ℝ → ℝ := fun p =>
    (((u : ℝ) ^ (-p⁻¹) - 1) ^ p +
      ((v : ℝ) ^ (-p⁻¹) - 1) ^ p) ^ p⁻¹
  have hs : Tendsto (fun p : ℝ => p * g p) atTop
      (𝓝 (max (-Real.log u) (-Real.log v))) := by
    simpa only [g] using tendsto_nelsen14_scaled_norm u v hu hv
  have hp := Real.tendsto_one_add_rpow_exp_of_tendsto hs
  have hi := hp.inv₀ (Real.exp_ne_zero _)
  have htarget : (Real.exp (max (-Real.log u) (-Real.log v)))⁻¹ =
      min (u : ℝ) (v : ℝ) := by
    rw [← Real.exp_neg]
    exact exp_neg_max_neg_log_eq_min u v hu hv
  have hi' : Tendsto (fun p : ℝ => ((1 + g p) ^ p)⁻¹) atTop
      (𝓝 (min (u : ℝ) (v : ℝ))) := by
    simpa only [htarget] using hi
  have hbase : ∀ᶠ p : ℝ in atTop, 0 ≤ 1 + g p := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with p hp
    have hp0 : 0 < p := by linarith
    have hneg : -p⁻¹ ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr hp0.le)
    have hxu : 0 ≤ (u : ℝ) ^ (-p⁻¹) - 1 := by
      have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu u.property.2 hneg
      linarith
    have hxv : 0 ≤ (v : ℝ) ^ (-p⁻¹) - 1 := by
      have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv v.property.2 hneg
      linarith
    have hg : 0 ≤ g p := by
      dsimp [g]
      exact Real.rpow_nonneg
        (add_nonneg (Real.rpow_nonneg hxu _) (Real.rpow_nonneg hxv _)) _
    linarith
  apply hi'.congr'
  filter_upwards [hbase] with p hp
  dsimp [g]
  exact (Real.rpow_neg hp p).symm


/-- Nelsen 14 converges pointwise to the upper Fréchet bound on the closed square. -/
theorem tendsto_nelsen14_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (nelsen14 (θ z) (hθ z)).cdf u) l
      (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (z : α) : (nelsen14 (θ z) (hθ z)).cdf u = 0 :=
      (nelsen14 (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (z : α) : (nelsen14 (θ z) (hθ z)).cdf u = 0 :=
      (nelsen14 (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  have hu' : 0 < (u 0 : ℝ) := lt_of_le_of_ne (u 0).property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv' : 0 < (u 1 : ℝ) := lt_of_le_of_ne (u 1).property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have ha := (tendsto_nelsen14_analytic (u 0) (u 1) hu' hv').comp hlim
  rw [cdf_comonotonic_two]
  have hformula (z : α) : (nelsen14 (θ z) (hθ z)).cdf u =
      (1 + ((((u 0 : ℝ) ^ (-(θ z)⁻¹) - 1) ^ (θ z) +
        ((u 1 : ℝ) ^ (-(θ z)⁻¹) - 1) ^ (θ z)) ^ (θ z)⁻¹)) ^ (-(θ z)) := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hz, nelsen14_cdf_full]
    simp only [hu, hv, or_self, ↓reduceIte]
    simp
  simpa only [Function.comp_def, hformula] using ha


private theorem tendsto_scaled_positive_power {α : Type*} {l : Filter α}
    (θ : α → ℝ) (hlim : Tendsto θ l atTop) (u : ℝ) (hu : 0 < u) :
    Tendsto (fun z => θ z * (1 - u ^ (θ z)⁻¹)) l (𝓝 (-Real.log u)) := by
  have hd : HasDerivAt (fun t : ℝ => u ^ t) (Real.log u) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_rpow hu
    convert h using 1 <;> simp
  have hs := hd.tendsto_slope_zero_right.comp
    (tendsto_inv_atTop_nhdsGT_zero.comp hlim)
  have hs' : Tendsto (fun z => θ z * (u ^ (θ z)⁻¹ - 1)) l
      (𝓝 (Real.log u)) := by
    simpa [Function.comp_def, Real.rpow_zero, smul_eq_mul] using hs
  convert hs'.neg using 1
  · ext z
    ring

private theorem tendsto_genestGhoudi_scaled_norm (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    Tendsto (fun p : ℝ =>
      p * ((((1 - (u : ℝ) ^ p⁻¹) ^ p +
        (1 - (v : ℝ) ^ p⁻¹) ^ p) ^ p⁻¹)))
      atTop (𝓝 (max (-Real.log u) (-Real.log v))) := by
  let x : ℝ → ℝ := fun p => 1 - (u : ℝ) ^ p⁻¹
  let y : ℝ → ℝ := fun p => 1 - (v : ℝ) ^ p⁻¹
  have hp : ∀ᶠ p : ℝ in atTop, 1 ≤ p := eventually_ge_atTop 1
  have hx : ∀ᶠ p : ℝ in atTop, 0 ≤ x p := by
    filter_upwards [hp] with p hp
    have hp0 : 0 < p := by linarith
    have hle := Real.rpow_le_one hu.le u.property.2 (inv_nonneg.mpr hp0.le)
    dsimp [x]
    linarith
  have hy : ∀ᶠ p : ℝ in atTop, 0 ≤ y p := by
    filter_upwards [hp] with p hp
    have hp0 : 0 < p := by linarith
    have hle := Real.rpow_le_one hv.le v.property.2 (inv_nonneg.mpr hp0.le)
    dsimp [y]
    linarith
  have hX : Tendsto (fun p : ℝ => p * x p) atTop (𝓝 (-Real.log u)) := by
    simpa only [x] using
      tendsto_scaled_positive_power (fun p : ℝ => p) tendsto_id (u : ℝ) hu
  have hY : Tendsto (fun p : ℝ => p * y p) atTop (𝓝 (-Real.log v)) := by
    simpa only [y] using
      tendsto_scaled_positive_power (fun p : ℝ => p) tendsto_id (v : ℝ) hv
  simpa only [x, y] using
    tendsto_scaled_powerNorm (fun p : ℝ => p) hp tendsto_id x y hx hy
      (-Real.log u) (-Real.log v) hX hY


private theorem tendsto_genestGhoudi_analytic (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    Tendsto (fun p : ℝ =>
      (max 0 (1 - (((1 - (u : ℝ) ^ p⁻¹) ^ p +
        (1 - (v : ℝ) ^ p⁻¹) ^ p) ^ p⁻¹))) ^ p)
      atTop (𝓝 (min (u : ℝ) (v : ℝ))) := by
  let g : ℝ → ℝ := fun p =>
    ((1 - (u : ℝ) ^ p⁻¹) ^ p +
      (1 - (v : ℝ) ^ p⁻¹) ^ p) ^ p⁻¹
  have hs : Tendsto (fun p : ℝ => p * g p) atTop
      (𝓝 (max (-Real.log u) (-Real.log v))) := by
    simpa only [g] using tendsto_genestGhoudi_scaled_norm u v hu hv
  have hzero : Tendsto g atTop (𝓝 0) := by
    have hi := hs.mul tendsto_inv_atTop_zero
    have hi' : Tendsto (fun p : ℝ => (p * g p) * p⁻¹) atTop (𝓝 0) := by
      simpa using hi
    apply hi'.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with p hp
    field_simp
  have hpos : ∀ᶠ p : ℝ in atTop, 0 ≤ 1 - g p := by
    have hh : ∀ᶠ p : ℝ in atTop, g p < 1 :=
      hzero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hh] with p hp
    linarith
  have hsneg : Tendsto (fun p : ℝ => p * (-g p)) atTop
      (𝓝 (-(max (-Real.log u) (-Real.log v)))) := by
    simpa only [mul_neg] using hs.neg
  have hp := Real.tendsto_one_add_rpow_exp_of_tendsto hsneg
  have hp' : Tendsto (fun p : ℝ => (1 - g p) ^ p) atTop
      (𝓝 (min (u : ℝ) (v : ℝ))) := by
    have htarget := exp_neg_max_neg_log_eq_min u v hu hv
    simpa only [sub_eq_add_neg, htarget] using hp
  apply hp'.congr'
  filter_upwards [hpos] with p hp
  dsimp [g]
  rw [max_eq_right hp]


/-- Genest–Ghoudi converges pointwise to the upper Fréchet bound on the closed square. -/
theorem tendsto_genestGhoudi_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (genestGhoudi (θ z) (hθ z)).cdf u) l
      (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (z : α) : (genestGhoudi (θ z) (hθ z)).cdf u = 0 :=
      (genestGhoudi (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (z : α) : (genestGhoudi (θ z) (hθ z)).cdf u = 0 :=
      (genestGhoudi (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  have hu' : 0 < (u 0 : ℝ) := lt_of_le_of_ne (u 0).property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv' : 0 < (u 1 : ℝ) := lt_of_le_of_ne (u 1).property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have ha := (tendsto_genestGhoudi_analytic (u 0) (u 1) hu' hv').comp hlim
  rw [cdf_comonotonic_two]
  have hformula (z : α) : (genestGhoudi (θ z) (hθ z)).cdf u =
      (max 0 (1 - (((1 - (u 0 : ℝ) ^ (θ z)⁻¹) ^ (θ z) +
        (1 - (u 1 : ℝ) ^ (θ z)⁻¹) ^ (θ z)) ^ (θ z)⁻¹))) ^ (θ z) := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hz, genestGhoudi_cdf_full]
    simp only [hu, hv, or_self, ↓reduceIte]
    simp
  simpa only [Function.comp_def, hformula] using ha

end ProbabilityTheory.Copula
