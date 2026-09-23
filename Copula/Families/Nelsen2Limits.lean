/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen
import Copula.Rank.Integration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Nelsen 2 infinite-parameter endpoint

The truncated-power family converges pointwise on the closed square to the
comonotonic copula for any real parameter path tending to infinity.
-/

open Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula
private theorem twoTermPowerNorm_le (p a b : ℝ) (hp : 0 < p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ p + b ^ p) ^ p⁻¹ ≤ (2 : ℝ) ^ p⁻¹ * max a b := by
  have hm : 0 ≤ max a b := ha.trans (le_max_left a b)
  have hpa : a ^ p ≤ (max a b) ^ p :=
    Real.rpow_le_rpow ha (le_max_left a b) hp.le
  have hpb : b ^ p ≤ (max a b) ^ p :=
    Real.rpow_le_rpow hb (le_max_right a b) hp.le
  have hsum : a ^ p + b ^ p ≤ 2 * (max a b) ^ p := by linarith
  have hpow := Real.rpow_le_rpow (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _))
    hsum (inv_nonneg.mpr hp.le)
  have heq : (2 * (max a b) ^ p) ^ p⁻¹ = (2 : ℝ) ^ p⁻¹ * max a b := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hm _),
      Real.rpow_rpow_inv hm hp.ne']
  rwa [heq] at hpow
/-- Nelsen 2 converges pointwise to the upper Fréchet bound as θ tends to infinity. -/
theorem tendsto_nelsen2_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen2 (θ a) (hθ a)).cdf u) l
      (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (a : α) : (nelsen2 (θ a) (hθ a)).cdf u = 0 :=
      (nelsen2 (θ a) (hθ a)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (a : α) : (nelsen2 (θ a) (hθ a)).cdf u = 0 :=
      (nelsen2 (θ a) (hθ a)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  let x : ℝ := 1 - (u 0 : ℝ)
  let y : ℝ := 1 - (u 1 : ℝ)
  let m : ℝ := max x y
  have hx : 0 ≤ x := by dsimp [x]; linarith [(u 0).property.2]
  have hy : 0 ≤ y := by dsimp [y]; linarith [(u 1).property.2]
  have hmax : m = 1 - min (u 0 : ℝ) (u 1 : ℝ) := by
    dsimp [m, x, y]
    rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
    · rw [min_eq_right h, max_eq_right (by linarith)]
  have hq : Tendsto (fun a => (2 : ℝ) ^ (θ a)⁻¹) l (𝓝 1) := by
    have hi := tendsto_inv_atTop_zero.comp hlim
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : α => (2 : ℝ)) l (𝓝 2)).rpow hi
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have hlow : Tendsto (fun a => max (0 : ℝ) (1 - (2 : ℝ) ^ (θ a)⁻¹ * m)) l
      (𝓝 (min (u 0 : ℝ) (u 1 : ℝ))) := by
    have hc : Continuous (fun q : ℝ => max (0 : ℝ) (1 - q * m)) := by fun_prop
    have ht := hc.continuousAt.tendsto.comp hq
    have hmin0 : 0 ≤ min (u 0 : ℝ) (u 1 : ℝ) :=
      le_min (u 0).property.1 (u 1).property.1
    have he : max (0 : ℝ) (1 - 1 * m) = min (u 0 : ℝ) (u 1 : ℝ) := by
      rw [hmax]
      simp only [one_mul]
      rw [max_eq_right (by linarith : 0 ≤ 1 - (1 - min (u 0 : ℝ) (u 1 : ℝ)))]
      ring
    simpa only [Function.comp_def, he] using ht
  rw [cdf_comonotonic_two]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro a
    have hn := twoTermPowerNorm_le (θ a) x y (by linarith [hθ a]) hx hy
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    change max (0 : ℝ) (1 - (2 : ℝ) ^ (θ a)⁻¹ * m) ≤ (nelsen2 (θ a) (hθ a)).cdf u
    rw [hz, nelsen2_cdf_full]
    simp only [hu, hv, or_self, ↓reduceIte]
    exact max_le_max le_rfl (by dsimp [x, y, m] at hn ⊢; linarith)
  · intro a
    exact le_min ((nelsen2 (θ a) (hθ a)).cdf_le_coord u 0)
      ((nelsen2 (θ a) (hθ a)).cdf_le_coord u 1)end ProbabilityTheory.Copula