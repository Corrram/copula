/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Basic
import Copula.Rank.Integration
import Copula.Order.Orthant
import Copula.Dependence.Basic

/-! # Order and limits of the Plackett family

For the Plackett copulas `C_θ` (`Copula.Families.Plackett.Basic`; Nelsen 2006, §3.3.1):

* the family is positively ordered: `θ ≤ θ'` implies `C_θ ≤ C_θ'` pointwise
  (`plackett_lowerOrthantLE`); the proof only uses the cross-product ratio equation and the
  Fréchet–Hoeffding bounds. Consequently `C_θ` is PQD for `θ ≥ 1` and NQD for `θ ≤ 1`;
* quantitative Fréchet–Hoeffding limits: `0 ≤ M(u,v) - C_θ(u,v) ≤ 1/√θ` and
  `0 ≤ C_θ(u,v) - W(u,v) ≤ √θ`, hence `C_θ → M` as `θ → ∞` and `C_θ → W` as `θ → 0⁺`
  (`tendsto_plackettCDF_atTop`, `tendsto_plackettCDF_zero`);
* Blomqvist's beta `(√θ - 1)/(√θ + 1)` is strictly increasing in `θ`.
-/

open Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The Fréchet–Hoeffding bounds for the Plackett formula on the unit square. -/
theorem plackettCDF_bounds {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    0 ≤ plackettCDF θ u v ∧ (u : ℝ) + v - 1 ≤ plackettCDF θ u v ∧
      plackettCDF θ u v ≤ u ∧ plackettCDF θ u v ≤ v := by
  have hW := (plackett θ hθ).cdf_countermonotonic_le ![u, v]
  have hM := (plackett θ hθ).cdf_le_comonotonic ![u, v]
  rw [cdf_countermonotonic, cdf_plackett_two] at hW
  rw [cdf_comonotonic_two, cdf_plackett_two] at hM
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, max_le_iff,
    le_min_iff] at hW hM
  exact ⟨hW.1, hW.2, hM.1, hM.2⟩

/-- The cross-product ratio equation for the Plackett formula. -/
theorem plackettCDF_cross_ratio {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    plackettCDF θ u v * (1 - u - v + plackettCDF θ u v) =
      θ * (u - plackettCDF θ u v) * (v - plackettCDF θ u v) := by
  have h := plackett_cross_ratio θ hθ u v
  rwa [cdf_plackett_two] at h

/-- The Plackett formula is nondecreasing in the parameter. -/
theorem plackettCDF_mono {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ ≤ θ') (u v : I) :
    plackettCDF θ u v ≤ plackettCDF θ' u v := by
  have hθ' : 0 < θ' := hθ.trans_le hθθ'
  rcases hθθ'.eq_or_lt with h | h
  · rw [h]
  obtain ⟨h0, hW, hu, hv⟩ := plackettCDF_bounds hθ u v
  obtain ⟨h0', hW', hu', hv'⟩ := plackettCDF_bounds hθ' u v
  have E := plackettCDF_cross_ratio hθ u v
  have E' := plackettCDF_cross_ratio hθ' u v
  set c := plackettCDF θ u v
  set c' := plackettCDF θ' u v
  by_contra! hlt
  have h1 : 0 < (u : ℝ) - c' := by linarith
  have h2 : 0 < (v : ℝ) - c' := by linarith
  nlinarith [mul_pos (sub_pos.mpr h) (mul_pos h1 h2),
    mul_nonneg (mul_nonneg hθ.le (sub_pos.mpr hlt).le) (by linarith : (0 : ℝ) ≤ u + v - c - c'),
    mul_nonneg (sub_pos.mpr hlt).le (by linarith : (0 : ℝ) ≤ 1 - u - v + c + c')]

/-- The Plackett family is positively ordered (Nelsen 2006, §3.3.1). -/
theorem plackett_lowerOrthantLE {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (hθθ' : θ ≤ θ') :
    (plackett θ hθ).LowerOrthantLE (plackett θ' hθ') := by
  intro u
  simp only [cdf_plackett]
  exact plackettCDF_mono hθ hθθ' (u 0) (u 1)

/-- `C_θ` is positively quadrant dependent for `θ ≥ 1`. -/
theorem isPQD_plackett {θ : ℝ} (hθ : 0 < θ) (h1 : 1 ≤ θ) : (plackett θ hθ).IsPQD := by
  intro u v
  have h := plackettCDF_mono one_pos h1 u v
  rw [cdf_plackett_two]
  simpa [plackettCDF] using h

/-- `C_θ` is negatively quadrant dependent for `θ ≤ 1`. -/
theorem isNQD_plackett {θ : ℝ} (hθ : 0 < θ) (h1 : θ ≤ 1) : (plackett θ hθ).IsNQD := by
  intro u v
  have h := plackettCDF_mono hθ h1 u v
  rw [cdf_plackett_two]
  simpa [plackettCDF] using h

/-- Quantitative convergence to the upper Fréchet–Hoeffding bound:
`0 ≤ min(u,v) - C_θ(u,v) ≤ 1/√θ`. -/
theorem min_sub_plackettCDF_le {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    0 ≤ min (u : ℝ) v - plackettCDF θ u v ∧ min (u : ℝ) v - plackettCDF θ u v ≤ 1 / √θ := by
  obtain ⟨h0, hW, hu, hv⟩ := plackettCDF_bounds hθ u v
  have E := plackettCDF_cross_ratio hθ u v
  set c := plackettCDF θ u v
  have hm0 : 0 ≤ min (u : ℝ) v - c := sub_nonneg.mpr (le_min hu hv)
  refine ⟨hm0, ?_⟩
  have hmu : min (u : ℝ) v ≤ u := min_le_left _ _
  have hmv : min (u : ℝ) v ≤ v := min_le_right _ _
  have hc1 : c ≤ 1 := hu.trans u.2.2
  have hsq : θ * (min (u : ℝ) v - c) ^ 2 ≤ 1 := by
    have hprod : (min (u : ℝ) v - c) ^ 2 ≤ (u - c) * (v - c) := by
      rw [sq]; exact mul_le_mul (by linarith) (by linarith) hm0 (by linarith)
    have hg : c * (1 - u - v + c) ≤ 1 := by
      have : 1 - (u : ℝ) - v + c ≤ 1 := by linarith [v.2.1]
      nlinarith [v.2.2]
    nlinarith [mul_le_mul_of_nonneg_left hprod hθ.le]
  have hs : 0 < √θ := Real.sqrt_pos.mpr hθ
  rw [le_div_iff₀ hs]
  have hss : √θ ^ 2 = θ := Real.sq_sqrt hθ.le
  nlinarith [sq_nonneg ((min (u : ℝ) v - c) * √θ - 1), mul_nonneg hm0 hs.le]

/-- Quantitative convergence to the lower Fréchet–Hoeffding bound:
`0 ≤ C_θ(u,v) - max(0, u + v - 1) ≤ √θ`. -/
theorem plackettCDF_sub_max_le {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    0 ≤ plackettCDF θ u v - max 0 ((u : ℝ) + v - 1) ∧
      plackettCDF θ u v - max 0 ((u : ℝ) + v - 1) ≤ √θ := by
  obtain ⟨h0, hW, hu, hv⟩ := plackettCDF_bounds hθ u v
  have E := plackettCDF_cross_ratio hθ u v
  set c := plackettCDF θ u v
  have hm0 : 0 ≤ c - max 0 ((u : ℝ) + v - 1) := sub_nonneg.mpr (max_le h0 hW)
  refine ⟨hm0, ?_⟩
  have hsq : (c - max 0 ((u : ℝ) + v - 1)) ^ 2 ≤ θ := by
    have hle : (c - max 0 ((u : ℝ) + v - 1)) ^ 2 ≤ c * (1 - u - v + c) := by
      rcases le_total ((u : ℝ) + v - 1) 0 with h | h
      · rw [max_eq_left h]; nlinarith
      · rw [max_eq_right h]; nlinarith
    have hr : (u - c) * (v - c) ≤ 1 := by
      nlinarith [mul_le_mul (by linarith [u.2.2, h0] : (u : ℝ) - c ≤ 1)
        (by linarith [v.2.2, h0] : (v : ℝ) - c ≤ 1) (by linarith) zero_le_one]
    nlinarith [mul_le_mul_of_nonneg_left hr hθ.le]
  calc c - max 0 ((u : ℝ) + v - 1) = √((c - max 0 ((u : ℝ) + v - 1)) ^ 2) :=
        (Real.sqrt_sq hm0).symm
    _ ≤ √θ := Real.sqrt_le_sqrt hsq

/-- `C_θ → M` pointwise as `θ → ∞` (Nelsen 2006, §3.3.1). -/
theorem tendsto_plackettCDF_atTop (u v : I) :
    Tendsto (fun θ => plackettCDF θ u v) atTop (𝓝 ((comonotonic 2).cdf ![u, v])) := by
  rw [cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hlim : Tendsto (fun θ : ℝ => min (u : ℝ) v - 1 / √θ) atTop (𝓝 (min (u : ℝ) v)) := by
    have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_sub (min (u : ℝ) v)
    simpa [Function.comp_def] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    linarith [(min_sub_plackettCDF_le hθ u v).2]
  · filter_upwards [eventually_gt_atTop 0] with θ hθ
    linarith [(min_sub_plackettCDF_le hθ u v).1]

/-- `C_θ → W` pointwise as `θ → 0⁺` (Nelsen 2006, §3.3.1). -/
theorem tendsto_plackettCDF_zero (u v : I) :
    Tendsto (fun θ => plackettCDF θ u v) (𝓝[>] 0) (𝓝 (countermonotonic.cdf ![u, v])) := by
  rw [cdf_countermonotonic]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hs : Tendsto (fun θ : ℝ => √θ) (𝓝[>] 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun θ : ℝ => max 0 ((u : ℝ) + v - 1) + √θ) (𝓝[>] 0)
      (𝓝 (max 0 ((u : ℝ) + v - 1))) := by
    simpa using hs.const_add (max 0 ((u : ℝ) + v - 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    linarith [(plackettCDF_sub_max_le (show 0 < θ from hθ) u v).1]
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    linarith [(plackettCDF_sub_max_le (show 0 < θ from hθ) u v).2]

/-- Blomqvist's beta of the Plackett copula is strictly increasing in `θ`. -/
theorem blomqvistBeta_plackett_strictMono {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ')
    (h : θ < θ') : (plackett θ hθ).blomqvistBeta < (plackett θ' hθ').blomqvistBeta := by
  rw [blomqvistBeta_plackett, blomqvistBeta_plackett]
  have hs : 0 ≤ √θ := Real.sqrt_nonneg θ
  have hss : √θ < √θ' := Real.sqrt_lt_sqrt hθ.le h
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end ProbabilityTheory.Copula
