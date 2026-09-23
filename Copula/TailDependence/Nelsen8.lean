/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen8
import Copula.TailDependence.Basic

/-! # Exact Nelsen 8 tail dependence

Both tail coefficients vanish for every finite θ ≥ 1, including the
countermonotonic endpoint θ = 1.
-/

open Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem n8_upper_ratio (θ : ℝ) (hθ : 1 ≤ θ) (t : I)
    (ht0 : 0 < (t : ℝ)) (ht : (t : ℝ) ≤ 1 / 2) :
    (nelsen8 θ hθ).upperTailRatio t =
      2 * (t : ℝ) * (θ*(θ-1) - (θ-1)^2*(t : ℝ)) /
        (θ^2-(θ-1)^2*(t : ℝ)^2) := by
  have hsymm : unitInterval.symm t ≠ 0 := by
    intro hz
    have h := congrArg (fun x : I => (x : ℝ)) hz
    simp only [unitInterval.coe_symm_eq] at h
    norm_num at h
    linarith
  have hx : 0 ≤ 1 - (t : ℝ) := by linarith
  have hθ2 : 1 ≤ θ^2 := by nlinarith
  have hsq : (t : ℝ)^2 ≤ (1-(t : ℝ))^2 := by nlinarith
  have hn : 0 ≤ θ^2*(1-(t : ℝ))^2 - (t : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ2) (sq_nonneg (1-(t : ℝ)))]
  have hd : 0 < θ^2-(θ-1)^2*(t : ℝ)^2 := by
    have hθk : 0 ≤ θ-1 := by linarith
    have hmul : (θ-1)^2*(t : ℝ)^2 ≤ (θ-1)^2 := by
      have ht2 : (t : ℝ)^2 ≤ 1 := by nlinarith [sq_nonneg (t : ℝ)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left ht2 (sq_nonneg (θ-1))
    nlinarith
  have hq : 0 ≤ (θ^2*(1-(t : ℝ))^2 - (t : ℝ)^2) /
      (θ^2-(θ-1)^2*(t : ℝ)^2) := div_nonneg hn hd.le
  rw [upperTailRatio_eq, diagonal, nelsen8_cdf_full]
  simp only [unitInterval.coe_symm_eq]
  rw [show 1 - (1 - (t : ℝ)) = (t : ℝ) by ring]
  have hqeq : (θ^2*(1-(t : ℝ))*(1-(t : ℝ)) - (t : ℝ)*(t : ℝ)) /
      (θ^2-(θ-1)^2*(t : ℝ)*(t : ℝ)) =
      (θ^2*(1-(t : ℝ))^2 - (t : ℝ)^2) /
      (θ^2-(θ-1)^2*(t : ℝ)^2) := by congr 1 <;> ring
  rw [hqeq, max_eq_right hq]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  have hdpoly : - (t : ℝ)^2 + (t : ℝ)^2 * θ * 2 -
      (t : ℝ)^2 * θ^2 + θ^2 ≠ 0 := by
    convert (ne_of_gt hd) using 1; ring
  field_simp [hne]
  ring_nf
  nlinarith [mul_inv_cancel₀ hdpoly]

/-- The Nelsen 8 upper-tail coefficient vanishes for all admissible parameters. -/
theorem hasUpperTailDependence_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).HasUpperTailDependence 0 := by
  let f : I → ℝ := fun t =>
    2 * (t : ℝ) * (θ*(θ-1) - (θ-1)^2*(t : ℝ)) /
      (θ^2-(θ-1)^2*(t : ℝ)^2)
  have hden : θ^2 ≠ 0 := by nlinarith
  have hcont : ContinuousAt f (0 : I) := by
    dsimp [f]
    apply ContinuousAt.div₀
    · fun_prop
    · fun_prop
    · simpa using hden
  have hval : f 0 = 0 := by simp [f]
  have hlim : Tendsto f (𝓝[>] (0 : I)) (𝓝 0) := by
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hco : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) :=
    (continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : I in 𝓝[>] (0 : I), (t : ℝ) < 1 / 2 :=
    hco.eventually (eventually_lt_nhds (by norm_num))
  have hpos : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < (t : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (nelsen8 θ hθ).upperTailRatio t = f t := by
    filter_upwards [hsmall, hpos] with t ht hp
    exact n8_upper_ratio θ hθ t hp (le_of_lt ht)
  exact hlim.congr' (heq.mono fun t ht => ht.symm)

/-- The Nelsen 8 lower-tail coefficient vanishes for all admissible parameters. -/
theorem hasLowerTailDependence_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).HasLowerTailDependence 0 := by
  let f : I → ℝ := fun t =>
    (θ^2*(t : ℝ)*(t : ℝ) - (1-(t : ℝ))*(1-(t : ℝ))) /
      (θ^2-(θ-1)^2*(1-(t : ℝ))*(1-(t : ℝ)))
  have hd0 : 0 < θ^2-(θ-1)^2 := by nlinarith
  have hval : f 0 < 0 := by
    dsimp [f]
    norm_num
    exact div_neg_of_neg_of_pos (by norm_num) hd0
  have hcont : ContinuousAt f (0 : I) := by
    dsimp [f]
    apply ContinuousAt.div₀
    · fun_prop
    · fun_prop
    · simpa using (ne_of_gt hd0)
  have hlim : Tendsto f (𝓝[>] (0 : I)) (𝓝 (f 0)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : I in 𝓝[>] (0 : I), f t < 0 :=
    hlim.eventually (eventually_lt_nhds hval)
  have heq : ∀ᶠ t : I in 𝓝[>] (0 : I),
      (nelsen8 θ hθ).lowerTailRatio t = 0 := by
    filter_upwards [hneg, self_mem_nhdsWithin] with t ht ht0
    have htn : t ≠ 0 := ne_of_gt ht0
    simp only [lowerTailRatio, diagonal, nelsen8_cdf_full]
    change max 0 (f t) / (t : ℝ) = 0
    rw [max_eq_left (le_of_lt ht)]
    simp
  exact tendsto_const_nhds.congr' (heq.mono fun t ht => ht.symm)
end ProbabilityTheory.Copula
