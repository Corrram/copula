/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Layercake
import Copula.Rank.Region.Common.StochasticRho
import Copula.Rank.Integration
import Copula.Families.Nelsen

/-! # Spearman's rho of Nelsen's family 2

Nelsen's family 2 is `C(u, v) = max (0, 1 - ((1-u)^θ + (1-v)^θ)^(1/θ))`, `θ ≥ 1`. Writing
`x = 1-u`, `y = 1-v`, we have `C = (1 - ‖(x, y)‖_θ)₊`, the *cone* over the `ℓ^θ` unit ball
(`SpearmanNelsen2.cone`). By the layer-cake formula and the volume of the `ℓ^θ` unit ball of the
plane (Mathlib: `MeasureTheory.volume_sum_rpow_lt`) the integral of the cone over the plane is
`V / 3` with `V = (2 Γ(1 + 1/θ))² / Γ(1 + 2/θ)`; by symmetry the quadrant carries a quarter of
it, so `∬ C = V / 12` and

`ρ = 4 Γ(1 + 1/θ)² / Γ(1 + 2/θ) - 3`   (`spearmanRho_nelsen2`).

For `θ = 1` this is `-1` (the copula is `W`), and `ρ → 1` as `θ → ∞`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace SpearmanNelsen2

/-- The cone function `max 0 (1 - ‖(a, b)‖_θ)`. -/
noncomputable def cone (θ a b : ℝ) : ℝ := max 0 (1 - (|a| ^ θ + |b| ^ θ) ^ θ⁻¹)

theorem continuous_cone (θ : ℝ) (hθ : 1 ≤ θ) : Continuous (fun z : Fin 2 → ℝ => cone θ (z 0) (z 1)) := by
  unfold cone
  have h0 : (0 : ℝ) < θ := by linarith
  have : Continuous fun z : Fin 2 → ℝ => (|z 0| ^ θ + |z 1| ^ θ) ^ θ⁻¹ := by
    apply Continuous.rpow_const
    · exact ((continuous_abs.comp (continuous_apply 0)).rpow_const (fun _ => Or.inr h0.le)).add
        ((continuous_abs.comp (continuous_apply 1)).rpow_const (fun _ => Or.inr h0.le))
    · intro z; right; exact inv_nonneg.mpr h0.le
  fun_prop

theorem cone_eq_zero (θ : ℝ) (hθ : 1 ≤ θ) {a b : ℝ} (h : 1 ≤ |a| ∨ 1 ≤ |b|) : cone θ a b = 0 := by
  have h0 : (0 : ℝ) < θ := by linarith
  unfold cone
  rw [max_eq_left]
  have key : ∀ x y : ℝ, 1 ≤ |x| → 1 ≤ (|x| ^ θ + |y| ^ θ) ^ θ⁻¹ := by
    intro x y hx
    calc (1 : ℝ) = (1 ^ θ) ^ θ⁻¹ := by rw [Real.one_rpow, Real.one_rpow]
      _ ≤ (|x| ^ θ + |y| ^ θ) ^ θ⁻¹ := by
        apply Real.rpow_le_rpow (by positivity) _ (inv_nonneg.mpr h0.le)
        have := Real.one_le_rpow hx h0.le
        have := Real.rpow_nonneg (abs_nonneg y) θ
        rw [Real.one_rpow]
        linarith
  rcases h with h | h
  · have := key a b h; linarith
  · have := key b a h
    rw [add_comm] at this; linarith


theorem cone_nonneg (θ a b : ℝ) : 0 ≤ cone θ a b := le_max_left _ _

theorem integrable_cone (θ : ℝ) (hθ : 1 ≤ θ) :
    Integrable (fun z : Fin 2 → ℝ => cone θ (z 0) (z 1)) := by
  apply (continuous_cone θ hθ).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro z hz
  apply cone_eq_zero θ hθ
  by_contra hcon
  push Not at hcon
  apply hz
  intro i _
  fin_cases i
  · exact abs_le.mp hcon.1.le
  · exact abs_le.mp hcon.2.le

/-- The volume of the level sets of the cone function. -/
theorem measure_lt_cone (θ : ℝ) (hθ : 1 ≤ θ) {t : ℝ} (ht : 0 < t) :
    volume {z : Fin 2 → ℝ | t < cone θ (z 0) (z 1)} =
      ENNReal.ofReal (1 - t) ^ 2 * ENNReal.ofReal ((2 * Real.Gamma (θ⁻¹ + 1)) ^ 2 /
        Real.Gamma (2 / θ + 1)) := by
  have h := volume_sum_rpow_lt (Fin 2) hθ (1 - t)
  simp only [Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_two] at h
  simp only [one_div] at h
  rw [← h]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, cone, lt_max_iff]
  constructor
  · rintro (hz | hz)
    · exact absurd hz (not_lt.mpr ht.le)
    · linarith
  · intro hz
    right
    linarith

theorem integral_Ioi_max_sq : (∫ t in Ioi (0 : ℝ), (max (1 - t) 0) ^ 2) = 1 / 3 := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc (0 : ℝ) 1) measurableSet_Ioi
    Ioc_subset_Ioi_self]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    have h1 : (∫ t in (0 : ℝ)..1, (max (1 - t) 0) ^ 2) = ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [max_eq_left (sub_nonneg.mpr ht.2)]
    rw [h1]
    have h2 := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) (a := 0) (b := 1) 1
    simp only [sub_self, sub_zero] at h2
    rw [h2, integral_pow]
    norm_num
  · intro t ht
    have : 1 < t := by
      by_contra h
      exact ht.2 ⟨ht.1, not_lt.mp h⟩
    simp only [max_eq_right (by linarith : 1 - t ≤ 0)]
    norm_num

/-- The integral of the cone function over the plane. -/
theorem integral_cone (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ z : Fin 2 → ℝ, cone θ (z 0) (z 1)) =
      (2 * Real.Gamma (θ⁻¹ + 1)) ^ 2 / Real.Gamma (2 / θ + 1) / 3 := by
  have h0 : (0 : ℝ) < θ := by linarith
  rw [(integrable_cone θ hθ).integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall fun z => cone_nonneg θ _ _)]
  have hV : 0 ≤ (2 * Real.Gamma (θ⁻¹ + 1)) ^ 2 / Real.Gamma (2 / θ + 1) :=
    div_nonneg (sq_nonneg _) (Real.Gamma_pos_of_pos (by positivity)).le
  have h : ∀ t ∈ Ioi (0 : ℝ), volume.real {z : Fin 2 → ℝ | t < cone θ (z 0) (z 1)} =
      (max (1 - t) 0) ^ 2 * ((2 * Real.Gamma (θ⁻¹ + 1)) ^ 2 / Real.Gamma (2 / θ + 1)) := by
    intro t ht
    rw [Measure.real, measure_lt_cone θ hθ ht, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal' , ENNReal.toReal_ofReal hV]
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_mul_const, integral_Ioi_max_sq]
  ring

theorem cone_abs_left (θ a b : ℝ) : cone θ |a| b = cone θ a b := by simp [cone]

theorem cone_abs_right (θ a b : ℝ) : cone θ a |b| = cone θ a b := by simp [cone]

/-- Reduction of the plane integral of the cone function to the positive quadrant. -/
theorem integral_cone_eq_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ z : Fin 2 → ℝ, cone θ (z 0) (z 1)) =
      4 * ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), cone θ x y := by
  have hm := volume_preserving_finTwoArrow ℝ
  have hi : Integrable (fun p : ℝ × ℝ => cone θ p.1 p.2) volume :=
    (hm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mp (integrable_cone θ hθ)
  have e1 : (∫ z : Fin 2 → ℝ, cone θ (z 0) (z 1)) = ∫ p : ℝ × ℝ, cone θ p.1 p.2 :=
    hm.integral_comp' (g := fun p : ℝ × ℝ => cone θ p.1 p.2)
  rw [e1, Measure.volume_eq_prod, integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  have e2 : ∀ x : ℝ, (∫ y : ℝ, cone θ x y) = 2 * ∫ y in Ioi (0 : ℝ), cone θ x y := by
    intro x
    rw [← integral_comp_abs (f := fun y => cone θ x y)]
    simp_rw [cone_abs_right]
  simp_rw [e2]
  rw [integral_const_mul]
  have e3 := integral_comp_abs (f := fun x => ∫ y in Ioi (0 : ℝ), cone θ x y)
  simp_rw [cone_abs_left] at e3
  rw [e3]
  ring

/-- Reflection of the unit interval and extension by zero to the positive half-line. -/
theorem integral_unit_one_sub (g : ℝ → ℝ) (hg : ∀ t, 1 ≤ t → g t = 0) :
    (∫ t : I, g (1 - (t : ℝ))) = ∫ t in Ioi (0 : ℝ), g t := by
  rw [integral_unitInterval (fun t : ℝ => g (1 - t))]
  have h := intervalIntegral.integral_comp_sub_left g (a := 0) (b := 1) 1
  simp only [sub_self, sub_zero] at h
  rw [h, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc (0 : ℝ) 1) measurableSet_Ioi
      Ioc_subset_Ioi_self]
  intro t ht
  have h1 : 1 < t := by
    by_contra h
    exact ht.2 ⟨ht.1, not_lt.mp h⟩
  exact hg t h1.le

theorem cone_comm (θ a b : ℝ) : cone θ a b = cone θ b a := by
  simp only [cone, add_comm]

theorem cdf_nelsen2_eq_cone (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen2 θ hθ).cdf ![u, v] = cone θ (1 - (u : ℝ)) (1 - (v : ℝ)) := by
  rw [nelsen2_cdf_full]
  have hu := u.property
  have hv := v.property
  by_cases h : u = 0 ∨ v = 0
  · simp only [h, ↓reduceIte]
    symm
    apply cone_eq_zero θ hθ
    rcases h with h | h
    · left
      rw [h]; simp
    · right
      rw [h]; simp
  · simp only [h, ↓reduceIte]
    simp only [cone, abs_of_nonneg (sub_nonneg.mpr hu.2), abs_of_nonneg (sub_nonneg.mpr hv.2)]

end SpearmanNelsen2

open SpearmanNelsen2 in
/-- Spearman's rho of Nelsen's family 2 (`θ ≥ 1`):
`ρ = 4 Γ(1 + 1/θ)² / Γ(1 + 2/θ) - 3`. -/
theorem spearmanRho_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen2 θ hθ).spearmanRho =
      4 * Real.Gamma (θ⁻¹ + 1) ^ 2 / Real.Gamma (2 / θ + 1) - 3 := by
  rw [RankRegion.Common.spearmanRho_eq_iterated_cdf]
  have hcone : ∀ x : ℝ, 1 ≤ x → ∀ y : ℝ, cone θ x y = 0 := fun x hx y =>
    cone_eq_zero θ hθ (Or.inl (by rwa [abs_of_nonneg (by linarith)]))
  have hcone' : ∀ y : ℝ, 1 ≤ y → ∀ x : ℝ, cone θ x y = 0 := fun y hy x =>
    cone_eq_zero θ hθ (Or.inr (by rwa [abs_of_nonneg (by linarith)]))
  have e1 : ∀ v : I, (∫ u : I, (nelsen2 θ hθ).cdf ![u, v]) =
      ∫ x in Ioi (0 : ℝ), cone θ x (1 - (v : ℝ)) := by
    intro v
    simp_rw [cdf_nelsen2_eq_cone]
    exact integral_unit_one_sub (fun x => cone θ x (1 - (v : ℝ))) (fun t ht => hcone t ht _)
  simp_rw [e1]
  rw [integral_unit_one_sub (fun y => ∫ x in Ioi (0 : ℝ), cone θ x y)
    (fun t ht => by simp [hcone' t ht])]
  have hq := integral_cone_eq_quadrant θ hθ
  rw [integral_cone θ hθ] at hq
  have hq' : (∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), cone θ x y) =
      ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), cone θ x y := by
    simp_rw [cone_comm θ _ _]
  rw [hq']
  have : (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), cone θ x y) =
      (2 * Real.Gamma (θ⁻¹ + 1)) ^ 2 / Real.Gamma (2 / θ + 1) / 12 := by
    linarith
  rw [this]
  ring

end ProbabilityTheory.Copula
