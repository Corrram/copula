/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.Boundary
import Mathlib.Analysis.SpecificLimits.Basic

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

theorem continuous_gammaValue {X : Type*} [TopologicalSpace X] {s c m : X → ℝ}
    (hs : Continuous s) (hc : Continuous c) (hm : Continuous m) (hpos : ∀ x, 0 < s x) :
    Continuous (fun x => gammaValue (s x) (c x) (m x)) := by
  have hA : Continuous (fun x => splitRatio (s x) (c x)) := by
    unfold splitRatio
    fun_prop
  have hd : ∀ x, 1 + splitRatio (s x) (c x) ≠ 0 := by
    intro x
    unfold splitRatio
    have hh := Real.sqrt_nonneg ((s x) ^ 2 + 2 * c x)
    linarith only [hh, hpos x]
  have ha : Continuous (fun x => centralLength (s x) (c x)) :=
    hA.div (continuous_const.add hA) hd
  have hz : Continuous (fun x => cornerLength (s x) (c x)) :=
    continuous_const.div (continuous_const.add hA) hd
  unfold gammaValue
  fun_prop

open RhoFootrule.UpperSpline

noncomputable def contactGamma (N : ℕ) : ℝ :=
  gammaValue (1 / (N : ℝ)) (-(1 / (8 * (N : ℝ) ^ 2))) (1 / (2 * (N : ℝ)))

theorem left_zero (N : ℕ) (hN : 0 < N) :
    (UpperParameter.left (RhoFootrule.leftFamily N hN 0)).gamma = contactGamma N := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  dsimp [UpperParameter.gamma, RhoFootrule.leftFamily, period, offset, contactGamma]
  norm_num
  congr 1 <;> field_simp
  all_goals norm_num

theorem right_zero (N : ℕ) (hN : 0 < N) :
    (UpperParameter.right (RhoFootrule.rightFamily N hN 0)).gamma = contactGamma (N + 1) := by
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp [UpperParameter.gamma, RhoFootrule.rightFamily, period, offset, contactGamma]
  norm_num
  congr 1 <;> field_simp
  all_goals norm_num

theorem middle_join (N : ℕ) (hN : 0 < N) :
    (UpperParameter.left (RhoFootrule.leftFamily N hN 1)).gamma =
      (UpperParameter.right (RhoFootrule.rightFamily N hN 1)).gamma := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp [UpperParameter.gamma, RhoFootrule.leftFamily, RhoFootrule.rightFamily, period, offset]
  norm_num
  congr 1
  field_simp
  ring

theorem continuous_right_gamma (N : ℕ) (hN : 0 < N) :
    Continuous (fun u : I => (UpperParameter.right (RhoFootrule.rightFamily N hN u)).gamma) := by
  apply continuous_gammaValue
  · dsimp [RhoFootrule.rightFamily, period]; fun_prop
  · dsimp [RhoFootrule.rightFamily, offset]; fun_prop
  · dsimp [RhoFootrule.rightFamily]; fun_prop
  · intro u; exact (RhoFootrule.rightFamily N hN u).period_pos

theorem continuous_left_gamma (N : ℕ) (hN : 0 < N) :
    Continuous (fun u : I => (UpperParameter.left (RhoFootrule.leftFamily N hN u)).gamma) := by
  apply continuous_gammaValue
  · dsimp [RhoFootrule.leftFamily, period]; fun_prop
  · dsimp [RhoFootrule.leftFamily, offset]; fun_prop
  · dsimp [RhoFootrule.leftFamily]; fun_prop
  · intro u; exact (RhoFootrule.leftFamily N hN u).period_pos

theorem between_contacts {g : ℝ} (N : ℕ) (hN : 0 < N)
    (hlo : contactGamma N ≤ g) (hhi : g ≤ contactGamma (N + 1)) :
    ∃ p : UpperParameter, p.gamma = g := by
  by_cases hm : g ≤ (UpperParameter.left (RhoFootrule.leftFamily N hN 1)).gamma
  · obtain ⟨u, hu⟩ := exists_unitInterval_eq (continuous_left_gamma N hN)
      (by simpa only [left_zero] using hlo) hm
    exact ⟨.left (RhoFootrule.leftFamily N hN u), hu⟩
  · obtain ⟨u, hu⟩ := exists_unitInterval_eq
      ((continuous_right_gamma N hN).comp unitInterval.continuous_symm)
      (by simpa only [Function.comp_apply, unitInterval.symm_zero, ← middle_join] using le_of_not_ge hm)
      (by simpa only [Function.comp_apply, unitInterval.symm_one, right_zero] using hhi)
    exact ⟨.right (RhoFootrule.rightFamily N hN (unitInterval.symm u)), hu⟩


theorem cornerLength_le_two_div {s : ℝ} (hs : 0 < s) (c : ℝ) :
    cornerLength s c ≤ 2 / s := by
  have hn := Real.sqrt_nonneg (s ^ 2 + 2 * c)
  unfold cornerLength splitRatio
  apply (div_le_div_iff₀ (by linarith) hs).mpr
  linarith

theorem halfShift_near_endpoint {s : ℝ} (hs : 1 ≤ s) :
    gammaValue s (3 / 8 - s / 2) (1 / 2) ≤ -1 + 8 / s := by
  let A := AuxiliaryCertificate.halfShift s hs
  have haz : centralLength s (3 / 8 - s / 2) + cornerLength s (3 / 8 - s / 2) = 1 := A.a_add_z
  have hz := cornerLength_le_two_div (show 0 < s by linarith) (3 / 8 - s / 2)
  have ha : centralLength s (3 / 8 - s / 2) = 1 - cornerLength s (3 / 8 - s / 2) := by linarith
  unfold gammaValue
  rw [ha]
  rw [show 8 / s = 4 * (2 / s) by ring]
  nlinarith only [hz, sq_nonneg (cornerLength s (3 / 8 - s / 2))]

theorem halfShift_join :
    gammaValue 1 (3 / 8 - 1 / 2) (1 / 2) = contactGamma 1 := by
  norm_num [contactGamma]

theorem below_first_contact {g : ℝ} (hg : -1 < g) (hg1 : g ≤ contactGamma 1) :
    ∃ p : UpperParameter, p.gamma = g := by
  let S : ℝ := 1 + 16 / (g + 1)
  have hgpos : 0 < g + 1 := by linarith
  have hS : 1 ≤ S := by
    have hh : 0 ≤ 16 / (g + 1) := by positivity
    dsimp [S]
    linarith
  have hSp : 0 < S := by linarith
  have hsmall : -1 + 8 / S < g := by
    have he : (g + 1) * S = g + 1 + 16 := by dsimp [S]; field_simp
    have hh : 8 / S < g + 1 := (div_lt_iff₀ hSp).mpr (by nlinarith only [he, hgpos])
    linarith
  let scale : I → ℝ := fun u => S + (1 - S) * u
  have hscale (u : I) : 1 ≤ scale u := by
    have hh := mul_nonneg (show 0 ≤ S - 1 by linarith) (sub_nonneg.mpr u.property.2)
    dsimp [scale]
    nlinarith only [hh]
  have hc : Continuous (fun u : I => gammaValue (scale u) (3 / 8 - scale u / 2) (1 / 2)) :=
    continuous_gammaValue (by dsimp [scale]; fun_prop) (by dsimp [scale]; fun_prop)
      continuous_const (fun u => by linarith [hscale u])
  have hend : scale 1 = 1 := by dsimp [scale]; norm_num
  obtain ⟨u, hu⟩ := exists_unitInterval_eq hc
    (by
      have hh := (halfShift_near_endpoint hS).trans hsmall.le
      simpa [scale] using hh)
    (by simpa only [hend, halfShift_join] using hg1)
  exact ⟨.halfShift (scale u) (hscale u), hu⟩

theorem contactGamma_tendsto :
    Filter.Tendsto contactGamma Filter.atTop (nhds 1) := by
  have hA : ContinuousAt (fun r : ℝ => splitRatio r (-(r ^ 2) / 8)) 0 := by
    unfold splitRatio
    fun_prop
  have hd : 1 + splitRatio 0 (-(0 ^ 2) / 8) ≠ 0 := by norm_num [splitRatio]
  have ha : ContinuousAt (fun r : ℝ => centralLength r (-(r ^ 2) / 8)) 0 :=
    hA.div (continuousAt_const.add hA) hd
  have hz : ContinuousAt (fun r : ℝ => cornerLength r (-(r ^ 2) / 8)) 0 :=
    continuousAt_const.div (continuousAt_const.add hA) hd
  have hG : ContinuousAt (fun r : ℝ => gammaValue r (-(r ^ 2) / 8) (r / 2)) 0 := by
    unfold gammaValue
    fun_prop
  have hh := hG.tendsto.comp (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he (N : ℕ) : contactGamma N = gammaValue (1 / (N : ℝ)) (-((1 / (N : ℝ)) ^ 2) / 8) ((1 / (N : ℝ)) / 2) := by
    unfold contactGamma
    congr 1 <;> simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
    all_goals ring
  simp only [Function.comp_def] at hh
  simp_rw [← he] at hh
  simpa [gammaValue, centralLength, cornerLength, splitRatio] using hh

theorem through_contacts (N : ℕ) (hN : 0 < N) {g : ℝ}
    (hg : -1 < g) (hhi : g ≤ contactGamma N) :
    ∃ p : UpperParameter, p.gamma = g := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hN0 : N = 0
    · subst N
      exact below_first_contact hg hhi
    · by_cases hlo : g ≤ contactGamma N
      · exact ih (by omega) hlo
      · exact between_contacts N (by omega) (le_of_not_ge hlo) hhi

theorem upperParameter_exists {g : ℝ} (hg : g ∈ Set.Icc (-1) 1) :
    ∃ p : UpperParameter, p.gamma = g := by
  by_cases hgm : g = -1
  · exact ⟨.lowerEndpoint, hgm.symm⟩
  by_cases hgp : g = 1
  · exact ⟨.upperEndpoint, hgp.symm⟩
  have hgl : -1 < g := lt_of_le_of_ne hg.1 (Ne.symm hgm)
  have hgu : g < 1 := lt_of_le_of_ne hg.2 hgp
  have he : ∀ᶠ N : ℕ in Filter.atTop, g < contactGamma N :=
    contactGamma_tendsto.eventually (lt_mem_nhds hgu)
  obtain ⟨N, hN, hh⟩ := (he.and (Filter.eventually_gt_atTop 0)).exists
  exact through_contacts N hh hgl hN.le

end ProbabilityTheory.Copula.RankRegion.RhoGamma
