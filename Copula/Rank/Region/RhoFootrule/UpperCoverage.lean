/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperRightOptimal
import Copula.Rank.Region.RhoFootrule.UpperLeftOptimal

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule

/-- A complete, countable collection of explicitly polynomial upper-boundary arcs. -/
inductive UpperParameter
  | endpoint
  | right (data : RightData)
  | left (data : LeftData)

namespace UpperParameter

noncomputable def footrule : UpperParameter → ℝ
  | .endpoint => 1
  | .right S => 1 - 3 * (S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2)
  | .left S => 1 - 3 * (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2)

noncomputable def rho : UpperParameter → ℝ
  | .endpoint => 1
  | .right S => 1 - 6 * ((S.w + S.N * S.v) ^ 2 +
      2 * S.N * (S.N + 1) * (S.w + S.N * S.v) * S.v ^ 2 +
      2 / 3 * S.N * (S.N + 1) * S.v ^ 3)
  | .left S => 1 - 6 * ((S.w + (S.N + 1) * S.v) ^ 2 -
      2 * S.N * (S.N + 1) * (S.w + (S.N + 1) * S.v) * S.v ^ 2 +
      2 / 3 * S.N * (S.N + 1) * S.v ^ 3)

noncomputable def copula : UpperParameter → Copula 2
  | .endpoint => comonotonic 2
  | .right S => S.copula
  | .left S => S.copula

theorem coefficients (a : UpperParameter) :
    a.copula.spearmanFootrule = a.footrule ∧ a.copula.spearmanRho = a.rho := by
  cases a with
  | endpoint => exact ⟨spearmanFootrule_comonotonic, spearmanRho_comonotonic⟩
  | right S => exact ⟨S.footrule, S.rho⟩
  | left S => exact ⟨S.footrule, S.rho⟩

theorem maximizes (a : UpperParameter) (C : Copula 2) (h : C.spearmanFootrule = a.footrule) :
    C.spearmanRho ≤ a.rho := by
  cases a with
  | endpoint => exact C.spearmanRho_mem_Icc.2
  | right S =>
    rw [← (coefficients (.right S)).2]
    exact S.maximizes_rho C (h.trans (coefficients (.right S)).1.symm)
  | left S =>
    rw [← (coefficients (.left S)).2]
    exact S.maximizes_rho C (h.trans (coefficients (.left S)).1.symm)

end UpperParameter

noncomputable def rightFamily (N : ℕ) (hN : 0 < N) (s : I) : RightData where
  N := N
  N_pos := hN
  v := (s : ℝ) / (2 * N * (N + 1))
  w := (1 - (s : ℝ)) / (2 * (N + 1))
  v_nonneg := div_nonneg s.property.1 (by positivity)
  w_nonneg := div_nonneg (sub_nonneg.mpr s.property.2) (by positivity)
  normalized := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

noncomputable def leftFamily (N : ℕ) (hN : 0 < N) (s : I) : LeftData where
  N := N
  N_pos := hN
  v := (s : ℝ) / (2 * N * (N + 1))
  w := (1 - (s : ℝ)) / (2 * N)
  v_nonneg := div_nonneg s.property.1 (by positivity)
  w_nonneg := div_nonneg (sub_nonneg.mpr s.property.2) (by positivity)
  normalized := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem rightFamily_footrule (N : ℕ) (hN : 0 < N) (s : I) :
    (UpperParameter.right (rightFamily N hN s)).footrule =
      1 - 3 * (1 / (2 * (N + 1 : ℝ)) + (s : ℝ) ^ 2 / (4 * N * (N + 1))) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp [UpperParameter.footrule, rightFamily]
  field_simp
  ring

theorem leftFamily_footrule (N : ℕ) (hN : 0 < N) (s : I) :
    (UpperParameter.left (leftFamily N hN s)).footrule =
      1 - 3 * (1 / (2 * (N : ℝ)) - (s : ℝ) ^ 2 / (4 * N * (N + 1))) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp [UpperParameter.footrule, leftFamily]
  field_simp
  ring

theorem contact_interval_cover {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1 / 2) :
    ∃ N : ℕ, 0 < N ∧ 1 / (2 * (N + 1 : ℝ)) ≤ m ∧ m ≤ 1 / (2 * (N : ℝ)) := by
  let N := Nat.floor (1 / (2 * m))
  have hN : 0 < N := Nat.floor_pos.mpr ((le_div_iff₀ (by positivity)).mpr (by linarith))
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ 1 / (2 * m) := Nat.floor_le (by positivity)
  have hlt : 1 / (2 * m) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨N, hN, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ (show 0 < 2 * m by positivity)).mp hlt
    nlinarith only [hh]
  · apply (le_div_iff₀ (by positivity)).mpr
    have hh := (le_div_iff₀ (show 0 < 2 * m by positivity)).mp hle
    nlinarith only [hh]

theorem upperParameter_exists {p : ℝ} (hp : p ∈ Set.Icc (-1 / 2) 1) :
    ∃ a : UpperParameter, a.footrule = p := by
  by_cases hp1 : p = 1
  · exact ⟨.endpoint, hp1.symm⟩
  have hp_lt : p < 1 := lt_of_le_of_ne hp.2 hp1
  let m := (1 - p) / 3
  have hm : 0 < m := by dsimp [m]; linarith
  have hm1 : m ≤ 1 / 2 := by dsimp [m]; linarith [hp.1]
  obtain ⟨N, hN, hlow, hupp⟩ := contact_interval_cover hm hm1
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 := ne_of_gt hn
  have hn1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hmid : 1 / (2 * (N + 1 : ℝ)) + 1 / (4 * N * (N + 1)) =
      1 / (2 * (N : ℝ)) - 1 / (4 * N * (N + 1)) := by field_simp; ring
  by_cases hmleft : m ≤ 1 / (2 * (N + 1 : ℝ)) + 1 / (4 * N * (N + 1))
  · obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := m)
      (f := fun s : I => 1 / (2 * (N + 1 : ℝ)) + (s : ℝ) ^ 2 / (4 * N * (N + 1)))
      (by fun_prop) (by simpa using hlow) (by simpa using hmleft)
    refine ⟨.right (rightFamily N hN s), ?_⟩
    rw [rightFamily_footrule, hs]
    dsimp [m]
    ring
  · have hmidle : 1 / (2 * (N : ℝ)) - 1 / (4 * N * (N + 1)) ≤ m := by
      rw [← hmid]
      exact le_of_not_ge hmleft
    obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := m)
      (f := fun s : I => 1 / (2 * (N : ℝ)) - (1 - (s : ℝ)) ^ 2 / (4 * N * (N + 1)))
      (by fun_prop) (by simpa using hmidle) (by simpa using hupp)
    refine ⟨.left (leftFamily N hN (unitInterval.symm s)), ?_⟩
    rw [leftFamily_footrule]
    change 1 - 3 * (1 / (2 * (N : ℝ)) - (1 - (s : ℝ)) ^ 2 / (4 * N * (N + 1))) = p
    rw [hs]
    dsimp [m]
    ring

end ProbabilityTheory.Copula.RankRegion.RhoFootrule
