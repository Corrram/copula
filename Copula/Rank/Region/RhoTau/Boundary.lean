/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau
import Copula.Rank.Region.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Coverage and ordering of the Schreyer–Paulin–Trutschnig arcs -/

open scoped unitInterval Topology
open Filter

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem continuous_arcTau (n : ℕ) : Continuous (arcTau n) := by
  unfold arcTau
  fun_prop

theorem continuous_arcRho (n : ℕ) : Continuous (arcRho n) := by
  unfold arcRho
  fun_prop

theorem strictMono_arcTau (n : ℕ) : StrictMono (fun s : I => arcTau n s) := by
  intro s t hst
  have hst' : (s : ℝ) < t := hst
  have hsq : (s : ℝ) ^ 2 < (t : ℝ) ^ 2 := by
    nlinarith [s.property.1]
  dsimp [arcTau]
  apply add_lt_add_right
  apply (div_lt_div_iff_of_pos_right (by positivity :
    (0 : ℝ) < ((n : ℝ) + 1) * (n + 2))).mpr
  linarith

theorem strictMono_arcRho (n : ℕ) : StrictMono (fun s : I => arcRho n s) := by
  intro s t hst
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hst' : (s : ℝ) < t := hst
  have hs := s.property
  have ht := t.property
  have hsum : 0 < (t : ℝ) + s := by linarith [hs.1]
  have hbound : 0 ≤ 3 * ((t : ℝ) + s) - ((t : ℝ) ^ 2 + t * s + (s : ℝ) ^ 2) := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2),
      mul_nonneg ht.1 (sub_nonneg.mpr ht.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hs.2)]
  have hfactor : 0 < 3 * ((n : ℝ) + 1) * ((t : ℝ) + s) -
      n * ((t : ℝ) ^ 2 + t * s + (s : ℝ) ^ 2) := by
    nlinarith [mul_nonneg hn hbound]
  have hpos : 0 < 2 * ((t : ℝ) - s) *
      (3 * ((n : ℝ) + 1) * ((t : ℝ) + s) -
        n * ((t : ℝ) ^ 2 + t * s + (s : ℝ) ^ 2)) /
      (((n : ℝ) + 1) ^ 2 * (n + 2) ^ 2) := by positivity
  have he : arcRho n t - arcRho n s =
      2 * ((t : ℝ) - s) *
      (3 * ((n : ℝ) + 1) * ((t : ℝ) + s) -
        n * ((t : ℝ) ^ 2 + t * s + (s : ℝ) ^ 2)) /
      (((n : ℝ) + 1) ^ 2 * (n + 2) ^ 2) := by
    unfold arcRho
    field_simp
    ring
  linarith

inductive LowerParameter
  | endpoint
  | arc (n : ℕ) (s : I)

namespace LowerParameter

noncomputable def tau : LowerParameter → ℝ
  | .endpoint => -1
  | .arc n s => arcTau n s

noncomputable def rho : LowerParameter → ℝ
  | .endpoint => -1
  | .arc n s => arcRho n s

noncomputable def copula : LowerParameter → Copula 2
  | .endpoint => countermonotonic
  | .arc n s => arcCopula n s

theorem coefficients (p : LowerParameter) :
    p.copula.kendallTau = p.tau ∧ p.copula.spearmanRho = p.rho := by
  cases p with
  | endpoint => exact ⟨kendallTau_countermonotonic, spearmanRho_countermonotonic⟩
  | arc n s => exact arcCopula_coefficients n s

theorem tau_mem (p : LowerParameter) : p.tau ∈ Set.Icc (-1) 1 := by
  rw [← p.coefficients.1]
  exact p.copula.kendallTau_mem_Icc

theorem rho_mem (p : LowerParameter) : p.rho ∈ Set.Icc (-1) 1 := by
  rw [← p.coefficients.2]
  exact p.copula.spearmanRho_mem_Icc

end LowerParameter


/-- Consecutive continuous arcs cover every point above their limiting junction. -/
theorem joined_arcs_cover {f : ℕ → I → ℝ} {j : ℕ → ℝ} {l x : ℝ}
    (hc : ∀ n, Continuous (f n)) (hzero : ∀ n, f n 0 = j (n + 1))
    (hone : ∀ n, f n 1 = j n) (hj : Tendsto j atTop (𝓝 l))
    (hl : l < x) (hx : x ≤ j 0) : ∃ n s, f n s = x := by
  have hfinite (N : ℕ) : j (N + 1) ≤ x → ∃ n s, f n s = x := by
    induction N with
    | zero =>
      intro h
      obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := x) (hc 0)
        (by rwa [hzero]) (by rwa [hone])
      exact ⟨0, s, hs⟩
    | succ N ih =>
      intro h
      by_cases hN : j (N + 1) ≤ x
      · exact ih hN
      obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := x) (hc (N + 1))
        (by simpa only [hzero, Nat.succ_eq_add_one] using h)
        (by rw [hone]; exact (lt_of_not_ge hN).le)
      exact ⟨N + 1, s, hs⟩
  have he : ∀ᶠ n : ℕ in atTop, j n < x := hj.eventually (gt_mem_nhds hl)
  obtain ⟨n, hn, hnpos⟩ := (he.and (eventually_gt_atTop 0)).exists
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hnpos)
  exact hfinite N hn.le

theorem tau_junction_tendsto :
    Tendsto (fun n : ℕ => -1 + 2 / ((n : ℝ) + 1)) atTop (𝓝 (-1 : ℝ)) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  convert (tendsto_const_nhds (x := (-1 : ℝ))).add h using 1
  · funext n; field_simp
  · norm_num

theorem rho_junction_tendsto :
    Tendsto (fun n : ℕ => -1 + 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 (-1 : ℝ)) := by
  have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul 2
  convert (tendsto_const_nhds (x := (-1 : ℝ))).add h using 1
  · funext n; field_simp
  · norm_num

theorem lowerParameter_tau_exists {t : ℝ} (ht : t ∈ Set.Icc (-1) 1) :
    ∃ p : LowerParameter, p.tau = t := by
  by_cases h : t = -1
  · exact ⟨.endpoint, h.symm⟩
  obtain ⟨n, s, hs⟩ := joined_arcs_cover
    (f := fun n s => arcTau n s) (j := fun n => -1 + 2 / ((n : ℝ) + 1))
    (fun n => (continuous_arcTau n).comp continuous_subtype_val)
    (fun n => by simpa only [Nat.cast_add, Nat.cast_one, Set.Icc.coe_zero,
      show ∀ x : ℝ, x + 1 + 1 = x + 2 by intro x; ring] using (arc_zero n).1)
    (fun n => (arc_one n).1) tau_junction_tendsto
    (lt_of_le_of_ne ht.1 (Ne.symm h)) (by norm_num; linarith [ht.2])
  exact ⟨.arc n s, hs⟩

theorem lowerParameter_rho_exists {r : ℝ} (hr : r ∈ Set.Icc (-1) 1) :
    ∃ p : LowerParameter, p.rho = r := by
  by_cases h : r = -1
  · exact ⟨.endpoint, h.symm⟩
  obtain ⟨n, s, hs⟩ := joined_arcs_cover
    (f := fun n s => arcRho n s) (j := fun n => -1 + 2 / ((n : ℝ) + 1) ^ 2)
    (fun n => (continuous_arcRho n).comp continuous_subtype_val)
    (fun n => by simpa only [Nat.cast_add, Nat.cast_one, Set.Icc.coe_zero,
      show ∀ x : ℝ, x + 1 + 1 = x + 2 by intro x; ring] using (arc_zero n).2)
    (fun n => (arc_one n).2) rho_junction_tendsto
    (lt_of_le_of_ne hr.1 (Ne.symm h)) (by norm_num; linarith [hr.2])
  exact ⟨.arc n s, hs⟩

/-- Filling the horizontal sections uses only actual prototype copulas and
continuity of Kendall's tau along mixtures. -/
theorem prototype_interval_attainable (a b : LowerParameter) {r t : ℝ}
    (ha : a.rho = r) (hb : -b.rho = r) (hl : -b.tau ≤ t) (hu : t ≤ a.tau) :
    (r, t) ∈ attainable .rho .tau := by
  apply fixed_coefficient_intermediate .rho .tau (by decide)
    (b.copula.reflect {1}) a.copula
  · change (b.copula.reflect {1}).spearmanRho = r
    rw [spearmanRho_reflect_second, b.coefficients.2, hb]
  · exact a.coefficients.2.trans ha
  · change (b.copula.reflect {1}).kendallTau ≤ t
    rwa [kendallTau_reflect_second, b.coefficients.1]
  · change t ≤ a.copula.kendallTau
    rwa [a.coefficients.1]

end ProbabilityTheory.Copula.RankRegion.RhoTau
