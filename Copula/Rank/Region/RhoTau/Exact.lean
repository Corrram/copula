/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Universal

/-! # The exact Spearman rho–Kendall tau region

The boundary parameters are the polynomial arcs of
Schreyer–Paulin–Trutschnig, together with their limiting endpoint.
The lower inequality follows from finite weighted permutations and
dominated convergence. Reflection gives the upper inequality; mixtures
at fixed rho fill every horizontal section between the boundary copulas.
-/

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem universal_upper (C : Copula 2) :
    ∃ p : LowerParameter, p.tau = -C.kendallTau ∧ C.spearmanRho ≤ -p.rho := by
  obtain ⟨p, ht, hr⟩ := universal_lower (C.reflect {1})
  rw [kendallTau_reflect_second] at ht
  rw [spearmanRho_reflect_second] at hr
  exact ⟨p, ht, by linarith⟩

/-- Exact membership, with arithmetic boundary parameters and no copula assumptions. -/
theorem exists_copula_iff (r t : ℝ) :
    (∃ C : Copula 2, C.spearmanRho = r ∧ C.kendallTau = t) ↔
      t ∈ Set.Icc (-1) 1 ∧
        (∃ a : LowerParameter, a.tau = t ∧ a.rho ≤ r) ∧
        (∃ b : LowerParameter, b.tau = -t ∧ r ≤ -b.rho) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨C.kendallTau_mem_Icc, universal_lower C, universal_upper C⟩
  · rintro ⟨_, ⟨a, hat, har⟩, ⟨b, hbt, hbr⟩⟩
    have hr : r ∈ Set.Icc (-1) 1 := ⟨a.rho_mem.1.trans har, by linarith [b.rho_mem.1]⟩
    obtain ⟨a', ha'⟩ := lowerParameter_rho_exists hr
    obtain ⟨b', hb'⟩ := lowerParameter_rho_exists
      (show -r ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [hr.2], by linarith [hr.1]⟩)
    have hu : t ≤ a'.tau := by
      rw [← hat, a.order_iff a', ha']
      exact har
    have hl : -b'.tau ≤ t := by
      have h : b.tau ≤ b'.tau := (b.order_iff b').mpr (by rw [hb']; linarith)
      rw [hbt] at h
      linarith
    exact (mem_attainable_iff .rho .tau r t).mp
      (prototype_interval_attainable a' b' ha' (by linarith) hl hu)

end ProbabilityTheory.Copula.RankRegion.RhoTau
