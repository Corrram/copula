/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Basic
import Copula.Rank.Region.Beta
import Copula.Rank.Region.RhoTau.Exact
import Copula.Rank.Region.RhoFootrule.Touchpoints
import Copula.Rank.Region.RhoFootrule.Exact
import Copula.Rank.Region.RhoGamma.SignAttainment
import Copula.Rank.Region.RhoGamma.HalfShift
import Copula.Rank.Region.RhoGamma.Exact

/-! # Pairwise attainable regions of five rank coefficients

All ten pairs have exact membership theorems, including boundary attainment
and every point in between. The coverage and mathematical references are in
`docs/rank-regions.md`.
-/

namespace ProbabilityTheory.Copula.RankRegion

theorem attainable_footrule_tau_iff (p t : ℝ) :
    (p, t) ∈ attainable .footrule .tau ↔
      p ∈ Set.Icc (-1 / 2) 1 ∧ 4 / 3 * p - 1 / 3 ≤ t ∧ t ≤ 2 / 3 * p + 1 / 3 := by
  rw [mem_attainable_iff]
  exact TauFootrule.exists_copula_iff p t

theorem attainable_gamma_tau_iff (g t : ℝ) :
    (g, t) ∈ attainable .gamma .tau ↔
      g ∈ Set.Icc (-1) 1 ∧ max (2 / 3 * g - 1 / 3) (2 * g - 1) ≤ t ∧
      t ≤ min (2 / 3 * g + 1 / 3) (2 * g + 1) := by
  rw [mem_attainable_iff]
  exact TauGamma.exists_copula_iff g t

theorem attainable_footrule_gamma_iff (p g : ℝ) :
    (p, g) ∈ attainable .footrule .gamma ↔
      p ∈ Set.Icc (-1 / 2) 1 ∧ 4 / 3 * p - 1 / 3 ≤ g ∧
      g ≤ min (4 / 3 * p + 1 / 6) (2 / 3 * p + 1 / 3) := by
  rw [mem_attainable_iff]
  exact FootruleGamma.exists_copula_iff p g

theorem attainable_beta_rho_iff (b r : ℝ) :
    (b, r) ∈ attainable .beta .rho ↔
      b ∈ Set.Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 3 - 1 ≤ r ∧
      r ≤ 1 - 3 / 16 * (1 - b) ^ 3 := by
  rw [mem_attainable_iff]
  exact Beta.rho_iff b r

theorem attainable_beta_tau_iff (b t : ℝ) :
    (b, t) ∈ attainable .beta .tau ↔
      b ∈ Set.Icc (-1) 1 ∧ 1 / 4 * (1 + b) ^ 2 - 1 ≤ t ∧
      t ≤ 1 - 1 / 4 * (1 - b) ^ 2 := by
  rw [mem_attainable_iff]
  exact Beta.tau_iff b t

theorem attainable_beta_footrule_iff (b p : ℝ) :
    (b, p) ∈ attainable .beta .footrule ↔
      b ∈ Set.Icc (-1) 1 ∧ 3 / 16 * (1 + b) ^ 2 - 1 / 2 ≤ p ∧
      p ≤ 1 - 3 / 8 * (1 - b) ^ 2 := by
  rw [mem_attainable_iff]
  exact Beta.footrule_iff b p

theorem attainable_beta_gamma_iff (b g : ℝ) :
    (b, g) ∈ attainable .beta .gamma ↔
      b ∈ Set.Icc (-1) 1 ∧ 3 / 8 * (1 + b) ^ 2 - 1 ≤ g ∧
      g ≤ 1 - 3 / 8 * (1 - b) ^ 2 := by
  rw [mem_attainable_iff]
  exact Beta.gamma_iff b g


/-- Exact rho–footrule membership; the upper boundary is a countable family of polynomial arcs. -/
theorem attainable_footrule_rho_iff (p r : ℝ) :
    (p, r) ∈ attainable .footrule .rho ↔
      p ∈ Set.Icc (-1 / 2) 1 ∧ RhoFootrule.lowerBoundary p ≤ r ∧
        ∃ a : RhoFootrule.UpperParameter, a.footrule = p ∧ r ≤ a.rho := by
  rw [mem_attainable_iff]
  exact RhoFootrule.exists_copula_iff p r


/-- Exact rho–gamma membership, including both sharp boundaries and every interior point. -/
theorem attainable_gamma_rho_iff (g r : ℝ) :
    (g, r) ∈ attainable .gamma .rho ↔
      g ∈ Set.Icc (-1) 1 ∧
        (∃ a : RhoGamma.UpperParameter, a.gamma = g ∧ r ≤ a.rho) ∧
        (∃ b : RhoGamma.UpperParameter, b.gamma = -g ∧ -b.rho ≤ r) := by
  rw [mem_attainable_iff]
  exact RhoGamma.exists_copula_iff g r


/-- The exact Schreyer–Paulin–Trutschnig rho–tau region. -/
theorem attainable_rho_tau_iff (r t : ℝ) :
    (r, t) ∈ attainable .rho .tau ↔
      t ∈ Set.Icc (-1) 1 ∧
        (∃ a : RhoTau.LowerParameter, a.tau = t ∧ a.rho ≤ r) ∧
        (∃ b : RhoTau.LowerParameter, b.tau = -t ∧ r ≤ -b.rho) := by
  rw [mem_attainable_iff]
  exact RhoTau.exists_copula_iff r t

end ProbabilityTheory.Copula.RankRegion
