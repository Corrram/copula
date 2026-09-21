/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoGamma.Coverage

/-! # The exact rho–gamma region

The upper boundary is given by explicit algebraic parameters. Reflection
supplies the lower boundary, and mixtures attain every point between them.
The parameters and their coordinates contain no variational optimization.
-/

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

theorem exists_copula_iff (g r : ℝ) :
    (∃ C : Copula 2, C.giniGamma = g ∧ C.spearmanRho = r) ↔
      g ∈ Set.Icc (-1) 1 ∧
        (∃ a : UpperParameter, a.gamma = g ∧ r ≤ a.rho) ∧
        (∃ b : UpperParameter, b.gamma = -g ∧ -b.rho ≤ r) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    refine ⟨C.giniGamma_mem_Icc, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := upperParameter_exists C.giniGamma_mem_Icc
      exact ⟨a, ha, a.maximizes C ha.symm⟩
    · have hg : -C.giniGamma ∈ Set.Icc (-1) 1 := by
        constructor <;> linarith [C.giniGamma_mem_Icc.1, C.giniGamma_mem_Icc.2]
      obtain ⟨b, hb⟩ := upperParameter_exists hg
      refine ⟨b, hb, ?_⟩
      have hh := b.maximizes (C.reflect {1}) (by rw [giniGamma_reflect_second, hb])
      rw [spearmanRho_reflect_second] at hh
      linarith
  · rintro ⟨_, ⟨a, ha, hu⟩, ⟨b, hb, hl⟩⟩
    apply fixed_gamma_intermediate (b.copula.reflect {1}) a.copula
    · rw [giniGamma_reflect_second, b.gamma_coefficient, hb, neg_neg]
    · exact a.gamma_coefficient.trans ha
    · rwa [spearmanRho_reflect_second, b.rho_coefficient]
    · rwa [a.rho_coefficient]

theorem upperParameter_rho_unique (a b : UpperParameter) (h : a.gamma = b.gamma) :
    a.rho = b.rho := by
  apply le_antisymm
  · have hh := b.maximizes a.copula (a.gamma_coefficient.trans h)
    rwa [a.rho_coefficient] at hh
  · have hh := a.maximizes b.copula (b.gamma_coefficient.trans h.symm)
    rwa [b.rho_coefficient] at hh

end ProbabilityTheory.Copula.RankRegion.RhoGamma
