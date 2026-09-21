/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.EqualBlocks
import Copula.Rank.Symmetry

/-! # The Schreyer–Paulin–Trutschnig prototype copulas

Schreyer, Paulin and Trutschnig (2017), *On the exact region determined
by Kendall's tau and Spearman's rho*, Lemma 3.5. Reflected ordinal sums
of W attain the junction points and every prototype arc. The parameter
`s ∈ I` varies from `n+2` equal blocks to `n+1` equal blocks.

The universal sharp inequality is proved in `RhoTau.Universal`, and
`RhoTau.Exact` proves the complete attainable-region characterization.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

/-- Index `n` represents `n+1` equal countermonotonic blocks, then reflection. -/
noncomputable def junctionCopula (n : ℕ) : Copula 2 :=
  (equalBlocks n countermonotonic).reflect {1}

theorem junctionCopula_coefficients (n : ℕ) :
    (junctionCopula n).kendallTau = -1 + 2 / ((n : ℝ) + 1) ∧
    (junctionCopula n).spearmanRho = -1 + 2 / ((n : ℝ) + 1) ^ 2 := by
  simp only [junctionCopula, kendallTau_reflect_second, spearmanRho_reflect_second,
    equalBlocks_tau, equalBlocks_rho, kendallTau_countermonotonic, spearmanRho_countermonotonic]
  constructor <;> ring

theorem junction_attainable (n : ℕ) :
    ∃ C : Copula 2, C.kendallTau = -1 + 2 / ((n : ℝ) + 1) ∧
      C.spearmanRho = -1 + 2 / ((n : ℝ) + 1) ^ 2 :=
  ⟨junctionCopula n, junctionCopula_coefficients n⟩

/-- Total width of the first `n+1` equal blocks of a prototype. -/
noncomputable def arcSplit (n : ℕ) (s : I) : I :=
  ⟨((n : ℝ) + 1 + s) / (n + 2), by
    constructor
    · apply div_nonneg <;> linarith [Nat.cast_nonneg (α := ℝ) n, s.property.1]
    · apply (div_le_one (by positivity)).mpr
      linarith [s.property.2]⟩

/-- A prototype has `n+1` equal blocks and one smaller block, followed by reflection. -/
noncomputable def arcCopula (n : ℕ) (s : I) : Copula 2 :=
  ((equalBlocks n countermonotonic).ordinalSum countermonotonic (arcSplit n s)).reflect {1}

/-- Polynomial parametrization of the tau coordinate of a prototype arc. -/
noncomputable def arcTau (n : ℕ) (s : ℝ) : ℝ :=
  -1 + 2 / ((n : ℝ) + 2) + 2 * s ^ 2 / (((n : ℝ) + 1) * (n + 2))

/-- Polynomial parametrization of the rho coordinate of a prototype arc. -/
noncomputable def arcRho (n : ℕ) (s : ℝ) : ℝ :=
  -1 + 2 / ((n : ℝ) + 2) ^ 2 +
    6 * s ^ 2 / (((n : ℝ) + 1) * (n + 2) ^ 2) -
    2 * n * s ^ 3 / (((n : ℝ) + 1) ^ 2 * (n + 2) ^ 2)

theorem arcCopula_coefficients (n : ℕ) (s : I) :
    (arcCopula n s).kendallTau = arcTau n s ∧
    (arcCopula n s).spearmanRho = arcRho n s := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [arcCopula, kendallTau_reflect_second, spearmanRho_reflect_second,
    kendallTau_ordinalSum, spearmanRho_ordinalSum, equalBlocks_tau, equalBlocks_rho,
    kendallTau_countermonotonic, spearmanRho_countermonotonic, arcSplit, arcTau, arcRho]
  constructor <;> field_simp <;> ring

theorem arc_attainable (n : ℕ) (s : I) :
    ∃ C : Copula 2, C.kendallTau = arcTau n s ∧ C.spearmanRho = arcRho n s :=
  ⟨arcCopula n s, arcCopula_coefficients n s⟩

theorem arc_zero (n : ℕ) :
    arcTau n 0 = -1 + 2 / ((n : ℝ) + 2) ∧
    arcRho n 0 = -1 + 2 / ((n : ℝ) + 2) ^ 2 := by
  simp [arcTau, arcRho]

theorem arc_one (n : ℕ) :
    arcTau n 1 = -1 + 2 / ((n : ℝ) + 1) ∧
    arcRho n 1 = -1 + 2 / ((n : ℝ) + 1) ^ 2 := by
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  simp only [arcTau, arcRho, one_pow]
  constructor <;> field_simp <;> ring

end ProbabilityTheory.Copula.RankRegion.RhoTau
