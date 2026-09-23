import Copula.OrdinalSum.Rank
import Copula.OrdinalSum.TailDependence
import Copula.Rank.Region.MeanVariance.Support.Functional

/-! # Equal diagonal blocks of every positive size

The index n represents n+1 cells, so no zero-cell convention is needed.
-/

open ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.MeanVariance.Support

noncomputable def equalSplit (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 2), by
    exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩⟩

noncomputable def equalBlocks : ℕ → Copula 2 → Copula 2
  | 0, C => C
  | n + 1, C => C.ordinalSum (equalBlocks n C) (equalSplit n)

theorem equalBlocks_rho (n : ℕ) (C : Copula 2) :
    (equalBlocks n C).spearmanRho = 1 - (1 - C.spearmanRho) / ((n : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp [equalBlocks]
  | succ n ih =>
    rw [equalBlocks, Copula.spearmanRho_ordinalSum, ih]
    simp only [equalSplit, Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    field_simp
    ring

theorem equalBlocks_tau (n : ℕ) (C : Copula 2) :
    (equalBlocks n C).kendallTau = 1 - (1 - C.kendallTau) / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [equalBlocks]
  | succ n ih =>
    rw [equalBlocks, Copula.kendallTau_ordinalSum, ih]
    simp only [equalSplit, Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    field_simp
    ring

theorem equalBlocks_footrule (n : ℕ) (C : Copula 2) :
    (equalBlocks n C).spearmanFootrule = 1 - (1 - C.spearmanFootrule) / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [equalBlocks]
  | succ n ih =>
    rw [equalBlocks, Copula.spearmanFootrule_ordinalSum, ih]
    simp only [equalSplit, Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
    field_simp
    ring

theorem HasFunctionalWitness.equalBlocks {C : Copula 2} (hC : HasFunctionalWitness C)
    (n : ℕ) : HasFunctionalWitness (equalBlocks n C) := by
  induction n with
  | zero => exact hC
  | succ n ih => exact hC.ordinalSum ih _

theorem equalBlocks_lower_tail (C : Copula 2) {l : ℝ} (hC : C.HasLowerTailDependence l)
    (n : ℕ) : (equalBlocks n C).HasLowerTailDependence l := by
  cases n with
  | zero => exact hC
  | succ n =>
    exact hC.ordinalSum _ _ (by change (0 : ℝ) < 1 / ((n : ℝ) + 2); positivity)

theorem equalBlocks_upper_tail (C : Copula 2) {l : ℝ} (hC : C.HasUpperTailDependence l)
    (n : ℕ) : (equalBlocks n C).HasUpperTailDependence l := by
  induction n with
  | zero => exact hC
  | succ n ih =>
    apply ih.ordinalSum
    change 1 / ((n : ℝ) + 2) < 1
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]

end ProbabilityTheory.Copula.RankRegion.MeanVariance.Support
