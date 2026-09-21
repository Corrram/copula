/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Verification.EqualBlocks
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.OrdinalSum.Rank

/-! # Equal diagonal blocks of every positive size

The index n represents n+1 cells, so no zero-cell convention is needed.
-/

open ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion

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

end ProbabilityTheory.Copula.RankRegion
