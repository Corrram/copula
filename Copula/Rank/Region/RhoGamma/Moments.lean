/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel

Adapted from Corrram/lean-verifications, commit
9e144da5e0d8e2b59dadf9cef090947cb2220313.
Source module: Papers.AnsariRockelSteinmassl2026RhoGamma.Moments
Imports and namespaces adapted to the copula package; unused helpers omitted.
-/
import Copula.Rank.Region.Moments
import Copula.Rank.Region.Mixture
import Copula.Rank.Symmetry
import Mathlib.Analysis.Convex.Basic

/-! # Moment identities, reflection symmetry, and fixed-gamma fibres

This checks equation (28) of Lemma 3.1 and the interpolation/symmetry steps
used to reduce the region problem to its upper boundary. The sign/magnitude
decomposition and the optimal transport argument remain separate obligations.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoGamma

theorem moment_representation (C : Copula 2) :
    C.spearmanRho = 1 - 6 * (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure) ∧
    C.giniGamma = 2 * (∫ x,
      |(x 0 : ℝ) + x 1 - 1| - |(x 0 : ℝ) - x 1| ∂C.toMeasure) :=
  ⟨C.spearmanRho_eq_one_sub, ProbabilityTheory.Copula.RankRegion.gamma_eq_abs_moments C⟩

theorem reflection_pair (C : Copula 2) :
    (C.reflect {1}).spearmanRho = -C.spearmanRho ∧
    (C.reflect {1}).giniGamma = -C.giniGamma :=
  ⟨C.spearmanRho_reflect_second, C.giniGamma_reflect_second⟩

theorem fixed_gamma_intermediate (C D : Copula 2) {g r : ℝ}
    (hC : C.giniGamma = g) (hD : D.giniGamma = g)
    (hrC : C.spearmanRho ≤ r) (hrD : r ≤ D.spearmanRho) :
    ∃ E : Copula 2, E.giniGamma = g ∧ E.spearmanRho = r := by
  have hc : Continuous (fun a : I => (D.mix C a).spearmanRho) := by
    simp_rw [Copula.spearmanRho_mix]
    fun_prop
  obtain ⟨a, ha⟩ := ProbabilityTheory.Copula.RankRegion.exists_unitInterval_eq hc
    (by simpa using hrC) (by simpa using hrD)
  refine ⟨D.mix C a, ?_, ha⟩
  rw [Copula.giniGamma_mix, hD, hC]
  ring

/-- The attainable set uses the source's coordinate order (rho, gamma). -/
def region : Set (ℝ × ℝ) := Set.range (fun C : Copula 2 => (C.spearmanRho, C.giniGamma))

/-- The convexity assertion of Theorem 1.1, independently of its boundary formula. -/
theorem region_convex : Convex ℝ region := by
  rintro x ⟨C, rfl⟩ y ⟨D, rfl⟩ a b ha hb hab
  refine ⟨C.mix D ⟨a, ha, by linarith⟩, ?_⟩
  have he : b = 1 - a := by linarith
  simp [Copula.spearmanRho_mix, Copula.giniGamma_mix, he]

/-- The central-symmetry assertion of Theorem 1.1. -/
theorem region_centrally_symmetric {r g : ℝ} (h : (r, g) ∈ region) :
    (-r, -g) ∈ region := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C.reflect {1}, ?_⟩
  have hr := congrArg Prod.fst hC
  have hg := congrArg Prod.snd hC
  change C.spearmanRho = r at hr
  change C.giniGamma = g at hg
  simp only [Copula.spearmanRho_reflect_second, Copula.giniGamma_reflect_second, hr, hg]

end ProbabilityTheory.Copula.RankRegion.RhoGamma
