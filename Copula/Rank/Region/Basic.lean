/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Mixture
import Copula.Rank.Symmetry
import Mathlib.Analysis.Convex.Basic

/-! # A uniform API for the ten pairwise rank regions

An attainable region is the image of actual copulas. Defining one is
distinct from proving a formula for its boundary; see the coverage table
in `docs/rank-regions.md` for the exact-region theorems currently available.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion

/-- The five coefficients considered in the classical pairwise region problem. -/
inductive Coefficient
  | rho | tau | beta | footrule | gamma
  deriving DecidableEq, Repr

/-- Evaluate a coefficient using the package's population normalization. -/
noncomputable def Coefficient.eval : Coefficient → Copula 2 → ℝ
  | .rho => spearmanRho
  | .tau => kendallTau
  | .beta => blomqvistBeta
  | .footrule => spearmanFootrule
  | .gamma => giniGamma

/-- All jointly attainable values, in the stated coordinate order. -/
def attainable (a b : Coefficient) : Set (ℝ × ℝ) :=
  Set.range (fun C : Copula 2 => (a.eval C, b.eval C))

theorem mem_attainable_iff (a b : Coefficient) (x y : ℝ) :
    (x, y) ∈ attainable a b ↔ ∃ C : Copula 2, a.eval C = x ∧ b.eval C = y := by
  simp [attainable, Prod.mk.injEq]

theorem mem_attainable_swap (a b : Coefficient) (x y : ℝ) :
    (x, y) ∈ attainable a b ↔ (y, x) ∈ attainable b a := by
  simp only [mem_attainable_iff]
  constructor <;> rintro ⟨C, h1, h2⟩ <;> exact ⟨C, h2, h1⟩

theorem Coefficient.eval_mix (k : Coefficient) (hk : k ≠ .tau)
    (C D : Copula 2) (a : I) :
    k.eval (C.mix D a) = (a : ℝ) * k.eval C + (1 - (a : ℝ)) * k.eval D := by
  cases k with
  | rho => exact spearmanRho_mix C D a
  | tau => exact (hk rfl).elim
  | beta => exact blomqvistBeta_mix C D a
  | footrule => exact spearmanFootrule_mix C D a
  | gamma => exact giniGamma_mix C D a

theorem Coefficient.continuous_eval_mix (k : Coefficient) (C D : Copula 2) :
    Continuous (fun a : I => k.eval (C.mix D a)) := by
  by_cases hk : k = .tau
  · subst k; exact continuous_tau_mix C D
  · simp_rw [k.eval_mix hk]; fun_prop

/-- The six pairs among the four affine coefficients have convex attainable regions. -/
theorem attainable_convex (a b : Coefficient) (ha : a ≠ .tau) (hb : b ≠ .tau) :
    Convex ℝ (attainable a b) := by
  rintro x ⟨C, rfl⟩ y ⟨D, rfl⟩ u v hu hv huv
  refine ⟨C.mix D ⟨u, hu, by linarith⟩, ?_⟩
  have he : v = 1 - u := by linarith
  simp [a.eval_mix ha, b.eval_mix hb, he]

/-- At fixed affine coefficient, the other coefficient attains intermediate values.
This also applies to Kendall's tau, whose dependence on mixture weights is quadratic. -/
theorem fixed_coefficient_intermediate (a b : Coefficient) (ha : a ≠ .tau)
    (C D : Copula 2) {x y : ℝ} (hC : a.eval C = x) (hD : a.eval D = x)
    (hyC : b.eval C ≤ y) (hyD : y ≤ b.eval D) :
    (x, y) ∈ attainable a b := by
  obtain ⟨u, hu⟩ := exists_unitInterval_eq (z := y) (b.continuous_eval_mix D C)
    (by simpa only [mix_zero] using hyC) (by simpa only [mix_one] using hyD)
  rw [mem_attainable_iff]
  refine ⟨D.mix C u, ?_, hu⟩
  rw [a.eval_mix ha, hD, hC]
  ring

theorem Coefficient.eval_reflect (k : Coefficient) (hk : k ≠ .footrule) (C : Copula 2) :
    k.eval (C.reflect {1}) = -k.eval C := by
  cases k with
  | rho => exact spearmanRho_reflect_second C
  | tau => exact kendallTau_reflect_second C
  | beta => exact blomqvistBeta_reflect_second C
  | footrule => exact (hk rfl).elim
  | gamma => exact giniGamma_reflect_second C

theorem mem_attainable_neg (a b : Coefficient) (ha : a ≠ .footrule) (hb : b ≠ .footrule)
    (x y : ℝ) : (x, y) ∈ attainable a b ↔ (-x, -y) ∈ attainable a b := by
  have h (u v : ℝ) : (u, v) ∈ attainable a b → (-u, -v) ∈ attainable a b := by
    rw [mem_attainable_iff, mem_attainable_iff]
    rintro ⟨C, rfl, rfl⟩
    exact ⟨C.reflect {1}, a.eval_reflect ha C, b.eval_reflect hb C⟩
  exact ⟨h x y, fun hh => by simpa only [neg_neg] using h (-x) (-y) hh⟩

end ProbabilityTheory.Copula.RankRegion
