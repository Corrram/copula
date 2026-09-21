/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Perturbation
import Copula.Rank.Region.Mixture

/-! # Restoring the inversion constraint after the extremal adjacent swap

For adjacent minimum and maximum entries, the two linear cubic coefficients
coincide. After swapping them, their mass can be redistributed to restore
the quadratic constraint, while retaining the strict cubic improvement.
This strengthens the swap step in Schreyer–Paulin–Trutschnig, Lemma 4.11.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem restore_pair_quadratic (x y A B : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ X Y : ℝ, 0 ≤ X ∧ 0 ≤ Y ∧ X + Y = x + y ∧
      A * X + B * Y + X * Y = A * x + B * y := by
  let f : ℝ → ℝ := fun t => A * t + B * (x + y - t) + t * (x + y - t)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hxhi : A * x + B * y ≤ f x := by
    dsimp [f]
    nlinarith [mul_nonneg hx hy]
  by_cases hAB : A ≤ B
  · have he : f (x + y) ≤ A * x + B * y := by
      dsimp [f]
      nlinarith [mul_nonneg (sub_nonneg.mpr hAB) hy]
    obtain ⟨X, hX, hval⟩ := intermediate_value_Icc'
      (show x ≤ x + y by linarith) hf.continuousOn ⟨he, hxhi⟩
    refine ⟨X, x + y - X, by linarith [hX.1], by linarith [hX.2], by ring, hval⟩
  · have he : f 0 ≤ A * x + B * y := by
      dsimp [f]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hAB)) hx]
    obtain ⟨X, hX, hval⟩ := intermediate_value_Icc hx hf.continuousOn ⟨he, hxhi⟩
    refine ⟨X, x + y - X, hX.1, by linarith [hX.2], by ring, hval⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
