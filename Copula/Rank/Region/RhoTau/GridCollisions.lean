/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.GridMoments

open MeasureTheory Filter
open scoped unitInterval Topology BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

noncomputable def gridCollision (n : ℕ) (x y : Fin 2 → I) : ℝ :=
  if gridCode n x = gridCode n y then 1 else 0

theorem measurable_gridCollision (n : ℕ) :
    Measurable (fun p : (Fin 2 → I) × (Fin 2 → I) => gridCollision n p.1 p.2) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_gridCode n).comp measurable_fst)
    ((measurable_gridCode n).comp measurable_snd)

theorem norm_gridCollision (n : ℕ) (x y : Fin 2 → I) : ‖gridCollision n x y‖ ≤ 1 := by
  unfold gridCollision
  split_ifs <;> norm_num

theorem eventually_grid_ne {x y : Fin 2 → I} (h : x 0 ≠ y 0) :
    ∀ᶠ n : ℕ in atTop, gridCode n x ≠ gridCode n y := by
  filter_upwards [eventually_grid_order h] with n hn
  intro he
  rw [he, orderSign_self] at hn
  have hs := orderSign_sq h
  rw [← hn] at hs
  norm_num at hs

theorem grid_collision_eq (C : Copula 2) (n : ℕ) :
    (∫ p, gridCollision n p.1 p.2 ∂C.toMeasure.prod C.toMeasure) =
      ∑ i, (gridWeights C n i) ^ 2 := by
  erw [integral_prod _ (integrable_bounded_one (C.toMeasure.prod C.toMeasure)
    (measurable_gridCollision n) (fun p => norm_gridCollision n p.1 p.2))]
  rw [show (∫ x, ∫ y, gridCollision n x y ∂C.toMeasure ∂C.toMeasure) =
    weighted2 (gridWeights C n) (fun i j => if i = j then 1 else 0) from
      integral_finite_pair C.toMeasure (measurable_gridCode n) (fun i j => if i = j then 1 else 0)]
  simp [weighted2, mul_ite, pow_two]

theorem tendsto_grid_squares (C : Copula 2) :
    Tendsto (fun n => ∑ i, (gridWeights C n i) ^ 2) atTop (𝓝 0) := by
  have ht := tendsto_integral_bounded_one (C.toMeasure.prod C.toMeasure)
    measurable_gridCollision (fun n p => norm_gridCollision n p.1 p.2)
    (g := fun _ => 0) (by
      filter_upwards [C.ae_prod_eval_ne C 0] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_grid_ne hp] with n hn
      simp [gridCollision, hn])
  simpa only [grid_collision_eq, integral_zero] using ht

theorem gridWeights_le_one (C : Copula 2) (n : ℕ) (i : Fin ((n + 1) * (n + 1))) :
    gridWeights C n i ≤ 1 := by
  rw [← gridWeights_sum C n]
  exact Finset.single_le_sum (fun j _ => gridWeights_nonneg C n j) (Finset.mem_univ i)

theorem tendsto_grid_cubes (C : Copula 2) :
    Tendsto (fun n => ∑ i, (gridWeights C n i) ^ 3) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun i _ => pow_nonneg (gridWeights_nonneg C n i) 3))
    (fun n => ?_) (tendsto_grid_squares C)
  apply Finset.sum_le_sum
  intro i _
  have h := gridWeights_le_one C n i
  nlinarith [sq_nonneg (gridWeights C n i),
    mul_nonneg (sq_nonneg (gridWeights C n i)) (sub_nonneg.mpr h)]

end ProbabilityTheory.Copula.RankRegion.RhoTau
