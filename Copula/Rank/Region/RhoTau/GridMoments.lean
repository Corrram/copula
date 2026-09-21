/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Quantization
import Copula.Rank.Region.RhoTau.FiniteIntegration
import Copula.Rank.Region.RhoTau.BoundedConvergence

open MeasureTheory Filter
open scoped unitInterval Topology BigOperators

set_option maxHeartbeats 400000

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

attribute [local irreducible] gridSwap

noncomputable def gridWeights (C : Copula 2) (n : ℕ) := finiteWeight C.toMeasure (gridCode n)

theorem gridWeights_nonneg (C : Copula 2) (n : ℕ) : ∀ i, 0 ≤ gridWeights C n i :=
  finiteWeight_nonneg _ _

theorem gridWeights_sum (C : Copula 2) (n : ℕ) : ∑ i, gridWeights C n i = 1 :=
  finiteWeight_sum _ (measurable_gridCode n)

noncomputable def gridFirst (n : ℕ) (x y : Fin 2 → I) : ℝ :=
  orderSign (gridCode n x) (gridCode n y)

noncomputable def gridSecond (n : ℕ) (x y : Fin 2 → I) : ℝ :=
  orderSign (gridSwap n (gridCode n x)) (gridSwap n (gridCode n y))

theorem measurable_gridFirst (n : ℕ) :
    Measurable (fun p : (Fin 2 → I) × (Fin 2 → I) => gridFirst n p.1 p.2) :=
  (measurable_of_finite (fun p : Fin ((n + 1) * (n + 1)) × Fin ((n + 1) * (n + 1)) => orderSign p.1 p.2)).comp
    (((measurable_gridCode n).comp measurable_fst).prodMk
      ((measurable_gridCode n).comp measurable_snd))

theorem measurable_gridSecond (n : ℕ) :
    Measurable (fun p : (Fin 2 → I) × (Fin 2 → I) => gridSecond n p.1 p.2) := by
  have hs : Measurable (fun x : Fin 2 → I => gridSwap n (gridCode n x)) :=
    (measurable_of_finite (gridSwap n)).comp (measurable_gridCode n)
  have ha : Measurable (fun p : (Fin 2 → I) × (Fin 2 → I) =>
      gridSwap n (gridCode n p.1)) := hs.comp measurable_fst
  have hb : Measurable (fun p : (Fin 2 → I) × (Fin 2 → I) =>
      gridSwap n (gridCode n p.2)) := hs.comp measurable_snd
  unfold gridSecond orderSign
  exact Measurable.ite (measurableSet_lt ha hb) measurable_const
    (Measurable.ite (measurableSet_lt hb ha) measurable_const measurable_const)

theorem norm_gridFirst (n : ℕ) (x y : Fin 2 → I) : ‖gridFirst n x y‖ ≤ 1 :=
  norm_orderSign_le_one _ _

theorem norm_gridSecond (n : ℕ) (x y : Fin 2 → I) : ‖gridSecond n x y‖ ≤ 1 :=
  norm_orderSign_le_one _ _

theorem norm_gridProduct (n : ℕ) (x y : Fin 2 → I) :
    ‖gridFirst n x y * gridSecond n x y‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_mul (norm_gridFirst n x y) (norm_gridSecond n x y) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

theorem tendsto_gridFirst_mean (C : Copula 2) (x : Fin 2 → I) :
    Tendsto (fun n => ∫ y, gridFirst n x y ∂C.toMeasure) atTop (𝓝 (1 - 2 * (x 0 : ℝ))) := by
  rw [← integral_orderSign C 0 (x 0)]
  apply tendsto_integral_bounded_one C.toMeasure
    (fun n => (measurable_gridFirst n).comp (measurable_const.prodMk measurable_id))
    (fun n y => norm_gridFirst n x y)
  filter_upwards [C.ae_eval_ne 0 (x 0)] with y hy
  exact tendsto_const_nhds.congr' ((eventually_grid_order hy.symm).mono (fun _ h => h.symm))

theorem tendsto_gridSecond_mean (C : Copula 2) (x : Fin 2 → I) :
    Tendsto (fun n => ∫ y, gridSecond n x y ∂C.toMeasure) atTop (𝓝 (1 - 2 * (x 1 : ℝ))) := by
  rw [← integral_orderSign C 1 (x 1)]
  apply tendsto_integral_bounded_one C.toMeasure
    (fun n => (measurable_gridSecond n).comp (measurable_const.prodMk measurable_id))
    (fun n y => norm_gridSecond n x y)
  filter_upwards [C.ae_eval_ne 1 (x 1)] with y hy
  exact tendsto_const_nhds.congr' ((eventually_grid_swap_order hy.symm).mono (fun _ h => h.symm))

theorem tendsto_grid_rank_moment (C : Copula 2) :
    Tendsto (fun n => ∫ x, (∫ y, gridFirst n x y ∂C.toMeasure) *
      (∫ y, gridSecond n x y ∂C.toMeasure) ∂C.toMeasure) atTop
      (𝓝 (∫ x, (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ)) ∂C.toMeasure)) := by
  apply tendsto_integral_bounded_one C.toMeasure
  · intro n
    exact ((measurable_gridFirst n).stronglyMeasurable.integral_prod_right'.measurable).mul
      ((measurable_gridSecond n).stronglyMeasurable.integral_prod_right'.measurable)
  · intro n x
    rw [norm_mul]
    exact (mul_le_mul (norm_integral_bounded_one C.toMeasure (norm_gridFirst n x))
      (norm_integral_bounded_one C.toMeasure (norm_gridSecond n x))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · exact Eventually.of_forall fun x => (tendsto_gridFirst_mean C x).mul (tendsto_gridSecond_mean C x)

theorem tendsto_grid_pair_moment (C : Copula 2) :
    Tendsto (fun n => ∫ p, gridFirst n p.1 p.2 * gridSecond n p.1 p.2
      ∂C.toMeasure.prod C.toMeasure) atTop (𝓝 C.kendallTau) := by
  rw [← integral_orderSign_product C]
  apply tendsto_integral_bounded_one (C.toMeasure.prod C.toMeasure)
    (fun n => (measurable_gridFirst n).mul (measurable_gridSecond n))
    (fun n p => norm_gridProduct n p.1 p.2)
  filter_upwards [C.ae_prod_eval_ne C 0, C.ae_prod_eval_ne C 1] with p h0 h1
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_grid_order h0, eventually_grid_swap_order h1] with n hn hn'
  exact (congrArg₂ (· * ·) hn hn').symm

theorem grid_pair_moment_eq (C : Copula 2) (n : ℕ) :
    (∫ p, gridFirst n p.1 p.2 * gridSecond n p.1 p.2 ∂C.toMeasure.prod C.toMeasure) =
      weighted2 (gridWeights C n) (fun i j => orderSign i j * orderSign (gridSwap n i) (gridSwap n j)) := by
  erw [integral_prod _ (integrable_bounded_one (C.toMeasure.prod C.toMeasure)
    ((measurable_gridFirst n).mul (measurable_gridSecond n)) (fun p => norm_gridProduct n p.1 p.2))]
  simpa only [gridFirst, gridSecond, gridWeights, Pi.mul_apply] using
    (integral_finite_pair C.toMeasure (measurable_gridCode n)
      (fun i j => orderSign i j * orderSign (gridSwap n i) (gridSwap n j)))

theorem grid_rank_moment_eq (C : Copula 2) (n : ℕ) :
    (∫ x, (∫ y, gridFirst n x y ∂C.toMeasure) *
      (∫ y, gridSecond n x y ∂C.toMeasure) ∂C.toMeasure) =
      ∑ i, gridWeights C n i * (∑ j, orderSign i j * gridWeights C n j) *
        (∑ k, orderSign (gridSwap n i) (gridSwap n k) * gridWeights C n k) := by
  simp only [gridFirst, gridSecond]
  have hsecond (x : Fin 2 → I) := integral_finite_map C.toMeasure (measurable_gridCode n)
    (fun j => orderSign (gridSwap n (gridCode n x)) (gridSwap n j))
  simp_rw [hsecond]
  simp_rw [integral_finite_map C.toMeasure (measurable_gridCode n)]
  rw [integral_finite_map C.toMeasure (measurable_gridCode n) (fun i =>
    (∑ j, finiteWeight C.toMeasure (gridCode n) j * orderSign i j) *
    (∑ k, finiteWeight C.toMeasure (gridCode n) k * orderSign (gridSwap n i) (gridSwap n k)))]
  simp only [gridWeights, mul_comm, mul_assoc]

end ProbabilityTheory.Copula.RankRegion.RhoTau
