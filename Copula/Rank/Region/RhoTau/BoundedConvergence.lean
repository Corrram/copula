/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.OrderIntegrals

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integrable_bounded_one {f : Ω → ℝ} (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (Eventually.of_forall hb)

theorem norm_integral_bounded_one {f : Ω → ℝ} (hb : ∀ x, ‖f x‖ ≤ 1) :
    ‖∫ x, f x ∂μ‖ ≤ 1 := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)

theorem tendsto_integral_bounded_one {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hb : ∀ n x, ‖f n x‖ ≤ 1)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ => 1)
    (fun n => (hf n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (hb n)) ht

end ProbabilityTheory.Copula.RankRegion.RhoTau
