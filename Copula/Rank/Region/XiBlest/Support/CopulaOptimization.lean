import Copula.Basic
import Copula.Comonotonic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Order.Compact

/-! # Continuous costs attain their extrema over all copulas

Uniform-marginal probability measures form a closed subset of the compact
space of probability measures on the unit cube, in the weak topology.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

noncomputable def uniformMarginalMeasures (d : ℕ) : Set (ProbabilityMeasure (Fin d → I)) :=
  {μ | ∀ i : Fin d, μ.map (fun x => x i) = (⟨volume, inferInstance⟩ : ProbabilityMeasure I)}

theorem isCompact_uniformMarginalMeasures (d : ℕ) : IsCompact (uniformMarginalMeasures d) := by
  apply IsClosed.isCompact
  unfold uniformMarginalMeasures
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq (ProbabilityMeasure.continuous_map (continuous_apply i)) continuous_const

theorem measure_mem_uniformMarginalMeasures {d : ℕ} (C : Copula d) :
    C.measure ∈ uniformMarginalMeasures d := by
  intro i
  apply Subtype.ext
  exact C.map_eval i

/-- A maximum exists for every continuous real cost, in every finite dimension. -/
theorem exists_copula_maximizer {d : ℕ} {f : (Fin d → I) → ℝ} (hf : Continuous f) :
    ∃ C : Copula d, ∀ D : Copula d, (∫ x, f x ∂D.toMeasure) ≤ ∫ x, f x ∂C.toMeasure := by
  have hn : (uniformMarginalMeasures d).Nonempty :=
    ⟨(Copula.comonotonic d).measure, measure_mem_uniformMarginalMeasures _⟩
  have hc : Continuous (fun μ : ProbabilityMeasure (Fin d → I) => ∫ x, f x ∂μ.toMeasure) :=
    ProbabilityMeasure.continuous_integral_continuousMap (⟨f, hf⟩ : C(Fin d → I, ℝ))
  obtain ⟨μ, hμ, hmax⟩ := (isCompact_uniformMarginalMeasures d).exists_isMaxOn hn hc.continuousOn
  let C : Copula d := { measure := μ, marginal_eq := fun i => congrArg Subtype.val (hμ i) }
  exact ⟨C, fun D => hmax (measure_mem_uniformMarginalMeasures D)⟩

theorem exists_copula_minimizer {d : ℕ} {f : (Fin d → I) → ℝ} (hf : Continuous f) :
    ∃ C : Copula d, ∀ D : Copula d, (∫ x, f x ∂C.toMeasure) ≤ ∫ x, f x ∂D.toMeasure := by
  obtain ⟨C, hC⟩ := exists_copula_maximizer hf.neg
  refine ⟨C, fun D => ?_⟩
  have h := hC D
  simp only [Pi.neg_apply, integral_neg, neg_le_neg_iff] at h
  exact h

/-- Any finite pair of continuous costs has a compact attainable set. -/
theorem isCompact_copula_integral_pair {f g : (Fin 2 → I) → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    IsCompact (Set.range (fun C : Copula 2 =>
      ((∫ x, f x ∂C.toMeasure), (∫ x, g x ∂C.toMeasure)))) := by
  let F : ProbabilityMeasure (Fin 2 → I) → ℝ × ℝ := fun μ =>
    ((∫ x, f x ∂μ.toMeasure), (∫ x, g x ∂μ.toMeasure))
  have hc : Continuous F :=
    (ProbabilityMeasure.continuous_integral_continuousMap (⟨f, hf⟩ : C(Fin 2 → I, ℝ))).prodMk
      (ProbabilityMeasure.continuous_integral_continuousMap (⟨g, hg⟩ : C(Fin 2 → I, ℝ)))
  have he : Set.range (fun C : Copula 2 =>
      ((∫ x, f x ∂C.toMeasure), (∫ x, g x ∂C.toMeasure))) =
      F '' uniformMarginalMeasures 2 := by
    ext y
    constructor
    · rintro ⟨C, rfl⟩
      exact ⟨C.measure, measure_mem_uniformMarginalMeasures C, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨{ measure := μ, marginal_eq := fun i => congrArg Subtype.val (hμ i) }, rfl⟩
  rw [he]
  exact (isCompact_uniformMarginalMeasures 2).image hc

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
