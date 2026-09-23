import Copula.Rank.Region.XiBlest.Support.CopulaOptimization
import Copula.CDF.Continuity
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Lower rectangles are continuity sets for every copula, including singular laws. -/
theorem copula_rectangle_frontier_null (C : Copula 2) (u v : I) :
    C.toMeasure (frontier (Iic ![u,v]))=0 := by
  have he : Iic ![u,v]=((fun x : Fin 2 → I => x 0) ⁻¹' Iic u) ∩ ((fun x : Fin 2 → I => x 1) ⁻¹' Iic v) := by
    ext x
    constructor
    · intro h
      exact ⟨h 0,h 1⟩
    · rintro ⟨h0,h1⟩ i
      fin_cases i
      · exact h0
      · exact h1
  have hn (i : Fin 2) (t : I) : C.toMeasure (frontier ((fun x => x i) ⁻¹' Iic t))=0 := by
    apply measure_mono_null ((show Continuous (fun x : Fin 2 → I => x i) from continuous_apply i).frontier_preimage_subset (Iic t))
    apply measure_mono_null (Set.preimage_mono (frontier_Iic_subset t))
    rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton t),C.map_eval,measure_singleton]
  rw [he]
  exact measure_mono_null (frontier_inter_subset _ _) (measure_union_null (measure_mono_null inter_subset_left (hn 0 u)) (measure_mono_null inter_subset_right (hn 1 v)))

theorem copula_cdf_tendsto_of_weak (C : ℕ → Copula 2) (D : Copula 2)
    (hC : Tendsto (fun n => (C n).measure) atTop (𝓝 D.measure)) (u v : I) :
    Tendsto (fun n => (C n).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v])) := by
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hC
    (copula_rectangle_frontier_null D u v)
  exact (ENNReal.tendsto_toReal (measure_ne_top D.toMeasure _)).comp hm

/-- Every sequence has a weak copula subsequential limit, with pointwise CDF convergence. -/
theorem exists_copula_subsequence (C : ℕ → Copula 2) :
    ∃ (D : Copula 2) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => (C (φ n)).measure) atTop (𝓝 D.measure) ∧
      ∀ u v : I, Tendsto (fun n => (C (φ n)).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v])) := by
  obtain ⟨μ,hμ,φ,hφ,hlim⟩ := (isCompact_uniformMarginalMeasures 2).tendsto_subseq
    (fun n => measure_mem_uniformMarginalMeasures (C n))
  let D : Copula 2 := { measure := μ, marginal_eq := fun i => congrArg Subtype.val (hμ i) }
  exact ⟨D,φ,hφ,hlim,copula_cdf_tendsto_of_weak (fun n => C (φ n)) D hlim⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
