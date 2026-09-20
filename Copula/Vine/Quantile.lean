/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Distribution.Quantile
import Copula.Rank.Conditional

/-!
# Conditional quantiles for pair-copula constructions

The generalized inverse of a copula's conditional distribution is jointly
measurable and samples its second coordinate given its first. No density or
strict monotonicity assumption is needed.
-/

open MeasureTheory Set Function
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The conditional CDF, with its value bundled in the unit interval. -/
noncomputable def conditionalCDFUnit (C : Copula 2) (u v : I) : I :=
  ⟨C.conditionalCDF u v, C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩

/-- The generalized conditional quantile of coordinate `1` given coordinate `0`. -/
noncomputable def conditionalQuantile (C : Copula 2) (u t : I) : I :=
  unitQuantile (C.conditionalKernel u) t

theorem conditionalQuantile_le_iff (C : Copula 2) (u t v : I) :
    C.conditionalQuantile u t ≤ v ↔ t ≤ C.conditionalCDFUnit u v :=
  unitQuantile_le_iff _ _ _

theorem monotone_conditionalQuantile (C : Copula 2) (u : I) :
    Monotone (C.conditionalQuantile u) := monotone_unitQuantile _

theorem measurable_conditionalQuantile (C : Copula 2) :
    Measurable (uncurry C.conditionalQuantile) := by
  apply measurable_of_Iic
  intro v
  change MeasurableSet {p : I × I | C.conditionalQuantile p.1 p.2 ≤ v}
  simp_rw [conditionalQuantile_le_iff]
  change MeasurableSet {p : I × I | (p.2 : ℝ) ≤ C.conditionalCDF p.1 v}
  exact measurableSet_le measurable_snd.subtype_val
    ((C.measurable_conditionalCDF_left v).comp measurable_fst)

@[simp]
theorem map_conditionalQuantile (C : Copula 2) (u : I) :
    volume.map (C.conditionalQuantile u) = C.conditionalKernel u := map_unitQuantile _

/-- Conditional inverse-transform sampling recovers the entire bivariate law. -/
theorem map_pair_conditionalQuantile (C : Copula 2) :
    ((volume : Measure I).prod volume).map
      (fun p : I × I => ![p.1, C.conditionalQuantile p.1 p.2]) = C.toMeasure := by
  let H : I × I → I × I := fun p => (p.1, C.conditionalQuantile p.1 p.2)
  have hH : Measurable H := measurable_fst.prodMk C.measurable_conditionalQuantile
  have hgraph : ((volume : Measure I).prod volume).map H =
      (volume : Measure I) ⊗ₘ C.conditionalKernel := by
    ext s hs
    rw [Measure.map_apply hH hs, Measure.prod_apply (hH hs), Measure.compProd_apply hs]
    apply lintegral_congr
    intro u
    rw [← C.map_conditionalQuantile u,
      Measure.map_apply C.measurable_conditionalQuantile.of_uncurry_left
        (measurable_prodMk_left hs)]
    rfl
  have hdis : (volume : Measure I) ⊗ₘ C.conditionalKernel =
      C.toMeasure.map (fun x => (x 0, x 1)) := by
    simpa only [conditionalKernel, C.map_eval] using
      (compProd_map_condDistrib (μ := C.toMeasure)
        (measurable_pi_apply (0 : Fin 2)).aemeasurable
        (measurable_pi_apply (1 : Fin 2)).aemeasurable)
  have h := congrArg (fun μ : Measure (I × I) => μ.map (fun p => ![p.1, p.2]))
    (hgraph.trans hdis)
  rw [Measure.map_map (by fun_prop) hH,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  have he : (fun x : Fin 2 → I => ![x 0, x 1]) = id := by
    funext x i
    fin_cases i <;> rfl
  simpa only [comp_def, H, he, Measure.map_id] using h

/-- Averaging the conditional quantile over an independent uniform root is uniform. -/
theorem map_uncurry_conditionalQuantile (C : Copula 2) :
    ((volume : Measure I).prod volume).map (uncurry C.conditionalQuantile) = volume := by
  have h := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (fun x => x 1))
    C.map_pair_conditionalQuantile
  have hm : Measurable (fun p : I × I => ![p.1, C.conditionalQuantile p.1 p.2]) := by
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_fst
    · exact C.measurable_conditionalQuantile
  rw [Measure.map_map (measurable_pi_apply 1) hm, C.map_eval] at h
  exact h

end ProbabilityTheory.Copula
