/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Vine.Basic
import Copula.Rank.ConditionalMixture

/-! # CDF recursion and independence for simplified C-vines -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The lower-orthant probability of a C-vine step. -/
theorem measure_vineStep_Iic {d : ℕ} (pairs : Fin d → Copula 2) (D : Copula d)
    (u : Fin (d + 1) → I) :
    (vineStep pairs D).toMeasure (Iic u) =
      ∫⁻ r in Iic (u 0), D.toMeasure
        (Iic (fun i => (pairs i).conditionalCDFUnit r (u i.succ))) := by
  rw [toMeasure_vineStep, Measure.map_apply (Vine.measurable_rootTransform pairs)
    measurableSet_Iic, Measure.prod_apply
      ((Vine.measurable_rootTransform pairs) measurableSet_Iic),
    ← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro r
  by_cases hr : r ≤ u 0
  · rw [indicator_of_mem (show r ∈ Iic (u 0) from hr)]
    congr 1
    ext z
    simp only [mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_succ,
      Vine.rootTransform, Fin.cons_zero, Fin.cons_succ,
      conditionalQuantile_le_iff, hr, true_and]
  · rw [indicator_of_notMem (show r ∉ Iic (u 0) from hr)]
    have he : (fun z => (r, z)) ⁻¹' Vine.rootTransform pairs ⁻¹' Iic u = ∅ := by
      ext z
      simp only [mem_preimage, mem_Iic, Pi.le_def, Fin.forall_fin_succ,
        Vine.rootTransform, Fin.cons_zero, hr, false_and, mem_empty_iff_false]
    rw [he, measure_empty]

/-- The usual recursive C-vine CDF formula, valid also for singular pair copulas. -/
theorem cdf_vineStep {d : ℕ} (pairs : Fin d → Copula 2) (D : Copula d)
    (u : Fin (d + 1) → I) :
    (vineStep pairs D).cdf u =
      ∫ r in Iic (u 0), D.cdf (fun i => (pairs i).conditionalCDFUnit r (u i.succ)) := by
  have hm : Measurable (fun r : I =>
      D.cdf (fun i => (pairs i).conditionalCDFUnit r (u i.succ))) := by
    apply D.continuous_cdf.measurable.comp
    apply Measurable.of_eval
    intro i
    exact ((pairs i).measurable_conditionalCDF_left (u i.succ)).subtype_mk
  have he (r : I) : D.toMeasure (Iic (fun i => (pairs i).conditionalCDFUnit r (u i.succ))) =
      ENNReal.ofReal (D.cdf (fun i => (pairs i).conditionalCDFUnit r (u i.succ))) := by
    exact (ofReal_measureReal (measure_ne_top D.toMeasure _)).symm
  rw [cdf, Measure.real, measure_vineStep_Iic]
  simp_rw [he]
  rw [← integral_toReal hm.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r => ENNReal.toReal_ofReal (D.cdf_nonneg _))

/-- With independent root-pair copulas, the root is independent of the residual copula. -/
theorem cdf_vineStep_independence {d : ℕ} (D : Copula d) (u : Fin (d + 1) → I) :
    (vineStep (fun _ => independence 2) D).cdf u =
      (u 0 : ℝ) * D.cdf (fun i => u i.succ) := by
  rw [cdf_vineStep]
  have he : (fun r : I => D.cdf (fun i => (independence 2).conditionalCDFUnit r (u i.succ))) =ᵐ[volume]
      (fun _ => D.cdf (fun i => u i.succ)) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin d => conditionalCDF_independence (u i.succ))]
      with r hr
    congr 1
    funext i
    exact Subtype.ext (hr i)
  rw [integral_congr_ae (ae_restrict_of_ae he), integral_const]
  simp [Measure.real, unitInterval.volume_Iic, ENNReal.toReal_ofReal (u 0).property.1]

@[simp]
theorem vineStep_independence (d : ℕ) :
    vineStep (fun _ : Fin d => independence 2) (independence d) = independence (d + 1) := by
  apply ext_cdf
  intro u
  rw [cdf_vineStep_independence, cdf_independence, cdf_independence, Fin.prod_univ_succ]

namespace CVine

/-- The vine whose pair copulas are all independent. -/
noncomputable def independent : (d : ℕ) → CVine d
  | 0 => .nil
  | d + 1 => .cons (fun _ => independence 2) (independent d)

@[simp]
theorem toCopula_independent (d : ℕ) : (independent d).toCopula = independence d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [independent, ih]

/-- Explicit three-variable pair-copula CDF formula. -/
theorem cdf_triple (A B D : Copula 2) (u v w : I) :
    (triple A B D).toCopula.cdf ![u, v, w] =
      ∫ r in Iic u, D.cdf ![A.conditionalCDFUnit r v, B.conditionalCDFUnit r w] := by
  rw [toCopula_triple, cdf_vineStep]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  congr 1
  funext i
  fin_cases i <;> rfl

end CVine

end ProbabilityTheory.Copula
