/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Transform.Power
import Copula.CDF.Extensionality
import Mathlib.MeasureTheory.Measure.Prod

/-! # Products of copulas with coordinatewise power weights

For independent vectors `U ~ C`, `V ~ D`, the coordinatewise maximum of
`Uᵢ^(1/aᵢ)` and `Vᵢ^(1/(1-aᵢ))` is uniform in each coordinate. Zero weights
are represented by a constant zero sample, so both endpoints are included.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The maximum of two independent vectors with complementary power marginal laws. -/
noncomputable def maxProductPoint (a : Fin d → I) (p : (Fin d → I) × (Fin d → I))
    (i : Fin d) : I := max (powerSample (a i) (p.1 i)) (powerSample (unitInterval.symm (a i)) (p.2 i))

@[fun_prop] theorem measurable_maxProductPoint (a : Fin d → I) :
    Measurable (maxProductPoint a) := by
  unfold maxProductPoint
  fun_prop

private theorem maxProductPoint_eval_preimage (a : Fin d → I) (i : Fin d) (t : I) :
    (fun p => maxProductPoint a p i) ⁻¹' Iic t =
      {x | x i ≤ unitPower t (a i) (a i).property.1} ×ˢ
      {y | y i ≤ unitPower t (unitInterval.symm (a i)) (unitInterval.symm (a i)).property.1} := by
  ext p
  simp only [mem_preimage, mem_Iic, maxProductPoint, max_le_iff, powerSample_le_iff,
    mem_prod, mem_ofPred_eq]

/-- The Liebscher power-product construction for two copulas. -/
noncomputable def maxProduct (C D : Copula d) (a : Fin d → I) : Copula d :=
  ofMap ⟨C.toMeasure.prod D.toMeasure, inferInstance⟩ (maxProductPoint a)
    (measurable_maxProductPoint a) (by
      intro i
      change (C.toMeasure.prod D.toMeasure).map (fun p => maxProductPoint a p i) = volume
      apply Measure.ext_of_Iic
      intro t
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
        maxProductPoint_eval_preimage, Measure.prod_prod]
      rw [C.measure_eval_le, D.measure_eval_le, unitInterval.volume_Iic]
      simp only [coe_unitPower]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg t.property.1 _)]
      congr 1
      change (t : ℝ) ^ (a i : ℝ) * (t : ℝ) ^ (1 - (a i : ℝ)) = (t : ℝ)
      by_cases ht : (t : ℝ) = 0
      · by_cases ha : (a i : ℝ) = 0
        · simp [ht, ha]
        · simp [ht, Real.zero_rpow ha]
      · rw [← Real.rpow_add (lt_of_le_of_ne t.property.1 (Ne.symm ht)),
          add_sub_cancel, Real.rpow_one])

theorem cdf_maxProduct (C D : Copula d) (a u : Fin d → I) :
    (maxProduct C D a).cdf u =
      C.cdf (fun i => unitPower (u i) (a i) (a i).property.1) *
      D.cdf (fun i => unitPower (u i) (unitInterval.symm (a i)) (unitInterval.symm (a i)).property.1) := by
  have he : maxProductPoint a ⁻¹' Iic u =
      Iic (fun i => unitPower (u i) (a i) (a i).property.1) ×ˢ
      Iic (fun i => unitPower (u i) (unitInterval.symm (a i)) (unitInterval.symm (a i)).property.1) := by
    ext p
    simp only [mem_preimage, mem_Iic, Pi.le_def, maxProductPoint, max_le_iff,
      powerSample_le_iff, mem_prod, forall_and]
  change ((C.toMeasure.prod D.toMeasure).map (maxProductPoint a)).real (Iic u) = _
  rw [map_measureReal_apply (measurable_maxProductPoint a) measurableSet_Iic, he,
    Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  rfl

@[simp] theorem maxProduct_zero (C D : Copula d) : maxProduct C D (fun _ => 0) = D := by
  apply ext_cdf
  intro u
  simp [cdf_maxProduct]

@[simp] theorem maxProduct_one (C D : Copula d) : maxProduct C D (fun _ => 1) = C := by
  apply ext_cdf
  intro u
  simp [cdf_maxProduct]

end ProbabilityTheory.Copula
