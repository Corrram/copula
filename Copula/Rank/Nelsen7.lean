/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Nelsen7
import Copula.Rank.ConditionalCDF
import Copula.Rank.Chatterjee
import Copula.Rank.Integration

/-! # Conditional CDF and Chatterjee's xi of Nelsen's seventh family

The formula includes the singular endpoint at zero and independence at one.
No density assumption is made.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen7_height_nonneg (θ v : I) :
    0 ≤ (θ : ℝ) * v + 1 - θ := by
  nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]

/-- The threshold separating the zero and positive parts of a conditional CDF. -/
noncomputable def nelsen7Threshold (θ v : I) : I :=
  ⟨(1 - (θ : ℝ)) * (1 - (v : ℝ)) / ((θ : ℝ) * v + 1 - θ), by
    have hh := nelsen7_height_nonneg θ v
    constructor
    · exact div_nonneg (mul_nonneg (sub_nonneg.mpr θ.property.2)
        (sub_nonneg.mpr v.property.2)) hh
    · by_cases hz : (θ : ℝ) * v + 1 - θ = 0
      · simp [hz]
      · apply (div_le_one (lt_of_le_of_ne hh (Ne.symm hz))).mpr
        nlinarith [v.property.1]⟩

/-- A version of the conditional CDF of the second coordinate given the first. -/
noncomputable def nelsen7ConditionalCDF (θ u v : I) : ℝ :=
  (Ioi (nelsen7Threshold θ v)).indicator (fun _ => (θ : ℝ) * v + 1 - θ) u

theorem integrable_nelsen7ConditionalCDF (θ v : I) :
    Integrable (fun u => nelsen7ConditionalCDF θ u v) :=
  (integrable_const _).indicator measurableSet_Ioi

theorem integral_Iic_nelsen7ConditionalCDF (θ u v : I) :
    (∫ t in Iic u, nelsen7ConditionalCDF θ t v) = (nelsen7 θ).cdf ![u, v] := by
  unfold nelsen7ConditionalCDF
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  simp only [Ioi_inter_Iic, integral_const, Measure.real, Measure.restrict_apply_univ,
    unitInterval.volume_Ioc, smul_eq_mul]
  rw [cdf_nelsen7]
  have hh := nelsen7_height_nonneg θ v
  have hc : ((θ : ℝ) * v + 1 - θ) * (nelsen7Threshold θ v : ℝ) =
      (1 - (θ : ℝ)) * (1 - (v : ℝ)) := by
    by_cases hz : (θ : ℝ) * v + 1 - θ = 0
    · have ht : (θ : ℝ) = 1 := by
        nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]
      rw [hz, ht]
      ring
    · dsimp [nelsen7Threshold]
      field_simp
  rw [ENNReal.toReal_ofReal', max_mul_of_nonneg _ _ hh, zero_mul, max_comm]
  congr 1
  nlinarith

theorem conditionalCDF_nelsen7 (θ v : I) :
    (fun u => (nelsen7 θ).conditionalCDF u v) =ᵐ[volume]
      fun u => nelsen7ConditionalCDF θ u v := by
  apply conditionalCDF_ae_eq_of_integral (hf := integrable_nelsen7ConditionalCDF θ v)
  · intro u
    exact indicator_nonneg (fun _ _ => nelsen7_height_nonneg θ v) _
  · exact fun u => integral_Iic_nelsen7ConditionalCDF θ u v

theorem integral_nelsen7ConditionalCDF_sq (θ v : I) :
    (∫ u : I, nelsen7ConditionalCDF θ u v ^ 2) =
      ((θ : ℝ) * v + 1 - θ) * (v : ℝ) := by
  have he : (fun u => nelsen7ConditionalCDF θ u v ^ 2) =
      fun u => ((θ : ℝ) * v + 1 - θ) * nelsen7ConditionalCDF θ u v := by
    funext u
    unfold nelsen7ConditionalCDF
    by_cases h : u ∈ Ioi (nelsen7Threshold θ v) <;> simp [h, sq]
  rw [he, integral_const_mul]
  have hi := integral_Iic_nelsen7ConditionalCDF θ 1 v
  have hI : Iic (1 : I) = univ := by
    ext x
    simp only [mem_Iic, mem_univ, iff_true]
    exact x.property.2
  rw [hI, Measure.restrict_univ] at hi
  simpa using congrArg (fun x : ℝ => ((θ : ℝ) * v + 1 - θ) * x) hi

/-- Table 6 of Ansari--Rockel, on the full closed parameter interval. -/
theorem chatterjeeXi_nelsen7 (θ : I) : (nelsen7 θ).chatterjeeXi = 1 - (θ : ℝ) := by
  have he (v : I) : (∫ u : I, (nelsen7 θ).conditionalCDF u v ^ 2) =
      (θ : ℝ) * (v : ℝ) ^ 2 + (1 - (θ : ℝ)) * (v : ℝ) := by
    calc
      _ = ∫ u : I, nelsen7ConditionalCDF θ u v ^ 2 := by
        apply integral_congr_ae
        filter_upwards [conditionalCDF_nelsen7 θ v] with u hu
        rw [hu]
      _ = _ := by rw [integral_nelsen7ConditionalCDF_sq]; ring
  unfold chatterjeeXi
  simp_rw [he]
  rw [integral_add, integral_const_mul, integral_const_mul, integral_unit_pow, integral_unit_id]
  · norm_num; ring
  all_goals exact integrable_continuous_unit volume (by fun_prop)

end ProbabilityTheory.Copula
