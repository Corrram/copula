/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Chatterjee
import Copula.Dependence.Conditional
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # The bridge from conditional CDFs to the classical partial derivative -/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- The CDF section extended constantly outside the unit interval. -/
noncomputable def cdfSection (C : Copula 2) (v : I) (u : ℝ) : ℝ :=
  C.cdf ![projIcc 0 1 zero_le_one u, v]

theorem integral_Iic_unit_eq_interval (f : I → ℝ) (u : I) :
    (∫ t in Iic u, f t) =
      ∫ t in (0 : ℝ)..(u : ℝ), f (projIcc 0 1 zero_le_one t) := by
  have h := unitInterval.measurePreserving_coe.setIntegral_preimage_emb
    unitInterval.measurableEmbedding_coe
    (fun t => f (projIcc 0 1 zero_le_one t)) (Iic (u : ℝ))
  have hs : Iic (u : ℝ) ∩ Icc 0 1 = Icc 0 (u : ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨ht, h0, _⟩; exact ⟨h0, ht⟩
    · rintro ⟨h0, ht⟩; exact ⟨ht, h0, ht.trans u.property.2⟩
  simpa only [projIcc_val, show ((↑) : I → ℝ) ⁻¹' Iic (u : ℝ) = Iic u from rfl,
    Measure.restrict_restrict measurableSet_Iic, hs,
    intervalIntegral.integral_of_le u.property.1, integral_Icc_eq_integral_Ioc] using h

/-- For each threshold, the classical first partial derivative equals the conditional
CDF almost everywhere in the conditioning coordinate. No density is required. -/
theorem conditionalCDF_eq_deriv (C : Copula 2) (v : I) :
    (fun u : I => C.conditionalCDF u v) =ᵐ[volume]
      fun u : I => deriv (cdfSection C v) (u : ℝ) := by
  let f : ℝ → ℝ := fun t => C.conditionalCDF (projIcc 0 1 zero_le_one t) v
  have hi : IntegrableOn f (Icc 0 1) := by
    apply (unitInterval.measurePreserving_coe.integrable_comp_emb
      unitInterval.measurableEmbedding_coe).1
    simpa [Function.comp_def, f] using C.integrable_conditionalCDF v
  have hf : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 hi
  have ha := ae_restrict_of_ae (s := Icc (0 : ℝ) 1) hf.ae_hasDerivAt_integral
  rw [← unitInterval.measurePreserving_coe.map_eq] at ha
  have hu := ae_of_ae_map measurable_subtype_coe.aemeasurable ha
  have h0 : ∀ᵐ u : I, u ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ u : I, u ≠ 1 := by simp [ae_iff]
  filter_upwards [hu, h0, h1] with u hu hu0 hu1
  have hu0' : 0 < (u : ℝ) := by
    have : (0 : I) < u := lt_of_le_of_ne u.property.1 (Ne.symm hu0)
    exact this
  have hu1' : (u : ℝ) < 1 := by
    have : u < (1 : I) := lt_of_le_of_ne u.property.2 hu1
    exact this
  have hd := hu (by simp) 0 (by simp)
  have he : cdfSection C v =ᶠ[𝓝 (u : ℝ)] (fun x => ∫ t in (0 : ℝ)..x, f t) := by
    filter_upwards [Ioo_mem_nhds hu0' hu1'] with x hx
    let t : I := ⟨x, hx.1.le, hx.2.le⟩
    have ht := integral_Iic_unit_eq_interval (fun s => C.conditionalCDF s v) t
    rw [← C.cdf_eq_integral_conditionalCDF] at ht
    simpa [cdfSection, f, t, projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩] using ht
  simpa [f] using (hd.congr_of_eventuallyEq he).deriv.symm

/-- Chatterjee's population coefficient in the derivative convention of the articles. -/
theorem chatterjeeXi_eq_integral_deriv (C : Copula 2) :
    C.chatterjeeXi =
      6 * (∫ v : I, ∫ u : I, deriv (cdfSection C v) (u : ℝ) ^ 2) - 2 := by
  unfold Copula.chatterjeeXi
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun v => integral_congr_ae (by
    filter_upwards [conditionalCDF_eq_deriv C v] with u hu
    rw [hu])

end ProbabilityTheory.Copula
