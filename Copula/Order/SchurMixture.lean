/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Schur
import Copula.Rank.ConditionalMixture

/-! # Mixtures and Schur order

Mixtures preserve a common Schur upper bound. In particular, adding an
independent component reduces predictability in the directional Schur order.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem integral_convex_conditionalCDF_mix_le (C D : Copula 2) (a v : I)
    {φ : ℝ → ℝ} (hc : Continuous φ) (hv : ConvexOn ℝ (Icc 0 1) φ) :
    (∫ u : I, φ ((C.mix D a).conditionalCDF u v)) ≤
      (a : ℝ) * (∫ u : I, φ (C.conditionalCDF u v)) +
        (1 - (a : ℝ)) * (∫ u : I, φ (D.conditionalCDF u v)) := by
  have h := integral_mono_ae ((C.mix D a).integrable_comp_conditionalCDF v hc)
    (((C.integrable_comp_conditionalCDF v hc).const_mul (a : ℝ)).add
      ((D.integrable_comp_conditionalCDF v hc).const_mul (1 - (a : ℝ)))) (by
      filter_upwards [conditionalCDF_mix C D a v] with u hu
      rw [hu]
      exact hv.2 ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩
        ⟨D.conditionalCDF_nonneg u v, D.conditionalCDF_le_one u v⟩
        a.property.1 (sub_nonneg.mpr a.property.2) (by ring))
  simp only [Pi.add_apply] at h
  rwa [integral_add ((C.integrable_comp_conditionalCDF v hc).const_mul (a : ℝ))
      ((D.integrable_comp_conditionalCDF v hc).const_mul (1 - (a : ℝ))),
    integral_const_mul, integral_const_mul] at h

theorem SchurLE.mix {C D E : Copula 2} (hC : C.SchurLE E) (hD : D.SchurLE E) (a : I) :
    (C.mix D a).SchurLE E := by
  intro v φ hc hv
  apply (integral_convex_conditionalCDF_mix_le C D a v hc hv).trans
  have h := add_le_add (mul_le_mul_of_nonneg_left (hC v φ hc hv) a.property.1)
    (mul_le_mul_of_nonneg_left (hD v φ hc hv) (sub_nonneg.mpr a.property.2))
  convert h using 1
  ring

theorem schurLE_mix_independence (C : Copula 2) (a : I) :
    (C.mix (independence 2) a).SchurLE C := (SchurLE.refl C).mix (schurLE_independence C) a

/-- Retaining a larger weight on a fixed copula increases predictability. -/
theorem schurLE_mix_independence_mono (C : Copula 2) {a b : I} (hab : a ≤ b) :
    (C.mix (independence 2) a).SchurLE (C.mix (independence 2) b) := by
  by_cases hb : b = 0
  · have ha : a = 0 := le_antisymm (hab.trans_eq hb) a.property.1
    simp [ha, hb, SchurLE.refl]
  have hbp : (0 : ℝ) < b := lt_of_le_of_ne b.property.1
    (Ne.symm (fun h => hb (Subtype.ext h)))
  let r : I := ⟨(a : ℝ) / (b : ℝ), div_nonneg a.property.1 hbp.le,
    (div_le_one hbp).2 hab⟩
  have he : (C.mix (independence 2) b).mix (independence 2) r = C.mix (independence 2) a := by
    apply ext_cdf
    intro u
    simp only [cdf_mix]
    dsimp [r]
    field_simp [hbp.ne']
    ring
  rw [← he]
  exact schurLE_mix_independence _ r

end ProbabilityTheory.Copula
