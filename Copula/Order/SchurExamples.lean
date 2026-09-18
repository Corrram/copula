/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Schur
import Copula.Order.Rank
import Copula.Dependence.Conditional

/-! # Minimality and contrasting examples for Schur order -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The least Schur equivalence class contains only independence. -/
theorem schurLE_independence_iff (C : Copula 2) :
    C.SchurLE (independence 2) ↔ C = independence 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ SchurLE.refl _⟩
  have hc (t : I) : (fun u : I => C.conditionalCDF u t) =ᵐ[volume] fun _ => (t : ℝ) := by
    have hs := h t (fun z => z ^ 2) (by fun_prop)
      ((convexOn_pow (𝕜 := ℝ) 2).subset (fun _ hx => hx.1) (convex_Icc 0 1))
    have hi : (∫ u : I, (independence 2).conditionalCDF u t ^ 2) = (t : ℝ) ^ 2 := by
      calc
        _ = ∫ _ : I, (t : ℝ) ^ 2 := integral_congr_ae (by
          filter_upwards [conditionalKernel_independence] with u hu
          simp [conditionalCDF, hu, Measure.real, unitInterval.volume_Iic,
            ENNReal.toReal_ofReal t.property.1])
        _ = _ := by simp
    rw [hi] at hs
    have hz : (∫ u : I, (C.conditionalCDF u t - (t : ℝ)) ^ 2) = 0 := by
      rw [C.integral_conditionalCDF_centered_sq]
      have hn : 0 ≤ ∫ u : I, (C.conditionalCDF u t - (t : ℝ)) ^ 2 :=
        integral_nonneg (fun u : I => sq_nonneg (C.conditionalCDF u t - (t : ℝ)))
      rw [C.integral_conditionalCDF_centered_sq] at hn
      linarith
    have ha := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun u : I => sq_nonneg (C.conditionalCDF u t - (t : ℝ)))
      (C.integrable_comp_conditionalCDF t (φ := fun z => (z - (t : ℝ)) ^ 2) (by fun_prop))).1 hz
    filter_upwards [ha] with u hu
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)
  apply ext_cdf
  intro u
  have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  rw [← he, C.cdf_eq_integral_conditionalCDF]
  rw [setIntegral_congr_ae measurableSet_Iic (by
    filter_upwards [hc (u 1)] with t ht using fun _ => ht)]
  simp [cdf_independence, Fin.prod_univ_two, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal (u 0).property.1]

theorem schurLE_not_antisymmetric :
    ¬ ∀ C D : Copula 2, C.SchurLE D → D.SchurLE C → C = D := by
  intro h
  have he := congrArg blomqvistBeta
    (h (comonotonic 2) countermonotonic (schurLE_countermonotonic _) (schurLE_comonotonic _))
  norm_num at he

/-- Concordance comparison does not imply Schur comparison. -/
theorem not_schurLE_countermonotonic_independence :
    ¬ countermonotonic.SchurLE (independence 2) := by
  intro h
  have hi := h.chatterjeeXi_le
  norm_num at hi

/-- Schur comparison does not imply concordance comparison. -/
theorem not_lowerOrthantLE_comonotonic_countermonotonic :
    ¬ (comonotonic 2).LowerOrthantLE countermonotonic := by
  intro h
  have hi := h.blomqvistBeta_le
  norm_num at hi

end ProbabilityTheory.Copula
