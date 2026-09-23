/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/import Copula.Families.Gumbel
import Copula.Families.Nelsen12Limits
import Copula.Rank.Integration


/-! # Gumbel–Hougaard infinite-parameter endpoint

The positive-coordinate CDF is the exponential of a two-coordinate power norm.
Its pointwise limit is comonotonicity, with grounded axes handled separately.
-/
open Filter
open scoped unitInterval Topology
namespace ProbabilityTheory.Copula

/-- Gumbel–Hougaard converges pointwise to the upper Fréchet bound. -/
theorem tendsto_gumbel_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (gumbel (θ z) (hθ z)).cdf u) l
      (𝓝 ((comonotonic 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (z : α) : (gumbel (θ z) (hθ z)).cdf u = 0 :=
      (gumbel (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (z : α) : (gumbel (θ z) (hθ z)).cdf u = 0 :=
      (gumbel (θ z) (hθ z)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (comonotonic 2).cdf u = 0 :=
      (comonotonic 2).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  let x : ℝ := -Real.log (u 0 : ℝ)
  let y : ℝ := -Real.log (u 1 : ℝ)
  have hu' : 0 < (u 0 : ℝ) := lt_of_le_of_ne (u 0).property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv' : 0 < (u 1 : ℝ) := lt_of_le_of_ne (u 1).property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have hx : 0 ≤ x := neg_nonneg.mpr (Real.log_nonpos (u 0).property.1 (u 0).property.2)
  have hy : 0 ≤ y := neg_nonneg.mpr (Real.log_nonpos (u 1).property.1 (u 1).property.2)
  have hp := tendsto_twoTermPowerNorm θ hθ hlim x y hx hy
  have hc : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
  have hlimit := hc.continuousAt.tendsto.comp hp
  have htarget : Real.exp (-max x y) = (comonotonic 2).cdf u := by
    rw [cdf_comonotonic_two]
    rcases le_total (u 0 : ℝ) (u 1 : ℝ) with h | h
    · have hxy : y ≤ x := by
        have hh := Real.log_le_log hu' h
        dsimp [x,y]
        linarith
      rw [max_eq_left hxy, min_eq_left h]
      simp [x, Real.exp_log hu']
    · have hxy : x ≤ y := by
        have hh := Real.log_le_log hv' h
        dsimp [x,y]
        linarith
      rw [max_eq_right hxy, min_eq_right h]
      simp [y, Real.exp_log hv']
  have hformula (z : α) : (gumbel (θ z) (hθ z)).cdf u =
      Real.exp (-((x ^ θ z + y ^ θ z) ^ (θ z)⁻¹)) := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hz, gumbel_cdf_full]
    simp only [hu, hv, or_self, ↓reduceIte]
    rfl
  simpa only [Function.comp_def, hformula, htarget] using hlimit

end ProbabilityTheory.Copula
