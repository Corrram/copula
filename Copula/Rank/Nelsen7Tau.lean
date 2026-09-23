/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Nelsen7Rho
import Copula.Rank.KendallConditionalProduct
import Copula.Rank.Region.XiRho.Support.ClampedRhoOptimization

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

set_option maxHeartbeats 1000000

namespace ProbabilityTheory.Copula

private def n7height (θ v : I) : ℝ := (θ : ℝ) * v + 1 - θ

private theorem n7height_nonneg (θ v : I) : 0 ≤ n7height θ v := by
  dsimp [n7height]
  nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]

private theorem n7height_mul_threshold (θ v : I) :
    n7height θ v * (Copula.nelsen7Threshold θ v : ℝ) =
      (1 - (θ : ℝ)) * (1 - (v : ℝ)) := by
  by_cases hz : n7height θ v = 0
  · have ht : (θ : ℝ) = 1 := by
      dsimp [n7height] at hz
      nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]
    rw [hz, ht]
    ring
  · dsimp [n7height, Copula.nelsen7Threshold] at *
    field_simp

private theorem n7cross (θ u v : I) :
    n7height θ v * ((u : ℝ) - (Copula.nelsen7Threshold θ v : ℝ)) =
      n7height θ u * ((v : ℝ) - (Copula.nelsen7Threshold θ u : ℝ)) := by
  have hv := n7height_mul_threshold θ v
  have hu := n7height_mul_threshold θ u
  dsimp [n7height] at *
  nlinarith

private theorem n7conditional_product (θ u v : I) :
    Copula.nelsen7ConditionalCDF θ u v * Copula.nelsen7ConditionalCDF θ v u =
      n7height θ u * Copula.nelsen7ConditionalCDF θ u v := by
  by_cases huv : u ∈ Ioi (Copula.nelsen7Threshold θ v)
  · by_cases hvu : v ∈ Ioi (Copula.nelsen7Threshold θ u)
    · simp [Copula.nelsen7ConditionalCDF, huv, hvu, n7height]
      ring
    · have hvzero : n7height θ v = 0 := by
        by_contra hn
        have hvpos : 0 < n7height θ v := lt_of_le_of_ne (n7height_nonneg θ v) (Ne.symm hn)
        have hdiff : 0 < (u : ℝ) - (Copula.nelsen7Threshold θ v : ℝ) :=
          sub_pos.mpr huv
        have hdiff' : (v : ℝ) - (Copula.nelsen7Threshold θ u : ℝ) ≤ 0 :=
          sub_nonpos.mpr (le_of_not_gt hvu)
        have hpos := mul_pos hvpos hdiff
        have hle := mul_nonpos_of_nonneg_of_nonpos (n7height_nonneg θ u) hdiff'
        linarith [n7cross θ u v]
      simp [Copula.nelsen7ConditionalCDF, huv, hvu, n7height,
        show (θ : ℝ) * v + 1 - θ = 0 from hvzero]
  · simp [Copula.nelsen7ConditionalCDF, huv]


private theorem n7conditional_measurable (θ : I) :
    Measurable (fun p : I × I => Copula.nelsen7ConditionalCDF θ p.1 p.2) := by
  have ht : Measurable (fun p : I × I => Copula.nelsen7Threshold θ p.2) := by
    unfold Copula.nelsen7Threshold
    fun_prop
  have hs : MeasurableSet {p : I × I | Copula.nelsen7Threshold θ p.2 < p.1} :=
    measurableSet_lt ht measurable_fst
  have he : (fun p : I × I => Copula.nelsen7ConditionalCDF θ p.1 p.2) =
      fun p => if Copula.nelsen7Threshold θ p.2 < p.1 then n7height θ p.2 else 0 := by
    funext p
    simp [Copula.nelsen7ConditionalCDF, n7height, Set.indicator]
  rw [he]
  have hh : Measurable (fun p : I × I => n7height θ p.2) := by
    dsimp [n7height]
    fun_prop
  exact hh.ite hs measurable_const

/-- Nelsen 7's tau is an affine transform of its rho at the same parameter. -/
theorem nelsen7_tau_rho (θ : I) :
    (Copula.nelsen7 θ).kendallTau =
      -1 + (θ : ℝ) / 3 * ((Copula.nelsen7 θ).spearmanRho + 3) := by
  let C := Copula.nelsen7 θ
  have hCt : C.transpose = C := (Copula.isArchimedean_nelsen7 θ).isExchangeable
  have hf : ∀ᵐ v : I, ∀ᵐ u : I,
      C.conditionalCDF u v = Copula.nelsen7ConditionalCDF θ u v :=
    Filter.Eventually.of_forall (fun v => Copula.conditionalCDF_nelsen7 θ v)
  have hr : ∀ᵐ v : I, ∀ᵐ u : I,
      C.conditionalCDF v u = Copula.nelsen7ConditionalCDF θ v u := by
    have hm : MeasurableSet {p : I × I |
        C.conditionalCDF p.2 p.1 = Copula.nelsen7ConditionalCDF θ p.2 p.1} :=
      measurableSet_eq_fun C.measurable_conditionalCDF
        ((n7conditional_measurable θ).comp measurable_swap)
    exact (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u = Copula.nelsen7ConditionalCDF θ v u) hm).mp
        (Filter.Eventually.of_forall (fun u => Copula.conditionalCDF_nelsen7 θ u))
  have hsection (v : I) :
      (∫ u : I, n7height θ u * C.conditionalCDF u v) =
        (v : ℝ) - (θ : ℝ) * (∫ u : I, (1 - (u : ℝ)) * C.conditionalCDF u v) := by
    have he : (fun u : I => n7height θ u * C.conditionalCDF u v) =
        fun u => C.conditionalCDF u v -
          (θ : ℝ) * ((1 - (u : ℝ)) * C.conditionalCDF u v) := by
      funext u
      dsimp [n7height]
      ring
    rw [he, integral_sub (C.integrable_conditionalCDF v)
      ((RankRegion.XiRho.Support.integrable_rho_section C v).const_mul _),
      integral_const_mul, C.integral_conditionalCDF]
  have hcross :
      (∫ u : I, ∫ v : I, C.conditionalCDF u v * C.conditionalCDF v u) =
        ∫ v : I, ∫ u : I, n7height θ u * C.conditionalCDF u v := by
    have hi : Integrable (fun p : I × I =>
        C.conditionalCDF p.1 p.2 * C.conditionalCDF p.2 p.1) := by
      simpa only [hCt] using crossConditional_integrable C
    rw [integral_integral_swap hi]
    apply integral_congr_ae
    filter_upwards [hf, hr] with v hv hv'
    apply integral_congr_ae
    filter_upwards [hv, hv'] with u hu hu'
    rw [hu, hu', n7conditional_product θ u v]
  change C.kendallTau = _
  rw [kendallTau_conditional_product, hCt, hcross]
  simp_rw [hsection]
  rw [integral_sub (Copula.integrable_continuous_unit volume continuous_subtype_val)
    ((RankRegion.XiRho.Support.integrable_rho_profile C).const_mul _),
    integral_const_mul, Copula.integral_unit_id,
    RankRegion.XiRho.Support.rho_conditional_formula]
  ring


/-- Table 6's exact Nelsen 7 Kendall-tau formula at interior parameters. -/
theorem nelsen7_tau_interior (θ : I) (h0 : (0 : ℝ) < θ) (h1 : (θ : ℝ) < 1) :
    (Copula.nelsen7 θ).kendallTau =
      2 - 2 / (θ : ℝ) -
        2 * ((θ : ℝ) - 1) ^ 2 * Real.log (1 - (θ : ℝ)) / (θ : ℝ) ^ 2 := by
  rw [nelsen7_tau_rho, nelsen7_rho_interior θ h0 h1]
  have hn : (θ : ℝ) ≠ 0 := ne_of_gt h0
  field_simp
  ring

/-- Table 6's exact Nelsen 7 Kendall-tau formula on the full closed interval. -/
theorem nelsen7_tau (θ : I) :
    (Copula.nelsen7 θ).kendallTau =
      if θ = 0 then -1 else if θ = 1 then 0 else
        2 - 2 / (θ : ℝ) -
          2 * ((θ : ℝ) - 1) ^ 2 * Real.log (1 - (θ : ℝ)) / (θ : ℝ) ^ 2 := by
  by_cases h0 : θ = 0
  · subst θ
    simp
  by_cases h1 : θ = 1
  · subst θ
    simp
  have hp : (0 : ℝ) < θ :=
    lt_of_le_of_ne θ.property.1 (Ne.symm (fun hz => h0 (Subtype.ext hz)))
  have hlt : (θ : ℝ) < 1 :=
    lt_of_le_of_ne θ.property.2 (fun hz => h1 (Subtype.ext hz))
  simpa [h0, h1] using nelsen7_tau_interior θ hp hlt

end ProbabilityTheory.Copula
