/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.TailDependence.Basic
import Copula.Families.Frechet

/-! # Tail-dependence benchmarks and mixture families -/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

theorem hasLowerTailDependence_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (fgm θ hθ).HasLowerTailDependence 0 := by
  have he : (fgm θ hθ).lowerTailRatio = fun t : I =>
      (t : ℝ) * (1 + θ * (1 - (t : ℝ)) * (1 - (t : ℝ))) := by
    funext t
    simp only [lowerTailRatio, diagonal, cdf_fgm, Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF]
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · field_simp
  unfold HasLowerTailDependence
  rw [he]
  have hc : Continuous (fun t : I => (t : ℝ) * (1 + θ * (1 - (t : ℝ)) * (1 - (t : ℝ)))) :=
    by fun_prop
  simpa using (hc.tendsto (0 : I)).mono_left
    (show 𝓝[>] (0 : I) ≤ 𝓝 (0 : I) from nhdsWithin_le_nhds)

theorem hasUpperTailDependence_fgm (θ : ℝ) (hθ : |θ| ≤ 1) :
    (fgm θ hθ).HasUpperTailDependence 0 :=
  ((isRadiallySymmetric_fgm θ hθ).hasUpperTailDependence_iff 0).2 (hasLowerTailDependence_fgm θ hθ)

theorem hasLowerTailDependence_independence : (independence 2).HasLowerTailDependence 0 := by
  simpa only [fgm_zero] using hasLowerTailDependence_fgm 0 (by norm_num)

theorem hasUpperTailDependence_independence : (independence 2).HasUpperTailDependence 0 := by
  simpa only [fgm_zero] using hasUpperTailDependence_fgm 0 (by norm_num)

theorem hasLowerTailDependence_comonotonic : (comonotonic 2).HasLowerTailDependence 1 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
  simp only [lowerTailRatio, diagonal_comonotonic]
  exact (div_self (ne_of_gt (show (0 : ℝ) < t from ht))).symm

theorem hasUpperTailDependence_comonotonic : (comonotonic 2).HasUpperTailDependence 1 :=
  (isRadiallySymmetric_comonotonic.hasUpperTailDependence_iff 1).2 hasLowerTailDependence_comonotonic

theorem hasLowerTailDependence_countermonotonic : countermonotonic.HasLowerTailDependence 0 := by
  apply tendsto_const_nhds.congr'
  have hh : ∀ᶠ t : I in 𝓝[>] (0 : I), t < unitHalf :=
    nhdsWithin_le_nhds (gt_mem_nhds (show (0 : I) < unitHalf by change (0 : ℝ) < 1 / 2; norm_num))
  filter_upwards [hh] with t ht
  simp only [lowerTailRatio, diagonal_countermonotonic]
  have hr : (t : ℝ) < 1 / 2 := ht
  rw [max_eq_left (by linarith), zero_div]

theorem hasUpperTailDependence_countermonotonic : countermonotonic.HasUpperTailDependence 0 :=
  (isRadiallySymmetric_countermonotonic.hasUpperTailDependence_iff 0).2
    hasLowerTailDependence_countermonotonic

theorem hasLowerTailDependence_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).HasLowerTailDependence a := by
  have h := ((hasLowerTailDependence_comonotonic.const_mul a).add
    (hasLowerTailDependence_countermonotonic.const_mul b)).add
      (hasLowerTailDependence_independence.const_mul (1 - a - b))
  have he : (fun t : I => a * (comonotonic 2).lowerTailRatio t +
      b * countermonotonic.lowerTailRatio t + (1 - a - b) * (independence 2).lowerTailRatio t) =
      (frechet a b ha hb hab).lowerTailRatio := by
    funext t
    simp only [lowerTailRatio, diagonal, cdf_frechet]
    ring
  change Tendsto (frechet a b ha hb hab).lowerTailRatio (𝓝[>] (0 : I)) (𝓝 a)
  simpa only [he, mul_one, mul_zero, add_zero] using h

theorem isRadiallySymmetric_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).IsRadiallySymmetric := by
  rw [isRadiallySymmetric_iff]
  intro u v
  simp only [cdf_frechet]
  rw [(isRadiallySymmetric_iff _).1 isRadiallySymmetric_comonotonic u v,
    (isRadiallySymmetric_iff _).1 isRadiallySymmetric_countermonotonic u v,
    (isRadiallySymmetric_iff _).1 isRadiallySymmetric_independence u v]
  ring

theorem hasUpperTailDependence_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).HasUpperTailDependence a :=
  ((isRadiallySymmetric_frechet a b ha hb hab).hasUpperTailDependence_iff a).2
    (hasLowerTailDependence_frechet a b ha hb hab)

theorem hasLowerTailDependence_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).HasLowerTailDependence (θ ^ 2 * (1 + θ) / 2) :=
  hasLowerTailDependence_frechet _ _ _ _ _

theorem hasUpperTailDependence_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).HasUpperTailDependence (θ ^ 2 * (1 + θ) / 2) :=
  hasUpperTailDependence_frechet _ _ _ _ _

end ProbabilityTheory.Copula
