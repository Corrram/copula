/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.TailDependence
import Copula.Families.Nelsen7
import Copula.Families.NelsenTable.N10
import Copula.Families.NelsenTable.N11
import Copula.Families.NelsenTable.N13
import Copula.Families.NelsenTable.N16
import Copula.Families.NelsenTable.N17
import Copula.Families.NelsenTable.N22
import Copula.TailDependence.Examples

/-! # Upper tail dependence of families of Nelsen's Table 4.1

Nelsen, *An Introduction to Copulas*, second edition, Corollary 5.4.3: if the inverse generator
`ψ` has a finite nonzero right derivative at `0` (equivalently `φ'(1⁻) ≠ 0`), then `δ'(1⁻) = 2`
and `λ_U = 0` (`BivariateGenerator.hasUpperTailDependence_zero_of_hasDerivWithinAt`). This file
applies that criterion to the families of Table 4.1 whose generator has `φ'(1) ∈ (−∞, 0)`:

| family | `ψ` near `0` | `ψ'(0)` |
| --- | --- | --- |
| 7 (`0 < θ ≤ 1`) | `(e^{−s} + θ − 1)/θ` | `−1/θ` |
| 10 | `(2/(e^s + 1))^{1/θ}` | `−1/(2θ)` |
| 11 | `(2 − e^s)^{1/θ}` | `−1/θ` |
| 13 | `exp(1 − (1 + s)^{1/θ})` | `−1/θ` |
| 16 | `(1 − θ − s + √((1 − θ − s)² + 4θ))/2` | `−1/(1 + θ)` |
| 17 | `(1 + (2^{−θ} − 1)e^{−s})^{−1/θ} − 1` | `2(1 − 2^θ)/θ` |
| 22 | `(1 − sin s)^{1/θ}` | `−1/θ` |

so each of these families has `λ_U = 0` (for family 7 also at `θ = 0`, where it is `W`).
The helper `BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq` reduces the criterion to
an explicit formula valid on some `[0, ε)`.
-/

open Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- Corollary 5.4.3 with an explicit local formula: if `ψ = F` on a right neighbourhood of `0`
and `F'(0) = d ≠ 0`, then `λ_U = 0`. -/
theorem BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq (g : BivariateGenerator)
    {F : ℝ → ℝ} {d : ℝ} (hF : ∀ᶠ s in 𝓝[≥] (0 : ℝ), g.toFun s = F s) (hd : HasDerivAt F d 0)
    (hd0 : d ≠ 0) : g.copula.HasUpperTailDependence 0 :=
  g.hasUpperTailDependence_zero_of_hasDerivWithinAt
    (hd.hasDerivWithinAt.congr_of_eventuallyEq hF (hF.self_of_nhdsWithin (mem_Ici.mpr le_rfl))) hd0

private theorem eventually_lt_nhdsGE {a : ℝ} (ha : 0 < a) : ∀ᶠ s in 𝓝[≥] (0 : ℝ), s < a :=
  nhdsWithin_le_nhds (Iio_mem_nhds ha)

/-- Nelsen's family 7 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen7 (θ : I) : (nelsen7 θ).HasUpperTailDependence 0 := by
  by_cases hθ : θ = 0
  · rw [hθ, nelsen7_zero]
    exact hasUpperTailDependence_countermonotonic
  set a : ℝ := (θ : ℝ) with ha_def
  have ha : 0 < a := lt_of_le_of_ne θ.property.1 (Ne.symm (fun hz => hθ (Subtype.ext hz)))
  unfold nelsen7
  rw [dite_eq_right_of_eq_false (eq_false hθ)]
  have hcont : Continuous (fun s : ℝ => (Real.exp (-s) + a - 1) / a) := by fun_prop
  have hpos : ∀ᶠ s in 𝓝[≥] (0 : ℝ), 0 < (Real.exp (-s) + a - 1) / a := by
    have h0 : 0 < (Real.exp (-0) + a - 1) / a := by
      rw [neg_zero, Real.exp_zero]; field_simp; linarith
    exact nhdsWithin_le_nhds (hcont.continuousAt.eventually (lt_mem_nhds h0))
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => (Real.exp (-s) + a - 1) / a) (d := -a⁻¹) ?_ ?_
    (neg_ne_zero.mpr (inv_ne_zero ha.ne'))
  · filter_upwards [hpos] with s hs
    exact max_eq_right hs.le
  · have h := (((hasDerivAt_neg' (0 : ℝ)).exp.add_const a).sub_const 1).div_const a
    refine h.congr_deriv ?_
    rw [neg_zero, Real.exp_zero]
    field_simp

/-- Nelsen's family 10 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen10 θ hθ h1).HasUpperTailDependence 0 := by
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => (2 / (Real.exp s + 1)) ^ θ⁻¹) (d := θ⁻¹ * -(1 / 2)) ?_ ?_
    (mul_ne_zero (inv_ne_zero hθ.ne') (by norm_num))
  · refine Eventually.of_forall fun s => ?_
    simp only [nelsen10Generator, BivariateGenerator.innerPower, amhGenerator]
    norm_num
  · have hb : HasDerivAt (fun s : ℝ => 2 / (Real.exp s + 1)) (-(1 / 2)) 0 := by
      have h := (hasDerivAt_const (0 : ℝ) (2 : ℝ)).div ((Real.hasDerivAt_exp 0).add_const 1)
        (by positivity)
      refine h.congr_deriv ?_
      rw [Real.exp_zero]
      norm_num
    have h := hb.rpow_const (p := θ⁻¹) (Or.inl (by rw [Real.exp_zero]; norm_num))
    refine h.congr_deriv ?_
    rw [Real.exp_zero]
    norm_num
    ring

/-- Nelsen's family 11 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    (nelsen11 θ hθ h2).HasUpperTailDependence 0 := by
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => (2 - Real.exp s) ^ θ⁻¹) (d := -θ⁻¹) ?_ ?_
    (neg_ne_zero.mpr (inv_ne_zero hθ.ne'))
  · filter_upwards [eventually_lt_nhdsGE (Real.log_pos one_lt_two)] with s hs
    change (2 - Real.exp (min s (Real.log 2))) ^ θ⁻¹ = _
    rw [min_eq_left hs.le]
  · have h := ((Real.hasDerivAt_exp 0).const_sub 2).rpow_const (p := θ⁻¹)
      (Or.inl (by rw [Real.exp_zero]; norm_num))
    refine h.congr_deriv ?_
    rw [Real.exp_zero]
    norm_num

/-- Nelsen's family 13 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen13 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen13 θ hθ).HasUpperTailDependence 0 := by
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => Real.exp (1 - (1 + s) ^ θ⁻¹)) (d := -θ⁻¹) (Eventually.of_forall fun _ => rfl)
    ?_ (neg_ne_zero.mpr (inv_ne_zero hθ.ne'))
  have h := ((((hasDerivAt_id (0 : ℝ)).const_add 1).rpow_const (p := θ⁻¹)
    (Or.inl (by norm_num))).const_sub 1).exp
  refine h.congr_deriv ?_
  norm_num

/-- Nelsen's family 16 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen16 θ hθ).HasUpperTailDependence 0 := by
  have hr : (1 - θ - 0) ^ 2 + 4 * θ = (1 + θ) ^ 2 := by ring
  have hs : √((1 - θ - 0) ^ 2 + 4 * θ) = 1 + θ := by
    rw [hr, Real.sqrt_sq (by linarith)]
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => (1 - θ - s + √((1 - θ - s) ^ 2 + 4 * θ)) / 2) (d := -(1 + θ)⁻¹)
    (Eventually.of_forall fun _ => rfl) ?_ (neg_ne_zero.mpr (inv_ne_zero (by linarith)))
  have hin : HasDerivAt (fun s : ℝ => 1 - θ - s) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub (1 - θ)
  have hq : HasDerivAt (fun s : ℝ => (1 - θ - s) ^ 2 + 4 * θ) _ 0 :=
    (hin.pow 2).add_const (4 * θ)
  have hsq := hq.sqrt (by rw [hr]; positivity)
  have h := (hin.add hsq).div_const 2
  refine h.congr_deriv ?_
  rw [hs]
  have h1 : (1 : ℝ) + θ ≠ 0 := by linarith
  field_simp
  push_cast
  ring

/-- Nelsen's family 17 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) :
    (nelsen17 θ hθ).HasUpperTailDependence 0 := by
  set c : ℝ := (2 : ℝ) ^ (-θ) - 1 with hc
  have h2pos : 0 < (2 : ℝ) ^ (-θ) := Real.rpow_pos_of_pos two_pos _
  have hc0 : c ≠ 0 := by
    rw [hc, sub_ne_zero]
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · exact (Real.one_lt_rpow (by norm_num) (by linarith)).ne'
    · exact (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).ne
  have hb : HasDerivAt (fun s : ℝ => 1 + c * Real.exp (-s)) (c * (Real.exp (-0) * -1)) 0 :=
    ((hasDerivAt_neg' (0 : ℝ)).exp.const_mul c).const_add 1
  have hb0 : (1 : ℝ) + c * Real.exp (-0) = (2 : ℝ) ^ (-θ) := by
    rw [neg_zero, Real.exp_zero, hc]; ring
  have h := (hb.rpow_const (p := -θ⁻¹) (Or.inl (by rw [hb0]; exact h2pos.ne'))).sub_const 1
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => (1 + c * Real.exp (-s)) ^ (-θ⁻¹) - 1) (Eventually.of_forall fun _ => rfl) h ?_
  rw [hb0]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 (by norm_num)) (neg_ne_zero.mpr
    (inv_ne_zero hθ))) (Real.rpow_pos_of_pos h2pos _).ne'

/-- Nelsen's family 22 has no upper tail dependence. -/
theorem hasUpperTailDependence_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen22 θ hθ h1).HasUpperTailDependence 0 := by
  refine BivariateGenerator.hasUpperTailDependence_zero_of_eventuallyEq _
    (F := fun s => (1 - Real.sin s) ^ θ⁻¹) (d := -θ⁻¹) ?_ ?_
    (neg_ne_zero.mpr (inv_ne_zero hθ.ne'))
  · filter_upwards [eventually_lt_nhdsGE (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with s hs
    change (1 - Real.sin (min s (Real.pi / 2))) ^ θ⁻¹ = _
    rw [min_eq_left hs.le]
  · have h := ((Real.hasDerivAt_sin 0).const_sub 1).rpow_const (p := θ⁻¹)
      (Or.inl (by rw [Real.sin_zero]; norm_num))
    refine h.congr_deriv ?_
    rw [Real.sin_zero, Real.cos_zero]
    norm_num

end ProbabilityTheory.Copula
