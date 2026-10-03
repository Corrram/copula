/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Basic
import Copula.Rank.Region.Common.StochasticRho
import Copula.Rank.Integration

/-! # Spearman's rho of the Plackett family

For the Plackett copula `C_θ` (`θ > 0`, `θ ≠ 1`) the inner integral is elementary: writing
`disc(u,v) = x² + 4θv(1-v)` with `x = (θ-1)u + 1 - (θ+1)v`, a primitive of `√disc` in `u` is
`(x √disc + 4θv(1-v) log(x + √disc)) / (2(θ-1))`, and the logarithmic boundary terms combine
to `log θ`. This gives

`∫₀¹ C_θ(u,v) du = v/2 + v(1-v) (θ² - 1 - 2θ log θ) / (2(θ-1)²)`

(`PlackettSpearman.integral_plackettCDF`) and hence Mardia's formula (K. V. Mardia, *Some
contributions to contingency-type bivariate distributions*, Biometrika 54 (1967); see Nelsen 2006,
§3.3.1):

`ρ(C_θ) = (θ + 1)/(θ - 1) - 2θ log θ/(θ - 1)²` (`spearmanRho_plackett`), with `ρ(C_1) = 0`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace PlackettSpearman

theorem plackettDisc_eq_sq_add (θ u v : ℝ) :
    plackettDisc θ u v = ((θ - 1) * u + 1 - (θ + 1) * v) ^ 2 + 4 * θ * v * (1 - v) := by
  unfold plackettDisc plackettLinear; ring

/-- A primitive of `u ↦ √disc(u,v)` for `0 < v < 1`. -/
noncomputable def sqrtPrimitive (θ v u : ℝ) : ℝ :=
  (((θ - 1) * u + 1 - (θ + 1) * v) * √(plackettDisc θ u v) +
    4 * θ * v * (1 - v) * Real.log (((θ - 1) * u + 1 - (θ + 1) * v) + √(plackettDisc θ u v))) /
      (2 * (θ - 1))

theorem hasDerivAt_sqrtPrimitive {θ v : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hv0 : 0 < v)
    (hv1 : v < 1) (u : ℝ) :
    HasDerivAt (sqrtPrimitive θ v) (√(plackettDisc θ u v)) u := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hm : 0 < 4 * θ * v * (1 - v) := by
    have := mul_pos hθ (mul_pos hv0 (sub_pos.mpr hv1)); nlinarith
  have hD : 0 < plackettDisc θ u v := by
    rw [plackettDisc_eq_sq_add]; positivity
  have hr : 0 < √(plackettDisc θ u v) := Real.sqrt_pos.mpr hD
  have hr2 : √(plackettDisc θ u v) ^ 2 =
      ((θ - 1) * u + 1 - (θ + 1) * v) ^ 2 + 4 * θ * v * (1 - v) := by
    rw [Real.sq_sqrt hD.le, plackettDisc_eq_sq_add]
  have hXr : 0 < ((θ - 1) * u + 1 - (θ + 1) * v) + √(plackettDisc θ u v) := by
    by_contra! hle
    have hle' : √(plackettDisc θ u v) ≤ -((θ - 1) * u + 1 - (θ + 1) * v) := by linarith
    nlinarith [mul_le_mul hle' hle' hr.le (by linarith)]
  have hX : HasDerivAt (fun x => (θ - 1) * x + 1 - (θ + 1) * v) (θ - 1) u := by
    have := (((hasDerivAt_id' u).const_mul (θ - 1)).add_const 1).sub_const ((θ + 1) * v)
    simpa using this
  have hs := (hasDerivAt_plackettDisc_left θ u v).sqrt hD.ne'
  have h := ((hX.mul hs).add
    (((hX.add hs).log hXr.ne').const_mul (4 * θ * v * (1 - v)))).div_const (2 * (θ - 1))
  unfold sqrtPrimitive
  convert h using 1
  have hD' : 2 * plackettLinear θ u v * (θ - 1) - 4 * θ * (θ - 1) * v =
      2 * (θ - 1) * ((θ - 1) * u + 1 - (θ + 1) * v) := by unfold plackettLinear; ring
  rw [hD']
  simp only [Pi.add_apply]
  generalize √(plackettDisc θ u v) = r at hr hr2 hXr ⊢
  generalize (θ - 1) * u + 1 - (θ + 1) * v = X at hr2 hXr ⊢
  generalize 4 * θ * v * (1 - v) = m at hr2 ⊢
  have hm' : m = r ^ 2 - X ^ 2 := by linarith
  subst hm'
  field_simp
  ring

/-- The closed form of the inner integral `∫₀¹ C_θ(u,v) du`. -/
noncomputable def innerIntegral (θ v : ℝ) : ℝ :=
  v / 2 + v * (1 - v) * (θ ^ 2 - 1 - 2 * θ * Real.log θ) / (2 * (θ - 1) ^ 2)

/-- A primitive of `u ↦ C_θ(u,v)`. -/
noncomputable def cdfPrimitive (θ v u : ℝ) : ℝ :=
  (u + (θ - 1) * (u ^ 2 / 2 + v * u) - sqrtPrimitive θ v u) / (2 * (θ - 1))

theorem hasDerivAt_cdfPrimitive {θ v : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hv0 : 0 < v)
    (hv1 : v < 1) (u : ℝ) :
    HasDerivAt (cdfPrimitive θ v) (plackettCDF θ u v) u := by
  have hp : HasDerivAt (fun x => x + (θ - 1) * (x ^ 2 / 2 + v * x))
      (1 + (θ - 1) * ((2 : ℕ) * u ^ (2 - 1) * 1 / 2 + v * 1)) u :=
    (hasDerivAt_id' u).add ((((hasDerivAt_id' u).pow 2).div_const 2).add
      ((hasDerivAt_id' u).const_mul v) |>.const_mul (θ - 1))
  have h := (hp.sub (hasDerivAt_sqrtPrimitive hθ hθ1 hv0 hv1 u)).div_const (2 * (θ - 1))
  unfold cdfPrimitive
  convert h using 1
  rw [plackettCDF_eq_of_ne hθ1]
  unfold plackettLinear
  push_cast
  ring

theorem sqrt_plackettDisc_zero_left {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    √(plackettDisc θ 0 v) = 1 + (θ - 1) * v := by
  rw [plackettDisc_zero_left, Real.sqrt_sq (by nlinarith)]

theorem sqrt_plackettDisc_one_left {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    √(plackettDisc θ 1 v) = θ - (θ - 1) * v := by
  rw [plackettDisc_one_left, Real.sqrt_sq (by nlinarith)]

/-- The inner integral of the Plackett copula, for every `v ∈ [0,1]` and `θ ≠ 1`. -/
theorem integral_plackettCDF {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) (v : I) :
    (∫ u : I, plackettCDF θ u v) = innerIntegral θ v := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  rw [integral_unitInterval (fun u => plackettCDF θ u v)]
  rcases eq_or_lt_of_le v.2.1 with h0 | h0
  · -- `v = 0`
    have hz : ∀ u : ℝ, u ∈ uIcc (0 : ℝ) 1 → plackettCDF θ u v = 0 := by
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      rw [plackettCDF_comm, ← h0]
      exact plackettCDF_zero_left hθ hu.1 hu.2
    rw [intervalIntegral.integral_congr hz]
    simp [innerIntegral, ← h0]
  rcases eq_or_lt_of_le v.2.2 with h1' | h1'
  · -- `v = 1`
    have hz : ∀ u : ℝ, u ∈ uIcc (0 : ℝ) 1 → plackettCDF θ u v = u := by
      intro u hu
      rw [uIcc_of_le zero_le_one] at hu
      rw [plackettCDF_comm, h1']
      exact plackettCDF_one_left hθ hu.1 hu.2
    rw [intervalIntegral.integral_congr hz, integral_id, h1']
    simp [innerIntegral]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_cdfPrimitive hθ hθ1 h0 h1' u)
    (((continuous_plackettCDF θ).comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      _ _)]
  unfold cdfPrimitive sqrtPrimitive innerIntegral
  rw [sqrt_plackettDisc_one_left hθ v.2.1 v.2.2, sqrt_plackettDisc_zero_left hθ v.2.1 v.2.2]
  have hv1 : (0 : ℝ) < 1 - v := sub_pos.mpr h1'
  have hA : (θ - 1) * 1 + 1 - (θ + 1) * v + (θ - (θ - 1) * v) = θ * (2 * (1 - v)) := by ring
  have hB : (θ - 1) * 0 + 1 - (θ + 1) * v + (1 + (θ - 1) * v) = 2 * (1 - v) := by ring
  rw [hA, hB, Real.log_mul hθ.ne' (by positivity)]
  field_simp
  ring

end PlackettSpearman

/-- Spearman's rho of the Plackett copula (Mardia 1967; Nelsen 2006, §3.3.1):
`ρ(C_θ) = (θ + 1)/(θ - 1) - 2θ log θ/(θ - 1)²` for `θ ≠ 1`. -/
theorem spearmanRho_plackett {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≠ 1) :
    (plackett θ hθ).spearmanRho = (θ + 1) / (θ - 1) - 2 * θ * Real.log θ / (θ - 1) ^ 2 := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  rw [RankRegion.Common.spearmanRho_eq_iterated_cdf]
  simp_rw [cdf_plackett_two, PlackettSpearman.integral_plackettCDF hθ hθ1]
  rw [integral_unitInterval (PlackettSpearman.innerIntegral θ)]
  set k := (θ ^ 2 - 1 - 2 * θ * Real.log θ) / (2 * (θ - 1) ^ 2)
  have hk : ∀ v, PlackettSpearman.innerIntegral θ v = v / 2 + k * (v - v ^ 2) := by
    intro v; unfold PlackettSpearman.innerIntegral; simp only [k]; ring
  have hF : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => v ^ 2 / 4 + k * (v ^ 2 / 2 - v ^ 3 / 3))
      (PlackettSpearman.innerIntegral θ x) x := by
    intro x _
    rw [hk]
    have h := (((hasDerivAt_id' x).pow 2).div_const 4).add
      (((((hasDerivAt_id' x).pow 2).div_const 2).sub (((hasDerivAt_id' x).pow 3).div_const 3)).const_mul k)
    convert h using 1
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF]
  · simp only [k]
    field_simp
    ring
  · apply Continuous.intervalIntegrable
    have : PlackettSpearman.innerIntegral θ = fun v => v / 2 + k * (v - v ^ 2) := funext hk
    rw [this]; fun_prop

/-- `ρ(C_1) = ρ(Π) = 0`. -/
theorem spearmanRho_plackett_one : (plackett 1 one_pos).spearmanRho = 0 := by
  rw [plackett_one]; exact spearmanRho_independence

end ProbabilityTheory.Copula
