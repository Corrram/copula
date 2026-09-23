/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/import Copula.Families.Nelsen8
import Copula.Dependence.Clayton
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


/-! # Nelsen 8 infinite-parameter endpoint

The family converges pointwise on the closed square to the Clayton copula with
parameter one, as stated in Ansari–Rockel Table 2.
-/
open Filter
open scoped unitInterval Topology
namespace ProbabilityTheory.Copula

private theorem n8_norm (θ u v : ℝ) (hθ : θ ≠ 0)
    (hd : θ^2-(θ-1)^2*(1-u)*(1-v) ≠ 0) :
    (θ^2*u*v-(1-u)*(1-v))/(θ^2-(θ-1)^2*(1-u)*(1-v)) =
      (u*v-θ⁻¹^2*(1-u)*(1-v))/(1-(1-θ⁻¹)^2*(1-u)*(1-v)) := by
  have hn : 1-(1-θ⁻¹)^2*(1-u)*(1-v) ≠ 0 := by
    intro hh
    apply hd
    have hh' : (1-(1-θ⁻¹)^2*(1-u)*(1-v))*θ^2 =
      θ^2-(θ-1)^2*(1-u)*(1-v) := by
      field_simp
    rw [hh, zero_mul] at hh'
    exact hh'.symm
  field_simp

private theorem clayton_one_rational (u v : I) (hu : 0 < (u:ℝ)) (hv : 0 < (v:ℝ)) :
    (clayton 2 1 (by norm_num)).cdf ![u,v] =
      (u:ℝ)*(v:ℝ)/((u:ℝ)+(v:ℝ)-(u:ℝ)*(v:ℝ)) := by
  rw [cdf_clayton_two_pos 1 (by norm_num) u v hu hv]
  norm_num
  rw [Real.rpow_neg_one, Real.rpow_neg_one, Real.rpow_neg_one]
  have hden : 0 < (u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ) := by
    have h := mul_nonneg hu.le (sub_nonneg.mpr v.property.2)
    nlinarith
  field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt hden]
  have hq : ((u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ)) *
      ((u : ℝ) + (v : ℝ) - (u : ℝ) * (v : ℝ))⁻¹ = 1 := by
    exact mul_inv_cancel₀ (ne_of_gt hden)
  convert hq using 1; ring

/-- The upper endpoint of Nelsen 8 is Clayton with parameter one. -/
theorem tendsto_nelsen8_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen8 (θ a) (hθ a)).cdf u) l
      (𝓝 ((clayton 2 1 (by norm_num)).cdf u)) := by
  by_cases hu : u 0 = 0
  · have hzero (a : α) : (nelsen8 (θ a) (hθ a)).cdf u = 0 :=
      (nelsen8 (θ a) (hθ a)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    have htarget : (clayton 2 1 (by norm_num)).cdf u = 0 :=
      (clayton 2 1 (by norm_num)).cdf_eq_zero_of_coord_eq_zero u 0 hu
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  by_cases hv : u 1 = 0
  · have hzero (a : α) : (nelsen8 (θ a) (hθ a)).cdf u = 0 :=
      (nelsen8 (θ a) (hθ a)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    have htarget : (clayton 2 1 (by norm_num)).cdf u = 0 :=
      (clayton 2 1 (by norm_num)).cdf_eq_zero_of_coord_eq_zero u 1 hv
    simpa only [hzero, htarget] using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 0))
  let x : ℝ := (u 0 : ℝ)
  let y : ℝ := (u 1 : ℝ)
  have hx : 0 < x := lt_of_le_of_ne (u 0).property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hy : 0 < y := lt_of_le_of_ne (u 1).property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have hd : 0 < 1 - (1 - x) * (1 - y) := by
    have h := mul_nonneg (sub_nonneg.mpr (u 0).property.2) hy.le
    dsimp [x, y] at h ⊢
    nlinarith
  have hi : Tendsto (fun a => (θ a)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlim
  have hcont : ContinuousAt
      (fun q : ℝ => max 0 ((x*y-q^2*(1-x)*(1-y))/(1-(1-q)^2*(1-x)*(1-y)))) 0 := by
    have hcnum : ContinuousAt (fun q : ℝ => x*y-q^2*(1-x)*(1-y)) 0 := by fun_prop
    have hcden : ContinuousAt (fun q : ℝ => 1-(1-q)^2*(1-x)*(1-y)) 0 := by fun_prop
    exact continuousAt_const.max (hcnum.div hcden (by simpa using hd.ne'))
  have hlim' := hcont.tendsto.comp hi
  have htarget : max 0 ((x*y-(0:ℝ)^2*(1-x)*(1-y))/(1-(1-(0:ℝ))^2*(1-x)*(1-y))) =
      (clayton 2 1 (by norm_num)).cdf u := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    rw [hz, clayton_one_rational (u 0) (u 1) hx hy]
    have hxy : 0 ≤ x*y/(1-(1-x)*(1-y)) :=
      div_nonneg (mul_nonneg hx.le hy.le) hd.le
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, sub_zero,
      one_pow, one_mul] at ⊢
    rw [max_eq_right hxy]
    dsimp [x,y]
    congr 1
    ring
  have hformula (a : α) : (nelsen8 (θ a) (hθ a)).cdf u =
      max 0 ((x*y-(θ a)⁻¹^2*(1-x)*(1-y)) /
        (1-(1-(θ a)⁻¹)^2*(1-x)*(1-y))) := by
    have hz : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
    have hden := n8_source_den_pos (θ a) x y (hθ a)
      (u 0).property.1 (u 0).property.2 (u 1).property.1 (u 1).property.2
    rw [hz, nelsen8_cdf_full]
    exact congrArg (max 0) (n8_norm (θ a) x y (by linarith [hθ a]) hden.ne')
  simpa only [Function.comp_def, hformula, htarget] using hlim'
end ProbabilityTheory.Copula
