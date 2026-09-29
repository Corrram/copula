/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.NelsenTable.N11
import Copula.Families.NelsenTable.N22
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Limits at `θ → 0⁺` of Nelsen's families 11 and 22

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1 lists the limiting case
`C₀ = Π` for family 11 (`C(u, v) = max(u^θ v^θ − 2(1 − u^θ)(1 − v^θ), 0)^{1/θ}`) and for
family 22 (`C(u, v) = (1 − a √(1 − b²) − b √(1 − a²))^{1/θ}` with `a = 1 − u^θ`, `b = 1 − v^θ`,
on the region `a² + b² ≤ 1`). Both are proved as pointwise convergence of the CDFs along any
filter on which the parameter tends to `0` through admissible values
(`tendsto_nelsen11_zero`, `tendsto_nelsen22_zero`).

Both follow from one elementary limit (`tendsto_max_rpow_inv_nhdsGT_zero`): if `F(0) = 1` and
`F'(0) = c`, then `max(F(θ), 0)^{1/θ} → e^c` as `θ → 0⁺`, since `log F(θ) / θ → c`. For both
families `F'(0) = log u + log v`, so the limit is `e^{log u + log v} = uv`.
-/

open Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- If `F(0) = 1` and `F'(0) = c`, then `max(F(θ), 0)^{1/θ} → e^c` as `θ → 0⁺`. -/
theorem tendsto_max_rpow_inv_nhdsGT_zero {F : ℝ → ℝ} {c : ℝ} (hF0 : F 0 = 1)
    (hF : HasDerivAt F c 0) :
    Tendsto (fun t => max (F t) 0 ^ t⁻¹) (𝓝[>] 0) (𝓝 (Real.exp c)) := by
  have hL : HasDerivAt (fun t => Real.log (F t)) (c / F 0) 0 := hF.log (by rw [hF0]; norm_num)
  rw [hF0, div_one] at hL
  have hs := hL.tendsto_slope_zero
  simp only [zero_add, hF0, Real.log_one, sub_zero, smul_eq_mul] at hs
  have hs' := hs.mono_left (nhdsWithin_mono _ fun x (hx : 0 < x) => ne_of_gt hx)
  have hexp := (Real.continuous_exp.tendsto c).comp hs'
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < F t :=
    nhdsWithin_le_nhds (hF.continuousAt.eventually (lt_mem_nhds (by rw [hF0]; norm_num)))
  refine hexp.congr' ?_
  filter_upwards [hpos] with t ht
  simp only [Function.comp_apply]
  rw [max_eq_left ht.le, Real.rpow_def_of_pos ht, mul_comm]

private theorem fin2_eq' (u : Fin 2 → I) : u = ![u 0, u 1] := by
  funext i
  fin_cases i <;> rfl

private theorem coe_pos_of_ne {u : I} (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem hasDerivAt_rpow_zero {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => x ^ t) (Real.log x) 0 := by
  have h := (Real.hasStrictDerivAt_const_rpow hx 0).hasDerivAt
  rwa [Real.rpow_zero, one_mul] at h

/-- The limit `Π` of Nelsen's family 11 as `θ → 0⁺` (Table 4.1), pointwise on the unit square. -/
theorem tendsto_nelsen11_zero {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (h2 : ∀ a, θ a ≤ 1 / 2) (hlim : Tendsto θ l (𝓝 0)) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen11 (θ a) (hθ a) (h2 a)).cdf u) l
      (𝓝 ((independence 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx := coe_pos_of_ne hu
  have hy := coe_pos_of_ne hv
  have hθ' : Tendsto θ l (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hθ⟩
  let F : ℝ → ℝ := fun t => x ^ t * y ^ t - 2 * (1 - x ^ t) * (1 - y ^ t)
  have hF0 : F 0 = 1 := by simp [F]
  have hF : HasDerivAt F (Real.log x + Real.log y) 0 := by
    have hX := hasDerivAt_rpow_zero hx
    have hY := hasDerivAt_rpow_zero hy
    have h := (hX.mul hY).sub (((hX.const_sub 1).const_mul 2).mul (hY.const_sub 1))
    exact h.congr_deriv (by simp [hxdef, hydef])
  have hlimF := tendsto_max_rpow_inv_nhdsGT_zero hF0 hF
  have hval : Real.exp (Real.log x + Real.log y) = (independence 2).cdf u := by
    rw [cdf_independence, Fin.prod_univ_two, ← hxdef, ← hydef, Real.exp_add, Real.exp_log hx,
      Real.exp_log hy]
  rw [hval] at hlimF
  refine (hlimF.comp hθ').congr' (Eventually.of_forall fun a => ?_)
  simp only [Function.comp_apply]
  rw [fin2_eq' u, cdf_nelsen11 (θ a) (hθ a) (h2 a) (u 0) (u 1) hu hv]

/-- The limit `Π` of Nelsen's family 22 as `θ → 0⁺` (Table 4.1), pointwise on the unit square. -/
theorem tendsto_nelsen22_zero {α : Type*} {l : Filter α} (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (h1 : ∀ a, θ a ≤ 1) (hlim : Tendsto θ l (𝓝 0)) (u : Fin 2 → I) :
    Tendsto (fun a => (nelsen22 (θ a) (hθ a) (h1 a)).cdf u) l
      (𝓝 ((independence 2).cdf u)) := by
  by_cases hu : u 0 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 hu]
    exact tendsto_const_nhds
  by_cases hv : u 1 = 0
  · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 hv]
    exact tendsto_const_nhds
  set x : ℝ := (u 0 : ℝ) with hxdef
  set y : ℝ := (u 1 : ℝ) with hydef
  have hx := coe_pos_of_ne hu
  have hy := coe_pos_of_ne hv
  have hθ' : Tendsto θ l (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hθ⟩
  let A : ℝ → ℝ := fun t => 1 - x ^ t
  let B : ℝ → ℝ := fun t => 1 - y ^ t
  let F : ℝ → ℝ := fun t => 1 - A t * √(1 - B t ^ 2) - B t * √(1 - A t ^ 2)
  have hA0 : A 0 = 0 := by simp [A]
  have hB0 : B 0 = 0 := by simp [B]
  have hF0 : F 0 = 1 := by simp [F, hA0, hB0]
  have hA : HasDerivAt A (-Real.log x) 0 := (hasDerivAt_rpow_zero hx).const_sub 1
  have hB : HasDerivAt B (-Real.log y) 0 := (hasDerivAt_rpow_zero hy).const_sub 1
  have hSA := ((hA.pow 2).const_sub 1).sqrt (by simp [hA0])
  have hSB := ((hB.pow 2).const_sub 1).sqrt (by simp [hB0])
  have hF : HasDerivAt F (Real.log x + Real.log y) 0 :=
    (((hA.mul hSB).const_sub 1).sub (hB.mul hSA)).congr_deriv (by simp [hA0, hB0])
  have hlimF := tendsto_max_rpow_inv_nhdsGT_zero hF0 hF
  have hval : Real.exp (Real.log x + Real.log y) = (independence 2).cdf u := by
    rw [cdf_independence, Fin.prod_univ_two, ← hxdef, ← hydef, Real.exp_add, Real.exp_log hx,
      Real.exp_log hy]
  rw [hval] at hlimF
  -- the region condition holds eventually
  have hAc : ContinuousAt A 0 := hA.continuousAt
  have hBc : ContinuousAt B 0 := hB.continuousAt
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), A t ^ 2 + B t ^ 2 ≤ 1 := by
    have hcont : ContinuousAt (fun t => A t ^ 2 + B t ^ 2) 0 := (hAc.pow 2).add (hBc.pow 2)
    have h0 : A 0 ^ 2 + B 0 ^ 2 < 1 := by simp [hA0, hB0]
    exact nhdsWithin_le_nhds ((hcont.eventually (gt_mem_nhds h0)).mono fun t ht => ht.le)
  have hpos' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < F t :=
    nhdsWithin_le_nhds (hF.continuousAt.eventually
      (lt_mem_nhds (show (0 : ℝ) < F 0 by rw [hF0]; norm_num)))
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ F t := hpos'.mono fun t ht => ht.le
  refine (hlimF.comp hθ').congr' ?_
  filter_upwards [hθ'.eventually hsmall, hθ'.eventually hpos] with a ha hb
  simp only [Function.comp_apply]
  rw [fin2_eq' u, cdf_nelsen22 (θ a) (hθ a) (h1 a) (u 0) (u 1) hu hv, max_eq_left hb]
  change _ = if A (θ a) ^ 2 + B (θ a) ^ 2 ≤ 1 then F (θ a) ^ (θ a)⁻¹ else 0
  simp only [ha, ite_true]

end ProbabilityTheory.Copula
