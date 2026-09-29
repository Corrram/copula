/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Diagonal
import Copula.Families.NelsenTable.N11
import Copula.Families.NelsenTable.N16
import Copula.Families.NelsenTable.N18
import Copula.Families.NelsenTable.N21
import Copula.Families.NelsenTable.N22
import Copula.TailDependence.Basic

/-! # Lower tail dependence of non-strict Archimedean copulas

If the inverse generator `ψ` vanishes on `[a, ∞)` with `a > 0` and the generator satisfies
`φ(t) → a` as `t → 0⁺`, then the diagonal `δ(t) = ψ(2 φ(t))` vanishes near zero, so the lower
tail-dependence coefficient is `λ_L = 0` (Nelsen, *An Introduction to Copulas*, second edition,
Section 5.4; for non-strict generators `C(t, t) = 0` for small `t`). This applies to the
non-strict families 11, 18, 21 and 22 of Nelsen's Table 4.1.

Two further tail coefficients follow from the explicit diagonals: family 18 has upper
tail-dependence coefficient `λ_U = 1`, and family 16 (for `θ > 0`) has lower tail-dependence
coefficient `λ_L = 1/2` (values as in Ansari and Rockel, Table 5).
-/

open Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- A copula whose diagonal vanishes near zero has lower tail-dependence coefficient zero. -/
theorem hasLowerTailDependence_zero_of_eventually_diagonal_eq_zero (C : Copula 2)
    (h : ∀ᶠ t : I in 𝓝[>] (0 : I), C.diagonal t = 0) : C.HasLowerTailDependence 0 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h] with t ht
  rw [lowerTailRatio, ht, zero_div]

/-- A non-strict generator (`ψ = 0` on `[a, ∞)`, `a > 0`) whose generator tends to `a` at
zero gives a copula without lower tail dependence. -/
theorem BivariateGenerator.hasLowerTailDependence_zero (g : BivariateGenerator) {a : ℝ}
    (ha : 0 < a) (hzero : ∀ s, a ≤ s → g.toFun s = 0)
    (hφ : Tendsto g.invFun (𝓝[>] (0 : I)) (𝓝 a)) : g.copula.HasLowerTailDependence 0 := by
  apply hasLowerTailDependence_zero_of_eventually_diagonal_eq_zero
  have hbig : ∀ᶠ t : I in 𝓝[>] (0 : I), a / 2 < g.invFun t :=
    hφ.eventually (lt_mem_nhds (half_lt_self ha))
  filter_upwards [hbig, self_mem_nhdsWithin] with t ht htpos
  have ht0 : t ≠ 0 := ne_of_gt htpos
  rw [g.diagonal_copula ht0]
  exact hzero _ (by linarith)

private theorem tendsto_of_continuousAt {f : I → ℝ} {a : ℝ} (hf : ContinuousAt f 0)
    (h0 : f 0 = a) : Tendsto f (𝓝[>] (0 : I)) (𝓝 a) := by
  rw [← h0]
  exact hf.tendsto.mono_left nhdsWithin_le_nhds

private theorem continuousAt_val_zero : ContinuousAt (fun u : I => (u : ℝ)) 0 :=
  continuous_subtype_val.continuousAt

/-- Nelsen's family 11 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    (nelsen11 θ hθ h2).HasLowerTailDependence 0 := by
  refine (nelsen11Generator θ hθ h2).hasLowerTailDependence_zero
    (Real.log_pos one_lt_two) (fun s hs => nelsen11Generator_toFun_of_le θ hθ h2 hs) ?_
  have h0 : ((0 : I) : ℝ) ^ θ = 0 := Real.zero_rpow hθ.ne'
  refine tendsto_of_continuousAt ?_ ?_
  · exact (continuousAt_const.sub (continuousAt_val_zero.rpow_const (Or.inr hθ.le))).log
      (by show (2 : ℝ) - ((0 : I) : ℝ) ^ θ ≠ 0; rw [h0]; norm_num)
  · rw [nelsen11Generator_invFun, h0, sub_zero]

/-- Nelsen's family 18 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) :
    (nelsen18 θ hθ).HasLowerTailDependence 0 := by
  refine (nelsen18Generator θ hθ).hasLowerTailDependence_zero (Real.exp_pos _)
    (fun s hs => nelsen18Generator_toFun_of_le θ hθ hs) ?_
  have hc : ContinuousAt (fun u : I => Real.exp (θ / ((u : ℝ) - 1))) 0 :=
    (continuousAt_const.div (continuousAt_val_zero.sub continuousAt_const)
      (by norm_num)).rexp
  have heq : (fun u : I => Real.exp (θ / ((u : ℝ) - 1))) =ᶠ[𝓝 0] nelsen18Phi θ := by
    have hlt : ∀ᶠ u : I in 𝓝 0, (u : ℝ) < 1 :=
      continuousAt_val_zero.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hlt] with u hu
    have hu1 : u ≠ 1 := fun h => by rw [h] at hu; norm_num at hu
    simp [nelsen18Phi, hu1]
  refine tendsto_of_continuousAt (hc.congr heq) ?_
  show nelsen18Phi θ 0 = Real.exp (-θ)
  simp [nelsen18Phi, div_neg]

/-- Nelsen's family 21 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen21 θ hθ).HasLowerTailDependence 0 := by
  refine (nelsen21Generator θ hθ).hasLowerTailDependence_zero one_pos
    (fun s hs => BivariateGenerator.ofClamp_toFun_of_le hs) ?_
  refine tendsto_of_continuousAt ?_ ?_
  · show ContinuousAt (fun u : I => 1 - (1 - (1 - (u : ℝ)) ^ θ) ^ θ⁻¹) 0
    exact continuousAt_const.sub ((continuousAt_const.sub
      ((continuousAt_const.sub continuousAt_val_zero).rpow_const (Or.inr (by linarith)))).rpow_const
        (Or.inr (inv_nonneg.mpr (by linarith))))
  · show 1 - (1 - (1 - ((0 : I) : ℝ)) ^ θ) ^ θ⁻¹ = 1
    rw [Set.Icc.coe_zero, sub_zero, Real.one_rpow, sub_self,
      Real.zero_rpow (inv_ne_zero (by linarith)), sub_zero]

/-- Nelsen's family 22 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen22 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen22 θ hθ h1).HasLowerTailDependence 0 := by
  refine (nelsen22Generator θ hθ h1).hasLowerTailDependence_zero (a := Real.pi / 2)
    (by linarith [Real.pi_pos])
    (fun s hs => ?_) ?_
  · rw [nelsen22Generator_toFun, min_eq_right hs, Real.sin_pi_div_two, sub_self,
      Real.zero_rpow (inv_ne_zero hθ.ne')]
  have hf : (nelsen22Generator θ hθ h1).invFun = fun u : I => Real.arcsin (1 - (u : ℝ) ^ θ) := by
    funext u
    exact nelsen22Generator_invFun θ hθ h1 u
  rw [hf]
  refine tendsto_of_continuousAt ?_ ?_
  · exact (continuousAt_const.sub (continuousAt_val_zero.rpow_const (Or.inr hθ.le))).arcsin
  · show Real.arcsin (1 - ((0 : I) : ℝ) ^ θ) = Real.pi / 2
    rw [Set.Icc.coe_zero, Real.zero_rpow hθ.ne', sub_zero, Real.arcsin_one]

private theorem tendsto_val_zero : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 0) :=
  (continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds

private theorem eventually_val_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : I in 𝓝[>] (0 : I), (t : ℝ) < ε :=
  tendsto_val_zero.eventually (eventually_lt_nhds hε)

private theorem eventually_val_pos : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < (t : ℝ) := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ht

/-- Nelsen's family 18 has upper tail-dependence coefficient one. -/
theorem hasUpperTailDependence_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) :
    (nelsen18 θ hθ).HasUpperTailDependence 1 := by
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos two_pos (by norm_num)
    linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let g : ℝ → ℝ := fun t => 2 - θ / (θ - t * Real.log 2)
  have hg : ContinuousAt g 0 := by
    apply continuousAt_const.sub (continuousAt_const.div (by fun_prop) _)
    simp only [zero_mul, sub_zero]
    linarith
  have hg0 : g 0 = 1 := by
    simp only [g, zero_mul, sub_zero, div_self (show θ ≠ 0 by linarith)]
    norm_num
  have hlim : Tendsto (fun t : I => g t) (𝓝[>] (0 : I)) (𝓝 1) := by
    rw [← hg0]
    exact hg.tendsto.comp tendsto_val_zero
  refine hlim.congr' ?_
  filter_upwards [eventually_val_lt (by norm_num : (0 : ℝ) < 1 / 2), eventually_val_pos]
    with t ht htp
  have hs0 : unitInterval.symm t ≠ 0 := by
    intro h
    have h' := congrArg (fun x : I => (x : ℝ)) h
    simp only [unitInterval.coe_symm_eq, Set.Icc.coe_zero] at h'
    linarith
  have hs1 : unitInterval.symm t ≠ 1 := by
    intro h
    have h' := congrArg (fun x : I => (x : ℝ)) h
    simp only [unitInterval.coe_symm_eq, Set.Icc.coe_one] at h'
    linarith
  rw [upperTailRatio_eq, diagonal, cdf_nelsen18 θ hθ _ _ hs0 hs1 hs0 hs1,
    unitInterval.coe_symm_eq]
  have hsub : 1 - (t : ℝ) - 1 = -(t : ℝ) := by ring
  have hden : 0 < θ - (t : ℝ) * Real.log 2 := by nlinarith
  have hlog : Real.log (Real.exp (θ / (1 - (t : ℝ) - 1)) + Real.exp (θ / (1 - (t : ℝ) - 1))) =
      Real.log 2 - θ / (t : ℝ) := by
    rw [← two_mul, Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp, hsub, div_neg]
    ring
  have hval : 1 + θ / (Real.log 2 - θ / (t : ℝ)) = 1 - θ * (t : ℝ) / (θ - (t : ℝ) * Real.log 2) := by
    have e1 : Real.log 2 - θ / (t : ℝ) = -(θ - (t : ℝ) * Real.log 2) / (t : ℝ) := by
      field_simp
      ring
    rw [e1, neg_div, div_neg, div_div_eq_mul_div]
    ring
  have hnn : 0 ≤ 1 - θ * (t : ℝ) / (θ - (t : ℝ) * Real.log 2) := by
    rw [sub_nonneg, div_le_one hden]
    nlinarith
  rw [hlog, hval, max_eq_left hnn]
  show 2 - θ / (θ - (t : ℝ) * Real.log 2) = _
  field_simp
  ring

/-- Nelsen's family 16 has lower tail-dependence coefficient `1/2` for every `θ > 0`. -/
theorem hasLowerTailDependence_nelsen16 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen16 θ hθ.le).HasLowerTailDependence (1 / 2) := by
  -- `t S(t)` with `S(t) = 2t - 1 - θ (2/t - 1)`.
  let P : ℝ → ℝ := fun t => 2 * t ^ 2 - t - 2 * θ + θ * t
  let h : ℝ → ℝ := fun t => 2 * θ / (√(P t ^ 2 + 4 * θ * t ^ 2) - P t)
  have hP0 : P 0 = -2 * θ := by simp only [P]; ring
  have hden0 : √(P 0 ^ 2 + 4 * θ * 0 ^ 2) - P 0 = 4 * θ := by
    rw [hP0, show (-2 * θ) ^ 2 + 4 * θ * (0 : ℝ) ^ 2 = (2 * θ) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
    ring
  have hc : ContinuousAt h 0 := by
    apply continuousAt_const.div (by fun_prop)
    rw [hden0]
    positivity
  have hh0 : h 0 = 1 / 2 := by
    show 2 * θ / (√(P 0 ^ 2 + 4 * θ * 0 ^ 2) - P 0) = 1 / 2
    rw [hden0]
    field_simp
    ring
  have hlim : Tendsto (fun t : I => h t) (𝓝[>] (0 : I)) (𝓝 (1 / 2)) := by
    rw [← hh0]
    exact hc.tendsto.comp tendsto_val_zero
  refine hlim.congr' ?_
  filter_upwards [eventually_val_pos] with t htp
  have ht0 : t ≠ 0 := fun h0 => by rw [h0] at htp; simp at htp
  rw [lowerTailRatio, diagonal, cdf_nelsen16 θ hθ.le t t ht0 ht0]
  set x : ℝ := (t : ℝ) with hx
  set S : ℝ := x + x - 1 - θ * (1 / x + 1 / x - 1) with hS
  have hPS : P x = x * S := by
    simp only [P, hS]
    field_simp
    ring
  set R : ℝ := √(S ^ 2 + 4 * θ) with hR
  have hR2 : R ^ 2 = S ^ 2 + 4 * θ := Real.sq_sqrt (by positivity)
  have hRS : S < R := by
    rcases lt_or_ge S 0 with h' | h'
    · linarith [Real.sqrt_nonneg (S ^ 2 + 4 * θ)]
    · exact (Real.lt_sqrt h').mpr (by linarith)
  have hsq : √(P x ^ 2 + 4 * θ * x ^ 2) = x * R := by
    rw [hPS, show (x * S) ^ 2 + 4 * θ * x ^ 2 = x ^ 2 * (S ^ 2 + 4 * θ) by ring,
      Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq htp.le]
  show 2 * θ / (√(P x ^ 2 + 4 * θ * x ^ 2) - P x) = (S + R) / 2 / x
  rw [hsq, hPS, show x * R - x * S = x * (R - S) by ring]
  have hRS' : 0 < R - S := by linarith
  rw [div_div, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-x) * hR2

end ProbabilityTheory.Copula
