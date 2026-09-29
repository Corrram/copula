/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Nelsen's family 9 (Gumbel–Barnett)

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 9 (Section 4.2):
generator `φ(t) = ln (1 - θ ln t)`, inverse generator `ψ(s) = exp ((1 - exp s) / θ)`, and
copula `C(u, v) = u v exp (-θ ln u ln v)`, for `0 < θ ≤ 1`.

Convexity of `ψ` on `[0, ∞)` is proved from its second derivative
`ψ''(s) = (1/θ) ψ(s) exp s ((exp s)/θ - 1) ≥ 0`, which is nonnegative exactly because
`θ ≤ 1 ≤ exp s`. This is the full parameter range of Nelsen's table (the limiting case
`θ = 0`, independence, is not a member of the family in this module).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen9_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen9_arg_ge_one (θ : ℝ) (hθ : 0 < θ) (u : I) :
    1 ≤ 1 - θ * Real.log (u : ℝ) := by
  have h := Real.log_nonpos u.property.1 u.property.2
  nlinarith [mul_nonneg hθ.le (neg_nonneg.mpr h)]

private theorem nelsen9_hasDerivAt (θ t : ℝ) :
    HasDerivAt (fun x => Real.exp ((1 - Real.exp x) / θ))
      (-(1 / θ) * Real.exp (t + (1 - Real.exp t) / θ)) t := by
  have hg : HasDerivAt (fun x => (1 - Real.exp x) / θ) ((0 - Real.exp t) / θ) t := by
    have h0 := ((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_exp t)).div_const θ
    exact h0
  have h : HasDerivAt (fun x => Real.exp ((1 - Real.exp x) / θ))
      (Real.exp ((1 - Real.exp t) / θ) * ((0 - Real.exp t) / θ)) t := hg.exp
  refine h.congr_deriv ?_
  rw [Real.exp_add]
  ring

private theorem nelsen9_hasDerivAt2 (θ t : ℝ) :
    HasDerivAt (fun x => -(1 / θ) * Real.exp (x + (1 - Real.exp x) / θ))
      (-(1 / θ) * (Real.exp (t + (1 - Real.exp t) / θ) * (1 + (0 - Real.exp t) / θ))) t := by
  have hg : HasDerivAt (fun x => (1 - Real.exp x) / θ) ((0 - Real.exp t) / θ) t := by
    have h0 := ((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_exp t)).div_const θ
    exact h0
  have hs : HasDerivAt (fun x => x + (1 - Real.exp x) / θ) (1 + (0 - Real.exp t) / θ) t :=
    (hasDerivAt_id' t).add hg
  exact hs.exp.const_mul (-(1 / θ))

private theorem nelsen9_convex (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    ConvexOn ℝ (Ici 0) (fun t => Real.exp ((1 - Real.exp t) / θ)) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (f' := fun t => -(1 / θ) * Real.exp (t + (1 - Real.exp t) / θ))
    (f'' := fun t => -(1 / θ) * (Real.exp (t + (1 - Real.exp t) / θ) *
      (1 + (0 - Real.exp t) / θ))) ?_ ?_ ?_ ?_
  · intro t _
    exact (nelsen9_hasDerivAt θ t).continuousAt.continuousWithinAt
  · intro t _
    exact (nelsen9_hasDerivAt θ t).hasDerivWithinAt
  · intro t _
    exact (nelsen9_hasDerivAt2 θ t).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    show 0 ≤ -(1 / θ) * (Real.exp (t + (1 - Real.exp t) / θ) * (1 + (0 - Real.exp t) / θ))
    have hE : θ ≤ Real.exp t := by
      have := Real.add_one_le_exp t
      linarith
    have hq : 1 ≤ Real.exp t / θ := (one_le_div hθ).mpr hE
    have hD : 1 + (0 - Real.exp t) / θ ≤ 0 := by
      have h : (0 - Real.exp t) / θ = -(Real.exp t / θ) := by ring
      rw [h]
      linarith
    have hnn : 0 ≤ (1 / θ) * (Real.exp (t + (1 - Real.exp t) / θ) *
        (-(1 + (0 - Real.exp t) / θ))) :=
      mul_nonneg (div_nonneg zero_le_one hθ.le)
        (mul_nonneg (Real.exp_pos _).le (by linarith))
    have he : -(1 / θ) * (Real.exp (t + (1 - Real.exp t) / θ) *
        (1 + (0 - Real.exp t) / θ)) = (1 / θ) * (Real.exp (t + (1 - Real.exp t) / θ) *
        (-(1 + (0 - Real.exp t) / θ))) := by ring
    rw [he]
    exact hnn

/-- The inverse generator `s ↦ exp ((1 - exp s) / θ)` of the Gumbel–Barnett family, for
`0 < θ ≤ 1`. Its generator is `u ↦ ln (1 - θ ln u)`. -/
noncomputable def nelsen9Generator (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : BivariateGenerator where
  toFun t := Real.exp ((1 - Real.exp t) / θ)
  invFun u := Real.log (1 - θ * Real.log (u : ℝ))
  nonneg _ _ := (Real.exp_pos _).le
  antitone := by
    intro x _ y _ hxy
    show Real.exp ((1 - Real.exp y) / θ) ≤ Real.exp ((1 - Real.exp x) / θ)
    apply Real.exp_le_exp.mpr
    refine div_le_div_of_nonneg_right ?_ hθ.le
    have := Real.exp_le_exp.mpr hxy
    linarith
  convex := nelsen9_convex θ hθ h1
  inv_nonneg u _ := Real.log_nonneg (nelsen9_arg_ge_one θ hθ u)
  inv_antitone u v hu huv := by
    have hup := nelsen9_u_pos u hu
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    have hl := Real.log_le_log hup huv'
    have hmono : θ * Real.log (u : ℝ) ≤ θ * Real.log (v : ℝ) :=
      mul_le_mul_of_nonneg_left hl hθ.le
    show Real.log (1 - θ * Real.log (v : ℝ)) ≤ Real.log (1 - θ * Real.log (u : ℝ))
    exact Real.log_le_log (by linarith [nelsen9_arg_ge_one θ hθ v]) (by linarith)
  inv_one := by simp
  right_inv u hu := by
    have hup := nelsen9_u_pos u hu
    have hb : 0 < 1 - θ * Real.log (u : ℝ) :=
      lt_of_lt_of_le zero_lt_one (nelsen9_arg_ge_one θ hθ u)
    show Real.exp ((1 - Real.exp (Real.log (1 - θ * Real.log (u : ℝ)))) / θ) = (u : ℝ)
    rw [Real.exp_log hb]
    have h : (1 - (1 - θ * Real.log (u : ℝ))) / θ = Real.log (u : ℝ) := by
      rw [div_eq_iff hθ.ne']
      ring
    rw [h, Real.exp_log hup]

/-- Nelsen's family 9 (Gumbel–Barnett) for `0 < θ ≤ 1`. -/
noncomputable def nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) : Copula 2 :=
  (nelsen9Generator θ hθ h1).copula

theorem isArchimedean_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    IsArchimedean (nelsen9 θ hθ h1) :=
  (nelsen9Generator θ hθ h1).isArchimedean

/-- The Gumbel–Barnett CDF `u v exp (-θ ln u ln v)` on positive coordinates. -/
theorem cdf_nelsen9 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen9 θ hθ h1).cdf u =
      (u 0 : ℝ) * (u 1 : ℝ) * Real.exp (-(θ * Real.log (u 0 : ℝ) * Real.log (u 1 : ℝ))) := by
  have hb0 : 0 < 1 - θ * Real.log (u 0 : ℝ) :=
    lt_of_lt_of_le zero_lt_one (nelsen9_arg_ge_one θ hθ (u 0))
  have hb1 : 0 < 1 - θ * Real.log (u 1 : ℝ) :=
    lt_of_lt_of_le zero_lt_one (nelsen9_arg_ge_one θ hθ (u 1))
  have hp0 := nelsen9_u_pos (u 0) (hu 0)
  have hp1 := nelsen9_u_pos (u 1) (hu 1)
  rw [nelsen9, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_or_of_not (hu 0) (hu 1) _ _]
  change Real.exp ((1 - Real.exp (Real.log (1 - θ * Real.log (u 0 : ℝ)) +
    Real.log (1 - θ * Real.log (u 1 : ℝ)))) / θ) = _
  rw [Real.exp_add, Real.exp_log hb0, Real.exp_log hb1]
  have h : (1 - (1 - θ * Real.log (u 0 : ℝ)) * (1 - θ * Real.log (u 1 : ℝ))) / θ =
      Real.log (u 0 : ℝ) + Real.log (u 1 : ℝ) +
        -(θ * Real.log (u 0 : ℝ) * Real.log (u 1 : ℝ)) := by
    rw [div_eq_iff hθ.ne']
    ring
  rw [h, Real.exp_add, Real.exp_add, Real.exp_log hp0, Real.exp_log hp1]

/-- The Gumbel–Barnett CDF on the whole closed unit square, with grounded zero axes. -/
theorem nelsen9_cdf_full (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) (u v : I) :
    (nelsen9 θ hθ h1).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (u : ℝ) * (v : ℝ) * Real.exp (-(θ * Real.log (u : ℝ) * Real.log (v : ℝ))) := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen9 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen9 θ hθ h1).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  have h := cdf_nelsen9 θ hθ h1 ![u, v] hp
  rw [ite_or_of_not (hu) (hv) _ _]
  exact h

end ProbabilityTheory.Copula
