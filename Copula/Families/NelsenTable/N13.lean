/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Exponential
import Copula.Archimedean.Power
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Nelsen's family 13

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 13 (Section 4.2):
generator `φ(t) = (1 - ln t)^θ - 1`, inverse generator `ψ(s) = exp (1 - (1 + s)^(1/θ))`,
and copula `C(u, v) = exp (1 - ((1 - ln u)^θ + (1 - ln v)^θ - 1)^(1/θ))`.

This module covers Nelsen's whole parameter range `θ > 0`. Convexity of the inverse
generator is proved from its second derivative: with `p = 1/θ`,
`ψ''(s) = p ψ(s) (1 + s)^(p - 2) (p (1 + s)^p - (p - 1)) ≥ 0`, since `(1 + s)^p ≥ 1`.
At `θ = 1` the family is independence (`C_1 = Π` in Nelsen's table).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen13_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen13_base_ge_one (u : I) : 1 ≤ 1 - Real.log (u : ℝ) := by
  have h := Real.log_nonpos u.property.1 u.property.2
  linarith

private theorem nelsen13_hasDerivAt (p : ℝ) {t : ℝ} (ht : 0 < 1 + t) :
    HasDerivAt (fun x => Real.exp (1 - (1 + x) ^ p))
      (-p * (Real.exp (1 - (1 + t) ^ p) * (1 + t) ^ (p - 1))) t := by
  have h1 : HasDerivAt (fun x => (1 + x) ^ p) (1 * p * (1 + t) ^ (p - 1)) t :=
    ((hasDerivAt_id t).const_add 1).rpow_const (Or.inl ht.ne')
  have h2 := (h1.const_sub 1).exp
  refine h2.congr_deriv ?_
  ring

private theorem nelsen13_hasDerivAt2 (p : ℝ) {t : ℝ} (ht : 0 < 1 + t) :
    HasDerivAt (fun x => -p * (Real.exp (1 - (1 + x) ^ p) * (1 + x) ^ (p - 1)))
      (p * Real.exp (1 - (1 + t) ^ p) *
        (p * ((1 + t) ^ (p - 1) * (1 + t) ^ (p - 1)) - (p - 1) * (1 + t) ^ (p - 1 - 1))) t := by
  have h1 : HasDerivAt (fun x => (1 + x) ^ p) (1 * p * (1 + t) ^ (p - 1)) t :=
    ((hasDerivAt_id t).const_add 1).rpow_const (Or.inl ht.ne')
  have h2 := (h1.const_sub 1).exp
  have h3 : HasDerivAt (fun x => (1 + x) ^ (p - 1)) (1 * (p - 1) * (1 + t) ^ (p - 1 - 1)) t :=
    ((hasDerivAt_id t).const_add 1).rpow_const (Or.inl ht.ne')
  have h4 := (h2.mul h3).const_mul (-p)
  refine h4.congr_deriv ?_
  ring

private theorem nelsen13_convexOn (p : ℝ) (hp : 0 < p) :
    ConvexOn ℝ (Ici 0) (fun t => Real.exp (1 - (1 + t) ^ p)) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    (f' := fun t => -p * (Real.exp (1 - (1 + t) ^ p) * (1 + t) ^ (p - 1)))
    (f'' := fun t => p * Real.exp (1 - (1 + t) ^ p) *
        (p * ((1 + t) ^ (p - 1) * (1 + t) ^ (p - 1)) - (p - 1) * (1 + t) ^ (p - 1 - 1)))
    ?_ ?_ ?_ ?_
  · intro t ht
    have ht0 : 0 ≤ t := ht
    exact (nelsen13_hasDerivAt p (by linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (nelsen13_hasDerivAt p (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (nelsen13_hasDerivAt2 p (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hb : 0 < 1 + t := by linarith
    show 0 ≤ p * Real.exp (1 - (1 + t) ^ p) *
        (p * ((1 + t) ^ (p - 1) * (1 + t) ^ (p - 1)) - (p - 1) * (1 + t) ^ (p - 1 - 1))
    have hsplit : (1 + t) ^ (p - 1) * (1 + t) ^ (p - 1) = (1 + t) ^ (p - 1 - 1) * (1 + t) ^ p := by
      rw [← Real.rpow_add hb, ← Real.rpow_add hb]
      ring_nf
    have hge : 1 ≤ (1 + t) ^ p := Real.one_le_rpow (by linarith) hp.le
    have hq : 0 < (1 + t) ^ (p - 1 - 1) := Real.rpow_pos_of_pos hb _
    rw [hsplit]
    apply mul_nonneg (mul_nonneg hp.le (Real.exp_pos _).le)
    have : (p - 1) * (1 + t) ^ (p - 1 - 1) ≤ p * ((1 + t) ^ (p - 1 - 1) * (1 + t) ^ p) := by
      nlinarith [mul_le_mul_of_nonneg_left hge (mul_nonneg hp.le hq.le)]
    linarith

/-- The inverse generator `s ↦ exp (1 - (1 + s)^(1/θ))` of Nelsen's family 13, for `θ > 0`.
Its generator is `u ↦ (1 - ln u)^θ - 1`. -/
noncomputable def nelsen13Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun t := Real.exp (1 - (1 + t) ^ θ⁻¹)
  invFun u := (1 - Real.log (u : ℝ)) ^ θ - 1
  nonneg _ _ := (Real.exp_pos _).le
  antitone x hx y _ hxy := by
    have hx0 : 0 ≤ x := hx
    show Real.exp (1 - (1 + y) ^ θ⁻¹) ≤ Real.exp (1 - (1 + x) ^ θ⁻¹)
    apply Real.exp_le_exp.mpr
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + x) (by linarith : 1 + x ≤ 1 + y)
      (inv_nonneg.mpr (by linarith : 0 ≤ θ))
    linarith
  convex := nelsen13_convexOn θ⁻¹ (inv_pos.mpr hθ)
  inv_nonneg u _ := by
    apply sub_nonneg.mpr
    exact Real.one_le_rpow (nelsen13_base_ge_one u) (by linarith)
  inv_antitone u v hu huv := by
    have hup := nelsen13_u_pos u hu
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    have hl := Real.log_le_log hup huv'
    have hv1 : 0 ≤ 1 - Real.log (v : ℝ) := by linarith [nelsen13_base_ge_one v]
    have h := Real.rpow_le_rpow hv1
      (by linarith : 1 - Real.log (v : ℝ) ≤ 1 - Real.log (u : ℝ)) (by linarith : 0 ≤ θ)
    show (1 - Real.log (v : ℝ)) ^ θ - 1 ≤ (1 - Real.log (u : ℝ)) ^ θ - 1
    linarith
  inv_one := by simp
  right_inv u hu := by
    have hup := nelsen13_u_pos u hu
    have hb0 : 0 ≤ 1 - Real.log (u : ℝ) := by linarith [nelsen13_base_ge_one u]
    show Real.exp (1 - (1 + ((1 - Real.log (u : ℝ)) ^ θ - 1)) ^ θ⁻¹) = (u : ℝ)
    have h1 : 1 + ((1 - Real.log (u : ℝ)) ^ θ - 1) = (1 - Real.log (u : ℝ)) ^ θ := by ring
    rw [h1, Real.rpow_rpow_inv hb0 hθ.ne', sub_sub_cancel, Real.exp_log hup]

/-- Nelsen's family 13 for `θ > 0`. -/
noncomputable def nelsen13 (θ : ℝ) (hθ : 0 < θ) : Copula 2 :=
  (nelsen13Generator θ hθ).copula

theorem isArchimedean_nelsen13 (θ : ℝ) (hθ : 0 < θ) : IsArchimedean (nelsen13 θ hθ) :=
  (nelsen13Generator θ hθ).isArchimedean

/-- The CDF of Nelsen's family 13 on positive coordinates. -/
theorem cdf_nelsen13 (θ : ℝ) (hθ : 0 < θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen13 θ hθ).cdf u =
      Real.exp (1 - (((1 - Real.log (u 0 : ℝ)) ^ θ + (1 - Real.log (u 1 : ℝ)) ^ θ - 1) ^
        θ⁻¹)) := by
  rw [nelsen13, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_or_of_not (hu 0) (hu 1) _ _]
  change Real.exp (1 - (1 + ((1 - Real.log (u 0 : ℝ)) ^ θ - 1 +
    ((1 - Real.log (u 1 : ℝ)) ^ θ - 1))) ^ θ⁻¹) = _
  have h : (1 : ℝ) + ((1 - Real.log (u 0 : ℝ)) ^ θ - 1 + ((1 - Real.log (u 1 : ℝ)) ^ θ - 1)) =
      (1 - Real.log (u 0 : ℝ)) ^ θ + (1 - Real.log (u 1 : ℝ)) ^ θ - 1 := by ring
  rw [h]

/-- Nelsen's family 13 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen13_cdf_full (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (nelsen13 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.exp (1 - (((1 - Real.log (u : ℝ)) ^ θ + (1 - Real.log (v : ℝ)) ^ θ - 1) ^
          θ⁻¹)) := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen13 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen13 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  have h := cdf_nelsen13 θ hθ ![u, v] hp
  rw [ite_or_of_not (hu) (hv) _ _]
  exact h

/-- At `θ = 1` Nelsen's family 13 is independence. -/
@[simp] theorem nelsen13_one : nelsen13 1 one_pos = independence 2 := by
  apply ext_cdf
  intro u
  by_cases hu : ∀ i, u i ≠ 0
  · rw [cdf_nelsen13 1 one_pos u hu, cdf_independence, Fin.prod_univ_two]
    have ha := nelsen13_u_pos (u 0) (hu 0)
    have hb := nelsen13_u_pos (u 1) (hu 1)
    have key : Real.exp (Real.log (u 0 : ℝ) + Real.log (u 1 : ℝ)) =
        (u 0 : ℝ) * (u 1 : ℝ) := by
      rw [Real.exp_add, Real.exp_log ha, Real.exp_log hb]
    rw [← key]
    simp only [Real.rpow_one, inv_one]
    congr 1
    ring
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    rw [cdf_eq_zero_of_coord_eq_zero _ u i hi, cdf_eq_zero_of_coord_eq_zero _ u i hi]

end ProbabilityTheory.Copula
