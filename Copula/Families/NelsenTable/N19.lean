/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Basic
import Copula.Archimedean.TheoryConvex

/-! # Nelsen's family 19

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 19 (Section 4.2):
generator `φ(t) = exp (θ / t) - exp θ`, inverse generator `ψ(s) = θ / log (s + exp θ)`,
and copula `C(u, v) = θ / log (exp (θ / u) + exp (θ / v) - exp θ)`, for `θ > 0`.

The inverse generator is a positive constant divided by a positive concave function, hence
convex. This is the full parameter range of Nelsen's table (the limiting case `θ = 0` is
not a member of the family in this module).
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen19_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen19_log_pos (θ : ℝ) (hθ : 0 < θ) {t : ℝ} (ht : 0 ≤ t) :
    0 < Real.log (t + Real.exp θ) :=
  lt_of_lt_of_le hθ (le_log_add_exp ht θ)

/-- The inverse generator `s ↦ θ / log (s + exp θ)` of Nelsen's family 19, for `θ > 0`.
Its generator is `u ↦ exp (θ / u) - exp θ`. -/
noncomputable def nelsen19Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun t := θ / Real.log (t + Real.exp θ)
  invFun u := Real.exp (θ / (u : ℝ)) - Real.exp θ
  nonneg t ht := div_nonneg hθ.le (nelsen19_log_pos θ hθ ht).le
  antitone x hx y _ hxy := by
    have hx0 : 0 ≤ x := hx
    have hxe : 0 < x + Real.exp θ := by
      have := Real.exp_pos θ
      linarith
    show θ / Real.log (y + Real.exp θ) ≤ θ / Real.log (x + Real.exp θ)
    exact div_le_div_of_nonneg_left hθ.le (nelsen19_log_pos θ hθ hx0)
      (Real.log_le_log hxe (by linarith))
  convex := convexOn_div_comp (f := fun s : ℝ => Real.log (s + Real.exp θ)) hθ.le
    (concaveOn_log_add (Real.exp_pos θ))
    (fun x hx => nelsen19_log_pos θ hθ (show 0 ≤ x from hx))
  inv_nonneg u hu := by
    have hup := nelsen19_u_pos u hu
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hup).mpr
    linarith [mul_nonneg hθ.le (sub_nonneg.mpr u.property.2)]
  inv_antitone u v hu huv := by
    have hup := nelsen19_u_pos u hu
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    have h := div_le_div_of_nonneg_left hθ.le hup huv'
    have h2 := Real.exp_le_exp.mpr h
    show Real.exp (θ / (v : ℝ)) - Real.exp θ ≤ Real.exp (θ / (u : ℝ)) - Real.exp θ
    linarith
  inv_one := by simp
  right_inv u _ := by
    show θ / Real.log (Real.exp (θ / (u : ℝ)) - Real.exp θ + Real.exp θ) = (u : ℝ)
    rw [sub_add_cancel, Real.log_exp]
    exact div_div_cancel₀ hθ.ne'

/-- Nelsen's family 19 for `θ > 0`. -/
noncomputable def nelsen19 (θ : ℝ) (hθ : 0 < θ) : Copula 2 :=
  (nelsen19Generator θ hθ).copula

theorem isArchimedean_nelsen19 (θ : ℝ) (hθ : 0 < θ) : IsArchimedean (nelsen19 θ hθ) :=
  (nelsen19Generator θ hθ).isArchimedean

/-- The CDF of Nelsen's family 19 on positive coordinates. -/
theorem cdf_nelsen19 (θ : ℝ) (hθ : 0 < θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen19 θ hθ).cdf u =
      θ / Real.log (Real.exp (θ / (u 0 : ℝ)) + Real.exp (θ / (u 1 : ℝ)) - Real.exp θ) := by
  rw [nelsen19, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_or_of_not (hu 0) (hu 1) _ _]
  change θ / Real.log (Real.exp (θ / (u 0 : ℝ)) - Real.exp θ +
    (Real.exp (θ / (u 1 : ℝ)) - Real.exp θ) + Real.exp θ) = _
  have h : Real.exp (θ / (u 0 : ℝ)) - Real.exp θ +
      (Real.exp (θ / (u 1 : ℝ)) - Real.exp θ) + Real.exp θ =
      Real.exp (θ / (u 0 : ℝ)) + Real.exp (θ / (u 1 : ℝ)) - Real.exp θ := by ring
  rw [h]

/-- Nelsen's family 19 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen19_cdf_full (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (nelsen19 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        θ / Real.log (Real.exp (θ / (u : ℝ)) + Real.exp (θ / (v : ℝ)) - Real.exp θ) := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen19 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen19 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  have h := cdf_nelsen19 θ hθ ![u, v] hp
  rw [ite_or_of_not (hu) (hv) _ _]
  exact h

end ProbabilityTheory.Copula
