/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Basic
import Copula.Archimedean.TheoryConvex

/-! # Nelsen's family 20

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 20 (Section 4.2):
generator `φ(t) = exp (t ^ (-θ)) - e`, inverse generator `ψ(s) = (log (s + e)) ^ (-1/θ)`,
and copula `C(u, v) = (log (exp (u ^ (-θ)) + exp (v ^ (-θ)) - e)) ^ (-1/θ)`, for `θ > 0`.

The inverse generator is a positive concave function raised to a nonpositive power, hence
convex. This is the full parameter range of Nelsen's table (the limiting case `θ = 0` is
not a member of the family in this module).
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen20_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen20_log_pos {t : ℝ} (ht : 0 ≤ t) : 0 < Real.log (t + Real.exp 1) :=
  lt_of_lt_of_le zero_lt_one (le_log_add_exp ht 1)

/-- The inverse generator `s ↦ (log (s + e)) ^ (-1/θ)` of Nelsen's family 20, for `θ > 0`.
Its generator is `u ↦ exp (u ^ (-θ)) - e`. -/
noncomputable def nelsen20Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun t := Real.log (t + Real.exp 1) ^ (-θ⁻¹)
  invFun u := Real.exp ((u : ℝ) ^ (-θ)) - Real.exp 1
  nonneg t ht := Real.rpow_nonneg (nelsen20_log_pos ht).le _
  antitone x hx y _ hxy := by
    have hx0 : 0 ≤ x := hx
    have hxe : 0 < x + Real.exp 1 := by
      have := Real.exp_pos 1
      linarith
    show Real.log (y + Real.exp 1) ^ (-θ⁻¹) ≤ Real.log (x + Real.exp 1) ^ (-θ⁻¹)
    exact Real.rpow_le_rpow_of_nonpos (nelsen20_log_pos hx0)
      (Real.log_le_log hxe (by linarith)) (neg_nonpos.mpr (inv_nonneg.mpr hθ.le))
  convex := convexOn_rpow_comp_nonpos (f := fun s : ℝ => Real.log (s + Real.exp 1))
    (neg_nonpos.mpr (inv_nonneg.mpr hθ.le)) (concaveOn_log_add (Real.exp_pos 1))
    (fun x hx => nelsen20_log_pos (show 0 ≤ x from hx))
  inv_nonneg u hu := by
    have hup := nelsen20_u_pos u hu
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hup u.property.2 (neg_nonpos.mpr hθ.le)
  inv_antitone u v hu huv := by
    have hup := nelsen20_u_pos u hu
    have huv' : (u : ℝ) ≤ (v : ℝ) := huv
    have h := Real.rpow_le_rpow_of_nonpos hup huv' (neg_nonpos.mpr hθ.le)
    have h2 := Real.exp_le_exp.mpr h
    show Real.exp ((v : ℝ) ^ (-θ)) - Real.exp 1 ≤ Real.exp ((u : ℝ) ^ (-θ)) - Real.exp 1
    linarith
  inv_one := by simp
  right_inv u hu := by
    have hup := nelsen20_u_pos u hu
    show Real.log (Real.exp ((u : ℝ) ^ (-θ)) - Real.exp 1 + Real.exp 1) ^ (-θ⁻¹) = (u : ℝ)
    rw [sub_add_cancel, Real.log_exp, ← Real.rpow_mul hup.le, neg_mul_neg,
      mul_inv_cancel₀ hθ.ne', Real.rpow_one]

/-- Nelsen's family 20 for `θ > 0`. -/
noncomputable def nelsen20 (θ : ℝ) (hθ : 0 < θ) : Copula 2 :=
  (nelsen20Generator θ hθ).copula

theorem isArchimedean_nelsen20 (θ : ℝ) (hθ : 0 < θ) : IsArchimedean (nelsen20 θ hθ) :=
  (nelsen20Generator θ hθ).isArchimedean

/-- The CDF of Nelsen's family 20 on positive coordinates. -/
theorem cdf_nelsen20 (θ : ℝ) (hθ : 0 < θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen20 θ hθ).cdf u =
      Real.log (Real.exp ((u 0 : ℝ) ^ (-θ)) + Real.exp ((u 1 : ℝ) ^ (-θ)) - Real.exp 1) ^
        (-θ⁻¹) := by
  rw [nelsen20, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_or_of_not (hu 0) (hu 1) _ _]
  change Real.log (Real.exp ((u 0 : ℝ) ^ (-θ)) - Real.exp 1 +
    (Real.exp ((u 1 : ℝ) ^ (-θ)) - Real.exp 1) + Real.exp 1) ^ (-θ⁻¹) = _
  have h : Real.exp ((u 0 : ℝ) ^ (-θ)) - Real.exp 1 +
      (Real.exp ((u 1 : ℝ) ^ (-θ)) - Real.exp 1) + Real.exp 1 =
      Real.exp ((u 0 : ℝ) ^ (-θ)) + Real.exp ((u 1 : ℝ) ^ (-θ)) - Real.exp 1 := by ring
  rw [h]

/-- Nelsen's family 20 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen20_cdf_full (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (nelsen20 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.log (Real.exp ((u : ℝ) ^ (-θ)) + Real.exp ((v : ℝ) ^ (-θ)) - Real.exp 1) ^
          (-θ⁻¹) := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen20 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen20 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  have h := cdf_nelsen20 θ hθ ![u, v] hp
  rw [ite_or_of_not (hu) (hv) _ _]
  exact h

end ProbabilityTheory.Copula
