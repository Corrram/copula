/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.ChatterjeeMixture
import Copula.Families.Frechet

/-! # Chatterjee's xi of Fréchet and Mardia copulas

The Fréchet formula is `(a-b)^2 + a*b`; the Mardia formula is
`θ^4 * (1+3*θ^2) / 4`. The proof includes all boundary and singular cases,
using the conditional-CDF mixture formula rather than a copula density.
See Ansari and Rockel, *Dependence properties of bivariate copula families*, Table 6.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

@[simp] theorem frechet_zero_zero : frechet 0 0 le_rfl le_rfl (by norm_num) = independence 2 := by
  apply ext_cdf
  intro u
  simp [cdf_frechet]

/-- Split off the independent part, then normalize the weights of `M` and `W`. -/
theorem frechet_eq_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hpos : 0 < a + b) :
    frechet a b ha hb hab =
      ((comonotonic 2).mix countermonotonic
        ⟨a / (a + b), div_nonneg ha hpos.le, (div_le_one hpos).2 (by linarith)⟩).mix
        (independence 2) ⟨a + b, add_nonneg ha hb, hab⟩ := by
  apply ext_cdf
  intro u
  simp only [cdf_frechet, cdf_mix]
  field_simp [ne_of_gt hpos]
  ring

theorem chatterjeeXi_frechet (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).chatterjeeXi = (a - b) ^ 2 + a * b := by
  by_cases hz : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst a
    subst b
    simp
  have hpos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  rw [frechet_eq_mix a b ha hb hab hpos, chatterjeeXi_mix_independence,
    chatterjeeXi_mix_comonotonic_countermonotonic]
  dsimp
  field_simp [hz]
  ring

theorem chatterjeeXi_mardia (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).chatterjeeXi = θ ^ 4 * (1 + 3 * θ ^ 2) / 4 := by
  rw [mardia, chatterjeeXi_frechet]
  ring

theorem chatterjeeXi_frechet_eq_zero_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (frechet a b ha hb hab).chatterjeeXi = 0 ↔ a = 0 ∧ b = 0 := by
  rw [chatterjeeXi_frechet]
  constructor
  · intro h
    have hab0 : a * b = 0 := by nlinarith [sq_nonneg (a - b), mul_nonneg ha hb]
    rcases mul_eq_zero.mp hab0 with h0 | h0
    · subst a
      constructor
      · rfl
      · nlinarith [sq_nonneg b]
    · subst b
      constructor
      · nlinarith [sq_nonneg a]
      · rfl
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem chatterjeeXi_mardia_eq_zero_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (mardia θ hθ).chatterjeeXi = 0 ↔ θ = 0 := by
  rw [chatterjeeXi_mardia]
  have hp : 1 + 3 * θ ^ 2 ≠ 0 := by nlinarith [sq_nonneg θ]
  simp [hp]

end ProbabilityTheory.Copula
