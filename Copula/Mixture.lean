/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Characterization

/-! # Finite mixtures of copulas -/

open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d n : ℕ}

theorem rectangleIncrement_sum (F : Fin n → (Fin d → I) → ℝ) (w : Fin n → ℝ)
    (a b : Fin d → I) :
    rectangleIncrement (fun u => ∑ j, w j * F j u) a b =
      ∑ j, w j * rectangleIncrement (F j) a b := by
  unfold rectangleIncrement partialIncrement
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Nonnegative finite mixtures preserve all classical copula conditions. -/
theorem isClassical_mixture (C : Fin n → Copula d) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    IsClassical (fun u => ∑ j, w j * (C j).cdf u) where
  normalized := by simp [hsum, cdf_one]
  grounded u i hi := by simp [cdf_eq_zero_of_coord_eq_zero _ u i hi]
  marginal i t := by simp [cdf_update_one, ← Finset.sum_mul, hsum]
  increasing a b hab := by
    rw [rectangleIncrement_sum]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) ((C j).rectangleIncrement_cdf_nonneg a b hab)

/-- A finite mixture with real nonnegative weights summing to one. -/
noncomputable def finiteMixture (C : Fin n → Copula d) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) : Copula d :=
  ofClassical _ (isClassical_mixture C w hw hsum)

@[simp] theorem cdf_finiteMixture (C : Fin n → Copula d) (w : Fin n → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (u : Fin d → I) :
    (finiteMixture C w hw hsum).cdf u = ∑ j, w j * (C j).cdf u :=
  congrFun (cdf_ofClassical _ _) u

/-- A two-component convex mixture. The first copula has weight `a`. -/
noncomputable def mix (C D : Copula d) (a : I) : Copula d :=
  finiteMixture ![C, D] ![(a : ℝ), 1 - (a : ℝ)]
    (by intro i; fin_cases i <;> simp <;> linarith [a.property.1, a.property.2])
    (by simp [Fin.sum_univ_two])

@[simp] theorem cdf_mix (C D : Copula d) (a : I) (u : Fin d → I) :
    (mix C D a).cdf u = (a : ℝ) * C.cdf u + (1 - (a : ℝ)) * D.cdf u := by
  simp [mix, Fin.sum_univ_two]

@[simp] theorem mix_zero (C D : Copula d) : mix C D 0 = D := by
  apply ext_cdf; intro u; simp

@[simp] theorem mix_one (C D : Copula d) : mix C D 1 = C := by
  apply ext_cdf; intro u; simp

end ProbabilityTheory.Copula
