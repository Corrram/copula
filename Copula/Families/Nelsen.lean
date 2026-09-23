/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Truncated
import Copula.Archimedean.Clayton

/-! # Numbered Archimedean families from Nelsen

The numbering follows Table 2 of Ansari and Rockel (arXiv:2310.17307v3).
All constructors return proved copula measures. Formulas are stated on positive
coordinates; the common groundedness theorem supplies the zero boundary.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Nelsen's family 2, including the lower Fréchet bound at one. -/
noncomputable def nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 :=
  (truncatedLinearGenerator.outerPower θ hθ).copula

/-- Genest–Ghoudi (Nelsen's family 15). -/
noncomputable def genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 :=
  ((truncatedLinearGenerator.outerPower θ hθ).innerPower θ hθ).copula

/-- Nelsen's family 12 is the `θ = 1` subfamily of BB1. -/
noncomputable def nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 := bb1 1 (by norm_num) θ hθ

/-- Nelsen's family 14 is the reciprocal-parameter subfamily of BB1. -/
noncomputable def nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 :=
  bb1 θ⁻¹ (inv_pos.mpr (by linarith)) θ hθ

theorem isArchimedean_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) : IsArchimedean (nelsen2 θ hθ) :=
  (truncatedLinearGenerator.outerPower θ hθ).isArchimedean

theorem isArchimedean_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    IsArchimedean (genestGhoudi θ hθ) :=
  ((truncatedLinearGenerator.outerPower θ hθ).innerPower θ hθ).isArchimedean

theorem isArchimedean_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) : IsArchimedean (nelsen12 θ hθ) :=
  isArchimedean_bb1 _ _ _ _

theorem isArchimedean_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) : IsArchimedean (nelsen14 θ hθ) :=
  isArchimedean_bb1 _ _ _ _

theorem cdf_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen2 θ hθ).cdf u =
      max 0 (1 - (((1 - (u 0 : ℝ)) ^ θ + (1 - (u 1 : ℝ)) ^ θ) ^ θ⁻¹)) := by
  rw [nelsen2, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  rfl

theorem cdf_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (genestGhoudi θ hθ).cdf u =
      (max 0 (1 - (((1 - (u 0 : ℝ) ^ θ⁻¹) ^ θ +
        (1 - (u 1 : ℝ) ^ θ⁻¹) ^ θ) ^ θ⁻¹))) ^ θ := by
  rw [genestGhoudi, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  rfl

theorem cdf_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen12 θ hθ).cdf u =
      (1 + (((u 0 : ℝ)⁻¹ - 1) ^ θ + ((u 1 : ℝ)⁻¹ - 1) ^ θ) ^ θ⁻¹)⁻¹ := by
  simpa [nelsen12, Real.rpow_neg_one] using cdf_bb1 1 (by norm_num) θ hθ u hu

theorem cdf_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I) (hu : ∀ i, u i ≠ 0) :
    (nelsen14 θ hθ).cdf u =
      (1 + (((u 0 : ℝ) ^ (-θ⁻¹) - 1) ^ θ +
        ((u 1 : ℝ) ^ (-θ⁻¹) - 1) ^ θ) ^ θ⁻¹) ^ (-θ) := by
  simpa [nelsen14] using cdf_bb1 θ⁻¹ (inv_pos.mpr (by linarith)) θ hθ u hu

@[simp] theorem nelsen2_one : nelsen2 1 le_rfl = countermonotonic := by simp [nelsen2]
@[simp] theorem genestGhoudi_one : genestGhoudi 1 le_rfl = countermonotonic := by
  simp [genestGhoudi]
@[simp] theorem nelsen12_one : nelsen12 1 le_rfl = clayton 2 1 (by norm_num) := by
  simp [nelsen12]
@[simp] theorem nelsen14_one : nelsen14 1 le_rfl = clayton 2 1 (by norm_num) := by
  simp [nelsen14]

/-- Promote an analytic positive-coordinate CDF formula to the closed square. -/
private theorem closedSquareCDF_of_positive (C : Copula 2) (F : I → I → ℝ)
    (h : ∀ u v : I, u ≠ 0 → v ≠ 0 → C.cdf ![u, v] = F u v)
    (u v : I) :
    C.cdf ![u, v] = if u = 0 ∨ v = 0 then 0 else F u v := by
  by_cases hu : u = 0
  · subst u
    simpa using C.cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    simpa [hu] using C.cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  simpa [hu, hv] using h u v hu hv

/-- Table 1's Nelsen 2 CDF on the closed square. -/
theorem nelsen2_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen2 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        max 0 (1 - (((1 - (u : ℝ)) ^ θ + (1 - (v : ℝ)) ^ θ) ^ θ⁻¹)) := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using cdf_nelsen2 θ hθ ![a, b] hp

/-- Table 1's Genest–Ghoudi (Nelsen 15) CDF on the closed square. -/
theorem genestGhoudi_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (genestGhoudi θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (max 0 (1 - (((1 - (u : ℝ) ^ θ⁻¹) ^ θ +
          (1 - (v : ℝ) ^ θ⁻¹) ^ θ) ^ θ⁻¹))) ^ θ := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using cdf_genestGhoudi θ hθ ![a, b] hp

/-- Table 1's Nelsen 12 CDF on the closed square. -/
theorem nelsen12_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen12 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + (((u : ℝ)⁻¹ - 1) ^ θ + ((v : ℝ)⁻¹ - 1) ^ θ) ^ θ⁻¹)⁻¹ := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using cdf_nelsen12 θ hθ ![a, b] hp

/-- Table 1's Nelsen 14 CDF on the closed square. -/
theorem nelsen14_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen14 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + (((u : ℝ) ^ (-θ⁻¹) - 1) ^ θ +
          ((v : ℝ) ^ (-θ⁻¹) - 1) ^ θ) ^ θ⁻¹) ^ (-θ) := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using cdf_nelsen14 θ hθ ![a, b] hp


end ProbabilityTheory.Copula
