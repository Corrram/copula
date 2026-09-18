/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Exponential
import Copula.Archimedean.Power
import Copula.ExtremeValue.Basic

/-! # Bivariate Gumbel–Hougaard (logistic extreme-value) copulas -/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Gumbel's inverse generator `exp(-t^(1/θ))`. -/
noncomputable def gumbelGenerator (θ : ℝ) (hθ : 1 ≤ θ) : BivariateGenerator :=
  exponentialGenerator.outerPower θ hθ

/-- The bivariate Gumbel–Hougaard copula, including independence at `θ = 1`. -/
noncomputable def gumbel (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 :=
  (gumbelGenerator θ hθ).copula

theorem isArchimedean_gumbel (θ : ℝ) (hθ : 1 ≤ θ) : IsArchimedean (gumbel θ hθ) :=
  (gumbelGenerator θ hθ).isArchimedean

theorem cdf_gumbel (θ : ℝ) (hθ : 1 ≤ θ) (u : Fin 2 → I)
    (hu : ∀ i, u i ≠ 0) :
    (gumbel θ hθ).cdf u =
      Real.exp (-(((-Real.log (u 0)) ^ θ + (-Real.log (u 1)) ^ θ) ^ θ⁻¹)) := by
  rw [gumbel, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    ite_eq_right (not_or.mpr ⟨hu 0, hu 1⟩)]
  rfl

@[simp] theorem gumbel_one : gumbel 1 le_rfl = independence 2 := by
  simp [gumbel, gumbelGenerator]

theorem isExtremeValue_gumbel (θ : ℝ) (hθ : 1 ≤ θ) : IsExtremeValue (gumbel θ hθ) := by
  intro u t ht
  by_cases hu : ∀ i, u i ≠ 0
  · have hup (i) : 0 < (u i : ℝ) := lt_of_le_of_ne (u i).property.1 (Ne.symm (by
      intro h; exact hu i (Subtype.ext h)))
    have hpow (i) : unitPower (u i) t ht.le ≠ 0 := by
      intro h
      have hz := congrArg (fun v : I => (v : ℝ)) h
      exact (Real.rpow_pos_of_pos (hup i) t).ne' hz
    rw [cdf_gumbel θ hθ _ hpow, cdf_gumbel θ hθ u hu]
    simp only [coe_unitPower, Real.log_rpow (hup _), neg_mul_eq_mul_neg]
    have hlog (i) : 0 ≤ -Real.log (u i) :=
      neg_nonneg.mpr (Real.log_nonpos (u i).property.1 (u i).property.2)
    rw [Real.mul_rpow ht.le (hlog 0), Real.mul_rpow ht.le (hlog 1), ← mul_add,
      Real.mul_rpow (Real.rpow_nonneg ht.le _) (add_nonneg
        (Real.rpow_nonneg (hlog 0) _) (Real.rpow_nonneg (hlog 1) _)),
      Real.rpow_rpow_inv ht.le (by linarith : θ ≠ 0)]
    rw [← Real.exp_mul]
    congr 1
    ring
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    have hp : unitPower (u i) t ht.le = 0 := by
      ext; simp [hi, Real.zero_rpow ht.ne']
    rw [cdf_eq_zero_of_coord_eq_zero _ _ i hp, cdf_eq_zero_of_coord_eq_zero _ u i hi,
      Real.zero_rpow ht.ne']

/-- An asymmetric logistic (Tawn) copula with two weights and `θ ≥ 1`. -/
noncomputable def tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) : Copula 2 :=
  maxProduct (gumbel θ hθ) (independence 2) ![α, β]

theorem isExtremeValue_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    IsExtremeValue (tawn θ hθ α β) :=
  (isExtremeValue_gumbel θ hθ).maxProduct (isExtremeValue_independence 2) _

end ProbabilityTheory.Copula
