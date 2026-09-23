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

/-- Table 1's Gumbel–Hougaard CDF on the whole closed square. The paper's
logarithmic expression applies to positive coordinates; copula groundedness
supplies the values on the two zero axes. -/
theorem gumbel_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (gumbel θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.exp (-(((-Real.log u) ^ θ + (-Real.log v) ^ θ) ^ θ⁻¹)) := by
  by_cases hu : u = 0
  · subst u
    simpa using (gumbel θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    simpa using (gumbel θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  rw [cdf_gumbel θ hθ ![u, v] hp]
  simp [hu, hv]


/-- Table 1's Tawn CDF at positive coordinates, with all finite shape and
weight endpoints included. -/
theorem tawn_cdf_positive (θ : ℝ) (hθ : 1 ≤ θ) (α β u v : I)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (tawn θ hθ α β).cdf ![u, v] =
      (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) ^ (1 - (β : ℝ)) *
        Real.exp (-(((α : ℝ) * (-Real.log u)) ^ θ +
          ((β : ℝ) * (-Real.log v)) ^ θ) ^ θ⁻¹) := by
  have hup : (0 : ℝ) < u := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hvp : (0 : ℝ) < v := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have hpow (i : Fin 2) :
      unitPower (![u, v] i) (![α, β] i) (![α, β] i).property.1 ≠ 0 := by
    intro he
    have hz := congrArg (fun x : I => (x : ℝ)) he
    fin_cases i
    · exact (Real.rpow_pos_of_pos hup _).ne' (by simpa using hz)
    · exact (Real.rpow_pos_of_pos hvp _).ne' (by simpa using hz)
  rw [tawn, cdf_maxProduct,
    cdf_gumbel θ hθ _ hpow, cdf_independence]
  simp only [Fin.prod_univ_two, coe_unitPower,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq, Real.log_rpow hup, Real.log_rpow hvp]
  have he1 : -((α : ℝ) * Real.log (u : ℝ)) =
      (α : ℝ) * (-Real.log u) := by ring
  have he2 : -((β : ℝ) * Real.log (v : ℝ)) =
      (β : ℝ) * (-Real.log v) := by ring
  rw [he1, he2]
  ring

/-- The Tawn formula on the closed square, making its zero-axis extension
explicit rather than applying `log 0` in the paper's analytic notation. -/
theorem tawn_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (α β u v : I) :
    (tawn θ hθ α β).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) ^ (1 - (β : ℝ)) *
          Real.exp (-(((α : ℝ) * (-Real.log u)) ^ θ +
            ((β : ℝ) * (-Real.log v)) ^ θ) ^ θ⁻¹) := by
  by_cases hu : u = 0
  · subst u
    simpa using (tawn θ hθ α β).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    simpa using (tawn θ hθ α β).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [tawn_cdf_positive θ hθ α β u v hu hv]
  simp [hu, hv]


/-- Both zero Tawn weights give independence, for every admissible shape. -/
theorem tawn_zero_zero (θ : ℝ) (hθ : 1 ≤ θ) :
    tawn θ hθ 0 0 = independence 2 := by
  have hw : (![ (0 : I), (0 : I)] : Fin 2 → I) = fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  simp [tawn, hw]

/-- Both unit Tawn weights recover the Gumbel–Hougaard copula. -/
theorem tawn_one_one (θ : ℝ) (hθ : 1 ≤ θ) :
    tawn θ hθ 1 1 = gumbel θ hθ := by
  have hw : (![ (1 : I), (1 : I)] : Fin 2 → I) = fun _ => 1 := by
    funext i
    fin_cases i <;> rfl
  simp [tawn, hw]

private theorem tawn_power_complement (u a : I) :
    (unitPower u a a.property.1 : ℝ) *
      (unitPower u (unitInterval.symm a) (unitInterval.symm a).property.1 : ℝ) =
        (u : ℝ) := by
  change (u : ℝ) ^ (a : ℝ) * (u : ℝ) ^ (1 - (a : ℝ)) = (u : ℝ)
  by_cases hu : (u : ℝ) = 0
  · by_cases ha : (a : ℝ) = 0
    · simp [hu, ha]
    · simp [hu, Real.zero_rpow ha]
  · rw [← Real.rpow_add (lt_of_le_of_ne u.property.1 (Ne.symm hu)),
      add_sub_cancel, Real.rpow_one]

theorem tawn_zero_left (θ : ℝ) (hθ : 1 ≤ θ) (β : I) :
    tawn θ hθ 0 β = independence 2 := by
  apply ext_cdf
  intro u
  rw [tawn, cdf_maxProduct]
  have hvec : (fun i : Fin 2 =>
      unitPower (u i) (![ (0 : I), β] i) (![ (0 : I), β] i).property.1) =
      Function.update (fun _ : Fin 2 => (1 : I)) 1
        (unitPower (u 1) β β.property.1) := by
    funext i
    fin_cases i <;> simp
  rw [hvec, (gumbel θ hθ).cdf_update_one]
  rw [cdf_independence, cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [unitInterval.symm_zero]
  simp only [coe_unitPower, unitInterval.coe_symm_eq]
  have hcoe : ((1 : I) : ℝ) = (1 : ℝ) := rfl
  rw [hcoe, Real.rpow_one]
  have hp : (u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ)) = (u 1 : ℝ) := by
    simpa only [coe_unitPower, unitInterval.coe_symm_eq] using
      tawn_power_complement (u 1) β
  calc
    _ = (u 0 : ℝ) * ((u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ))) := by ring
    _ = _ := by rw [hp]


theorem tawn_zero_right (θ : ℝ) (hθ : 1 ≤ θ) (α : I) :
    tawn θ hθ α 0 = independence 2 := by
  apply ext_cdf
  intro u
  rw [tawn, cdf_maxProduct]
  have hvec : (fun i : Fin 2 =>
      unitPower (u i) (![ α, (0 : I)] i) (![ α, (0 : I)] i).property.1) =
      Function.update (fun _ : Fin 2 => (1 : I)) 0
        (unitPower (u 0) α α.property.1) := by
    funext i
    fin_cases i <;> simp
  rw [hvec, (gumbel θ hθ).cdf_update_one]
  rw [cdf_independence, cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [unitInterval.symm_zero]
  simp only [coe_unitPower, unitInterval.coe_symm_eq]
  have hcoe : ((1 : I) : ℝ) = (1 : ℝ) := rfl
  rw [hcoe, Real.rpow_one]
  have hp : (u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ)) = (u 0 : ℝ) := by
    simpa only [coe_unitPower, unitInterval.coe_symm_eq] using
      tawn_power_complement (u 0) α
  calc
    _ = ((u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ))) * (u 1 : ℝ) := by ring
    _ = _ := by rw [hp]


theorem tawn_shape_one (α β : I) :
    tawn 1 le_rfl α β = independence 2 := by
  apply ext_cdf
  intro u
  rw [tawn, gumbel_one, cdf_maxProduct,
    cdf_independence, cdf_independence, cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    coe_unitPower, unitInterval.coe_symm_eq]
  have h0 : (u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ)) = (u 0 : ℝ) := by
    simpa only [coe_unitPower, unitInterval.coe_symm_eq] using
      tawn_power_complement (u 0) α
  have h1 : (u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ)) = (u 1 : ℝ) := by
    simpa only [coe_unitPower, unitInterval.coe_symm_eq] using
      tawn_power_complement (u 1) β
  calc
    _ = ((u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ))) *
        ((u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ))) := by ring
    _ = _ := by rw [h0, h1]



end ProbabilityTheory.Copula
