/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ClaytonTotalPositivity

/-! # MTP2 of the positive-Clayton density formula

The measure equality needed for `HasMTP2Density` remains a separate theorem.
-/

open Real
open scoped unitInterval

namespace ProbabilityTheory.Copula

private noncomputable def claytonKernel (θ q : ℝ) (u v : I) : ℝ :=
  if u = 0 ∨ v = 0 then 0
  else ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) ^ q

private theorem claytonKernelTP2 (θ q : ℝ) (hθ : 0 < θ) (hq : q ≤ 0) :
    IsTP2 (claytonKernel θ q) := by
  intro a b c d hab hcd
  by_cases ha0 : a = 0
  · subst a
    simp [claytonKernel]
  by_cases hc0 : c = 0
  · subst c
    simp [claytonKernel]
  have ha : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1
    (Ne.symm (fun h => ha0 (Subtype.ext h)))
  have hb : 0 < (b : ℝ) := lt_of_lt_of_le ha hab
  have hc : 0 < (c : ℝ) := lt_of_le_of_ne c.property.1
    (Ne.symm (fun h => hc0 (Subtype.ext h)))
  have hd : 0 < (d : ℝ) := lt_of_lt_of_le hc hcd
  have hb0 : b ≠ 0 := by
    intro e
    subst b
    norm_num at hb
  have hd0 : d ≠ 0 := by
    intro e
    subst d
    norm_num at hd
  let x := (a : ℝ) ^ (-θ)
  let X := (b : ℝ) ^ (-θ)
  let y := (c : ℝ) ^ (-θ)
  let Y := (d : ℝ) ^ (-θ)
  have hx : X ≤ x := Real.rpow_le_rpow_of_nonpos ha hab (by linarith)
  have hy : Y ≤ y := Real.rpow_le_rpow_of_nonpos hc hcd (by linarith)
  have hx1 : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hb b.property.2 (by linarith)
  have hy1 : 1 ≤ Y := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hd d.property.2 (by linarith)
  let A := x + y - 1
  let B := x + Y - 1
  let C := X + y - 1
  let D := X + Y - 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hC : 0 < C := by dsimp [C]; linarith
  have hD : 0 < D := by dsimp [D]; linarith
  have hprod : A * D ≤ B * C := by
    dsimp [A, B, C, D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hA hD) hprod hq
  rw [Real.mul_rpow hB.le hC.le, Real.mul_rpow hA.le hD.le] at hpow
  simpa [claytonKernel, ha0, hb0, hc0, hd0, A, B, C, D, x, X, y, Y]
    using hpow


/-- The standard positive-Clayton density formula, set to zero on coordinate axes. Its identification as a density of the copula measure is a separate obligation. -/
noncomputable def claytonDensityFormula (θ : ℝ) (x : Fin 2 → I) : ℝ :=
  (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
    claytonKernel θ (-2 - 1 / θ) (x 0) (x 1)

/-- The explicit positive-Clayton density formula is MTP2 as a function. This alone does not prove `HasMTP2Density` for the copula. -/
theorem isMTP2_claytonDensityFormula_positive (θ : ℝ) (hθ : 0 < θ) :
    IsMTP2 (claytonDensityFormula θ) := by
  rw [isMTP2_fin_two_iff]
  have hf : IsTP2 (fun u v : I =>
      (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1)) := by
    intro a b c d _ _
    apply le_of_eq
    ring
  have hfn : ∀ u v : I, 0 ≤ (1 + θ) * (u : ℝ) ^ (-θ - 1) *
      (v : ℝ) ^ (-θ - 1) := by
    intro u v
    exact mul_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg u.property.1 _)) (Real.rpow_nonneg v.property.1 _)
  have hkn : ∀ u v : I, 0 ≤ claytonKernel θ (-2 - 1 / θ) u v := by
    intro u v
    unfold claytonKernel
    split_ifs with h
    · exact le_refl 0
    · have hu0 : u ≠ 0 := fun he => h (Or.inl he)
      have hv0 : v ≠ 0 := fun he => h (Or.inr he)
      have hu : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1
        (Ne.symm (fun he => hu0 (Subtype.ext he)))
      have hv : 0 < (v : ℝ) := lt_of_le_of_ne v.property.1
        (Ne.symm (fun he => hv0 (Subtype.ext he)))
      have hx : 1 ≤ (u : ℝ) ^ (-θ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu u.property.2 (by linarith)
      have hy : 1 ≤ (v : ℝ) ^ (-θ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv v.property.2 (by linarith)
      exact Real.rpow_nonneg (by linarith : 0 ≤ (u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) _
  have hq : -2 - 1 / θ ≤ 0 := by
    have hi : 0 < 1 / θ := one_div_pos.mpr hθ
    linarith
  have ht := hf.mul (claytonKernelTP2 θ (-2 - 1 / θ) hθ hq) hfn hkn
  simpa only [claytonDensityFormula, Matrix.cons_val_zero, Matrix.cons_val_one]
    using ht

/-- The explicit positive-Clayton density formula is nonnegative. -/
theorem claytonDensityFormula_nonneg (θ : ℝ) (hθ : 0 < θ) (x : Fin 2 → I) :
    0 ≤ claytonDensityFormula θ x := by
  unfold claytonDensityFormula claytonKernel
  by_cases h : x 0 = 0 ∨ x 1 = 0
  · simp [h]
  rw [ite_eq_right h]
  have h0 : x 0 ≠ 0 := fun he => h (Or.inl he)
  have h1 : x 1 ≠ 0 := fun he => h (Or.inr he)
  have hu : 0 < (x 0 : ℝ) := lt_of_le_of_ne (x 0).property.1
    (Ne.symm (fun he => h0 (Subtype.ext he)))
  have hv : 0 < (x 1 : ℝ) := lt_of_le_of_ne (x 1).property.1
    (Ne.symm (fun he => h1 (Subtype.ext he)))
  have hx : 1 ≤ (x 0 : ℝ) ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu (x 0).property.2 (by linarith)
  have hy : 1 ≤ (x 1 : ℝ) ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv (x 1).property.2 (by linarith)
  exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg (x 0).property.1 _))
    (Real.rpow_nonneg (x 1).property.1 _))
    (Real.rpow_nonneg (by linarith : 0 ≤ (x 0 : ℝ) ^ (-θ) +
      (x 1 : ℝ) ^ (-θ) - 1) _)

/-- The explicit positive-Clayton density formula is measurable. -/
theorem measurable_claytonDensityFormula (θ : ℝ) :
    Measurable (claytonDensityFormula θ) := by
  unfold claytonDensityFormula claytonKernel
  have hs : MeasurableSet {x : Fin 2 → I | x 0 = 0 ∨ x 1 = 0} := by
    exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).union
      (measurableSet_eq_fun (measurable_pi_apply 1) measurable_const)
  apply Measurable.mul
  · fun_prop
  · exact Measurable.ite hs measurable_const (by fun_prop)

end ProbabilityTheory.Copula
