/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Bivariate

/-! # Product perturbations of independence

For Lipschitz functions `φ ψ : I → ℝ` vanishing at both endpoints, with Lipschitz constants
`Lφ` and `Lψ` satisfying `Lφ * Lψ ≤ 1`, the function

`C(u,v) = uv + φ(u) ψ(v)`

is a copula: its rectangle increments are `(b-a)(e-c) + (φ b - φ a)(ψ e - ψ c)`, which are
bounded below by `(1 - Lφ Lψ)(b-a)(e-c) ≥ 0`. This covers the tent copulas `Π ± ℓ ⊗ τ`,
the Blomqvist copulas `Π + b ℓ ⊗ ℓ`, and the sine copulas `Π + (a/π) sin(π ·) ⊗ ℓ`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A real function on the unit interval that vanishes at both endpoints and is Lipschitz with
constant `lip`. -/
structure BoundaryProfile where
  /-- The profile function. -/
  toFun : I → ℝ
  /-- Its Lipschitz constant. -/
  lip : ℝ
  lip_nonneg : 0 ≤ lip
  zero : toFun 0 = 0
  one : toFun 1 = 0
  lipschitz : ∀ s t : I, |toFun s - toFun t| ≤ lip * |(s : ℝ) - t|

namespace BoundaryProfile

instance : CoeFun BoundaryProfile (fun _ => I → ℝ) := ⟨BoundaryProfile.toFun⟩

theorem abs_le (φ : BoundaryProfile) (t : I) :
    |φ t| ≤ φ.lip * min (t : ℝ) (1 - t) := by
  have h0 := φ.lipschitz t 0
  have h1 := φ.lipschitz t 1
  rw [φ.zero, sub_zero] at h0
  rw [φ.one, sub_zero] at h1
  have e0 : |(t : ℝ) - ((0 : I) : ℝ)| = t := by
    simp only [Set.Icc.coe_zero, sub_zero]
    exact abs_of_nonneg t.property.1
  have e1 : |(t : ℝ) - ((1 : I) : ℝ)| = 1 - t := by
    simp only [Set.Icc.coe_one]
    rw [abs_sub_comm]
    exact abs_of_nonneg (by linarith [t.property.2])
  rw [e0] at h0
  rw [e1] at h1
  change |φ.toFun t| ≤ _
  rcases le_total (t : ℝ) (1 - t) with h | h
  · rw [min_eq_left h]; exact h0
  · rw [min_eq_right h]; exact h1

/-- The scaled profile `c • φ`. -/
noncomputable def smul (c : ℝ) (φ : BoundaryProfile) : BoundaryProfile where
  toFun t := c * φ t
  lip := |c| * φ.lip
  lip_nonneg := mul_nonneg (abs_nonneg c) φ.lip_nonneg
  zero := by simp [φ.zero]
  one := by simp [φ.one]
  lipschitz s t := by
    rw [← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (φ.lipschitz s t) (abs_nonneg c)

@[simp] theorem smul_apply (c : ℝ) (φ : BoundaryProfile) (t : I) : (φ.smul c) t = c * φ t := rfl

end BoundaryProfile

/-- The bivariate function `uv + φ(u) ψ(v)`. -/
noncomputable def productPerturbationCDF (φ ψ : BoundaryProfile) (u v : I) : ℝ :=
  (u : ℝ) * v + φ u * ψ v

theorem productPerturbation_isClassical (φ ψ : BoundaryProfile) (h : φ.lip * ψ.lip ≤ 1) :
    IsClassical (fun u : Fin 2 → I => productPerturbationCDF φ ψ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (productPerturbationCDF φ ψ)
  · intro v; simp [productPerturbationCDF, show φ 0 = 0 from φ.zero]
  · intro u; simp [productPerturbationCDF, show ψ 0 = 0 from ψ.zero]
  · intro v; simp [productPerturbationCDF, show φ 1 = 0 from φ.one]
  · intro u; simp [productPerturbationCDF, show ψ 1 = 0 from ψ.one]
  · intro a b c e hab hce
    have hab' : (a : ℝ) ≤ b := hab
    have hce' : (c : ℝ) ≤ e := hce
    have hφ := φ.lipschitz b a
    have hψ := ψ.lipschitz e c
    rw [abs_of_nonneg (sub_nonneg.mpr hab')] at hφ
    rw [abs_of_nonneg (sub_nonneg.mpr hce')] at hψ
    have hprod : |(φ b - φ a) * (ψ e - ψ c)| ≤ (φ.lip * ((b : ℝ) - a)) * (ψ.lip * ((e : ℝ) - c)) := by
      rw [abs_mul]
      exact mul_le_mul hφ hψ (abs_nonneg _) (mul_nonneg φ.lip_nonneg (sub_nonneg.mpr hab'))
    have hrect : productPerturbationCDF φ ψ b e - productPerturbationCDF φ ψ a e -
        productPerturbationCDF φ ψ b c + productPerturbationCDF φ ψ a c =
        ((b : ℝ) - a) * ((e : ℝ) - c) + (φ b - φ a) * (ψ e - ψ c) := by
      unfold productPerturbationCDF; ring
    rw [hrect]
    have hbase : 0 ≤ ((b : ℝ) - a) * ((e : ℝ) - c) :=
      mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hce')
    have hL : (φ.lip * ((b : ℝ) - a)) * (ψ.lip * ((e : ℝ) - c)) ≤ ((b : ℝ) - a) * ((e : ℝ) - c) := by
      have : (φ.lip * ((b : ℝ) - a)) * (ψ.lip * ((e : ℝ) - c)) =
          (φ.lip * ψ.lip) * (((b : ℝ) - a) * ((e : ℝ) - c)) := by ring
      rw [this]
      exact mul_le_of_le_one_left hbase h
    linarith [neg_abs_le ((φ b - φ a) * (ψ e - ψ c))]

/-- The copula `Π + φ ⊗ ψ` for boundary profiles with `Lip φ * Lip ψ ≤ 1`. -/
noncomputable def productPerturbation (φ ψ : BoundaryProfile) (h : φ.lip * ψ.lip ≤ 1) :
    Copula 2 :=
  ofClassical _ (productPerturbation_isClassical φ ψ h)

@[simp] theorem cdf_productPerturbation (φ ψ : BoundaryProfile) (h : φ.lip * ψ.lip ≤ 1)
    (u v : I) : (productPerturbation φ ψ h).cdf ![u, v] = (u : ℝ) * v + φ u * ψ v := by
  simp [productPerturbation, productPerturbationCDF]

end ProbabilityTheory.Copula
