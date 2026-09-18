/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Total positivity of functions, copula CDFs and densities

`IsTP2CDF` concerns the CDF. `HasMTP2Density` requires a nonnegative Lebesgue
density version satisfying the lattice inequality. They are distinct notions.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory

/-- Total positivity of order two of a bivariate function. -/
def IsTP2 {α β : Type*} [Preorder α] [Preorder β] (f : α → β → ℝ) : Prop :=
  ∀ a b c d, a ≤ b → c ≤ d → f a d * f b c ≤ f a c * f b d

/-- Multivariate total positivity of order two, also called log-supermodularity.
Nonnegativity is supplied separately when using this for a density. -/
def IsMTP2 {α : Type*} [Lattice α] (f : α → ℝ) : Prop :=
  ∀ x y, f x * f y ≤ f (x ⊓ y) * f (x ⊔ y)

theorem IsTP2.swap {α β : Type*} [Preorder α] [Preorder β] {f : α → β → ℝ}
    (h : IsTP2 f) : IsTP2 (fun b a => f a b) := by
  intro a b c d hab hcd
  simpa [mul_comm] using h c d a b hcd hab

theorem IsTP2.mul {α β : Type*} [Preorder α] [Preorder β] {f g : α → β → ℝ}
    (hf : IsTP2 f) (hg : IsTP2 g) (hnf : ∀ a b, 0 ≤ f a b) (hng : ∀ a b, 0 ≤ g a b) :
    IsTP2 (fun a b => f a b * g a b) := by
  intro a b c d hab hcd
  nlinarith [mul_le_mul (hf a b c d hab hcd) (hg a b c d hab hcd)
    (mul_nonneg (hng a d) (hng b c)) (mul_nonneg (hnf a c) (hnf b d))]

theorem IsMTP2.mul {α : Type*} [Lattice α] {f g : α → ℝ}
    (hf : IsMTP2 f) (hg : IsMTP2 g) (hnf : ∀ x, 0 ≤ f x) (hng : ∀ x, 0 ≤ g x) :
    IsMTP2 (fun x => f x * g x) := by
  intro x y
  nlinarith [mul_le_mul (hf x y) (hg x y) (mul_nonneg (hng x) (hng y))
    (mul_nonneg (hnf (x ⊓ y)) (hnf (x ⊔ y)))]

/-- Composing with a lattice homomorphism preserves MTP2. -/
theorem IsMTP2.comp {α β : Type*} [Lattice α] [Lattice β] {f : β → ℝ}
    (hf : IsMTP2 f) (g : LatticeHom α β) : IsMTP2 (f ∘ g) := by
  intro x y
  simpa only [Function.comp_apply, map_inf, map_sup] using hf (g x) (g y)

theorem isMTP2_const {α : Type*} [Lattice α] (c : ℝ) : IsMTP2 (fun _ : α => c) :=
  fun _ _ => le_rfl

/-- Products of one-coordinate factors are MTP2, with equality in the lattice inequality. -/
theorem isMTP2_prod {ι α : Type*} [Fintype ι] [LinearOrder α] (f : ι → α → ℝ) :
    IsMTP2 (fun x : ι → α => ∏ i, f i (x i)) := by
  intro x y
  apply le_of_eq
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases le_total (x i) (y i) with h | h
  · simp [Pi.inf_apply, Pi.sup_apply, inf_eq_left.mpr h, sup_eq_right.mpr h]
  · simp [Pi.inf_apply, Pi.sup_apply, inf_eq_right.mpr h, sup_eq_left.mpr h, mul_comm]

namespace Copula

/-- The lattice and ordered-rectangle formulations agree in dimension two. -/
theorem isMTP2_fin_two_iff {α : Type*} [LinearOrder α] (f : (Fin 2 → α) → ℝ) :
    IsMTP2 f ↔ IsTP2 (fun u v => f ![u, v]) := by
  have hi (a b c d : α) (hab : a ≤ b) (hcd : c ≤ d) :
      (![a, d] ⊓ ![b, c]) = ![a, c] := by
    ext i; fin_cases i <;> simp [inf_eq_left.mpr hab, inf_eq_right.mpr hcd]
  have hs (a b c d : α) (hab : a ≤ b) (hcd : c ≤ d) :
      (![a, d] ⊔ ![b, c]) = ![b, d] := by
    ext i; fin_cases i <;> simp [sup_eq_right.mpr hab, sup_eq_left.mpr hcd]
  constructor
  · intro h a b c d hab hcd
    simpa only [hi a b c d hab hcd, hs a b c d hab hcd] using h ![a, d] ![b, c]
  · intro h x y
    have he (z : Fin 2 → α) : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
    rcases le_total (x 0) (y 0) with h0 | h0 <;>
      rcases le_total (x 1) (y 1) with h1 | h1
    · have hxy : x ≤ y := by intro i; fin_cases i; exact h0; exact h1
      simp [inf_eq_left.mpr hxy, sup_eq_right.mpr hxy]
    · rw [← he x, ← he y, hi (x 0) (y 0) (y 1) (x 1) h0 h1,
        hs (x 0) (y 0) (y 1) (x 1) h0 h1]
      exact h (x 0) (y 0) (y 1) (x 1) h0 h1
    · rw [mul_comm, inf_comm, sup_comm, ← he y, ← he x,
        hi (y 0) (x 0) (x 1) (y 1) h0 h1, hs (y 0) (x 0) (x 1) (y 1) h0 h1]
      exact h (y 0) (x 0) (x 1) (y 1) h0 h1
    · have hyx : y ≤ x := by intro i; fin_cases i; exact h0; exact h1
      simp [inf_eq_right.mpr hyx, sup_eq_left.mpr hyx, mul_comm]

/-- TP2 of the copula's distribution function. -/
def IsTP2CDF (C : Copula 2) : Prop := IsTP2 (fun u v : I => C.cdf ![u, v])

/-- A copula has an MTP2 density if some nonnegative measurable density version
with respect to uniform cube volume satisfies the lattice inequality. -/
def HasMTP2Density {d : ℕ} (C : Copula d) : Prop :=
  ∃ f : (Fin d → I) → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ IsMTP2 f ∧
    C.toMeasure = (volume : Measure (Fin d → I)).withDensity (fun x => ENNReal.ofReal (f x))

theorem IsTP2CDF.isLTD {C : Copula 2} (h : C.IsTP2CDF) : C.IsLTD := by
  intro a b v hab
  simpa [mul_comm] using h a b v 1 hab v.property.2

theorem IsTP2CDF.isPQD {C : Copula 2} (h : C.IsTP2CDF) : C.IsPQD := h.isLTD.isPQD

theorem isTP2CDF_independence : (independence 2).IsTP2CDF := by
  intro a b c d _ _
  simp only [cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

theorem hasMTP2Density_independence (d : ℕ) : (independence d).HasMTP2Density := by
  refine ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, isMTP2_const 1, ?_⟩
  simp
  rfl

end Copula
end ProbabilityTheory
