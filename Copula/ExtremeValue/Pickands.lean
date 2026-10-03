/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Diagonal
import Copula.Classical.Bivariate
import Mathlib.Analysis.Convex.Slope

/-! # Pickands dependence functions and bivariate extreme-value copulas

A *Pickands dependence function* is a convex function `A : [0,1] → ℝ` with
`max(t, 1 - t) ≤ A(t) ≤ 1`. The associated *stable tail dependence function* is
`ℓ_A(x,y) = (x + y) A(y / (x + y))` on `[0,∞)²`, and the Pickands copula is

`C_A(u,v) = exp(log(uv) A(log v / log(uv))) = exp(-ℓ_A(-log u, -log v))`

for `u, v ∈ (0,1]`, extended by zero on the two lower edges.

Main results:
* `pickandsCopula A hA`: `C_A` is a copula (`IsPickandsFunction A` suffices). The proof of
  2-increasingness is the standard one: `ℓ_A` is positively homogeneous, nondecreasing in each
  variable and submodular (from the chord-slope monotonicity of the convex perspective
  `r ↦ ℓ_A(1,r)`), and `exp ∘ (-ℓ_A)` is then supermodular because `exp` is convex and increasing.
* `cdf_pickandsCopula_eq_exp`: the classical formula `exp(log(uv) A(log v / log(uv)))`.
* `isExtremeValue_pickandsCopula`: `C_A` is max-stable.
* `pickandsCopula_const_one`: `A ≡ 1` gives `Π`; `pickandsCopula_max`: `A = max(t,1-t)` gives `M`.
* `pickandsCopula_eq_iff`: `A ↦ C_A` is injective on `[0,1]`;
  `pickandsCopula_lowerOrthantLE_iff`: `A ≤ B` on `[0,1]` iff `C_B ≤ C_A` pointwise.
* `isPQD_pickandsCopula`: every Pickands copula is positively quadrant dependent.
* `hasPowerDiagonal_pickandsCopula`: the diagonal is `t^{2A(1/2)}`, so the extremal coefficient
  is `2A(1/2)`; `pickandsCopula_eq_comonotonic_iff`: `C_A = M` iff `A(1/2) = 1/2`.

The converse (every bivariate extreme-value copula is a Pickands copula) is in
`Copula.ExtremeValue.PickandsConverse`.

References: J. Pickands, *Multivariate extreme value distributions* (1981); G. Gudendorf and
J. Segers, *Extreme-value copulas*, in *Copula Theory and Its Applications* (2010);
H. Joe, *Dependence Modeling with Copulas* (2014); F. Durante and C. Sempi, *Principles of
Copula Theory* (2016).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A Pickands dependence function: convex on `[0,1]` with `max(t, 1 - t) ≤ A(t) ≤ 1` there.
Values outside `[0,1]` are irrelevant. -/
structure IsPickandsFunction (A : ℝ → ℝ) : Prop where
  convexOn : ConvexOn ℝ (Icc 0 1) A
  le_one : ∀ t ∈ Icc (0 : ℝ) 1, A t ≤ 1
  max_le : ∀ t ∈ Icc (0 : ℝ) 1, max t (1 - t) ≤ A t

/-- The stable tail dependence function `ℓ_A(x,y) = (x + y) A(y / (x + y))` of a Pickands
function (with `ℓ_A(0,0) = 0`). -/
noncomputable def pickandsTail (A : ℝ → ℝ) (x y : ℝ) : ℝ := (x + y) * A (y / (x + y))

theorem pickands_ratio_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y / (x + y) ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg hy (add_nonneg hx hy),
    div_le_one_of_le₀ (le_add_of_nonneg_left hx) (add_nonneg hx hy)⟩

namespace IsPickandsFunction

variable {A : ℝ → ℝ}

theorem apply_zero (hA : IsPickandsFunction A) : A 0 = 1 := by
  have h1 := hA.le_one 0 ⟨le_rfl, zero_le_one⟩
  have h2 := hA.max_le 0 ⟨le_rfl, zero_le_one⟩
  have : max (0 : ℝ) (1 - 0) = 1 := by norm_num
  linarith

theorem apply_one (hA : IsPickandsFunction A) : A 1 = 1 := by
  have h1 := hA.le_one 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hA.max_le 1 ⟨zero_le_one, le_rfl⟩
  have : max (1 : ℝ) (1 - 1) = 1 := by norm_num
  linarith

theorem half_le (hA : IsPickandsFunction A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 / 2 ≤ A t := by
  have h := hA.max_le t ht
  have h1 := le_max_left t (1 - t)
  have h2 := le_max_right t (1 - t)
  linarith

theorem pos (hA : IsPickandsFunction A) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < A t := by
  linarith [hA.half_le ht]

/-- The reflected function `t ↦ A(1 - t)` (the Pickands function of the transposed copula). -/
theorem comp_one_sub (hA : IsPickandsFunction A) : IsPickandsFunction (fun t => A (1 - t)) where
  convexOn := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : 1 - y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h := hA.convexOn.2 hx' hy' ha hb hab
    have he : a • (1 - x) + b • (1 - y) = 1 - (a • x + b • y) := by
      simp only [smul_eq_mul]
      linear_combination hab
    rw [he] at h
    exact h
  le_one t ht := hA.le_one (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  max_le t ht := by
    have h := hA.max_le (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [sub_sub_cancel, max_comm] at h
    exact h

/-- A Pickands function lies below the chord `max(t, 1-t)` iff it touches it at `1/2`. -/
theorem eq_max_iff (hA : IsPickandsFunction A) :
    A (1 / 2) = 1 / 2 ↔ EqOn A (fun t => max t (1 - t)) (Icc 0 1) := by
  constructor
  · intro h t ht
    apply le_antisymm _ (hA.max_le t ht)
    have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    rcases le_total t (1 / 2) with h2 | h2
    · have hc := hA.convexOn.2 (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hh
        (by linarith : (0 : ℝ) ≤ 1 - 2 * t) (by linarith [ht.1] : (0 : ℝ) ≤ 2 * t) (by ring)
      have he : (1 - 2 * t) • (0 : ℝ) + (2 * t) • (1 / 2 : ℝ) = t := by
        simp only [smul_eq_mul]; ring
      rw [he, hA.apply_zero, h, smul_eq_mul, smul_eq_mul] at hc
      exact hc.trans (by linarith [le_max_right t (1 - t)])
    · have hc := hA.convexOn.2 hh (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
        (by linarith [ht.2] : (0 : ℝ) ≤ 2 - 2 * t) (by linarith : (0 : ℝ) ≤ 2 * t - 1) (by ring)
      have he : (2 - 2 * t) • (1 / 2 : ℝ) + (2 * t - 1) • (1 : ℝ) = t := by
        simp only [smul_eq_mul]; ring
      rw [he, hA.apply_one, h, smul_eq_mul, smul_eq_mul] at hc
      exact hc.trans (by linarith [le_max_left t (1 - t)])
  · intro h
    rw [h ⟨by norm_num, by norm_num⟩]
    norm_num

end IsPickandsFunction

section Tail

variable {A : ℝ → ℝ}

theorem pickandsTail_smul (A : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) (x y : ℝ) :
    pickandsTail A (s * x) (s * y) = s * pickandsTail A x y := by
  unfold pickandsTail
  rw [← mul_add, mul_div_mul_left _ _ hs]
  ring

theorem pickandsTail_zero_left (hA : IsPickandsFunction A) (y : ℝ) : pickandsTail A 0 y = y := by
  unfold pickandsTail
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [zero_add, div_self hy, hA.apply_one, mul_one]

theorem pickandsTail_zero_right (hA : IsPickandsFunction A) (x : ℝ) : pickandsTail A x 0 = x := by
  unfold pickandsTail
  rw [add_zero, zero_div, hA.apply_zero, mul_one]

theorem pickandsTail_le_add (hA : IsPickandsFunction A) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pickandsTail A x y ≤ x + y := by
  unfold pickandsTail
  calc (x + y) * A (y / (x + y)) ≤ (x + y) * 1 :=
        mul_le_mul_of_nonneg_left (hA.le_one _ (pickands_ratio_mem hx hy)) (add_nonneg hx hy)
    _ = x + y := mul_one _

theorem max_le_pickandsTail (hA : IsPickandsFunction A) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max x y ≤ pickandsTail A x y := by
  unfold pickandsTail
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h | h
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  · have hm := hA.max_le _ (pickands_ratio_mem hx hy)
    have hne : x + y ≠ 0 := h.ne'
    have h1 : (x + y) * (y / (x + y)) = y := by field_simp
    have h2 : (x + y) * (1 - y / (x + y)) = x := by
      rw [mul_sub, h1]; ring
    apply max_le
    · calc x = (x + y) * (1 - y / (x + y)) := h2.symm
        _ ≤ (x + y) * A (y / (x + y)) :=
          mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hm) h.le
    · calc y = (x + y) * (y / (x + y)) := h1.symm
        _ ≤ (x + y) * A (y / (x + y)) :=
          mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hm) h.le

theorem pickandsTail_nonneg (hA : IsPickandsFunction A) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ pickandsTail A x y :=
  hx.trans ((le_max_left x y).trans (max_le_pickandsTail hA hx hy))

theorem pickandsTail_swap (A : ℝ → ℝ) (x y : ℝ) :
    pickandsTail A x y = pickandsTail (fun t => A (1 - t)) y x := by
  unfold pickandsTail
  rcases eq_or_ne (x + y) 0 with h | h
  · have h' : y + x = 0 := by linarith
    rw [h, h', zero_mul, zero_mul]
  · rw [add_comm y x]
    show (x + y) * A (y / (x + y)) = (x + y) * A (1 - x / (x + y))
    congr 2
    rw [eq_sub_iff_add_eq, ← add_div, add_comm y x, div_self h]

/-- The perspective `r ↦ ℓ_A(1, r)` is convex on `[0, ∞)`. -/
theorem convexOn_pickandsTail_one (hA : IsPickandsFunction A) :
    ConvexOn ℝ (Ici 0) (fun r => pickandsTail A 1 r) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro r hr s hs a b ha hb hab
  rw [mem_Ici] at hr hs
  simp only [smul_eq_mul, pickandsTail]
  have hm0 : 0 ≤ a * r + b * s := add_nonneg (mul_nonneg ha hr) (mul_nonneg hb hs)
  have hD : 0 < 1 + (a * r + b * s) := by linarith
  have hr1 : 0 < 1 + r := by linarith
  have hs1 : 0 < 1 + s := by linarith
  have hμ : 0 ≤ a * (1 + r) / (1 + (a * r + b * s)) := div_nonneg (mul_nonneg ha hr1.le) hD.le
  have hν : 0 ≤ b * (1 + s) / (1 + (a * r + b * s)) := div_nonneg (mul_nonneg hb hs1.le) hD.le
  have hsum : a * (1 + r) / (1 + (a * r + b * s)) + b * (1 + s) / (1 + (a * r + b * s)) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hD.ne']
    linear_combination hab
  have key := hA.convexOn.2 (pickands_ratio_mem zero_le_one hr)
    (pickands_ratio_mem zero_le_one hs) hμ hν hsum
  have harg : (a * (1 + r) / (1 + (a * r + b * s))) • (r / (1 + r)) +
      (b * (1 + s) / (1 + (a * r + b * s))) • (s / (1 + s)) =
      (a * r + b * s) / (1 + (a * r + b * s)) := by
    simp only [smul_eq_mul]
    field_simp
  rw [harg, smul_eq_mul, smul_eq_mul] at key
  calc (1 + (a * r + b * s)) * A ((a * r + b * s) / (1 + (a * r + b * s)))
      ≤ (1 + (a * r + b * s)) * (a * (1 + r) / (1 + (a * r + b * s)) * A (r / (1 + r)) +
          b * (1 + s) / (1 + (a * r + b * s)) * A (s / (1 + s))) :=
        mul_le_mul_of_nonneg_left key hD.le
    _ = a * ((1 + r) * A (r / (1 + r))) + b * ((1 + s) * A (s / (1 + s))) := by
        field_simp

theorem pickandsTail_one_mono (hA : IsPickandsFunction A) {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') :
    pickandsTail A 1 r ≤ pickandsTail A 1 r' := by
  have h0 : pickandsTail A 1 0 ≤ pickandsTail A 1 r' := by
    rw [pickandsTail_zero_right hA]
    exact (le_max_left _ _).trans (max_le_pickandsTail hA zero_le_one (hr.trans hrr))
  rcases eq_or_lt_of_le (hr.trans hrr) with h | h
  · have : r = r' := by linarith
    rw [this]
  · have hb : 0 ≤ 1 - r / r' := sub_nonneg.2 (div_le_one_of_le₀ hrr h.le)
    have hc := (convexOn_pickandsTail_one hA).2 (mem_Ici.2 h.le)
      (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0) (div_nonneg hr h.le) hb (add_sub_cancel _ _)
    simp only [smul_eq_mul, mul_zero, add_zero] at hc
    rw [div_mul_cancel₀ r h.ne'] at hc
    calc pickandsTail A 1 r ≤ r / r' * pickandsTail A 1 r' + (1 - r / r') * pickandsTail A 1 0 := hc
      _ ≤ r / r' * pickandsTail A 1 r' + (1 - r / r') * pickandsTail A 1 r' :=
        by linarith [mul_le_mul_of_nonneg_left h0 hb]
      _ = pickandsTail A 1 r' := by ring

private theorem pickandsTail_eq_mul_one (A : ℝ → ℝ) {x : ℝ} (hx : 0 < x) (z : ℝ) :
    pickandsTail A x z = x * pickandsTail A 1 (z / x) := by
  rw [← pickandsTail_smul A hx.ne', mul_one, mul_div_cancel₀ z hx.ne']

/-- `ℓ_A` is nondecreasing in its second variable. -/
theorem pickandsTail_mono_right (hA : IsPickandsFunction A) {x y y' : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hyy : y ≤ y') : pickandsTail A x y ≤ pickandsTail A x y' := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · rw [pickandsTail_zero_left hA, pickandsTail_zero_left hA]
    exact hyy
  · rw [pickandsTail_eq_mul_one A hx, pickandsTail_eq_mul_one A hx]
    exact mul_le_mul_of_nonneg_left (pickandsTail_one_mono hA (div_nonneg hy hx.le)
      (div_le_div_of_nonneg_right hyy hx.le)) hx.le

/-- `ℓ_A` is nondecreasing in its first variable. -/
theorem pickandsTail_mono_left (hA : IsPickandsFunction A) {x x' y : ℝ} (hx : 0 ≤ x)
    (hxx : x ≤ x') (hy : 0 ≤ y) : pickandsTail A x y ≤ pickandsTail A x' y := by
  rw [pickandsTail_swap A x y, pickandsTail_swap A x' y]
  exact pickandsTail_mono_right hA.comp_one_sub hy hx hxx

private theorem submodular_aux (hA : IsPickandsFunction A) {x x' y y' : ℝ} (hx : 0 < x)
    (hxx : x ≤ x') (hy : 0 ≤ y) (hyy : y ≤ y') :
    pickandsTail A x y + pickandsTail A x' y' ≤ pickandsTail A x y' + pickandsTail A x' y := by
  rcases eq_or_lt_of_le hyy with rfl | hyy
  · linarith
  have hx' : 0 < x' := hx.trans_le hxx
  rw [pickandsTail_eq_mul_one A hx, pickandsTail_eq_mul_one A hx',
    pickandsTail_eq_mul_one A hx, pickandsTail_eq_mul_one A hx']
  have hconv := convexOn_pickandsTail_one hA
  have h13 : y / x' < y' / x' := div_lt_div_of_pos_right hyy hx'
  have h34 : y' / x' ≤ y' / x := div_le_div_of_nonneg_left (hy.trans hyy.le) hx hxx
  have h24 : y / x < y' / x := div_lt_div_of_pos_right hyy hx
  have h12 : y / x' ≤ y / x := div_le_div_of_nonneg_left hy hx hxx
  have m1 : y / x' ∈ Ici (0 : ℝ) := div_nonneg hy hx'.le
  have m2 : y / x ∈ Ici (0 : ℝ) := div_nonneg hy hx.le
  have m3 : y' / x' ∈ Ici (0 : ℝ) := div_nonneg (hy.trans hyy.le) hx'.le
  have m4 : y' / x ∈ Ici (0 : ℝ) := div_nonneg (hy.trans hyy.le) hx.le
  have s1 := hconv.secant_mono m1 m3 m4 h13.ne' (by linarith) h34
  have s2 := hconv.secant_mono m4 m1 m2 (by linarith) h24.ne h12
  set ψ := fun r => pickandsTail A 1 r with hψ
  rw [← neg_sub (ψ (y' / x)), ← neg_sub (y' / x), neg_div_neg_eq,
    ← neg_sub (ψ (y' / x)) (ψ (y / x)), ← neg_sub (y' / x) (y / x), neg_div_neg_eq] at s2
  have key := s1.trans s2
  have d31 : y' / x' - y / x' = (y' - y) / x' := by ring
  have d42 : y' / x - y / x = (y' - y) / x := by ring
  rw [d31, d42, div_div_eq_mul_div, div_div_eq_mul_div] at key
  have := (div_le_div_iff_of_pos_right (sub_pos.2 hyy)).1 key
  show x * ψ (y / x) + x' * ψ (y' / x') ≤ x * ψ (y' / x) + x' * ψ (y / x')
  linarith

/-- `ℓ_A` is submodular on `[0,∞)²`: for `x ≤ x'`, `y ≤ y'`,
`ℓ(x,y) + ℓ(x',y') ≤ ℓ(x,y') + ℓ(x',y)`. -/
theorem pickandsTail_submodular (hA : IsPickandsFunction A) {x x' y y' : ℝ} (hx : 0 ≤ x)
    (hxx : x ≤ x') (hy : 0 ≤ y) (hyy : y ≤ y') :
    pickandsTail A x y + pickandsTail A x' y' ≤ pickandsTail A x y' + pickandsTail A x' y := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · rcases eq_or_lt_of_le hy with rfl | hy
    · rw [pickandsTail_zero_left hA, pickandsTail_zero_left hA, pickandsTail_zero_right hA]
      linarith [pickandsTail_le_add hA (le_refl 0 |>.trans hxx) (le_refl 0 |>.trans hyy)]
    · have h := submodular_aux hA.comp_one_sub hy hyy (le_refl 0) hxx
      rw [← pickandsTail_swap, ← pickandsTail_swap, ← pickandsTail_swap,
        ← pickandsTail_swap] at h
      linarith
  · exact submodular_aux hA hx hxx hy hyy

theorem pickandsTail_le_of_le {B : ℝ → ℝ} (h : ∀ t ∈ Icc (0 : ℝ) 1, A t ≤ B t) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : pickandsTail A x y ≤ pickandsTail B x y :=
  mul_le_mul_of_nonneg_left (h _ (pickands_ratio_mem hx hy)) (add_nonneg hx hy)

end Tail

/-- The convex increasing function `exp(-·)` turns submodularity of an increasing function into
nonnegativity of the rectangle increment. -/
private theorem exp_neg_rect {p q r s : ℝ} (hpr : p ≤ r) (hps : p ≤ s) (hq : q ≤ r + s - p) :
    Real.exp (-r) + Real.exp (-s) ≤ Real.exp (-p) + Real.exp (-q) := by
  have hE := Real.exp_pos (-p)
  have hR : Real.exp (-r) ≤ Real.exp (-p) := Real.exp_le_exp.2 (by linarith)
  have hS : Real.exp (-s) ≤ Real.exp (-p) := Real.exp_le_exp.2 (by linarith)
  have hT : Real.exp (-(r + s - p)) ≤ Real.exp (-q) := Real.exp_le_exp.2 (by linarith)
  have hprod : Real.exp (-(r + s - p)) * Real.exp (-p) = Real.exp (-r) * Real.exp (-s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hfac : Real.exp (-p) * (Real.exp (-p) + Real.exp (-(r + s - p)) - Real.exp (-r) -
      Real.exp (-s)) = (Real.exp (-p) - Real.exp (-r)) * (Real.exp (-p) - Real.exp (-s)) := by
    linear_combination hprod
  have h1 : Real.exp (-p) * 0 ≤ Real.exp (-p) * (Real.exp (-p) + Real.exp (-(r + s - p)) -
      Real.exp (-r) - Real.exp (-s)) := by
    rw [mul_zero, hfac]
    exact mul_nonneg (sub_nonneg.2 hR) (sub_nonneg.2 hS)
  have h2 := le_of_mul_le_mul_left h1 hE
  linarith

private theorem coe_pos_of_ne {u : I} (hu : u ≠ 0) : (0 : ℝ) < u :=
  lt_of_le_of_ne u.2.1 (fun h => hu (Subtype.ext h.symm))

private theorem ne_zero_of_coe_pos {u : I} (h : (0 : ℝ) < u) : u ≠ 0 := by
  rintro rfl
  simp at h

private theorem neg_log_nonneg (u : I) : 0 ≤ -Real.log u :=
  neg_nonneg.2 (Real.log_nonpos u.2.1 u.2.2)

/-- The Pickands CDF formula `exp(-ℓ_A(-log u, -log v))`, zero on the lower edges. -/
noncomputable def pickandsCDF (A : ℝ → ℝ) (u v : I) : ℝ :=
  if u = 0 ∨ v = 0 then 0 else Real.exp (-pickandsTail A (-Real.log u) (-Real.log v))

section CDF

variable {A : ℝ → ℝ}

theorem pickandsCDF_nonneg (A : ℝ → ℝ) (u v : I) : 0 ≤ pickandsCDF A u v := by
  unfold pickandsCDF
  split_ifs <;> positivity

theorem pickandsCDF_zero_left (A : ℝ → ℝ) (v : I) : pickandsCDF A 0 v = 0 := by
  simp [pickandsCDF]

theorem pickandsCDF_zero_right (A : ℝ → ℝ) (u : I) : pickandsCDF A u 0 = 0 := by
  simp [pickandsCDF]

theorem pickandsCDF_one_left (hA : IsPickandsFunction A) (v : I) : pickandsCDF A 1 v = v := by
  unfold pickandsCDF
  by_cases hv : v = 0
  · simp [hv]
  · rw [ite_eq_right (by simp [hv])]
    rw [Set.Icc.coe_one, Real.log_one, neg_zero, pickandsTail_zero_left hA, neg_neg,
      Real.exp_log (coe_pos_of_ne hv)]

theorem pickandsCDF_one_right (hA : IsPickandsFunction A) (u : I) : pickandsCDF A u 1 = u := by
  unfold pickandsCDF
  by_cases hu : u = 0
  · simp [hu]
  · rw [ite_eq_right (by simp [hu])]
    rw [Set.Icc.coe_one, Real.log_one, neg_zero, pickandsTail_zero_right hA, neg_neg,
      Real.exp_log (coe_pos_of_ne hu)]

theorem pickandsCDF_mono (hA : IsPickandsFunction A) {u u' v v' : I} (hu : u ≤ u')
    (hv : v ≤ v') : pickandsCDF A u v ≤ pickandsCDF A u' v' := by
  by_cases h : u = 0 ∨ v = 0
  · rw [pickandsCDF, ite_eq_left h]
    exact pickandsCDF_nonneg A u' v'
  · push Not at h
    have hu0 := coe_pos_of_ne h.1
    have hv0 := coe_pos_of_ne h.2
    have hu' : u' ≠ 0 := ne_zero_of_coe_pos (hu0.trans_le hu)
    have hv' : v' ≠ 0 := ne_zero_of_coe_pos (hv0.trans_le hv)
    rw [pickandsCDF, ite_eq_right (not_or.2 ⟨h.1, h.2⟩), pickandsCDF,
      ite_eq_right (not_or.2 ⟨hu', hv'⟩)]
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hlu : -Real.log u' ≤ -Real.log u := neg_le_neg (Real.log_le_log hu0 hu)
    have hlv : -Real.log v' ≤ -Real.log v := neg_le_neg (Real.log_le_log hv0 hv)
    exact (pickandsTail_mono_left hA (neg_log_nonneg u') hlu (neg_log_nonneg v')).trans
      (pickandsTail_mono_right hA (neg_log_nonneg u) (neg_log_nonneg v') hlv)

theorem pickandsCDF_rect (hA : IsPickandsFunction A) {a b c e : I} (hab : a ≤ b) (hce : c ≤ e) :
    0 ≤ pickandsCDF A b e - pickandsCDF A a e - pickandsCDF A b c + pickandsCDF A a c := by
  by_cases ha : a = 0
  · rw [ha, pickandsCDF_zero_left, pickandsCDF_zero_left]
    linarith [pickandsCDF_mono hA (le_refl b) hce]
  by_cases hc : c = 0
  · rw [hc, pickandsCDF_zero_right, pickandsCDF_zero_right]
    linarith [pickandsCDF_mono hA hab (le_refl e)]
  have ha0 := coe_pos_of_ne ha
  have hc0 := coe_pos_of_ne hc
  have hb := ne_zero_of_coe_pos (ha0.trans_le hab)
  have he := ne_zero_of_coe_pos (hc0.trans_le hce)
  unfold pickandsCDF
  rw [ite_eq_right (not_or.2 ⟨hb, he⟩), ite_eq_right (not_or.2 ⟨ha, he⟩),
    ite_eq_right (not_or.2 ⟨hb, hc⟩),
    ite_eq_right (not_or.2 ⟨ha, hc⟩)]
  have hx := neg_log_nonneg b
  have hy := neg_log_nonneg e
  have hxx : -Real.log b ≤ -Real.log a := neg_le_neg (Real.log_le_log ha0 hab)
  have hyy : -Real.log e ≤ -Real.log c := neg_le_neg (Real.log_le_log hc0 hce)
  have hsub := pickandsTail_submodular hA hx hxx hy hyy
  have h1 := pickandsTail_mono_left hA hx hxx hy
  have h2 := pickandsTail_mono_right hA hx hy hyy
  have := exp_neg_rect h1 h2 (q := pickandsTail A (-Real.log a) (-Real.log c)) (by linarith)
  linarith

end CDF

/-- The bivariate extreme-value copula `C_A` of a Pickands dependence function `A`. -/
noncomputable def pickandsCopula (A : ℝ → ℝ) (hA : IsPickandsFunction A) : Copula 2 :=
  ofClassical _ (IsClassical.ofBivariate (pickandsCDF A) (pickandsCDF_zero_left A)
    (pickandsCDF_zero_right A) (pickandsCDF_one_left hA) (pickandsCDF_one_right hA)
    (fun _ _ _ _ hab hce => pickandsCDF_rect hA hab hce))

section Copula

variable {A : ℝ → ℝ}

theorem cdf_pickandsCopula (hA : IsPickandsFunction A) (u : Fin 2 → I) :
    (pickandsCopula A hA).cdf u = pickandsCDF A (u 0) (u 1) := by
  rw [pickandsCopula, cdf_ofClassical]

theorem cdf_pickandsCopula_two (hA : IsPickandsFunction A) (u v : I) :
    (pickandsCopula A hA).cdf ![u, v] = pickandsCDF A u v := by
  rw [cdf_pickandsCopula]
  rfl

/-- The classical Pickands formula `C_A(u,v) = exp(log(uv) A(log v / log(uv)))` on `(0,1]²`. -/
theorem cdf_pickandsCopula_eq_exp (hA : IsPickandsFunction A) {u v : I} (hu : u ≠ 0)
    (hv : v ≠ 0) :
    (pickandsCopula A hA).cdf ![u, v] =
      Real.exp (Real.log ((u : ℝ) * v) * A (Real.log v / Real.log ((u : ℝ) * v))) := by
  rw [cdf_pickandsCopula_two, pickandsCDF, ite_eq_right (not_or.2 ⟨hu, hv⟩), pickandsTail,
    Real.log_mul (coe_pos_of_ne hu).ne' (coe_pos_of_ne hv).ne', ← neg_add, neg_div_neg_eq]
  congr 1
  ring

/-- Pickands copulas are extreme-value copulas (max-stable). -/
theorem isExtremeValue_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).IsExtremeValue := by
  intro u t ht
  rw [cdf_pickandsCopula, cdf_pickandsCopula]
  show pickandsCDF A (unitPower (u 0) t ht.le) (unitPower (u 1) t ht.le) =
    pickandsCDF A (u 0) (u 1) ^ t
  have hz (w : I) (hw : w = 0) : unitPower w t ht.le = 0 := by
    apply Subtype.ext
    simp [hw, Real.zero_rpow ht.ne']
  by_cases h : u 0 = 0 ∨ u 1 = 0
  · have h' : unitPower (u 0) t ht.le = 0 ∨ unitPower (u 1) t ht.le = 0 :=
      h.imp (hz _) (hz _)
    rw [pickandsCDF, ite_eq_left h', pickandsCDF, ite_eq_left h, Real.zero_rpow ht.ne']
  · push Not at h
    have h0 := coe_pos_of_ne h.1
    have h1 := coe_pos_of_ne h.2
    have hp0 : unitPower (u 0) t ht.le ≠ 0 :=
      ne_zero_of_coe_pos (by simpa using Real.rpow_pos_of_pos h0 t)
    have hp1 : unitPower (u 1) t ht.le ≠ 0 :=
      ne_zero_of_coe_pos (by simpa using Real.rpow_pos_of_pos h1 t)
    rw [pickandsCDF, ite_eq_right (not_or.2 ⟨hp0, hp1⟩), pickandsCDF,
      ite_eq_right (not_or.2 ⟨h.1, h.2⟩)]
    simp only [coe_unitPower, Real.log_rpow h0, Real.log_rpow h1]
    rw [show -(t * Real.log (u 0)) = t * -Real.log (u 0) by ring,
      show -(t * Real.log (u 1)) = t * -Real.log (u 1) by ring, pickandsTail_smul A ht.ne',
      ← Real.exp_mul]
    congr 1
    ring

/-- The point `exp(-max(s, 0))` of the unit interval. -/
noncomputable def expNegUnit (s : ℝ) : I :=
  ⟨Real.exp (-max s 0), (Real.exp_pos _).le,
    Real.exp_le_one_iff.2 (neg_nonpos.2 (le_max_right _ _))⟩

@[simp] theorem coe_expNegUnit (s : ℝ) : (expNegUnit s : ℝ) = Real.exp (-max s 0) := rfl

theorem expNegUnit_ne_zero (s : ℝ) : expNegUnit s ≠ 0 :=
  ne_zero_of_coe_pos (Real.exp_pos _)

theorem neg_log_expNegUnit (s : ℝ) : -Real.log (expNegUnit s) = max s 0 := by
  rw [coe_expNegUnit, Real.log_exp, neg_neg]

/-- Evaluation of `C_A` on the curve `(e^{-(1-t)}, e^{-t})` recovers `A`. -/
theorem cdf_pickandsCopula_expNegUnit (hA : IsPickandsFunction A) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (pickandsCopula A hA).cdf ![expNegUnit (1 - t), expNegUnit t] = Real.exp (-A t) := by
  rw [cdf_pickandsCopula_two, pickandsCDF,
    ite_eq_right (not_or.2 ⟨expNegUnit_ne_zero _, expNegUnit_ne_zero _⟩), neg_log_expNegUnit,
    neg_log_expNegUnit, max_eq_left (sub_nonneg.2 ht.2), max_eq_left ht.1, pickandsTail,
    sub_add_cancel, div_one, one_mul]

/-- The constant Pickands function `1`. -/
theorem isPickandsFunction_const_one : IsPickandsFunction (fun _ => 1) where
  convexOn := convexOn_const 1 (convex_Icc 0 1)
  le_one _ _ := le_rfl
  max_le t ht := max_le ht.2 (by linarith [ht.1])

/-- `A ≡ 1` gives the independence copula. -/
theorem pickandsCopula_const_one :
    pickandsCopula (fun _ => 1) isPickandsFunction_const_one = independence 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_pickandsCopula_two, cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold pickandsCDF
  split_ifs with h
  · rcases h with h | h <;> simp [h]
  · push Not at h
    rw [pickandsTail, mul_one, neg_add, neg_neg, neg_neg, Real.exp_add,
      Real.exp_log (coe_pos_of_ne h.1), Real.exp_log (coe_pos_of_ne h.2)]

/-- The lower boundary `max(t, 1 - t)` is a Pickands function. -/
theorem isPickandsFunction_max : IsPickandsFunction (fun t => max t (1 - t)) where
  convexOn := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    apply max_le
    · have h1 := mul_le_mul_of_nonneg_left (le_max_left x (1 - x)) ha
      have h2 := mul_le_mul_of_nonneg_left (le_max_left y (1 - y)) hb
      linarith
    · have h1 := mul_le_mul_of_nonneg_left (le_max_right x (1 - x)) ha
      have h2 := mul_le_mul_of_nonneg_left (le_max_right y (1 - y)) hb
      linarith
  le_one t ht := max_le ht.2 (by linarith [ht.1])
  max_le _ _ := le_rfl

theorem pickandsTail_max {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pickandsTail (fun t => max t (1 - t)) x y = max x y := by
  unfold pickandsTail
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h | h
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  · have hne : x + y ≠ 0 := h.ne'
    rw [mul_max_of_nonneg _ _ h.le, max_comm]
    congr 1
    · rw [mul_sub, mul_div_cancel₀ y hne]
      ring
    · exact mul_div_cancel₀ y hne

/-- `A = max(t, 1 - t)` gives the comonotonicity copula `M`. -/
theorem pickandsCopula_max :
    pickandsCopula (fun t => max t (1 - t)) isPickandsFunction_max = comonotonic 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_pickandsCopula_two, cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold pickandsCDF
  split_ifs with h
  · rcases h with h | h <;> simp [h, u.2.1, v.2.1]
  · push Not at h
    have hu := coe_pos_of_ne h.1
    have hv := coe_pos_of_ne h.2
    rw [pickandsTail_max (neg_log_nonneg u) (neg_log_nonneg v)]
    rcases le_total (u : ℝ) v with huv | huv
    · rw [max_eq_left (neg_le_neg (Real.log_le_log hu huv)), neg_neg, Real.exp_log hu,
        min_eq_left huv]
    · rw [max_eq_right (neg_le_neg (Real.log_le_log hv huv)), neg_neg, Real.exp_log hv,
        min_eq_right huv]

/-- Every Pickands copula is positively quadrant dependent (`A ≤ 1`). -/
theorem isPQD_pickandsCopula (hA : IsPickandsFunction A) : (pickandsCopula A hA).IsPQD := by
  intro u v
  rw [cdf_pickandsCopula_two, pickandsCDF]
  split_ifs with h
  · rcases h with h | h <;> simp [h]
  · push Not at h
    have h0 := coe_pos_of_ne h.1
    have h1 := coe_pos_of_ne h.2
    calc (u : ℝ) * v = Real.exp (-(-Real.log u + -Real.log v)) := by
          rw [neg_add, neg_neg, neg_neg, Real.exp_add, Real.exp_log h0, Real.exp_log h1]
      _ ≤ _ := Real.exp_le_exp.2
          (neg_le_neg (pickandsTail_le_add hA (neg_log_nonneg u) (neg_log_nonneg v)))

/-- Pointwise order of Pickands functions reverses the pointwise order of copulas. -/
theorem pickandsCopula_lowerOrthantLE {B : ℝ → ℝ} (hA : IsPickandsFunction A)
    (hB : IsPickandsFunction B) (h : ∀ t ∈ Icc (0 : ℝ) 1, A t ≤ B t) :
    (pickandsCopula B hB).LowerOrthantLE (pickandsCopula A hA) := by
  intro u
  rw [cdf_pickandsCopula, cdf_pickandsCopula]
  unfold pickandsCDF
  split_ifs
  · exact le_rfl
  · exact Real.exp_le_exp.2 (neg_le_neg
      (pickandsTail_le_of_le h (neg_log_nonneg _) (neg_log_nonneg _)))

/-- `A ≤ B` on `[0,1]` if and only if `C_B ≤ C_A` pointwise. -/
theorem pickandsCopula_lowerOrthantLE_iff {B : ℝ → ℝ} (hA : IsPickandsFunction A)
    (hB : IsPickandsFunction B) :
    (pickandsCopula B hB).LowerOrthantLE (pickandsCopula A hA) ↔
      ∀ t ∈ Icc (0 : ℝ) 1, A t ≤ B t := by
  refine ⟨fun h t ht => ?_, pickandsCopula_lowerOrthantLE hA hB⟩
  have h' := h ![expNegUnit (1 - t), expNegUnit t]
  rw [cdf_pickandsCopula_expNegUnit hA ht, cdf_pickandsCopula_expNegUnit hB ht] at h'
  linarith [Real.exp_le_exp.1 h']

/-- `A ↦ C_A` is injective: two Pickands copulas agree iff the functions agree on `[0,1]`. -/
theorem pickandsCopula_eq_iff {B : ℝ → ℝ} (hA : IsPickandsFunction A)
    (hB : IsPickandsFunction B) :
    pickandsCopula A hA = pickandsCopula B hB ↔ EqOn A B (Icc 0 1) := by
  constructor
  · intro h t ht
    have h1 := cdf_pickandsCopula_expNegUnit hA ht
    rw [h, cdf_pickandsCopula_expNegUnit hB ht] at h1
    linarith [Real.exp_injective h1]
  · intro h
    apply LowerOrthantLE.antisymm
    · exact pickandsCopula_lowerOrthantLE hB hA (fun t ht => (h ht).ge)
    · exact pickandsCopula_lowerOrthantLE hA hB (fun t ht => (h ht).le)

/-- The diagonal of `C_A` is `t ^ (2 A(1/2))`. -/
theorem hasPowerDiagonal_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).HasPowerDiagonal (2 * A (1 / 2)) := by
  intro t
  have hκ : 0 < 2 * A (1 / 2) := by
    linarith [hA.half_le (t := 1 / 2) ⟨by norm_num, by norm_num⟩]
  rw [diagonal, cdf_pickandsCopula_two, pickandsCDF]
  split_ifs with h
  · rcases h with h | h <;> rw [h, Set.Icc.coe_zero, Real.zero_rpow hκ.ne']
  · push Not at h
    have ht0 := coe_pos_of_ne h.1
    rw [Real.rpow_def_of_pos ht0, pickandsTail]
    rcases eq_or_ne (Real.log t) 0 with hl | hl
    · rw [hl]
      simp
    · have hhalf : -Real.log t / (-Real.log t + -Real.log t) = 1 / 2 := by
        rw [div_eq_iff (by intro h'; apply hl; linarith)]
        ring
      rw [hhalf]
      congr 1
      ring

/-- The extremal coefficient of `C_A` is `2 A(1/2)`. -/
theorem extremalCoefficient_pickandsCopula (hA : IsPickandsFunction A) :
    (pickandsCopula A hA).extremalCoefficient = 2 * A (1 / 2) :=
  (hasPowerDiagonal_pickandsCopula hA).extremalCoefficient_eq

/-- `C_A = M` iff `A(1/2) = 1/2` (iff `A = max(t, 1-t)` on `[0,1]`). -/
theorem pickandsCopula_eq_comonotonic_iff (hA : IsPickandsFunction A) :
    pickandsCopula A hA = comonotonic 2 ↔ A (1 / 2) = 1 / 2 := by
  constructor
  · intro h
    have h1 := (hasPowerDiagonal_one_iff _).2 h
    have := h1.unique (hasPowerDiagonal_pickandsCopula hA)
    linarith
  · intro h
    rw [← pickandsCopula_max]
    exact (pickandsCopula_eq_iff hA isPickandsFunction_max).2 (hA.eq_max_iff.1 h)

/-- `C_A = Π` iff `A ≡ 1` on `[0,1]`. -/
theorem pickandsCopula_eq_independence_iff (hA : IsPickandsFunction A) :
    pickandsCopula A hA = independence 2 ↔ EqOn A (fun _ => 1) (Icc 0 1) := by
  rw [← pickandsCopula_const_one]
  exact pickandsCopula_eq_iff hA isPickandsFunction_const_one

end Copula

end ProbabilityTheory.Copula
