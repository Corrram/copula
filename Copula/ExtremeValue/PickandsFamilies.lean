/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.PickandsConverse
import Copula.Families.Gumbel
import Copula.Families.MarshallOlkin

/-! # Pickands functions of the classical extreme-value families

The existing extreme-value constructors of the library are identified as Pickands copulas, with
their Pickands functions on `[0,1]`:

* independence: `A ≡ 1`; comonotonicity: `A(t) = max(t, 1 - t)`;
* Gumbel–Hougaard (logistic), `θ ≥ 1`: `A(t) = (t^θ + (1-t)^θ)^{1/θ}` (`gumbelPickands`);
* Marshall–Olkin with the library's convention
  `C(u,v) = min(u^α, v^β) u^{1-α} v^{1-β}`: `A(t) = max(1 - β t, 1 - α (1 - t))`
  (`marshallOlkinPickands`); Cuadras–Augé is the case `α = β`;
* Tawn's asymmetric logistic `C(u,v) = u^{1-α} v^{1-β} exp(-((α x)^θ + (β y)^θ)^{1/θ})`
  (`x = -log u`, `y = -log v`):
  `A(t) = (1-α)(1-t) + (1-β) t + ((α(1-t))^θ + (β t)^θ)^{1/θ}` (`tawnPickands`).

In each case the Pickands property (in particular convexity) is obtained from the general
converse theorem `IsExtremeValue.isPickandsFunction_pickandsOf`, since the families are known to
be max-stable copulas.

(With the opposite labelling of the coordinates, the Marshall–Olkin function reads
`max(1 - α t, 1 - β (1 - t))` as in Gudendorf–Segers (2010).)

References: G. Gudendorf and J. Segers, *Extreme-value copulas* (2010); H. Joe,
*Dependence Modeling with Copulas* (2014); J. A. Tawn, *Bivariate extreme value
theory: models and estimation* (1988).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Pickands functions may be changed off `[0,1]`. -/
theorem IsPickandsFunction.congr {A B : ℝ → ℝ} (hA : IsPickandsFunction A)
    (h : EqOn A B (Icc 0 1)) : IsPickandsFunction B where
  convexOn := hA.convexOn.congr h
  le_one t ht := by rw [← h ht]; exact hA.le_one t ht
  max_le t ht := by rw [← h ht]; exact hA.max_le t ht

/-- An extreme-value copula is the Pickands copula of any function agreeing with `A_C` on
`[0,1]`. -/
theorem IsExtremeValue.eq_pickandsCopula_of_eqOn {C : Copula 2} (hC : C.IsExtremeValue)
    {B : ℝ → ℝ} (hB : IsPickandsFunction B) (h : EqOn (pickandsOf C) B (Icc 0 1)) :
    C = pickandsCopula B hB := by
  conv_lhs => rw [hC.eq_pickandsCopula]
  exact (pickandsCopula_eq_iff _ hB).2 h

private theorem neg_log_expNegUnit_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    -Real.log (expNegUnit s) = s := by
  rw [neg_log_expNegUnit, max_eq_left hs]

private theorem expNegUnit_pair_ne_zero (s t : ℝ) :
    ∀ i, (![expNegUnit s, expNegUnit t] : Fin 2 → I) i ≠ 0 := by
  intro i
  fin_cases i
  · exact expNegUnit_ne_zero s
  · exact expNegUnit_ne_zero t

theorem pickandsOf_independence : EqOn (pickandsOf (independence 2)) (fun _ => 1) (Icc 0 1) := by
  rw [← pickandsCopula_const_one]
  exact pickandsOf_pickandsCopula _

theorem pickandsOf_comonotonic :
    EqOn (pickandsOf (comonotonic 2)) (fun t => max t (1 - t)) (Icc 0 1) := by
  rw [← pickandsCopula_max]
  exact pickandsOf_pickandsCopula _

/-! ### Gumbel–Hougaard -/

/-- The logistic Pickands function `(t^θ + (1-t)^θ)^{1/θ}`. -/
noncomputable def gumbelPickands (θ t : ℝ) : ℝ := (t ^ θ + (1 - t) ^ θ) ^ θ⁻¹

theorem pickandsOf_gumbel (θ : ℝ) (hθ : 1 ≤ θ) :
    EqOn (pickandsOf (gumbel θ hθ)) (gumbelPickands θ) (Icc 0 1) := by
  intro t ht
  rw [pickandsOf, evTail, cdf_gumbel θ hθ _ (expNegUnit_pair_ne_zero _ _)]
  have h0 : -Real.log ((![expNegUnit (1 - t), expNegUnit t] 0 : I) : ℝ) = 1 - t :=
    neg_log_expNegUnit_of_nonneg (sub_nonneg.2 ht.2)
  have h1 : -Real.log ((![expNegUnit (1 - t), expNegUnit t] 1 : I) : ℝ) = t :=
    neg_log_expNegUnit_of_nonneg ht.1
  rw [h0, h1, Real.log_exp, neg_neg, gumbelPickands, add_comm]

/-- The logistic function is a Pickands function for `θ ≥ 1`. -/
theorem isPickandsFunction_gumbelPickands (θ : ℝ) (hθ : 1 ≤ θ) :
    IsPickandsFunction (gumbelPickands θ) :=
  (isExtremeValue_gumbel θ hθ).isPickandsFunction_pickandsOf.congr (pickandsOf_gumbel θ hθ)

/-- The Gumbel–Hougaard copula is the Pickands copula of the logistic function. -/
theorem gumbel_eq_pickandsCopula (θ : ℝ) (hθ : 1 ≤ θ) :
    gumbel θ hθ = pickandsCopula (gumbelPickands θ) (isPickandsFunction_gumbelPickands θ hθ) :=
  (isExtremeValue_gumbel θ hθ).eq_pickandsCopula_of_eqOn _ (pickandsOf_gumbel θ hθ)

/-! ### Marshall–Olkin and Cuadras–Augé -/

/-- The Marshall–Olkin Pickands function `max(1 - β t, 1 - α (1 - t))`. -/
noncomputable def marshallOlkinPickands (α β t : ℝ) : ℝ := max (1 - β * t) (1 - α * (1 - t))

theorem pickandsOf_marshallOlkin (α β : I) :
    EqOn (pickandsOf (marshallOlkin α β)) (marshallOlkinPickands α β) (Icc 0 1) := by
  intro t ht
  rw [pickandsOf, evTail, cdf_marshallOlkin]
  change -Real.log (min ((expNegUnit (1 - t) : ℝ) ^ (α : ℝ)) ((expNegUnit t : ℝ) ^ (β : ℝ)) *
    ((expNegUnit (1 - t) : ℝ) ^ (1 - (α : ℝ)) * (expNegUnit t : ℝ) ^ (1 - (β : ℝ)))) = _
  rw [coe_expNegUnit, coe_expNegUnit, max_eq_left (sub_nonneg.2 ht.2), max_eq_left ht.1,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_monotone.map_min, ← Real.exp_add, ← Real.exp_add, Real.log_exp,
    marshallOlkinPickands]
  rcases le_total ((α : ℝ) * (1 - t)) ((β : ℝ) * t) with h | h
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rw [min_eq_left (by linarith), max_eq_left (by linarith)]
    ring

theorem isPickandsFunction_marshallOlkinPickands (α β : I) :
    IsPickandsFunction (marshallOlkinPickands α β) :=
  (isExtremeValue_marshallOlkin α β).isPickandsFunction_pickandsOf.congr
    (pickandsOf_marshallOlkin α β)

/-- The Marshall–Olkin copula is the Pickands copula of `max(1 - β t, 1 - α (1 - t))`. -/
theorem marshallOlkin_eq_pickandsCopula (α β : I) :
    marshallOlkin α β = pickandsCopula (marshallOlkinPickands α β)
      (isPickandsFunction_marshallOlkinPickands α β) :=
  (isExtremeValue_marshallOlkin α β).eq_pickandsCopula_of_eqOn _ (pickandsOf_marshallOlkin α β)

/-- The Cuadras–Augé copula is the Pickands copula of `1 - α min(t, 1 - t)`. -/
theorem cuadrasAuge_eq_pickandsCopula (α : I) :
    cuadrasAuge α = pickandsCopula (marshallOlkinPickands α α)
      (isPickandsFunction_marshallOlkinPickands α α) :=
  marshallOlkin_eq_pickandsCopula α α

theorem marshallOlkinPickands_self (α t : ℝ) (hα : 0 ≤ α) :
    marshallOlkinPickands α α t = 1 - α * min t (1 - t) := by
  rw [marshallOlkinPickands, mul_min_of_nonneg _ _ hα]
  rcases le_total (α * t) (α * (1 - t)) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-! ### Tawn's asymmetric logistic model -/

/-- Tawn's asymmetric logistic Pickands function
`(1-α)(1-t) + (1-β) t + ((α(1-t))^θ + (β t)^θ)^{1/θ}`. -/
noncomputable def tawnPickands (θ α β t : ℝ) : ℝ :=
  (1 - α) * (1 - t) + (1 - β) * t + ((α * (1 - t)) ^ θ + (β * t) ^ θ) ^ θ⁻¹

theorem pickandsOf_tawn (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    EqOn (pickandsOf (tawn θ hθ α β)) (tawnPickands θ α β) (Icc 0 1) := by
  intro t ht
  rw [pickandsOf, evTail, tawn_cdf_positive θ hθ α β _ _ (expNegUnit_ne_zero _)
    (expNegUnit_ne_zero _), neg_log_expNegUnit_of_nonneg (sub_nonneg.2 ht.2),
    neg_log_expNegUnit_of_nonneg ht.1, coe_expNegUnit, coe_expNegUnit,
    max_eq_left (sub_nonneg.2 ht.2), max_eq_left ht.1, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add, ← Real.exp_add, Real.log_exp, tawnPickands]
  ring

theorem isPickandsFunction_tawnPickands (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    IsPickandsFunction (tawnPickands θ α β) :=
  (isExtremeValue_tawn θ hθ α β).isPickandsFunction_pickandsOf.congr (pickandsOf_tawn θ hθ α β)

/-- Tawn's asymmetric logistic copula is the Pickands copula of `tawnPickands`. -/
theorem tawn_eq_pickandsCopula (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    tawn θ hθ α β = pickandsCopula (tawnPickands θ α β)
      (isPickandsFunction_tawnPickands θ hθ α β) :=
  (isExtremeValue_tawn θ hθ α β).eq_pickandsCopula_of_eqOn _ (pickandsOf_tawn θ hθ α β)

end ProbabilityTheory.Copula
