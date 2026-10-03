/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Multivariate.Concordance
import Copula.Multivariate.LowerBound

/-!
# The lower bound of multivariate Spearman's rho

The lower Fréchet–Hoeffding bound `W_d(u) = max(0, u₁ + ⋯ + u_d - d + 1)` satisfies

`∫_{[0,1]^d} W_d dΠ_d = 1 / (d+1)!`

(`integral_lowerFrechetBound`): after the reflection `vᵢ = 1 - uᵢ` it is the integral of
`max(0, 1 - ∑ vᵢ)` over the cube, i.e. the volume of the `(d+1)`-dimensional simplex. Since every
`d`-copula dominates `W_d` pointwise, `∫ C dΠ ≥ 1/(d+1)!`, and the multivariate Spearman's rho
`ρ_d(C) = (d+1)/(2^d - d - 1) · (2^d ∫ C dΠ - 1)` (`multivariateSpearmanRho`) satisfies

`ρ_d(C) ≥ (2^d - (d+1)!) / (d! (2^d - d - 1))`

(`le_multivariateSpearmanRho`; Nelsen 1996, Joe 1990; Schmid–Schmidt 2007). For `d = 2` this is
`-1` (attained at `W`), for `d = 3` it is `-2/3`.

The integral is computed by induction on the dimension: for `s ≤ 1`,
`∫_{[0,1]^n} max(0, s - ∑(1 - xᵢ)) dx = max(0, s)^{n+1} / (n+1)!`
(`integral_max_zero_sub_sum`).

References: R. B. Nelsen, *Nonparametric measures of multivariate association* (1996);
F. Schmid and R. Schmidt, *Multivariate extensions of Spearman's rho and related statistics*,
Statist. Probab. Lett. 77 (2007) 407–416; H. Joe, *Multivariate concordance*, J. Multivariate
Anal. 35 (1990).
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-- `∫₀¹ max(0, s - (1 - t))^{k+1} dt = max(0, s)^{k+2} / (k+2)` for `s ≤ 1`. -/
theorem integral_unit_max_zero_pow (k : ℕ) {s : ℝ} (hs : s ≤ 1) :
    (∫ t : I, (max 0 (s - (1 - (t : ℝ)))) ^ (k + 1)) = (max 0 s) ^ (k + 2) / (k + 2) := by
  rw [integral_unitInterval (fun t => (max 0 (s - (1 - t))) ^ (k + 1))]
  have hshift : (∫ t in (0 : ℝ)..1, (max 0 (s - (1 - t))) ^ (k + 1)) =
      ∫ w in (s - 1)..s, (max 0 w) ^ (k + 1) := by
    have h := intervalIntegral.integral_comp_add_right (fun w : ℝ => (max 0 w) ^ (k + 1))
      (a := (0 : ℝ)) (b := 1) (s - 1)
    simp only [zero_add] at h
    rw [show (1 : ℝ) + (s - 1) = s by ring] at h
    rw [← h]
    congr 1
    funext t
    congr 2
    ring
  rw [hshift]
  have hzero : ∀ a b : ℝ, a ≤ b → b ≤ 0 → (∫ w in a..b, (max 0 w) ^ (k + 1)) = 0 := by
    intro a b hab hb
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
    intro w hw
    rw [uIcc_of_le hab] at hw
    simp only
    rw [max_eq_left (hw.2.trans hb), zero_pow (Nat.succ_ne_zero k)]
  rcases le_or_gt s 0 with h0 | h0
  · rw [max_eq_left h0, zero_pow (by omega), zero_div]
    exact hzero _ _ (by linarith) h0
  · have hcont : Continuous (fun w : ℝ => (max 0 w) ^ (k + 1)) := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      hzero _ _ (by linarith) le_rfl, zero_add, max_eq_right h0.le]
    rw [intervalIntegral.integral_congr (g := fun w => w ^ (k + 1)), integral_pow]
    · push_cast
      rw [zero_pow (by omega), sub_zero]
      ring
    · intro w hw
      rw [uIcc_of_le h0.le] at hw
      simp only
      rw [max_eq_right hw.1]

/-- **Volume of the simplex**: for `s ≤ 1`,
`∫_{[0,1]^n} max(0, s - ∑ (1 - xᵢ)) dx = max(0, s)^{n+1} / (n+1)!`. -/
theorem integral_max_zero_sub_sum (n : ℕ) {s : ℝ} (hs : s ≤ 1) :
    (∫ x : Fin n → I, max 0 (s - ∑ i, (1 - (x i : ℝ))) ∂(Measure.pi fun _ => volume)) =
      (max 0 s) ^ (n + 1) / (n + 1).factorial := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure I))
      0).symm
    rw [← hmp.integral_comp']
    have hfun : (fun p : I × (Fin n → I) => max 0 (s - ∑ i, (1 - ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => I) 0).symm p i : ℝ)))) =
        fun p => max 0 ((s - (1 - (p.1 : ℝ))) - ∑ i, (1 - (p.2 i : ℝ))) := by
      funext p
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.cons_zero, cast_eq]
      congr 1
      ring
    rw [hfun]
    have hint : Integrable (fun p : I × (Fin n → I) =>
        max 0 ((s - (1 - (p.1 : ℝ))) - ∑ i, (1 - (p.2 i : ℝ))))
        ((volume : Measure I).prod (Measure.pi fun _ => volume)) :=
      (by fun_prop : Continuous (fun p : I × (Fin n → I) =>
        max 0 ((s - (1 - (p.1 : ℝ))) - ∑ i, (1 - (p.2 i : ℝ))))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_prod _ hint]
    simp only
    have hstep : ∀ t : I, (∫ y : Fin n → I, max 0 ((s - (1 - (t : ℝ))) - ∑ i, (1 - (y i : ℝ)))
        ∂(Measure.pi fun _ => volume)) = (max 0 (s - (1 - (t : ℝ)))) ^ (n + 1) /
          (n + 1).factorial := fun t => ih (by linarith [t.2.2])
    simp_rw [hstep]
    rw [integral_div, integral_unit_max_zero_pow n hs, Nat.factorial_succ (n + 1)]
    push_cast
    field_simp
    ring

variable {d : ℕ}

/-- **`∫ W_d dΠ_d = 1/(d+1)!`**. -/
theorem integral_lowerFrechetBound (d : ℕ) :
    (∫ u, lowerFrechetBound d u ∂(independence d).toMeasure) = 1 / (d + 1).factorial := by
  have h := integral_max_zero_sub_sum d (s := 1) le_rfl
  rw [max_eq_right zero_le_one, one_pow] at h
  rw [toMeasure_independence, ← h]
  congr 1
  funext u
  rw [lowerFrechetBound, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  ring

/-- Every `d`-copula has `∫ C dΠ ≥ 1/(d+1)!`. -/
theorem one_div_factorial_le_integral_cdf (C : Copula d) :
    1 / ((d + 1).factorial : ℝ) ≤ ∫ u, C.cdf u ∂(independence d).toMeasure := by
  rw [← integral_lowerFrechetBound d]
  exact integral_mono (integrable_continuous_cube _
    (by unfold lowerFrechetBound; fun_prop)) (C.integrable_cdf _)
    (fun u => lowerFrechetBound_le_cdf C u)

/-- **Lower bound of multivariate Spearman's rho**:
`ρ_d(C) ≥ (2^d - (d+1)!) / (d! (2^d - d - 1))` for every `d`-copula, `d ≥ 2`
(Nelsen 1996; Schmid–Schmidt 2007). -/
theorem le_multivariateSpearmanRho (hd : 2 ≤ d) (C : Copula d) :
    ((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1)) ≤
      C.multivariateSpearmanRho := by
  have hlt := dim_add_one_lt_two_pow hd
  have hD : 0 < (2 : ℝ) ^ d - d - 1 := by linarith
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hint := one_div_factorial_le_integral_cdf C
  have hfs : ((d + 1).factorial : ℝ) = (d + 1) * d.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  rw [hfs] at hint
  have hlhs : ((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1)) =
      ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) *
        ((2 : ℝ) ^ d * (1 / (((d : ℝ) + 1) * d.factorial)) - 1) := by
    rw [hfs]
    field_simp
  rw [hlhs, multivariateSpearmanRho]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hD.le)
  have : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

/-- For `d = 3` the lower bound is `ρ₃ ≥ -2/3`. -/
theorem neg_two_thirds_le_multivariateSpearmanRho_three (C : Copula 3) :
    -2 / 3 ≤ C.multivariateSpearmanRho := by
  have h := le_multivariateSpearmanRho (by norm_num) C
  norm_num [Nat.factorial] at h
  linarith

end ProbabilityTheory.Copula
