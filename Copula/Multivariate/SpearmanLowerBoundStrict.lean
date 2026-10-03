/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Multivariate.SpearmanLowerBound
import Copula.Order.Survival
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The lower bound of multivariate Spearman's rho is not best possible for `d ≥ 3`

`Copula.Multivariate.SpearmanLowerBound` proves the classical bound
`ρ_d(C) ≥ (2^d - (d+1)!) / (d! (2^d - d - 1))` for the multivariate Spearman's rho
`ρ_d(C) = (d+1)/(2^d - d - 1) · (2^d ∫ C dΠ - 1)` (Nelsen 1996; Schmid–Schmidt 2007, `ρ₁`), which
comes from `C ≥ W_d` and `∫ W_d dΠ = 1/(d+1)!`. For `d = 2` it is the sharp bound `-1`. For
`d ≥ 3` the lower Fréchet–Hoeffding bound `W_d` is not a copula, and the bound is in fact **not
best possible**: there is a uniform gap.

Main results:
* `exp_neg_le_integral_cdf`: `∫ C dΠ ≥ e^{-d}` for every `d`-copula. Proof: by Fubini
  `∫ C dΠ = E_C[∏ᵢ (1 - Uᵢ)] = E_C[exp(∑ᵢ log(1 - Uᵢ))]`; the tangent line
  `exp(s) ≥ e^{-d} (1 + d + s)` and `E[log(1 - Uᵢ)] = ∫₀¹ log(1 - t) dt = -1` give
  `∫ C dΠ ≥ e^{-d}` (this is Jensen's inequality for `exp`).
* `exp_lt_factorial`: `e^d < (d+1)!` for `d ≥ 3`, hence `1/(d+1)! < e^{-d}`.
* `one_div_factorial_lt_integral_cdf`: for `d ≥ 3`, `∫ C dΠ > 1/(d+1)!` for every copula (so the
  bound is never attained), and `le_multivariateSpearmanRho_exp`:
  `ρ_d(C) ≥ (d+1)/(2^d - d - 1) · (2^d e^{-d} - 1)`, which is strictly larger than the classical
  bound for `d ≥ 3` (`lowerBound_lt_expBound`).
* `exists_gap_multivariateSpearmanRho`: for `d ≥ 3` there is `ε > 0` with
  `ρ_d(C) ≥ (2^d - (d+1)!)/(d!(2^d - d - 1)) + ε` for all `C`; in particular the classical bound
  is not the infimum (`not_isGLB_lowerBound`). For `d = 3`: `ρ₃(C) ≥ 8e^{-3} - 1 ≈ -0.6017 > -2/3`
  (`multivariateSpearmanRho_three_ge`).

The exact infimum is not determined here. The bound `8e^{-3} - 1 ≈ -0.6017` is not attained,
since `-log(1 - Uᵢ)` are exponential and cannot have a constant sum. The sharp dual bound
(`Copula.Multivariate.SpearmanInfimumDual`) gives `ρ₃ ≥ -0.56158`
(`Copula.Multivariate.SpearmanInfimumThree`), and an explicit copula has `ρ₃ = -631/1125`
(`Copula.Multivariate.SpearmanInfimumWitness`); numerically the infimum is `≈ -0.5615741`.

References: R. B. Nelsen, *Nonparametric measures of multivariate association* (1996);
F. Schmid and R. Schmidt, *Multivariate extensions of Spearman's rho and related statistics*,
Statist. Probab. Lett. 77 (2007) 407–416.
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

theorem integrable_log_one_sub : Integrable (fun t : I => Real.log (1 - (t : ℝ))) := by
  have h : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume 0 1 := by
    have := ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).comp_sub_left 1).symm
    simpa using this
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at h
  exact (unitInterval.measurePreserving_coe.integrable_comp_emb
    unitInterval.measurableEmbedding_coe).2 h

/-- `∫₀¹ log(1 - t) dt = -1`. -/
theorem integral_log_one_sub : (∫ t : I, Real.log (1 - (t : ℝ))) = -1 := by
  rw [integral_unitInterval (fun t => Real.log (1 - t)),
    intervalIntegral.integral_comp_sub_left (fun t => Real.log t), integral_log]
  norm_num

theorem integrable_log_one_sub_eval (C : Copula d) (i : Fin d) :
    Integrable (fun y : Fin d → I => Real.log (1 - (y i : ℝ))) C.toMeasure := by
  have hm : Measurable (fun t : I => Real.log (1 - (t : ℝ))) := by fun_prop
  exact (C.measurePreserving_eval i).integrable_comp hm.aestronglyMeasurable |>.2
    integrable_log_one_sub

theorem integral_log_one_sub_eval (C : Copula d) (i : Fin d) :
    (∫ y, Real.log (1 - (y i : ℝ)) ∂C.toMeasure) = -1 := by
  rw [C.integral_eval i (fun t : I => Real.log (1 - (t : ℝ))) (by fun_prop),
    integral_log_one_sub]

/-- The tangent-line inequality behind Jensen's bound: for `yᵢ < 1`,
`∏ᵢ (1 - yᵢ) ≥ e^{-d} (1 + d + ∑ᵢ log(1 - yᵢ))`. -/
theorem exp_neg_mul_le_prod {y : Fin d → I} (hy : ∀ i, (y i : ℝ) < 1) :
    Real.exp (-(d : ℝ)) * (1 + d + ∑ i, Real.log (1 - (y i : ℝ))) ≤ ∏ i, (1 - (y i : ℝ)) := by
  have hprod : ∏ i, (1 - (y i : ℝ)) = Real.exp (∑ i, Real.log (1 - (y i : ℝ))) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => (Real.exp_log (by linarith [hy i])).symm
  rw [hprod]
  set S := ∑ i, Real.log (1 - (y i : ℝ))
  have h := Real.add_one_le_exp (S + d)
  calc Real.exp (-(d : ℝ)) * (1 + d + S) ≤ Real.exp (-(d : ℝ)) * Real.exp (S + d) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = Real.exp S := by rw [← Real.exp_add]; ring_nf

/-- **Jensen's lower bound**: every `d`-copula satisfies `∫ C dΠ ≥ e^{-d}`. -/
theorem exp_neg_le_integral_cdf (C : Copula d) :
    Real.exp (-(d : ℝ)) ≤ ∫ u, C.cdf u ∂(independence d).toMeasure := by
  rw [integral_cdf_independence_eq_prod]
  have hsum : Integrable (fun y : Fin d → I => ∑ i, Real.log (1 - (y i : ℝ))) C.toMeasure :=
    integrable_finsetSum _ fun i _ => integrable_log_one_sub_eval C i
  have hg : Integrable (fun y : Fin d → I =>
      Real.exp (-(d : ℝ)) * (1 + d + ∑ i, Real.log (1 - (y i : ℝ)))) C.toMeasure :=
    ((integrable_const _).add hsum).const_mul _
  have hval : (∫ y, Real.exp (-(d : ℝ)) * (1 + d + ∑ i, Real.log (1 - (y i : ℝ)))
      ∂C.toMeasure) = Real.exp (-(d : ℝ)) := by
    rw [integral_const_mul, integral_add (integrable_const _) hsum,
      integral_finsetSum _ fun i _ => integrable_log_one_sub_eval C i]
    simp only [integral_log_one_sub_eval, integral_const, probReal_univ, one_smul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← hval]
  apply integral_mono_ae hg (integrable_continuous_cube _ (by fun_prop))
  have hne : ∀ᵐ y ∂C.toMeasure, ∀ i, y i ≠ 1 := ae_all_iff.2 fun i => C.ae_eval_ne i 1
  filter_upwards [hne] with y hy
  exact exp_neg_mul_le_prod fun i =>
    lt_of_le_of_ne (y i).2.2 fun h => hy i (Subtype.ext h)

/-- `e^d < (d+1)!` for `d ≥ 3`. -/
theorem exp_lt_factorial (hd : 3 ≤ d) : Real.exp d < (d + 1).factorial := by
  induction d, hd using Nat.le_induction with
  | base =>
    have h3 : Real.exp (3 : ℕ) = Real.exp (1 / 16) ^ 48 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    have he := Real.exp_bound_div_one_sub_of_interval (x := 1 / 16) (by norm_num) (by norm_num)
    have : Real.exp (1 / 16) ^ 48 ≤ (1 / (1 - 1 / 16)) ^ 48 :=
      pow_le_pow_left₀ (Real.exp_pos _).le he 48
    norm_num [Nat.factorial] at this ⊢
    linarith
  | succ n hn ih =>
    have he : Real.exp 1 ≤ 4 := by
      have h := Real.exp_bound_div_one_sub_of_interval (x := 1 / 2) (by norm_num) (by norm_num)
      have h2 : Real.exp 1 = Real.exp (1 / 2) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have : Real.exp (1 / 2) ^ 2 ≤ (1 / (1 - 1 / 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le h 2
      norm_num at this
      linarith
    have hsplit : Real.exp ((n + 1 : ℕ) : ℝ) = Real.exp n * Real.exp 1 := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [hsplit, Nat.factorial_succ (n + 1)]
    push_cast
    have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    calc Real.exp n * Real.exp 1 < ((n + 1).factorial : ℝ) * Real.exp 1 :=
          mul_lt_mul_of_pos_right ih (Real.exp_pos _)
      _ ≤ ((n + 1).factorial : ℝ) * 4 := mul_le_mul_of_nonneg_left he hf.le
      _ ≤ ((n : ℝ) + 1 + 1) * ((n + 1).factorial : ℝ) := by nlinarith

/-- `1/(d+1)! < e^{-d}` for `d ≥ 3`. -/
theorem one_div_factorial_lt_exp_neg (hd : 3 ≤ d) :
    1 / ((d + 1).factorial : ℝ) < Real.exp (-(d : ℝ)) := by
  rw [Real.exp_neg, one_div]
  exact inv_strictAnti₀ (Real.exp_pos _) (exp_lt_factorial hd)

/-- For `d ≥ 3` the bound `∫ C dΠ ≥ 1/(d+1)!` is strict for every copula: it is never
attained (`W_d` is not a copula). -/
theorem one_div_factorial_lt_integral_cdf (hd : 3 ≤ d) (C : Copula d) :
    1 / ((d + 1).factorial : ℝ) < ∫ u, C.cdf u ∂(independence d).toMeasure :=
  (one_div_factorial_lt_exp_neg hd).trans_le (exp_neg_le_integral_cdf C)

/-- **Improved lower bound of multivariate Spearman's rho**:
`ρ_d(C) ≥ (d+1)/(2^d - d - 1) · (2^d e^{-d} - 1)` for every `d`-copula, `d ≥ 2`. -/
theorem le_multivariateSpearmanRho_exp (hd : 2 ≤ d) (C : Copula d) :
    ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) * ((2 : ℝ) ^ d * Real.exp (-(d : ℝ)) - 1) ≤
      C.multivariateSpearmanRho := by
  have hD : 0 < (2 : ℝ) ^ d - d - 1 := by linarith [dim_add_one_lt_two_pow hd]
  rw [multivariateSpearmanRho]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hD.le)
  have := exp_neg_le_integral_cdf C
  have h2 : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

/-- For `d ≥ 3` the improved bound is strictly larger than the classical bound
`(2^d - (d+1)!)/(d!(2^d - d - 1))`. -/
theorem lowerBound_lt_expBound (hd : 3 ≤ d) :
    ((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1)) <
      ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) * ((2 : ℝ) ^ d * Real.exp (-(d : ℝ)) - 1) := by
  have hD : 0 < (2 : ℝ) ^ d - d - 1 := by linarith [dim_add_one_lt_two_pow (by omega : 2 ≤ d)]
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hfs : ((d + 1).factorial : ℝ) = (d + 1) * d.factorial := by
    push_cast [Nat.factorial_succ]
    ring
  have hlhs : ((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1)) =
      ((d : ℝ) + 1) / ((2 : ℝ) ^ d - d - 1) *
        ((2 : ℝ) ^ d * (1 / (d + 1).factorial) - 1) := by
    rw [hfs]
    field_simp
  rw [hlhs]
  apply mul_lt_mul_of_pos_left _ (div_pos (by positivity) hD)
  have := one_div_factorial_lt_exp_neg hd
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  nlinarith

/-- **The classical lower bound is not best possible for `d ≥ 3`**: there is a uniform gap
`ε > 0` with `ρ_d(C) ≥ (2^d - (d+1)!)/(d!(2^d - d - 1)) + ε` for every `d`-copula. -/
theorem exists_gap_multivariateSpearmanRho (hd : 3 ≤ d) :
    ∃ ε > 0, ∀ C : Copula d,
      ((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1)) + ε ≤
        C.multivariateSpearmanRho := by
  refine ⟨_, sub_pos.2 (lowerBound_lt_expBound hd), fun C => ?_⟩
  have := le_multivariateSpearmanRho_exp (by omega) C
  linarith

/-- For `d ≥ 3` the classical lower bound is not the infimum of `ρ_d` over `d`-copulas. -/
theorem not_isGLB_lowerBound (hd : 3 ≤ d) :
    ¬ IsGLB (Set.range (fun C : Copula d => C.multivariateSpearmanRho))
      (((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1))) := by
  intro h
  obtain ⟨ε, hε, hC⟩ := exists_gap_multivariateSpearmanRho hd
  have hlb : (((2 : ℝ) ^ d - (d + 1).factorial) / (d.factorial * ((2 : ℝ) ^ d - d - 1)) + ε) ∈
      lowerBounds (Set.range (fun C : Copula d => C.multivariateSpearmanRho)) := by
    rintro _ ⟨C, rfl⟩
    exact hC C
  linarith [h.2 hlb]

/-- For `d = 3`: `ρ₃(C) ≥ 8e^{-3} - 1 ≈ -0.6017`, strictly above the classical bound `-2/3`. -/
theorem multivariateSpearmanRho_three_ge (C : Copula 3) :
    8 * Real.exp (-3) - 1 ≤ C.multivariateSpearmanRho := by
  have h := le_multivariateSpearmanRho_exp (by norm_num) C
  norm_num at h
  linarith

theorem neg_two_thirds_lt_exp_bound_three : (-2 / 3 : ℝ) < 8 * Real.exp (-3) - 1 := by
  have h := one_div_factorial_lt_exp_neg (d := 3) le_rfl
  norm_num [Nat.factorial] at h
  linarith

end ProbabilityTheory.Copula
