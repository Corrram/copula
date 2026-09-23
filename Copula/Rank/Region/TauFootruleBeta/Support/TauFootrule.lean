import Copula.Rank.Region.TauFootruleBeta.Support.RankMoments

/-! # Universal Kendall tau versus Spearman footrule bounds

The lower bound follows by comparing the two diagonal evaluations with the
CDF at the sampled point. The upper bound uses C(u,v) <= min(u,v).
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support

theorem diagonal_pair_le (C : Copula 2) (u v : I) :
    C.cdf ![u, u] + C.cdf ![v, v] ≤ 2 * C.cdf ![u, v] + |(u : ℝ) - v| := by
  rcases le_total u v with huv | hvu
  · have h₁ := C.monotone_cdf (show ![u, u] ≤ ![u, v] from by
        intro i; fin_cases i <;> simp [huv])
    have h₂ := C.cdf_sub_le_sum_abs ![v, v] ![u, v]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
      abs_zero, add_zero] at h₂
    rw [abs_sub_comm (u : ℝ) (v : ℝ)]
    linarith
  · have h₁ := C.monotone_cdf (show ![v, v] ≤ ![u, v] from by
        intro i; fin_cases i <;> simp [hvu])
    have h₂ := C.cdf_sub_le_sum_abs ![u, u] ![u, v]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
      abs_zero, zero_add] at h₂
    linarith

theorem tau_footrule_lower (C : Copula 2) :
    4 / 3 * C.spearmanFootrule - 1 / 3 ≤ C.kendallTau := by
  have h := integral_mono (μ := C.toMeasure)
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I =>
      C.cdf ![x 0, x 0] + C.cdf ![x 1, x 1]) by fun_prop))
    (Copula.integrable_continuous_cube _ (show Continuous (fun x : Fin 2 → I =>
      2 * C.cdf ![x 0, x 1] + |(x 0 : ℝ) - x 1|) by fun_prop))
    (fun x => diagonal_pair_le C (x 0) (x 1))
  have hx (x : Fin 2 → I) : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  simp only [hx] at h
  rw [integral_add, integral_add, integral_const_mul,
    C.integral_eval 0 (fun t => C.cdf ![t, t]) (by fun_prop),
    C.integral_eval 1 (fun t => C.cdf ![t, t]) (by fun_prop)] at h
  · have hp := footrule_eq_abs_moment C
    unfold Copula.spearmanFootrule at hp ⊢
    unfold Copula.kendallTau
    linarith
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

theorem tau_footrule_upper (C : Copula 2) :
    C.kendallTau ≤ 2 / 3 * C.spearmanFootrule + 1 / 3 := by
  have h := C.lowerOrthantLE_comonotonic.concordanceQ_le_left C
  rw [Copula.concordanceQ_self, Copula.concordanceQ_comm,
    Copula.concordanceQ_comonotonic] at h
  linarith

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
