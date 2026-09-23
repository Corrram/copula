import Copula.Rank.Region.MeanVariance.Paper.BoundaryFormula

/-! # Exactly the zero-variance means

This closes the contact-set characterization in Proposition 1.6(iii).
-/

open MeasureTheory ProbabilityTheory
open Copula.RankRegion
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.MeanVariance

private theorem correction_positive {k v : ℝ} (hk : 0 < k) (hv : 0 < v) (hkv : k * v ≤ 1 / 2) :
    0 < 2 / 3 * k * v ^ 3 - k ^ 2 * v ^ 4 := by
  have h := mul_pos (mul_pos hk (pow_pos hv 3)) (show 0 < 2 / 3 - k * v by linarith)
  convert h using 1
  ring

private theorem right_variance_polynomial (S : RhoFootrule.RightData) :
    minimumVariance (S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2) =
      2 / 3 * (S.N * (S.N + 1)) * S.v ^ 3 - (S.N * (S.N + 1)) ^ 2 * S.v ^ 4 := by
  unfold minimumVariance
  rw [show 1 - 3 * (S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2) =
    (RhoFootrule.UpperParameter.right S).footrule by rfl, upperRho_parameter]
  dsimp [RhoFootrule.UpperParameter.rho]
  ring

private theorem right_variance_zero (S : RhoFootrule.RightData)
    (h : minimumVariance (S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2) = 0) : S.v = 0 := by
  have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
  have hkv : (S.N * (S.N + 1) : ℝ) * S.v ≤ 1 / 2 := by
    have hw := mul_nonneg (show (0 : ℝ) ≤ S.N + 1 by positivity) S.w_nonneg
    nlinarith only [S.normalized, hw]
  rw [right_variance_polynomial] at h
  by_contra hv
  have hp := correction_positive (by positivity : (0 : ℝ) < S.N * (S.N + 1))
    (lt_of_le_of_ne S.v_nonneg (Ne.symm hv)) hkv
  linarith

private theorem left_variance_polynomial (S : RhoFootrule.LeftData) :
    minimumVariance (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2) =
      2 / 3 * (S.N * (S.N + 1)) * S.v ^ 3 - (S.N * (S.N + 1)) ^ 2 * S.v ^ 4 := by
  unfold minimumVariance
  rw [show 1 - 3 * (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2) =
    (RhoFootrule.UpperParameter.left S).footrule by rfl, upperRho_parameter]
  dsimp [RhoFootrule.UpperParameter.rho]
  ring

private theorem left_variance_zero (S : RhoFootrule.LeftData)
    (h : minimumVariance (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2) = 0) : S.v = 0 := by
  have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
  have hkv : (S.N * (S.N + 1) : ℝ) * S.v ≤ 1 / 2 := by
    have hw := mul_nonneg (show (0 : ℝ) ≤ S.N by positivity) S.w_nonneg
    nlinarith only [S.normalized, hw]
  rw [left_variance_polynomial] at h
  by_contra hv
  have hp := correction_positive (by positivity : (0 : ℝ) < S.N * (S.N + 1))
    (lt_of_le_of_ne S.v_nonneg (Ne.symm hv)) hkv
  linarith

/-- The correction vanishes exactly at zero and the reciprocal even-integer means. -/
theorem minimum_variance_zero_iff {m : ℝ} (hm : m ∈ Set.Icc 0 (1 / 2)) :
    minimumVariance m = 0 ↔ m = 0 ∨ ∃ N : ℕ, 0 < N ∧ m = 1 / (2 * (N : ℝ)) := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := RhoFootrule.upperParameter_exists
      (show 1 - 3 * m ∈ Set.Icc (-1 / 2 : ℝ) 1 by constructor <;> linarith [hm.1, hm.2])
    cases a with
    | endpoint =>
      change 1 = 1 - 3 * m at ha
      exact Or.inl (by linarith)
    | right S =>
      have he : m = S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2 := by
        change 1 - 3 * (S.w + S.N * S.v + S.N * (S.N + 1) * S.v ^ 2) = 1 - 3 * m at ha
        linarith
      have hv := right_variance_zero S (he ▸ h)
      simp only [hv, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
      refine Or.inr ⟨S.N + 1, Nat.succ_pos _, ?_⟩
      have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
      apply (eq_div_iff (by positivity)).mpr
      have hh := S.normalized
      simp only [hv, mul_zero, add_zero] at hh
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith only [hh, he]
    | left S =>
      have he : m = S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2 := by
        change 1 - 3 * (S.w + (S.N + 1) * S.v - S.N * (S.N + 1) * S.v ^ 2) = 1 - 3 * m at ha
        linarith
      have hv := left_variance_zero S (he ▸ h)
      simp only [hv, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] at he
      refine Or.inr ⟨S.N, S.N_pos, ?_⟩
      have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
      apply (eq_div_iff (by positivity)).mpr
      have hh := S.normalized
      simp only [hv, mul_zero, add_zero] at hh
      nlinarith only [hh, he]
  · rintro (rfl | ⟨N, hN, rfl⟩)
    · unfold minimumVariance
      norm_num [show upperRho 1 = 1 from upperRho_parameter .endpoint]
    · let S : RhoFootrule.LeftData :=
        { N := N, N_pos := hN, v := 0, w := 1 / (2 * (N : ℝ)),
          v_nonneg := le_rfl, w_nonneg := by positivity,
          normalized := by
            have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
            field_simp [hn]
            ring }
      have h := left_variance_polynomial S
      simpa [S] using h

/-- Theorem 2.4's constant-value classification in the equivalent uniform-copula coordinates. -/
theorem constant_displacement_iff {m : ℝ} (hm : m ∈ Set.Icc 0 (1 / 2)) :
    (∃ C : Copula 2, ∀ᵐ x ∂C.toMeasure, |(x 0 : ℝ) - x 1| = m) ↔
      m = 0 ∨ ∃ N : ℕ, 0 < N ∧ m = 1 / (2 * (N : ℝ)) := by
  rw [← minimum_variance_zero_iff hm]
  constructor
  · rintro ⟨C, hC⟩
    have hmean : (∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure) = m := by
      rw [integral_congr_ae hC, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    have hsq : (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure) = m ^ 2 := by
      have he : (fun x : Fin 2 → I => ((x 0 : ℝ) - x 1) ^ 2) =ᵐ[C.toMeasure] fun _ => m ^ 2 := by
        filter_upwards [hC] with x hx
        nlinarith only [sq_abs ((x 0 : ℝ) - x 1), congrArg (fun r : ℝ => r ^ 2) hx]
      rw [integral_congr_ae he, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
    have h := sharp_second_moment C
    dsimp only at h
    rw [hmean, hsq] at h
    exact le_antisymm (by linarith only [h]) (minimum_variance_nonneg hm)
  · intro h
    obtain ⟨C, _, hvar⟩ := minimum_variance_attained hm
    rw [h] at hvar
    have he := (integral_eq_zero_iff_of_nonneg (fun x : Fin 2 → I =>
      sq_nonneg (|(x 0 : ℝ) - x 1| - m))
      (Copula.integrable_continuous_cube C.toMeasure (by fun_prop))).mp hvar
    refine ⟨C, ?_⟩
    filter_upwards [he] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

end ProbabilityTheory.Copula.RankRegion.MeanVariance
