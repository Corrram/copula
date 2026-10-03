/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Exact

/-!
# Daniels' inequality between Kendall's tau and Spearman's rho

Daniels (1950) proved `-1 ≤ 3τ - 2ρ ≤ 1` for every continuous bivariate distribution
(Nelsen, *An Introduction to Copulas*, 2nd ed., §5.1.3). We derive it from the exact
`(τ, ρ)` region of Schreyer, Paulin and Trutschnig (2017), formalized in
`Copula.Rank.Region.RhoTau`: every copula lies above a point of the lower boundary with the
same `τ` and below the reflection of a boundary point with opposite `τ`, and along each
polynomial boundary arc

`1 - (3 τ - 2 ρ) = 2 n ((n+1)³ - 3 (n+1) s² - 2 s³) / ((n+1)² (n+2)²) ≥ 0`.

The bound is attained, e.g. at `(τ, ρ) = (0, -1/2)` (the arc `n = 1`, `s = 1`).
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace RankRegion.RhoTau

/-- The closed form of `1 - (3 τ - 2 ρ)` along a lower boundary arc. -/
private theorem one_sub_daniels_arc (n : ℕ) (s : ℝ) :
    1 - (3 * arcTau n s - 2 * arcRho n s) =
      2 * n * (((n : ℝ) + 1) ^ 3 - 3 * ((n : ℝ) + 1) * s ^ 2 - 2 * s ^ 3) /
        (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2) := by
  unfold arcTau arcRho
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- Daniels' bound along every lower boundary arc. -/
private theorem daniels_arc (n : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    3 * arcTau n s - 2 * arcRho n s ≤ 1 := by
  have hnum : 0 ≤ 2 * (n : ℝ) * (((n : ℝ) + 1) ^ 3 - 3 * ((n : ℝ) + 1) * s ^ 2 - 2 * s ^ 3) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hs2 : s ^ 2 ≤ 1 := by nlinarith
      have hs3 : s ^ 3 ≤ 1 := by nlinarith
      have hq : 0 ≤ ((n : ℝ) + 1) ^ 3 - 3 * ((n : ℝ) + 1) * s ^ 2 - 2 * s ^ 3 := by
        have hA := mul_le_mul_of_nonneg_left hs2 (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
        have hB : 0 ≤ ((n : ℝ) - 1) * ((n : ℝ) + 2) ^ 2 :=
          mul_nonneg (by linarith) (by positivity)
        nlinarith
      positivity
  have h := one_sub_daniels_arc n s
  have : 0 ≤ 1 - (3 * arcTau n s - 2 * arcRho n s) := by
    rw [h]
    positivity
  linarith

/-- Daniels' bound at every lower boundary parameter. -/
theorem LowerParameter.three_mul_tau_sub_two_mul_rho_le (p : LowerParameter) :
    3 * p.tau - 2 * p.rho ≤ 1 := by
  cases p with
  | endpoint => simp [LowerParameter.tau, LowerParameter.rho]; norm_num
  | arc n s => exact daniels_arc n s s.property.1 s.property.2

end RankRegion.RhoTau

open RankRegion.RhoTau in
/-- Daniels' inequality, upper half: `3 τ - 2 ρ ≤ 1` (Nelsen, §5.1.3). -/
theorem three_mul_kendallTau_sub_two_mul_spearmanRho_le (C : Copula 2) :
    3 * C.kendallTau - 2 * C.spearmanRho ≤ 1 := by
  obtain ⟨p, ht, hr⟩ := universal_lower C
  have := p.three_mul_tau_sub_two_mul_rho_le
  rw [ht] at this
  linarith

open RankRegion.RhoTau in
/-- Daniels' inequality, lower half: `-1 ≤ 3 τ - 2 ρ` (Nelsen, §5.1.3). -/
theorem neg_one_le_three_mul_kendallTau_sub_two_mul_spearmanRho (C : Copula 2) :
    -1 ≤ 3 * C.kendallTau - 2 * C.spearmanRho := by
  obtain ⟨p, ht, hr⟩ := universal_upper C
  have := p.three_mul_tau_sub_two_mul_rho_le
  rw [ht] at this
  linarith

/-- Daniels' inequality `|3 τ - 2 ρ| ≤ 1` (Daniels 1950; Nelsen, §5.1.3). -/
theorem abs_three_mul_kendallTau_sub_two_mul_spearmanRho_le (C : Copula 2) :
    |3 * C.kendallTau - 2 * C.spearmanRho| ≤ 1 :=
  abs_le.mpr ⟨C.neg_one_le_three_mul_kendallTau_sub_two_mul_spearmanRho,
    C.three_mul_kendallTau_sub_two_mul_spearmanRho_le⟩

end ProbabilityTheory.Copula
