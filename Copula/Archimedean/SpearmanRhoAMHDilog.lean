/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.SpearmanRhoAMH
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Spearman's rho of the AMH copula in dilogarithm form

Nelsen, *An Introduction to Copulas*, second edition, Example 5.7 (Table 4.1, family 4.2.3): for
`0 < |θ| < 1`
`ρ_θ = 12 (1 + θ)/θ² · Li₂(θ) − 3 (θ + 12)/θ − 24 (1 − θ)/θ² · log (1 − θ)`,
where `Li₂(x) = ∑ₙ xⁿ / n²` is the dilogarithm (`dilogSeries`); in Nelsen's notation
`Li₂(θ) = dilog(1 − θ)` for `dilog(x) = ∫₁ˣ log t/(1 − t) dt`.

The proof uses the partial fraction decomposition
`1 / ((k+1)² (k+2)²) = 1/(k+1)² + 1/(k+2)² − 2/(k+1) + 2/(k+2)` in the series of
`spearmanRho_amh` and the power series of `Li₂` and of `−log (1 − x)`.
-/

open Filter
open scoped Topology

namespace ProbabilityTheory.Copula

/-- The dilogarithm as a power series, `Li₂(x) = ∑ₙ x^{n+1} / (n+1)²` (`|x| ≤ 1`). -/
noncomputable def dilogSeries (x : ℝ) : ℝ := ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2

theorem summable_dilogSeries {x : ℝ} (hx : |x| ≤ 1) :
    Summable fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2 := by
  have hs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr
      ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    simpa using this
  refine Summable.of_norm_bounded hs fun n => ?_
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2)]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg x) hx) (by positivity)

/-- **Spearman's rho of the AMH copula in dilogarithm form** (Nelsen, Example 5.7):
for `0 < |θ| < 1`,
`ρ = 12 (1 + θ)/θ² · Li₂(θ) − 3 (θ + 12)/θ − 24 (1 − θ)/θ² · log (1 − θ)`. -/
theorem spearmanRho_amh_dilog (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (h0 : θ ≠ 0)
    (habs : |θ| < 1) :
    (amh θ hmin hmax).spearmanRho =
      12 * (1 + θ) / θ ^ 2 * dilogSeries θ - 3 * (θ + 12) / θ -
        24 * (1 - θ) / θ ^ 2 * Real.log (1 - θ) := by
  have hD := (summable_dilogSeries habs.le).hasSum
  have hL := Real.hasSum_pow_div_log_of_abs_lt_one habs
  -- pieces
  have hA : HasSum (fun k : ℕ => θ ^ k / ((k : ℝ) + 1) ^ 2) (θ⁻¹ * dilogSeries θ) := by
    have e : (fun k : ℕ => θ ^ k / ((k : ℝ) + 1) ^ 2) =
        fun k : ℕ => θ⁻¹ * (θ ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
      funext k; rw [pow_succ θ k]; field_simp
    rw [e]
    exact hD.mul_left θ⁻¹
  have hB : HasSum (fun k : ℕ => θ ^ k / ((k : ℝ) + 2) ^ 2)
      ((θ ^ 2)⁻¹ * (dilogSeries θ - θ)) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => θ ^ (n + 1) / ((n : ℝ) + 1) ^ 2) 1).mpr hD
    have h2 := this.mul_left (θ ^ 2)⁻¹
    convert h2 using 1
    · funext k
      have e1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      have e2 : θ ^ (k + 1 + 1) = θ ^ k * θ ^ 2 := by ring
      rw [e1, e2]
      field_simp
    · simp [dilogSeries]
  have hC1 : HasSum (fun k : ℕ => θ ^ k / ((k : ℝ) + 1)) (θ⁻¹ * -Real.log (1 - θ)) := by
    have e : (fun k : ℕ => θ ^ k / ((k : ℝ) + 1)) =
        fun k : ℕ => θ⁻¹ * (θ ^ (k + 1) / ((k : ℝ) + 1)) := by
      funext k; rw [pow_succ θ k]; field_simp
    rw [e]
    exact hL.mul_left θ⁻¹
  have hC2 : HasSum (fun k : ℕ => θ ^ k / ((k : ℝ) + 2))
      ((θ ^ 2)⁻¹ * (-Real.log (1 - θ) - θ)) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => θ ^ (n + 1) / ((n : ℝ) + 1)) 1).mpr hL
    have h2 := this.mul_left (θ ^ 2)⁻¹
    convert h2 using 1
    · funext k
      have e1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
      have e2 : θ ^ (k + 1 + 1) = θ ^ k * θ ^ 2 := by ring
      rw [e1, e2]
      field_simp
    · simp
  have hsum := (hA.add hB).sub ((hC1.sub hC2).mul_left 2)
  have hterm : ∀ k : ℕ, θ ^ k / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2) =
      θ ^ k / ((k : ℝ) + 1) ^ 2 + θ ^ k / ((k : ℝ) + 2) ^ 2 -
        2 * (θ ^ k / ((k : ℝ) + 1) - θ ^ k / ((k : ℝ) + 2)) := by
    intro k
    have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [spearmanRho_amh]
  have hfun : (fun k : ℕ => θ ^ k / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2)) =
      fun k : ℕ => θ ^ k / ((k : ℝ) + 1) ^ 2 + θ ^ k / ((k : ℝ) + 2) ^ 2 -
        2 * (θ ^ k / ((k : ℝ) + 1) - θ ^ k / ((k : ℝ) + 2)) := funext hterm
  rw [hfun, hsum.tsum_eq]
  field_simp
  ring

end ProbabilityTheory.Copula
