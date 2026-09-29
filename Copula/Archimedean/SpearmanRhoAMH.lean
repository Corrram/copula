/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.SpearmanCDF
import Copula.Rank.Integration
import Copula.Families.AMH
import Mathlib.Analysis.PSeries

/-! # Spearman's rho of the Ali--Mikhail--Haq family as a series

For `|θ| ≤ 1` the AMH copula `C(u, v) = u v / (1 - θ (1-u) (1-v))` has the expansion
`C(u, v) = ∑ₖ θᵏ · u(1-u)ᵏ · v(1-v)ᵏ`, and `∫₀¹ t (1-t)ᵏ dt = 1 / ((k+1)(k+2))`. Integrating term
by term gives (Nelsen, *An Introduction to Copulas*, Example 5.7 in dilogarithm form)
`ρ = 12 ∑ₖ θᵏ / ((k+1)² (k+2)²) - 3`, which is the series of the dilogarithm expression.
-/

open MeasureTheory Filter Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace SpearmanAMH

theorem integral_unit_mul_one_sub_pow (k : ℕ) :
    (∫ t : I, (t : ℝ) * (1 - (t : ℝ)) ^ k) = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  rw [integral_unitInterval (fun t : ℝ => t * (1 - t) ^ k)]
  have h := intervalIntegral.integral_comp_sub_left (fun t : ℝ => t * (1 - t) ^ k) (a := 0)
    (b := 1) 1
  simp only [sub_sub_cancel, sub_self, sub_zero] at h
  rw [← h]
  have e : (fun x : ℝ => (1 - x) * x ^ k) = fun x : ℝ => x ^ k - x ^ (k + 1) := by
    funext x; ring
  rw [e, intervalIntegral.integral_sub ((continuous_pow k).intervalIntegrable _ _)
    ((continuous_pow (k + 1)).intervalIntegrable _ _), integral_pow, integral_pow]
  field_simp
  push_cast
  ring


/-- The `k`-th term of the AMH expansion: `θᵏ · u (1-u)ᵏ · v (1-v)ᵏ`. -/
noncomputable def term (θ : ℝ) (k : ℕ) (x : Fin 2 → I) : ℝ :=
  θ ^ k * (((x 0 : ℝ) * (1 - (x 0 : ℝ)) ^ k) * ((x 1 : ℝ) * (1 - (x 1 : ℝ)) ^ k))

theorem g_nonneg (k : ℕ) (t : I) : 0 ≤ (t : ℝ) * (1 - (t : ℝ)) ^ k :=
  mul_nonneg t.property.1 (pow_nonneg (sub_nonneg.mpr t.property.2) k)

theorem hasSum_cdf_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) (a b : I) :
    HasSum (fun k : ℕ => term θ k ![a, b]) ((amh θ hmin hmax).cdf ![a, b]) := by
  rw [cdf_amh]
  by_cases hab : (a : ℝ) = 0 ∨ (b : ℝ) = 0
  · have h0 : (a : ℝ) * b = 0 := by rcases hab with h | h <;> simp [h]
    have : (fun k : ℕ => term θ k ![a, b]) = fun _ => 0 := by
      funext k
      rcases hab with h | h <;> simp [term, h]
    rw [this, h0, zero_div]
    exact hasSum_zero
  · obtain ⟨hab1, -⟩ := not_or.mp hab
    have ha : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (Ne.symm hab1)
    have hb0 : (0 : ℝ) ≤ 1 - b := sub_nonneg.mpr b.property.2
    have hb1 : (1 : ℝ) - b ≤ 1 := by linarith [b.property.1]
    have ha0 : (0 : ℝ) ≤ 1 - a := sub_nonneg.mpr a.property.2
    have hr : |θ * (1 - (a : ℝ)) * (1 - (b : ℝ))| < 1 := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hb0]
      have h1 : |θ| ≤ 1 := abs_le.mpr ⟨hmin, hmax⟩
      have h2 : |θ| * (1 - (a : ℝ)) ≤ 1 - a := by nlinarith
      nlinarith [abs_nonneg θ]
    have hg := (hasSum_geometric_of_abs_lt_one hr).mul_left ((a : ℝ) * b)
    have e : (fun k : ℕ => term θ k ![a, b]) =
        fun k : ℕ => (a : ℝ) * b * (θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) ^ k := by
      funext k
      simp only [term, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_pow, mul_pow]
      ring
    rw [e]
    have e2 : (a : ℝ) * b / (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ))) =
        (a : ℝ) * b * (1 - θ * (1 - (a : ℝ)) * (1 - (b : ℝ)))⁻¹ := div_eq_mul_inv _ _
    rw [e2]
    exact hg

theorem continuous_term (θ : ℝ) (k : ℕ) : Continuous (term θ k) := by
  unfold term
  fun_prop

theorem integral_term (θ : ℝ) (k : ℕ) :
    (∫ x, term θ k x ∂(independence 2).toMeasure) =
      θ ^ k * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2 := by
  unfold term
  rw [integral_const_mul,
    integral_independence_mul (fun t : I => (t : ℝ) * (1 - (t : ℝ)) ^ k)
      (fun t : I => (t : ℝ) * (1 - (t : ℝ)) ^ k), integral_unit_mul_one_sub_pow]
  ring

theorem norm_term (θ : ℝ) (k : ℕ) (x : Fin 2 → I) :
    ‖term θ k x‖ = |θ| ^ k * (((x 0 : ℝ) * (1 - (x 0 : ℝ)) ^ k) *
      ((x 1 : ℝ) * (1 - (x 1 : ℝ)) ^ k)) := by
  unfold term
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_of_nonneg (g_nonneg k (x 0)),
    abs_of_nonneg (g_nonneg k (x 1))]

theorem integral_norm_term (θ : ℝ) (k : ℕ) :
    (∫ x, ‖term θ k x‖ ∂(independence 2).toMeasure) =
      |θ| ^ k * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2 := by
  simp_rw [norm_term]
  rw [integral_const_mul,
    integral_independence_mul (fun t : I => (t : ℝ) * (1 - (t : ℝ)) ^ k)
      (fun t : I => (t : ℝ) * (1 - (t : ℝ)) ^ k), integral_unit_mul_one_sub_pow]
  ring

theorem summable_integral_norm_term (θ : ℝ) (hθ : |θ| ≤ 1) :
    Summable fun k : ℕ => ∫ x, ‖term θ k x‖ ∂(independence 2).toMeasure := by
  simp_rw [integral_norm_term]
  have hs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr
      ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    simpa using this
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hp : |θ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg θ) hθ
  have hd : ((k : ℝ) + 1) ^ 2 ≤ (((k : ℝ) + 1) * ((k : ℝ) + 2)) ^ 2 := by
    apply pow_le_pow_left₀ hk1.le
    nlinarith
  calc |θ| ^ k * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2
      ≤ 1 * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ^ 2 :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) ^ 2 := by rw [one_mul, one_div_pow]
    _ ≤ 1 / ((k : ℝ) + 1) ^ 2 := one_div_le_one_div_of_le (by positivity) hd

end SpearmanAMH

open SpearmanAMH in
/-- Spearman's rho of the AMH copula (`|θ| ≤ 1`) as a convergent series:
`ρ + 3 = ∑ₖ 12 θᵏ / ((k+1)² (k+2)²)`. -/
theorem hasSum_spearmanRho_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    HasSum (fun k : ℕ => 12 * (θ ^ k / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2)))
      ((amh θ hmin hmax).spearmanRho + 3) := by
  have hθ : |θ| ≤ 1 := abs_le.mpr ⟨hmin, hmax⟩
  have h := hasSum_integral_of_summable_integral_norm (μ := (independence 2).toMeasure)
    (F := fun k : ℕ => term θ k)
    (fun k => integrable_continuous_cube _ (continuous_term θ k))
    (summable_integral_norm_term θ hθ)
  have hcdf : (fun x : Fin 2 → I => ∑' k : ℕ, term θ k x) = (amh θ hmin hmax).cdf := by
    funext x
    have hx : x = ![x 0, x 1] := by
      funext i; fin_cases i <;> rfl
    rw [hx]
    exact (hasSum_cdf_amh θ hmin hmax (x 0) (x 1)).tsum_eq
  rw [hcdf] at h
  simp_rw [integral_term] at h
  have h12 := h.mul_left 12
  rw [(amh θ hmin hmax).spearmanRho_eq_integral_cdf]
  convert h12 using 1
  · funext k
    rw [one_div_pow, mul_pow]
    ring
  · ring

/-- Spearman's rho of the AMH copula (`|θ| ≤ 1`):
`ρ = 12 ∑ₖ θᵏ / ((k+1)² (k+2)²) - 3`. -/
theorem spearmanRho_amh (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (amh θ hmin hmax).spearmanRho =
      12 * (∑' k : ℕ, θ ^ k / (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) ^ 2)) - 3 := by
  have h := (hasSum_spearmanRho_amh θ hmin hmax).tsum_eq
  rw [tsum_mul_left] at h
  linarith


end ProbabilityTheory.Copula
