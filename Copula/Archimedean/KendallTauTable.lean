/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTauGenerator
import Copula.Families.Clayton.Negative
import Copula.Families.Nelsen
import Copula.Families.Nelsen7
import Copula.Families.Nelsen8
import Copula.Families.NelsenTable.N18
import Copula.Families.NelsenTable.N16
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Copula.Rank.Benchmarks

/-! # Kendall's tau of further families of Nelsen's Table 4.1

Applications of Nelsen's Corollary 5.1.4, `τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt`
(`BivariateGenerator.kendallTau_eq_of_hasDerivAt`), to the families of Nelsen, *An Introduction
to Copulas*, second edition, Table 4.1 whose Kendall integrand is elementary:

* family 4.2.1 (Clayton) on its negative range `−1 ≤ θ < 0`: `τ = θ / (θ + 2)`
  (`kendallTau_claytonNegative`), completing `kendallTau_clayton` for `θ > 0`;
* family 4.2.7, `0 < θ ≤ 1`: `τ = 2 − 2/θ − 2 (1 − θ)² log(1 − θ) / θ²` (`kendallTau_nelsen7`;
  `θ = 1` is independence, with `0 · log 0 = 0`), and `τ = −1` at `θ = 0` (`W`);
* family 4.2.8, `θ ≥ 1`: `τ = (θ − 4) / (3θ)` (`kendallTau_nelsen8`);
* family 4.2.15 (Genest–Ghoudi), `θ ≥ 1`: `τ = (2θ − 3) / (2θ − 1)` (`kendallTau_genestGhoudi`);
* family 4.2.18, `θ ≥ 2`: `τ = 1 − 4 / (3θ)` (`kendallTau_nelsen18`).

The integrands are `(t^{θ+1} − t)/θ` (Clayton, `θ < 0`),
`(θt + 1 − θ) log(θt + 1 − θ) / θ` (#7), `−(1 − t)(1 + (θ − 1)t)/θ` (#8),
`−(t^{1 − 1/θ} − t)` (#15) and `−(t − 1)²/θ` (#18). All five generators except #1 with `θ = −1`
limits are non-strict; `kendallTau_eq_of_hasDerivAt` covers strict and non-strict generators alike.
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace KendallTauTable

/-- The real extension of a generator at an interior point is its value there. -/
theorem invFunReal_of_mem (g : BivariateGenerator) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    g.invFunReal t = g.invFun ⟨t, ht.1.le, ht.2.le⟩ := by
  rw [BivariateGenerator.invFunReal, projIcc_of_mem _ ⟨ht.1.le, ht.2.le⟩]

end KendallTauTable

open KendallTauTable

/-! ### Clayton, negative parameters -/

/-- Nelsen, Table 4.1 / Section 5.1.1: Kendall's tau of the Clayton copula for `−1 ≤ θ < 0` is
`θ / (θ + 2)`. -/
theorem kendallTau_claytonNegative (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).kendallTau = θ / (θ + 2) := by
  have hθ0 : θ ≠ 0 := hn.ne
  have hθ2 : θ + 2 ≠ 0 := by linarith
  rw [claytonNegative, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => 1 - t ^ (-θ)) (φ' := fun t => θ * t ^ (-θ - 1))]
  · have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
        (1 - t ^ (-θ)) / (θ * t ^ (-θ - 1)) = θ⁻¹ * (t ^ (θ + 1) - t) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have hp : 0 < t ^ (-θ - 1) := Real.rpow_pos_of_pos ht.1 _
      have h1 : t ^ (θ + 1) * t ^ (-θ - 1) = 1 := by
        rw [← Real.rpow_add ht.1, show θ + 1 + (-θ - 1) = 0 by ring, Real.rpow_zero]
      have h2 : t * t ^ (-θ - 1) = t ^ (-θ) := by
        conv_lhs => rw [show t * t ^ (-θ - 1) = t ^ (1 : ℝ) * t ^ (-θ - 1) by rw [Real.rpow_one]]
        rw [← Real.rpow_add ht.1, show 1 + (-θ - 1) = -θ by ring]
      have h3 : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ0
      rw [div_eq_iff (mul_ne_zero hθ0 hp.ne')]
      linear_combination (-1 : ℝ) * h1 + h2 -
        (t ^ (θ + 1) * t ^ (-θ - 1) - t * t ^ (-θ - 1)) * h3
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
        intervalIntegral.intervalIntegrable_id,
      integral_id, integral_rpow (Or.inl (by linarith)), Real.one_rpow,
      Real.zero_rpow (by linarith)]
    have hθ3 : θ + 1 + 1 ≠ 0 := by linarith
    field_simp
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    simp [BivariateGenerator.innerPower, truncatedLinearGenerator]
  · intro t ht
    have h := ((Real.hasDerivAt_rpow_const (p := -θ) (Or.inl ht.1.ne')).const_sub 1)
    refine h.congr_deriv ?_
    ring
  · exact continuousOn_const.mul
      (continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne')
  · intro t ht
    exact mul_ne_zero hθ0 (Real.rpow_pos_of_pos ht.1 _).ne'

/-! ### Family 4.2.8 -/

/-- Nelsen, Table 4.1, family 8 (`θ ≥ 1`): `τ = (θ − 4) / (3θ)`. -/
theorem kendallTau_nelsen8 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen8 θ hθ).kendallTau = (θ - 4) / (3 * θ) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hden : ∀ t : ℝ, 0 ≤ t → 0 < 1 + (θ - 1) * t := fun t ht => by nlinarith
  rw [nelsen8, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => (1 - t) / (1 + (θ - 1) * t)) (φ' := fun t => -θ / (1 + (θ - 1) * t) ^ 2)]
  · have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
        (1 - t) / (1 + (θ - 1) * t) / (-θ / (1 + (θ - 1) * t) ^ 2) =
          -θ⁻¹ * (1 + (θ - 2) * t - (θ - 1) * t ^ 2) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have hd := (hden t ht.1.le).ne'
      field_simp
      ring
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
      intervalIntegral.integral_const_mul]
    have hP : ∫ t in (0 : ℝ)..1, (1 + (θ - 2) * t - (θ - 1) * t ^ 2) = (θ + 2) / 6 := by
      have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
          (fun t : ℝ => t + (θ - 2) * (t ^ 2 / 2) - (θ - 1) * (t ^ 3 / 3))
          (1 + (θ - 2) * x - (θ - 1) * x ^ 2) x := by
        intro x _
        have h := (((hasDerivAt_id' x).add (((hasDerivAt_pow 2 x).div_const 2).const_mul
          (θ - 2))).sub (((hasDerivAt_pow 3 x).div_const 3).const_mul (θ - 1)))
        refine h.congr_deriv ?_
        push_cast
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (by apply Continuous.intervalIntegrable; fun_prop)]
      ring
    rw [hP]
    field_simp
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have hd := (hden t ht.1.le).ne'
    have h1 : HasDerivAt (fun t : ℝ => 1 + (θ - 1) * t) (θ - 1) t := by
      simpa using ((hasDerivAt_id t).const_mul (θ - 1)).const_add 1
    have h := ((hasDerivAt_id t).const_sub 1).div h1 hd
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (hden t ht.1.le).ne'
  · intro t ht
    exact div_ne_zero (neg_ne_zero.mpr hθ0) (pow_ne_zero 2 (hden t ht.1.le).ne')

/-! ### Family 4.2.18 -/

/-- Nelsen, Table 4.1, family 18 (`θ ≥ 2`): `τ = 1 − 4 / (3θ)`. -/
theorem kendallTau_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) :
    (nelsen18 θ hθ).kendallTau = 1 - 4 / (3 * θ) := by
  have hθ0 : θ ≠ 0 := by linarith
  rw [nelsen18, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => Real.exp (θ / (t - 1)))
    (φ' := fun t => Real.exp (θ / (t - 1)) * (-θ / (t - 1) ^ 2))]
  · have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
        Real.exp (θ / (t - 1)) / (Real.exp (θ / (t - 1)) * (-θ / (t - 1) ^ 2)) =
          -θ⁻¹ * (t - 1) ^ 2 := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      rcases ht.2.lt_or_eq with h1 | h1
      · have hd : t - 1 ≠ 0 := by linarith
        have he := (Real.exp_pos (θ / (t - 1))).ne'
        field_simp
      · subst h1
        simp
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
        (fun x => x ^ 2), integral_pow]
    field_simp
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    have h1 : (⟨t, ht.1.le, ht.2.le⟩ : I) ≠ 1 := fun h => ht.2.ne (congrArg Subtype.val h)
    change nelsen18Phi θ _ = _
    simp [nelsen18Phi, h1]
  · intro t ht
    have hd : t - 1 ≠ 0 := by linarith [ht.2]
    have h := (((hasDerivAt_id t).sub_const 1).inv hd).const_mul θ |>.exp
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · simp only [Pi.inv_apply, id]
      field_simp
    · simp only [Pi.inv_apply, id, div_eq_mul_inv]
  · apply ContinuousOn.mul
    · exact Real.continuous_exp.comp_continuousOn
        (continuousOn_const.div (by fun_prop) fun t ht => by linarith [ht.2])
    · exact continuousOn_const.div (by fun_prop) fun t ht =>
        pow_ne_zero 2 (by linarith [ht.2])
  · intro t ht
    have hd : t - 1 ≠ 0 := by linarith [ht.2]
    exact mul_ne_zero (Real.exp_pos _).ne' (div_ne_zero (neg_ne_zero.mpr hθ0) (pow_ne_zero 2 hd))

/-! ### Family 4.2.7 -/

/-- `∫_a^b y log y dy = F(b) − F(a)` with `F(y) = y² log y / 2 − y² / 4`, for `0 ≤ a ≤ b`. -/
theorem integral_mul_log_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ y in a..b, y * Real.log y) =
      (b * (b * Real.log b) / 2 - b ^ 2 / 4) - (a * (a * Real.log a) / 2 - a ^ 2 / 4) := by
  let F : ℝ → ℝ := fun x => x * (x * Real.log x) / 2 - x ^ 2 / 4
  have hcont : ContinuousOn F (Icc a b) :=
    ((continuous_id.mul Real.continuous_mul_log).div_const 2 |>.sub
      ((continuous_pow 2).div_const 4)).continuousOn
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (x * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (ha.trans_lt hx.1).ne'
    have h : HasDerivAt (fun y => y * (y * Real.log y) / 2 - y ^ 2 / 4)
        ((1 * (x * Real.log x) + x * (Real.log x + 1)) / 2 - ((2 : ℕ) * x ^ (2 - 1)) / 4) x :=
      (((hasDerivAt_id' x).mul (Real.hasDerivAt_mul_log hx0)).div_const 2).sub
        ((hasDerivAt_pow 2 x).div_const 4)
    refine h.congr_deriv ?_
    push_cast
    ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
    (Real.continuous_mul_log.intervalIntegrable a b)

/-- Nelsen, Table 4.1, family 7 (`0 < θ ≤ 1`):
`τ = 2 − 2/θ − 2 (1 − θ)² log(1 − θ) / θ²` (at `θ = 1`, independence, this is `0`). -/
theorem kendallTau_nelsen7 (θ : I) (hθ : θ ≠ 0) :
    (nelsen7 θ).kendallTau =
      2 - 2 / (θ : ℝ) - 2 * (1 - (θ : ℝ)) ^ 2 * Real.log (1 - (θ : ℝ)) / (θ : ℝ) ^ 2 := by
  set a : ℝ := (θ : ℝ) with ha_def
  have ha : 0 < a := lt_of_le_of_ne θ.property.1 (Ne.symm (fun hz => hθ (Subtype.ext hz)))
  have ha1 : a ≤ 1 := θ.property.2
  have hpos : ∀ t : ℝ, 0 < t → 0 < a * t + 1 - a := fun t ht => by nlinarith [mul_pos ha ht]
  unfold nelsen7
  rw [dite_eq_right_of_eq_false (eq_false hθ), BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => -Real.log (a * t + 1 - a)) (φ' := fun t => -a / (a * t + 1 - a))]
  · have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
        -Real.log (a * t + 1 - a) / (-a / (a * t + 1 - a)) =
          a⁻¹ * ((a * t + (1 - a)) * Real.log (a * t + (1 - a))) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have hp := (hpos t ht.1).ne'
      rw [show a * t + (1 - a) = a * t + 1 - a by ring]
      field_simp
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_add (fun y => y * Real.log y) ha.ne' (1 - a),
      mul_zero, zero_add, mul_one, show a + (1 - a) = 1 by ring,
      integral_mul_log_of_nonneg (by linarith) (by linarith), Real.log_one, smul_eq_mul]
    field_simp
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have hp := (hpos t ht.1).ne'
    have h1 : HasDerivAt (fun t : ℝ => a * t + 1 - a) a t := by
      simpa using (((hasDerivAt_id t).const_mul a).add_const 1).sub_const a
    exact (h1.log hp).neg.congr_deriv (by rw [neg_div])
  · exact continuousOn_const.div (by fun_prop) fun t ht => (hpos t ht.1).ne'
  · intro t ht
    exact div_ne_zero (neg_ne_zero.mpr ha.ne') (hpos t ht.1).ne'

/-- Family 7 at `θ = 0` is `W`, with `τ = −1`. -/
theorem kendallTau_nelsen7_zero : (nelsen7 0).kendallTau = -1 := by
  rw [nelsen7_zero, kendallTau_countermonotonic]

/-! ### Family 4.2.15 (Genest–Ghoudi) -/

/-- Nelsen, Table 4.1, family 15 (Genest–Ghoudi, `θ ≥ 1`): `τ = (2θ − 3) / (2θ − 1)`. -/
theorem kendallTau_genestGhoudi (θ : ℝ) (hθ : 1 ≤ θ) :
    (genestGhoudi θ hθ).kendallTau = (2 * θ - 3) / (2 * θ - 1) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hp0 : 0 < θ⁻¹ := inv_pos.mpr (by linarith)
  have hp1 : θ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hθ
  have hb : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - t ^ θ⁻¹ := fun t ht => by
    have := Real.rpow_lt_one ht.1.le ht.2 hp0
    linarith
  rw [genestGhoudi, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => (1 - t ^ θ⁻¹) ^ θ)
    (φ' := fun t => -((1 - t ^ θ⁻¹) ^ (θ - 1) * t ^ (θ⁻¹ - 1)))]
  · have hint : ∀ t ∈ Ioo (0 : ℝ) 1,
        (1 - t ^ θ⁻¹) ^ θ / -((1 - t ^ θ⁻¹) ^ (θ - 1) * t ^ (θ⁻¹ - 1)) =
          -(t ^ (1 - θ⁻¹) - t) := by
      intro t ht
      have hbt := hb t ht
      have h1 : (1 - t ^ θ⁻¹) ^ θ = (1 - t ^ θ⁻¹) * (1 - t ^ θ⁻¹) ^ (θ - 1) := by
        have he : (1 - t ^ θ⁻¹) ^ θ = (1 - t ^ θ⁻¹) ^ ((1 : ℝ) + (θ - 1)) := by
          congr 1; ring
        rw [he, Real.rpow_add hbt, Real.rpow_one]
      have h2 : t ^ (θ⁻¹ - 1) * t ^ (1 - θ⁻¹) = 1 := by
        rw [← Real.rpow_add ht.1, show θ⁻¹ - 1 + (1 - θ⁻¹) = 0 by ring, Real.rpow_zero]
      have h3 : t ^ θ⁻¹ * t ^ (1 - θ⁻¹) = t := by
        rw [← Real.rpow_add ht.1, show θ⁻¹ + (1 - θ⁻¹) = 1 by ring, Real.rpow_one]
      have hq := (Real.rpow_pos_of_pos hbt (θ - 1)).ne'
      have hr := (Real.rpow_pos_of_pos ht.1 (θ⁻¹ - 1)).ne'
      rw [div_eq_iff (neg_ne_zero.mpr (mul_ne_zero hq hr)), h1]
      linear_combination (-((1 - t ^ θ⁻¹) * (1 - t ^ θ⁻¹) ^ (θ - 1))) * h2 -
        ((1 - t ^ θ⁻¹) ^ (θ - 1) * t ^ (θ⁻¹ - 1)) * h3
    have hI : (∫ t in (0 : ℝ)..1, (1 - t ^ θ⁻¹) ^ θ / -((1 - t ^ θ⁻¹) ^ (θ - 1) * t ^ (θ⁻¹ - 1))) =
        ∫ t in (0 : ℝ)..1, -(t ^ (1 - θ⁻¹) - t) := by
      rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_congr_fun measurableSet_Ioo fun t ht => hint t ht
    rw [hI, intervalIntegral.integral_neg, intervalIntegral.integral_sub
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
        intervalIntegral.intervalIntegrable_id,
      integral_id, integral_rpow (Or.inl (by linarith)), Real.one_rpow,
      Real.zero_rpow (by linarith)]
    have h2θ : 2 * θ - 1 ≠ 0 := by linarith
    have h4 : 1 - θ⁻¹ + 1 ≠ 0 := by linarith
    rw [show (1 : ℝ) - θ⁻¹ + 1 = (2 * θ - 1) / θ by field_simp; ring]
    field_simp
    ring
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    simp [BivariateGenerator.innerPower, BivariateGenerator.outerPower, truncatedLinearGenerator]
  · intro t ht
    have hbt := hb t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 - t ^ θ⁻¹) (-(θ⁻¹ * t ^ (θ⁻¹ - 1))) t :=
      (Real.hasDerivAt_rpow_const (p := θ⁻¹) (Or.inl ht.1.ne')).const_sub 1
    have h := h1.rpow_const (p := θ) (Or.inr hθ)
    refine h.congr_deriv ?_
    field_simp
  · apply ContinuousOn.neg
    apply ContinuousOn.mul
    · exact (continuousOn_const.sub
        (continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne')).rpow_const
        fun x hx => Or.inl (hb x hx).ne'
    · exact continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne'
  · intro t ht
    exact neg_ne_zero.mpr (mul_ne_zero (Real.rpow_pos_of_pos (hb t ht) _).ne'
      (Real.rpow_pos_of_pos ht.1 _).ne')

/-! ### Family 4.2.16 -/

/-- An antiderivative of the (negated) Kendall integrand of family 16. -/
private noncomputable def n16F (θ t : ℝ) : ℝ :=
  (1 - θ) * t - t ^ 2 / 2 + θ * Real.log (t ^ 2 + θ) - (1 - θ) * √θ * Real.arctan (t / √θ)

private theorem n16F_hasDerivAt {θ : ℝ} (hθ : 0 < θ) (t : ℝ) :
    HasDerivAt (n16F θ) ((1 - θ) - t + (2 * θ * t - θ * (1 - θ)) / (t ^ 2 + θ)) t := by
  have hq : 0 < t ^ 2 + θ := by positivity
  have hs : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hsq : √θ * √θ = θ := Real.mul_self_sqrt hθ.le
  have h1 := (hasDerivAt_id t).const_mul (1 - θ)
  have h2 := (hasDerivAt_pow 2 t).div_const 2
  have h3 := (((hasDerivAt_pow 2 t).add_const θ).log hq.ne').const_mul θ
  have h4 := (((hasDerivAt_id t).div_const √θ).arctan).const_mul ((1 - θ) * √θ)
  have h := ((h1.sub h2).add h3).sub h4
  refine h.congr_deriv ?_
  simp only [id]
  have hq' : 1 + (t / √θ) ^ 2 = (t ^ 2 + θ) / θ := by
    field_simp
    rw [Real.sq_sqrt hθ.le]
    ring
  rw [hq']
  field_simp
  push_cast
  ring_nf

/-- Nelsen, Table 4.1, family 16 (`θ > 0`):
`τ = 4θ − 1 − 4θ log((1 + θ)/θ) + 4 (1 − θ) √θ arctan(1/√θ)`
(at `θ = 0` the family is `W` with `τ = −1`). -/
theorem kendallTau_nelsen16 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen16 θ hθ.le).kendallTau =
      4 * θ - 1 - 4 * θ * Real.log ((1 + θ) / θ) + 4 * (1 - θ) * √θ * Real.arctan (1 / √θ) := by
  have hq : ∀ t : ℝ, 0 < t ^ 2 + θ := fun t => by positivity
  rw [nelsen16, BivariateGenerator.kendallTau_eq_of_hasDerivAt
    (φ := fun t => (θ / t + 1) * (1 - t)) (φ' := fun t => -θ / t ^ 2 - 1)]
  · have hint : ∀ t ∈ uIoc (0 : ℝ) 1, (θ / t + 1) * (1 - t) / (-θ / t ^ 2 - 1) =
        -((1 - θ) - t + (2 * θ * t - θ * (1 - θ)) / (t ^ 2 + θ)) := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht0 := ht.1.ne'
      have hd : -θ / t ^ 2 - 1 ≠ 0 := by
        have : 0 < θ / t ^ 2 := by positivity
        rw [neg_div]
        linarith
      have hq0 := (hq t).ne'
      rw [div_eq_iff hd]
      field_simp
      ring
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
      intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => n16F_hasDerivAt hθ t)
        (by
          apply Continuous.intervalIntegrable
          exact (continuous_const.sub continuous_id).add
            ((continuous_const.mul continuous_id).sub continuous_const |>.div
              ((continuous_pow 2).add continuous_const) fun t => (hq t).ne'))]
    simp only [n16F]
    have hθ1 : Real.log (1 + θ) - Real.log θ = Real.log ((1 + θ) / θ) :=
      (Real.log_div (by linarith) hθ.ne').symm
    norm_num
    rw [← hθ1, show (1 : ℝ) + θ = θ + 1 by ring] at *
    ring_nf
  · intro t ht
    rw [invFunReal_of_mem _ ht]
    rfl
  · intro t ht
    have ht0 := ht.1.ne'
    have h := (((hasDerivAt_inv ht0).const_mul θ).add_const 1).mul
      ((hasDerivAt_id' t).const_sub 1)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
    · field_simp
      ring
    · simp only [div_eq_mul_inv, Pi.mul_apply]
  · exact (continuousOn_const.div (by fun_prop) fun t ht => pow_ne_zero 2 ht.1.ne').sub
      continuousOn_const
  · intro t ht
    have : 0 < θ / t ^ 2 := div_pos hθ (pow_pos ht.1 2)
    have h' : -θ / t ^ 2 - 1 < 0 := by rw [neg_div]; linarith
    exact h'.ne

end ProbabilityTheory.Copula
