/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTau
import Copula.Archimedean.Clayton
import Copula.Families.Gumbel
import Copula.Families.Nelsen
import Copula.Rank.Benchmarks

/-! # Kendall's tau of Archimedean families

Applications of Nelsen's Corollary 5.1.4 (`BivariateGenerator.IsC1.kendallTau_eq`),
see Nelsen, *An Introduction to Copulas*, second edition, Section 5.1.1 and Table 4.1:

* Clayton (family 4.2.1), `θ > 0`: `τ = θ / (θ + 2)` (`kendallTau_clayton`);
* Gumbel–Hougaard (family 4.2.4), `θ ≥ 1`: `τ = 1 − 1/θ` (`kendallTau_gumbel`);
* BB1 (the outer power `φ^δ` of Clayton's generator, Nelsen Section 4.5):
  `τ = 1 − 2 / (δ (θ + 2))` (`kendallTau_bb1`), via `τ_{φ^δ} = 1 + (τ_φ − 1)/δ`;
* Nelsen's families 4.2.12 and 4.2.14 (subfamilies of BB1): `τ = 1 − 2/(3θ)`
  (`kendallTau_nelsen12`) and `τ = (2θ − 1)/(2θ + 1)` (`kendallTau_nelsen14`);
* the non-strict family 4.2.2 (outer powers of the generator of `W`): `τ = 1 − 2/θ`
  (`kendallTau_nelsen2`).

Both generators are strict with continuously differentiable inverse generators
(`isC1_claytonGenerator`, `isC1_gumbelGenerator`), and the integrands `φ/φ'`
are elementary: `−(t − t^{θ+1})/θ` for Clayton and `t log t / θ` for Gumbel.
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- `∫₀¹ t log t dt = −1/4`. -/
theorem integral_mul_log_unit : (∫ x in (0 : ℝ)..1, x * Real.log x) = -1 / 4 := by
  let F : ℝ → ℝ := fun x => x * (x * Real.log x) / 2 - x ^ 2 / 4
  have hcont : ContinuousOn F (Icc 0 1) :=
    ((continuous_id.mul Real.continuous_mul_log).div_const 2 |>.sub
      ((continuous_pow 2).div_const 4)).continuousOn
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (x * Real.log x) x := by
    intro x hx
    have h : HasDerivAt (fun y => y * (y * Real.log y) / 2 - y ^ 2 / 4)
        ((1 * (x * Real.log x) + x * (Real.log x + 1)) / 2 - ((2 : ℕ) * x ^ (2 - 1)) / 4) x :=
      (((hasDerivAt_id' x).mul (Real.hasDerivAt_mul_log hx.1.ne')).div_const 2).sub
        ((hasDerivAt_pow 2 x).div_const 4)
    refine h.congr_deriv ?_
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    (Real.continuous_mul_log.intervalIntegrable 0 1)]
  simp [F]
  norm_num

/-- The derivative of Clayton's inverse generator `(1 + s)^(-1/θ)`. -/
noncomputable def claytonGeneratorDeriv (θ : ℝ) (s : ℝ) : ℝ := -θ⁻¹ * (1 + s) ^ (-θ⁻¹ - 1)

/-- Clayton's inverse generator is continuously differentiable on `(0, ∞)`. -/
theorem isC1_claytonGenerator (θ : ℝ) (hθ : 0 < θ) :
    (claytonGenerator θ hθ).IsC1 (claytonGeneratorDeriv θ) := by
  refine BivariateGenerator.IsC1.of_isStrict (fun s hs => ?_) ?_
  · have h : HasDerivAt (fun y : ℝ => (1 + y) ^ (-θ⁻¹)) (1 * -θ⁻¹ * (1 + s) ^ (-θ⁻¹ - 1)) s :=
      ((hasDerivAt_id s).const_add 1).rpow_const (p := -θ⁻¹)
        (Or.inl (ne_of_gt (show (0 : ℝ) < 1 + s by linarith)))
    rw [one_mul] at h
    exact h
  · refine continuousOn_const.mul ?_
    exact (continuousOn_const.add continuousOn_id).rpow_const fun x hx =>
      Or.inl (ne_of_gt (show (0 : ℝ) < 1 + x by linarith [show (0 : ℝ) < x from hx]))

/-- Nelsen, Section 5.1.1: Kendall's tau of the Clayton copula is `θ / (θ + 2)`. -/
theorem kendallTau_clayton (θ : ℝ) (hθ : 0 < θ) : (clayton 2 θ hθ).kendallTau = θ / (θ + 2) := by
  rw [← claytonGenerator_copula θ hθ, (isC1_claytonGenerator θ hθ).kendallTau_eq]
  have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
      (claytonGenerator θ hθ).invFunReal t *
        claytonGeneratorDeriv θ ((claytonGenerator θ hθ).invFunReal t) =
      -θ⁻¹ * (t - t ^ (1 + θ)) := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    let u : I := ⟨t, ht.1.le, ht.2⟩
    have hφ : (claytonGenerator θ hθ).invFunReal t = t ^ (-θ) - 1 :=
      (claytonGenerator θ hθ).invFunReal_coe u
    rw [hφ, claytonGeneratorDeriv, add_sub_cancel, ← Real.rpow_mul ht.1.le,
      show -θ * (-θ⁻¹ - 1) = 1 + θ by field_simp; ring]
    have hmul : t ^ (-θ) * t ^ (1 + θ) = t := by
      rw [← Real.rpow_add ht.1, show -θ + (1 + θ) = 1 by ring, Real.rpow_one]
    linear_combination -θ⁻¹ * hmul
  rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegral.intervalIntegrable_id
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)),
    integral_id, integral_rpow (Or.inl (by linarith)), Real.one_rpow,
    Real.zero_rpow (by linarith)]
  field_simp
  ring

/-- The derivative of Gumbel's inverse generator `exp(-s^(1/θ))`. -/
noncomputable def gumbelGeneratorDeriv (θ : ℝ) (s : ℝ) : ℝ :=
  Real.exp (-(s ^ θ⁻¹)) * -(θ⁻¹ * s ^ (θ⁻¹ - 1))

/-- Gumbel's inverse generator is continuously differentiable on `(0, ∞)`. -/
theorem isC1_gumbelGenerator (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbelGenerator θ hθ).IsC1 (gumbelGeneratorDeriv θ) := by
  refine BivariateGenerator.IsC1.of_isStrict
    (fun s hs => (Real.hasDerivAt_rpow_const (p := θ⁻¹) (Or.inl hs.ne')).neg.exp) ?_
  have h1 : ContinuousOn (fun s : ℝ => s ^ θ⁻¹) (Ioi 0) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)
  have h2 : ContinuousOn (fun s : ℝ => s ^ (θ⁻¹ - 1)) (Ioi 0) :=
    continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)
  exact (Real.continuous_exp.comp_continuousOn h1.neg).mul (continuousOn_const.mul h2).neg

/-- Nelsen, Section 5.1.1: Kendall's tau of the Gumbel–Hougaard copula is `1 − 1/θ`. -/
theorem kendallTau_gumbel (θ : ℝ) (hθ : 1 ≤ θ) : (gumbel θ hθ).kendallTau = 1 - 1 / θ := by
  have hθ0 : θ ≠ 0 := by linarith
  rw [gumbel, (isC1_gumbelGenerator θ hθ).kendallTau_eq]
  have hint : ∀ t ∈ uIoc (0 : ℝ) 1,
      (gumbelGenerator θ hθ).invFunReal t *
        gumbelGeneratorDeriv θ ((gumbelGenerator θ hθ).invFunReal t) =
      θ⁻¹ * (t * Real.log t) := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    let u : I := ⟨t, ht.1.le, ht.2⟩
    have hφ : (gumbelGenerator θ hθ).invFunReal t = (-Real.log t) ^ θ :=
      (gumbelGenerator θ hθ).invFunReal_coe u
    have hL : 0 ≤ -Real.log t := neg_nonneg.mpr (Real.log_nonpos ht.1.le ht.2)
    rw [hφ, gumbelGeneratorDeriv, Real.rpow_rpow_inv hL hθ0, neg_neg, Real.exp_log ht.1,
      ← Real.rpow_mul hL, show θ * (θ⁻¹ - 1) = 1 - θ by field_simp]
    have hmul : (-Real.log t) ^ θ * (-Real.log t) ^ (1 - θ) = -Real.log t := by
      rw [← Real.rpow_add' hL (by ring_nf; norm_num), show θ + (1 - θ) = 1 by ring,
        Real.rpow_one]
    linear_combination -(θ⁻¹ * t) * hmul
  rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hint t ht),
    intervalIntegral.integral_const_mul, integral_mul_log_unit]
  field_simp
  ring

/-- Kendall's tau of BB1: `τ = 1 − 2 / (δ (θ + 2))`. -/
theorem kendallTau_bb1 (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 1 ≤ δ) :
    (bb1 θ hθ δ hδ).kendallTau = 1 - 2 / (δ * (θ + 2)) := by
  have hδ0 : δ ≠ 0 := by linarith
  have hθ2 : θ + 2 ≠ 0 := by linarith
  rw [bb1, (isC1_claytonGenerator θ hθ).kendallTau_outerPower δ hδ,
    claytonGenerator_copula, kendallTau_clayton]
  field_simp
  ring

/-- Kendall's tau of Nelsen's family 4.2.12: `τ = 1 − 2/(3θ)`. -/
theorem kendallTau_nelsen12 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).kendallTau = 1 - 2 / (3 * θ) := by
  rw [nelsen12, kendallTau_bb1]
  ring

/-- Kendall's tau of Nelsen's family 4.2.14: `τ = (2θ − 1)/(2θ + 1)`. -/
theorem kendallTau_nelsen14 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).kendallTau = (2 * θ - 1) / (2 * θ + 1) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ2 : 2 * θ + 1 ≠ 0 := by linarith
  rw [nelsen14, kendallTau_bb1]
  field_simp
  ring

/-- The non-strict generator `ψ(s) = max(0, 1 − s)` of `W` is `C¹` on `(0, 1)`, where it is
positive. -/
theorem isC1_truncatedLinearGenerator : truncatedLinearGenerator.IsC1 (fun _ => -1) where
  hasDerivAt s _ hpos := by
    have hs1 : s < 1 := by
      by_contra h
      push Not at h
      have : truncatedLinearGenerator.toFun s = 0 := max_eq_left (by linarith)
      linarith
    refine ((hasDerivAt_id s).const_sub 1).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hs1] with y hy
    exact max_eq_right (by simp only [mem_Iio] at hy; linarith)
  continuousAt _ _ _ := continuousAt_const

/-- Kendall's tau of Nelsen's family 4.2.2: `τ = 1 − 2/θ`. -/
theorem kendallTau_nelsen2 (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen2 θ hθ).kendallTau = 1 - 2 / θ := by
  rw [nelsen2, isC1_truncatedLinearGenerator.kendallTau_outerPower θ hθ,
    truncatedLinearGenerator_copula, kendallTau_countermonotonic]
  ring

end ProbabilityTheory.Copula
