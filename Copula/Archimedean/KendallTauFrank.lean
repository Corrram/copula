/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTau
import Copula.Families.Frank

/-! # Kendall's tau of the Frank family as an elementary integral

For Frank's family (Nelsen, *An Introduction to Copulas*, second edition, family 4.2.5) with
`θ > 0`, Nelsen's Corollary 5.1.4 gives
`τ = 1 + (4/θ) ∫₀¹ (e^{θt} − 1) log((1 − e^{−θt}) / (1 − e^{−θ})) dt` (`kendallTau_frank`).
Nelsen writes this through the Debye function as `τ = 1 − (4/θ)(1 − D₁(θ))`; the passage to the
Debye form (an integration by parts and a substitution) is not formalized here.

The inverse generator `ψ(s) = −log(1 − (1 − e^{−θ}) e^{−s}) / θ` is strict and smooth
(`isC1_frankGenerator`).
-/

open MeasureTheory Set Filter
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The derivative of Frank's inverse generator. -/
noncomputable def frankGeneratorDeriv (θ : ℝ) (s : ℝ) : ℝ :=
  -((1 - Real.exp (-θ)) * Real.exp (-s)) / (θ * (1 - (1 - Real.exp (-θ)) * Real.exp (-s)))

private theorem frank_base_pos' {θ : ℝ} (hθ : 0 < θ) {s : ℝ} (hs : 0 ≤ s) :
    0 < 1 - (1 - Real.exp (-θ)) * Real.exp (-s) := by
  have h1 : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ)
  have h2 := Real.exp_pos (-θ)
  have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs)
  have hep := Real.exp_pos (-s)
  nlinarith

/-- Frank's inverse generator is continuously differentiable on `(0, ∞)`. -/
theorem isC1_frankGenerator (θ : ℝ) (hθ : 0 < θ) :
    (frankGenerator θ hθ).IsC1 (frankGeneratorDeriv θ) := by
  refine BivariateGenerator.IsC1.of_isStrict (fun s hs => ?_) ?_
  · have hb := (frank_base_pos' hθ hs.le).ne'
    have h := (((((hasDerivAt_id' s).neg.exp).const_mul (1 - Real.exp (-θ))).const_sub 1).log
      hb).neg.div_const θ
    refine h.congr_deriv ?_
    simp only [frankGeneratorDeriv, Pi.neg_apply]
    field_simp
  · apply ContinuousOn.div
    · exact (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).neg.continuousOn
    · exact (continuous_const.mul (continuous_const.sub
        (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))).continuousOn
    · intro s hs
      exact mul_ne_zero hθ.ne' (frank_base_pos' hθ (le_of_lt hs)).ne'

/-- Nelsen, Corollary 5.1.4 for Frank's family:
`τ = 1 + (4/θ) ∫₀¹ (e^{θt} − 1) log((1 − e^{−θt}) / (1 − e^{−θ})) dt`. -/
theorem kendallTau_frank (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).kendallTau = 1 + 4 / θ * ∫ t in (0 : ℝ)..1,
      (Real.exp (θ * t) - 1) * Real.log ((1 - Real.exp (-(θ * t))) / (1 - Real.exp (-θ))) := by
  rw [frank, (isC1_frankGenerator θ hθ).kendallTau_eq]
  have hp : 0 < 1 - Real.exp (-θ) := by
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ); linarith
  have hident : ∀ t ∈ uIoc (0 : ℝ) 1,
      (frankGenerator θ hθ).invFunReal t *
        frankGeneratorDeriv θ ((frankGenerator θ hθ).invFunReal t) =
      θ⁻¹ * ((Real.exp (θ * t) - 1) *
        Real.log ((1 - Real.exp (-(θ * t))) / (1 - Real.exp (-θ)))) := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    set X := (1 - Real.exp (-(θ * t))) / (1 - Real.exp (-θ)) with hX
    have hφ : (frankGenerator θ hθ).invFunReal t = -Real.log X := by
      have h := (frankGenerator θ hθ).invFunReal_coe ⟨t, ht.1.le, ht.2⟩
      rw [h]
      change -Real.log ((1 - Real.exp (-θ * t)) / (1 - Real.exp (-θ))) = _
      rw [neg_mul]
    have hq : 0 < 1 - Real.exp (-(θ * t)) := by
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hθ ht.1)); linarith
    have hXpos : 0 < X := div_pos hq hp
    have hpX : (1 - Real.exp (-θ)) * X = 1 - Real.exp (-(θ * t)) := by
      rw [hX]; field_simp
    have hE : Real.exp (θ * t) * Real.exp (-(θ * t)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hEpos := Real.exp_pos (-(θ * t))
    rw [hφ, frankGeneratorDeriv, neg_neg, Real.exp_log hXpos, hpX,
      show 1 - (1 - Real.exp (-(θ * t))) = Real.exp (-(θ * t)) by ring]
    field_simp
    linear_combination (-(Real.log X)) * hE
  rw [intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => hident t ht),
    intervalIntegral.integral_const_mul]
  ring

end ProbabilityTheory.Copula
