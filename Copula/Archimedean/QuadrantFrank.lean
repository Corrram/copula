/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantLogConvex
import Copula.Families.FrankNegative

/-! # Quadrant dependence of Frank's family (Nelsen's family 5)

* `isPQD_frank`, `not_isNQD_frank`: for `θ > 0`, Frank's copula is PQD and not NQD;
* `isNQD_frankNegative`, `not_isPQD_frankNegative`: for `θ < 0` it is NQD and not PQD.

The inverse generator `ψ(t) = -log(1 - (1 - e^{-θ}) e^{-t}) / θ` is strictly log-convex,
because with `w = (1 - e^{-θ}) e^{-t}` one has `θ² (ψ ψ'' - ψ'²) = w (-log(1 - w) - w) / (1 - w)² > 0`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace FrankQuadrant

variable {θ : ℝ}

private theorem a_pos (hθ : 0 < θ) : 0 < 1 - Real.exp (-θ) := by
  have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hθ); linarith

private theorem w_lt_one (hθ : 0 < θ) {t : ℝ} (ht : 0 ≤ t) :
    (1 - Real.exp (-θ)) * Real.exp (-t) < 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have h2 := Real.exp_pos (-θ)
  have := a_pos hθ
  nlinarith [Real.exp_pos (-t)]

private theorem hasDerivAt_w (a t : ℝ) :
    HasDerivAt (fun t => a * Real.exp (-t)) (-(a * Real.exp (-t))) t := by
  have := (hasDerivAt_id t).neg.exp.const_mul a
  refine this.congr_deriv ?_
  simp

private theorem hasDerivAt_psi (hθ : 0 < θ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -Real.log (1 - (1 - Real.exp (-θ)) * Real.exp (-t)) / θ)
      (-((1 - Real.exp (-θ)) * Real.exp (-t)) /
        (θ * (1 - (1 - Real.exp (-θ)) * Real.exp (-t)))) t := by
  have hb : 1 - (1 - Real.exp (-θ)) * Real.exp (-t) ≠ 0 :=
    (sub_pos.mpr (w_lt_one hθ ht.le)).ne'
  have h := (((hasDerivAt_w (1 - Real.exp (-θ)) t).const_sub 1).log hb).neg.div_const θ
  refine h.congr_deriv ?_
  field_simp

private theorem hasDerivAt_psi1 (hθ : 0 < θ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -((1 - Real.exp (-θ)) * Real.exp (-t)) /
        (θ * (1 - (1 - Real.exp (-θ)) * Real.exp (-t))))
      (((1 - Real.exp (-θ)) * Real.exp (-t)) /
        (θ * (1 - (1 - Real.exp (-θ)) * Real.exp (-t)) ^ 2)) t := by
  have hb : 1 - (1 - Real.exp (-θ)) * Real.exp (-t) ≠ 0 :=
    (sub_pos.mpr (w_lt_one hθ ht.le)).ne'
  have hw := hasDerivAt_w (1 - Real.exp (-θ)) t
  have h := hw.neg.div ((hw.const_sub 1).const_mul θ) (mul_ne_zero hθ.ne' hb)
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  field_simp
  ring

/-- Frank's inverse generator is positive on `[0, ∞)`. -/
theorem toFun_pos (hθ : 0 < θ) : ∀ t, 0 ≤ t → 0 < (frankGenerator θ hθ).toFun t := by
  intro t ht
  show 0 < -Real.log (1 - (1 - Real.exp (-θ)) * Real.exp (-t)) / θ
  apply div_pos _ hθ
  apply neg_pos.mpr
  apply Real.log_neg
  · have := a_pos hθ
    have := Real.exp_pos (-t)
    have := w_lt_one hθ ht
    positivity
  · have := a_pos hθ
    have := Real.exp_pos (-t)
    nlinarith

/-- Frank's generator is strictly log-convex. -/
theorem strictConvexOn_log (hθ : 0 < θ) :
    StrictConvexOn ℝ (Ici 0) (fun t => Real.log ((frankGenerator θ hθ).toFun t)) := by
  have hpos := toFun_pos hθ
  refine strictConvexOn_log_of_derivs hpos ?_ (fun t ht => hasDerivAt_psi hθ ht)
    (fun t ht => hasDerivAt_psi1 hθ ht) ?_
  · exact (((continuousOn_const.sub (continuousOn_const.mul
      (Real.continuous_exp.comp continuous_neg).continuousOn)).log (fun t ht =>
        (sub_pos.mpr (w_lt_one hθ (mem_Ici.mp ht))).ne')).neg.div_const θ)
  · intro t ht
    have hw0 : 0 < (1 - Real.exp (-θ)) * Real.exp (-t) :=
      mul_pos (a_pos hθ) (Real.exp_pos _)
    have hw1 := w_lt_one hθ ht.le
    set w := (1 - Real.exp (-θ)) * Real.exp (-t) with hw
    have hb : 0 < 1 - w := sub_pos.mpr hw1
    have hlog : w < -Real.log (1 - w) := by
      have h := Real.add_one_lt_exp (neg_ne_zero.mpr hw0.ne')
      have := (Real.log_lt_iff_lt_exp hb).mpr (by linarith : 1 - w < Real.exp (-w))
      linarith
    show (-w / (θ * (1 - w))) ^ 2 < w / (θ * (1 - w) ^ 2) * (-Real.log (1 - w) / θ)
    have e1 : (-w / (θ * (1 - w))) ^ 2 = w ^ 2 / (θ ^ 2 * (1 - w) ^ 2) := by
      field_simp
    have e2 : w / (θ * (1 - w) ^ 2) * (-Real.log (1 - w) / θ) =
        w * (-Real.log (1 - w)) / (θ ^ 2 * (1 - w) ^ 2) := by
      field_simp
    rw [e1, e2]
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith

end FrankQuadrant

/-- Frank's copula with `θ > 0` is PQD. -/
theorem isPQD_frank (θ : ℝ) (hθ : 0 < θ) : (frank θ hθ).IsPQD :=
  ((frankGenerator θ hθ).isPQD_and_not_isNQD_of_strictConvexOn (FrankQuadrant.toFun_pos hθ)
    (FrankQuadrant.strictConvexOn_log hθ)).1

/-- Frank's copula with `θ > 0` is not NQD. -/
theorem not_isNQD_frank (θ : ℝ) (hθ : 0 < θ) : ¬ (frank θ hθ).IsNQD :=
  ((frankGenerator θ hθ).isPQD_and_not_isNQD_of_strictConvexOn (FrankQuadrant.toFun_pos hθ)
    (FrankQuadrant.strictConvexOn_log hθ)).2

/-- Frank's copula with `θ < 0` is NQD. -/
theorem isNQD_frankNegative (θ : ℝ) (hθ : θ < 0) : (frankNegative θ hθ).IsNQD :=
  isNQD_reflect_of_isPQD (isPQD_frank (-θ) (neg_pos.mpr hθ))

/-- Frank's copula with `θ < 0` is not PQD. -/
theorem not_isPQD_frankNegative (θ : ℝ) (hθ : θ < 0) : ¬ (frankNegative θ hθ).IsPQD :=
  not_isPQD_reflect_of_not_isNQD (not_isNQD_frank (-θ) (neg_pos.mpr hθ))

end ProbabilityTheory.Copula
