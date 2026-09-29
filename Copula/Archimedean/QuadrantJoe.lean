/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantLogConvex
import Copula.Families.Joe
import Copula.Dependence.Examples
import Copula.Dependence.Singular

/-! # Quadrant dependence of Joe's family (Nelsen's family 6)

For `θ > 1`, Joe's copula is PQD and not NQD; for `θ = 1` it is independence.
The inverse generator is `ψ(t) = 1 - (1 - e^{-t})^p`, `p = 1/θ ∈ (0, 1)`. With `e = e^{-t}` and
`z = 1 - e` one finds `ψ ψ'' - ψ'² = p e z^{p-2} (1 - p e) (1 - z^p) - p² z^{2p-2} e²`, which is
positive because `z^p < 1 - p e` (Bernoulli's inequality).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace JoeQuadrant

variable {p : ℝ}

private theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-t) := by
  have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht); linarith

private theorem one_sub_exp_lt {t : ℝ} : 1 - Real.exp (-t) < 1 := by
  have := Real.exp_pos (-t); linarith

private theorem hasDerivAt_e (t : ℝ) : HasDerivAt (fun t => 1 - Real.exp (-t)) (Real.exp (-t)) t := by
  have := ((hasDerivAt_id t).neg.exp).const_sub 1
  refine this.congr_deriv ?_
  simp

private theorem hasDerivAt_psi {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => 1 - (1 - Real.exp (-t)) ^ p)
      (-(p * (1 - Real.exp (-t)) ^ (p - 1) * Real.exp (-t))) t := by
  have h := ((hasDerivAt_e t).rpow_const (p := p) (Or.inl (one_sub_exp_pos ht).ne')).const_sub 1
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_psi1 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -(p * (1 - Real.exp (-t)) ^ (p - 1) * Real.exp (-t)))
      (p * Real.exp (-t) * (1 - Real.exp (-t)) ^ (p - 2) * (1 - p * Real.exp (-t))) t := by
  have h1 := (hasDerivAt_e t).rpow_const (p := p - 1) (Or.inl (one_sub_exp_pos ht).ne')
  have h2 : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
    have := (hasDerivAt_id t).neg.exp
    refine this.congr_deriv ?_
    simp
  have h := ((h1.const_mul p).mul h2).neg
  refine h.congr_deriv ?_
  have hz : (1 - Real.exp (-t)) ^ (p - 1) = (1 - Real.exp (-t)) ^ (p - 2) * (1 - Real.exp (-t)) := by
    rw [← Real.rpow_add_one (one_sub_exp_pos ht).ne']; ring_nf
  rw [show p - 1 - 1 = p - 2 by ring, hz]
  ring

/-- Joe's inverse generator is positive on `[0, ∞)`. -/
theorem toFun_pos {θ : ℝ} (hθ : 1 < θ) : ∀ t, 0 ≤ t → 0 < (joeGenerator θ hθ.le).toFun t := by
  intro t ht
  have hp0 : 0 < θ⁻¹ := inv_pos.mpr (by linarith)
  show 0 < 1 - (1 - Real.exp (-t)) ^ θ⁻¹
  have := Real.rpow_lt_one (by have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht); linarith)
    one_sub_exp_lt hp0
  linarith

/-- Joe's generator is strictly log-convex for `θ > 1`. -/
theorem strictConvexOn_log {θ : ℝ} (hθ : 1 < θ) :
    StrictConvexOn ℝ (Ici 0) (fun t => Real.log ((joeGenerator θ hθ.le).toFun t)) := by
  have hp0 : 0 < θ⁻¹ := inv_pos.mpr (by linarith)
  have hp1 : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ
  have hpos := toFun_pos hθ
  refine strictConvexOn_log_of_derivs hpos ?_ (fun t ht => hasDerivAt_psi ht)
    (fun t ht => hasDerivAt_psi1 ht) ?_
  · exact continuousOn_const.sub (ContinuousOn.rpow_const
      (continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn)
      (fun _ _ => Or.inr hp0.le))
  · intro t ht
    have hz0 := one_sub_exp_pos ht
    have he0 := Real.exp_pos (-t)
    set e := Real.exp (-t) with he
    set z := 1 - e with hz
    show (-(θ⁻¹ * z ^ (θ⁻¹ - 1) * e)) ^ 2 < θ⁻¹ * e * z ^ (θ⁻¹ - 2) * (1 - θ⁻¹ * e) *
      (1 - z ^ θ⁻¹)
    have hA : 0 < z ^ (θ⁻¹ - 2) := Real.rpow_pos_of_pos hz0 _
    have h1 : z ^ (θ⁻¹ - 1) = z ^ (θ⁻¹ - 2) * z := by
      rw [← Real.rpow_add_one hz0.ne']; ring_nf
    have h2 : z ^ θ⁻¹ = z ^ (θ⁻¹ - 2) * z ^ 2 := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz0]; ring_nf
    have hB := rpow_one_add_lt_one_add_mul_self (p := θ⁻¹) (s := -e)
      (by have : e < 1 := by rw [he]; exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
          linarith) (neg_ne_zero.mpr he0.ne') hp0 hp1
    rw [show 1 + -e = z by rw [hz]; ring] at hB
    set A := z ^ (θ⁻¹ - 2) with hAdef
    set Z := z ^ θ⁻¹ with hZ
    have key : θ⁻¹ * e * A * (1 - θ⁻¹ * e) * (1 - Z) - (-(θ⁻¹ * (A * z) * e)) ^ 2 =
        θ⁻¹ * e * A * (1 - Z - θ⁻¹ * e) := by
      rw [h2]; ring
    rw [h1]
    have : 0 < θ⁻¹ * e * A * (1 - Z - θ⁻¹ * e) := by
      apply mul_pos (by positivity)
      nlinarith
    linarith

end JoeQuadrant

/-- Joe's copula with `θ ≥ 1` is PQD (independence at `θ = 1`). -/
theorem isPQD_joe (θ : ℝ) (hθ : 1 ≤ θ) : (joe θ hθ).IsPQD := by
  rcases hθ.eq_or_lt with rfl | h
  · rw [joe_one]; exact isPQD_independence
  · exact ((joeGenerator θ hθ).isPQD_and_not_isNQD_of_strictConvexOn (JoeQuadrant.toFun_pos h)
      (JoeQuadrant.strictConvexOn_log h)).1

/-- Joe's copula with `θ > 1` is not NQD. -/
theorem not_isNQD_joe (θ : ℝ) (hθ : 1 < θ) : ¬ (joe θ hθ.le).IsNQD :=
  ((joeGenerator θ hθ.le).isPQD_and_not_isNQD_of_strictConvexOn (JoeQuadrant.toFun_pos hθ)
    (JoeQuadrant.strictConvexOn_log hθ)).2

/-- Joe's copula is NQD iff `θ = 1` (independence). -/
theorem isNQD_joe_iff (θ : ℝ) (hθ : 1 ≤ θ) : (joe θ hθ).IsNQD ↔ θ = 1 := by
  rcases hθ.eq_or_lt with rfl | h
  · simp only [joe_one, isNQD_independence]
  · exact iff_of_false (not_isNQD_joe θ h) h.ne'

end ProbabilityTheory.Copula
