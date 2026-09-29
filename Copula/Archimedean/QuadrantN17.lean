/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantLogConvex
import Copula.Families.NelsenTable.N17
import Copula.Dependence.Examples
import Copula.Dependence.Singular

/-! # Quadrant dependence of Nelsen's family 17

The inverse generator of family 17 is `ψ(s) = (1 + d e^{-s})^q - 1` with `q = -1/θ` and
`d = 2^{-θ} - 1`, so that `q d > 0`. With `E = e^{-s}` and `B = 1 + d E` one finds
`ψ ψ'' - ψ'² = q d E B^{q-2} (B^q - 1 - q (B - 1))`. By Bernoulli's inequality the bracket is
strictly positive for `q < 0` and `q > 1`, and strictly negative for `0 < q < 1`. Hence:

* `θ > 0` (`q < 0`) and `-1 < θ < 0` (`q > 1`): PQD and not NQD;
* `θ < -1` (`0 < q < 1`): NQD and not PQD;
* `θ = -1`: independence.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace N17Quadrant

variable {d q : ℝ}

private theorem base_pos (hd : -1 < d) {t : ℝ} (ht : 0 ≤ t) : 0 < 1 + d * Real.exp (-t) := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have h0 := Real.exp_pos (-t)
  rcases le_or_gt 0 d with h | h
  · positivity
  · nlinarith

/-- Bernoulli-type inequality for negative exponents. -/
private theorem one_add_mul_sub_lt_rpow_of_neg {B q : ℝ} (hB : 0 < B) (hB1 : B ≠ 1) (hq : q < 0) :
    1 + q * (B - 1) < B ^ q := by
  have hl : Real.log B ≠ 0 := fun h => hB1 (by
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact h; linarith])
  have h1 := Real.add_one_lt_exp (mul_ne_zero hq.ne hl)
  have h2 := Real.log_le_sub_one_of_pos hB
  rw [Real.rpow_def_of_pos hB, mul_comm (Real.log B) q]
  nlinarith

private theorem hasDerivAt_psi (hd : -1 < d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => (1 + d * Real.exp (-t)) ^ q - 1)
      (-(q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 1))) t := by
  have hB : HasDerivAt (fun t => 1 + d * Real.exp (-t)) (-(d * Real.exp (-t))) t := by
    have := ((hasDerivAt_id t).neg.exp.const_mul d).const_add 1
    refine this.congr_deriv ?_
    simp
  have h := (hB.rpow_const (p := q) (Or.inl (base_pos hd ht.le).ne')).sub_const 1
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_psi1 (hd : -1 < d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -(q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 1)))
      (q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 2) *
        (1 + q * d * Real.exp (-t))) t := by
  have hB : HasDerivAt (fun t => 1 + d * Real.exp (-t)) (-(d * Real.exp (-t))) t := by
    have := ((hasDerivAt_id t).neg.exp.const_mul d).const_add 1
    refine this.congr_deriv ?_
    simp
  have hE : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
    have := (hasDerivAt_id t).neg.exp
    refine this.congr_deriv ?_
    simp
  have h1 := hB.rpow_const (p := q - 1) (Or.inl (base_pos hd ht.le).ne')
  have h := (((hE.const_mul (q * d)).mul h1)).neg
  refine h.congr_deriv ?_
  have hz : (1 + d * Real.exp (-t)) ^ (q - 1) =
      (1 + d * Real.exp (-t)) ^ (q - 2) * (1 + d * Real.exp (-t)) := by
    rw [← Real.rpow_add_one (base_pos hd ht.le).ne']; ring_nf
  rw [show q - 1 - 1 = q - 2 by ring, hz]
  ring

/-- Second-derivative identity `ψ ψ'' - ψ'² = c E A (B^q - 1 - c E)`, `c = q d`. -/
private theorem key_identity (hd : -1 < d) {t : ℝ} (ht : 0 < t) :
    (q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 2) * (1 + q * d * Real.exp (-t))) *
        ((1 + d * Real.exp (-t)) ^ q - 1) -
      (-(q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 1))) ^ 2 =
    q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 2) *
      ((1 + d * Real.exp (-t)) ^ q - 1 - q * d * Real.exp (-t)) := by
  have hb := base_pos hd ht.le
  have hz : (1 + d * Real.exp (-t)) ^ (q - 1) =
      (1 + d * Real.exp (-t)) ^ (q - 2) * (1 + d * Real.exp (-t)) := by
    rw [← Real.rpow_add_one hb.ne']; ring_nf
  have hz2 : (1 + d * Real.exp (-t)) ^ q =
      (1 + d * Real.exp (-t)) ^ (q - 2) * (1 + d * Real.exp (-t)) ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hb]; ring_nf
  rw [hz]
  set B := 1 + d * Real.exp (-t)
  set A := B ^ (q - 2)
  set E := Real.exp (-t)
  have hBE : d * E = B - 1 := by simp only [B]; ring
  rw [hz2]
  have : q * d * E = q * (B - 1) := by rw [mul_assoc, hBE]
  rw [this]
  ring

/-- Positivity of the inverse generator. -/
theorem psi_pos (hd : -1 < d) (hd0 : d ≠ 0) (hqd : 0 < q * d) {t : ℝ} (ht : 0 ≤ t) :
    0 < (1 + d * Real.exp (-t)) ^ q - 1 := by
  have hb := base_pos hd ht
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have h0 := Real.exp_pos (-t)
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · have hq : q < 0 := by nlinarith
    have : 1 + d * Real.exp (-t) < 1 := by nlinarith
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hb this hq
    linarith
  · have hq : 0 < q := by nlinarith
    have : 1 < 1 + d * Real.exp (-t) := by nlinarith
    have := Real.one_lt_rpow this hq
    linarith

private theorem continuousOn_psi (hd : -1 < d) :
    ContinuousOn (fun t => (1 + d * Real.exp (-t)) ^ q - 1) (Ici 0) := by
  refine ContinuousOn.sub (ContinuousOn.rpow_const (continuousOn_const.add (continuousOn_const.mul
    (Real.continuous_exp.comp continuous_neg).continuousOn)) (fun t ht => Or.inl
      (base_pos hd (mem_Ici.mp ht)).ne')) continuousOn_const

/-- Strict log-convexity when `q < 0` or `q > 1`. -/
theorem strictConvexOn_log (hd : -1 < d) (hd0 : d ≠ 0) (hqd : 0 < q * d)
    (hq : q < 0 ∨ 1 < q) :
    StrictConvexOn ℝ (Ici 0) (fun t => Real.log ((1 + d * Real.exp (-t)) ^ q - 1)) := by
  refine strictConvexOn_log_of_derivs (fun t ht => psi_pos hd hd0 hqd ht) (continuousOn_psi hd)
    (fun t ht => hasDerivAt_psi hd ht) (fun t ht => hasDerivAt_psi1 hd ht) ?_
  intro t ht
  have hb := base_pos hd ht.le
  have hE := Real.exp_pos (-t)
  have hpsi := psi_pos hd hd0 hqd ht.le
  have hid := key_identity (q := q) hd ht
  have hBne : 1 + d * Real.exp (-t) ≠ 1 := by
    intro h; have : d * Real.exp (-t) = 0 := by linarith
    exact hd0 (by simpa [hE.ne'] using this)
  have hs : d * Real.exp (-t) ≠ 0 := mul_ne_zero hd0 hE.ne'
  have hbern : 1 + q * d * Real.exp (-t) < (1 + d * Real.exp (-t)) ^ q := by
    have hs1 : -1 ≤ d * Real.exp (-t) := by linarith
    rcases hq with hq | hq
    · have := one_add_mul_sub_lt_rpow_of_neg hb hBne hq
      nlinarith
    · have := one_add_mul_self_lt_rpow_one_add hs1 hs hq
      nlinarith
  have hA : 0 < (1 + d * Real.exp (-t)) ^ (q - 2) := Real.rpow_pos_of_pos hb _
  have hcE : 0 < q * d * Real.exp (-t) := mul_pos hqd hE
  have : 0 < q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 2) *
      ((1 + d * Real.exp (-t)) ^ q - 1 - q * d * Real.exp (-t)) :=
    mul_pos (mul_pos hcE hA) (by linarith)
  linarith

/-- Strict log-concavity when `0 < q < 1`. -/
theorem strictConcaveOn_log (hd : -1 < d) (hd0 : d ≠ 0) (hqd : 0 < q * d)
    (hq0 : 0 < q) (hq1 : q < 1) :
    StrictConcaveOn ℝ (Ici 0) (fun t => Real.log ((1 + d * Real.exp (-t)) ^ q - 1)) := by
  refine strictConcaveOn_log_of_derivs (fun t ht => psi_pos hd hd0 hqd ht) (continuousOn_psi hd)
    (fun t ht => hasDerivAt_psi hd ht) (fun t ht => hasDerivAt_psi1 hd ht) ?_
  intro t ht
  have hb := base_pos hd ht.le
  have hE := Real.exp_pos (-t)
  have hid := key_identity (q := q) hd ht
  have hs : d * Real.exp (-t) ≠ 0 := mul_ne_zero hd0 hE.ne'
  have hs1 : -1 ≤ d * Real.exp (-t) := by
    have := hb; linarith
  have hbern : (1 + d * Real.exp (-t)) ^ q < 1 + q * d * Real.exp (-t) := by
    have := rpow_one_add_lt_one_add_mul_self hs1 hs hq0 hq1
    nlinarith
  have hA : 0 < (1 + d * Real.exp (-t)) ^ (q - 2) := Real.rpow_pos_of_pos hb _
  have hcE : 0 < q * d * Real.exp (-t) := mul_pos hqd hE
  have : q * d * Real.exp (-t) * (1 + d * Real.exp (-t)) ^ (q - 2) *
      ((1 + d * Real.exp (-t)) ^ q - 1 - q * d * Real.exp (-t)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hcE hA) (by linarith)
  linarith

/-- The constants `d = 2^{-θ} - 1` and `q = -1/θ` satisfy `-1 < d`, `d ≠ 0` and `0 < q d`. -/
theorem params (θ : ℝ) (hθ : θ ≠ 0) :
    -1 < (2 : ℝ) ^ (-θ) - 1 ∧ (2 : ℝ) ^ (-θ) - 1 ≠ 0 ∧ 0 < -θ⁻¹ * ((2 : ℝ) ^ (-θ) - 1) := by
  have h2 := Real.rpow_pos_of_pos two_pos (-θ)
  refine ⟨by linarith, ?_, ?_⟩
  · rcases hθ.lt_or_gt with h | h
    · have := Real.one_lt_rpow one_lt_two (neg_pos.mpr h); linarith
    · have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos h); linarith
  · rcases hθ.lt_or_gt with h | h
    · have := Real.one_lt_rpow one_lt_two (neg_pos.mpr h)
      exact mul_pos (neg_pos.mpr (inv_lt_zero.mpr h)) (by linarith)
    · have := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos h)
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (inv_pos.mpr h)) (by linarith)

end N17Quadrant

/-- Nelsen's family 17 is PQD and not NQD for `θ > 0` and for `-1 < θ < 0`. -/
theorem isPQD_and_not_isNQD_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) (h : -1 < θ) :
    (nelsen17 θ hθ).IsPQD ∧ ¬ (nelsen17 θ hθ).IsNQD := by
  obtain ⟨hd, hd0, hqd⟩ := N17Quadrant.params θ hθ
  have hq : -θ⁻¹ < 0 ∨ 1 < -θ⁻¹ := by
    rcases hθ.lt_or_gt with h' | h'
    · right
      rw [← inv_neg]
      exact (one_lt_inv₀ (by linarith)).mpr (by linarith)
    · left; exact neg_neg_of_pos (inv_pos.mpr h')
  exact (nelsen17Generator θ hθ).isPQD_and_not_isNQD_of_strictConvexOn
    (fun t ht => N17Quadrant.psi_pos hd hd0 hqd ht)
    (N17Quadrant.strictConvexOn_log hd hd0 hqd hq)

/-- Nelsen's family 17 is NQD and not PQD for `θ < -1`. -/
theorem isNQD_and_not_isPQD_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) (h : θ < -1) :
    (nelsen17 θ hθ).IsNQD ∧ ¬ (nelsen17 θ hθ).IsPQD := by
  obtain ⟨hd, hd0, hqd⟩ := N17Quadrant.params θ hθ
  have hq0 : 0 < -θ⁻¹ := neg_pos.mpr (inv_lt_zero.mpr (by linarith))
  have hq1 : -θ⁻¹ < 1 := by
    rw [← inv_neg]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  exact (nelsen17Generator θ hθ).isNQD_and_not_isPQD_of_strictConcaveOn
    (fun t ht => N17Quadrant.psi_pos hd hd0 hqd ht)
    (N17Quadrant.strictConcaveOn_log hd hd0 hqd hq0 hq1)

/-- Nelsen's family 17 is PQD iff `θ ≥ -1`. -/
theorem isPQD_nelsen17_iff (θ : ℝ) (hθ : θ ≠ 0) : (nelsen17 θ hθ).IsPQD ↔ -1 ≤ θ := by
  constructor
  · intro h
    by_contra hc
    exact (isNQD_and_not_isPQD_nelsen17 θ hθ (not_le.mp hc)).2 h
  · intro h
    rcases h.eq_or_lt with rfl | h'
    · rw [nelsen17_neg_one]; exact isPQD_independence
    · exact (isPQD_and_not_isNQD_nelsen17 θ hθ h').1

/-- Nelsen's family 17 is NQD iff `θ ≤ -1`. -/
theorem isNQD_nelsen17_iff (θ : ℝ) (hθ : θ ≠ 0) : (nelsen17 θ hθ).IsNQD ↔ θ ≤ -1 := by
  constructor
  · intro h
    by_contra hc
    exact (isPQD_and_not_isNQD_nelsen17 θ hθ (by linarith [not_le.mp hc])).2 h
  · intro h
    rcases h.eq_or_lt with rfl | h'
    · rw [nelsen17_neg_one]; exact isNQD_independence
    · exact (isNQD_and_not_isPQD_nelsen17 θ hθ h').1

end ProbabilityTheory.Copula
