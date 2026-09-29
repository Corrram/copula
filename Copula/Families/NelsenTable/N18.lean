/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Clamp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Nelsen's family 18

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 18 (Section 4.2):
generator `φ(t) = exp (θ / (t - 1))` for `θ ≥ 2` and copula
`C(u, v) = max (1 + θ / ln (exp (θ / (u - 1)) + exp (θ / (v - 1)))) 0`.

The generator is non-strict (`φ(0) = e^(-θ)`, and `φ(1) = 0` as the limit `t → 1⁻`, imposed
explicitly here). The pseudo-inverse is `ψ(s) = 1 + θ / ln (min s e^(-θ))`, built with
`BivariateGenerator.ofClamp`. On `(0, e^(-θ))` one has `ln s < -θ ≤ -2` and
`ψ''(s) = θ ln s (ln s + 2) / (s ln² s)² ≥ 0`; this is exactly where `θ ≥ 2` is needed.
At `s = 0` Lean's convention `ln 0 = 0` gives `ψ(0) = 1`, which is also the limit.
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private theorem nelsen18_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen18_u_lt_one (u : I) (hu : u ≠ 1) : (u : ℝ) < 1 :=
  lt_of_le_of_ne u.property.2 (fun h => hu (Subtype.ext h))

private theorem nelsen18_hasDerivAt (θ : ℝ) {t : ℝ} (ht : 0 < t) (hl : Real.log t ≠ 0) :
    HasDerivAt (fun x => 1 + θ / Real.log x) (-θ * (t * Real.log t ^ 2)⁻¹) t := by
  have h := ((Real.hasDerivAt_log ht.ne').inv hl).const_mul θ
  refine (h.const_add 1).congr_deriv ?_
  field_simp

private theorem nelsen18_hasDerivAt2 (θ : ℝ) {t : ℝ} (ht : 0 < t) (hl : Real.log t ≠ 0) :
    HasDerivAt (fun x => -θ * (x * Real.log x ^ 2)⁻¹)
      (θ * (Real.log t * (Real.log t + 2)) / (t * Real.log t ^ 2) ^ 2) t := by
  have hh : HasDerivAt (fun x => x * Real.log x ^ 2)
      (1 * Real.log t ^ 2 + t * ((2 : ℕ) * Real.log t ^ (2 - 1) * t⁻¹)) t :=
    (hasDerivAt_id t).mul ((Real.hasDerivAt_log ht.ne').pow 2)
  have hne : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht.ne' (pow_ne_zero 2 hl)
  refine ((hh.inv hne).const_mul (-θ)).congr_deriv ?_
  field_simp
  ring

private theorem nelsen18_continuousAt_zero (θ : ℝ) :
    ContinuousAt (fun x => 1 + θ / Real.log x) 0 := by
  have hg : ContinuousAt (fun x => (Real.log x)⁻¹) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, Real.log_zero, inv_zero]
    exact Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot
  have h2 : ContinuousAt (fun x => 1 + θ * (Real.log x)⁻¹) 0 :=
    continuousAt_const.add (continuousAt_const.mul hg)
  simpa only [div_eq_mul_inv] using h2

private theorem nelsen18_exp_lt_one (θ : ℝ) (hθ : 0 < θ) : Real.exp (-θ) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

private theorem nelsen18_log_neg {θ : ℝ} (hθ : 0 < θ) {t : ℝ} (ht : 0 < t)
    (hta : t ≤ Real.exp (-θ)) : Real.log t < 0 :=
  Real.log_neg ht (lt_of_le_of_lt hta (nelsen18_exp_lt_one θ hθ))

private theorem nelsen18_convexOn (θ : ℝ) (hθ : 2 ≤ θ) :
    ConvexOn ℝ (Icc 0 (Real.exp (-θ))) (fun x => 1 + θ / Real.log x) := by
  have hθ0 : 0 < θ := by linarith
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (Real.exp (-θ)))
    (f' := fun t => -θ * (t * Real.log t ^ 2)⁻¹)
    (f'' := fun t => θ * (Real.log t * (Real.log t + 2)) / (t * Real.log t ^ 2) ^ 2) ?_ ?_ ?_ ?_
  · intro t ht
    rcases ht.1.eq_or_lt with h0 | h0
    · subst h0
      exact (nelsen18_continuousAt_zero θ).continuousWithinAt
    · have hl := (nelsen18_log_neg hθ0 h0 ht.2).ne
      exact (nelsen18_hasDerivAt θ h0 hl).continuousAt.continuousWithinAt
  all_goals
    intro t ht
    rw [interior_Icc] at ht
    have hl := nelsen18_log_neg hθ0 ht.1 ht.2.le
  · exact (nelsen18_hasDerivAt θ ht.1 hl.ne).hasDerivWithinAt
  · exact (nelsen18_hasDerivAt2 θ ht.1 hl.ne).hasDerivWithinAt
  · have hlt : Real.log t < -θ := by
      have := Real.log_lt_log ht.1 ht.2
      rwa [Real.log_exp] at this
    show 0 ≤ θ * (Real.log t * (Real.log t + 2)) / (t * Real.log t ^ 2) ^ 2
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg hθ0.le (mul_nonneg_of_nonpos_of_nonpos hl.le (by linarith))

private theorem nelsen18_antitoneOn (θ : ℝ) (hθ : 0 < θ) :
    AntitoneOn (fun x => 1 + θ / Real.log x) (Icc 0 (Real.exp (-θ))) := by
  intro x hx y hy hxy
  show 1 + θ / Real.log y ≤ 1 + θ / Real.log x
  rcases hx.1.eq_or_lt with h0 | h0
  · subst h0
    rcases hy.1.eq_or_lt with h1 | h1
    · subst h1
      exact le_rfl
    · have hl := nelsen18_log_neg hθ h1 hy.2
      rw [Real.log_zero, div_zero]
      linarith [div_nonpos_of_nonneg_of_nonpos hθ.le hl.le]
  · have hlx := nelsen18_log_neg hθ h0 hx.2
    have hly := nelsen18_log_neg hθ (lt_of_lt_of_le h0 hxy) hy.2
    have hle : Real.log x ≤ Real.log y := Real.log_le_log h0 hxy
    rw [← neg_neg (Real.log y), ← neg_neg (Real.log x), div_neg, div_neg]
    have := div_le_div_of_nonneg_left hθ.le (neg_pos.mpr hly) (neg_le_neg hle)
    linarith

/-- The generator `u ↦ exp (θ / (u - 1))` of family 18, with its value `0` at `u = 1`. -/
noncomputable def nelsen18Phi (θ : ℝ) (u : I) : ℝ :=
  if u = 1 then 0 else Real.exp (θ / ((u : ℝ) - 1))

private theorem nelsen18Phi_of_ne (θ : ℝ) {u : I} (hu : u ≠ 1) :
    nelsen18Phi θ u = Real.exp (θ / ((u : ℝ) - 1)) := by
  simp [nelsen18Phi, hu]

private theorem nelsen18Phi_le (θ : ℝ) (hθ : 0 < θ) {u : I} (hu : u ≠ 0) :
    nelsen18Phi θ u ∈ Icc 0 (Real.exp (-θ)) := by
  unfold nelsen18Phi
  split_ifs with h
  · exact ⟨le_rfl, (Real.exp_pos _).le⟩
  · refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
    have hup := nelsen18_u_pos u hu
    have hu1 := nelsen18_u_lt_one u h
    rw [div_le_iff_of_neg (by linarith)]
    nlinarith

/-- The clamped pseudo-inverse `s ↦ 1 + θ / ln (min s e^(-θ))` of Nelsen's family 18, for
`θ ≥ 2`. Its generator is `u ↦ exp (θ / (u - 1))` (with value `0` at `u = 1`). -/
noncomputable def nelsen18Generator (θ : ℝ) (hθ : 2 ≤ θ) : BivariateGenerator :=
  BivariateGenerator.ofClamp (fun x => 1 + θ / Real.log x) (Real.exp (-θ))
    (Real.exp_pos _).le (nelsen18_convexOn θ hθ) (nelsen18_antitoneOn θ (by linarith))
    (by
      show 1 + θ / Real.log (Real.exp (-θ)) = 0
      rw [Real.log_exp, div_neg, div_self (by linarith)]
      ring)
    (nelsen18Phi θ) (fun u hu => nelsen18Phi_le θ (by linarith) hu)
    (by
      intro u v hu huv
      by_cases hv1 : v = 1
      · rw [show nelsen18Phi θ v = 0 by simp [nelsen18Phi, hv1]]
        exact (nelsen18Phi_le θ (by linarith) hu).1
      have hu1 : u ≠ 1 := fun h => hv1 (le_antisymm v.property.2 (h ▸ huv))
      rw [nelsen18Phi_of_ne θ hu1, nelsen18Phi_of_ne θ hv1]
      apply Real.exp_le_exp.mpr
      have hu1' := nelsen18_u_lt_one u hu1
      have hv1' := nelsen18_u_lt_one v hv1
      have huv' : (u : ℝ) ≤ (v : ℝ) := huv
      have e1 : θ / ((v : ℝ) - 1) = -(θ / (1 - (v : ℝ))) := by rw [← div_neg, neg_sub]
      have e2 : θ / ((u : ℝ) - 1) = -(θ / (1 - (u : ℝ))) := by rw [← div_neg, neg_sub]
      rw [e1, e2]
      have := div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ θ) (by linarith : 0 < 1 - (v : ℝ))
        (by linarith : 1 - (v : ℝ) ≤ 1 - (u : ℝ))
      linarith)
    (by simp [nelsen18Phi])
    (by
      intro u hu
      by_cases hu1 : u = 1
      · rw [show nelsen18Phi θ u = 0 by simp [nelsen18Phi, hu1], hu1]
        simp
      rw [nelsen18Phi_of_ne θ hu1]
      show 1 + θ / Real.log (Real.exp (θ / ((u : ℝ) - 1))) = (u : ℝ)
      rw [Real.log_exp, div_div_cancel₀ (by linarith)]
      ring)

/-- Nelsen's family 18 for `θ ≥ 2`. -/
noncomputable def nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) : Copula 2 :=
  (nelsen18Generator θ hθ).copula

theorem isArchimedean_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) : IsArchimedean (nelsen18 θ hθ) :=
  (nelsen18Generator θ hθ).isArchimedean

/-- The generator of family 18 is non-strict: its pseudo-inverse vanishes from `e^(-θ)` on. -/
theorem nelsen18Generator_toFun_of_le (θ : ℝ) (hθ : 2 ≤ θ) {s : ℝ} (hs : Real.exp (-θ) ≤ s) :
    (nelsen18Generator θ hθ).toFun s = 0 := by
  show 1 + θ / Real.log (min s (Real.exp (-θ))) = 0
  rw [min_eq_right hs, Real.log_exp, div_neg, div_self (by linarith)]
  ring

/-- The CDF of Nelsen's family 18 on the open unit square:
`C(u, v) = max (1 + θ / ln (exp (θ / (u - 1)) + exp (θ / (v - 1)))) 0`. -/
theorem cdf_nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) (u v : I) (hu : u ≠ 0) (hu1 : u ≠ 1) (hv : v ≠ 0)
    (hv1 : v ≠ 1) :
    (nelsen18 θ hθ).cdf ![u, v] =
      max (1 + θ / Real.log (Real.exp (θ / ((u : ℝ) - 1)) + Real.exp (θ / ((v : ℝ) - 1)))) 0 := by
  have hθ0 : 0 < θ := by linarith
  rw [nelsen18, BivariateGenerator.cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [BivariateGenerator.cdf, ite_or_of_not hu hv _ _]
  show 1 + θ / Real.log (min (nelsen18Phi θ u + nelsen18Phi θ v) (Real.exp (-θ))) = _
  rw [nelsen18Phi_of_ne θ hu1, nelsen18Phi_of_ne θ hv1]
  set S := Real.exp (θ / ((u : ℝ) - 1)) + Real.exp (θ / ((v : ℝ) - 1)) with hS
  have hSpos : 0 < S := by positivity
  have hSu := (nelsen18Phi_le θ hθ0 hu).2
  have hSv := (nelsen18Phi_le θ hθ0 hv).2
  rw [nelsen18Phi_of_ne θ hu1] at hSu
  rw [nelsen18Phi_of_ne θ hv1] at hSv
  rcases le_total S (Real.exp (-θ)) with h | h
  · rw [min_eq_left h, max_eq_left]
    have := nelsen18_antitoneOn θ hθ0 ⟨hSpos.le, h⟩ ⟨(Real.exp_pos _).le, le_rfl⟩ h
    simp only [Real.log_exp, div_neg, div_self hθ0.ne'] at this
    linarith
  · rw [min_eq_right h, max_eq_right, Real.log_exp, div_neg, div_self hθ0.ne']
    · ring
    -- `S ≤ 2 e^(-θ) ≤ 2 e^(-2) < 1`, so `ln S < 0`, and `ln S ≥ -θ`.
    have he2 : 2 * Real.exp (-θ) < 1 := by
      have h1 : Real.exp (-θ) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      have h2 : 2 + 1 < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
      have h3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-2)]
    have hlS : Real.log S < 0 := Real.log_neg hSpos (by linarith)
    have hlS2 : -θ ≤ Real.log S := by
      rw [← Real.log_exp (-θ)]
      exact Real.log_le_log (Real.exp_pos _) h
    have : θ / Real.log S ≤ -1 := by
      rw [div_le_iff_of_neg hlS]
      linarith
    linarith

end ProbabilityTheory.Copula
