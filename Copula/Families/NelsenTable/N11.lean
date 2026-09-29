/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Clamp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Nelsen's family 11

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 11 (Section 4.2):
generator `φ(t) = ln (2 - t^θ)` for `0 < θ ≤ 1/2` and copula
`C(u, v) = (max (u^θ v^θ - 2 (1 - u^θ) (1 - v^θ)) 0)^(1/θ)`.

The generator is non-strict (`φ(0) = ln 2`), so the inverse generator is the clamped function
`ψ(s) = (2 - exp (min s (ln 2)))^(1/θ)` built with `BivariateGenerator.ofClamp`. With
`p = 1/θ ≥ 2`, convexity on `[0, ln 2]` follows from
`ψ''(s) = p eˢ (2 - eˢ)^(p - 2) (p eˢ - 2) ≥ 0`; this is exactly where `θ ≤ 1/2` is needed.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem nelsen11_u_pos (u : I) (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

private theorem nelsen11_hasDerivAt (p : ℝ) {t : ℝ} (ht : 0 < 2 - Real.exp t) :
    HasDerivAt (fun x => (2 - Real.exp x) ^ p)
      (-p * (Real.exp t * (2 - Real.exp t) ^ (p - 1))) t := by
  have h := ((Real.hasDerivAt_exp t).const_sub 2).rpow_const (p := p) (Or.inl ht.ne')
  refine h.congr_deriv ?_
  ring

private theorem nelsen11_hasDerivAt2 (p : ℝ) {t : ℝ} (ht : 0 < 2 - Real.exp t) :
    HasDerivAt (fun x => -p * (Real.exp x * (2 - Real.exp x) ^ (p - 1)))
      (p * Real.exp t * ((p - 1) * Real.exp t * (2 - Real.exp t) ^ (p - 1 - 1) -
        (2 - Real.exp t) ^ (p - 1))) t := by
  have h1 := ((Real.hasDerivAt_exp t).const_sub 2).rpow_const (p := p - 1) (Or.inl ht.ne')
  have h2 := ((Real.hasDerivAt_exp t).mul h1).const_mul (-p)
  refine h2.congr_deriv ?_
  ring

private theorem nelsen11_convexOn (p : ℝ) (hp : 2 ≤ p) :
    ConvexOn ℝ (Icc 0 (Real.log 2)) (fun t => (2 - Real.exp t) ^ p) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (Real.log 2))
    (f' := fun t => -p * (Real.exp t * (2 - Real.exp t) ^ (p - 1)))
    (f'' := fun t => p * Real.exp t * ((p - 1) * Real.exp t * (2 - Real.exp t) ^ (p - 1 - 1) -
        (2 - Real.exp t) ^ (p - 1))) ?_ ?_ ?_ ?_
  · exact ((continuous_const.sub Real.continuous_exp).rpow_const
      (fun _ => Or.inr (by linarith))).continuousOn
  all_goals
    intro t ht
    rw [interior_Icc] at ht
    have hlt : Real.exp t < 2 := by
      have := Real.exp_lt_exp.mpr ht.2
      rwa [Real.exp_log two_pos] at this
    have hb : 0 < 2 - Real.exp t := by linarith
  · exact (nelsen11_hasDerivAt p hb).hasDerivWithinAt
  · exact (nelsen11_hasDerivAt2 p hb).hasDerivWithinAt
  · show 0 ≤ p * Real.exp t * ((p - 1) * Real.exp t * (2 - Real.exp t) ^ (p - 1 - 1) -
        (2 - Real.exp t) ^ (p - 1))
    have hsplit : (2 - Real.exp t) ^ (p - 1) = (2 - Real.exp t) ^ (p - 1 - 1) * (2 - Real.exp t) := by
      rw [← Real.rpow_add_one hb.ne']
      ring_nf
    have hq : 0 < (2 - Real.exp t) ^ (p - 1 - 1) := Real.rpow_pos_of_pos hb _
    have he : 1 ≤ Real.exp t := Real.one_le_exp ht.1.le
    rw [hsplit]
    apply mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le)
    have : 0 ≤ (2 - Real.exp t) ^ (p - 1 - 1) * (p * Real.exp t - 2) :=
      mul_nonneg hq.le (by nlinarith)
    nlinarith

private theorem nelsen11_antitoneOn (p : ℝ) (hp : 0 ≤ p) :
    AntitoneOn (fun t => (2 - Real.exp t) ^ p) (Icc 0 (Real.log 2)) := by
  intro x _ y hy hxy
  have hle : Real.exp y ≤ 2 := by
    have := Real.exp_le_exp.mpr hy.2
    rwa [Real.exp_log two_pos] at this
  exact Real.rpow_le_rpow (by linarith) (by linarith [Real.exp_le_exp.mpr hxy]) hp

private theorem nelsen11_pow_le_one (θ : ℝ) (hθ : 0 < θ) (u : I) : (u : ℝ) ^ θ ≤ 1 :=
  Real.rpow_le_one u.property.1 u.property.2 hθ.le

private theorem nelsen11_arg (θ : ℝ) (hθ : 0 < θ) (u : I) (hu : u ≠ 0) :
    1 ≤ 2 - (u : ℝ) ^ θ ∧ 2 - (u : ℝ) ^ θ < 2 := by
  have hp := Real.rpow_pos_of_pos (nelsen11_u_pos u hu) θ
  constructor <;> linarith [nelsen11_pow_le_one θ hθ u]

/-- The clamped inverse generator `s ↦ (2 - exp (min s (ln 2)))^(1/θ)` of Nelsen's family 11,
for `0 < θ ≤ 1/2`. Its generator is `u ↦ ln (2 - u^θ)`. -/
noncomputable def nelsen11Generator (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    BivariateGenerator :=
  BivariateGenerator.ofClamp (fun t => (2 - Real.exp t) ^ θ⁻¹) (Real.log 2)
    (Real.log_nonneg one_le_two)
    (nelsen11_convexOn θ⁻¹ (by
      rw [le_inv_comm₀ two_pos hθ]
      linarith))
    (nelsen11_antitoneOn θ⁻¹ (inv_nonneg.mpr hθ.le))
    (by
      show (2 - Real.exp (Real.log 2)) ^ θ⁻¹ = 0
      rw [Real.exp_log two_pos, sub_self, Real.zero_rpow (inv_ne_zero hθ.ne')])
    (fun u => Real.log (2 - (u : ℝ) ^ θ))
    (by
      intro u hu
      obtain ⟨h1, h2⟩ := nelsen11_arg θ hθ u hu
      exact ⟨Real.log_nonneg h1, Real.log_le_log (by linarith) h2.le⟩)
    (by
      intro u v hu huv
      have hup := nelsen11_u_pos u hu
      have h := Real.rpow_le_rpow hup.le huv hθ.le
      obtain ⟨h1, _⟩ := nelsen11_arg θ hθ v (fun hv => hu (le_antisymm (hv ▸ huv) u.property.1))
      exact Real.log_le_log (by linarith) (by linarith))
    (by simp only [Set.Icc.coe_one, Real.one_rpow]; norm_num)
    (by
      intro u hu
      have hup := nelsen11_u_pos u hu
      obtain ⟨h1, _⟩ := nelsen11_arg θ hθ u hu
      show (2 - Real.exp (Real.log (2 - (u : ℝ) ^ θ))) ^ θ⁻¹ = (u : ℝ)
      rw [Real.exp_log (by linarith), sub_sub_cancel, Real.rpow_rpow_inv hup.le hθ.ne'])

/-- Nelsen's family 11 for `0 < θ ≤ 1/2`. -/
noncomputable def nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) : Copula 2 :=
  (nelsen11Generator θ hθ h2).copula

theorem isArchimedean_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    IsArchimedean (nelsen11 θ hθ h2) :=
  (nelsen11Generator θ hθ h2).isArchimedean

/-- The generator of Nelsen's family 11 is `u ↦ ln (2 - u^θ)`. -/
theorem nelsen11Generator_invFun (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) (u : I) :
    (nelsen11Generator θ hθ h2).invFun u = Real.log (2 - (u : ℝ) ^ θ) := rfl

/-- The generator of family 11 is non-strict: its pseudo-inverse vanishes from `ln 2` on. -/
theorem nelsen11Generator_toFun_of_le (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) {s : ℝ}
    (hs : Real.log 2 ≤ s) : (nelsen11Generator θ hθ h2).toFun s = 0 := by
  show (2 - Real.exp (min s (Real.log 2))) ^ θ⁻¹ = 0
  rw [min_eq_right hs, Real.exp_log two_pos, sub_self, Real.zero_rpow (inv_ne_zero hθ.ne')]

/-- The CDF of Nelsen's family 11 on positive coordinates:
`C(u, v) = (max (u^θ v^θ - 2 (1 - u^θ) (1 - v^θ)) 0)^(1/θ)`. -/
theorem cdf_nelsen11 (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) (u v : I) (hu : u ≠ 0)
    (hv : v ≠ 0) :
    (nelsen11 θ hθ h2).cdf ![u, v] =
      (max ((u : ℝ) ^ θ * (v : ℝ) ^ θ - 2 * (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ)) 0) ^ θ⁻¹ := by
  obtain ⟨hu1, _⟩ := nelsen11_arg θ hθ u hu
  obtain ⟨hv1, _⟩ := nelsen11_arg θ hθ v hv
  rw [nelsen11, BivariateGenerator.cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [BivariateGenerator.cdf, ite_or_of_not hu hv _ _]
  show (2 - Real.exp (min (Real.log (2 - (u : ℝ) ^ θ) + Real.log (2 - (v : ℝ) ^ θ))
    (Real.log 2))) ^ θ⁻¹ = _
  have hmin : Real.exp (min (Real.log (2 - (u : ℝ) ^ θ) + Real.log (2 - (v : ℝ) ^ θ))
      (Real.log 2)) = min ((2 - (u : ℝ) ^ θ) * (2 - (v : ℝ) ^ θ)) 2 := by
    rw [Real.exp_monotone.map_min, Real.exp_add, Real.exp_log (by linarith),
      Real.exp_log (by linarith), Real.exp_log two_pos]
  rw [hmin, ← max_sub_sub_left, sub_self]
  rw [show 2 - (2 - (u : ℝ) ^ θ) * (2 - (v : ℝ) ^ θ) =
    (u : ℝ) ^ θ * (v : ℝ) ^ θ - 2 * (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ) by ring]

/-- Nelsen's family 11 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen11_cdf_full (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) (u v : I) :
    (nelsen11 θ hθ h2).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (max ((u : ℝ) ^ θ * (v : ℝ) ^ θ - 2 * (1 - (u : ℝ) ^ θ) * (1 - (v : ℝ) ^ θ)) 0) ^
          θ⁻¹ := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen11 θ hθ h2).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen11 θ hθ h2).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [ite_or_of_not hu hv _ _]
  exact cdf_nelsen11 θ hθ h2 u v hu hv

end ProbabilityTheory.Copula
