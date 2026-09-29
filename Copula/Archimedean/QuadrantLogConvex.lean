/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantCriteria
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Quadrant dependence from strict log-convexity of the inverse generator

If `log ψ` is strictly convex on `[0, ∞)` for the inverse generator `ψ` of an Archimedean copula
(with `ψ > 0`), then `ψ(0) = 1` gives the strict superadditivity `ψ(x) ψ(y) < ψ(x + y)` for
`x, y > 0`. By the criteria of `Copula.Archimedean.QuadrantCriteria` the copula is then PQD but not
NQD. Strict log-concavity gives the opposite (NQD but not PQD). Strict (log-)convexity is
checked from the second derivative: `ψ ψ'' > (ψ')²` (resp. `<`) on `(0, ∞)`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- If `ψ > 0` is twice differentiable on `(0, ∞)`, continuous on `[0, ∞)` and
`ψ'^2 < ψ ψ''` there, then `log ψ` is strictly convex on `[0, ∞)`. -/
theorem strictConvexOn_log_of_derivs {ψ ψ1 ψ2 : ℝ → ℝ} (hpos : ∀ t, 0 ≤ t → 0 < ψ t)
    (hcont : ContinuousOn ψ (Ici 0)) (h1 : ∀ t, 0 < t → HasDerivAt ψ (ψ1 t) t)
    (h2 : ∀ t, 0 < t → HasDerivAt ψ1 (ψ2 t) t) (h : ∀ t, 0 < t → ψ1 t ^ 2 < ψ2 t * ψ t) :
    StrictConvexOn ℝ (Ici 0) (fun t => Real.log (ψ t)) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0)
    (hcont.log (fun t ht => (hpos t ht).ne')) ?_
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd : deriv (fun t => Real.log (ψ t)) =ᶠ[nhds x] fun t => ψ1 t / ψ t := by
    filter_upwards [Ioi_mem_nhds hx0] with y hy
    exact ((h1 y hy).log (hpos y hy.le).ne').deriv
  have hpx := hpos x hx0.le
  have hder := (h2 x hx0).div (h1 x hx0) hpx.ne'
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply,
    hd.deriv_eq, show deriv (fun t => ψ1 t / ψ t) x = _ from hder.deriv]
  apply div_pos _ (pow_pos hpx 2)
  have := h x hx0
  nlinarith

/-- If `ψ > 0` is twice differentiable on `(0, ∞)`, continuous on `[0, ∞)` and
`ψ ψ'' < (ψ')²` there, then `log ψ` is strictly concave on `[0, ∞)`. -/
theorem strictConcaveOn_log_of_derivs {ψ ψ1 ψ2 : ℝ → ℝ} (hpos : ∀ t, 0 ≤ t → 0 < ψ t)
    (hcont : ContinuousOn ψ (Ici 0)) (h1 : ∀ t, 0 < t → HasDerivAt ψ (ψ1 t) t)
    (h2 : ∀ t, 0 < t → HasDerivAt ψ1 (ψ2 t) t) (h : ∀ t, 0 < t → ψ2 t * ψ t < ψ1 t ^ 2) :
    StrictConcaveOn ℝ (Ici 0) (fun t => Real.log (ψ t)) := by
  refine strictConcaveOn_of_deriv2_neg (convex_Ici 0)
    (hcont.log (fun t ht => (hpos t ht).ne')) ?_
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd : deriv (fun t => Real.log (ψ t)) =ᶠ[nhds x] fun t => ψ1 t / ψ t := by
    filter_upwards [Ioi_mem_nhds hx0] with y hy
    exact ((h1 y hy).log (hpos y hy.le).ne').deriv
  have hpx := hpos x hx0.le
  have hder := (h2 x hx0).div (h1 x hx0) hpx.ne'
  rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply,
    hd.deriv_eq, show deriv (fun t => ψ1 t / ψ t) x = _ from hder.deriv]
  apply div_neg_of_neg_of_pos _ (pow_pos hpx 2)
  have := h x hx0
  nlinarith

/-- A strictly convex `f` on `[0, ∞)` with `f 0 = 0` is strictly superadditive on `(0, ∞)`. -/
theorem lt_add_of_strictConvexOn {f : ℝ → ℝ} (hf : StrictConvexOn ℝ (Ici 0) f) (h0 : f 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : f x + f y < f (x + y) := by
  have hs : 0 < x + y := add_pos hx hy
  have key : ∀ z, 0 < z → z < x + y → f z < z / (x + y) * f (x + y) := by
    intro z hz hzs
    have ha : 0 < z / (x + y) := div_pos hz hs
    have hb : 0 < 1 - z / (x + y) := by
      rw [sub_pos, div_lt_one hs]; exact hzs
    have h := hf.2 (mem_Ici.mpr hs.le) (mem_Ici.mpr le_rfl : (0 : ℝ) ∈ Ici 0)
      hs.ne' ha hb (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, h0] at h
    rwa [div_mul_cancel₀ _ hs.ne'] at h
  have h1 := key x hx (by linarith)
  have h2 := key y hy (by linarith)
  have : x / (x + y) * f (x + y) + y / (x + y) * f (x + y) = f (x + y) := by
    rw [← add_mul, ← add_div, div_self hs.ne', one_mul]
  linarith

namespace BivariateGenerator

/-- If `log ψ` is strictly convex on `[0, ∞)`, then `ψ(x) ψ(y) < ψ(x + y)` for `x, y > 0`. -/
theorem mul_lt_toFun_add_of_strictConvexOn (g : BivariateGenerator)
    (hpos : ∀ t, 0 ≤ t → 0 < g.toFun t)
    (hf : StrictConvexOn ℝ (Ici 0) (fun t => Real.log (g.toFun t))) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) : g.toFun x * g.toFun y < g.toFun (x + y) := by
  have h := lt_add_of_strictConvexOn hf (by simp [g.toFun_zero]) hx hy
  rw [← Real.log_mul (hpos x hx.le).ne' (hpos y hy.le).ne'] at h
  exact (Real.log_lt_log_iff (mul_pos (hpos x hx.le) (hpos y hy.le))
    (hpos _ (add_pos hx hy).le)).mp h

/-- If `log ψ` is strictly concave on `[0, ∞)`, then `ψ(x + y) < ψ(x) ψ(y)` for `x, y > 0`. -/
theorem toFun_add_lt_mul_of_strictConcaveOn (g : BivariateGenerator)
    (hpos : ∀ t, 0 ≤ t → 0 < g.toFun t)
    (hf : StrictConcaveOn ℝ (Ici 0) (fun t => Real.log (g.toFun t))) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) : g.toFun (x + y) < g.toFun x * g.toFun y := by
  have h := lt_add_of_strictConvexOn hf.neg (by simp [g.toFun_zero]) hx hy
  simp only [Pi.neg_apply] at h
  have h' : Real.log (g.toFun x) + Real.log (g.toFun y) > Real.log (g.toFun (x + y)) := by
    linarith
  rw [← Real.log_mul (hpos x hx.le).ne' (hpos y hy.le).ne'] at h'
  exact (Real.log_lt_log_iff (hpos _ (add_pos hx hy).le)
    (mul_pos (hpos x hx.le) (hpos y hy.le))).mp h'

/-- A generator with strictly log-convex inverse generator yields a PQD copula which is not
NQD. -/
theorem isPQD_and_not_isNQD_of_strictConvexOn (g : BivariateGenerator)
    (hpos : ∀ t, 0 ≤ t → 0 < g.toFun t)
    (hf : StrictConvexOn ℝ (Ici 0) (fun t => Real.log (g.toFun t))) :
    g.copula.IsPQD ∧ ¬ g.copula.IsNQD := by
  refine ⟨isPQD_of_psi g fun x y hx hy => ?_, not_isNQD_of_psi g (x := 1) (y := 1) zero_le_one
    zero_le_one (mul_lt_toFun_add_of_strictConvexOn g hpos hf one_pos one_pos)⟩
  rcases hx.eq_or_lt with rfl | hx'
  · simp [g.toFun_zero]
  rcases hy.eq_or_lt with rfl | hy'
  · simp [g.toFun_zero]
  exact (mul_lt_toFun_add_of_strictConvexOn g hpos hf hx' hy').le

/-- A generator with strictly log-concave inverse generator yields an NQD copula which is not
PQD. -/
theorem isNQD_and_not_isPQD_of_strictConcaveOn (g : BivariateGenerator)
    (hpos : ∀ t, 0 ≤ t → 0 < g.toFun t)
    (hf : StrictConcaveOn ℝ (Ici 0) (fun t => Real.log (g.toFun t))) :
    g.copula.IsNQD ∧ ¬ g.copula.IsPQD := by
  refine ⟨isNQD_of_psi g fun x y hx hy => ?_, not_isPQD_of_psi g (x := 1) (y := 1) zero_le_one
    zero_le_one (toFun_add_lt_mul_of_strictConcaveOn g hpos hf one_pos one_pos)⟩
  rcases hx.eq_or_lt with rfl | hx'
  · simp [g.toFun_zero]
  rcases hy.eq_or_lt with rfl | hy'
  · simp [g.toFun_zero]
  exact (toFun_add_lt_mul_of_strictConcaveOn g hpos hf hx' hy').le

end BivariateGenerator

end ProbabilityTheory.Copula
