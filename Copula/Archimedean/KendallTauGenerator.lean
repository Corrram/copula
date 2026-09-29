/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.KendallTau
import Mathlib.Analysis.Convex.Continuous

/-! # Kendall's tau from a differentiable generator

Nelsen, *An Introduction to Copulas*, second edition, Corollary 5.1.4 states
`τ_C = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt` in terms of the generator `φ`. The library's
`BivariateGenerator.IsC1.kendallTau_eq` requires a continuous derivative of the *inverse*
generator `ψ`. This file derives that hypothesis from the generator itself:

* `BivariateGenerator.continuousAt_toFun`: `ψ` is continuous on `(0, ∞)` (it is convex);
* `BivariateGenerator.IsC1.of_invFunReal`: if `φ` has a continuous nonvanishing derivative `φ'`
  on `(0, 1)`, then `ψ` is `C¹` on its positivity region with `ψ'(s) = 1 / φ'(ψ(s))`
  (inverse function rule);
* `BivariateGenerator.kendallTau_eq_of_hasDerivAt`: then `τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt`, for any
  explicit real function `φ` agreeing with the generator on `(0, 1)`.

This is the form used for the families of Nelsen's Table 4.1 in
`Copula.Archimedean.KendallTauTable`.
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- The inverse generator is continuous on `(0, ∞)`, being convex on `[0, ∞)`. -/
theorem continuousAt_toFun (g : BivariateGenerator) {s : ℝ} (hs : 0 < s) :
    ContinuousAt g.toFun s := by
  have h := g.convex.continuousOn_interior
  rw [interior_Ici] at h
  exact h.continuousAt (Ioi_mem_nhds hs)

/-- `φ(ψ(s)) = s` for the real extension of the generator, where `ψ(s) > 0`. -/
theorem invFunReal_toFun (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) (hpos : 0 < g.toFun s) :
    g.invFunReal (g.toFun s) = s := by
  rw [invFunReal, projIcc_of_mem _ ⟨g.nonneg s hs, g.toFun_le_one hs⟩]
  exact g.invFun_toI hs hpos

/-- Inverse function rule: if the generator has a continuous nonvanishing derivative `φ'` on
`(0, 1)`, then the inverse generator is `C¹` on its positivity region, with
`ψ'(s) = 1 / φ'(ψ(s))`. -/
theorem IsC1.of_invFunReal {g : BivariateGenerator} {φ' : ℝ → ℝ}
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g.invFunReal (φ' t) t)
    (hc : ContinuousOn φ' (Ioo 0 1)) (hne : ∀ t ∈ Ioo (0 : ℝ) 1, φ' t ≠ 0) :
    g.IsC1 (fun s => (φ' (g.toFun s))⁻¹) where
  hasDerivAt s hs hpos := by
    have hmem : g.toFun s ∈ Ioo (0 : ℝ) 1 := ⟨hpos, g.toFun_lt_one hs⟩
    apply HasDerivAt.of_local_left_inverse (g.continuousAt_toFun hs) (hd _ hmem) (hne _ hmem)
    have hev : ∀ᶠ y in 𝓝 s, 0 < g.toFun y :=
      (g.continuousAt_toFun hs).eventually (lt_mem_nhds hpos)
    filter_upwards [hev, Ioi_mem_nhds hs] with y hy hy0
    exact g.invFunReal_toFun (le_of_lt hy0) hy
  continuousAt s hs hpos := by
    have hmem : g.toFun s ∈ Ioo (0 : ℝ) 1 := ⟨hpos, g.toFun_lt_one hs⟩
    have h1 : ContinuousAt φ' (g.toFun s) := hc.continuousAt (Ioo_mem_nhds hmem.1 hmem.2)
    exact (h1.comp (g.continuousAt_toFun hs)).inv₀ (hne _ hmem)

/-- Nelsen, Corollary 5.1.4 in terms of the generator: if `φ` has a continuous nonvanishing
derivative `φ'` on `(0, 1)`, then `τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt`. -/
theorem kendallTau_eq_of_invFunReal {g : BivariateGenerator} {φ' : ℝ → ℝ}
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g.invFunReal (φ' t) t)
    (hc : ContinuousOn φ' (Ioo 0 1)) (hne : ∀ t ∈ Ioo (0 : ℝ) 1, φ' t ≠ 0) :
    g.copula.kendallTau = 1 + 4 * ∫ t in (0 : ℝ)..1, g.invFunReal t / φ' t := by
  rw [(IsC1.of_invFunReal hd hc hne).kendallTau_eq]
  congr 2
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le zero_le_one] at ht
  simp only [IsC1.toFun_invFunReal ht.1 ht.2, div_eq_mul_inv]

/-- Nelsen, Corollary 5.1.4 for an explicit generator: if `φ` agrees with the generator on
`(0, 1)` and has a continuous nonvanishing derivative `φ'` there, then
`τ = 1 + 4 ∫₀¹ φ(t) / φ'(t) dt`. -/
theorem kendallTau_eq_of_hasDerivAt {g : BivariateGenerator} {φ φ' : ℝ → ℝ}
    (heq : ∀ t ∈ Ioo (0 : ℝ) 1, g.invFunReal t = φ t)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (φ' t) t)
    (hc : ContinuousOn φ' (Ioo 0 1)) (hne : ∀ t ∈ Ioo (0 : ℝ) 1, φ' t ≠ 0) :
    g.copula.kendallTau = 1 + 4 * ∫ t in (0 : ℝ)..1, φ t / φ' t := by
  have hd' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g.invFunReal (φ' t) t := by
    intro t ht
    refine (hd t ht).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact heq y hy
  rw [kendallTau_eq_of_invFunReal hd' hc hne]
  congr 2
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by simp only [heq t ht]

end BivariateGenerator

end ProbabilityTheory.Copula
