/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.TailDependence.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Tail dependence from one-sided derivatives of the diagonal

The diagonal may be represented by any real function agreeing on `[0,1]`.
Only a derivative within this interval is required at the relevant endpoint.
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- The right derivative of the diagonal at zero is the lower tail coefficient. -/
theorem hasLowerTailDependence_of_hasDerivWithinAt {C : Copula 2} {f : ℝ → ℝ} {l : ℝ}
    (hf : ∀ t : I, f t = C.diagonal t)
    (hd : HasDerivWithinAt f l (Icc 0 1) 0) : C.HasLowerTailDependence l := by
  have ht : Tendsto (fun t : I => (t : ℝ)) (𝓝[>] (0 : I))
      (𝓝[Icc 0 1 \ {0}] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t)] with t ht
    exact ⟨t.property, by simpa using ne_of_gt (show (0 : ℝ) < t from ht)⟩
  have hzero : f 0 = 0 := by simpa using hf 0
  have h := (hasDerivWithinAt_iff_tendsto_slope.1 hd).comp ht
  change Tendsto (fun t : I => C.diagonal t / (t : ℝ)) (𝓝[>] (0 : I)) (𝓝 l)
  simpa only [Function.comp_def, slope_def_field, hzero, sub_zero, hf] using h

/-- Two minus the left derivative at one is the upper tail coefficient. -/
theorem hasUpperTailDependence_of_hasDerivWithinAt {C : Copula 2} {f : ℝ → ℝ} {l : ℝ}
    (hf : ∀ t : I, f t = C.diagonal t)
    (hd : HasDerivWithinAt f l (Icc 0 1) 1) : C.HasUpperTailDependence (2 - l) := by
  rw [hasUpperTailDependence_iff_tendsto_one]
  have ht : Tendsto (fun t : I => (t : ℝ)) (𝓝[<] (1 : I))
      (𝓝[Icc 0 1 \ {1}] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[<] (1 : I), t < 1)] with t ht
    exact ⟨t.property, by simpa using ne_of_lt (show (t : ℝ) < 1 from ht)⟩
  have hone : f 1 = 1 := by simpa using hf 1
  have h := (tendsto_const_nhds (x := (2 : ℝ))).sub
    ((hasDerivWithinAt_iff_tendsto_slope.1 hd).comp ht)
  apply h.congr'
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[<] (1 : I), t < 1)] with t ht
  simp only [Function.comp_def, slope_def_field, hone, hf]
  have hn : (t : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ht)
  have hn' : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht)
  field_simp [hn, hn']
  ring

end ProbabilityTheory.Copula
