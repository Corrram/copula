/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.LevelCurves
import Copula.Archimedean.Diagonal
import Copula.TailDependence.Derivative

/-! # Tail dependence of Archimedean copulas via the generator

Nelsen, *An Introduction to Copulas*, second edition, Corollary 5.4.3: for an Archimedean
copula with inverse generator `ψ = φ^[-1]`,

* `λ_L = lim_{x → ∞} ψ(2x) / ψ(x)` for a strict generator
  (`BivariateGenerator.hasLowerTailDependence_of_tendsto`), and `λ_L = 0` for a non-strict one
  (`BivariateGenerator.hasLowerTailDependence_zero_of_not_isStrict`);
* `λ_U = 2 − lim_{x → 0+} (1 − ψ(2x)) / (1 − ψ(x))`
  (`BivariateGenerator.hasUpperTailDependence_of_tendsto`). This comes from the left derivative
  of the diagonal at one, `δ'(1⁻) = lim_{x → 0+} (1 − ψ(2x)) / (1 − ψ(x))`
  (`BivariateGenerator.hasDerivWithinAt_diagonal_one`).

If `ψ` has a finite nonzero right derivative at `0` (equivalently `φ'(1⁻) ≠ 0`), the limit is
`2`, so `δ'(1⁻) = 2` and `λ_U = 0` (`BivariateGenerator.hasUpperTailDependence_zero_of_hasDerivWithinAt`;
Nelsen, Section 5.4). No differentiability is assumed in
the general statements. The limits along the generator are transported to the tail ratios of
`Copula.TailDependence` by the facts `φ(t) → ∞` as `t → 0+` for strict generators
(`BivariateGenerator.IsStrict.tendsto_invFun_atTop`) and `φ(t) → 0+` as `t → 1-`
(`BivariateGenerator.tendsto_invFunReal_one`).
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- `ψ(s) < 1` for `s > 0`. -/
theorem toFun_lt_one (g : BivariateGenerator) {s : ℝ} (hs : 0 < s) : g.toFun s < 1 := by
  rcases (g.nonneg s hs.le).lt_or_eq with h | h
  · have := g.toFun_lt_of_lt le_rfl hs h
    rwa [g.toFun_zero] at this
  · rw [← h]
    exact one_pos

/-- For a strict generator `φ(t) → ∞` as `t → 0+`. -/
theorem IsStrict.tendsto_invFun_atTop {g : BivariateGenerator} (hg : g.IsStrict) :
    Tendsto (fun t : I => g.invFun t) (𝓝[>] (0 : I)) atTop := by
  refine tendsto_atTop.2 fun M => ?_
  have hM : 0 ≤ max M 0 := le_max_right _ _
  have hpos := hg _ hM
  have ht0 : g.toI hM ≠ 0 := g.toI_ne_zero hM hpos
  have hlt : (0 : I) < g.toI hM := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm ht0)
  filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
  have htne : t ≠ 0 := ht.1.ne'
  by_contra hlt'
  push Not at hlt'
  have h := g.antitone_nonneg (g.inv_nonneg t htne) hM (hlt'.le.trans (le_max_left _ _))
  rw [g.right_inv t htne] at h
  exact absurd (show (t : ℝ) < g.toFun (max M 0) from ht.2) (not_lt.mpr h)

/-- `φ(x) → 0+` as `x → 1` within `[0, 1] \ {1}`. -/
theorem tendsto_invFunReal_one (g : BivariateGenerator) :
    Tendsto g.invFunReal (𝓝[Icc 0 1 \ {1}] (1 : ℝ)) (𝓝[>] 0) := by
  have hpos : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), x ∈ Icc (0 : ℝ) 1 \ {1} := self_mem_nhdsWithin
    have h2 : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), (0 : ℝ) < x :=
      nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)
    filter_upwards [h1, h2] with x hx hx0
    exact ⟨hx0, lt_of_le_of_ne hx.1.2 hx.2⟩
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, ?_⟩
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun ε hε => ?_⟩
    · filter_upwards [hpos] with x hx
      let u : I := ⟨x, hx.1.le, hx.2.le⟩
      have hu : u ≠ 0 := fun h => hx.1.ne' (congrArg Subtype.val h)
      have : g.invFunReal x = g.invFun u := g.invFunReal_coe u
      rw [this]
      exact ha.trans_le (g.inv_nonneg u hu)
    · have hψ := g.toFun_lt_one hε
      have hnb : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), g.toFun ε < x :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hψ)
      filter_upwards [hpos, hnb] with x hx hxε
      let u : I := ⟨x, hx.1.le, hx.2.le⟩
      have hu : u ≠ 0 := fun h => hx.1.ne' (congrArg Subtype.val h)
      have : g.invFunReal x = g.invFun u := g.invFunReal_coe u
      rw [this]
      by_contra hle
      push Not at hle
      have h := g.antitone_nonneg hε.le (g.inv_nonneg u hu) hle
      rw [g.right_inv u hu] at h
      exact absurd hxε (not_lt.mpr h)
  · filter_upwards [hpos] with x hx
    let u : I := ⟨x, hx.1.le, hx.2.le⟩
    have hu : u ≠ 0 := fun h => hx.1.ne' (congrArg Subtype.val h)
    have hu1 : u ≠ 1 := fun h => hx.2.ne (congrArg Subtype.val h)
    have : g.invFunReal x = g.invFun u := g.invFunReal_coe u
    rw [mem_Ioi, this]
    exact g.invFun_pos hu hu1

/-- The lower tail ratio along the generator: `δ(t) / t = ψ(2φ(t)) / ψ(φ(t))`. -/
theorem lowerTailRatio_copula (g : BivariateGenerator) {t : I} (ht : t ≠ 0) :
    g.copula.lowerTailRatio t = g.toFun (2 * g.invFun t) / g.toFun (g.invFun t) := by
  rw [lowerTailRatio, g.diagonal_copula ht, g.right_inv t ht]

/-- Nelsen, Corollary 5.4.3 (lower tail): for a strict generator,
`λ_L = lim_{x → ∞} ψ(2x) / ψ(x)` whenever this limit exists. -/
theorem hasLowerTailDependence_of_tendsto {g : BivariateGenerator} (hg : g.IsStrict) {l : ℝ}
    (h : Tendsto (fun x => g.toFun (2 * x) / g.toFun x) atTop (𝓝 l)) :
    g.copula.HasLowerTailDependence l := by
  unfold HasLowerTailDependence
  refine (h.comp hg.tendsto_invFun_atTop).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (g.lowerTailRatio_copula (ne_of_gt ht)).symm

/-- A non-strict generator has no lower tail dependence (Nelsen, Section 5.4). -/
theorem hasLowerTailDependence_zero_of_not_isStrict {g : BivariateGenerator}
    (hg : ¬ g.IsStrict) : g.copula.HasLowerTailDependence 0 := by
  obtain ⟨t₀, ht₀, hz⟩ := g.exists_diagonal_eq_zero hg
  have hlt : (0 : I) < t₀ := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm ht₀)
  unfold HasLowerTailDependence
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
  rw [lowerTailRatio, g.diagonal_eq_cdf, hz t ht.2.le, zero_div]

/-- Nelsen, Corollary 5.4.3 (the diagonal at one): if
`(1 − ψ(2x)) / (1 − ψ(x)) → m` as `x → 0+`, the diagonal has left derivative `m` at one. -/
theorem hasDerivWithinAt_diagonal_one (g : BivariateGenerator) {m : ℝ}
    (h : Tendsto (fun x => (1 - g.toFun (2 * x)) / (1 - g.toFun x)) (𝓝[>] 0) (𝓝 m)) :
    HasDerivWithinAt (fun x => g.copula.diagonal (projIcc 0 1 zero_le_one x)) m
      (Icc 0 1) 1 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine (h.comp g.tendsto_invFunReal_one).congr' ?_
  have hpos : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), x ∈ Icc (0 : ℝ) 1 \ {1} := self_mem_nhdsWithin
    have h2 : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), (0 : ℝ) < x :=
      nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)
    filter_upwards [h1, h2] with x hx hx0
    exact ⟨hx0, lt_of_le_of_ne hx.1.2 hx.2⟩
  filter_upwards [hpos] with x hx
  let u : I := ⟨x, hx.1.le, hx.2.le⟩
  have hu : u ≠ 0 := fun h => hx.1.ne' (congrArg Subtype.val h)
  have hxu : g.invFunReal x = g.invFun u := g.invFunReal_coe u
  have hpx : projIcc 0 1 zero_le_one x = u := projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩
  have hp1 : projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := projIcc_right zero_le_one
  have hd1 : g.copula.diagonal 1 = 1 := by
    rw [g.diagonal_eq_cdf, cdf_one_left]
    rfl
  simp only [Function.comp_apply, slope_def_field, hxu, hpx, hp1, hd1,
    g.diagonal_copula hu]
  have hr : g.toFun (g.invFun u) = x := g.right_inv u hu
  rw [hr]
  have hn : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.ne
  have hn' : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.ne'
  field_simp
  ring

/-- Nelsen, Corollary 5.4.3 (upper tail): `λ_U = 2 − lim_{x → 0+} (1 − ψ(2x)) / (1 − ψ(x))`
whenever this limit exists. -/
theorem hasUpperTailDependence_of_tendsto (g : BivariateGenerator) {m : ℝ}
    (h : Tendsto (fun x => (1 - g.toFun (2 * x)) / (1 - g.toFun x)) (𝓝[>] 0) (𝓝 m)) :
    g.copula.HasUpperTailDependence (2 - m) :=
  hasUpperTailDependence_of_hasDerivWithinAt (fun t => by rw [projIcc_val])
    (g.hasDerivWithinAt_diagonal_one h)

/-- If `ψ` has a finite nonzero right derivative at `0`, then
`(1 − ψ(2x)) / (1 − ψ(x)) → 2` as `x → 0+`. -/
theorem tendsto_upperRatio_of_hasDerivWithinAt (g : BivariateGenerator) {d : ℝ}
    (hd : HasDerivWithinAt g.toFun d (Ici 0) 0) (hd0 : d ≠ 0) :
    Tendsto (fun x => (1 - g.toFun (2 * x)) / (1 - g.toFun x)) (𝓝[>] 0) (𝓝 2) := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope.1 hd)
  have hfilt : 𝓝[Ici (0 : ℝ) \ {0}] (0 : ℝ) = 𝓝[>] 0 := by
    congr 1
    ext x
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hfilt] at hs
  have h2 : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos two_pos (show (0 : ℝ) < x from hx)
  have hA := (hs.comp h2).const_mul 2
  have hq := hA.div hs hd0
  have hlim : 2 * d / d = 2 := by field_simp
  rw [hlim] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [Pi.div_apply, Function.comp_apply]
  rw [slope_def_field, slope_def_field, sub_zero, sub_zero, g.toFun_zero]
  by_cases hB : g.toFun x - 1 = 0
  · have hB' : 1 - g.toFun x = 0 := by linarith
    rw [hB, hB', zero_div, div_zero, div_zero]
  · have hB' : 1 - g.toFun x ≠ 0 := fun h => hB (by linarith)
    field_simp
    ring

/-- `δ'(1⁻) = 2` when `ψ` has a finite nonzero right derivative at `0`. -/
theorem hasDerivWithinAt_diagonal_one_two (g : BivariateGenerator) {d : ℝ}
    (hd : HasDerivWithinAt g.toFun d (Ici 0) 0) (hd0 : d ≠ 0) :
    HasDerivWithinAt (fun x => g.copula.diagonal (projIcc 0 1 zero_le_one x)) 2
      (Icc 0 1) 1 :=
  g.hasDerivWithinAt_diagonal_one (g.tendsto_upperRatio_of_hasDerivWithinAt hd hd0)

/-- A finite nonzero right derivative of `ψ` at `0` (equivalently `φ'(1⁻) ≠ 0`) excludes upper
tail dependence. -/
theorem hasUpperTailDependence_zero_of_hasDerivWithinAt (g : BivariateGenerator) {d : ℝ}
    (hd : HasDerivWithinAt g.toFun d (Ici 0) 0) (hd0 : d ≠ 0) :
    g.copula.HasUpperTailDependence 0 := by
  have h := g.hasUpperTailDependence_of_tendsto (g.tendsto_upperRatio_of_hasDerivWithinAt hd hd0)
  rwa [sub_self] at h

end BivariateGenerator

end ProbabilityTheory.Copula
