/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Archimax
import Copula.Archimedean.MultivariateConverse
import Copula.Families.Gumbel

/-! # Tail coefficients of Archimax copulas under regular variation

`Copula.ExtremeValue.Archimax` expresses the tail coefficients of the Archimax copula
`C_{ψ,A}(u,v) = ψ(ℓ_A(φ(u), φ(v)))` through limits of ratios of the inverse generator `ψ`
(`κ = 2A(1/2)`):

`λ_U = 2 - lim_{x→0+} (1 - ψ(κx))/(1 - ψ(x))`,  `λ_L = lim_{x→∞} ψ(κx)/ψ(x)` (strict generators).

Here we evaluate these limits under the regular-variation hypotheses of Capéraà, Fougères and
Genest (2000, Section 4), stated on the generator `φ`:

* if `φ(1 - at)/φ(1 - t) → a^m` as `t → 0+` for every `a > 0` (`φ(1 - 1/x)` regularly varying
  with index `-m` at `∞`, `m > 0`), then `λ_U = 2 - (2A(1/2))^{1/m}`
  (`hasUpperTailDependence_archimaxCopula_of_regularVariation`);
* if `g` is strict and `φ(at)/φ(t) → a^{-k}` as `t → 0+` for every `a > 0` (`φ` regularly varying
  at `0` with index `-k`, `k > 0`), then `λ_L = (2A(1/2))^{-1/k}`
  (`hasLowerTailDependence_archimaxCopula_of_regularVariation`);
* a non-strict generator gives `λ_L = 0` as soon as `A(1/2) > 1/2`
  (`hasLowerTailDependence_archimaxCopula_zero_of_not_isStrict`); the excluded case
  `A(1/2) = 1/2` forces `A(t) = max(t, 1-t)` and `C = M`.

The passage from `φ` to `ψ = φ^{-1}` is the classical inversion of regular variation for monotone
functions (`tendsto_inverse_ratio_of_regularVariation`, proved by a sandwich argument, no
uniform convergence theorem needed). The hypotheses directly on `ψ` are
`hasUpperTailDependence_archimaxCopula_of_toFun_ratio` and
`hasLowerTailDependence_archimaxCopula_of_toFun_ratio`.

Examples: Gumbel's generator `φ(t) = (-log t)^θ` has `m = θ`; for it we verify the hypothesis
and obtain `λ_U = 2 - (2A(1/2))^{1/θ}` for every Pickands function
(`hasUpperTailDependence_archimaxCopula_gumbelGenerator`; `A ≡ 1` recovers Gumbel's
`2 - 2^{1/θ}`). Clayton's generator `φ(t) = (t^{-θ} - 1)/θ` has `k = θ`, so `A ≡ 1` gives the
classical `λ_L = 2^{-1/θ}`.

References: P. Capéraà, A.-L. Fougères and C. Genest, *Bivariate distributions with given
extreme value attractor*, J. Multivariate Anal. 72 (2000) 30–49, Section 4; N. H. Bingham,
C. M. Goldie and J. L. Teugels, *Regular Variation* (1987), Theorem 1.5.12 (inverses).
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

theorem tendsto_const_mul_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => a * x) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun x : ℝ => a * x) (𝓝 0) (𝓝 (a * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos ha (show (0 : ℝ) < x from hx)

/-- **Inversion of regular variation at `0+`.** Let `F` be strictly increasing and positive on
`(0, δ)` with `F(at)/F(t) → a^m` (`t → 0+`) for every `a > 0`, and let `G(y) → 0+` be a right
inverse of `F` near `0` (`F(G(y)) = y`). Then `G(sy)/G(y) → s^{1/m}` for every `s > 0`. -/
theorem tendsto_inverse_ratio_of_regularVariation {F G : ℝ → ℝ} {m δ : ℝ} (hm : 0 < m)
    (hδ : 0 < δ) (hFmono : StrictMonoOn F (Ioo 0 δ)) (hFpos : ∀ t ∈ Ioo 0 δ, 0 < F t)
    (hF : ∀ a, 0 < a → Tendsto (fun t => F (a * t) / F t) (𝓝[>] 0) (𝓝 (a ^ m)))
    (hG : Tendsto G (𝓝[>] 0) (𝓝[>] 0)) (hFG : ∀ᶠ y in 𝓝[>] (0 : ℝ), F (G y) = y)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun y => G (s * y) / G y) (𝓝[>] 0) (𝓝 (s ^ (1 / m))) := by
  have hsy := tendsto_const_mul_nhdsGT_zero hs
  have hG1 : ∀ᶠ y in 𝓝[>] (0 : ℝ), G y ∈ Ioo 0 δ := hG (Ioo_mem_nhdsGT hδ)
  have hG2 : ∀ᶠ y in 𝓝[>] (0 : ℝ), G (s * y) ∈ Ioo 0 δ := hsy.eventually hG1
  have hFGs : ∀ᶠ y in 𝓝[>] (0 : ℝ), F (G (s * y)) = s * y := hsy.eventually hFG
  have hpow : ∀ b : ℝ, 0 ≤ b → (b ^ m < s ↔ b < s ^ (1 / m)) := by
    intro b hb
    constructor
    · intro h
      have := Real.rpow_lt_rpow (Real.rpow_nonneg hb m) h (by positivity : 0 < 1 / m)
      rwa [← Real.rpow_mul hb, mul_one_div_cancel hm.ne', Real.rpow_one] at this
    · intro h
      have := Real.rpow_lt_rpow hb h hm
      rwa [← Real.rpow_mul hs.le, one_div_mul_cancel hm.ne', Real.rpow_one] at this
  have hsmall : ∀ b, 0 < b → ∀ᶠ t in 𝓝[>] (0 : ℝ), b * t ∈ Ioo 0 δ ∧ t ∈ Ioo 0 δ := fun b hb =>
    ((tendsto_const_mul_nhdsGT_zero hb).eventually (Ioo_mem_nhdsGT hδ)).and
      (Ioo_mem_nhdsGT hδ)
  rw [tendsto_order]
  constructor
  · intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [hG1, hG2] with y h1 h2
      exact lt_of_le_of_lt hb0 (div_pos h2.1 h1.1)
    have hbm : b ^ m < s := (hpow b hb0.le).2 hb
    have hev := hG.eventually (((hF b hb0).eventually (gt_mem_nhds hbm)).and (hsmall b hb0))
    filter_upwards [hev, hG1, hG2, hFG, hFGs] with y ⟨h1, h2, h3⟩ h4 h5 h6 h7
    have hlt : F (b * G y) < F (G (s * y)) := by
      rw [h7]
      have := (div_lt_iff₀ (hFpos _ h3)).1 h1
      rw [h6] at this
      linarith
    have := (hFmono.lt_iff_lt h2 h5).1 hlt
    rw [lt_div_iff₀ h4.1]
    linarith
  · intro B hB
    have hB0 : 0 < B := lt_of_le_of_lt (Real.rpow_nonneg hs.le _) hB
    have hBm : s < B ^ m := by
      by_contra h
      push Not at h
      rcases h.lt_or_eq with h | h
      · exact absurd ((hpow B hB0.le).1 h) (not_lt.2 hB.le)
      · have : s ^ (1 / m) = (B ^ m) ^ (1 / m) := by rw [h]
        rw [← Real.rpow_mul hB0.le, mul_one_div_cancel hm.ne', Real.rpow_one] at this
        exact absurd this hB.ne
    have hev := hG.eventually (((hF B hB0).eventually (lt_mem_nhds hBm)).and (hsmall B hB0))
    filter_upwards [hev, hG1, hG2, hFG, hFGs] with y ⟨h1, h2, h3⟩ h4 h5 h6 h7
    have hlt : F (G (s * y)) < F (B * G y) := by
      rw [h7]
      have := (lt_div_iff₀ (hFpos _ h3)).1 h1
      rw [h6] at this
      linarith
    have := (hFmono.lt_iff_lt h5 h2).1 hlt
    rw [div_lt_iff₀ h4.1]
    linarith

namespace BivariateGenerator

variable (g : BivariateGenerator) {A : ℝ → ℝ}

/-- `ψ(x) → 1` as `x → 0+`. -/
theorem tendsto_toFun_zero : Tendsto g.toFun (𝓝[>] 0) (𝓝 1) := by
  have h := g.continuousWithinAt_toFun_zero
  rw [ContinuousWithinAt, g.toFun_zero] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- For a strict generator, `ψ(x) → 0` as `x → ∞`. -/
theorem tendsto_toFun_atTop : Tendsto g.toFun atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_ge_atTop 0] with x hx
    exact ha.trans_le (g.nonneg x hx)
  · set m : ℝ := min (ε / 2) (1 / 2)
    have hm0 : 0 < m := lt_min (by linarith) (by norm_num)
    have hm1 : m ≤ 1 / 2 := min_le_right _ _
    have hmε : m < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let u : I := ⟨m, hm0.le, by linarith⟩
    have hu : u ≠ 0 := fun h => hm0.ne' (congrArg Subtype.val h)
    filter_upwards [eventually_ge_atTop (g.invFun u)] with x hx
    have h := g.antitone_nonneg (g.inv_nonneg u hu) ((g.inv_nonneg u hu).trans hx) hx
    rw [g.right_inv u hu] at h
    exact lt_of_le_of_lt h hmε

/-- `φ(ψ(x)) = x` whenever `ψ(x) > 0`, in terms of `invFunReal`. -/
theorem invFunReal_toFun {x : ℝ} (hx : 0 ≤ x) (hpos : 0 < g.toFun x) :
    g.invFunReal (g.toFun x) = x := by
  rw [← g.coe_toI hx, g.invFunReal_coe, g.invFun_toI hx hpos]

/-- **Upper tail inversion**: if `φ(1 - at)/φ(1 - t) → a^m` as `t → 0+` for all `a > 0`, then
`(1 - ψ(sx))/(1 - ψ(x)) → s^{1/m}` as `x → 0+` for all `s > 0`. -/
theorem tendsto_one_sub_toFun_ratio {m : ℝ} (hm : 0 < m)
    (hφ : ∀ a, 0 < a →
      Tendsto (fun t => g.invFunReal (1 - a * t) / g.invFunReal (1 - t)) (𝓝[>] 0) (𝓝 (a ^ m)))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x => (1 - g.toFun (s * x)) / (1 - g.toFun x)) (𝓝[>] 0) (𝓝 (s ^ (1 / m))) := by
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, (1 - t) ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hFpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g.invFunReal (1 - t) := by
    intro t ht
    let u : I := ⟨1 - t, hmem t ht⟩
    have hu0 : u ≠ 0 := fun h => by
      have := congrArg Subtype.val h; simp only [u, Set.Icc.coe_zero] at this; linarith [ht.2]
    have hu1 : u ≠ 1 := fun h => by
      have := congrArg Subtype.val h; simp only [u, Set.Icc.coe_one] at this; linarith [ht.1]
    rw [show (1 - t) = (u : ℝ) from rfl, g.invFunReal_coe]
    exact g.invFun_pos hu0 hu1
  have hFmono : StrictMonoOn (fun t => g.invFunReal (1 - t)) (Ioo 0 1) := by
    intro t ht t' ht' htt'
    let u : I := ⟨1 - t', hmem t' ht'⟩
    let v : I := ⟨1 - t, hmem t ht⟩
    have hu0 : u ≠ 0 := fun h => by
      have := congrArg Subtype.val h; simp only [u, Set.Icc.coe_zero] at this; linarith [ht'.2]
    have huv : u < v := by
      change (1 - t' : ℝ) < 1 - t
      linarith
    change g.invFunReal ((v : I) : ℝ) < g.invFunReal ((u : I) : ℝ)
    rw [g.invFunReal_coe, g.invFunReal_coe]
    exact g.invFun_lt_of_lt hu0 huv
  have hG : Tendsto (fun x => 1 - g.toFun x) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · simpa using (g.tendsto_toFun_zero).const_sub (1 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.2 (g.toFun_lt_one hx)
  have hFG : ∀ᶠ x in 𝓝[>] (0 : ℝ), g.invFunReal (1 - (1 - g.toFun x)) = x := by
    filter_upwards [self_mem_nhdsWithin, g.tendsto_toFun_zero.eventually (lt_mem_nhds one_pos)]
      with x hx hpos
    rw [sub_sub_cancel]
    exact g.invFunReal_toFun (le_of_lt hx) hpos
  exact tendsto_inverse_ratio_of_regularVariation (F := fun t => g.invFunReal (1 - t)) hm
    one_pos hFmono hFpos hφ hG hFG hs

/-- **Lower tail inversion**: for a strict generator with `φ(at)/φ(t) → a^{-k}` as `t → 0+` for
all `a > 0`, `ψ(sx)/ψ(x) → s^{-1/k}` as `x → ∞` for all `s > 0`. -/
theorem IsStrict.tendsto_toFun_ratio_atTop {g : BivariateGenerator} (hg : g.IsStrict) {k : ℝ}
    (hk : 0 < k)
    (hφ : ∀ a, 0 < a →
      Tendsto (fun t => g.invFunReal (a * t) / g.invFunReal t) (𝓝[>] 0) (𝓝 (a ^ (-k))))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x => g.toFun (s * x) / g.toFun x) atTop (𝓝 (s ^ (-1 / k))) := by
  have hFpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < g.invFunReal t := by
    intro t ht
    let u : I := ⟨t, ht.1.le, ht.2.le⟩
    have hu0 : u ≠ 0 := fun h => ht.1.ne' (congrArg Subtype.val h)
    have hu1 : u ≠ 1 := fun h => ht.2.ne (congrArg Subtype.val h)
    rw [show t = (u : ℝ) from rfl, g.invFunReal_coe]
    exact g.invFun_pos hu0 hu1
  have hFmono : StrictMonoOn (fun t => 1 / g.invFunReal t) (Ioo 0 1) := by
    intro t ht t' ht' htt'
    let u : I := ⟨t, ht.1.le, ht.2.le⟩
    let v : I := ⟨t', ht'.1.le, ht'.2.le⟩
    have hu0 : u ≠ 0 := fun h => ht.1.ne' (congrArg Subtype.val h)
    have hlt : g.invFunReal t' < g.invFunReal t := by
      rw [show t = (u : ℝ) from rfl, show t' = (v : ℝ) from rfl, g.invFunReal_coe,
        g.invFunReal_coe]
      exact g.invFun_lt_of_lt hu0 htt'
    exact one_div_lt_one_div_of_lt (hFpos t' ht') hlt
  have hF : ∀ a, 0 < a → Tendsto (fun t => (1 / g.invFunReal (a * t)) / (1 / g.invFunReal t))
      (𝓝[>] 0) (𝓝 (a ^ k)) := by
    intro a ha
    have h := (hφ a ha).inv₀ (Real.rpow_pos_of_pos ha _).ne'
    rw [Real.rpow_neg ha.le, inv_inv] at h
    refine h.congr fun t => ?_
    simp only [one_div, inv_div_inv, inv_div]
  have hpos0 : ∀ y : ℝ, 0 < y → 0 < g.toFun y⁻¹ := fun y hy => hg _ (inv_pos.2 hy).le
  have hG : Tendsto (fun y : ℝ => g.toFun y⁻¹) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨g.tendsto_toFun_atTop.comp tendsto_inv_nhdsGT_zero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hpos0 y hy
  have hFG : ∀ᶠ y in 𝓝[>] (0 : ℝ), 1 / g.invFunReal (g.toFun y⁻¹) = y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [g.invFunReal_toFun (inv_pos.2 hy).le (hpos0 y hy), one_div, inv_inv]
  have h := tendsto_inverse_ratio_of_regularVariation (F := fun t => 1 / g.invFunReal t)
    (G := fun y => g.toFun y⁻¹) hk one_pos hFmono
    (fun t ht => one_div_pos.2 (hFpos t ht)) hF hG hFG (inv_pos.2 hs)
  have h' := h.comp tendsto_inv_atTop_nhdsGT_zero
  rw [Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, ← neg_div] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [Function.comp_apply, mul_inv, inv_inv]

/-! ### Archimax tail coefficients -/

theorem two_mul_half_pos (hA : IsPickandsFunction A) : 0 < 2 * A (1 / 2) := by
  have := hA.half_le (t := 1 / 2) ⟨by norm_num, by norm_num⟩
  linarith

/-- `λ_U = 2 - (2A(1/2))^{1/m}` when `(1 - ψ(sx))/(1 - ψ(x)) → s^{1/m}` at `s = 2A(1/2)`. -/
theorem hasUpperTailDependence_archimaxCopula_of_toFun_ratio (hA : IsPickandsFunction A)
    {m : ℝ}
    (h : Tendsto (fun x => (1 - g.toFun (2 * A (1 / 2) * x)) / (1 - g.toFun x)) (𝓝[>] 0)
      (𝓝 ((2 * A (1 / 2)) ^ (1 / m)))) :
    (g.archimaxCopula A hA).HasUpperTailDependence (2 - (2 * A (1 / 2)) ^ (1 / m)) :=
  g.hasUpperTailDependence_archimaxCopula_of_tendsto hA h

/-- **Capéraà–Fougères–Genest, upper tail**: if `φ(1 - at)/φ(1 - t) → a^m` as `t → 0+` for every
`a > 0` (`m > 0`), then the Archimax copula has `λ_U = 2 - (2A(1/2))^{1/m}`. -/
theorem hasUpperTailDependence_archimaxCopula_of_regularVariation (hA : IsPickandsFunction A)
    {m : ℝ} (hm : 0 < m)
    (hφ : ∀ a, 0 < a →
      Tendsto (fun t => g.invFunReal (1 - a * t) / g.invFunReal (1 - t)) (𝓝[>] 0) (𝓝 (a ^ m))) :
    (g.archimaxCopula A hA).HasUpperTailDependence (2 - (2 * A (1 / 2)) ^ (1 / m)) :=
  g.hasUpperTailDependence_archimaxCopula_of_toFun_ratio hA
    (g.tendsto_one_sub_toFun_ratio hm hφ (two_mul_half_pos hA))

/-- `λ_L = (2A(1/2))^{-1/k}` for a strict generator when `ψ(sx)/ψ(x) → s^{-1/k}` as `x → ∞` at
`s = 2A(1/2)`. -/
theorem hasLowerTailDependence_archimaxCopula_of_toFun_ratio (hA : IsPickandsFunction A)
    (hg : g.IsStrict) {k : ℝ}
    (h : Tendsto (fun x => g.toFun (2 * A (1 / 2) * x) / g.toFun x) atTop
      (𝓝 ((2 * A (1 / 2)) ^ (-1 / k)))) :
    (g.archimaxCopula A hA).HasLowerTailDependence ((2 * A (1 / 2)) ^ (-1 / k)) :=
  g.hasLowerTailDependence_archimaxCopula_of_tendsto hA hg h

/-- **Capéraà–Fougères–Genest, lower tail**: for a strict generator with `φ(at)/φ(t) → a^{-k}` as
`t → 0+` for every `a > 0` (`k > 0`), the Archimax copula has `λ_L = (2A(1/2))^{-1/k}`. -/
theorem hasLowerTailDependence_archimaxCopula_of_regularVariation (hA : IsPickandsFunction A)
    (hg : g.IsStrict) {k : ℝ} (hk : 0 < k)
    (hφ : ∀ a, 0 < a →
      Tendsto (fun t => g.invFunReal (a * t) / g.invFunReal t) (𝓝[>] 0) (𝓝 (a ^ (-k)))) :
    (g.archimaxCopula A hA).HasLowerTailDependence ((2 * A (1 / 2)) ^ (-1 / k)) :=
  g.hasLowerTailDependence_archimaxCopula_of_toFun_ratio hA hg
    (hg.tendsto_toFun_ratio_atTop hk hφ (two_mul_half_pos hA))

/-- A non-strict generator gives **no lower tail dependence** as soon as `A(1/2) > 1/2`: the
diagonal `ψ(2A(1/2) φ(t))` vanishes near `0`. -/
theorem hasLowerTailDependence_archimaxCopula_zero_of_not_isStrict (hA : IsPickandsFunction A)
    (hg : ¬ g.IsStrict) (hA2 : 1 / 2 < A (1 / 2)) :
    (g.archimaxCopula A hA).HasLowerTailDependence 0 := by
  obtain ⟨S, hS, hpos, hzero, -⟩ := g.exists_zero_threshold hg
  set κ := 2 * A (1 / 2) with hκ
  have hκ1 : 1 < κ := by linarith
  set x₀ := S * (1 + 1 / κ) / 2 with hx₀
  have hκinv : 1 / κ < 1 := by rw [div_lt_one (by linarith)]; exact hκ1
  have hκinv0 : 0 < 1 / κ := by positivity
  have hx₀0 : 0 ≤ x₀ := by positivity
  have hx₀S : x₀ < S := by rw [hx₀]; nlinarith
  have hκx₀ : S < κ * x₀ := by
    rw [hx₀]
    have : κ * (S * (1 + 1 / κ) / 2) = S * (κ + 1) / 2 := by field_simp
    rw [this]
    nlinarith
  have hψx₀ := hpos x₀ hx₀0 hx₀S
  set t₀ := g.toI hx₀0 with ht₀
  have ht₀0 : t₀ ≠ 0 := g.toI_ne_zero hx₀0 hψx₀
  have hlt : (0 : I) < t₀ := lt_of_le_of_ne unitInterval.nonneg' (Ne.symm ht₀0)
  unfold HasLowerTailDependence
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
  have htne : t ≠ 0 := ht.1.ne'
  rw [g.lowerTailRatio_archimaxCopula hA htne]
  have hφt : x₀ ≤ g.invFun t := by
    have := g.inv_antitone t t₀ htne ht.2.le
    rwa [g.invFun_toI hx₀0 hψx₀] at this
  have hz : g.toFun (κ * g.invFun t) = 0 :=
    hzero _ (lt_of_lt_of_le hκx₀ (mul_le_mul_of_nonneg_left hφt (by linarith)))
  rw [hz, zero_div]

end BivariateGenerator

/-! ### Example: Gumbel's generator -/

/-- `(1 - e^{-y})/y → 1` as `y → 0+`. -/
theorem tendsto_one_sub_exp_neg_div :
    Tendsto (fun y : ℝ => (1 - Real.exp (-y)) / y) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
    have h := ((Real.hasDerivAt_exp (-0)).comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).const_sub 1
    rw [neg_zero, Real.exp_zero] at h
    exact h.congr_deriv (by norm_num)
  refine hd.tendsto_slope_zero_right.congr fun t => ?_
  simp only [zero_add, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul]
  ring

/-- For Gumbel's generator `ψ(x) = exp(-x^{1/θ})`:
`(1 - ψ(sx))/(1 - ψ(x)) → s^{1/θ}` as `x → 0+`. -/
theorem tendsto_gumbelGenerator_ratio (θ : ℝ) (hθ : 1 ≤ θ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x => (1 - (gumbelGenerator θ hθ).toFun (s * x)) /
      (1 - (gumbelGenerator θ hθ).toFun x)) (𝓝[>] 0) (𝓝 (s ^ (1 / θ))) := by
  have hθ0 : 0 < θ⁻¹ := inv_pos.2 (by linarith)
  have hb : Tendsto (fun x : ℝ => x ^ θ⁻¹) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have h := ((Real.continuous_rpow_const hθ0.le).tendsto 0)
      rw [Real.zero_rpow hθ0.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.rpow_pos_of_pos hx _
  have hsb := hb.comp (tendsto_const_mul_nhdsGT_zero hs)
  have h := ((tendsto_one_sub_exp_neg_div.comp hsb).div (tendsto_one_sub_exp_neg_div.comp hb)
    one_ne_zero).const_mul (s ^ θ⁻¹)
  rw [div_one, mul_one] at h
  rw [one_div]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hb0 : 0 < x ^ θ⁻¹ := Real.rpow_pos_of_pos hx0 _
  have hsθ : 0 < s ^ θ⁻¹ := Real.rpow_pos_of_pos hs _
  have he : 0 < 1 - Real.exp (-(x ^ θ⁻¹)) := by
    have := Real.exp_lt_exp.2 (show -(x ^ θ⁻¹) < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  change s ^ θ⁻¹ * ((1 - Real.exp (-((s * x) ^ θ⁻¹))) / (s * x) ^ θ⁻¹ /
    ((1 - Real.exp (-(x ^ θ⁻¹))) / x ^ θ⁻¹)) =
    (1 - Real.exp (-((s * x) ^ θ⁻¹))) / (1 - Real.exp (-(x ^ θ⁻¹)))
  rw [Real.mul_rpow hs.le hx0.le]
  field_simp

/-- **Gumbel–Archimax copulas**: with Gumbel's generator `ψ(x) = exp(-x^{1/θ})` (`θ ≥ 1`) and any
Pickands function `A`, the Archimax copula has `λ_U = 2 - (2A(1/2))^{1/θ}` (Capéraà–Fougères–Genest
2000; `A ≡ 1` gives Gumbel's `2 - 2^{1/θ}`). -/
theorem hasUpperTailDependence_archimaxCopula_gumbelGenerator {A : ℝ → ℝ}
    (hA : IsPickandsFunction A) (θ : ℝ) (hθ : 1 ≤ θ) :
    ((gumbelGenerator θ hθ).archimaxCopula A hA).HasUpperTailDependence
      (2 - (2 * A (1 / 2)) ^ (1 / θ)) :=
  (gumbelGenerator θ hθ).hasUpperTailDependence_archimaxCopula_of_toFun_ratio hA
    (tendsto_gumbelGenerator_ratio θ hθ (BivariateGenerator.two_mul_half_pos hA))

end ProbabilityTheory.Copula
