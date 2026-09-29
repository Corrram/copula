/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.TailDependence
import Copula.Families.NelsenTable.N10
import Copula.Families.NelsenTable.N13
import Copula.Families.NelsenTable.N17
import Copula.Families.NelsenTable.N21

/-! # Further tail coefficients of families of Nelsen's Table 4.1

Applications of Nelsen, *An Introduction to Copulas*, second edition, Corollary 5.4.3:

* for a strict generator, `λ_L = lim_{x → ∞} ψ(2x)/ψ(x)`
  (`BivariateGenerator.hasLowerTailDependence_of_tendsto`). Families 10, 13 and 17 are strict
  with `ψ(2x)/ψ(x) → 0`, so `λ_L = 0` (`hasLowerTailDependence_nelsen10`,
  `hasLowerTailDependence_nelsen13`, `hasLowerTailDependence_nelsen17`). For family 13,
  `ψ(2x)/ψ(x) = exp((1 + x)^{1/θ} − (1 + 2x)^{1/θ})`; for family 10 it is
  `((e^x + 1)/(e^{2x} + 1))^{1/θ} ≤ (2e^{−x})^{1/θ}`; for family 17, `ψ(s) = G(e^{−s})` with
  `G(0) = 0`, `G'(0) ≠ 0`, so `ψ(2x)/ψ(x) ~ e^{−x}`.
* `λ_U = 2 − lim_{x → 0⁺} (1 − ψ(2x))/(1 − ψ(x))`
  (`BivariateGenerator.hasUpperTailDependence_of_tendsto`). For family 21,
  `1 − ψ(x) = (1 − (1 − x)^θ)^{1/θ}` near `0`, so the limit is `2^{1/θ}` and
  `λ_U = 2 − 2^{1/θ}` (`hasUpperTailDependence_nelsen21`).

The helper `tendsto_ratio_of_hasDerivAt` states the elementary fact that if `H(0) = 0` and
`H'(0) = d ≠ 0` then `H(2x)/H(x) → 2` as `x → 0⁺`.
-/

open Filter Set
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-- If `H(0) = 0` and `H'(0) = d ≠ 0`, then `H(2x)/H(x) → 2` as `x → 0⁺`. -/
theorem tendsto_ratio_of_hasDerivAt {H : ℝ → ℝ} {d : ℝ} (hH0 : H 0 = 0) (hd : HasDerivAt H d 0)
    (hd0 : d ≠ 0) : Tendsto (fun x => H (2 * x) / H x) (𝓝[>] 0) (𝓝 2) := by
  have hs := hd.tendsto_slope_zero
  simp only [zero_add, hH0, sub_zero, smul_eq_mul] at hs
  have hs' : Tendsto (fun t => t⁻¹ * H t) (𝓝[>] 0) (𝓝 d) :=
    hs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have h2 : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos two_pos (show (0 : ℝ) < x from hx)
  have hA := ((hs'.comp h2).const_mul 2).div hs' hd0
  rw [show 2 * d / d = 2 by field_simp] at hA
  refine hA.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [Pi.div_apply, Function.comp_apply]
  by_cases hHx : H x = 0
  · simp [hHx]
  · field_simp

/-! ### Lower tails of strict families -/

/-- Nelsen's family 13 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen13 (θ : ℝ) (hθ : 0 < θ) :
    (nelsen13 θ hθ).HasLowerTailDependence 0 := by
  set p : ℝ := θ⁻¹ with hp_def
  have hp : 0 < p := inv_pos.mpr hθ
  have hstrict : (nelsen13Generator θ hθ).IsStrict := fun s _ => Real.exp_pos _
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto hstrict
  have hk : 0 < (3 / 2 : ℝ) ^ p - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3 / 2) hp
    linarith
  have hlow : Tendsto (fun x : ℝ => ((3 / 2 : ℝ) ^ p - 1) * x ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).const_mul_atTop hk
  have hdiff : Tendsto (fun x : ℝ => (1 + 2 * x) ^ p - (1 + x) ^ p) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hlow
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    have h1 : (3 / 2 : ℝ) * (1 + x) ≤ 1 + 2 * x := by linarith
    have h2 : ((3 / 2 : ℝ) * (1 + x)) ^ p ≤ (1 + 2 * x) ^ p :=
      Real.rpow_le_rpow (by positivity) h1 hp.le
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
    have h3 : x ^ p ≤ (1 + x) ^ p := Real.rpow_le_rpow hx0 (by linarith) hp.le
    nlinarith
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiff)
  refine hexp.congr' (Eventually.of_forall fun x => ?_)
  change Real.exp (-((1 + 2 * x) ^ p - (1 + x) ^ p)) =
    Real.exp (1 - (1 + 2 * x) ^ p) / Real.exp (1 - (1 + x) ^ p)
  rw [← Real.exp_sub]
  ring_nf

/-- Nelsen's family 10 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen10 (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen10 θ hθ h1).HasLowerTailDependence 0 := by
  set p : ℝ := θ⁻¹ with hp_def
  have hp : 0 < p := inv_pos.mpr hθ
  have hψ : ∀ s, (nelsen10Generator θ hθ h1).toFun s = (2 / (Real.exp s + 1)) ^ p := by
    intro s
    simp only [nelsen10Generator, BivariateGenerator.innerPower, amhGenerator]
    norm_num
    rw [hp_def]
  have hstrict : (nelsen10Generator θ hθ h1).IsStrict := fun s _ => by
    rw [hψ]; positivity
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto hstrict
  have hq : Tendsto (fun x : ℝ => (Real.exp x + 1) / (Real.exp (2 * x) + 1)) atTop (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => 2 * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hup
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have he1 : 1 ≤ Real.exp x := Real.one_le_exp hx
    have he2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [two_mul, Real.exp_add]
    have hen : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [div_le_iff₀ (by positivity), he2]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
  have hc : Tendsto (fun y : ℝ => y ^ p) (𝓝 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
    rwa [Real.zero_rpow hp.ne'] at this
  refine (hc.comp hq).congr' (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, hψ]
  rw [← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-- Nelsen's family 17 has no lower tail dependence. -/
theorem hasLowerTailDependence_nelsen17 (θ : ℝ) (hθ : θ ≠ 0) :
    (nelsen17 θ hθ).HasLowerTailDependence 0 := by
  set c : ℝ := (2 : ℝ) ^ (-θ) - 1 with hc
  set q : ℝ := -θ⁻¹ with hq_def
  have h2pos : 0 < (2 : ℝ) ^ (-θ) := Real.rpow_pos_of_pos two_pos _
  -- sign information
  have hsign : (θ < 0 ∧ 0 < c ∧ 0 < q) ∨ (0 < θ ∧ -1 < c ∧ c < 0 ∧ q < 0) := by
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · left
      refine ⟨hneg, ?_, ?_⟩
      · have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < -θ)
        rw [hc]; linarith
      · rw [hq_def]; exact neg_pos.mpr (inv_lt_zero.mpr hneg)
    · right
      refine ⟨hpos, by rw [hc]; linarith, ?_, ?_⟩
      · have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith : -θ < 0)
        rw [hc]; linarith
      · rw [hq_def]; exact neg_neg_of_pos (inv_pos.mpr hpos)
  have hc0 : c ≠ 0 := by rcases hsign with h | h; exacts [h.2.1.ne', h.2.2.1.ne]
  have hq0 : q ≠ 0 := by rcases hsign with h | h; exacts [h.2.2.ne', h.2.2.2.ne]
  -- `ψ(s) = G(e^{-s})`
  let G : ℝ → ℝ := fun y => (1 + c * y) ^ q - 1
  have hψ : ∀ s, (nelsen17Generator θ hθ).toFun s = G (Real.exp (-s)) := fun s => rfl
  have hbase : ∀ y, 0 ≤ y → y ≤ 1 → 0 < 1 + c * y := by
    intro y hy0 hy1
    rcases hsign with h | h
    · nlinarith [h.2.1]
    · nlinarith [h.2.2.1]
  have hGpos : ∀ y, 0 < y → y ≤ 1 → 0 < G y := by
    intro y hy0 hy1
    simp only [G, sub_pos]
    rcases hsign with h | h
    · have : 1 < 1 + c * y := by nlinarith [h.2.1]
      exact Real.one_lt_rpow this h.2.2
    · have h1 : 1 + c * y < 1 := by nlinarith [h.2.2.1]
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hbase y hy0.le hy1) h1 h.2.2.2
  have hstrict : (nelsen17Generator θ hθ).IsStrict := by
    intro s hs
    rw [hψ]
    exact hGpos _ (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith))
  apply BivariateGenerator.hasLowerTailDependence_of_tendsto hstrict
  -- the derivative of `G` at `0`
  have hGd : HasDerivAt G (c * q) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul c).const_add 1).rpow_const (p := q)
      (Or.inl (by simp))
    have h' := h.sub_const 1
    refine h'.congr_deriv ?_
    simp
  have hG0 : G 0 = 0 := by simp [G]
  have hsl := hGd.tendsto_slope_zero
  simp only [zero_add, hG0, sub_zero, smul_eq_mul] at hsl
  have hy : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall fun x => (Real.exp_pos _).ne'⟩
  have hy2 : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝[≠] 0) :=
    hy.comp (tendsto_id.const_mul_atTop two_pos)
  have hcq : c * q ≠ 0 := mul_ne_zero hc0 hq0
  have hlim := ((Real.tendsto_exp_neg_atTop_nhds_zero.mul (hsl.comp hy2)).div (hsl.comp hy) hcq)
  rw [zero_mul, zero_div] at hlim
  refine hlim.congr' (Eventually.of_forall fun x => ?_)
  simp only [Pi.div_apply, Function.comp_apply, hψ]
  have he : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have hpos := (Real.exp_pos (-x)).ne'
  rw [he]
  by_cases hGx : G (Real.exp (-x)) = 0
  · simp [hGx]
  · field_simp

/-! ### Upper tail of family 21 -/

/-- Nelsen's family 21 has upper tail-dependence coefficient `λ_U = 2 − 2^{1/θ}`. -/
theorem hasUpperTailDependence_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen21 θ hθ).HasUpperTailDependence (2 - 2 ^ θ⁻¹) := by
  have hθ0 : θ ≠ 0 := by linarith
  apply BivariateGenerator.hasUpperTailDependence_of_tendsto
  let H : ℝ → ℝ := fun x => 1 - (1 - x) ^ θ
  have hH0 : H 0 = 0 := by simp [H]
  have hHd : HasDerivAt H θ 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_sub 1).rpow_const (p := θ)
      (Or.inl (by norm_num))).const_sub 1
    refine h.congr_deriv ?_
    simp
  have hrat := tendsto_ratio_of_hasDerivAt hH0 hHd hθ0
  have hc : Tendsto (fun y : ℝ => y ^ θ⁻¹) (𝓝 2) (𝓝 (2 ^ θ⁻¹)) :=
    (Real.continuousAt_rpow_const 2 θ⁻¹ (Or.inl two_ne_zero)).tendsto
  refine (hc.comp hrat).congr' ?_
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 / 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [hsmall, self_mem_nhdsWithin] with x hx hx0
  have hx0' : (0 : ℝ) < x := hx0
  have hHnn : ∀ y, 0 ≤ y → y ≤ 1 → 0 ≤ H y := fun y hy0 hy1 => by
    simp only [H, sub_nonneg]
    exact Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  have hψ : ∀ y, 0 ≤ y → y ≤ 1 → 1 - (nelsen21Generator θ hθ).toFun y = H y ^ θ⁻¹ := by
    intro y _ hy1
    change 1 - nelsen21Fun θ (min y 1) = _
    rw [min_eq_left hy1, nelsen21Fun]
    ring
  simp only [Function.comp_apply]
  rw [hψ _ (by linarith) (by linarith), hψ _ (by linarith) (by linarith),
    Real.div_rpow (hHnn _ (by linarith) (by linarith)) (hHnn _ (by linarith) (by linarith))]

end ProbabilityTheory.Copula
