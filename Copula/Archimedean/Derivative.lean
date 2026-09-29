/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.LevelCurves
import Copula.Rank.ConditionalDerivative

/-! # Differentiable Archimedean generators and conditional distributions

For the analytic formulas of Nelsen, *An Introduction to Copulas*, second edition,
Theorem 4.3.4 (the Kendall distribution function) and Corollary 5.1.4 (Kendall's tau via the
generator), we consider generators whose inverse generator `ψ` has a continuous derivative `ψ'`
on its positivity region `{s > 0 : ψ(s) > 0}` (`BivariateGenerator.IsC1`; for strict generators
this is `(0, ∞)`, see `BivariateGenerator.IsC1.of_isStrict`). Then:

* the generator `φ` is continuous on `(0, 1)` for every generator
  (`BivariateGenerator.continuousAt_invFunReal`);
* `ψ' < 0` where `ψ > 0` (`BivariateGenerator.IsC1.deriv_neg`) and
  `φ'(u) = 1 / ψ'(φ(u))` on `(0, 1)` (`BivariateGenerator.IsC1.hasDerivAt_invFunReal`);
* the first partial derivative is `∂₁C(u, v) = ψ'(φ(u) + φ(v)) / ψ'(φ(u))` where `C(u, v) > 0`
  (`BivariateGenerator.IsC1.hasDerivAt_cdfSection`);
* for almost every `u`, the conditional distribution function of the second coordinate given
  the first equals this partial derivative simultaneously for all `v > 0` with `C(u, v) > 0`
  (`BivariateGenerator.IsC1.ae_conditionalCDF_eq`). The exceptional null set is chosen
  once, via rational thresholds, monotonicity of the conditional CDF and continuity of the
  partial derivative in `v`.
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- The generator is continuous on `(0, 1)`. -/
theorem continuousAt_invFunReal (g : BivariateGenerator) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousAt g.invFunReal x := by
  let u : I := ⟨x, hx0.le, hx1.le⟩
  have hu : u ≠ 0 := fun h => hx0.ne' (congrArg Subtype.val h)
  have hxu : g.invFunReal x = g.invFun u := g.invFunReal_coe u
  have hloc : ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hx0 hx1
  have hval : ∀ y ∈ Ioo (0 : ℝ) 1, ∃ w : I, w ≠ 0 ∧ (w : ℝ) = y ∧ g.invFunReal y = g.invFun w :=
    fun y hy => ⟨⟨y, hy.1.le, hy.2.le⟩, fun h => hy.1.ne' (congrArg Subtype.val h), rfl,
      g.invFunReal_coe ⟨y, hy.1.le, hy.2.le⟩⟩
  unfold ContinuousAt
  rw [hxu]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases lt_or_ge a 0 with ha0 | ha0
    · filter_upwards [hloc] with y hy
      obtain ⟨w, hw, -, hwe⟩ := hval y hy
      rw [hwe]
      exact ha0.trans_le (g.inv_nonneg w hw)
    · have hpos : 0 < g.toFun (g.invFun u) := by rw [g.right_inv u hu]; exact hx0
      have hlt := g.toFun_lt_of_lt ha0 ha hpos
      rw [g.right_inv u hu] at hlt
      filter_upwards [hloc, Iio_mem_nhds (show x < g.toFun a from hlt)] with y hy hya
      obtain ⟨w, hw, hwy, hwe⟩ := hval y hy
      rw [hwe]
      by_contra hle
      push Not at hle
      have h := g.antitone_nonneg (g.inv_nonneg w hw) ha0 hle
      rw [g.right_inv w hw, hwy] at h
      exact absurd hya (not_lt.mpr h)
  · have hψb : g.toFun b < x := by
      have hb0 : 0 ≤ b := (g.inv_nonneg u hu).trans hb.le
      rcases (g.nonneg b hb0).lt_or_eq with hpos | hzero
      · have := g.toFun_lt_of_lt (g.inv_nonneg u hu) hb hpos
        rwa [g.right_inv u hu] at this
      · rw [← hzero]
        exact hx0
    filter_upwards [hloc, Ioi_mem_nhds hψb] with y hy hyb
    obtain ⟨w, hw, hwy, hwe⟩ := hval y hy
    rw [hwe]
    by_contra hle
    push Not at hle
    have h := g.antitone_nonneg ((g.inv_nonneg u hu).trans hb.le) (g.inv_nonneg w hw) hle
    rw [g.right_inv w hw, hwy] at h
    exact absurd (show g.toFun b < y from hyb) (not_lt.mpr h)

/-- A generator whose inverse generator `ψ` is continuously differentiable, with derivative `ψ'`,
on its positivity region `{s > 0 : ψ(s) > 0}` (all of `(0, ∞)` for a strict generator, `(0, φ(0))`
for a non-strict one). The values of `ψ'` elsewhere are not used. -/
structure IsC1 (g : BivariateGenerator) (ψ' : ℝ → ℝ) : Prop where
  /-- `ψ'` is the derivative of `ψ` where `ψ` is positive. -/
  hasDerivAt : ∀ s, 0 < s → 0 < g.toFun s → HasDerivAt g.toFun (ψ' s) s
  /-- The derivative is continuous where `ψ` is positive. -/
  continuousAt : ∀ s, 0 < s → 0 < g.toFun s → ContinuousAt ψ' s

namespace IsC1

variable {g : BivariateGenerator} {ψ' : ℝ → ℝ}

/-- A strict generator with `ψ` continuously differentiable on `(0, ∞)`. -/
theorem of_isStrict (hd : ∀ s, 0 < s → HasDerivAt g.toFun (ψ' s) s)
    (hc : ContinuousOn ψ' (Ioi 0)) : g.IsC1 ψ' where
  hasDerivAt s hs _ := hd s hs
  continuousAt _ hs _ := hc.continuousAt (Ioi_mem_nhds hs)

/-- The derivative of an inverse generator is negative where the inverse generator is positive. -/
theorem deriv_neg (h : g.IsC1 ψ') {s : ℝ} (hs : 0 < s) (hpos : 0 < g.toFun s) : ψ' s < 0 := by
  have hle := g.convex.le_slope_of_hasDerivAt (mem_Ici.mpr hs.le)
    (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ s + 1)) (by linarith) (h.hasDerivAt s hs hpos)
  have hlt : g.toFun (s + 1) < g.toFun s := by
    rcases (g.nonneg (s + 1) (by linarith)).lt_or_eq with h1 | h1
    · exact g.toFun_lt_of_lt hs.le (by linarith) h1
    · rw [← h1]; exact hpos
  rw [slope_def_field, show s + 1 - s = 1 by ring, div_one] at hle
  linarith

theorem deriv_ne_zero (h : g.IsC1 ψ') {s : ℝ} (hs : 0 < s) (hpos : 0 < g.toFun s) : ψ' s ≠ 0 :=
  (h.deriv_neg hs hpos).ne

/-- The generator is positive on `(0, 1)`, as a real function. -/
theorem invFunReal_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < g.invFunReal x := by
  let u : I := ⟨x, hx.1.le, hx.2.le⟩
  have hu : u ≠ 0 := fun e => hx.1.ne' (congrArg Subtype.val e)
  have hu1 : u ≠ 1 := fun e => hx.2.ne (congrArg Subtype.val e)
  rw [show g.invFunReal x = g.invFun u from g.invFunReal_coe u]
  exact g.invFun_pos hu hu1

/-- `ψ(φ(x)) = x` for `x ∈ (0, 1]`, for the real extension of the generator. -/
theorem toFun_invFunReal {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : g.toFun (g.invFunReal x) = x := by
  let u : I := ⟨x, hx0.le, hx1⟩
  have hu : u ≠ 0 := fun e => hx0.ne' (congrArg Subtype.val e)
  rw [show g.invFunReal x = g.invFun u from g.invFunReal_coe u, g.right_inv u hu]

/-- `φ'(x) = 1 / ψ'(φ(x))` on `(0, 1)`. -/
theorem hasDerivAt_invFunReal (h : g.IsC1 ψ') {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt g.invFunReal (ψ' (g.invFunReal x))⁻¹ x := by
  have hpos := invFunReal_pos (g := g) hx
  have hψ : 0 < g.toFun (g.invFunReal x) := by rw [toFun_invFunReal hx.1 hx.2.le]; exact hx.1
  apply HasDerivAt.of_local_left_inverse (g.continuousAt_invFunReal hx.1 hx.2)
    (h.hasDerivAt _ hpos hψ) (h.deriv_ne_zero hpos hψ)
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact toFun_invFunReal hy.1 hy.2.le

/-- The CDF section of the copula of a generator, at an interior first coordinate. -/
theorem cdfSection_eq (g : BivariateGenerator) {v : I} (hv : v ≠ 0) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    cdfSection g.copula v y = g.toFun (g.invFunReal y + g.invFun v) := by
  let w : I := ⟨y, hy.1.le, hy.2.le⟩
  have hw : w ≠ 0 := fun e => hy.1.ne' (congrArg Subtype.val e)
  have hp : projIcc (0 : ℝ) 1 zero_le_one y = w := projIcc_of_mem zero_le_one ⟨hy.1.le, hy.2.le⟩
  rw [cdfSection, cdf_copula, show g.invFunReal y = g.invFun w from g.invFunReal_coe w, hp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [cdf, ite_or_of_not hw hv]

/-- The first partial derivative `∂₁C(x, v) = ψ'(φ(x) + φ(v)) / ψ'(φ(x))` at `x ∈ (0, 1)` with
`C(x, v) > 0`. -/
theorem hasDerivAt_cdfSection (h : g.IsC1 ψ') {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) {v : I}
    (hv : v ≠ 0) (hC : 0 < g.toFun (g.invFunReal x + g.invFun v)) :
    HasDerivAt (cdfSection g.copula v)
      (ψ' (g.invFunReal x + g.invFun v) * (ψ' (g.invFunReal x))⁻¹) x := by
  have hpos := invFunReal_pos (g := g) hx
  have hs : 0 < g.invFunReal x + g.invFun v := add_pos_of_pos_of_nonneg hpos (g.inv_nonneg v hv)
  have hd := (h.hasDerivAt _ hs hC).comp x
    ((h.hasDerivAt_invFunReal hx).add_const (g.invFun v))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact cdfSection_eq g hv hy

/-- The conditional CDF is monotone in the threshold. -/
theorem conditionalCDF_mono (C : Copula 2) (u : I) {v w : I} (hvw : v ≤ w) :
    C.conditionalCDF u v ≤ C.conditionalCDF u w :=
  measureReal_mono (Iic_subset_Iic.mpr hvw)

theorem conditionalCDF_one (C : Copula 2) (u : I) : C.conditionalCDF u 1 = 1 := by
  rw [conditionalCDF, show Iic (1 : I) = univ from
    eq_univ_of_forall fun x => mem_Iic.mpr unitInterval.le_one', probReal_univ]

/-- For almost every `u`, the conditional distribution function of the copula of a `C¹`
generator is the partial derivative `ψ'(φ(u) + φ(v)) / ψ'(φ(u))`, simultaneously for all
thresholds `v > 0` with `C(u, v) > 0`. -/
theorem ae_conditionalCDF_eq (h : g.IsC1 ψ') :
    ∀ᵐ u : I, u ≠ 0 ∧ u ≠ 1 ∧ ∀ v : I, v ≠ 0 → 0 < g.toFun (g.invFun u + g.invFun v) →
      g.copula.conditionalCDF u v = ψ' (g.invFun u + g.invFun v) * (ψ' (g.invFun u))⁻¹ := by
  let vq : ℚ → I := fun q => projIcc 0 1 zero_le_one (q : ℝ)
  have hall : ∀ᵐ u : I, ∀ q : ℚ, g.copula.conditionalCDF u (vq q) =
      deriv (cdfSection g.copula (vq q)) (u : ℝ) :=
    ae_all_iff.2 fun q => conditionalCDF_eq_deriv g.copula (vq q)
  have h0 : ∀ᵐ u : I, u ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ u : I, u ≠ 1 := by simp [ae_iff]
  filter_upwards [hall, h0, h1] with u hq hu0 hu1
  refine ⟨hu0, hu1, ?_⟩
  have hx : (u : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨coe_pos hu0, lt_of_le_of_ne u.property.2 (fun e => hu1 (Subtype.ext e))⟩
  have hφu : g.invFunReal u = g.invFun u := g.invFunReal_coe u
  have hpu : 0 < g.invFun u := g.invFun_pos hu0 hu1
  let D : ℝ → ℝ := fun y => ψ' (g.invFun u + g.invFunReal y) * (ψ' (g.invFun u))⁻¹
  let P : ℝ → ℝ := fun y => g.toFun (g.invFun u + g.invFunReal y)
  -- On positive rational thresholds with `C(u, q) > 0` the conditional CDF is `D`.
  have hDq : ∀ q : ℚ, 0 < (q : ℝ) → 0 < P q →
      g.copula.conditionalCDF u (vq q) = D q := by
    intro q hq0 hPq
    have hne : vq q ≠ 0 := by
      intro e
      have := congrArg Subtype.val e
      simp only [vq, Set.Icc.coe_zero] at this
      rcases le_total (q : ℝ) 1 with hq1 | hq1
      · rw [projIcc_of_mem zero_le_one ⟨hq0.le, hq1⟩] at this
        exact hq0.ne' this
      · rw [projIcc_of_right_le zero_le_one hq1] at this
        exact one_ne_zero this
    have hC : 0 < g.toFun (g.invFunReal u + g.invFun (vq q)) := by rw [hφu]; exact hPq
    rw [hq q, (h.hasDerivAt_cdfSection hx hne hC).deriv, hφu]
    rfl
  have hvq_le : ∀ q : ℚ, ∀ v : I, (q : ℝ) ≤ v → vq q ≤ v := by
    intro q v hqv
    change (projIcc 0 1 zero_le_one (q : ℝ) : ℝ) ≤ v
    rcases le_total 0 (q : ℝ) with hq0 | hq0
    · rw [projIcc_of_mem zero_le_one ⟨hq0, hqv.trans v.property.2⟩]
      exact hqv
    · rw [projIcc_of_le_left zero_le_one hq0]
      exact v.property.1
  have hle_vq : ∀ q : ℚ, ∀ v : I, (v : ℝ) ≤ q → (q : ℝ) ≤ 1 → v ≤ vq q := by
    intro q v hvq hq1
    change (v : ℝ) ≤ (projIcc 0 1 zero_le_one (q : ℝ) : ℝ)
    rw [projIcc_of_mem zero_le_one ⟨v.property.1.trans hvq, hq1⟩]
    exact hvq
  intro v hv hPv
  by_cases hv1 : v = 1
  · subst hv1
    rw [conditionalCDF_one, g.inv_one, add_zero,
      mul_inv_cancel₀ (h.deriv_ne_zero hpu (by rw [g.right_inv u hu0]; exact coe_pos hu0))]
  have hvx : (v : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨coe_pos hv, lt_of_le_of_ne v.property.2 (fun e => hv1 (Subtype.ext e))⟩
  have hPv' : 0 < P v := by simp only [P, g.invFunReal_coe]; exact hPv
  have hs : 0 < g.invFun u + g.invFunReal v := add_pos_of_pos_of_nonneg hpu
    (invFunReal_pos (g := g) hvx).le
  have hin : ContinuousAt (fun y => g.invFun u + g.invFunReal y) v :=
    continuousAt_const.add (g.continuousAt_invFunReal hvx.1 hvx.2)
  have hD : ContinuousAt D v := by
    have hcomp : ContinuousAt (fun y => ψ' (g.invFun u + g.invFunReal y)) v :=
      ContinuousAt.comp (f := fun y => g.invFun u + g.invFunReal y) (g := ψ')
        (h.continuousAt _ hs hPv') hin
    exact hcomp.mul continuousAt_const
  have hP : ContinuousAt P v :=
    ContinuousAt.comp (f := fun y => g.invFun u + g.invFunReal y) (g := g.toFun)
      (h.hasDerivAt _ hs hPv').continuousAt hin
  have hDv : D v = ψ' (g.invFun u + g.invFun v) * (ψ' (g.invFun u))⁻¹ := by
    simp only [D, g.invFunReal_coe]
  rw [← hDv]
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      (hD.eventually (gt_mem_nhds hlt))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hlr.2 hvx.2)
    have hqD := hsub ⟨hlr.1.trans hq1, hq2.trans_le (min_le_left _ _)⟩
    have hvle := hle_vq q v hq1.le (hq2.trans_le (min_le_right _ _)).le
    have hPq : 0 < P q := by
      have hφ : g.invFunReal q ≤ g.invFun v := by
        rw [show g.invFunReal q = g.invFun (vq q) from rfl]
        exact g.inv_antitone v (vq q) hv hvle
      have hq0 : 0 ≤ g.invFunReal q := by
        rw [show g.invFunReal q = g.invFun (vq q) from rfl]
        exact g.inv_nonneg _ (fun e => hv (le_antisymm (e ▸ hvle) unitInterval.nonneg'))
      exact hPv.trans_le (g.antitone_nonneg (by positivity)
        (add_nonneg hpu.le (g.inv_nonneg v hv)) (by linarith))
    have hmono := conditionalCDF_mono g.copula u hvle
    rw [hDq q (hvx.1.trans hq1) hPq] at hmono
    exact absurd (hmono.trans_lt hqD) (lt_irrefl _)
  · by_contra hlt
    push Not at hlt
    obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
      ((hD.eventually (lt_mem_nhds hlt)).and (hP.eventually (lt_mem_nhds hPv')))
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hlr.1 hvx.1)
    have hqD := hsub ⟨(le_max_left _ _).trans_lt hq1, hq2.trans hlr.2⟩
    have hmono := conditionalCDF_mono g.copula u (hvq_le q v hq2.le)
    rw [hDq q ((le_max_right _ _).trans_lt hq1) hqD.2] at hmono
    exact absurd (hqD.1.trans_le hmono) (lt_irrefl _)

end IsC1

end BivariateGenerator

end ProbabilityTheory.Copula
