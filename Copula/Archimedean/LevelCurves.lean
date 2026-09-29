/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Associativity

/-! # Level curves and the zero set of bivariate Archimedean copulas

For `C(u, v) = ψ(φ(u) + φ(v))` (Nelsen, *An Introduction to Copulas*, second edition,
Sections 4.1 and 4.3):

* the generator `φ` is strictly decreasing (`BivariateGenerator.invFun_lt_of_lt`) and convex on
  `(0, 1]` (`BivariateGenerator.convexOn_invFunReal`);
* for `t > 0` the level set `C(u, v) = t` is the curve `φ(u) + φ(v) = φ(t)`
  (`BivariateGenerator.cdf_eq_iff`), and `C(u, v) ≥ t` iff `φ(u) + φ(v) ≤ φ(t)`
  (`BivariateGenerator.le_cdf_iff`);
* the level curve `v = L_t(u) = ψ(φ(t) − φ(u))`, `t ≤ u ≤ 1`, lies on level `t`
  (`BivariateGenerator.cdf_levelCurve`) and is convex (Nelsen, Theorem 4.3.2,
  `BivariateGenerator.convexOn_levelCurve`); equivalently, every upper level set
  `{C ≥ t}` is convex (`BivariateGenerator.convex_upperLevelSet`);
* the zero set `C(u, v) = 0` is `{u = 0} ∪ {v = 0} ∪ {ψ(φ(u) + φ(v)) = 0}`
  (`BivariateGenerator.cdf_eq_zero_iff`). A generator is *strict* (`ψ > 0` everywhere,
  Nelsen's `φ(0) = ∞`) iff `C > 0` on `(0, 1]²` (`BivariateGenerator.isStrict_iff`).
  A non-strict generator has a finite zero `S = φ(0) > 0` with `ψ > 0` on `[0, S)` and `ψ = 0`
  on `(S, ∞)` (`BivariateGenerator.exists_zero_threshold`), so its diagonal vanishes near zero
  (`BivariateGenerator.exists_diagonal_eq_zero`).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- The generator `φ` as a real function, extended constantly outside `[0, 1]`
(its value at `0` is the unused junk value `φ(0)` of the structure). -/
noncomputable def invFunReal (g : BivariateGenerator) (x : ℝ) : ℝ :=
  g.invFun (projIcc 0 1 zero_le_one x)

@[simp] theorem invFunReal_coe (g : BivariateGenerator) (u : I) :
    g.invFunReal (u : ℝ) = g.invFun u := by
  rw [invFunReal, projIcc_val]

/-- A generator is strict when the inverse generator never vanishes (Nelsen's `φ(0) = ∞`). -/
def IsStrict (g : BivariateGenerator) : Prop := ∀ s, 0 ≤ s → 0 < g.toFun s

theorem coe_pos {u : I} (hu : u ≠ 0) : 0 < (u : ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

/-- The generator is strictly decreasing on `(0, 1]`. -/
theorem invFun_lt_of_lt (g : BivariateGenerator) {u v : I} (hu : u ≠ 0) (huv : u < v) :
    g.invFun v < g.invFun u := by
  refine lt_of_le_of_ne (g.inv_antitone u v hu huv.le) ?_
  intro h
  have hv : v ≠ 0 := (unitInterval.nonneg'.trans_lt huv).ne'
  have hr := g.right_inv v hv
  rw [h, g.right_inv u hu] at hr
  exact huv.ne (Subtype.ext hr)

/-- `t ≤ ψ(s)` iff `s ≤ φ(t)`, for `t > 0` and `s ≥ 0`. -/
theorem le_toFun_iff (g : BivariateGenerator) {t : I} (ht : t ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    (t : ℝ) ≤ g.toFun s ↔ s ≤ g.invFun t := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hpos : 0 < g.toFun s := (coe_pos ht).trans_le h
    have h2 := g.toFun_lt_of_lt (g.inv_nonneg t ht) hlt hpos
    rw [g.right_inv t ht] at h2
    linarith
  · intro h
    calc (t : ℝ) = g.toFun (g.invFun t) := (g.right_inv t ht).symm
      _ ≤ g.toFun s := g.antitone_nonneg hs (g.inv_nonneg t ht) h

/-- Upper level sets: for `t > 0`, `t ≤ C(u, v)` iff `u, v > 0` and `φ(u) + φ(v) ≤ φ(t)`. -/
theorem le_cdf_iff (g : BivariateGenerator) {t : I} (ht : t ≠ 0) (u v : I) :
    (t : ℝ) ≤ g.cdf u v ↔ u ≠ 0 ∧ v ≠ 0 ∧ g.invFun u + g.invFun v ≤ g.invFun t := by
  by_cases hu : u = 0
  · simp only [hu, cdf_zero_left, ne_eq, not_true_eq_false, false_and, iff_false, not_le]
    exact coe_pos ht
  by_cases hv : v = 0
  · simp only [hv, cdf_zero_right, ne_eq, not_true_eq_false, false_and, and_false, iff_false,
      not_le]
    exact coe_pos ht
  rw [cdf, ite_or_of_not hu hv,
    g.le_toFun_iff ht (add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv))]
  exact ⟨fun h => ⟨hu, hv, h⟩, fun h => h.2.2⟩

/-- Level curves: for `t > 0` and `u, v > 0`, `C(u, v) = t` iff `φ(u) + φ(v) = φ(t)`. -/
theorem cdf_eq_iff (g : BivariateGenerator) {t u v : I} (ht : t ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    g.cdf u v = t ↔ g.invFun u + g.invFun v = g.invFun t := by
  constructor
  · intro h
    obtain ⟨w, hw, hwe⟩ := g.invFun_cdf hu hv (h ▸ coe_pos ht)
    rw [h] at hw
    rw [← hwe, Subtype.ext hw]
  · intro h
    rw [cdf, ite_or_of_not hu hv, h, g.right_inv t ht]

/-- The zero set of an Archimedean copula. -/
theorem cdf_eq_zero_iff (g : BivariateGenerator) (u v : I) :
    g.cdf u v = 0 ↔ u = 0 ∨ v = 0 ∨ g.toFun (g.invFun u + g.invFun v) = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  rw [cdf, ite_or_of_not hu hv]
  simp [hu, hv]

/-- The copula of a strict generator is positive on `(0, 1]²`. -/
theorem IsStrict.cdf_pos {g : BivariateGenerator} (hg : g.IsStrict) {u v : I} (hu : u ≠ 0)
    (hv : v ≠ 0) : 0 < g.cdf u v := by
  rw [cdf, ite_or_of_not hu hv]
  exact hg _ (add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv))

/-- The generator on the positive unit interval: `φ(1/2)` is a positive argument where `ψ`
is still positive. -/
private theorem exists_pos_toFun_pos (g : BivariateGenerator) :
    ∃ a, 0 < a ∧ 0 < g.toFun a := by
  let h : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hh0 : h ≠ 0 := fun e => by
    have := congrArg (fun w : I => (w : ℝ)) e
    norm_num [h] at this
  have hh1 : h ≠ 1 := fun e => by
    have := congrArg (fun w : I => (w : ℝ)) e
    norm_num [h] at this
  refine ⟨g.invFun h, g.invFun_pos hh0 hh1, ?_⟩
  rw [g.right_inv h hh0]
  norm_num [h]

/-- A non-strict generator has a positive zero threshold `S`: `ψ > 0` on `[0, S)`,
`ψ = 0` on `(S, ∞)`, and `φ ≤ S` on `(0, 1]` (Nelsen's `φ(0) = S < ∞`). -/
theorem exists_zero_threshold (g : BivariateGenerator) (hg : ¬ g.IsStrict) :
    ∃ S, 0 < S ∧ (∀ s, 0 ≤ s → s < S → 0 < g.toFun s) ∧ (∀ s, S < s → g.toFun s = 0) ∧
      ∀ u : I, u ≠ 0 → g.invFun u ≤ S := by
  unfold IsStrict at hg
  push Not at hg
  obtain ⟨s₀, hs₀, hz₀⟩ := hg
  let Z : Set ℝ := {s | 0 ≤ s ∧ g.toFun s = 0}
  have hZ : Z.Nonempty := ⟨s₀, hs₀, le_antisymm hz₀ (g.nonneg s₀ hs₀)⟩
  have hbdd : BddBelow Z := ⟨0, fun s hs => hs.1⟩
  obtain ⟨a, ha, hpa⟩ := g.exists_pos_toFun_pos
  have hlow : ∀ z ∈ Z, a < z := by
    intro z hz
    by_contra hle
    push Not at hle
    have := g.antitone_nonneg hz.1 ha.le hle
    rw [hz.2] at this
    linarith
  have hpos : ∀ s, 0 ≤ s → s < sInf Z → 0 < g.toFun s := by
    intro s hs hlt
    rcases (g.nonneg s hs).lt_or_eq with h | h
    · exact h
    · exact absurd (csInf_le hbdd ⟨hs, h.symm⟩) (not_le.mpr hlt)
  have hzero : ∀ s, sInf Z < s → g.toFun s = 0 := by
    intro s hs
    obtain ⟨z, hz, hzs⟩ := exists_lt_of_csInf_lt hZ hs
    have := g.antitone_nonneg hz.1 (hz.1.trans hzs.le) hzs.le
    rw [hz.2] at this
    exact le_antisymm this (g.nonneg s (hz.1.trans hzs.le))
  refine ⟨sInf Z, ha.trans_le (le_csInf hZ fun z hz => (hlow z hz).le), hpos, hzero, ?_⟩
  intro u hu
  by_contra hlt
  push Not at hlt
  have h := hzero _ hlt
  rw [g.right_inv u hu] at h
  exact hu (Subtype.ext h)

/-- The diagonal of a non-strict generator vanishes on an initial interval `(0, t₀]`. -/
theorem exists_diagonal_eq_zero (g : BivariateGenerator) (hg : ¬ g.IsStrict) :
    ∃ t₀ : I, t₀ ≠ 0 ∧ ∀ t : I, t ≤ t₀ → g.cdf t t = 0 := by
  obtain ⟨S, hS, hpos, hzero, -⟩ := g.exists_zero_threshold hg
  have hx : (0 : ℝ) ≤ 3 * S / 4 := by positivity
  have hxp : 0 < g.toFun (3 * S / 4) := hpos _ hx (by linarith)
  refine ⟨g.toI hx, g.toI_ne_zero hx hxp, ?_⟩
  intro t ht
  by_cases h0 : t = 0
  · simp [h0]
  have hφ : 3 * S / 4 ≤ g.invFun t := by
    have := g.inv_antitone t (g.toI hx) h0 ht
    rwa [g.invFun_toI hx hxp] at this
  rw [cdf, ite_or_of_not h0 h0]
  exact hzero _ (by linarith)

/-- A generator is strict iff its copula is positive on `(0, 1]²`. -/
theorem isStrict_iff (g : BivariateGenerator) :
    g.IsStrict ↔ ∀ u v : I, u ≠ 0 → v ≠ 0 → 0 < g.cdf u v := by
  refine ⟨fun hg u v hu hv => hg.cdf_pos hu hv, fun h => ?_⟩
  by_contra hg
  obtain ⟨t₀, ht₀, hz⟩ := g.exists_diagonal_eq_zero hg
  exact (h t₀ t₀ ht₀ ht₀).ne' (hz t₀ le_rfl)

/-- The generator `φ` is convex on `(0, 1]` (Nelsen, Section 4.1: the pseudo-inverse of a
convex decreasing function is convex). -/
theorem convexOn_invFunReal (g : BivariateGenerator) : ConvexOn ℝ (Ioc 0 1) g.invFunReal := by
  refine ⟨convex_Ioc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  let u : I := ⟨x, hx.1.le, hx.2⟩
  let v : I := ⟨y, hy.1.le, hy.2⟩
  have hu : u ≠ 0 := fun h => hx.1.ne' (congrArg Subtype.val h)
  have hv : v ≠ 0 := fun h => hy.1.ne' (congrArg Subtype.val h)
  have hzmem : a • x + b • y ∈ Ioc (0 : ℝ) 1 := (convex_Ioc 0 1) hx hy ha hb hab
  let w : I := ⟨a • x + b • y, hzmem.1.le, hzmem.2⟩
  have hw : w ≠ 0 := fun h => hzmem.1.ne' (congrArg Subtype.val h)
  have hxu : g.invFunReal x = g.invFun u := g.invFunReal_coe u
  have hyv : g.invFunReal y = g.invFun v := g.invFunReal_coe v
  have hzw : g.invFunReal (a • x + b • y) = g.invFun w := g.invFunReal_coe w
  rw [hxu, hyv, hzw]
  have hm0 : 0 ≤ a • g.invFun u + b • g.invFun v := by
    simp only [smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (g.inv_nonneg u hu)) (mul_nonneg hb (g.inv_nonneg v hv))
  have hc := g.convex.2 (mem_Ici.mpr (g.inv_nonneg u hu)) (mem_Ici.mpr (g.inv_nonneg v hv))
    ha hb hab
  rw [g.right_inv u hu, g.right_inv v hv] at hc
  by_contra hlt
  push Not at hlt
  have h := g.toFun_lt_of_lt hm0 hlt (by rw [g.right_inv w hw]; exact coe_pos hw)
  rw [g.right_inv w hw] at h
  exact absurd hc (not_le.mpr h)

/-- Nelsen, Theorem 4.3.2 (set form): for every level `t`, the upper level set
`{(u, v) ∈ [0,1]² : C(u, v) ≥ t}` is convex. -/
theorem convex_upperLevelSet (g : BivariateGenerator) (t : I) :
    Convex ℝ {p : ℝ × ℝ | p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∧
      (t : ℝ) ≤ g.cdf (projIcc 0 1 zero_le_one p.1) (projIcc 0 1 zero_le_one p.2)} := by
  by_cases ht : t = 0
  · have he : {p : ℝ × ℝ | p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∧
        (t : ℝ) ≤ g.cdf (projIcc 0 1 zero_le_one p.1) (projIcc 0 1 zero_le_one p.2)} =
        Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
      ext p
      simp only [mem_ofPred_eq, and_iff_left_iff_imp]
      intro _
      rw [ht]
      exact g.cdf_nonneg _ _
    rw [he]
    exact (convex_Icc 0 1).prod (convex_Icc 0 1)
  have he : {p : ℝ × ℝ | p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ∧
      (t : ℝ) ≤ g.cdf (projIcc 0 1 zero_le_one p.1) (projIcc 0 1 zero_le_one p.2)} =
      {p : ℝ × ℝ | p ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 ∧
        g.invFunReal p.1 + g.invFunReal p.2 ≤ g.invFun t} := by
    ext p
    simp only [mem_ofPred_eq, mem_prod, mem_Icc, mem_Ioc]
    rw [g.le_cdf_iff ht]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hu, hv, hs⟩
      refine ⟨⟨⟨lt_of_le_of_ne h1 ?_, h2⟩, lt_of_le_of_ne h3 ?_, h4⟩, hs⟩
      · intro h
        apply hu
        rw [← h]
        exact projIcc_left zero_le_one
      · intro h
        apply hv
        rw [← h]
        exact projIcc_left zero_le_one
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, hs⟩
      refine ⟨⟨⟨h1.le, h2⟩, h3.le, h4⟩, ?_, ?_, hs⟩
      · intro h
        have := congrArg Subtype.val h
        rw [projIcc_of_mem zero_le_one ⟨h1.le, h2⟩] at this
        exact h1.ne' this
      · intro h
        have := congrArg Subtype.val h
        rw [projIcc_of_mem zero_le_one ⟨h3.le, h4⟩] at this
        exact h3.ne' this
  rw [he]
  intro p hp q hq a b ha hb hab
  have hc := g.convexOn_invFunReal
  refine ⟨⟨hc.1 hp.1.1 hq.1.1 ha hb hab, hc.1 hp.1.2 hq.1.2 ha hb hab⟩, ?_⟩
  have h1 := hc.2 hp.1.1 hq.1.1 ha hb hab
  have h2 := hc.2 hp.1.2 hq.1.2 ha hb hab
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2 ⊢
  have hp2 := mul_le_mul_of_nonneg_left hp.2 ha
  have hq2 := mul_le_mul_of_nonneg_left hq.2 hb
  have he : a * g.invFun t + b * g.invFun t = g.invFun t := by rw [← add_mul, hab, one_mul]
  linarith

/-- The level curve `L_t(u) = ψ(φ(t) − φ(u))` of level `t`. -/
noncomputable def levelCurve (g : BivariateGenerator) (t : I) (x : ℝ) : ℝ :=
  g.toFun (g.invFun t - g.invFunReal x)

/-- The level curve lies on level `t`: `C(u, L_t(u)) = t` for `t ≤ u`, `t > 0`. -/
theorem cdf_levelCurve (g : BivariateGenerator) {t u : I} (ht : t ≠ 0) (htu : t ≤ u) :
    ∃ v : I, (v : ℝ) = g.levelCurve t u ∧ g.cdf u v = t := by
  have hu : u ≠ 0 := fun h => ht (le_antisymm (h ▸ htu) unitInterval.nonneg')
  have hs : 0 ≤ g.invFun t - g.invFun u := sub_nonneg.mpr (g.inv_antitone t u ht htu)
  refine ⟨g.toI hs, by simp [levelCurve], ?_⟩
  rw [g.cdf_toI hu hs, add_sub_cancel, g.right_inv t ht]

/-- Nelsen, Theorem 4.3.2: the level curves of an Archimedean copula are convex. -/
theorem convexOn_levelCurve (g : BivariateGenerator) {t : I} (ht : t ≠ 0) :
    ConvexOn ℝ (Icc (t : ℝ) 1) (g.levelCurve t) := by
  have ht0 := coe_pos ht
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxI : x ∈ Ioc (0 : ℝ) 1 := ⟨ht0.trans_le hx.1, hx.2⟩
  have hyI : y ∈ Ioc (0 : ℝ) 1 := ⟨ht0.trans_le hy.1, hy.2⟩
  have hzI := (convex_Icc (t : ℝ) 1) hx hy ha hb hab
  have hφ (z : ℝ) (hz : z ∈ Icc (t : ℝ) 1) : g.invFunReal z ≤ g.invFun t := by
    let w : I := ⟨z, (ht0.trans_le hz.1).le, hz.2⟩
    have : g.invFunReal z = g.invFun w := g.invFunReal_coe w
    rw [this]
    exact g.inv_antitone t w ht hz.1
  have hc := g.convexOn_invFunReal.2 hxI hyI ha hb hab
  unfold levelCurve
  simp only [smul_eq_mul] at hc hzI ⊢
  have he : a * (g.invFun t - g.invFunReal x) + b * (g.invFun t - g.invFunReal y) =
      g.invFun t - (a * g.invFunReal x + b * g.invFunReal y) := by
    linear_combination g.invFun t * hab
  have hx0 := sub_nonneg.mpr (hφ x hx)
  have hy0 := sub_nonneg.mpr (hφ y hy)
  calc g.toFun (g.invFun t - g.invFunReal (a * x + b * y))
      ≤ g.toFun (a * (g.invFun t - g.invFunReal x) + b * (g.invFun t - g.invFunReal y)) := by
        apply g.antitone_nonneg (by positivity) (sub_nonneg.mpr (hφ _ hzI))
        linarith
    _ ≤ a * g.toFun (g.invFun t - g.invFunReal x) + b * g.toFun (g.invFun t - g.invFunReal y) := by
        have h := g.convex.2 (mem_Ici.mpr hx0) (mem_Ici.mpr hy0) ha hb hab
        simpa only [smul_eq_mul] using h

end BivariateGenerator

end ProbabilityTheory.Copula
