/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Basic
import Mathlib.Analysis.Convex.Slope

/-! # Generic theory of bivariate Archimedean generators

Consequences of the axioms of `BivariateGenerator` used in Nelsen,
*An Introduction to Copulas*, second edition, Section 4.1 (the representation
`C(u, v) = ψ(φ(u) + φ(v))` and its immediate consequences): the inverse generator
`ψ` is strictly decreasing where it is positive, the generator `φ` inverts `ψ` on its
positive range (`φ(C(u, v)) = φ(u) + φ(v)` when `C(u, v) > 0`), and `C(u, v) < u`
whenever `0 < u` and `0 < v < 1`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

/-- The inverse generator takes the value one at zero. -/
theorem toFun_zero (g : BivariateGenerator) : g.toFun 0 = 1 := by
  have h1 : (1 : I) ≠ 0 := by
    intro h
    have h' : (1 : ℝ) = 0 := congrArg (fun v : I => (v : ℝ)) h
    norm_num at h'
  have h := g.right_inv 1 h1
  rw [g.inv_one, Set.Icc.coe_one] at h
  exact h

/-- The inverse generator is antitone on nonnegative arguments (with plain `0 ≤ _`
hypotheses instead of membership in `Ici 0`). -/
theorem antitone_nonneg (g : BivariateGenerator) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≤ b) : g.toFun b ≤ g.toFun a :=
  g.antitone (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hab

/-- The inverse generator is at most one on nonnegative arguments. -/
theorem toFun_le_one (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) : g.toFun s ≤ 1 :=
  calc g.toFun s ≤ g.toFun 0 := g.antitone_nonneg le_rfl hs hs
    _ = 1 := g.toFun_zero

/-- The inverse generator is strictly decreasing wherever it is positive:
if `0 ≤ a < b` and `ψ b > 0` then `ψ b < ψ a`. -/
theorem toFun_lt_of_lt (g : BivariateGenerator) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : 0 < g.toFun b) : g.toFun b < g.toFun a := by
  have hb0 : 0 ≤ b := ha.trans hab.le
  refine lt_of_le_of_ne (g.antitone_nonneg ha hb0 hab.le) ?_
  intro heq
  have hua : 0 < g.toFun a := by rw [← heq]; exact hb
  have hflat : ∀ t, a ≤ t → g.toFun t = g.toFun a := by
    intro t ht
    have ht0 : 0 ≤ t := ha.trans ht
    apply le_antisymm (g.antitone_nonneg ha ht0 ht)
    rcases le_or_gt t b with htb | htb
    · calc g.toFun a = g.toFun b := heq.symm
        _ ≤ g.toFun t := g.antitone_nonneg ht0 hb0 htb
    · have hs := g.convex.slope_mono_adjacent (show a ∈ Ici (0 : ℝ) from ha)
        (show t ∈ Ici (0 : ℝ) from ht0) hab htb
      rw [heq, sub_self, zero_div] at hs
      have h6 := (le_div_iff₀ (sub_pos.mpr htb)).mp hs
      linarith
  have hu1 : g.toFun a ≤ 1 := g.toFun_le_one ha
  obtain ⟨v, hv⟩ : ∃ v : I, (v : ℝ) = g.toFun a / 2 :=
    ⟨⟨g.toFun a / 2, by linarith, by linarith⟩, rfl⟩
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    have hz : ((0 : I) : ℝ) = 0 := rfl
    linarith
  have hr := g.right_inv v hvne
  rw [hv] at hr
  have hw0 := g.inv_nonneg v hvne
  rcases le_or_gt (g.invFun v) a with hwa | hwa
  · have h7 := g.antitone_nonneg hw0 ha hwa
    linarith
  · have h8 := hflat (g.invFun v) (le_of_lt hwa)
    linarith

/-- The value `ψ(s)` of the inverse generator at a nonnegative argument, as a point of `I`. -/
noncomputable def toI (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) : I :=
  ⟨g.toFun s, g.nonneg s hs, g.toFun_le_one hs⟩

@[simp] theorem coe_toI (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) :
    (g.toI hs : ℝ) = g.toFun s := rfl

theorem toI_ne_zero (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) (hpos : 0 < g.toFun s) :
    g.toI hs ≠ 0 := by
  intro h
  have h' : g.toFun s = 0 := congrArg (fun v : I => (v : ℝ)) h
  exact hpos.ne' h'

/-- The generator inverts the inverse generator on its positive range:
`φ(ψ(s)) = s` whenever `s ≥ 0` and `ψ(s) > 0` (Nelsen, Section 4.1). -/
theorem invFun_toI (g : BivariateGenerator) {s : ℝ} (hs : 0 ≤ s) (hpos : 0 < g.toFun s) :
    g.invFun (g.toI hs) = s := by
  have hne := g.toI_ne_zero hs hpos
  have hr : g.toFun (g.invFun (g.toI hs)) = g.toFun s := g.right_inv (g.toI hs) hne
  have hnn := g.inv_nonneg (g.toI hs) hne
  rcases lt_trichotomy (g.invFun (g.toI hs)) s with hlt | heq | hgt
  · exfalso
    have h := g.toFun_lt_of_lt hnn hlt hpos
    rw [hr] at h
    exact lt_irrefl _ h
  · exact heq
  · exfalso
    have h := g.toFun_lt_of_lt hs hgt (by rw [hr]; exact hpos)
    rw [hr] at h
    exact lt_irrefl _ h

/-- Nelsen's identity `φ(C(u,v)) = φ(u) + φ(v)` whenever `C(u,v) > 0`. -/
theorem invFun_cdf (g : BivariateGenerator) {u v : I} (hu : u ≠ 0) (hv : v ≠ 0)
    (hpos : 0 < g.cdf u v) :
    ∃ w : I, (w : ℝ) = g.cdf u v ∧ g.invFun w = g.invFun u + g.invFun v := by
  have hs : 0 ≤ g.invFun u + g.invFun v := add_nonneg (g.inv_nonneg u hu) (g.inv_nonneg v hv)
  have hc : g.cdf u v = g.toFun (g.invFun u + g.invFun v) := by
    rw [BivariateGenerator.cdf, ite_or_of_not (hu) (hv) _ _]
  rw [hc] at hpos
  exact ⟨g.toI hs, hc.symm, g.invFun_toI hs hpos⟩

/-- The generator is strictly positive at every point of `(0,1)`. -/
theorem invFun_pos (g : BivariateGenerator) {v : I} (hv0 : v ≠ 0) (hv1 : v ≠ 1) :
    0 < g.invFun v := by
  refine lt_of_le_of_ne (g.inv_nonneg v hv0) ?_
  intro h
  have hr := g.right_inv v hv0
  rw [← h, g.toFun_zero] at hr
  exact hv1 (Subtype.ext hr.symm)

/-- `C(u,v) < u` for `u > 0` and `0 < v < 1` (Nelsen, Section 4.1). -/
theorem cdf_lt_left (g : BivariateGenerator) {u v : I} (hu : u ≠ 0) (hv : v ≠ 0)
    (hv1 : v ≠ 1) : g.cdf u v < (u : ℝ) := by
  have hu0 := g.inv_nonneg u hu
  have hvp := g.invFun_pos hv hv1
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hr := g.right_inv u hu
  have hs : 0 ≤ g.invFun u + g.invFun v := by linarith
  have hle : g.toFun (g.invFun u + g.invFun v) ≤ g.toFun (g.invFun u) :=
    g.antitone_nonneg hu0 hs (by linarith)
  have hne : g.toFun (g.invFun u + g.invFun v) ≠ g.toFun (g.invFun u) := by
    intro heq
    have hpos : 0 < g.toFun (g.invFun u + g.invFun v) := by
      rw [heq, hr]
      exact hup
    have h := g.toFun_lt_of_lt hu0 (by linarith : g.invFun u < g.invFun u + g.invFun v) hpos
    rw [heq] at h
    exact lt_irrefl _ h
  rw [BivariateGenerator.cdf, ite_or_of_not (hu) (hv) _ _]
  calc g.toFun (g.invFun u + g.invFun v) < g.toFun (g.invFun u) := lt_of_le_of_ne hle hne
    _ = (u : ℝ) := hr

/-- `C(u,v) < v` for `v > 0` and `0 < u < 1`. -/
theorem cdf_lt_right (g : BivariateGenerator) {u v : I} (hu : u ≠ 0) (hu1 : u ≠ 1)
    (hv : v ≠ 0) : g.cdf u v < (v : ℝ) := by
  rw [g.cdf_comm u v]
  exact g.cdf_lt_left hv hu hu1

end BivariateGenerator

/-- A copula with generator `g` in the sense of `HasArchimedeanGenerator` is `g.copula`. -/
theorem HasArchimedeanGenerator.eq_copula {C : Copula 2} {g : BivariateGenerator}
    (h : HasArchimedeanGenerator C g) : C = g.copula := by
  apply ext_cdf
  intro u
  by_cases hu : ∀ i, u i ≠ 0
  · rw [h u hu, g.hasArchimedeanGenerator u hu]
  · push Not at hu
    obtain ⟨i, hi⟩ := hu
    rw [cdf_eq_zero_of_coord_eq_zero _ _ i hi, cdf_eq_zero_of_coord_eq_zero _ _ i hi]

/-- A bivariate Archimedean copula is the copula of some `BivariateGenerator`. -/
theorem IsArchimedean.exists_generator_copula {C : Copula 2} (h : IsArchimedean C) :
    ∃ g : BivariateGenerator, C = g.copula := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.eq_copula⟩

end ProbabilityTheory.Copula
