/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Basic

/-! # Non-strict generators by clamping

A non-strict Archimedean generator `φ` has a finite value `φ(0) = a`; its pseudo-inverse is
`ψ(t) = F(min t a)`, where `F` is the inverse of `φ` on `[0, a]` (Nelsen, *An Introduction to
Copulas*, second edition, Definition 4.1.1 and Theorem 4.1.4). This file packages the
verification that such a clamped function is an admissible bivariate inverse generator:
`F` convex and antitone on `[0, a]` with `F a = 0` suffices, because `t ↦ min t a` is concave
and a convex antitone function of a concave function is convex.

The constructor `BivariateGenerator.ofClamp` is used for the non-strict families 11, 18, 21
and 22 of Nelsen's Table 4.1.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A convex antitone function of a concave function is convex (sets in `ℝ`, with an explicit
`MapsTo` hypothesis instead of an image set). -/
theorem convexOn_comp_concaveOn_of_mapsTo {g f : ℝ → ℝ} {D T : Set ℝ}
    (hg : ConvexOn ℝ T g) (hanti : AntitoneOn g T) (hf : ConcaveOn ℝ D f)
    (hmaps : MapsTo f D T) : ConvexOn ℝ D (fun x => g (f x)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hfx := hmaps hx
  have hfy := hmaps hy
  have hc : a • f x + b • f y ≤ f (a • x + b • y) := hf.2 hx hy ha hb hab
  have hmem : a • f x + b • f y ∈ T := hg.1 hfx hfy ha hb hab
  calc g (f (a • x + b • y)) ≤ g (a • f x + b • f y) :=
        hanti hmem (hmaps (hf.1 hx hy ha hb hab)) hc
    _ ≤ a • g (f x) + b • g (f y) := hg.2 hfx hfy ha hb hab

/-- `t ↦ min t a` is concave on the whole line. -/
theorem concaveOn_min_const (a : ℝ) : ConcaveOn ℝ univ (fun t : ℝ => min t a) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  simp only [smul_eq_mul]
  apply le_min
  · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hp)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hq)
  · calc p * min x a + q * min y a ≤ p * a + q * a :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) hp)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hq)
      _ = a := by rw [← add_mul, hpq, one_mul]

/-- Clamping a convex function that is antitone on `[0, a]` at `a` gives a convex function on
`[0, ∞)`. -/
theorem convexOn_clamp {F : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (hconv : ConvexOn ℝ (Icc 0 a) F)
    (hanti : AntitoneOn F (Icc 0 a)) : ConvexOn ℝ (Ici 0) (fun t => F (min t a)) := by
  refine convexOn_comp_concaveOn_of_mapsTo hconv hanti
    ((concaveOn_min_const a).subset (subset_univ _) (convex_Ici 0)) ?_
  intro t ht
  exact ⟨le_min (mem_Ici.mp ht) ha, min_le_right _ _⟩

namespace BivariateGenerator

/-- A non-strict bivariate generator from the inverse `F` of the generator on `[0, a]`,
extended by zero beyond `a` (as `F (min t a)`). The generator `φ` must take values in
`[0, a]`, be antitone, vanish at one, and be inverted by `F`. -/
noncomputable def ofClamp (F : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) (hconv : ConvexOn ℝ (Icc 0 a) F)
    (hanti : AntitoneOn F (Icc 0 a)) (hFa : F a = 0) (φ : I → ℝ)
    (hφ : ∀ u, u ≠ 0 → φ u ∈ Icc 0 a) (hφanti : ∀ u v, u ≠ 0 → u ≤ v → φ v ≤ φ u)
    (hφ1 : φ 1 = 0) (hright : ∀ u, u ≠ 0 → F (φ u) = u) : BivariateGenerator where
  toFun t := F (min t a)
  invFun := φ
  nonneg t ht := by
    have hm : min t a ∈ Icc 0 a := ⟨le_min ht ha, min_le_right _ _⟩
    rw [← hFa]
    exact hanti hm ⟨ha, le_rfl⟩ (min_le_right _ _)
  antitone x hx y hy hxy := hanti ⟨le_min (mem_Ici.mp hx) ha, min_le_right _ _⟩
    ⟨le_min (mem_Ici.mp hy) ha, min_le_right _ _⟩ (min_le_min_right a hxy)
  convex := convexOn_clamp ha hconv hanti
  inv_nonneg u hu := (hφ u hu).1
  inv_antitone := hφanti
  inv_one := hφ1
  right_inv u hu := by
    show F (min (φ u) a) = u
    rw [min_eq_left (hφ u hu).2]
    exact hright u hu

theorem ofClamp_toFun {F : ℝ → ℝ} {a : ℝ} {ha : 0 ≤ a} {hconv : ConvexOn ℝ (Icc 0 a) F}
    {hanti : AntitoneOn F (Icc 0 a)} {hFa : F a = 0} {φ : I → ℝ}
    {hφ : ∀ u, u ≠ 0 → φ u ∈ Icc 0 a} {hφanti : ∀ u v, u ≠ 0 → u ≤ v → φ v ≤ φ u}
    {hφ1 : φ 1 = 0} {hright : ∀ u, u ≠ 0 → F (φ u) = u} (t : ℝ) :
    (ofClamp F a ha hconv hanti hFa φ hφ hφanti hφ1 hright).toFun t = F (min t a) := rfl

theorem ofClamp_invFun {F : ℝ → ℝ} {a : ℝ} {ha : 0 ≤ a} {hconv : ConvexOn ℝ (Icc 0 a) F}
    {hanti : AntitoneOn F (Icc 0 a)} {hFa : F a = 0} {φ : I → ℝ}
    {hφ : ∀ u, u ≠ 0 → φ u ∈ Icc 0 a} {hφanti : ∀ u v, u ≠ 0 → u ≤ v → φ v ≤ φ u}
    {hφ1 : φ 1 = 0} {hright : ∀ u, u ≠ 0 → F (φ u) = u} (u : I) :
    (ofClamp F a ha hconv hanti hFa φ hφ hφanti hφ1 hright).invFun u = φ u := rfl

/-- A clamped generator is non-strict: its pseudo-inverse vanishes from `a` on. -/
theorem ofClamp_toFun_of_le {F : ℝ → ℝ} {a : ℝ} {ha : 0 ≤ a} {hconv : ConvexOn ℝ (Icc 0 a) F}
    {hanti : AntitoneOn F (Icc 0 a)} {hFa : F a = 0} {φ : I → ℝ}
    {hφ : ∀ u, u ≠ 0 → φ u ∈ Icc 0 a} {hφanti : ∀ u v, u ≠ 0 → u ≤ v → φ v ≤ φ u}
    {hφ1 : φ 1 = 0} {hright : ∀ u, u ≠ 0 → F (φ u) = u} {t : ℝ} (ht : a ≤ t) :
    (ofClamp F a ha hconv hanti hFa φ hφ hφanti hφ1 hright).toFun t = 0 := by
  rw [ofClamp_toFun, min_eq_right ht, hFa]

end BivariateGenerator

end ProbabilityTheory.Copula
