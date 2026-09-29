/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Archimedean.Clamp
import Copula.Archimedean.Truncated

/-! # Nelsen's family 21

Nelsen, *An Introduction to Copulas*, second edition, Table 4.1, number 21 (Section 4.2):
generator `φ(t) = 1 - (1 - (1 - t)^θ)^(1/θ)` for `θ ≥ 1` and copula
`C(u, v) = 1 - (1 - (max (A + B - 1) 0)^θ)^(1/θ)` with `A = (1 - (1 - u)^θ)^(1/θ)` and
`B = (1 - (1 - v)^θ)^(1/θ)`.

The generator is non-strict (`φ(0) = 1`) and is an involution of `[0, 1]`, so the pseudo-inverse
is `ψ(s) = φ(min s 1)`, built with `BivariateGenerator.ofClamp`. Convexity needs no
derivatives: `φ = G ∘ h` with `h(s) = 1 - (1 - s)^θ` concave and `G(z) = 1 - z^(1/θ)` convex and
antitone on `[0, 1]`. (Geometrically, `z ↦ (1 - z^θ)^(1/θ)` is the boundary of the unit
`ℓ^θ` ball.) At `θ = 1` the family is the lower Fréchet bound (`C_1 = W`).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The generator (and, on `[0, 1]`, its own inverse) `t ↦ 1 - (1 - (1 - t)^θ)^(1/θ)` of
Nelsen's family 21. -/
noncomputable def nelsen21Fun (θ : ℝ) (t : ℝ) : ℝ := 1 - (1 - (1 - t) ^ θ) ^ θ⁻¹

private theorem nelsen21_inner_mem (θ : ℝ) (hθ : 1 ≤ θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) ^ θ ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.rpow_nonneg (by linarith [ht.2]) _,
    Real.rpow_le_one (by linarith [ht.2]) (by linarith [ht.1]) (by linarith)⟩

private theorem nelsen21_outer_mem (θ : ℝ) (hθ : 1 ≤ θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - (1 - t) ^ θ) ^ θ⁻¹ ∈ Icc (0 : ℝ) 1 := by
  have h := nelsen21_inner_mem θ hθ ht
  exact ⟨Real.rpow_nonneg (by linarith [h.2]) _,
    Real.rpow_le_one (by linarith [h.2]) (by linarith [h.1]) (inv_nonneg.mpr (by linarith))⟩

theorem nelsen21Fun_mem (θ : ℝ) (hθ : 1 ≤ θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    nelsen21Fun θ t ∈ Icc (0 : ℝ) 1 := by
  have h := nelsen21_outer_mem θ hθ ht
  exact ⟨by unfold nelsen21Fun; linarith [h.2], by unfold nelsen21Fun; linarith [h.1]⟩

/-- The generator of family 21 is an involution of `[0, 1]`. -/
theorem nelsen21Fun_nelsen21Fun (θ : ℝ) (hθ : 1 ≤ θ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    nelsen21Fun θ (nelsen21Fun θ t) = t := by
  have hθ0 : θ ≠ 0 := by linarith
  have hi := nelsen21_inner_mem θ hθ ht
  unfold nelsen21Fun
  rw [sub_sub_cancel, Real.rpow_inv_rpow (by linarith [hi.2]) hθ0, sub_sub_cancel,
    Real.rpow_rpow_inv (by linarith [ht.2]) hθ0, sub_sub_cancel]

private theorem nelsen21_concaveOn_inner (θ : ℝ) (hθ : 1 ≤ θ) :
    ConcaveOn ℝ (Icc 0 1) (fun t : ℝ => 1 - (1 - t) ^ θ) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := (convexOn_rpow hθ).2 (show 1 - x ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; linarith [hx.2])
    (show 1 - y ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; linarith [hy.2]) ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  have he : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by linear_combination hab
  rw [he] at hc
  nlinarith

private theorem nelsen21_convexOn_outer (θ : ℝ) (hθ : 1 ≤ θ) :
    ConvexOn ℝ (Icc 0 1) (fun z : ℝ => 1 - z ^ θ⁻¹) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := (Real.concaveOn_rpow (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ θ))
    (inv_le_one_of_one_le₀ hθ)).2 (show x ∈ Ici (0 : ℝ) from hx.1)
    (show y ∈ Ici (0 : ℝ) from hy.1) ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  nlinarith

private theorem nelsen21_antitoneOn_outer (θ : ℝ) (hθ : 1 ≤ θ) :
    AntitoneOn (fun z : ℝ => 1 - z ^ θ⁻¹) (Icc 0 1) := by
  intro x hx y _ hxy
  have := Real.rpow_le_rpow hx.1 hxy (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ θ))
  show 1 - y ^ θ⁻¹ ≤ 1 - x ^ θ⁻¹
  linarith

theorem nelsen21Fun_convexOn (θ : ℝ) (hθ : 1 ≤ θ) :
    ConvexOn ℝ (Icc 0 1) (nelsen21Fun θ) := by
  have h := convexOn_comp_concaveOn_of_mapsTo (nelsen21_convexOn_outer θ hθ)
    (nelsen21_antitoneOn_outer θ hθ) (nelsen21_concaveOn_inner θ hθ)
    (fun t ht => by
      have h := nelsen21_inner_mem θ hθ ht
      exact ⟨by linarith [h.2], by linarith [h.1]⟩)
  exact h

theorem nelsen21Fun_antitoneOn (θ : ℝ) (hθ : 1 ≤ θ) :
    AntitoneOn (nelsen21Fun θ) (Icc 0 1) := by
  intro x hx y hy hxy
  have h1 := Real.rpow_le_rpow (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y) (by linarith : 1 - y ≤ 1 - x)
    (by linarith : (0 : ℝ) ≤ θ)
  have hix := nelsen21_inner_mem θ hθ hx
  have h2 := Real.rpow_le_rpow (by linarith [hix.2] : (0 : ℝ) ≤ 1 - (1 - x) ^ θ)
    (by linarith : 1 - (1 - x) ^ θ ≤ 1 - (1 - y) ^ θ) (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ θ))
  unfold nelsen21Fun
  linarith

theorem nelsen21Fun_one (θ : ℝ) (hθ : 1 ≤ θ) : nelsen21Fun θ 1 = 0 := by
  unfold nelsen21Fun
  rw [sub_self, Real.zero_rpow (by linarith), sub_zero, Real.one_rpow, sub_self]

/-- The clamped pseudo-inverse `s ↦ φ(min s 1)` of Nelsen's family 21, for `θ ≥ 1`. The generator
is `φ(u) = 1 - (1 - (1 - u)^θ)^(1/θ)`. -/
noncomputable def nelsen21Generator (θ : ℝ) (hθ : 1 ≤ θ) : BivariateGenerator :=
  BivariateGenerator.ofClamp (nelsen21Fun θ) 1 zero_le_one (nelsen21Fun_convexOn θ hθ)
    (nelsen21Fun_antitoneOn θ hθ) (nelsen21Fun_one θ hθ) (fun u => nelsen21Fun θ u)
    (fun u _ => nelsen21Fun_mem θ hθ u.property)
    (fun u v _ huv => nelsen21Fun_antitoneOn θ hθ u.property v.property huv)
    (by simpa using nelsen21Fun_one θ hθ)
    (fun u _ => nelsen21Fun_nelsen21Fun θ hθ u.property)

/-- Nelsen's family 21 for `θ ≥ 1`. -/
noncomputable def nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 :=
  (nelsen21Generator θ hθ).copula

theorem isArchimedean_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) : IsArchimedean (nelsen21 θ hθ) :=
  (nelsen21Generator θ hθ).isArchimedean

/-- The CDF of Nelsen's family 21 on positive coordinates:
`C(u, v) = 1 - (1 - (max (A + B - 1) 0)^θ)^(1/θ)` with `A = (1 - (1 - u)^θ)^(1/θ)`,
`B = (1 - (1 - v)^θ)^(1/θ)`. -/
theorem cdf_nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (nelsen21 θ hθ).cdf ![u, v] =
      1 - (1 - (max ((1 - (1 - (u : ℝ)) ^ θ) ^ θ⁻¹ + (1 - (1 - (v : ℝ)) ^ θ) ^ θ⁻¹ - 1) 0) ^ θ) ^
        θ⁻¹ := by
  rw [nelsen21, BivariateGenerator.cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [BivariateGenerator.cdf, ite_or_of_not hu hv _ _]
  show nelsen21Fun θ (min (nelsen21Fun θ u + nelsen21Fun θ v) 1) = _
  have hm : min (nelsen21Fun θ u + nelsen21Fun θ v) 1 =
      1 - max ((1 - (1 - (u : ℝ)) ^ θ) ^ θ⁻¹ + (1 - (1 - (v : ℝ)) ^ θ) ^ θ⁻¹ - 1) 0 := by
    rw [← min_sub_sub_left, sub_zero]
    unfold nelsen21Fun
    congr 1
    ring
  rw [hm]
  unfold nelsen21Fun
  rw [sub_sub_cancel]

/-- Nelsen's family 21 on the whole closed unit square, with grounded zero axes. -/
theorem nelsen21_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen21 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        1 - (1 - (max ((1 - (1 - (u : ℝ)) ^ θ) ^ θ⁻¹ + (1 - (1 - (v : ℝ)) ^ θ) ^ θ⁻¹ - 1) 0) ^
          θ) ^ θ⁻¹ := by
  by_cases hu : u = 0
  · subst u
    rw [ite_or_of_left rfl _ _]
    exact (nelsen21 θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    rw [ite_or_of_right rfl _ _]
    exact (nelsen21 θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  rw [ite_or_of_not hu hv _ _]
  exact cdf_nelsen21 θ hθ u v hu hv

/-- At `θ = 1` the generator of family 21 is the truncated linear generator of `W`. -/
theorem nelsen21Generator_one : nelsen21Generator 1 le_rfl = truncatedLinearGenerator := by
  have h1 : (nelsen21Generator 1 le_rfl).toFun = truncatedLinearGenerator.toFun := by
    funext s
    show nelsen21Fun 1 (min s 1) = max 0 (1 - s)
    unfold nelsen21Fun
    rw [Real.rpow_one, inv_one, Real.rpow_one, sub_sub_cancel, ← max_sub_sub_left, sub_self]
    exact max_comm _ _
  have h2 : (nelsen21Generator 1 le_rfl).invFun = truncatedLinearGenerator.invFun := by
    funext u
    show nelsen21Fun 1 u = 1 - (u : ℝ)
    unfold nelsen21Fun
    rw [Real.rpow_one, inv_one, Real.rpow_one, sub_sub_cancel]
  cases h : nelsen21Generator 1 le_rfl
  cases h' : truncatedLinearGenerator
  rw [h, h'] at h1 h2
  simp only at h1 h2
  subst h1 h2
  rfl

/-- `C_1 = W`: at `θ = 1` Nelsen's family 21 is the lower Fréchet bound. -/
@[simp] theorem nelsen21_one : nelsen21 1 le_rfl = countermonotonic := by
  rw [nelsen21, nelsen21Generator_one, truncatedLinearGenerator_copula]

end ProbabilityTheory.Copula
