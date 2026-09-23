/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical.Bivariate
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp

/-! # Bivariate Archimedean generators

We use the decreasing inverse-generator convention: `ψ` is convex on `[0,∞)`
and `φ` is its inverse on `(0,1]`. Zero coordinates are handled separately.
Convexity is sufficient in dimension two; this constructor makes no claim of
admissibility in higher dimensions.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The analytic conditions sufficient for a bivariate Archimedean copula. -/
structure BivariateGenerator where
  /-- Decreasing inverse generator. -/
  toFun : ℝ → ℝ
  /-- Generator on positive unit-interval arguments; its value at zero is unused. -/
  invFun : I → ℝ
  nonneg : ∀ t, 0 ≤ t → 0 ≤ toFun t
  antitone : AntitoneOn toFun (Ici 0)
  convex : ConvexOn ℝ (Ici 0) toFun
  inv_nonneg : ∀ u, u ≠ 0 → 0 ≤ invFun u
  inv_antitone : ∀ u v, u ≠ 0 → u ≤ v → invFun v ≤ invFun u
  inv_one : invFun 1 = 0
  right_inv : ∀ u, u ≠ 0 → toFun (invFun u) = (u : ℝ)

namespace BivariateGenerator

theorem convex_increment {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ici 0) f)
    {a b c e : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : a ≤ b) (hce : c ≤ e) :
    0 ≤ f (b + e) - f (a + e) - f (b + c) + f (a + c) := by
  by_cases hz : b - a + (e - c) = 0
  · have hb : b = a := by linarith
    have he : e = c := by linarith
    simp [hb, he]
  have ht : 0 < b - a + (e - c) := by positivity
  have hp : 0 ≤ (b - a) / (b - a + (e - c)) := div_nonneg (sub_nonneg.mpr hab) ht.le
  have hq : 0 ≤ (e - c) / (b - a + (e - c)) := div_nonneg (sub_nonneg.mpr hce) ht.le
  have hpq : (b - a) / (b - a + (e - c)) + (e - c) / (b - a + (e - c)) = 1 := by
    rw [← add_div, div_self hz]
  have h₁ := hf.2 (show a + c ∈ Ici 0 by simp only [mem_Ici]; linarith)
    (show b + e ∈ Ici 0 by simp only [mem_Ici]; linarith) hp hq hpq
  have h₂ := hf.2 (show a + c ∈ Ici 0 by simp only [mem_Ici]; linarith)
    (show b + e ∈ Ici 0 by simp only [mem_Ici]; linarith) hq hp (by linarith)
  have he₁ : (b - a) / (b - a + (e - c)) * (a + c) +
      (e - c) / (b - a + (e - c)) * (b + e) = a + e := by field_simp; ring
  have he₂ : (e - c) / (b - a + (e - c)) * (a + c) +
      (b - a) / (b - a + (e - c)) * (b + e) = b + c := by field_simp; ring
  simp only [smul_eq_mul, he₁] at h₁
  simp only [smul_eq_mul, he₂] at h₂
  have hs := add_le_add h₁ h₂
  have he : (b - a) / (b - a + (e - c)) * f (a + c) +
      (e - c) / (b - a + (e - c)) * f (b + e) +
      ((e - c) / (b - a + (e - c)) * f (a + c) +
      (b - a) / (b - a + (e - c)) * f (b + e)) = f (a + c) + f (b + e) := by
    calc
      _ = ((b - a) / (b - a + (e - c)) + (e - c) / (b - a + (e - c))) *
        (f (a + c) + f (b + e)) := by ring
      _ = _ := by rw [hpq, one_mul]
  rw [he] at hs
  linarith

/-- The Archimedean formula, with grounded boundary values. -/
noncomputable def cdf (g : BivariateGenerator) (u v : I) : ℝ :=
  if u = 0 ∨ v = 0 then 0 else g.toFun (g.invFun u + g.invFun v)

@[simp] theorem cdf_zero_left (g : BivariateGenerator) (v : I) : g.cdf 0 v = 0 := by
  simp [cdf]

@[simp] theorem cdf_zero_right (g : BivariateGenerator) (u : I) : g.cdf u 0 = 0 := by
  simp [cdf]

@[simp] theorem cdf_one_left (g : BivariateGenerator) (v : I) : g.cdf 1 v = v := by
  by_cases hv : v = 0
  · simp [hv]
  · simp [cdf, hv, g.inv_one, g.right_inv v hv]

@[simp] theorem cdf_one_right (g : BivariateGenerator) (u : I) : g.cdf u 1 = u := by
  by_cases hu : u = 0
  · simp [hu]
  · simp [cdf, hu, g.inv_one, g.right_inv u hu]

theorem cdf_nonneg (g : BivariateGenerator) (u v : I) : 0 ≤ g.cdf u v := by
  by_cases h : u = 0 ∨ v = 0
  · simp [cdf, h]
  · simpa [cdf, h] using g.nonneg _
      (add_nonneg (g.inv_nonneg u (not_or.mp h).1) (g.inv_nonneg v (not_or.mp h).2))

theorem cdf_mono_left (g : BivariateGenerator) (v : I) : Monotone (fun u => g.cdf u v) := by
  intro a b hab
  by_cases ha : a = 0
  · simpa [ha] using g.cdf_nonneg b v
  by_cases hv : v = 0
  · simp [hv]
  have hb : b ≠ 0 := fun h => ha (le_antisymm (h ▸ hab) unitInterval.nonneg')
  simp only [cdf, ha, hb, hv, or_self, ite_false]
  exact g.antitone (add_nonneg (g.inv_nonneg b hb) (g.inv_nonneg v hv))
    (add_nonneg (g.inv_nonneg a ha) (g.inv_nonneg v hv))
    (by linarith [g.inv_antitone a b ha hab])

theorem cdf_comm (g : BivariateGenerator) (u v : I) : g.cdf u v = g.cdf v u := by
  simp only [cdf, or_comm, add_comm]

theorem isClassical_cdf (g : BivariateGenerator) :
    IsClassical (fun u : Fin 2 → I => g.cdf (u 0) (u 1)) := by
  apply IsClassical.ofBivariate _ g.cdf_zero_left g.cdf_zero_right
    g.cdf_one_left g.cdf_one_right
  intro a b c e hab hce
  by_cases ha : a = 0
  · simp only [ha, g.cdf_zero_left, sub_zero, add_zero]
    exact sub_nonneg.mpr (by simpa only [g.cdf_comm b] using g.cdf_mono_left b hce)
  by_cases hc : c = 0
  · simpa [hc] using sub_nonneg.mpr (g.cdf_mono_left e hab)
  have hb : b ≠ 0 := fun h => ha (le_antisymm (h ▸ hab) unitInterval.nonneg')
  have he : e ≠ 0 := fun h => hc (le_antisymm (h ▸ hce) unitInterval.nonneg')
  simp only [cdf, ha, hb, hc, he, or_self, ite_false]
  have h := convex_increment g.convex (g.inv_nonneg b hb) (g.inv_nonneg e he)
    (g.inv_antitone a b ha hab) (g.inv_antitone c e hc hce)
  linarith

/-- The copula measure represented by a bivariate Archimedean generator. -/
noncomputable def copula (g : BivariateGenerator) : Copula 2 :=
  ofClassical _ g.isClassical_cdf

@[simp] theorem cdf_copula (g : BivariateGenerator) (u : Fin 2 → I) :
    g.copula.cdf u = g.cdf (u 0) (u 1) := by
  exact congrFun (cdf_ofClassical _ _) u

end BivariateGenerator

/-- Identification of a copula's Archimedean generator in its given dimension.
The copula already supplies validity; bivariate convexity alone is not used to
construct higher-dimensional copulas. Grounded boundary values follow from `C`. -/
def HasArchimedeanGenerator {d : ℕ} (C : Copula d) (g : BivariateGenerator) : Prop :=
  ∀ (u : Fin d → I), (∀ i, u i ≠ 0) → C.cdf u = g.toFun (∑ i, g.invFun (u i))

/-- A copula with an identified decreasing Archimedean generator. -/
def IsArchimedean {d : ℕ} (C : Copula d) : Prop := ∃ g, HasArchimedeanGenerator C g

theorem BivariateGenerator.hasArchimedeanGenerator (g : BivariateGenerator) :
    HasArchimedeanGenerator g.copula g := by
  intro u hu
  simp [BivariateGenerator.cdf_copula, BivariateGenerator.cdf, hu 0, hu 1, Fin.sum_univ_two]

theorem BivariateGenerator.isArchimedean (g : BivariateGenerator) : IsArchimedean g.copula :=
  ⟨g, g.hasArchimedeanGenerator⟩

end ProbabilityTheory.Copula
