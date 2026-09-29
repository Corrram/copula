/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Diagonal
import Copula.Classical.Bivariate
import Copula.Classical.Characterization

/-!
# Construction of bivariate copulas with a prescribed diagonal

Given a function `δ : I → ℝ` satisfying the necessary conditions for a diagonal section
(`δ 1 = 1`, `0 ≤ δ t ≤ t`, `δ` increasing, and `δ t' - δ t ≤ 2 (t' - t)` for `t ≤ t'`,
see `Copula.Diagonal`), the function
`K u v = min (min u v) ((δ u + δ v) / 2)` is the CDF of a bivariate copula with diagonal `δ`
(Nelsen, *An Introduction to Copulas*, 2nd ed., §3.2.6: the construction of Fredricks and
Nelsen, the diagonal copula of Bertino). This shows that the necessary conditions are also
sufficient.

The rectangle inequality is proved by writing
`K u v = (δ u + δ v) / 2 - ((α v - β u)⁺ + (α u - β v)⁺)` with `α = δ / 2` and
`β t = t - δ t / 2` both increasing. The two positive parts cannot be positive
simultaneously, and `(α v - β u)⁺` has nonpositive mixed increments by convexity of `x ↦ x⁺`.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The necessary conditions for a function to be the diagonal section of a bivariate copula. -/
structure IsDiagonalFunction (δ : I → ℝ) : Prop where
  /-- The diagonal takes the value one at one. -/
  one : δ 1 = 1
  /-- The diagonal is nonnegative. -/
  nonneg : ∀ t, 0 ≤ δ t
  /-- The diagonal lies below the identity. -/
  le_self : ∀ t, δ t ≤ t
  /-- The diagonal is increasing. -/
  monotone : Monotone δ
  /-- The diagonal is `2`-Lipschitz. -/
  lipschitz : ∀ s t : I, s ≤ t → δ t - δ s ≤ 2 * ((t : ℝ) - (s : ℝ))

/-- The diagonal section of every bivariate copula satisfies the necessary conditions. -/
theorem isDiagonalFunction_diagonal (C : Copula 2) : IsDiagonalFunction C.diagonal where
  one := C.diagonal_one
  nonneg := C.diagonal_nonneg
  le_self := C.diagonal_le
  monotone := C.monotone_diagonal
  lipschitz _ _ hst := (C.diagonal_sub_mem_Icc hst).2

/-- The Fredricks–Nelsen kernel `min (min u v) ((δ u + δ v) / 2)`. -/
noncomputable def diagKernel (δ : I → ℝ) (u v : I) : ℝ :=
  min (min (u : ℝ) (v : ℝ)) ((δ u + δ v) / 2)

/-- The increasing function `δ / 2` used in the rectangle inequality. -/
noncomputable def diagAlpha (δ : I → ℝ) (t : I) : ℝ := δ t / 2

/-- The increasing function `t - δ t / 2` used in the rectangle inequality. -/
noncomputable def diagBeta (δ : I → ℝ) (t : I) : ℝ := (t : ℝ) - δ t / 2

private theorem diagKernel_min_eq (x y a b : ℝ) (hx : a ≤ x) (hy : b ≤ y) :
    min (min x y) ((a + b) / 2) =
      (a + b) / 2 - (max 0 (b / 2 - (x - a / 2)) + max 0 (a / 2 - (y - b / 2))) := by
  by_cases h1 : (a + b) / 2 ≤ x
  · by_cases h2 : (a + b) / 2 ≤ y
    · rw [min_eq_right (le_min h1 h2),
        max_eq_left (by linarith : b / 2 - (x - a / 2) ≤ 0),
        max_eq_left (by linarith : a / 2 - (y - b / 2) ≤ 0)]
      ring
    · have h2' : y < (a + b) / 2 := not_le.mp h2
      rw [min_eq_right (by linarith : y ≤ x), min_eq_left h2'.le,
        max_eq_left (by linarith : b / 2 - (x - a / 2) ≤ 0),
        max_eq_right (by linarith : 0 ≤ a / 2 - (y - b / 2))]
      ring
  · have h1' : x < (a + b) / 2 := not_le.mp h1
    rw [min_eq_left (by linarith : x ≤ y), min_eq_left h1'.le,
      max_eq_right (by linarith : 0 ≤ b / 2 - (x - a / 2)),
      max_eq_left (by linarith : a / 2 - (y - b / 2) ≤ 0)]
    ring

private theorem posPart_add_le (y₁ y₂ y₃ : ℝ) (h₁ : y₃ ≤ y₁) (h₂ : y₃ ≤ y₂) :
    max 0 y₁ + max 0 y₂ ≤ max 0 (y₁ + y₂ - y₃) + max 0 y₃ := by
  simp only [max_def]
  split_ifs <;> linarith

private theorem posPart_mixed_le (α β : I → ℝ) (hα : Monotone α) (hβ : Monotone β)
    (a b c e : I) (hab : a ≤ b) (hce : c ≤ e) :
    max 0 (α e - β b) + max 0 (α c - β a) ≤ max 0 (α e - β a) + max 0 (α c - β b) := by
  have h := posPart_add_le (α e - β b) (α c - β a) (α c - β b)
    (by linarith [hα hce]) (by linarith [hβ hab])
  have hx : α e - β b + (α c - β a) - (α c - β b) = α e - β a := by ring
  rw [hx] at h
  linarith

private theorem diagKernel_eq {δ : I → ℝ} (hδ : IsDiagonalFunction δ) (u v : I) :
    diagKernel δ u v = (δ u + δ v) / 2 -
      (max 0 (diagAlpha δ v - diagBeta δ u) + max 0 (diagAlpha δ u - diagBeta δ v)) := by
  unfold diagKernel diagAlpha diagBeta
  exact diagKernel_min_eq (u : ℝ) (v : ℝ) (δ u) (δ v) (hδ.le_self u) (hδ.le_self v)

private theorem diagKernel_increment {δ : I → ℝ} (hδ : IsDiagonalFunction δ)
    (a b c e : I) (hab : a ≤ b) (hce : c ≤ e) :
    0 ≤ diagKernel δ b e - diagKernel δ a e - diagKernel δ b c + diagKernel δ a c := by
  have hα : Monotone (diagAlpha δ) := by
    intro s t hst
    unfold diagAlpha
    have h := hδ.monotone hst
    linarith
  have hβ : Monotone (diagBeta δ) := by
    intro s t hst
    unfold diagBeta
    have h := hδ.lipschitz s t hst
    linarith
  have h1 := posPart_mixed_le (diagAlpha δ) (diagBeta δ) hα hβ a b c e hab hce
  have h2 := posPart_mixed_le (diagAlpha δ) (diagBeta δ) hα hβ c e a b hce hab
  rw [diagKernel_eq hδ b e, diagKernel_eq hδ a e, diagKernel_eq hδ b c, diagKernel_eq hδ a c]
  linarith

/-- The Fredricks–Nelsen kernel of a diagonal function satisfies the classical copula
conditions. -/
theorem IsDiagonalFunction.isClassical {δ : I → ℝ} (hδ : IsDiagonalFunction δ) :
    IsClassical (fun u : Fin 2 → I => diagKernel δ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (diagKernel δ)
  · intro v
    unfold diagKernel
    rw [Set.Icc.coe_zero, min_eq_left v.property.1,
      min_eq_left (by linarith [hδ.nonneg 0, hδ.nonneg v] : (0 : ℝ) ≤ (δ 0 + δ v) / 2)]
  · intro u
    unfold diagKernel
    rw [Set.Icc.coe_zero, min_eq_right u.property.1,
      min_eq_left (by linarith [hδ.nonneg 0, hδ.nonneg u] : (0 : ℝ) ≤ (δ u + δ 0) / 2)]
  · intro v
    have hv : (v : ℝ) ≤ (δ 1 + δ v) / 2 := by
      have h := hδ.lipschitz v 1 unitInterval.le_one'
      rw [Set.Icc.coe_one] at h
      linarith [hδ.one]
    unfold diagKernel
    rw [Set.Icc.coe_one, min_eq_right v.property.2, min_eq_left hv]
  · intro u
    have hu : (u : ℝ) ≤ (δ u + δ 1) / 2 := by
      have h := hδ.lipschitz u 1 unitInterval.le_one'
      rw [Set.Icc.coe_one] at h
      linarith [hδ.one]
    unfold diagKernel
    rw [Set.Icc.coe_one, min_eq_left u.property.2, min_eq_left hu]
  · exact fun a b c e hab hce => diagKernel_increment hδ a b c e hab hce

/-- The bivariate copula with CDF `min (min u v) ((δ u + δ v) / 2)` (Fredricks–Nelsen). -/
noncomputable def diagonalCopula (δ : I → ℝ) (hδ : IsDiagonalFunction δ) : Copula 2 :=
  ofClassical _ hδ.isClassical

/-- The CDF of `diagonalCopula δ` is the Fredricks–Nelsen kernel. -/
theorem cdf_diagonalCopula (δ : I → ℝ) (hδ : IsDiagonalFunction δ) (u : Fin 2 → I) :
    (diagonalCopula δ hδ).cdf u = diagKernel δ (u 0) (u 1) :=
  congrFun (cdf_ofClassical _ hδ.isClassical) u

/-- The diagonal section of `diagonalCopula δ` is `δ`. -/
theorem diagonal_diagonalCopula (δ : I → ℝ) (hδ : IsDiagonalFunction δ) (t : I) :
    (diagonalCopula δ hδ).diagonal t = δ t := by
  have h0 : (![t, t] : Fin 2 → I) 0 = t := by simp
  have h1 : (![t, t] : Fin 2 → I) 1 = t := by simp
  have hg : (δ t + δ t) / 2 = δ t := by ring
  unfold diagonal
  rw [cdf_diagonalCopula, h0, h1]
  unfold diagKernel
  rw [hg, min_self, min_eq_right (hδ.le_self t)]

/-- A function is the diagonal section of a bivariate copula if and only if it satisfies the
necessary conditions (Nelsen, §3.2.6). -/
theorem isDiagonalFunction_iff_exists_copula (δ : I → ℝ) :
    IsDiagonalFunction δ ↔ ∃ C : Copula 2, C.diagonal = δ := by
  refine ⟨fun hδ => ⟨diagonalCopula δ hδ, funext (diagonal_diagonalCopula δ hδ)⟩, ?_⟩
  rintro ⟨C, rfl⟩
  exact isDiagonalFunction_diagonal C

end ProbabilityTheory.Copula
