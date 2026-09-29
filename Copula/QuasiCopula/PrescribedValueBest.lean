/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.QuasiCopula.PrescribedValue
import Copula.Classical.Bivariate

/-!
# The prescribed-value bounds are copulas

Nelsen, *An Introduction to Copulas*, second edition, Theorem 3.2.3 (and its quasi-copula
version in §6.2).

For `(a, b) ∈ [0,1]²` and `max (0, a + b - 1) ≤ θ ≤ min (a, b)`, the upper bound
`min (u, v, θ + (u - a)⁺ + (v - b)⁺)` and the lower bound
`max (0, u + v - 1, θ - (a - u)⁺ - (b - v)⁺)` are copulas taking the value `θ` at `(a, b)`
(`prescribedUpperCopula`, `prescribedLowerCopula`). Together with the bounds of
`Copula.QuasiCopula.PrescribedValue` this shows that they are the pointwise best-possible bounds
for copulas, and for quasi-copulas, with `C(a, b) = θ` (`isGreatest_prescribedUpper`,
`isLeast_prescribedLower`, `isGreatest_prescribedUpper_quasiCopula`,
`isLeast_prescribedLower_quasiCopula`).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ### Real-variable facts -/

theorem prescribedUpper_rectangle_nonneg {a b θ : ℝ} (h0 : 0 ≤ θ) (ha : θ ≤ a) (hb : θ ≤ b)
    {u₁ u₂ v₁ v₂ : ℝ} (hu₀ : 0 ≤ u₁) (hu : u₁ ≤ u₂) (hu₁ : u₂ ≤ 1) (hv₀ : 0 ≤ v₁)
    (hv : v₁ ≤ v₂) (hv₁ : v₂ ≤ 1) :
    0 ≤ prescribedUpper a b θ u₂ v₂ - prescribedUpper a b θ u₁ v₂ -
      prescribedUpper a b θ u₂ v₁ + prescribedUpper a b θ u₁ v₁ := by
  rw [prescribedUpper_eq_shuffle h0 ha hb (by linarith) hu₁ (by linarith) hv₁,
    prescribedUpper_eq_shuffle h0 ha hb hu₀ (by linarith) (by linarith) hv₁,
    prescribedUpper_eq_shuffle h0 ha hb (by linarith) hu₁ hv₀ (by linarith),
    prescribedUpper_eq_shuffle h0 ha hb hu₀ (by linarith) hv₀ (by linarith)]
  unfold prescribedUpperShuffle
  have m := monotone_segmentMass
  have k1 := min_rectangle_nonneg (m 0 θ hu) (m 0 θ hv)
  have k2 := min_rectangle_nonneg (m θ (a - θ) hu) (m b (a - θ) hv)
  have k3 := min_rectangle_nonneg (m a (b - θ) hu) (m θ (b - θ) hv)
  have k4 := min_rectangle_nonneg (m (a + b - θ) (1 - (a + b - θ)) hu)
    (m (a + b - θ) (1 - (a + b - θ)) hv)
  linarith

theorem prescribedUpper_zero_left {a b θ t : ℝ} (h0 : 0 ≤ θ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    prescribedUpper a b θ 0 t = 0 := by
  simp only [prescribedUpper, max_def, min_def]
  split_ifs <;> linarith

theorem prescribedUpper_zero_right {a b θ s : ℝ} (h0 : 0 ≤ θ) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    prescribedUpper a b θ s 0 = 0 := by
  simp only [prescribedUpper, max_def, min_def]
  split_ifs <;> linarith

theorem prescribedUpper_one_left {a b θ t : ℝ} (h1 : a + b - 1 ≤ θ) (ht1 : t ≤ 1) :
    prescribedUpper a b θ 1 t = t := by
  simp only [prescribedUpper, max_def, min_def]
  split_ifs <;> linarith

theorem prescribedUpper_one_right {a b θ s : ℝ} (h1 : a + b - 1 ≤ θ) (hs1 : s ≤ 1) :
    prescribedUpper a b θ s 1 = s := by
  simp only [prescribedUpper, max_def, min_def]
  split_ifs <;> linarith

theorem prescribedUpper_self {a b θ : ℝ} (ha : θ ≤ a) (hb : θ ≤ b) :
    prescribedUpper a b θ a b = θ := by
  simp only [prescribedUpper, sub_self, max_self, add_zero]
  exact min_eq_right (le_min ha hb)

theorem prescribedLower_self {a b θ : ℝ} (h0 : 0 ≤ θ) (h1 : a + b - 1 ≤ θ) :
    prescribedLower a b θ a b = θ := by
  simp only [prescribedLower, sub_self, max_self, sub_zero]
  exact max_eq_right (max_le h0 h1)

/-- Reflecting the second coordinate of the upper bound for `(a, 1 - b, a - θ)` gives the lower
bound for `(a, b, θ)`. -/
theorem sub_prescribedUpper_reflect (a b θ u v : ℝ) :
    u - prescribedUpper a (1 - b) (a - θ) u (1 - v) = prescribedLower a b θ u v := by
  simp only [prescribedUpper, prescribedLower, show 1 - v - (1 - b) = b - v by ring,
    max_def, min_def]
  split_ifs <;> linarith

/-! ### The copulas -/

section Upper

variable (a b : I) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : (a : ℝ) + b - 1 ≤ θ) (ha : θ ≤ a) (hb : θ ≤ b)

include h0 h1 ha hb in
theorem isClassical_prescribedUpper :
    IsClassical (fun u : Fin 2 → I => prescribedUpper a b θ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (fun s t : I => prescribedUpper a b θ s t)
  · intro t
    exact prescribedUpper_zero_left h0 a.2.1 t.2.1
  · intro s
    exact prescribedUpper_zero_right h0 b.2.1 s.2.1
  · intro t
    exact prescribedUpper_one_left h1 t.2.2
  · intro s
    exact prescribedUpper_one_right h1 s.2.2
  · intro s s' t t' hs ht
    exact prescribedUpper_rectangle_nonneg h0 ha hb s.2.1 hs s'.2.2 t.2.1 ht t'.2.2

/-- The upper Fréchet-type bound for a prescribed value `C(a, b) = θ`, as a copula (a shuffle of
`M`). -/
noncomputable def prescribedUpperCopula : Copula 2 :=
  ofClassical _ (isClassical_prescribedUpper a b h0 h1 ha hb)

theorem cdf_prescribedUpperCopula (u v : I) :
    (prescribedUpperCopula a b h0 h1 ha hb).cdf ![u, v] = prescribedUpper a b θ u v := by
  rw [prescribedUpperCopula, cdf_ofClassical]
  rfl

theorem cdf_prescribedUpperCopula_self :
    (prescribedUpperCopula a b h0 h1 ha hb).cdf ![a, b] = θ := by
  rw [cdf_prescribedUpperCopula]
  exact prescribedUpper_self ha hb

end Upper

section Lower

variable (a b : I) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : (a : ℝ) + b - 1 ≤ θ) (ha : θ ≤ a) (hb : θ ≤ b)

/-- The lower Fréchet-type bound for a prescribed value `C(a, b) = θ`, as a copula: the reflection
in the second coordinate of the upper bound for `C(a, 1 - b) = a - θ`. -/
noncomputable def prescribedLowerCopula : Copula 2 :=
  (prescribedUpperCopula a (unitInterval.symm b) (θ := (a : ℝ) - θ) (by linarith)
    (by rw [unitInterval.coe_symm_eq]; linarith) (by linarith)
    (by rw [unitInterval.coe_symm_eq]; linarith)).reflect {1}

theorem cdf_prescribedLowerCopula (u v : I) :
    (prescribedLowerCopula a b h0 h1 ha hb).cdf ![u, v] = prescribedLower a b θ u v := by
  rw [prescribedLowerCopula, cdf_reflect_second, cdf_prescribedUpperCopula,
    unitInterval.coe_symm_eq, unitInterval.coe_symm_eq]
  exact sub_prescribedUpper_reflect _ _ _ _ _

theorem cdf_prescribedLowerCopula_self :
    (prescribedLowerCopula a b h0 h1 ha hb).cdf ![a, b] = θ := by
  rw [cdf_prescribedLowerCopula]
  exact prescribedLower_self h0 h1

end Lower

/-! ### Best-possible bounds -/

section Best

variable (a b : I) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : (a : ℝ) + b - 1 ≤ θ) (ha : θ ≤ a) (hb : θ ≤ b)

include h0 h1 ha hb in
/-- **Nelsen, Theorem 3.2.3 (upper bound is best possible).** Among copulas with
`C(a, b) = θ`, the largest possible value of `C(u, v)` is
`min (u, v, θ + (u - a)⁺ + (v - b)⁺)`. -/
theorem isGreatest_prescribedUpper (u v : I) :
    IsGreatest {x | ∃ C : Copula 2, C.cdf ![a, b] = θ ∧ C.cdf ![u, v] = x}
      (prescribedUpper a b θ u v) := by
  refine ⟨⟨prescribedUpperCopula a b h0 h1 ha hb, cdf_prescribedUpperCopula_self a b h0 h1 ha hb,
    cdf_prescribedUpperCopula a b h0 h1 ha hb u v⟩, ?_⟩
  rintro _ ⟨C, hC, rfl⟩
  rw [← hC]
  exact cdf_le_prescribedUpper C a b u v

include h0 h1 ha hb in
/-- **Nelsen, Theorem 3.2.3 (lower bound is best possible).** Among copulas with
`C(a, b) = θ`, the smallest possible value of `C(u, v)` is
`max (0, u + v - 1, θ - (a - u)⁺ - (b - v)⁺)`. -/
theorem isLeast_prescribedLower (u v : I) :
    IsLeast {x | ∃ C : Copula 2, C.cdf ![a, b] = θ ∧ C.cdf ![u, v] = x}
      (prescribedLower a b θ u v) := by
  refine ⟨⟨prescribedLowerCopula a b h0 h1 ha hb, cdf_prescribedLowerCopula_self a b h0 h1 ha hb,
    cdf_prescribedLowerCopula a b h0 h1 ha hb u v⟩, ?_⟩
  rintro _ ⟨C, hC, rfl⟩
  rw [← hC]
  exact prescribedLower_le_cdf C a b u v

include h0 h1 ha hb in
/-- The upper bound is also best possible among quasi-copulas with `Q(a, b) = θ`. -/
theorem isGreatest_prescribedUpper_quasiCopula (u v : I) :
    IsGreatest {x | ∃ Q : (Fin 2 → I) → ℝ, IsQuasiCopula Q ∧ Q ![a, b] = θ ∧ Q ![u, v] = x}
      (prescribedUpper a b θ u v) := by
  refine ⟨⟨_, isQuasiCopula_cdf (prescribedUpperCopula a b h0 h1 ha hb),
    cdf_prescribedUpperCopula_self a b h0 h1 ha hb,
    cdf_prescribedUpperCopula a b h0 h1 ha hb u v⟩, ?_⟩
  rintro _ ⟨Q, hQ, hθ, rfl⟩
  rw [← hθ]
  exact hQ.le_prescribedUpper a b u v

include h0 h1 ha hb in
/-- The lower bound is also best possible among quasi-copulas with `Q(a, b) = θ`. -/
theorem isLeast_prescribedLower_quasiCopula (u v : I) :
    IsLeast {x | ∃ Q : (Fin 2 → I) → ℝ, IsQuasiCopula Q ∧ Q ![a, b] = θ ∧ Q ![u, v] = x}
      (prescribedLower a b θ u v) := by
  refine ⟨⟨_, isQuasiCopula_cdf (prescribedLowerCopula a b h0 h1 ha hb),
    cdf_prescribedLowerCopula_self a b h0 h1 ha hb,
    cdf_prescribedLowerCopula a b h0 h1 ha hb u v⟩, ?_⟩
  rintro _ ⟨Q, hQ, hθ, rfl⟩
  rw [← hθ]
  exact hQ.prescribedLower_le a b u v

end Best

end ProbabilityTheory.Copula
