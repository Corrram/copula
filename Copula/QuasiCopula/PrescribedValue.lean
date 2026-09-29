/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.QuasiCopula.Basic
import Copula.Reflection.Bivariate

/-!
# Best-possible bounds for copulas with a prescribed value

Nelsen, *An Introduction to Copulas*, second edition, Theorem 3.2.3, and its quasi-copula
version in §6.2.

If a bivariate copula (or quasi-copula) `C` takes the value `θ` at the point `(a, b)`, then for
all `(u, v)`
```
max (0, u + v - 1, θ - (a - u)⁺ - (b - v)⁺) ≤ C(u, v) ≤ min (u, v, θ + (u - a)⁺ + (v - b)⁺)
```
(`IsQuasiCopula.prescribedLower_le`, `IsQuasiCopula.le_prescribedUpper` and the copula versions
`prescribedLower_le_cdf`, `cdf_le_prescribedUpper`). Both bounds are copulas taking the value
`θ` at `(a, b)` whenever `W(a,b) ≤ θ ≤ M(a,b)` (`prescribedUpperCopula`,
`prescribedLowerCopula`), so they are pointwise best-possible, even among quasi-copulas
(`isGreatest_prescribedUpper`, `isLeast_prescribedLower` and their quasi-copula versions).

The upper bound is the shuffle of `M` that moves the strips `[θ, a]` and `[a, a + b - θ]` of the
first coordinate onto `[b, a + b - θ]` and `[θ, b]`; this representation
(`prescribedUpper_eq_shuffle`) gives the rectangle inequality. The lower bound is obtained from the
upper bound for the parameters `(a, 1 - b, a - θ)` by reflecting the second coordinate.
-/

open Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-- Nelsen's upper bound `min (u, v, θ + (u - a)⁺ + (v - b)⁺)` for copulas with `C(a, b) = θ`. -/
noncomputable def prescribedUpper (a b θ u v : ℝ) : ℝ :=
  min (min u v) (θ + max (u - a) 0 + max (v - b) 0)

/-- Nelsen's lower bound `max (0, u + v - 1, θ - (a - u)⁺ - (b - v)⁺)` for copulas with
`C(a, b) = θ`. -/
noncomputable def prescribedLower (a b θ u v : ℝ) : ℝ :=
  max (max 0 (u + v - 1)) (θ - max (a - u) 0 - max (b - v) 0)

theorem abs_max_sub_right (x y : ℝ) : |max x y - y| = max (x - y) 0 := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, sub_self, abs_zero, max_eq_right (sub_nonpos.mpr h)]
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr h)]

theorem abs_sub_min_right (x y : ℝ) : |y - min x y| = max (y - x) 0 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [min_eq_right h, sub_self, abs_zero, max_eq_right (sub_nonpos.mpr h)]

theorem coe_max_unitInterval (x y : I) : ((max x y : I) : ℝ) = max (x : ℝ) y :=
  Subtype.mono_coe _ |>.map_max

theorem coe_min_unitInterval (x y : I) : ((min x y : I) : ℝ) = min (x : ℝ) y :=
  Subtype.mono_coe _ |>.map_min

namespace IsQuasiCopula

variable {Q : (Fin 2 → I) → ℝ}

/-- **Upper bound for a prescribed value (quasi-copulas).** -/
theorem le_prescribedUpper (hQ : IsQuasiCopula Q) (a b u v : I) :
    Q ![u, v] ≤ prescribedUpper a b (Q ![a, b]) u v := by
  refine le_min (le_min (by simpa using hQ.le_coord ![u, v] 0)
    (by simpa using hQ.le_coord ![u, v] 1)) ?_
  have hm := hQ.monotone (show ![u, v] ≤ ![max u a, max v b] by
    intro i; fin_cases i <;> simp)
  have hl := (le_abs_self _).trans (hQ.lipschitz ![max u a, max v b] ![a, b])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, coe_max_unitInterval, abs_max_sub_right] at hl
  linarith

/-- **Lower bound for a prescribed value (quasi-copulas).** -/
theorem prescribedLower_le (hQ : IsQuasiCopula Q) (a b u v : I) :
    prescribedLower a b (Q ![a, b]) u v ≤ Q ![u, v] := by
  refine max_le ?_ ?_
  · have h := hQ.frechet_lower_le ![u, v]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h
    convert h using 2
    push_cast
    ring
  · have hm := hQ.monotone (show ![min u a, min v b] ≤ ![u, v] by
      intro i; fin_cases i <;> simp)
    have hl := (le_abs_self _).trans (hQ.lipschitz ![a, b] ![min u a, min v b])
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, coe_min_unitInterval, abs_sub_min_right] at hl
    linarith

end IsQuasiCopula

/-- **Nelsen, Theorem 3.2.3 (upper bound).** -/
theorem cdf_le_prescribedUpper (C : Copula 2) (a b u v : I) :
    C.cdf ![u, v] ≤ prescribedUpper a b (C.cdf ![a, b]) u v :=
  (isQuasiCopula_cdf C).le_prescribedUpper a b u v

/-- **Nelsen, Theorem 3.2.3 (lower bound).** -/
theorem prescribedLower_le_cdf (C : Copula 2) (a b u v : I) :
    prescribedLower a b (C.cdf ![a, b]) u v ≤ C.cdf ![u, v] :=
  (isQuasiCopula_cdf C).prescribedLower_le a b u v

/-! ### The upper bound is a shuffle of `M` -/

/-- The length of `[p, p + w] ∩ (-∞, x]`, for `w ≥ 0`. -/
noncomputable def segmentMass (p w x : ℝ) : ℝ := max 0 (min (x - p) w)

theorem segmentMass_of_le (p w x : ℝ) (h : x ≤ p) : segmentMass p w x = 0 :=
  max_eq_left ((min_le_left _ _).trans (by linarith))

theorem segmentMass_of_mem (p w x : ℝ) (h₁ : p ≤ x) (h₂ : x ≤ p + w) :
    segmentMass p w x = x - p := by
  rw [segmentMass, min_eq_left (by linarith), max_eq_right (by linarith)]

theorem segmentMass_of_ge (p w x : ℝ) (hw : 0 ≤ w) (h : p + w ≤ x) : segmentMass p w x = w := by
  rw [segmentMass, min_eq_right (by linarith), max_eq_right hw]

theorem monotone_segmentMass (p w : ℝ) : Monotone (segmentMass p w) := by
  intro x y h
  unfold segmentMass
  gcongr

theorem min_rectangle_nonneg {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    0 ≤ min x₂ y₂ - min x₁ y₂ - min x₂ y₁ + min x₁ y₁ := by
  simp only [min_def]
  split_ifs <;> linarith

/-- The shuffle of `M` with strips `[0, θ] → [0, θ]`, `[θ, a] → [b, a + b - θ]`,
`[a, a + b - θ] → [θ, b]` and `[a + b - θ, 1] → [a + b - θ, 1]`. -/
noncomputable def prescribedUpperShuffle (a b θ u v : ℝ) : ℝ :=
  min (segmentMass 0 θ u) (segmentMass 0 θ v) +
    min (segmentMass θ (a - θ) u) (segmentMass b (a - θ) v) +
    min (segmentMass a (b - θ) u) (segmentMass θ (b - θ) v) +
    min (segmentMass (a + b - θ) (1 - (a + b - θ)) u)
      (segmentMass (a + b - θ) (1 - (a + b - θ)) v)

private theorem prescribedUpper_eq_shuffle_aux0 {a b θ u v : ℝ} (h0 : 0 ≤ θ) (ha : θ ≤ a)
    (hb : θ ≤ b) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hu0 : 0 ≤ u)
    (hu : u ≤ θ)
    (hv : v ≤ θ ∨ (θ ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a + b - θ) ∨ a + b - θ ≤ v) :
    prescribedUpper a b θ u v = prescribedUpperShuffle a b θ u v := by
  unfold prescribedUpper prescribedUpperShuffle
  rcases hv with hv | ⟨hv, hv'⟩ | ⟨hv, hv'⟩ | hv
  · rw [segmentMass_of_mem 0 θ u (by linarith) (by linarith),
      segmentMass_of_le θ (a - θ) u (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_mem 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_le θ (b - θ) v (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_mem 0 θ u (by linarith) (by linarith),
      segmentMass_of_le θ (a - θ) u (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_mem θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_mem 0 θ u (by linarith) (by linarith),
      segmentMass_of_le θ (a - θ) u (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_mem b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_mem 0 θ u (by linarith) (by linarith),
      segmentMass_of_le θ (a - θ) u (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_ge b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) v (by linarith) (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith

private theorem prescribedUpper_eq_shuffle_aux1 {a b θ u v : ℝ} (h0 : 0 ≤ θ) (ha : θ ≤ a)
    (hb : θ ≤ b) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hu : θ ≤ u) (hu' : u ≤ a)
    (hv : v ≤ θ ∨ (θ ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a + b - θ) ∨ a + b - θ ≤ v) :
    prescribedUpper a b θ u v = prescribedUpperShuffle a b θ u v := by
  unfold prescribedUpper prescribedUpperShuffle
  rcases hv with hv | ⟨hv, hv'⟩ | ⟨hv, hv'⟩ | hv
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_mem θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_mem 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_le θ (b - θ) v (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_mem θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_mem θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_mem θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_mem b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_mem θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_le a (b - θ) u (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_ge b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) v (by linarith) (by linarith),
      max_eq_right (by linarith : u - a ≤ 0),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith

private theorem prescribedUpper_eq_shuffle_aux2 {a b θ u v : ℝ} (h0 : 0 ≤ θ) (ha : θ ≤ a)
    (hb : θ ≤ b) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hu : a ≤ u) (hu' : u ≤ a + b - θ)
    (hv : v ≤ θ ∨ (θ ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a + b - θ) ∨ a + b - θ ≤ v) :
    prescribedUpper a b θ u v = prescribedUpperShuffle a b θ u v := by
  unfold prescribedUpper prescribedUpperShuffle
  rcases hv with hv | ⟨hv, hv'⟩ | ⟨hv, hv'⟩ | hv
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_mem a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_mem 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_le θ (b - θ) v (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_mem a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_mem θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_mem a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_mem b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_mem a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) u (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_ge b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) v (by linarith) (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith

private theorem prescribedUpper_eq_shuffle_aux3 {a b θ u v : ℝ} (h0 : 0 ≤ θ) (ha : θ ≤ a)
    (hb : θ ≤ b) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hu : a + b - θ ≤ u) (hu' : u ≤ 1)
    (hv : v ≤ θ ∨ (θ ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a + b - θ) ∨ a + b - θ ≤ v) :
    prescribedUpper a b θ u v = prescribedUpperShuffle a b θ u v := by
  unfold prescribedUpper prescribedUpperShuffle
  rcases hv with hv | ⟨hv, hv'⟩ | ⟨hv, hv'⟩ | hv
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_ge a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) u (by linarith) (by linarith),
      segmentMass_of_mem 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_le θ (b - θ) v (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_ge a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) u (by linarith) (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_le b (a - θ) v (by linarith),
      segmentMass_of_mem θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_right (by linarith : v - b ≤ 0)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_ge a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) u (by linarith) (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_mem b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_le (a + b - θ) (1 - (a + b - θ)) v (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [segmentMass_of_ge 0 θ u (by linarith) (by linarith),
      segmentMass_of_ge θ (a - θ) u (by linarith) (by linarith),
      segmentMass_of_ge a (b - θ) u (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) u (by linarith) (by linarith),
      segmentMass_of_ge 0 θ v (by linarith) (by linarith),
      segmentMass_of_ge b (a - θ) v (by linarith) (by linarith),
      segmentMass_of_ge θ (b - θ) v (by linarith) (by linarith),
      segmentMass_of_mem (a + b - θ) (1 - (a + b - θ)) v (by linarith) (by linarith),
      max_eq_left (by linarith : 0 ≤ u - a),
      max_eq_left (by linarith : 0 ≤ v - b)]
    simp only [min_def]
    split_ifs <;> linarith

/-- The upper bound agrees with the shuffle of `M` on the unit square. -/
theorem prescribedUpper_eq_shuffle {a b θ u v : ℝ} (h0 : 0 ≤ θ) (ha : θ ≤ a) (hb : θ ≤ b)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    prescribedUpper a b θ u v = prescribedUpperShuffle a b θ u v := by
  have hv : v ≤ θ ∨ (θ ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a + b - θ) ∨ a + b - θ ≤ v := by
    rcases le_total v θ with h | h
    · exact Or.inl h
    rcases le_total v b with h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    rcases le_total v (a + b - θ) with h'' | h''
    · exact Or.inr (Or.inr (Or.inl ⟨h', h''⟩))
    · exact Or.inr (Or.inr (Or.inr h''))
  rcases le_total u θ with h | h
  · exact prescribedUpper_eq_shuffle_aux0 h0 ha hb hv0 hv1 hu0 h hv
  rcases le_total u a with h' | h'
  · exact prescribedUpper_eq_shuffle_aux1 h0 ha hb hv0 hv1 h h' hv
  rcases le_total u (a + b - θ) with h'' | h''
  · exact prescribedUpper_eq_shuffle_aux2 h0 ha hb hv0 hv1 h' h'' hv
  · exact prescribedUpper_eq_shuffle_aux3 h0 ha hb hv0 hv1 h'' hu1 hv

end ProbabilityTheory.Copula
