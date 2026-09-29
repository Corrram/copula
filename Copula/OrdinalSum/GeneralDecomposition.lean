/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.GeneralProperties
import Copula.OrdinalSum.Cut

/-! # Decomposition into general ordinal sums

Nelsen, *An Introduction to Copulas*, 2nd ed., Theorem 3.2.1 characterizes ordinal sums by
fixed points of the diagonal section. This file proves the version for an arbitrary family `J`
of pairwise disjoint open intervals: a copula `C` is an ordinal sum with respect to `J` if and
only if `δ_C(t) = t` for every `t ∈ [0,1]` outside the open intervals
(`exists_generalOrdinalSum_iff`). In that case the components are unique
(`existsUnique_generalOrdinalSum_iff`) and are the rescaled restrictions
```text
C_k(s,t) = (C(a_k + w_k s, a_k + w_k t) - a_k) / w_k,
```
which are copulas as soon as `δ_C(a_k) = a_k` and `δ_C(b_k) = b_k` (`OrdinalIntervals.component`).
The binary case is `exists_ordinalSum_iff_exists_diagonal_fixedPoint` in
`Copula.OrdinalSum.Decomposition`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

namespace OrdinalIntervals

variable {ι : Type*} (J : OrdinalIntervals ι)

@[simp] theorem embed_zero (k : ι) : J.embed k 0 = J.left k := by
  apply Subtype.ext; simp [coe_embed]

@[simp] theorem embed_one (k : ι) : J.embed k 1 = J.right k := by
  apply Subtype.ext; simp [coe_embed, width]

theorem embed_mono (k : ι) : Monotone (J.embed k) := by
  intro s t h
  change (J.left k : ℝ) + J.width k * s ≤ J.left k + J.width k * t
  have : (s : ℝ) ≤ t := h
  nlinarith [J.width_pos k]

theorem embed_coord (k : ι) {u : I} (hl : J.left k ≤ u) (hr : u ≤ J.right k) :
    J.embed k (J.coord k u) = u :=
  Subtype.ext (J.left_add_width_mul_coord k hl hr)

/-- The rescaled restriction of `C` to the square `[a_k, b_k]²`. -/
noncomputable def componentCDF (C : Copula 2) (k : ι) (s t : I) : ℝ :=
  (C.cdf ![J.embed k s, J.embed k t] - J.left k) / J.width k

theorem isClassical_componentCDF (C : Copula 2) (k : ι)
    (ha : C.diagonal (J.left k) = J.left k) (hb : C.diagonal (J.right k) = J.right k) :
    IsClassical (fun x : Fin 2 → I => J.componentCDF C k (x 0) (x 1)) := by
  have hw := J.width_pos k
  apply IsClassical.ofBivariate
  · intro t
    simp only [componentCDF, embed_zero]
    rw [C.cdf_left_cut_of_ge _ _ ha (J.left_le_embed k t)]
    simp
  · intro s
    simp only [componentCDF, embed_zero]
    rw [C.cdf_right_cut_of_ge _ _ ha (J.left_le_embed k s)]
    simp
  · intro t
    simp only [componentCDF, embed_one]
    rw [C.cdf_left_cut_of_le _ _ hb (J.embed_le_right k t), coe_embed]
    field_simp
    ring
  · intro s
    simp only [componentCDF, embed_one]
    rw [C.cdf_right_cut_of_le _ _ hb (J.embed_le_right k s), coe_embed]
    field_simp
    ring
  · intro a b c d hab hcd
    have h := C.rectangleIncrement_cdf_nonneg ![J.embed k a, J.embed k c]
      ![J.embed k b, J.embed k d] (by
        intro i; fin_cases i
        · exact J.embed_mono k hab
        · exact J.embed_mono k hcd)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    simp only [componentCDF]
    rw [div_sub_div_same, div_sub_div_same, ← add_div]
    apply div_nonneg _ hw.le
    linarith

/-- The component of `C` on the `k`th square, a copula when both endpoints are diagonal fixed
points. -/
noncomputable def component (C : Copula 2) (k : ι)
    (ha : C.diagonal (J.left k) = J.left k) (hb : C.diagonal (J.right k) = J.right k) :
    Copula 2 :=
  ofClassical _ (J.isClassical_componentCDF C k ha hb)

theorem cdf_component (C : Copula 2) (k : ι)
    (ha : C.diagonal (J.left k) = J.left k) (hb : C.diagonal (J.right k) = J.right k)
    (s t : I) :
    (J.component C k ha hb).cdf ![s, t] =
      (C.cdf ![J.embed k s, J.embed k t] - J.left k) / J.width k :=
  congrFun (cdf_ofClassical _ _) ![s, t]

/-- The components of an ordinal sum are its summands. -/
theorem component_generalOrdinalSum (C : ι → Copula 2) (k : ι)
    (ha : (generalOrdinalSum J C).diagonal (J.left k) = J.left k)
    (hb : (generalOrdinalSum J C).diagonal (J.right k) = J.right k) :
    J.component (generalOrdinalSum J C) k ha hb = C k := by
  apply ext_cdf_two
  intro s t
  rw [cdf_component, cdf_component_eq J C k]

end OrdinalIntervals

variable {ι : Type*} (J : OrdinalIntervals ι)

/-- If the diagonal of `C` is the identity outside the open intervals, then `C` is the ordinal
sum of its components. -/
theorem eq_generalOrdinalSum_component (C : Copula 2)
    (h : ∀ t : I, (∀ k, ¬ (J.left k < t ∧ t < J.right k)) → C.diagonal t = t) :
    C = generalOrdinalSum J (fun k => J.component C k (h _ fun l => J.left_not_mem k l)
      (h _ fun l => J.right_not_mem k l)) := by
  apply ext_cdf_two
  intro u v
  by_cases hk : ∃ k, J.left k < u ∧ u < J.right k ∧ J.left k < v ∧ v < J.right k
  · obtain ⟨k, h1, h2, h3, h4⟩ := hk
    rw [cdf_generalOrdinalSum_of_mem J _ k ⟨h1.le, h2.le⟩ ⟨h3.le, h4.le⟩,
      OrdinalIntervals.cdf_component, J.embed_coord k h1.le h2.le, J.embed_coord k h3.le h4.le]
    field_simp [(J.width_pos k).ne']
    ring
  · simp only [not_exists, not_and] at hk
    rw [cdf_generalOrdinalSum_of_not_mem J _ u v (fun k hk' => by
      obtain ⟨h1, h2, h3, h4⟩ := hk'
      exact absurd h4 (hk k h1 h2 h3))]
    rcases le_total u v with huv | huv
    · rw [min_eq_left (show (u : ℝ) ≤ v from huv)]
      by_cases hu : ∃ k, J.left k < u ∧ u < J.right k
      · obtain ⟨k, h1, h2⟩ := hu
        have hv : J.right k ≤ v := by
          by_contra hv
          exact hk k h1 h2 (lt_of_lt_of_le h1 huv) (lt_of_not_ge hv)
        exact C.cdf_cross_cut_lower_upper (J.right k) u v
          (h _ fun l => J.right_not_mem k l) h2.le hv
      · simp only [not_exists] at hu
        exact C.cdf_cross_cut_lower_upper u u v (h u hu) le_rfl huv
    · rw [min_eq_right (show (v : ℝ) ≤ u from huv)]
      by_cases hv : ∃ k, J.left k < v ∧ v < J.right k
      · obtain ⟨k, h1, h2⟩ := hv
        have hu : J.right k ≤ u := by
          by_contra hu
          exact hk k (lt_of_lt_of_le h1 huv) (lt_of_not_ge hu) h1 h2
        exact C.cdf_cross_cut_upper_lower (J.right k) u v
          (h _ fun l => J.right_not_mem k l) hu h2.le
      · simp only [not_exists] at hv
        exact C.cdf_cross_cut_upper_lower v u v (h v hv) huv le_rfl

/-- **Nelsen, Theorem 3.2.1** (general form): `C` is an ordinal sum with respect to `J` if and
only if its diagonal is the identity outside the open intervals of `J`. -/
theorem exists_generalOrdinalSum_iff (C : Copula 2) :
    (∃ D : ι → Copula 2, C = generalOrdinalSum J D) ↔
      ∀ t : I, (∀ k, ¬ (J.left k < t ∧ t < J.right k)) → C.diagonal t = t := by
  constructor
  · rintro ⟨D, rfl⟩ t ht
    exact diagonal_generalOrdinalSum_of_not_mem J D t ht
  · intro h
    exact ⟨_, eq_generalOrdinalSum_component J C h⟩

/-- The decomposition of Nelsen, Theorem 3.2.1 is unique. -/
theorem existsUnique_generalOrdinalSum_iff (C : Copula 2) :
    (∃! D : ι → Copula 2, C = generalOrdinalSum J D) ↔
      ∀ t : I, (∀ k, ¬ (J.left k < t ∧ t < J.right k)) → C.diagonal t = t := by
  rw [← exists_generalOrdinalSum_iff]
  constructor
  · exact fun h => h.exists
  · rintro ⟨D, hD⟩
    exact ⟨D, hD, fun E hE => generalOrdinalSum_injective J (hE.symm.trans hD)⟩

end ProbabilityTheory.Copula
