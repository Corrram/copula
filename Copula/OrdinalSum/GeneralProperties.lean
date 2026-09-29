/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.General
import Copula.OrdinalSum.Dependence

/-! # Properties of general ordinal sums

For the general ordinal sum `generalOrdinalSum J C` of Nelsen, *An Introduction to Copulas*,
2nd ed., Definition 3.2.1, this file proves:

* the defining formula: `C(u,v) = a_k + w_k C_k(c_k u, c_k v)` on the closed square
  `[a_k, b_k]²` (`cdf_generalOrdinalSum_of_mem`) and `C(u,v) = min(u,v)` whenever `(u,v)` lies in
  none of the open squares (`cdf_generalOrdinalSum_of_not_mem`);
* recovery of the components (`cdf_generalOrdinalSum_embed`) and injectivity in the components;
* diagonal fixed points: `δ(t) = t` outside the open intervals, in particular at all endpoints
  (the easy half of Nelsen, Theorem 3.2.1);
* transpose and exchangeability, pointwise order, and positive quadrant dependence, extending the
  binary results of `Copula.OrdinalSum.Properties` and `Copula.OrdinalSum.Dependence`;
* the existing constructions as instances: finite ordinal sums on an `IntervalPartition`
  (`generalOrdinalSum_ofPartition`), countable ordinal sums on a `CountableIntervalPartition`
  (`generalOrdinalSum_ofCountable`) and the binary `ordinalSum` (`ordinalSum_eq_generalOrdinalSum`).
-/

open Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {ι : Type*} (J : OrdinalIntervals ι) (C : ι → Copula 2)

namespace OrdinalIntervals

/-- The `k`th block does not contribute outside its open square. -/
theorem defect_eq_zero_of_not_mem (k : ι) (u v : I)
    (h : ¬ (J.left k < u ∧ u < J.right k ∧ J.left k < v ∧ v < J.right k)) :
    J.defect C k u v = 0 := by
  simp only [defect]
  rcases le_or_gt u (J.left k) with hu | hu
  · rw [J.coord_of_le k hu, Set.Icc.coe_zero, cdf_two_zero_left,
      min_eq_left (J.coord k v).property.1]
    simp
  rcases le_or_gt (J.right k) u with hu' | hu'
  · rw [J.coord_of_ge k hu', Set.Icc.coe_one, cdf_two_one_left,
      min_eq_right (J.coord k v).property.2]
    simp
  rcases le_or_gt v (J.left k) with hv | hv
  · rw [J.coord_of_le k hv, Set.Icc.coe_zero, cdf_two_zero_right,
      min_eq_right (J.coord k u).property.1]
    simp
  rcases le_or_gt (J.right k) v with hv' | hv'
  · rw [J.coord_of_ge k hv', Set.Icc.coe_one, cdf_two_one_right,
      min_eq_left (J.coord k u).property.2]
    simp
  exact absurd ⟨hu, hu', hv, hv'⟩ h

/-- A point of a closed square `[a_k, b_k]` lies in no other open interval. -/
theorem not_mem_of_mem_Icc {k l : ι} (hkl : l ≠ k) {u : I} (hl : J.left k ≤ u)
    (hr : u ≤ J.right k) : ¬ (J.left l < u ∧ u < J.right l) := by
  rintro ⟨h1, h2⟩
  rcases J.disjoint hkl with h | h
  · exact absurd (h.trans hl) (not_le.mpr h2)
  · exact absurd (hr.trans h) (not_le.mpr h1)

/-- The left endpoint of an interval lies in no open interval of the family. -/
theorem left_not_mem (k l : ι) : ¬ (J.left l < J.left k ∧ J.left k < J.right l) := by
  by_cases hkl : l = k
  · subst hkl; exact fun h => lt_irrefl _ h.1
  · exact J.not_mem_of_mem_Icc hkl le_rfl (J.left_lt_right k).le

/-- The right endpoint of an interval lies in no open interval of the family. -/
theorem right_not_mem (k l : ι) : ¬ (J.left l < J.right k ∧ J.right k < J.right l) := by
  by_cases hkl : l = k
  · subst hkl; exact fun h => lt_irrefl _ h.2
  · exact J.not_mem_of_mem_Icc hkl (J.left_lt_right k).le le_rfl

/-- The affine embedding `s ↦ a_k + w_k s` of `[0,1]` onto `[a_k, b_k]`. -/
noncomputable def embed (k : ι) (s : I) : I :=
  ⟨(J.left k : ℝ) + J.width k * s, by
    have hw := J.width_pos k
    have hs := s.property
    have hl := (J.left k).property
    have hr := (J.right k).property
    constructor
    · nlinarith [hs.1, hl.1]
    · have : J.width k * s ≤ J.width k := mul_le_of_le_one_right hw.le hs.2
      simp only [width] at this ⊢
      linarith [hr.2]⟩

theorem coe_embed (k : ι) (s : I) : (J.embed k s : ℝ) = J.left k + J.width k * s := rfl

theorem left_le_embed (k : ι) (s : I) : J.left k ≤ J.embed k s := by
  change (J.left k : ℝ) ≤ J.left k + J.width k * s
  nlinarith [J.width_pos k, s.property.1]

theorem embed_le_right (k : ι) (s : I) : J.embed k s ≤ J.right k := by
  change (J.left k : ℝ) + J.width k * s ≤ J.right k
  have : J.width k * s ≤ J.width k := mul_le_of_le_one_right (J.width_pos k).le s.property.2
  simp only [width] at this ⊢
  linarith

@[simp] theorem coord_embed (k : ι) (s : I) : J.coord k (J.embed k s) = s := by
  apply Subtype.ext
  rw [J.coe_coord_of_mem k (J.left_le_embed k s) (J.embed_le_right k s), coe_embed]
  field_simp [(J.width_pos k).ne']
  ring

end OrdinalIntervals

/-! ### The defining formula -/

/-- Off the open squares the ordinal sum coincides with `M`. -/
theorem cdf_generalOrdinalSum_of_not_mem (u v : I)
    (h : ∀ k, ¬ (J.left k < u ∧ u < J.right k ∧ J.left k < v ∧ v < J.right k)) :
    (generalOrdinalSum J C).cdf ![u, v] = min (u : ℝ) v := by
  rw [cdf_generalOrdinalSum_eq_min_sub]
  simp [J.defect_eq_zero_of_not_mem C _ u v (h _)]

/-- **Nelsen, Definition 3.2.1**: on the square `[a_k, b_k]²` the ordinal sum is
`a_k + w_k C_k((u - a_k)/w_k, (v - a_k)/w_k)`. -/
theorem cdf_generalOrdinalSum_of_mem (k : ι) {u v : I} (hu : J.left k ≤ u ∧ u ≤ J.right k)
    (hv : J.left k ≤ v ∧ v ≤ J.right k) :
    (generalOrdinalSum J C).cdf ![u, v] =
      J.left k + J.width k * (C k).cdf ![J.coord k u, J.coord k v] := by
  rw [cdf_generalOrdinalSum_eq_min_sub, tsum_eq_single k]
  · simp only [OrdinalIntervals.defect, mul_sub]
    rw [mul_min_of_nonneg _ _ (J.width_pos k).le]
    have h1 := J.left_add_width_mul_coord k hu.1 hu.2
    have h2 := J.left_add_width_mul_coord k hv.1 hv.2
    have hm : min (J.width k * (J.coord k u : ℝ)) (J.width k * (J.coord k v : ℝ)) =
        min (u : ℝ) v - J.left k := by
      rw [← min_sub_sub_right, ← h1, ← h2]
      ring_nf
    rw [hm]
    ring
  · intro l hl
    apply J.defect_eq_zero_of_not_mem
    rintro ⟨h1, h2, _, _⟩
    exact J.not_mem_of_mem_Icc hl hu.1 hu.2 ⟨h1, h2⟩

/-- The components are recovered by the affine embedding of their square. -/
theorem cdf_generalOrdinalSum_embed (k : ι) (s t : I) :
    (generalOrdinalSum J C).cdf ![J.embed k s, J.embed k t] =
      J.left k + J.width k * (C k).cdf ![s, t] := by
  rw [cdf_generalOrdinalSum_of_mem J C k ⟨J.left_le_embed k s, J.embed_le_right k s⟩
    ⟨J.left_le_embed k t, J.embed_le_right k t⟩]
  simp

theorem cdf_component_eq (k : ι) (s t : I) :
    (C k).cdf ![s, t] =
      ((generalOrdinalSum J C).cdf ![J.embed k s, J.embed k t] - J.left k) / J.width k := by
  rw [cdf_generalOrdinalSum_embed]
  field_simp [(J.width_pos k).ne']
  ring

/-- The general ordinal sum determines its components. -/
theorem generalOrdinalSum_injective : Function.Injective (generalOrdinalSum J) := by
  intro C D h
  funext k
  apply ext_cdf_two
  intro s t
  rw [cdf_component_eq J C k, cdf_component_eq J D k, h]

theorem generalOrdinalSum_eq_iff (D : ι → Copula 2) :
    generalOrdinalSum J C = generalOrdinalSum J D ↔ C = D :=
  (generalOrdinalSum_injective J).eq_iff

/-! ### Diagonal fixed points -/

/-- Outside the open intervals the diagonal of an ordinal sum is the identity. -/
theorem diagonal_generalOrdinalSum_of_not_mem (t : I)
    (h : ∀ k, ¬ (J.left k < t ∧ t < J.right k)) :
    (generalOrdinalSum J C).diagonal t = t := by
  rw [diagonal, cdf_generalOrdinalSum_of_not_mem J C t t
    (fun k hk => h k ⟨hk.1, hk.2.1⟩), min_self]

theorem diagonal_generalOrdinalSum_left (k : ι) :
    (generalOrdinalSum J C).diagonal (J.left k) = J.left k :=
  diagonal_generalOrdinalSum_of_not_mem J C _ fun l => J.left_not_mem k l

theorem diagonal_generalOrdinalSum_right (k : ι) :
    (generalOrdinalSum J C).diagonal (J.right k) = J.right k :=
  diagonal_generalOrdinalSum_of_not_mem J C _ fun l => J.right_not_mem k l

/-- Inside a square the diagonal is the rescaled diagonal of the component. -/
theorem diagonal_generalOrdinalSum_of_mem (k : ι) {t : I} (ht : J.left k ≤ t ∧ t ≤ J.right k) :
    (generalOrdinalSum J C).diagonal t = J.left k + J.width k * (C k).diagonal (J.coord k t) :=
  cdf_generalOrdinalSum_of_mem J C k ht ht

/-! ### Transpose, order and dependence -/

theorem transpose_generalOrdinalSum :
    (generalOrdinalSum J C).transpose = generalOrdinalSum J (fun k => (C k).transpose) := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_generalOrdinalSum_two, cdf_generalOrdinalSum_two, min_comm]
  simp only [cdf_transpose]

theorem IsExchangeable.generalOrdinalSum (h : ∀ k, (C k).IsExchangeable) :
    (generalOrdinalSum J C).IsExchangeable := by
  change (Copula.generalOrdinalSum J C).transpose = _
  rw [transpose_generalOrdinalSum]
  congr 1
  funext k
  exact h k

/-- An ordinal sum is exchangeable exactly when all components are. -/
theorem isExchangeable_generalOrdinalSum_iff :
    (generalOrdinalSum J C).IsExchangeable ↔ ∀ k, (C k).IsExchangeable := by
  refine ⟨fun h k => ?_, IsExchangeable.generalOrdinalSum J C⟩
  have h' : generalOrdinalSum J (fun k => (C k).transpose) = generalOrdinalSum J C := by
    rw [← transpose_generalOrdinalSum]
    exact h
  exact congrFun ((generalOrdinalSum_injective J) h') k

/-- The ordinal sum is monotone in the components for the pointwise order, and conversely. -/
theorem lowerOrthantLE_generalOrdinalSum_iff (D : ι → Copula 2) :
    (generalOrdinalSum J C).LowerOrthantLE (generalOrdinalSum J D) ↔
      ∀ k, (C k).LowerOrthantLE (D k) := by
  constructor
  · intro h k x
    have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_component_eq J C k, cdf_component_eq J D k]
    exact div_le_div_of_nonneg_right (sub_le_sub_right (h _) _) (J.width_pos k).le
  · intro h x
    rw [cdf_generalOrdinalSum, cdf_generalOrdinalSum]
    apply add_le_add le_rfl
    exact Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (h k _) (J.width_pos k).le)
      (J.summable_cdf C _ _) (J.summable_cdf D _ _)

private theorem pqd_block_bound {a w s t : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (haw : a + w ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (a + w * s) * (a + w * t) ≤ a + w * (s * t) := by
  have e : a + w * (s * t) - (a + w * s) * (a + w * t) =
      (1 - s) * (1 - t) * (a * (1 - a)) + s * (1 - t) * (a * (1 - a - w)) +
        (1 - s) * t * (a * (1 - a - w)) + s * t * ((a + w) * (1 - a - w)) := by ring
  have h1 : 0 ≤ (1 - s) * (1 - t) * (a * (1 - a)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg ha (by linarith))
  have h2 : 0 ≤ s * (1 - t) * (a * (1 - a - w)) :=
    mul_nonneg (mul_nonneg hs0 (by linarith)) (mul_nonneg ha (by linarith))
  have h3 : 0 ≤ (1 - s) * t * (a * (1 - a - w)) :=
    mul_nonneg (mul_nonneg (by linarith) ht0) (mul_nonneg ha (by linarith))
  have h4 : 0 ≤ s * t * ((a + w) * (1 - a - w)) :=
    mul_nonneg (mul_nonneg hs0 ht0) (mul_nonneg (by linarith) (by linarith))
  linarith

/-- An ordinal sum of positively quadrant dependent copulas is positively quadrant dependent. -/
theorem IsPQD.generalOrdinalSum (h : ∀ k, (C k).IsPQD) : (generalOrdinalSum J C).IsPQD := by
  intro u v
  by_cases hk : ∃ k, J.left k < u ∧ u < J.right k ∧ J.left k < v ∧ v < J.right k
  · obtain ⟨k, h1, h2, h3, h4⟩ := hk
    rw [cdf_generalOrdinalSum_of_mem J C k ⟨h1.le, h2.le⟩ ⟨h3.le, h4.le⟩]
    have hu := J.left_add_width_mul_coord k h1.le h2.le
    have hv := J.left_add_width_mul_coord k h3.le h4.le
    have hb := pqd_block_bound (J.left k).property.1 (J.width_pos k).le
      (by simp only [OrdinalIntervals.width]; linarith [(J.right k).property.2])
      (J.coord k u).property.1 (J.coord k u).property.2
      (J.coord k v).property.1 (J.coord k v).property.2
    rw [hu, hv] at hb
    have hC := mul_le_mul_of_nonneg_left (h k (J.coord k u) (J.coord k v)) (J.width_pos k).le
    linarith
  · simp only [not_exists, not_and] at hk
    rw [cdf_generalOrdinalSum_of_not_mem J C u v (fun k hk' => by
      obtain ⟨h1, h2, h3, h4⟩ := hk'
      exact absurd h4 (hk k h1 h2 h3))]
    rcases le_total (u : ℝ) v with huv | huv
    · rw [min_eq_left huv]
      exact mul_le_of_le_one_right u.property.1 v.property.2
    · rw [min_eq_right huv]
      exact mul_le_of_le_one_left v.property.1 u.property.2

/-! ### Special cases -/

/-- The ordinal sum of copies of `M` is `M`. -/
@[simp] theorem generalOrdinalSum_comonotonic :
    generalOrdinalSum J (fun _ => comonotonic 2) = comonotonic 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_generalOrdinalSum_eq_min_sub, cdf_comonotonic_two]
  simp only [OrdinalIntervals.defect, cdf_comonotonic_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_self, mul_zero, tsum_zero, sub_zero]

/-- The ordinal sum over an empty family of intervals is `M`. -/
theorem generalOrdinalSum_of_isEmpty [IsEmpty ι] : generalOrdinalSum J C = comonotonic 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_generalOrdinalSum_eq_min_sub, cdf_comonotonic_two]
  simp

namespace OrdinalIntervals

/-- The cells of a finite interval partition. -/
def ofPartition {n : ℕ} (P : IntervalPartition n) : OrdinalIntervals (Fin n) where
  left i := P.point i.castSucc
  right i := P.point i.succ
  left_lt_right _ := P.strictMono Fin.castSucc_lt_succ
  disjoint i j hij := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (P.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h))
    · exact Or.inr (P.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h))

/-- The blocks of a countable interval partition. -/
def ofCountable (P : CountableIntervalPartition) : OrdinalIntervals ℕ where
  left k := P.point k
  right k := P.point (k + 1)
  left_lt_right k := P.strictMono (Nat.lt_succ_self k)
  disjoint k l hkl := by
    rcases lt_or_gt_of_ne hkl with h | h
    · exact Or.inl (P.strictMono.monotone h)
    · exact Or.inr (P.strictMono.monotone h)

end OrdinalIntervals

/-- Finite ordinal sums on an interval partition are general ordinal sums without gaps. -/
theorem generalOrdinalSum_ofPartition {n : ℕ} (P : IntervalPartition n) (C : Fin n → Copula 2) :
    generalOrdinalSum (OrdinalIntervals.ofPartition P) C = finiteOrdinalSum P C := by
  have hgap (u : I) : (OrdinalIntervals.ofPartition P).gap u = 0 := by
    rw [OrdinalIntervals.gap, tsum_fintype]
    exact sub_eq_zero.mpr (P.sum_width_mul_coord u).symm
  apply ext_cdf
  intro u
  rw [cdf_generalOrdinalSum, cdf_finiteOrdinalSum, hgap, hgap, min_self, zero_add, tsum_fintype]
  rfl

/-- Countable ordinal sums on adjacent blocks are general ordinal sums without gaps. -/
theorem generalOrdinalSum_ofCountable (P : CountableIntervalPartition) (C : ℕ → Copula 2) :
    generalOrdinalSum (OrdinalIntervals.ofCountable P) C = countableOrdinalSum P C := by
  have hgap (u : I) : (OrdinalIntervals.ofCountable P).gap u = 0 := by
    rw [OrdinalIntervals.gap]
    exact sub_eq_zero.mpr (P.hasSum_width_mul_coord u).tsum_eq.symm
  apply ext_cdf
  intro u
  rw [cdf_generalOrdinalSum, cdf_countableOrdinalSum, hgap, hgap, min_self, zero_add]
  rfl

/-- The binary ordinal sum is a general ordinal sum over two intervals. -/
theorem ordinalSum_eq_generalOrdinalSum (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    C.ordinalSum D a =
      generalOrdinalSum (OrdinalIntervals.ofPartition (IntervalPartition.binary a ha0 ha1))
        ![C, D] := by
  rw [generalOrdinalSum_ofPartition, finiteOrdinalSum_binary]

end ProbabilityTheory.Copula
