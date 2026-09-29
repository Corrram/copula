/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rearrangement.Primitive

/-! # Level sets of the primitive and of its rearranged primitive

The level-set step of the primitive comparison lemma: with `F = primDev h v` and
`G = rearrDev h v`,

`λ{|F| > y} ≤ λ{G > y}` for every `y ≥ 0`,

and, when `F` exceeds `y` somewhere, the quantitative improvement
`λ{|F| > y} + λ{-y < F < 0} ≤ λ{G > y}` which yields the strict inequalities.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ## Excursions of a continuous function on the unit interval -/

/-- For a continuous `F` on `[0,1]` with `F(0) = F(1) = 0` that exceeds `y > 0` at some point,
there are intervals `(a,b)` before and `(c,d)` after the level set `{F ≥ y}` on which
`0 < F ≤ y`, with `F ≤ 0` at the outer endpoints and `F ≥ y` at the inner ones. -/
theorem exists_positive_excursions (F : ℝ → ℝ) (hF : Continuous F) (h0 : F 0 = 0)
    (h1 : F 1 = 0) {y : ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hty : y < F t) :
    ∃ a b c d : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ 1 ∧ F a ≤ 0 ∧ y ≤ F b ∧ y ≤ F c ∧
      F d ≤ 0 ∧ (∀ u ∈ Ioo a b, 0 < F u ∧ F u ≤ y) ∧ (∀ u ∈ Ioo c d, 0 < F u ∧ F u ≤ y) := by
  set S : Set ℝ := Icc 0 1 ∩ {u | y ≤ F u} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const hF)
  have hSn : S.Nonempty := ⟨t, ht, hty.le⟩
  have hSb : BddBelow S := bddBelow_Icc.mono inter_subset_left
  have hSa : BddAbove S := bddAbove_Icc.mono inter_subset_left
  have hb := hSc.csInf_mem hSn hSb
  have hc := hSc.csSup_mem hSn hSa
  set b := sInf S
  set c := sSup S
  have hbc : b ≤ c := (csInf_le hSb ⟨ht, hty.le⟩).trans (le_csSup hSa ⟨ht, hty.le⟩)
  have hlt_b : ∀ u ∈ Icc (0 : ℝ) 1, u < b → F u < y := by
    intro u hu hub
    by_contra hcon
    push Not at hcon
    exact absurd (csInf_le hSb ⟨hu, hcon⟩) (not_le.mpr hub)
  have hgt_c : ∀ u ∈ Icc (0 : ℝ) 1, c < u → F u < y := by
    intro u hu huc
    by_contra hcon
    push Not at hcon
    exact absurd (le_csSup hSa ⟨hu, hcon⟩) (not_le.mpr huc)
  set T₁ : Set ℝ := Icc 0 b ∩ {u | F u ≤ 0} with hT₁
  have hT₁c : IsClosed T₁ := isClosed_Icc.inter (isClosed_le hF continuous_const)
  have hT₁n : T₁.Nonempty := ⟨0, ⟨le_rfl, hb.1.1⟩, h0.le⟩
  have hT₁a : BddAbove T₁ := bddAbove_Icc.mono inter_subset_left
  have ha := hT₁c.csSup_mem hT₁n hT₁a
  set a := sSup T₁
  set T₂ : Set ℝ := Icc c 1 ∩ {u | F u ≤ 0} with hT₂
  have hT₂c : IsClosed T₂ := isClosed_Icc.inter (isClosed_le hF continuous_const)
  have hT₂n : T₂.Nonempty := ⟨1, ⟨hc.1.2, le_rfl⟩, h1.le⟩
  have hT₂b : BddBelow T₂ := bddBelow_Icc.mono inter_subset_left
  have hd := hT₂c.csInf_mem hT₂n hT₂b
  set d := sInf T₂
  refine ⟨a, b, c, d, ha.1.1, ha.1.2, hbc, hd.1.1, hd.1.2, ha.2, hb.2, hc.2, hd.2, ?_, ?_⟩
  · intro u hu
    have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨ha.1.1.trans hu.1.le, hu.2.le.trans hb.1.2⟩
    refine ⟨?_, (hlt_b u hu1 hu.2).le⟩
    by_contra hcon
    push Not at hcon
    exact absurd (le_csSup hT₁a ⟨⟨hu1.1, hu.2.le⟩, hcon⟩) (not_le.mpr hu.1)
  · intro u hu
    have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hc.1.1.trans hu.1.le, hu.2.le.trans hd.1.2⟩
    refine ⟨?_, (hgt_c u hu1 hu.1).le⟩
    by_contra hcon
    push Not at hcon
    exact absurd (csInf_le hT₂b ⟨⟨hu.1.le, hu1.2⟩, hcon⟩) (not_le.mpr hu.2)

/-! ## The level-set comparison -/

section Main

variable {h : I → ℝ} {v : ℝ}

/-- The key estimate behind the level-set comparison: two disjoint sets on which `|F| ≤ y`,
carrying mass `≥ y` and `≤ -y` of `f = h - v`, force `λ{|F| > y} + λ(J) ≤ λ{G ≥ y}` for every
further set `J` inside `{|F| ≤ y}` disjoint from both. -/
theorem level_bound_of_sets (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) {y : ℝ} (E₁ E₂ J : Set I)
    (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂) (hJ : MeasurableSet J)
    (h12 : Disjoint E₁ E₂) (hJ1 : Disjoint J E₁) (hJ2 : Disjoint J E₂)
    (hm₁ : y ≤ (∫ u in E₁, h u) - volume.real E₁ * v)
    (hm₂ : (∫ u in E₂, h u) - volume.real E₂ * v ≤ -y)
    (hb₁ : ∀ u ∈ E₁, |primDev h v u| ≤ y) (hb₂ : ∀ u ∈ E₂, |primDev h v u| ≤ y)
    (hbJ : ∀ u ∈ J, |primDev h v u| ≤ y) :
    volume.real {u : I | y < |primDev h v u|} + volume.real J ≤
      volume.real {u : I | y ≤ rearrDev h v u} := by
  have hG₁ : y ≤ rearrDev h v (measureUnit E₁) :=
    hm₁.trans (integral_set_sub_le_rearrDev hf0 hf1 hm E₁)
  have hG₂ : y ≤ rearrDev h v (unitInterval.symm (measureUnit E₂)) := by
    have := neg_rearrDev_le_integral_set_sub hf0 hf1 hm hv E₂ hE₂
    linarith
  have hmeasF : MeasurableSet {u : I | y < |primDev h v u|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_primDev (v := v) hf0 hf1 hm))
  have hmeasG : MeasurableSet {u : I | y ≤ rearrDev h v u} :=
    measurableSet_le measurable_const (measurable_rearrDev hf1)
  -- the union E₁ ∪ E₂ has measure λ(E₁) + λ(E₂) and is disjoint from {|F| > y} ∪ J
  have hunion : volume.real (E₁ ∪ E₂) = volume.real E₁ + volume.real E₂ :=
    measureReal_union h12 hE₂
  have hle1 : volume.real E₁ + volume.real E₂ ≤ 1 := by
    rw [← hunion]; exact measureReal_le_one
  have hdisj : Disjoint ({u : I | y < |primDev h v u|} ∪ J) (E₁ ∪ E₂) := by
    refine Disjoint.union_left (Disjoint.union_right ?_ ?_) (Disjoint.union_right hJ1 hJ2)
    · rw [Set.disjoint_left]
      intro u hu hu'
      exact absurd (hb₁ u hu') (not_le.mpr hu)
    · rw [Set.disjoint_left]
      intro u hu hu'
      exact absurd (hb₂ u hu') (not_le.mpr hu)
  have hdisjFJ : Disjoint {u : I | y < |primDev h v u|} J := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd (hbJ u hu') (not_le.mpr hu)
  have hsum : volume.real {u : I | y < |primDev h v u|} + volume.real J +
      (volume.real E₁ + volume.real E₂) ≤ 1 := by
    rw [← measureReal_union hdisjFJ hJ, ← hunion, ← measureReal_union hdisj (hE₁.union hE₂)]
    exact measureReal_le_one
  -- concavity: G ≥ y between λ(E₁) and 1 - λ(E₂)
  have hs : (measureUnit E₁ : ℝ) ≤ (unitInterval.symm (measureUnit E₂) : ℝ) := by
    rw [unitInterval.coe_symm_eq, coe_measureUnit, coe_measureUnit]
    linarith
  have hsub : Icc (measureUnit E₁) (unitInterval.symm (measureUnit E₂)) ⊆
      {u : I | y ≤ rearrDev h v u} := by
    intro u hu
    exact rearrDev_ge_of_ge hf1 hu.1 hu.2 hG₁ hG₂
  have hI := measureReal_mono (μ := (volume : Measure I)) hsub
  rw [measureReal_Icc_unit _ _ hs, unitInterval.coe_symm_eq, coe_measureUnit,
    coe_measureUnit] at hI
  linarith

/-- The level-set inequality with closed level sets of `G`, for `y > 0`, together with the
improvement by `λ{-y < F < 0}` when `F` exceeds `y` somewhere. -/
theorem level_bound_ge (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) {y : ℝ} (hy : 0 < y) :
    volume.real {u : I | y < |primDev h v u|} ≤ volume.real {u : I | y ≤ rearrDev h v u} ∧
    ((∃ t, y < primDev h v t) →
      volume.real {u : I | y < |primDev h v u|} +
        volume.real {u : I | -y < primDev h v u ∧ primDev h v u < 0} ≤
          volume.real {u : I | y ≤ rearrDev h v u}) := by
  have hFc := continuous_primDev (v := v) hf0 hf1 hm
  set F : ℝ → ℝ := fun t => primDev h v (projIcc 0 1 zero_le_one t) with hFdef
  have hFcont : Continuous F := hFc.comp continuous_projIcc
  have hF0 : F 0 = 0 := by simp [F, primDev_zero]
  have hF1 : F 1 = 0 := by simp [F, primDev_one hv]
  have hFeq : ∀ u : I, F u = primDev h v u := fun u => by simp [F]
  have hmeasJ : MeasurableSet {u : I | -y < primDev h v u ∧ primDev h v u < 0} :=
    (measurableSet_lt measurable_const (measurable_primDev hf0 hf1 hm)).inter
      (measurableSet_lt (measurable_primDev hf0 hf1 hm) measurable_const)
  -- the mass of `f` on an open interval is the increment of `F`
  have hmass : ∀ a b : I, a ≤ b →
      (∫ u in Ioo a b, h u) - volume.real (Ioo a b) * v = primDev h v b - primDev h v a := by
    intro a b hab
    rw [← primitive_sub_primitive_Ioo hf0 hf1 hm hab, measureReal_Ioo_unit a b hab]
    unfold primDev
    ring
  -- the positive case: `F` exceeds `y`
  have hpos : (∃ t, y < primDev h v t) →
      volume.real {u : I | y < |primDev h v u|} +
        volume.real {u : I | -y < primDev h v u ∧ primDev h v u < 0} ≤
          volume.real {u : I | y ≤ rearrDev h v u} := by
    rintro ⟨t, ht⟩
    obtain ⟨a, b, c, d, ha0, hab, hbc, hcd, hd1, hFa, hFb, hFc', hFd, hab', hcd'⟩ :=
      exists_positive_excursions (y := y) F hFcont hF0 hF1 (t := t) t.property (by rw [hFeq]; exact ht)
    let a' : I := ⟨a, ha0, hab.trans (hbc.trans (hcd.trans hd1))⟩
    let b' : I := ⟨b, ha0.trans hab, hbc.trans (hcd.trans hd1)⟩
    let c' : I := ⟨c, ha0.trans (hab.trans hbc), hcd.trans hd1⟩
    let d' : I := ⟨d, ha0.trans (hab.trans (hbc.trans hcd)), hd1⟩
    have hFa' : primDev h v a' ≤ 0 := by rw [← hFeq]; exact hFa
    have hFb' : y ≤ primDev h v b' := by rw [← hFeq]; exact hFb
    have hFc'' : y ≤ primDev h v c' := by rw [← hFeq]; exact hFc'
    have hFd' : primDev h v d' ≤ 0 := by rw [← hFeq]; exact hFd
    apply level_bound_of_sets (y := y) hf0 hf1 hm hv (Ioo a' b') (Ioo c' d')
      {u : I | -y < primDev h v u ∧ primDev h v u < 0} measurableSet_Ioo measurableSet_Ioo hmeasJ
    · exact Set.disjoint_left.mpr fun u hu hu' => absurd (hu.2.trans_le hbc) (not_lt.mpr hu'.1.le)
    · exact Set.disjoint_left.mpr fun u hu hu' => by
        have := (hab' u ⟨hu'.1, hu'.2⟩).1
        rw [hFeq] at this
        exact absurd hu.2 (not_lt.mpr this.le)
    · exact Set.disjoint_left.mpr fun u hu hu' => by
        have := (hcd' u ⟨hu'.1, hu'.2⟩).1
        rw [hFeq] at this
        exact absurd hu.2 (not_lt.mpr this.le)
    · rw [hmass a' b' hab]; linarith
    · rw [hmass c' d' hcd]; linarith
    · intro u hu
      have := hab' u ⟨hu.1, hu.2⟩
      rw [hFeq] at this
      exact abs_le.mpr ⟨by linarith, this.2⟩
    · intro u hu
      have := hcd' u ⟨hu.1, hu.2⟩
      rw [hFeq] at this
      exact abs_le.mpr ⟨by linarith, this.2⟩
    · intro u hu
      exact abs_le.mpr ⟨hu.1.le, by linarith [hu.2]⟩
  refine ⟨?_, hpos⟩
  by_cases hA : ∃ t, y < primDev h v t
  · have := hpos hA
    linarith [measureReal_nonneg (μ := (volume : Measure I))
      (s := {u : I | -y < primDev h v u ∧ primDev h v u < 0})]
  by_cases hB : ∃ t, primDev h v t < -y
  · -- the negative case: apply the excursion lemma to `-F`
    obtain ⟨t, ht⟩ := hB
    obtain ⟨a, b, c, d, ha0, hab, hbc, hcd, hd1, hFa, hFb, hFc', hFd, hab', hcd'⟩ :=
      exists_positive_excursions (y := y) (fun s => -F s) hFcont.neg (by simp [hF0]) (by simp [hF1])
        (t := t) t.property (by simp only [hFeq]; linarith)
    let a' : I := ⟨a, ha0, hab.trans (hbc.trans (hcd.trans hd1))⟩
    let b' : I := ⟨b, ha0.trans hab, hbc.trans (hcd.trans hd1)⟩
    let c' : I := ⟨c, ha0.trans (hab.trans hbc), hcd.trans hd1⟩
    let d' : I := ⟨d, ha0.trans (hab.trans (hbc.trans hcd)), hd1⟩
    have hFa' : 0 ≤ primDev h v a' := by rw [← hFeq]; show 0 ≤ F a; linarith
    have hFb' : primDev h v b' ≤ -y := by rw [← hFeq]; show F b ≤ -y; linarith
    have hFc'' : primDev h v c' ≤ -y := by rw [← hFeq]; show F c ≤ -y; linarith
    have hFd' : 0 ≤ primDev h v d' := by rw [← hFeq]; show 0 ≤ F d; linarith
    have := level_bound_of_sets (y := y) hf0 hf1 hm hv (Ioo c' d') (Ioo a' b') ∅ measurableSet_Ioo
      measurableSet_Ioo MeasurableSet.empty
      (Set.disjoint_left.mpr fun u hu hu' =>
        absurd (hu'.2.trans_le hbc) (not_lt.mpr hu.1.le))
      (Set.disjoint_left.mpr fun u hu => absurd hu (Set.notMem_empty u))
      (Set.disjoint_left.mpr fun u hu => absurd hu (Set.notMem_empty u))
      (by rw [hmass c' d' hcd]; linarith) (by rw [hmass a' b' hab]; linarith)
      (fun u hu => by
        have := hcd' u ⟨hu.1, hu.2⟩
        simp only [hFeq] at this
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
      (fun u hu => by
        have := hab' u ⟨hu.1, hu.2⟩
        simp only [hFeq] at this
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
      (fun u hu => absurd hu (Set.notMem_empty u))
    simpa using this
  · -- both sets empty: `{|F| > y}` is empty
    push Not at hA hB
    have he : {u : I | y < |primDev h v u|} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact abs_le.mpr ⟨hB u, hA u⟩
    rw [he]
    simp [measureReal_nonneg]

/-- Passing from closed to open level sets of `b` by letting `y' ↓ y`. -/
theorem measure_gt_add_le_of_forall {a b : I → ℝ} {y y₁ : ℝ} (hy : y < y₁) (c : ℝ)
    (hle : ∀ y' ∈ Ioo y y₁,
      volume.real {u : I | y' < a u} + c ≤ volume.real {u : I | y' ≤ b u}) :
    volume.real {u : I | y < a u} + c ≤ volume.real {u : I | y < b u} := by
  set s : ℕ → Set I := fun n => {u : I | y + 1 / ((n : ℝ) + 1) < a u} with hs
  have hU : {u : I | y < a u} = ⋃ n, s n := by
    ext u
    simp only [hs, mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone s := by
    intro m n hmn u hu
    simp only [hs, mem_ofPred_eq] at hu ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have hseq := tendsto_measure_iUnion_atTop (μ := (volume : Measure I)) hmono
  rw [← hU] at hseq
  have hreal : Tendsto (fun n : ℕ => volume.real (s n) + c) atTop
      (𝓝 (volume.real {u : I | y < a u} + c)) :=
    ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hseq).add_const c
  apply le_of_tendsto hreal
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hle' : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  have h1 := hle (y + 1 / ((n : ℝ) + 1)) ⟨by linarith, by linarith⟩
  have h2 : volume.real {u : I | y + 1 / ((n : ℝ) + 1) ≤ b u} ≤ volume.real {u : I | y < b u} :=
    measureReal_mono (fun u (hu : y + 1 / ((n : ℝ) + 1) ≤ b u) =>
      (lt_of_lt_of_le (by linarith) hu : y < b u))
  exact h1.trans h2

/-- Level-set comparison: `λ{|F| > y} ≤ λ{G > y}` for every `y ≥ 0`. -/
theorem measure_abs_primDev_gt_le (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1) (hm : Measurable h)
    (hv : (∫ u, h u) = v) {y : ℝ} (hy : 0 ≤ y) :
    volume.real {u : I | y < |primDev h v u|} ≤ volume.real {u : I | y < rearrDev h v u} := by
  have := measure_gt_add_le_of_forall (a := fun u => |primDev h v u|) (b := rearrDev h v)
    (y := y) (y₁ := y + 1) (by linarith) 0 (fun y' hy' => by
      rw [add_zero]
      exact (level_bound_ge hf0 hf1 hm hv (hy.trans_lt hy'.1)).1)
  simpa using this

/-- Quantitative level-set comparison: when `F` exceeds `y ≥ 0` somewhere, the open set `{-y < F < 0}` is
disjoint from the level set `{|F| > y}` and both together still fit into `{G > y}`. -/
theorem measure_abs_primDev_gt_add_le (hf0 : ∀ u, 0 ≤ h u) (hf1 : ∀ u, h u ≤ 1)
    (hm : Measurable h) (hv : (∫ u, h u) = v) {y : ℝ} (hy : 0 ≤ y) {t : I}
    (ht : y < primDev h v t) :
    volume.real {u : I | y < |primDev h v u|} +
      volume.real {u : I | -y < primDev h v u ∧ primDev h v u < 0} ≤
        volume.real {u : I | y < rearrDev h v u} := by
  apply measure_gt_add_le_of_forall (a := fun u => |primDev h v u|) (b := rearrDev h v)
    (y := y) (y₁ := primDev h v t) ht
  intro y' hy'
  have h1 := (level_bound_ge hf0 hf1 hm hv (hy.trans_lt hy'.1)).2 ⟨t, hy'.2⟩
  have h2 : volume.real {u : I | -y < primDev h v u ∧ primDev h v u < 0} ≤
      volume.real {u : I | -y' < primDev h v u ∧ primDev h v u < 0} :=
    measureReal_mono (fun u hu => ⟨by linarith [hu.1, hy'.1], hu.2⟩)
  linarith

end Main

end ProbabilityTheory.Copula
