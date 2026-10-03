/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Multivariate.LowerBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Copula.Order.Orthant

/-!
# The lower Fréchet–Hoeffding bound is pointwise best possible

**Nelsen 2006, Theorem 2.10.13.** For every `d` and every point `u ∈ [0,1]^d` there is a
`d`-copula `C` with `C(u) = W_d(u) = max(0, ∑ uᵢ - d + 1)`. Consequently `W_d` is the pointwise
infimum of all `d`-copulas (`lowerFrechetBound_eq_iInf`), although for `d ≥ 3` it is not itself a
copula (`Copula.Multivariate.LowerBound`), and for `d ≥ 3` there is no smallest `d`-copula
(`not_exists_least_copula`).

## Construction

Put `ℓᵢ = 1 - uᵢ` and the cumulative offsets `aᵢ = ℓ₀ + ⋯ + ℓᵢ₋₁`. For `V` uniform on `(0,1]`
the coordinates `Uᵢ = 1 - frac(V - aᵢ)` are uniform (`cyclicShift`, `map_cyclicShift`), and the
events `{Uᵢ > uᵢ} = {frac(V - aᵢ) < ℓᵢ}` are consecutive arcs of length `ℓᵢ` on the circle
`ℝ/ℤ`. They are disjoint when `∑ ℓᵢ ≤ 1` and cover the circle otherwise, so
`P(U ≤ u) = max(0, 1 - ∑ ℓᵢ) = W_d(u)`. This is a cyclic version of Nelsen's proof (which uses the
same disjoint-or-covering arrangement of the events `{Uᵢ > uᵢ}`).
-/

open MeasureTheory Set Finset
open scoped unitInterval BigOperators ENNReal

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-! ### Uniformity of cyclic shifts -/

/-- The cyclic shift `v ↦ 1 - frac(v - a)`, with values in `(0, 1]`. -/
noncomputable def cyclicShift (a v : ℝ) : I :=
  ⟨1 - Int.fract (v - a), by linarith [Int.fract_lt_one (v - a)],
    by linarith [Int.fract_nonneg (v - a)]⟩

theorem measurable_cyclicShift (a : ℝ) : Measurable (cyclicShift a) :=
  (measurable_const.sub (measurable_id.sub_const a).fract).subtype_mk

/-- Uniform distribution on `(0, 1]`, as a probability measure on `ℝ`. -/
noncomputable def unitIocMeasure : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Ioc 0 1), ⟨by simp [Real.volume_Ioc]⟩⟩

private theorem toMeasure_unitIocMeasure :
    (unitIocMeasure : Measure ℝ) = volume.restrict (Ioc 0 1) := rfl

/-- The preimage of a lower set under the cyclic shift: `frac(v - a) ≥ 1 - t`. -/
private theorem cyclicShift_preimage_Iic (a : ℝ) (t : I) :
    cyclicShift a ⁻¹' Iic t = {v : ℝ | 1 - (t : ℝ) ≤ Int.fract (v - a)} := by
  ext v
  change cyclicShift a v ≤ t ↔ _
  rw [← Subtype.coe_le_coe, Set.mem_ofPred_eq]
  change 1 - Int.fract (v - a) ≤ (t : ℝ) ↔ _
  constructor <;> intro h <;> linarith

private theorem volume_cyclic_window (a : ℝ) (t : I) :
    volume ({v : ℝ | 1 - (t : ℝ) ≤ Int.fract (v - a)} ∩ Ioc a (a + 1)) = ENNReal.ofReal t := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  apply le_antisymm
  · calc
      _ ≤ volume (Icc (a + 1 - t) (a + 1)) := by
        apply measure_mono
        rintro v ⟨hv, hva, hvb⟩
        refine ⟨?_, hvb⟩
        rcases hvb.lt_or_eq with hlt | heq
        · rw [Set.mem_ofPred_eq, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩] at hv
          linarith
        · linarith
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  · calc
      _ = volume (Ioo (a + 1 - t) (a + 1)) := by rw [Real.volume_Ioo]; congr 1; ring
      _ ≤ _ := by
        apply measure_mono
        rintro v ⟨hva, hvb⟩
        refine ⟨?_, by linarith, hvb.le⟩
        rw [Set.mem_ofPred_eq, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
        linarith

/-- **Cyclic shifts preserve the uniform distribution.** -/
theorem map_cyclicShift (a : ℝ) :
    (unitIocMeasure : Measure ℝ).map (cyclicShift a) = (volume : Measure I) := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_cyclicShift a) measurableSet_Iic, unitInterval.volume_Iic,
    cyclicShift_preimage_Iic, toMeasure_unitIocMeasure]
  set S := {v : ℝ | 1 - (t : ℝ) ≤ Int.fract (v - a)} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_le measurable_const (measurable_id.sub_const a).fract
  have hper : Function.Periodic (S.indicator (1 : ℝ → ℝ)) 1 := by
    intro v
    have : (v + 1 ∈ S) ↔ (v ∈ S) := by
      simp only [hSdef, Set.mem_ofPred_eq, show v + 1 - a = (v - a) + 1 by ring, Int.fract_add_one]
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (this.mpr hv)]
      rfl
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv (this.mp h))]
  have hint := hper.intervalIntegral_add_eq 0 a
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    integral_indicator_one hS, integral_indicator_one hS, zero_add] at hint
  rw [Measure.restrict_apply hS]
  rw [measureReal_def, measureReal_def, Measure.restrict_apply hS,
    Measure.restrict_apply hS, volume_cyclic_window] at hint
  have hfin : volume (S ∩ Ioc (0 : ℝ) 1) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (by simp [Real.volume_Ioc])).ne
  exact (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp hint

/-! ### Consecutive arcs -/

/-- The cumulative offsets `aₙ = ∑_{j < n} ℓⱼ`. -/
noncomputable def cyclicOffset (ℓ : Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin d => (j : ℕ) < n), ℓ j

section Offsets

variable {ℓ : Fin d → ℝ}

private theorem cyclicOffset_zero : cyclicOffset ℓ 0 = 0 := by
  simp [cyclicOffset]

private theorem cyclicOffset_succ (i : Fin d) :
    cyclicOffset ℓ (i + 1) = cyclicOffset ℓ i + ℓ i := by
  unfold cyclicOffset
  have h : univ.filter (fun j : Fin d => (j : ℕ) < i + 1) =
      insert i (univ.filter (fun j : Fin d => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Nat.lt_succ_iff]
    constructor
    · intro hj
      rcases hj.lt_or_eq with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (Fin.ext heq)
    · rintro (h | hj)
      · rw [h]
      · exact hj.le
  rw [h, Finset.sum_insert (by simp), add_comm]

private theorem cyclicOffset_mono (hℓ : ∀ i, 0 ≤ ℓ i) {n m : ℕ} (h : n ≤ m) :
    cyclicOffset ℓ n ≤ cyclicOffset ℓ m := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hj
    exact lt_of_lt_of_le hj h
  · intro i _ _
    exact hℓ i

private theorem cyclicOffset_nonneg (hℓ : ∀ i, 0 ≤ ℓ i) (n : ℕ) : 0 ≤ cyclicOffset ℓ n :=
  Finset.sum_nonneg fun i _ => hℓ i

private theorem cyclicOffset_le_sum (hℓ : ∀ i, 0 ≤ ℓ i) (n : ℕ) :
    cyclicOffset ℓ n ≤ ∑ i, ℓ i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => hℓ i

private theorem cyclicOffset_dim : cyclicOffset ℓ d = ∑ i, ℓ i := by
  unfold cyclicOffset
  congr 1
  ext j
  simp

/-- **Consecutive arcs.** For `v ∈ (0,1)`, some `frac(v - aᵢ)` is below `ℓᵢ` exactly when
`v < ∑ ℓᵢ`. -/
theorem exists_fract_lt_iff (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (∃ i : Fin d, Int.fract (v - cyclicOffset ℓ i) < ℓ i) ↔ v < ∑ i, ℓ i := by
  constructor
  · rintro ⟨i, hi⟩
    have hk : ⌊v - cyclicOffset ℓ i⌋ ≤ 0 := by
      have h1 := Int.floor_le (v - cyclicOffset ℓ i)
      have h2 := cyclicOffset_nonneg hℓ0 i
      have : (⌊v - cyclicOffset ℓ i⌋ : ℝ) < 1 := by linarith
      exact_mod_cast (show (⌊v - cyclicOffset ℓ i⌋ : ℝ) ≤ 0 by
        have := Int.cast_lt.mp (show (⌊v - cyclicOffset ℓ i⌋ : ℝ) < ((1 : ℤ) : ℝ) by
          simpa using this)
        exact_mod_cast Int.lt_add_one_iff.mp (by simpa using this))
    have hkR : (⌊v - cyclicOffset ℓ i⌋ : ℝ) ≤ 0 := by exact_mod_cast hk
    have hf : Int.fract (v - cyclicOffset ℓ i) = v - cyclicOffset ℓ i - ⌊v - cyclicOffset ℓ i⌋ :=
      rfl
    have hs := cyclicOffset_succ (ℓ := ℓ) i
    have hle := cyclicOffset_le_sum hℓ0 (i + 1)
    linarith
  · intro hv
    have hex : ∃ n, v < cyclicOffset ℓ (n + 1) := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd
        simp at hv
        linarith
      · refine ⟨d - 1, ?_⟩
        rw [Nat.sub_add_cancel hd, cyclicOffset_dim]
        exact hv
    classical
    set n := Nat.find hex with hn
    have hnspec : v < cyclicOffset ℓ (n + 1) := Nat.find_spec hex
    have hnd : n < d := by
      by_contra hcon
      push Not at hcon
      have h1 : cyclicOffset ℓ (n + 1) = ∑ i, ℓ i := by
        unfold cyclicOffset
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        omega
      have hd : 0 < d := by
        rcases Nat.eq_zero_or_pos d with hd | hd
        · subst hd; simp at hv; linarith
        · exact hd
      have := Nat.find_min' hex (show v < cyclicOffset ℓ (d - 1 + 1) by
        rw [Nat.sub_add_cancel hd, cyclicOffset_dim]; exact hv)
      omega
    have hlow : cyclicOffset ℓ n ≤ v := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, cyclicOffset_zero]
        exact hv0
      · have := Nat.find_min hex (show n - 1 < n by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact not_lt.mp this
    refine ⟨⟨n, hnd⟩, ?_⟩
    have hs := cyclicOffset_succ (ℓ := ℓ) ⟨n, hnd⟩
    simp only at hs
    rw [Int.fract_eq_self.mpr ⟨by simp only; linarith, by simp only; linarith [hℓ1 ⟨n, hnd⟩]⟩]
    simp only
    linarith

end Offsets

/-! ### The attaining copula -/

/-- The cyclic copula attaining `W_d` at the point `u`: the law of
`(1 - frac(V - aᵢ))ᵢ` with `aᵢ = ∑_{j<i} (1 - uⱼ)` and `V` uniform. -/
noncomputable def lowerBoundWitness (u : Fin d → I) : Copula d :=
  ofMap unitIocMeasure
    (fun v i => cyclicShift (cyclicOffset (fun j => 1 - (u j : ℝ)) i) v)
    (Measurable.of_eval fun _ => measurable_cyclicShift _)
    (fun _ => map_cyclicShift _)

/-- **Nelsen 2006, Theorem 2.10.13**: the witness copula attains the lower bound at `u`. -/
theorem cdf_lowerBoundWitness (u : Fin d → I) :
    (lowerBoundWitness u).cdf u = lowerFrechetBound d u := by
  set ℓ : Fin d → ℝ := fun j => 1 - (u j : ℝ) with hℓ
  have hℓ0 : ∀ i, 0 ≤ ℓ i := fun i => sub_nonneg.mpr (u i).property.2
  have hℓ1 : ∀ i, ℓ i ≤ 1 := fun i => by simp only [hℓ]; linarith [(u i).property.1]
  have hX : Measurable (fun v (i : Fin d) => cyclicShift (cyclicOffset ℓ i) v) :=
    Measurable.of_eval fun i => measurable_cyclicShift _
  set L := ∑ i, ℓ i with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => hℓ0 i
  have hset : (fun v (i : Fin d) => cyclicShift (cyclicOffset ℓ i) v) ⁻¹' Iic u ∩ Ioo 0 1 =
      {v : ℝ | L ≤ v} ∩ Ioo 0 1 := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨hv, h0, h1⟩
      refine ⟨?_, h0, h1⟩
      by_contra hlt
      push Not at hlt
      obtain ⟨i, hi⟩ := (exists_fract_lt_iff hℓ0 hℓ1 h0.le h1).mpr hlt
      have := hv i
      rw [← Subtype.coe_le_coe] at this
      simp only [cyclicShift, hℓ] at this hi
      linarith
    · rintro ⟨hv, h0, h1⟩
      refine ⟨?_, h0, h1⟩
      intro i
      have hn : ¬ ∃ i : Fin d, Int.fract (v - cyclicOffset ℓ i) < ℓ i := by
        rw [exists_fract_lt_iff hℓ0 hℓ1 h0.le h1]
        exact not_lt.mpr hv
      push Not at hn
      have := hn i
      rw [← Subtype.coe_le_coe]
      simp only [cyclicShift, hℓ] at this ⊢
      linarith
  have hmeasS : MeasurableSet ((fun v (i : Fin d) => cyclicShift (cyclicOffset ℓ i) v) ⁻¹'
      Iic u) := hX measurableSet_Iic
  have hIoc : volume.restrict (Ioc (0 : ℝ) 1) = volume.restrict (Ioo 0 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm
  rw [cdf, lowerBoundWitness, toMeasure_ofMap,
    map_measureReal_apply hX measurableSet_Iic]
  change (volume.restrict (Ioc (0 : ℝ) 1)).real _ = _
  rw [hIoc, measureReal_def, Measure.restrict_apply hmeasS, hset]
  have hvol : volume ({v : ℝ | L ≤ v} ∩ Ioo 0 1) = ENNReal.ofReal (1 - L) := by
    apply le_antisymm
    · calc
        _ ≤ volume (Icc L 1) := by
          apply measure_mono
          rintro v ⟨hv, _, h1⟩
          exact ⟨hv, h1.le⟩
        _ = _ := Real.volume_Icc
    · calc
        _ = volume (Ioo L 1) := Real.volume_Ioo.symm
        _ ≤ _ := by
          apply measure_mono
          rintro v ⟨h0, h1⟩
          exact ⟨h0.le, lt_of_le_of_lt hL0 h0, h1⟩
  rw [hvol, ENNReal.toReal_ofReal', lowerFrechetBound, max_comm]
  congr 1
  simp only [hL, hℓ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- **Nelsen 2006, Theorem 2.10.13**: for every `u` some `d`-copula attains `W_d(u)`. -/
theorem exists_cdf_eq_lowerFrechetBound (u : Fin d → I) :
    ∃ C : Copula d, C.cdf u = lowerFrechetBound d u :=
  ⟨lowerBoundWitness u, cdf_lowerBoundWitness u⟩

/-- `W_d` is the pointwise infimum of all `d`-copulas. -/
theorem lowerFrechetBound_eq_iInf (u : Fin d → I) :
    lowerFrechetBound d u = ⨅ C : Copula d, C.cdf u := by
  apply le_antisymm
  · exact le_ciInf fun C => lowerFrechetBound_le_cdf C u
  · rw [← cdf_lowerBoundWitness u]
    exact ciInf_le ⟨0, by rintro _ ⟨C, rfl⟩; exact C.cdf_nonneg u⟩ _

/-- **For `d ≥ 3` there is no smallest `d`-copula** in the pointwise order. -/
theorem not_exists_least_copula (hd : 3 ≤ d) :
    ¬ ∃ C : Copula d, ∀ D : Copula d, C.LowerOrthantLE D := by
  rintro ⟨C, hC⟩
  apply cdf_ne_lowerFrechetBound hd C
  funext u
  apply le_antisymm
  · rw [← cdf_lowerBoundWitness u]
    exact hC _ u
  · exact lowerFrechetBound_le_cdf C u

end ProbabilityTheory.Copula
