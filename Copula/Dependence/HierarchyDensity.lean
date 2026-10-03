/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.HierarchyCorner
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.DensityTotalPositivity

/-!
# Total positivity of the copula measure and the positive dependence hierarchy

A bivariate copula `C` is *TP2 as a measure* (`IsTP2Measure`) if for all measurable sets
`S₁ ≤ S₂` and `T₁ ≤ T₂` of `[0,1]` (every point of the first set below every point of the
second)

`C(S₁ × T₂) · C(S₂ × T₁) ≤ C(S₁ × T₁) · C(S₂ × T₂)`.

For absolutely continuous copulas this is Lehmann's positive likelihood ratio dependence: we
prove that an MTP2 (log-supermodular) Lebesgue density implies it
(`HasMTP2Density.isTP2Measure`), by integrating the pointwise TP2 inequality as in the
basic composition formula of Karlin. The measure form also covers singular copulas: `M` is TP2
as a measure but has no density.

From `IsTP2Measure` we obtain, by choosing the four sets as intervals, the top of the positive
dependence hierarchy of Nelsen, *An Introduction to Copulas*, 2nd ed., §5.2.3, and Joe,
*Multivariate Models and Dependence Concepts* (1997), §2.1:

```text
TP2 density ⟹ IsTP2Measure ⟹ SI(V|U) and SI(U|V) (i.e. CI) ⟹ LTD, RTI ⟹ PQD
                          ⟹ LCSD (= TP2 CDF) ⟹ LTD in both directions
                          ⟹ RCSI (= TP2 survival function) ⟹ RTI in both directions
```

`rectMass C S T` denotes the copula mass of the product set `S × T`.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The copula mass of the product set `S × T`. -/
noncomputable def rectMass (C : Copula 2) (S T : Set I) : ℝ :=
  C.toMeasure.real {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ T}

/-- Total positivity of order two of the copula measure on ordered product sets. -/
def IsTP2Measure (C : Copula 2) : Prop :=
  ∀ S₁ S₂ T₁ T₂ : Set I, MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet T₁ →
    MeasurableSet T₂ → (∀ s ∈ S₁, ∀ s' ∈ S₂, s ≤ s') → (∀ t ∈ T₁, ∀ t' ∈ T₂, t ≤ t') →
      C.rectMass S₁ T₂ * C.rectMass S₂ T₁ ≤ C.rectMass S₁ T₁ * C.rectMass S₂ T₂

/-! ## Rectangle masses -/

section RectMass

variable (C : Copula 2)

theorem measurableSet_rect {S T : Set I} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    MeasurableSet {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ T} :=
  (hS.preimage (measurable_pi_apply 0)).inter (hT.preimage (measurable_pi_apply 1))

theorem rectMass_union_left {S S' T : Set I} (hS' : MeasurableSet S') (hT : MeasurableSet T)
    (hd : Disjoint S S') : C.rectMass (S ∪ S') T = C.rectMass S T + C.rectMass S' T := by
  unfold rectMass
  have he : {x : Fin 2 → I | x 0 ∈ S ∪ S' ∧ x 1 ∈ T} =
      {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ T} ∪ {x | x 0 ∈ S' ∧ x 1 ∈ T} := by
    ext x; simp only [mem_union, mem_ofPred_eq]; tauto
  rw [he, measureReal_union _ (measurableSet_rect hS' hT)]
  exact Set.disjoint_left.mpr fun x hx hx' => Set.disjoint_left.mp hd hx.1 hx'.1

theorem rectMass_union_right {S T T' : Set I} (hS : MeasurableSet S) (hT' : MeasurableSet T')
    (hd : Disjoint T T') : C.rectMass S (T ∪ T') = C.rectMass S T + C.rectMass S T' := by
  unfold rectMass
  have he : {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ T ∪ T'} =
      {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ T} ∪ {x | x 0 ∈ S ∧ x 1 ∈ T'} := by
    ext x; simp only [mem_union, mem_ofPred_eq]; tauto
  rw [he, measureReal_union _ (measurableSet_rect hS hT')]
  exact Set.disjoint_left.mpr fun x hx hx' => Set.disjoint_left.mp hd hx.2 hx'.2

theorem rectMass_univ_right {S : Set I} (hS : MeasurableSet S) :
    C.rectMass S univ = volume.real S := by
  unfold rectMass Measure.real
  have he : {x : Fin 2 → I | x 0 ∈ S ∧ x 1 ∈ univ} = (fun x => x 0) ⁻¹' S := by
    ext x; simp
  rw [he, C.measure_preimage_eval 0 hS]

theorem rectMass_univ_left {T : Set I} (hT : MeasurableSet T) :
    C.rectMass univ T = volume.real T := by
  unfold rectMass Measure.real
  have he : {x : Fin 2 → I | x 0 ∈ univ ∧ x 1 ∈ T} = (fun x => x 1) ⁻¹' T := by
    ext x; simp
  rw [he, C.measure_preimage_eval 1 hT]

theorem rectMass_Iic_Iic (a b : I) : C.rectMass (Iic a) (Iic b) = C.cdf ![a, b] := by
  unfold rectMass cdf
  congr 1
  ext x
  simp [Pi.le_def, Fin.forall_fin_two]

theorem rectMass_Ioc_left {a b : I} (hab : a ≤ b) {T : Set I} (hT : MeasurableSet T) :
    C.rectMass (Ioc a b) T = C.rectMass (Iic b) T - C.rectMass (Iic a) T := by
  rw [← Iic_union_Ioc_eq_Iic hab, C.rectMass_union_left measurableSet_Ioc hT
    (Iic_disjoint_Ioc le_rfl)]
  ring

theorem rectMass_Ioc_right {c d : I} (hcd : c ≤ d) {S : Set I} (hS : MeasurableSet S) :
    C.rectMass S (Ioc c d) = C.rectMass S (Iic d) - C.rectMass S (Iic c) := by
  rw [← Iic_union_Ioc_eq_Iic hcd, C.rectMass_union_right hS measurableSet_Ioc
    (Iic_disjoint_Ioc le_rfl)]
  ring

theorem rectMass_Ioi_left (a : I) {T : Set I} (hT : MeasurableSet T) :
    C.rectMass (Ioi a) T = C.rectMass univ T - C.rectMass (Iic a) T := by
  rw [← Iic_union_Ioi (a := a), C.rectMass_union_left (S := Iic a) measurableSet_Ioi hT
    (Set.disjoint_left.mpr fun _ hx hx' => not_lt.mpr (mem_Iic.mp hx) (mem_Ioi.mp hx'))]
  ring

theorem rectMass_Ioi_right (c : I) {S : Set I} (hS : MeasurableSet S) :
    C.rectMass S (Ioi c) = C.rectMass S univ - C.rectMass S (Iic c) := by
  rw [← Iic_union_Ioi (a := c), C.rectMass_union_right (T := Iic c) hS measurableSet_Ioi
    (Set.disjoint_left.mpr fun _ hx hx' => not_lt.mpr (mem_Iic.mp hx) (mem_Ioi.mp hx'))]
  ring

theorem rectMass_Iic_Ioi (a c : I) :
    C.rectMass (Iic a) (Ioi c) = (a : ℝ) - C.cdf ![a, c] := by
  rw [C.rectMass_Ioi_right c measurableSet_Iic, C.rectMass_univ_right measurableSet_Iic,
    C.rectMass_Iic_Iic, Measure.real, unitInterval.volume_Iic, ENNReal.toReal_ofReal a.2.1]

theorem rectMass_Ioi_Ioi (a c : I) :
    C.rectMass (Ioi a) (Ioi c) = C.survival ![a, c] := by
  rw [C.rectMass_Ioi_left a measurableSet_Ioi, C.rectMass_univ_left measurableSet_Ioi,
    C.rectMass_Iic_Ioi, survival_two, Measure.real, unitInterval.volume_Ioi,
    ENNReal.toReal_ofReal (sub_nonneg.mpr c.2.2)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end RectMass

/-! ## Integrating the pointwise TP2 inequality -/

/-- Integrated TP2 inequality over ordered measurable sets (a generalization of the
quadrant computation in `Dependence.DensityTotalPositivity`). -/
private theorem lintegral_cross_sets (F : I → I → ENNReal)
    (hF : Measurable (Function.uncurry F))
    (hTP : ∀ a b c d : I, a ≤ b → c ≤ d → F a d * F b c ≤ F a c * F b d)
    {S₁ S₂ T₁ T₂ : Set I} (hS₁ : MeasurableSet S₁) (hS₂ : MeasurableSet S₂)
    (hT₁ : MeasurableSet T₁) (hT₂ : MeasurableSet T₂)
    (hS : ∀ s ∈ S₁, ∀ s' ∈ S₂, s ≤ s') (hT : ∀ t ∈ T₁, ∀ t' ∈ T₂, t ≤ t') :
    (∫⁻ x in S₁, ∫⁻ y in T₂, F x y) * (∫⁻ x in S₂, ∫⁻ y in T₁, F x y) ≤
      (∫⁻ x in S₁, ∫⁻ y in T₁, F x y) * (∫⁻ x in S₂, ∫⁻ y in T₂, F x y) := by
  let μL : Measure I := (volume : Measure I).restrict S₁
  let μH : Measure I := (volume : Measure I).restrict S₂
  let νL : Measure I := (volume : Measure I).restrict T₁
  let νH : Measure I := (volume : Measure I).restrict T₂
  let L : I → ENNReal := fun x => ∫⁻ y, F x y ∂νL
  let H : I → ENNReal := fun x => ∫⁻ y, F x y ∂νH
  have hsection (x : I) : Measurable (F x) := by
    simpa [Function.uncurry, Function.comp_def] using
      hF.comp (measurable_const.prodMk measurable_id :
        Measurable (fun y : I => (x, y)))
  have hL : Measurable L := Measurable.lintegral_prod_right (ν := νL) hF
  have hH : Measurable H := Measurable.lintegral_prod_right (ν := νH) hF
  have hpoint (x x' y : I) (hx : x ∈ S₁) (hx' : x' ∈ S₂) (hy : y ∈ T₁) :
      F x' y * H x ≤ F x y * H x' := by
    have hmono :
        (∫⁻ y', F x' y * F x y' ∂νH) ≤ (∫⁻ y', F x y * F x' y' ∂νH) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hT₂] with y' hy'
      calc
        F x' y * F x y' = F x y' * F x' y := mul_comm _ _
        _ ≤ F x y * F x' y' := hTP x x' y y' (hS x hx x' hx') (hT y hy y' hy')
    rw [lintegral_const_mul (F x' y) (hsection x),
      lintegral_const_mul (F x y) (hsection x')] at hmono
    exact hmono
  have hpair (x x' : I) (hx : x ∈ S₁) (hx' : x' ∈ S₂) : L x' * H x ≤ L x * H x' := by
    have hmono : (∫⁻ y, F x' y * H x ∂νL) ≤ (∫⁻ y, F x y * H x' ∂νL) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hT₁] with y hy
      exact hpoint x x' y hx hx' hy
    rw [lintegral_mul_const (H x) (hsection x'),
      lintegral_mul_const (H x') (hsection x)] at hmono
    exact hmono
  have hsingle (x : I) (hx : x ∈ S₁) :
      (∫⁻ x', L x' ∂μH) * H x ≤ L x * (∫⁻ x', H x' ∂μH) := by
    have hmono : (∫⁻ x', L x' * H x ∂μH) ≤ (∫⁻ x', L x * H x' ∂μH) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS₂] with x' hx'
      exact hpair x x' hx hx'
    rw [lintegral_mul_const (H x) hL, lintegral_const_mul (L x) hH] at hmono
    exact hmono
  have hmono :
      (∫⁻ x, (∫⁻ x', L x' ∂μH) * H x ∂μL) ≤ (∫⁻ x, L x * (∫⁻ x', H x' ∂μH) ∂μL) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hS₁] with x hx
    exact hsingle x hx
  rw [lintegral_const_mul _ hH, lintegral_mul_const _ hL] at hmono
  change (∫⁻ x, H x ∂μL) * (∫⁻ x, L x ∂μH) ≤ (∫⁻ x, L x ∂μL) * (∫⁻ x, H x ∂μH)
  simpa only [mul_comm] using hmono

private theorem lintegral_fin_two_unit' (g : (Fin 2 → I) → ENNReal) (hg : Measurable g) :
    (∫⁻ x, g x) = ∫⁻ u : I, ∫⁻ v : I, g ![u, v] := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  have hp : MeasurePreserving e (volume : Measure (Fin 2 → I))
      (volume : Measure (I × I)) := volume_preserving_finTwoArrow I
  have h := hp.symm.lintegral_comp hg
  rw [Measure.volume_eq_prod I I] at h
  rw [lintegral_prod (fun z => g (e.symm z))
    (hg.comp e.symm.measurable).aemeasurable] at h
  simpa [e, MeasurableEquiv.finTwoArrow] using h.symm

private theorem lintegral_cube_rect' (F : I → I → ENNReal)
    (hF : Measurable (Function.uncurry F)) (s t : Set I)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (∫⁻ x in {x : Fin 2 → I | x 0 ∈ s ∧ x 1 ∈ t}, F (x 0) (x 1)) =
      ∫⁻ u in s, ∫⁻ v in t, F u v := by
  let r : Set (Fin 2 → I) := {x | x 0 ∈ s ∧ x 1 ∈ t}
  have hr : MeasurableSet r := measurableSet_rect hs ht
  have hG : Measurable (fun x : Fin 2 → I => F (x 0) (x 1)) := by
    simpa [Function.uncurry, Function.comp_def] using
      hF.comp (((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)) :
        Measurable (fun x : Fin 2 → I => (x 0, x 1)))
  change (∫⁻ x in r, F (x 0) (x 1)) = _
  rw [← lintegral_indicator hr, lintegral_fin_two_unit' _ (hG.indicator hr)]
  have he (u v : I) : r.indicator (fun x : Fin 2 → I => F (x 0) (x 1)) ![u, v] =
      s.indicator (fun u' : I => t.indicator (F u') v) u := by
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ t
    all_goals simp [Set.indicator, r, hu, hv]
  simp_rw [he]
  have hi (u : I) :
      (∫⁻ v, s.indicator (fun u' : I => t.indicator (F u') v) u) =
        s.indicator (fun u' : I => ∫⁻ v, t.indicator (F u') v) u := by
    by_cases hu : u ∈ s <;> simp [Set.indicator, hu]
  simp_rw [hi]
  simp_rw [lintegral_indicator ht]
  rw [lintegral_indicator hs]

/-- An MTP2 Lebesgue density makes the copula measure TP2 on ordered product sets
(Lehmann's positive likelihood ratio dependence). -/
theorem HasMTP2Density.isTP2Measure {C : Copula 2} (h : C.HasMTP2Density) :
    C.IsTP2Measure := by
  obtain ⟨f, hf, hn, hm, heq⟩ := h
  let F : I → I → ENNReal := fun u v => ENNReal.ofReal (f ![u, v])
  have hF : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hTP : ∀ a b c d : I, a ≤ b → c ≤ d → F a d * F b c ≤ F a c * F b d := by
    intro a b c d hab hcd
    have ht := (isMTP2_fin_two_iff f).mp hm a b c d hab hcd
    dsimp [F]
    rw [← ENNReal.ofReal_mul (hn _), ← ENNReal.ofReal_mul (hn _)]
    exact ENNReal.ofReal_le_ofReal ht
  have hrect (s t : Set I) (hs : MeasurableSet s) (ht : MeasurableSet t) :
      C.toMeasure {x : Fin 2 → I | x 0 ∈ s ∧ x 1 ∈ t} = ∫⁻ u in s, ∫⁻ v in t, F u v := by
    rw [heq, withDensity_apply _ (measurableSet_rect hs ht)]
    have hfun : (fun x : Fin 2 → I => ENNReal.ofReal (f x)) =
        (fun x : Fin 2 → I => F (x 0) (x 1)) := by
      funext x
      have hx : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
      simp [F, hx]
    rw [hfun]
    exact lintegral_cube_rect' F hF s t hs ht
  intro S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ hS hT
  have hc := lintegral_cross_sets F hF hTP hS₁ hS₂ hT₁ hT₂ hS hT
  rw [← hrect _ _ hS₁ hT₂, ← hrect _ _ hS₂ hT₁, ← hrect _ _ hS₁ hT₁, ← hrect _ _ hS₂ hT₂] at hc
  have h' := ENNReal.toReal_mono (by finiteness) hc
  simpa only [rectMass, Measure.real, ENNReal.toReal_mul] using h'

/-! ## Consequences of TP2 of the copula measure -/

/-- TP2 of the measure is symmetric in the coordinates. -/
theorem rectMass_transpose (C : Copula 2) {S T : Set I} (hS : MeasurableSet S)
    (hT : MeasurableSet T) : C.transpose.rectMass S T = C.rectMass T S := by
  unfold rectMass transpose
  rw [toMeasure_reindex, map_measureReal_apply (by fun_prop) (measurableSet_rect hS hT)]
  congr 1
  ext x
  simp [and_comm]

theorem IsTP2Measure.transpose {C : Copula 2} (h : C.IsTP2Measure) :
    C.transpose.IsTP2Measure := by
  intro S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ hS hT
  rw [C.rectMass_transpose hS₁ hT₂, C.rectMass_transpose hS₂ hT₁,
    C.rectMass_transpose hS₁ hT₁, C.rectMass_transpose hS₂ hT₂]
  have := h T₁ T₂ S₁ S₂ hT₁ hT₂ hS₁ hS₂ hT hS
  linarith [mul_comm (C.rectMass T₁ S₂) (C.rectMass T₂ S₁)]

/-- TP2 of the measure implies TP2 of the CDF, i.e. LCSD (Nelsen, §5.2). -/
theorem IsTP2Measure.isTP2CDF {C : Copula 2} (h : C.IsTP2Measure) : C.IsTP2CDF := by
  intro a b c d hab hcd
  have hc := h (Iic a) (Ioc a b) (Iic c) (Ioc c d) measurableSet_Iic measurableSet_Ioc
    measurableSet_Iic measurableSet_Ioc (fun s hs s' hs' => (mem_Iic.mp hs).trans hs'.1.le)
    (fun t ht t' ht' => (mem_Iic.mp ht).trans ht'.1.le)
  rw [C.rectMass_Ioc_right hcd measurableSet_Iic, C.rectMass_Ioc_left hab measurableSet_Iic,
    C.rectMass_Ioc_left hab measurableSet_Ioc, C.rectMass_Ioc_right hcd measurableSet_Iic,
    C.rectMass_Ioc_right hcd measurableSet_Iic] at hc
  simp only [rectMass_Iic_Iic] at hc
  nlinarith [hc]

/-- TP2 of the measure implies LCSD. -/
theorem IsTP2Measure.isLCSD {C : Copula 2} (h : C.IsTP2Measure) : C.IsLCSD :=
  h.isTP2CDF.isLCSD

/-- TP2 of the measure implies stochastic increasingness of `V` given `U`. -/
theorem IsTP2Measure.isSI {C : Copula 2} (h : C.IsTP2Measure) : C.IsSI := by
  intro a b c v hab hbc
  have hc := h (Ioc a b) (Ioc b c) (Iic v) (Ioi v) measurableSet_Ioc measurableSet_Ioc
    measurableSet_Iic measurableSet_Ioi (fun s hs s' hs' => hs.2.trans hs'.1.le)
    (fun t ht t' ht' => (mem_Iic.mp ht).trans (mem_Ioi.mp ht').le)
  rw [C.rectMass_Ioi_right v measurableSet_Ioc, C.rectMass_Ioi_right v measurableSet_Ioc,
    C.rectMass_univ_right measurableSet_Ioc, C.rectMass_univ_right measurableSet_Ioc,
    C.rectMass_Ioc_left hab measurableSet_Iic, C.rectMass_Ioc_left hbc measurableSet_Iic] at hc
  simp only [rectMass_Iic_Iic, Measure.real, unitInterval.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (show (b : ℝ) ≤ c from hbc))] at hc
  nlinarith [hc]

/-- TP2 of the measure implies stochastic increasingness in both directions (CI). -/
theorem IsTP2Measure.isCI {C : Copula 2} (h : C.IsTP2Measure) : C.IsCI :=
  ⟨h.isSI, h.transpose.isSI⟩

/-- TP2 of the measure implies TP2 of the joint survival function, i.e. RCSI. -/
theorem IsTP2Measure.isRCSI {C : Copula 2} (h : C.IsTP2Measure) : C.IsRCSI := by
  rw [isRCSI_iff_isTP2_survival]
  intro a b c d hab hcd
  have hc := h (Ioc a b) (Ioi b) (Ioc c d) (Ioi d) measurableSet_Ioc measurableSet_Ioi
    measurableSet_Ioc measurableSet_Ioi (fun s hs s' hs' => hs.2.trans (mem_Ioi.mp hs').le)
    (fun t ht t' ht' => ht.2.trans (mem_Ioi.mp ht').le)
  have hL (T : Set I) (hT : MeasurableSet T) :
      C.rectMass (Ioc a b) T = C.rectMass (Ioi a) T - C.rectMass (Ioi b) T := by
    rw [C.rectMass_Ioi_left a hT, C.rectMass_Ioi_left b hT, C.rectMass_Ioc_left hab hT]
    ring
  have hR (S : Set I) (hS : MeasurableSet S) :
      C.rectMass S (Ioc c d) = C.rectMass S (Ioi c) - C.rectMass S (Ioi d) := by
    rw [C.rectMass_Ioi_right c hS, C.rectMass_Ioi_right d hS, C.rectMass_Ioc_right hcd hS]
    ring
  rw [hL _ measurableSet_Ioi, hR _ measurableSet_Ioi, hL _ measurableSet_Ioc,
    hR _ measurableSet_Ioi, hR _ measurableSet_Ioi] at hc
  simp only [rectMass_Ioi_Ioi] at hc
  nlinarith [hc]

/-- TP2 of the measure implies RTI in both directions. -/
theorem IsTP2Measure.isRTI {C : Copula 2} (h : C.IsTP2Measure) : C.IsRTI := h.isSI.isRTI

theorem IsTP2Measure.isLTD {C : Copula 2} (h : C.IsTP2Measure) : C.IsLTD := h.isSI.isLTD

theorem IsTP2Measure.isPQD {C : Copula 2} (h : C.IsTP2Measure) : C.IsPQD := h.isSI.isPQD

/-! ## The density level of the hierarchy -/

/-- An MTP2 density implies stochastic increasingness (Lehmann 1966; Nelsen, §5.2.3). -/
theorem HasMTP2Density.isSI {C : Copula 2} (h : C.HasMTP2Density) : C.IsSI :=
  h.isTP2Measure.isSI

/-- An MTP2 density implies conditional increasingness in both directions. -/
theorem HasMTP2Density.isCI {C : Copula 2} (h : C.HasMTP2Density) : C.IsCI :=
  h.isTP2Measure.isCI

/-- An MTP2 density implies a TP2 CDF (LCSD). -/
theorem HasMTP2Density.isTP2CDF {C : Copula 2} (h : C.HasMTP2Density) : C.IsTP2CDF :=
  h.isTP2Measure.isTP2CDF

/-- An MTP2 density implies LCSD. -/
theorem HasMTP2Density.isLCSD {C : Copula 2} (h : C.HasMTP2Density) : C.IsLCSD :=
  h.isTP2Measure.isLCSD

/-- An MTP2 density implies RCSI. -/
theorem HasMTP2Density.isRCSI {C : Copula 2} (h : C.HasMTP2Density) : C.IsRCSI :=
  h.isTP2Measure.isRCSI

/-! ## Benchmarks -/

theorem isTP2Measure_independence : (independence 2).IsTP2Measure :=
  (hasMTP2Density_independence 2).isTP2Measure

/-- `M` is TP2 as a measure although it has no MTP2 density
(`not_hasMTP2Density_comonotonic`): the density level of the hierarchy is strictly stronger. -/
theorem isTP2Measure_comonotonic : (comonotonic 2).IsTP2Measure := by
  have hmass (S T : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T) :
      (comonotonic 2).rectMass S T = volume.real (S ∩ T) := by
    unfold rectMass
    rw [toMeasure_comonotonic, map_measureReal_apply (by fun_prop) (measurableSet_rect hS hT)]
    congr 1
  intro S₁ S₂ T₁ T₂ hS₁ hS₂ hT₁ hT₂ hS hT
  rw [hmass _ _ hS₁ hT₂, hmass _ _ hS₂ hT₁, hmass _ _ hS₁ hT₁, hmass _ _ hS₂ hT₂]
  have hz : volume.real (S₁ ∩ T₂) * volume.real (S₂ ∩ T₁) = 0 := by
    rcases (S₁ ∩ T₂).eq_empty_or_nonempty with he | ⟨y, hy₁, hy₂⟩
    · simp [he]
    · have hsub : S₂ ∩ T₁ ⊆ {y} := fun z hz =>
        le_antisymm (hT z hz.2 y hy₂) (hS y hy₁ z hz.1)
      have h0 : volume.real (S₂ ∩ T₁) = 0 := by
        have := measureReal_mono (μ := (volume : Measure I)) hsub
        simp only [Measure.real, measure_singleton, ENNReal.toReal_zero] at this
        exact le_antisymm this measureReal_nonneg
      rw [h0, mul_zero]
  rw [hz]
  exact mul_nonneg measureReal_nonneg measureReal_nonneg

theorem not_isTP2Measure_countermonotonic : ¬ countermonotonic.IsTP2Measure :=
  fun h => not_isPQD_countermonotonic h.isPQD

end ProbabilityTheory.Copula
