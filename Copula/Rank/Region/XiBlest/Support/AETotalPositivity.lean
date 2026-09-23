import Copula.Rank.Region.XiBlest.Support.StepDensity
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Ordered density minors, with a null-set invariant convention

The sign +1 gives TP2 and -1 gives RR2. The four coordinates are quantified
almost everywhere with respect to uniform measure, so changing a density on
a null set cannot change this property.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

def HasAEOrderedMinors (s : ℝ) (f : I → I → ℝ) : Prop :=
  ∀ᵐ u₁ : I, ∀ᵐ u₂ : I, ∀ᵐ v₁ : I, ∀ᵐ v₂ : I,
    u₁ ≤ u₂ → v₁ ≤ v₂ →
      0 ≤ s * (f u₁ v₁ * f u₂ v₂ - f u₁ v₂ * f u₂ v₁)

theorem HasAEOrderedMinors.congr {s : ℝ} {f g : I → I → ℝ}
    (hf : HasAEOrderedMinors s f) (he : ∀ᵐ u : I, ∀ᵐ v : I, f u v = g u v) :
    HasAEOrderedMinors s g := by
  filter_upwards [hf, he] with u₁ h₁ e₁
  filter_upwards [h₁, he] with u₂ h₂ e₂
  filter_upwards [h₂, e₁, e₂] with v₁ h₃ e₁₁ e₂₁
  filter_upwards [h₃, e₁, e₂] with v₂ h₄ e₁₂ e₂₂
  simpa only [e₁₁, e₁₂, e₂₁, e₂₂] using h₄

theorem aeOrderedMinors_congr {s : ℝ} {f g : I → I → ℝ}
    (he : ∀ᵐ u : I, ∀ᵐ v : I, f u v = g u v) :
    HasAEOrderedMinors s f ↔ HasAEOrderedMinors s g := by
  constructor
  · exact fun h => h.congr he
  · intro h
    apply h.congr
    filter_upwards [he] with u hu
    filter_upwards [hu] with v hv
    exact hv.symm

theorem exists_mem_Ioo_of_ae {a b : I} (hab : a < b) {p : I → Prop}
    (hp : ∀ᵐ u : I, p u) : ∃ u ∈ Ioo a b, p u := by
  apply Measure.exists_mem_of_measure_ne_zero_of_ae _ (ae_restrict_of_ae hp)
  rw [unitInterval.volume_Ioo]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))

theorem medianSign_antitone : Antitone medianSign := by
  intro u v huv
  by_cases hv : v ≤ Copula.unitHalf
  · simp [medianSign, hv, huv.trans hv]
  · by_cases hu : u ≤ Copula.unitHalf <;> simp [medianSign, hu, hv]

theorem stepDensity_minor (d : I → ℝ) (u₁ u₂ v₁ v₂ : I) :
    (1 + medianSign u₁ * d v₁) * (1 + medianSign u₂ * d v₂) -
      (1 + medianSign u₁ * d v₂) * (1 + medianSign u₂ * d v₁) =
    (medianSign u₁ - medianSign u₂) * (d v₁ - d v₂) := by ring

theorem stepDensity_ordered_minors {s : ℝ} {d : I → ℝ}
    (hd : Antitone (fun v => s * d v)) (u₁ u₂ v₁ v₂ : I)
    (hu : u₁ ≤ u₂) (hv : v₁ ≤ v₂) :
    0 ≤ s * ((1 + medianSign u₁ * d v₁) * (1 + medianSign u₂ * d v₂) -
      (1 + medianSign u₁ * d v₂) * (1 + medianSign u₂ * d v₁)) := by
  rw [stepDensity_minor]
  have h := mul_nonneg (sub_nonneg.mpr (medianSign_antitone hu)) (sub_nonneg.mpr (hd hv))
  nlinarith only [h]

theorem stepDensity_ae_minors_iff (s : ℝ) (d : I → ℝ) :
    HasAEOrderedMinors s (fun u v => 1 + medianSign u * d v) ↔
      ∀ᵐ v₁ : I, ∀ᵐ v₂ : I, v₁ ≤ v₂ → s * d v₂ ≤ s * d v₁ := by
  constructor
  · intro h
    obtain ⟨u₁, hu₁, h₁⟩ := exists_mem_Ioo_of_ae
      (show (0 : I) < Copula.unitHalf by change (0 : ℝ) < 1 / 2; norm_num) h
    obtain ⟨u₂, hu₂, h₂⟩ := exists_mem_Ioo_of_ae
      (show Copula.unitHalf < (1 : I) by change (1 / 2 : ℝ) < 1; norm_num) h₁
    filter_upwards [h₂] with v₁ h₃
    filter_upwards [h₃] with v₂ h₄
    intro hv
    have hm := h₄ (hu₁.2.le.trans hu₂.1.le) hv
    rw [stepDensity_minor] at hm
    simp only [medianSign, ite_eq_left hu₁.2.le, ite_eq_right (not_le.mpr hu₂.1)] at hm
    nlinarith only [hm]
  · intro h
    filter_upwards [] with u₁
    filter_upwards [] with u₂
    filter_upwards [h] with v₁ h₁
    filter_upwards [h₁] with v₂ h₂
    intro hu hv
    rw [stepDensity_minor]
    have hm := mul_nonneg (sub_nonneg.mpr (medianSign_antitone hu)) (sub_nonneg.mpr (h₂ hv))
    nlinarith only [hm]

/-- Reverse regularity on ordered rectangles; equality of coordinates is allowed. -/
def IsRR2 (f : I → I → ℝ) : Prop :=
  ∀ u₁ u₂ v₁ v₂, u₁ ≤ u₂ → v₁ ≤ v₂ → f u₁ v₁ * f u₂ v₂ ≤ f u₁ v₂ * f u₂ v₁

def HasRR2Density (C : Copula 2) : Prop :=
  ∃ f : (Fin 2 → I) → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
    IsRR2 (fun u v => f ![u, v]) ∧
    C.toMeasure = (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (f x))

theorem aeOrderedMinors_of_tp2 {f : I → I → ℝ} (h : IsTP2 f) : HasAEOrderedMinors 1 f := by
  filter_upwards [] with u₁
  filter_upwards [] with u₂
  filter_upwards [] with v₁
  filter_upwards [] with v₂
  intro hu hv
  simpa only [one_mul] using sub_nonneg.mpr (h u₁ u₂ v₁ v₂ hu hv)

theorem aeOrderedMinors_of_rr2 {f : I → I → ℝ} (h : IsRR2 f) : HasAEOrderedMinors (-1) f := by
  filter_upwards [] with u₁
  filter_upwards [] with u₂
  filter_upwards [] with v₁
  filter_upwards [] with v₂
  intro hu hv
  have hi := h u₁ u₂ v₁ v₂ hu hv
  linarith

theorem ae_curry_of_ae_eq {f g : (Fin 2 → I) → ℝ} (he : f =ᵐ[volume] g) :
    ∀ᵐ u : I, ∀ᵐ v : I, f ![u, v] = g ![u, v] := by
  have hp := ((volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow).quasiMeasurePreserving.ae_eq_comp he
  exact Measure.ae_ae_of_ae_prod hp

theorem density_ae_eq {f g : (Fin 2 → I) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hnf : ∀ x, 0 ≤ f x) (hng : ∀ x, 0 ≤ g x)
    (he : (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : f =ᵐ[volume] g := by
  have h := (withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal.aemeasurable
    hg.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [h] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hnf x) (hng x)).mp hx

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
