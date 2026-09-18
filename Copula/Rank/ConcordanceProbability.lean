/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Concordance

/-! # Concordant and discordant independent pairs

For independent vectors with copulas `C` and `D`, the concordance function
is the probability of concordance minus the probability of discordance.
Uniform marginals exclude coordinate ties even for singular copulas.
Taking `C = D` gives Kendall's probabilistic interpretation.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Pairs whose two coordinate differences have the same strict sign. -/
def concordantPairs : Set ((Fin 2 → I) × (Fin 2 → I)) :=
  {p | 0 < ((p.1 0 : ℝ) - p.2 0) * ((p.1 1 : ℝ) - p.2 1)}

/-- Pairs whose two coordinate differences have opposite strict signs. -/
def discordantPairs : Set ((Fin 2 → I) × (Fin 2 → I)) :=
  {p | ((p.1 0 : ℝ) - p.2 0) * ((p.1 1 : ℝ) - p.2 1) < 0}

theorem measurableSet_concordantPairs : MeasurableSet concordantPairs := by
  unfold concordantPairs
  exact measurableSet_lt measurable_const (by fun_prop)

theorem measurableSet_discordantPairs : MeasurableSet discordantPairs := by
  unfold discordantPairs
  exact measurableSet_lt (by fun_prop) measurable_const

theorem ae_prod_eval_ne (C D : Copula 2) (i : Fin 2) :
    ∀ᵐ p ∂C.toMeasure.prod D.toMeasure, p.1 i ≠ p.2 i := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl).2
  exact Filter.Eventually.of_forall fun x => (D.ae_eval_ne i (x i)).mono fun _ h => h.symm

theorem measureReal_pairs_le (C D : Copula 2) :
    (C.toMeasure.prod D.toMeasure).real {p | p.1 ≤ p.2} = ∫ x, C.cdf x ∂D.toMeasure := by
  classical
  let s : Set ((Fin 2 → I) × (Fin 2 → I)) := {p | p.1 ≤ p.2}
  have hs : MeasurableSet s := measurableSet_le measurable_fst measurable_snd
  calc
    _ = ∫ p, s.indicator (fun _ => (1 : ℝ)) p ∂C.toMeasure.prod D.toMeasure :=
      (integral_indicator_one hs).symm
    _ = ∫ y, ∫ x, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂C.toMeasure ∂D.toMeasure :=
      integral_prod_symm _ ((integrable_const (1 : ℝ)).indicator hs)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simpa [s, Set.indicator, cdf] using
          (integral_indicator_one (μ := C.toMeasure) (s := Iic y) measurableSet_Iic)

theorem measureReal_pairs_ge (C D : Copula 2) :
    (C.toMeasure.prod D.toMeasure).real {p | p.2 ≤ p.1} = ∫ x, C.cdf x ∂D.toMeasure := by
  classical
  let s : Set ((Fin 2 → I) × (Fin 2 → I)) := {p | p.2 ≤ p.1}
  have hs : MeasurableSet s := measurableSet_le measurable_snd measurable_fst
  calc
    _ = ∫ p, s.indicator (fun _ => (1 : ℝ)) p ∂C.toMeasure.prod D.toMeasure :=
      (integral_indicator_one hs).symm
    _ = ∫ x, ∫ y, s.indicator (fun _ => (1 : ℝ)) (x, y) ∂D.toMeasure ∂C.toMeasure :=
      integral_prod _ ((integrable_const (1 : ℝ)).indicator hs)
    _ = ∫ x, D.cdf x ∂C.toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simpa [s, Set.indicator, cdf] using
          (integral_indicator_one (μ := D.toMeasure) (s := Iic x) measurableSet_Iic)
    _ = _ := integral_cdf_swap D C

theorem measureReal_concordantPairs (C D : Copula 2) :
    (C.toMeasure.prod D.toMeasure).real concordantPairs = (1 + C.concordanceQ D) / 2 := by
  classical
  let s : Set ((Fin 2 → I) × (Fin 2 → I)) := {p | p.1 ≤ p.2}
  let t : Set ((Fin 2 → I) × (Fin 2 → I)) := {p | p.2 ≤ p.1}
  have hs : MeasurableSet s := measurableSet_le measurable_fst measurable_snd
  have ht : MeasurableSet t := measurableSet_le measurable_snd measurable_fst
  have he : concordantPairs =ᵐ[C.toMeasure.prod D.toMeasure] s ∪ t := by
    filter_upwards [C.ae_prod_eval_ne D 0, C.ae_prod_eval_ne D 1] with p h0 h1
    have h0' : (p.1 0 : ℝ) ≠ p.2 0 := fun h => h0 (Subtype.ext h)
    have h1' : (p.1 1 : ℝ) ≠ p.2 1 := fun h => h1 (Subtype.ext h)
    apply propext
    simp only [concordantPairs, s, t, mem_ofPred_eq, mem_union, Pi.le_def, Fin.forall_fin_two]
    rw [mul_pos_iff]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
      · exact Or.inr ⟨by exact_mod_cast (show (p.2 0 : ℝ) ≤ p.1 0 by linarith),
          by exact_mod_cast (show (p.2 1 : ℝ) ≤ p.1 1 by linarith)⟩
      · exact Or.inl ⟨by exact_mod_cast (show (p.1 0 : ℝ) ≤ p.2 0 by linarith),
          by exact_mod_cast (show (p.1 1 : ℝ) ≤ p.2 1 by linarith)⟩
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · right
        have ha' : (p.1 0 : ℝ) ≤ p.2 0 := ha
        have hb' : (p.1 1 : ℝ) ≤ p.2 1 := hb
        exact ⟨sub_neg.mpr (lt_of_le_of_ne ha' h0'), sub_neg.mpr (lt_of_le_of_ne hb' h1')⟩
      · left
        have ha' : (p.2 0 : ℝ) ≤ p.1 0 := ha
        have hb' : (p.2 1 : ℝ) ≤ p.1 1 := hb
        exact ⟨sub_pos.mpr (lt_of_le_of_ne ha' h0'.symm),
          sub_pos.mpr (lt_of_le_of_ne hb' h1'.symm)⟩
  have hd : AEDisjoint (C.toMeasure.prod D.toMeasure) s t := by
    rw [AEDisjoint, measure_eq_zero_iff_ae_notMem]
    filter_upwards [C.ae_prod_eval_ne D 0] with p hp
    simp only [s, t, mem_ofPred_eq, mem_inter_iff]
    rintro ⟨hst, hts⟩
    exact hp (le_antisymm (hst 0) (hts 0))
  have hm := congrArg ENNReal.toReal (measure_congr he)
  change (C.toMeasure.prod D.toMeasure).real concordantPairs =
    (C.toMeasure.prod D.toMeasure).real (s ∪ t) at hm
  rw [hm, measureReal_union₀ ht.nullMeasurableSet hd]
  change (C.toMeasure.prod D.toMeasure).real {p | p.1 ≤ p.2} +
    (C.toMeasure.prod D.toMeasure).real {p | p.2 ≤ p.1} = _
  rw [measureReal_pairs_le, measureReal_pairs_ge, concordanceQ]
  ring

theorem measureReal_discordantPairs (C D : Copula 2) :
    (C.toMeasure.prod D.toMeasure).real discordantPairs = (1 - C.concordanceQ D) / 2 := by
  have he : discordantPairs =ᵐ[C.toMeasure.prod D.toMeasure] concordantPairsᶜ := by
    filter_upwards [C.ae_prod_eval_ne D 0, C.ae_prod_eval_ne D 1] with p h0 h1
    have hn : ((p.1 0 : ℝ) - p.2 0) * ((p.1 1 : ℝ) - p.2 1) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr (fun h => h0 (Subtype.ext h)))
        (sub_ne_zero.mpr (fun h => h1 (Subtype.ext h)))
    simp only [discordantPairs, concordantPairs, mem_ofPred_eq, mem_compl_iff, not_lt]
    exact propext ⟨le_of_lt, fun h => lt_of_le_of_ne h hn⟩
  have hm := congrArg ENNReal.toReal (measure_congr he)
  change (C.toMeasure.prod D.toMeasure).real discordantPairs =
    (C.toMeasure.prod D.toMeasure).real concordantPairsᶜ at hm
  rw [hm, measureReal_compl measurableSet_concordantPairs, probReal_univ,
    measureReal_concordantPairs]
  ring

theorem measureReal_concordant_add_discordant (C D : Copula 2) :
    (C.toMeasure.prod D.toMeasure).real concordantPairs +
      (C.toMeasure.prod D.toMeasure).real discordantPairs = 1 := by
  rw [measureReal_concordantPairs, measureReal_discordantPairs]
  ring

theorem concordanceQ_eq_concordant_sub_discordant (C D : Copula 2) :
    C.concordanceQ D = (C.toMeasure.prod D.toMeasure).real concordantPairs -
      (C.toMeasure.prod D.toMeasure).real discordantPairs := by
  rw [measureReal_concordantPairs, measureReal_discordantPairs]
  ring

/-- Kendall's tau is concordance probability minus discordance probability
for two independent observations from the copula. -/
theorem kendallTau_eq_concordant_sub_discordant (C : Copula 2) :
    C.kendallTau = (C.toMeasure.prod C.toMeasure).real concordantPairs -
      (C.toMeasure.prod C.toMeasure).real discordantPairs :=
  C.concordanceQ_eq_concordant_sub_discordant C

theorem concordanceQ_eq_one_iff (C D : Copula 2) :
    C.concordanceQ D = 1 ↔ ∀ᵐ p ∂C.toMeasure.prod D.toMeasure, p ∈ concordantPairs := by
  change C.concordanceQ D = 1 ↔ concordantPairs ∈ ae (C.toMeasure.prod D.toMeasure)
  rw [mem_ae_iff_prob_eq_one measurableSet_concordantPairs,
    ← ENNReal.toReal_eq_one_iff ((C.toMeasure.prod D.toMeasure) concordantPairs)]
  change C.concordanceQ D = 1 ↔ (C.toMeasure.prod D.toMeasure).real concordantPairs = 1
  rw [measureReal_concordantPairs]
  constructor <;> intro h <;> linarith

theorem concordanceQ_eq_neg_one_iff (C D : Copula 2) :
    C.concordanceQ D = -1 ↔ ∀ᵐ p ∂C.toMeasure.prod D.toMeasure, p ∈ discordantPairs := by
  change C.concordanceQ D = -1 ↔ discordantPairs ∈ ae (C.toMeasure.prod D.toMeasure)
  rw [mem_ae_iff_prob_eq_one measurableSet_discordantPairs,
    ← ENNReal.toReal_eq_one_iff ((C.toMeasure.prod D.toMeasure) discordantPairs)]
  change C.concordanceQ D = -1 ↔ (C.toMeasure.prod D.toMeasure).real discordantPairs = 1
  rw [measureReal_discordantPairs]
  constructor <;> intro h <;> linarith

theorem kendallTau_eq_one_iff_ae_concordant (C : Copula 2) :
    C.kendallTau = 1 ↔ ∀ᵐ p ∂C.toMeasure.prod C.toMeasure, p ∈ concordantPairs :=
  C.concordanceQ_eq_one_iff C

theorem kendallTau_eq_neg_one_iff_ae_discordant (C : Copula 2) :
    C.kendallTau = -1 ↔ ∀ᵐ p ∂C.toMeasure.prod C.toMeasure, p ∈ discordantPairs :=
  C.concordanceQ_eq_neg_one_iff C

theorem kendallTau_eq_zero_iff_balanced (C : Copula 2) :
    C.kendallTau = 0 ↔ (C.toMeasure.prod C.toMeasure).real concordantPairs =
      (C.toMeasure.prod C.toMeasure).real discordantPairs := by
  rw [kendallTau_eq_concordant_sub_discordant, sub_eq_zero]

end ProbabilityTheory.Copula
