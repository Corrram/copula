/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rearrangement
import Copula.Unique
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Data.EReal.Operations

/-! # Copula information and entropy

Copula information is KL divergence from the independent uniform law. In two
dimensions it is mutual information; in higher dimensions it is total
correlation. Values lie in `ℝ≥0∞`, so singular dependence is not silently
converted to a finite real number. Copula entropy is its negative in `EReal`.
The logarithm convention is natural logarithms (information in nats).
-/

open MeasureTheory Set InformationTheory
open scoped unitInterval ENNReal

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Relative entropy of the copula law with respect to independent uniforms. -/
noncomputable def copulaInformation (C : Copula d) : ℝ≥0∞ :=
  klDiv C.toMeasure (independence d).toMeasure

/-- Extended copula entropy. Infinite information gives entropy `-∞`. -/
noncomputable def copulaEntropy (C : Copula d) : EReal := -(C.copulaInformation : EReal)

theorem copulaInformation_eq_zero_iff (C : Copula d) :
    C.copulaInformation = 0 ↔ C = independence d := by
  rw [copulaInformation, klDiv_eq_zero_iff]
  exact ⟨ext, congrArg toMeasure⟩

@[simp] theorem copulaInformation_independence (d : ℕ) :
    (independence d).copulaInformation = 0 := klDiv_self _

@[simp] theorem copulaEntropy_independence (d : ℕ) :
    (independence d).copulaEntropy = 0 := by simp [copulaEntropy]

theorem copulaEntropy_nonpos (C : Copula d) : C.copulaEntropy ≤ 0 :=
  EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)

theorem copulaEntropy_eq_zero_iff (C : Copula d) :
    C.copulaEntropy = 0 ↔ C = independence d := by
  simp only [copulaEntropy, EReal.neg_eq_zero_iff, EReal.coe_ennreal_eq_zero,
    copulaInformation_eq_zero_iff]

/-- Exact finiteness conditions, including integrability of the log-likelihood ratio. -/
theorem copulaInformation_ne_top_iff (C : Copula d) :
    C.copulaInformation ≠ ∞ ↔ C.toMeasure ≪ (independence d).toMeasure ∧
      Integrable (llr C.toMeasure (independence d).toMeasure) C.toMeasure :=
  klDiv_ne_top_iff

theorem copulaInformation_eq_top_of_not_ac (C : Copula d)
    (h : ¬ C.toMeasure ≪ (independence d).toMeasure) : C.copulaInformation = ∞ :=
  klDiv_of_not_ac h

/-- The finite integral formula, with the two probability-mass correction terms cancelled. -/
theorem copulaInformation_eq_integral (C : Copula d)
    (hac : C.toMeasure ≪ (independence d).toMeasure)
    (hi : Integrable (llr C.toMeasure (independence d).toMeasure) C.toMeasure) :
    C.copulaInformation = ENNReal.ofReal (∫ x, llr C.toMeasure (independence d).toMeasure x
      ∂C.toMeasure) := by
  simp only [copulaInformation, klDiv_of_ac_of_integrable hac hi, probReal_univ, add_sub_cancel_right]

/-- A nonnegative density-integral representation, also valid for infinite information.
Here `klFun c = c * log c + 1 - c` and the density is the Radon–Nikodym derivative. -/
theorem copulaInformation_eq_lintegral_density (C : Copula d)
    (hac : C.toMeasure ≪ (independence d).toMeasure) :
    C.copulaInformation = ∫⁻ x,
      ENNReal.ofReal (klFun (C.toMeasure.rnDeriv (independence d).toMeasure x).toReal)
        ∂(independence d).toMeasure := klDiv_eq_lintegral_klFun_of_ac hac

/-- Coordinatewise processing preserving uniform margins cannot increase information. -/
theorem copulaInformation_rearrange_le (C : Copula d) (f : Fin d → I → I)
    (hf : ∀ i, MeasurePreserving (f i) volume volume) :
    (C.rearrange f hf).copulaInformation ≤ C.copulaInformation := by
  have h := klDiv_map_le C.toMeasure (independence d).toMeasure
    (show Measurable (fun x : Fin d → I => fun i => f i (x i)) from
      Measurable.of_eval (fun i => (hf i).measurable.comp (measurable_pi_apply i)))
  rw [← toMeasure_rearrange C f hf, ← toMeasure_rearrange (independence d) f hf,
    rearrange_independence] at h
  exact h

@[simp] theorem copulaInformation_shuffle (C : Copula 2) (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    (C.shuffle e he).copulaInformation = C.copulaInformation := by
  have h (D : Copula 2) (e : I ≃ᵐ I) (he : MeasurePreserving e volume volume) :
      (D.shuffle e he).copulaInformation ≤ D.copulaInformation :=
    D.copulaInformation_rearrange_le _ _
  apply le_antisymm (h C e he)
  simpa only [shuffle_symm] using h (C.shuffle e he) e.symm (MeasurePreserving.symm e he)

@[simp] theorem copulaEntropy_shuffle (C : Copula 2) (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    (C.shuffle e he).copulaEntropy = C.copulaEntropy := by simp [copulaEntropy]

/-- A measurable graph has zero independent bivariate uniform probability. -/
theorem volume_cube_graph {f : I → I} (hf : Measurable f) :
    (volume : Measure (Fin 2 → I)) {x | x 1 = f (x 0)} = 0 := by
  have hs : MeasurableSet {p : I × I | p.2 = f p.1} :=
    measurableSet_eq_fun measurable_snd (hf.comp measurable_fst)
  have hp : (volume : Measure I).prod volume {p : I × I | p.2 = f p.1} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hs
    apply Filter.Eventually.of_forall
    intro u
    have he : Prod.mk u ⁻¹' {p : I × I | p.2 = f p.1} = {f u} := rfl
    simp [he]
  exact ((measurePreserving_finTwoArrow (volume : Measure I)).measure_preimage
    hs.nullMeasurableSet).trans hp

/-- Every completely dependent bivariate copula has infinite mutual information. -/
theorem IsCompletelyDependent.copulaInformation_eq_top {C : Copula 2}
    (h : C.IsCompletelyDependent) : C.copulaInformation = ∞ := by
  obtain ⟨f, hf, ha⟩ := h
  apply C.copulaInformation_eq_top_of_not_ac
  intro hac
  have hz := hac (volume_cube_graph hf)
  have hm : C.toMeasure {x | x 1 = f (x 0)} = 1 :=
    (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (measurable_pi_apply 1)
      (hf.comp (measurable_pi_apply 0)))).1 ha
  rw [hm] at hz
  exact one_ne_zero hz

theorem IsCompletelyDependent.copulaEntropy_eq_bot {C : Copula 2}
    (h : C.IsCompletelyDependent) : C.copulaEntropy = ⊥ := by
  simp [copulaEntropy, h.copulaInformation_eq_top]

@[simp] theorem copulaInformation_comonotonic : (comonotonic 2).copulaInformation = ∞ := by
  have h := (isCompletelyDependent_graphCopula id (MeasurePreserving.id volume)).copulaInformation_eq_top
  simpa only [graphCopula_id] using h

@[simp] theorem copulaInformation_countermonotonic : countermonotonic.copulaInformation = ∞ := by
  have h := (isCompletelyDependent_graphCopula unitInterval.symm
    unitInterval.measurePreserving_symm).copulaInformation_eq_top
  simpa only [graphCopula_symm] using h

@[simp] theorem copulaEntropy_comonotonic : (comonotonic 2).copulaEntropy = ⊥ := by
  simp [copulaEntropy]

@[simp] theorem copulaEntropy_countermonotonic : countermonotonic.copulaEntropy = ⊥ := by
  simp [copulaEntropy]

@[simp] theorem copulaInformation_dim_zero (C : Copula 0) : C.copulaInformation = 0 :=
  C.copulaInformation_eq_zero_iff.mpr (Subsingleton.elim _ _)

@[simp] theorem copulaInformation_dim_one (C : Copula 1) : C.copulaInformation = 0 :=
  C.copulaInformation_eq_zero_iff.mpr (Subsingleton.elim _ _)

end ProbabilityTheory.Copula
