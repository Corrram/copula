/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.MarkovProduct
import Copula.Rank.CorrelationRatio
import Copula.Reflection.Bivariate

/-! # Measure-preserving rearrangements and complete dependence

Coordinatewise uniform-preserving maps transform copulas into copulas. The
maps need not be invertible. Invertible maps include generalized shuffles;
finite piecewise shuffles are not separately encoded here.

`graphCopula f hf` is the law of `(U, f(U))`, for uniform `U`. Its conditional
law is deterministic, and its Markov products follow composition of maps.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Apply a uniform-preserving map to each coordinate of a copula. -/
noncomputable def rearrange (C : Copula d) (f : Fin d → I → I)
    (hf : ∀ i, MeasurePreserving (f i) volume volume) : Copula d :=
  ofMap C.measure (fun x i => f i (x i))
    (Measurable.of_eval (fun i => (hf i).measurable.comp (measurable_pi_apply i)))
    (fun i => ((hf i).comp (C.measurePreserving_eval i)).map_eq)

@[simp] theorem toMeasure_rearrange (C : Copula d) (f : Fin d → I → I)
    (hf : ∀ i, MeasurePreserving (f i) volume volume) :
    (C.rearrange f hf).toMeasure = C.toMeasure.map (fun x i => f i (x i)) := rfl

@[simp] theorem rearrange_id (C : Copula d) :
    C.rearrange (fun _ => id) (fun _ => MeasurePreserving.id volume) = C := by
  apply ext
  exact Measure.map_id

theorem rearrange_rearrange (C : Copula d) (f g : Fin d → I → I)
    (hf : ∀ i, MeasurePreserving (f i) volume volume)
    (hg : ∀ i, MeasurePreserving (g i) volume volume) :
    (C.rearrange f hf).rearrange g hg =
      C.rearrange (fun i => g i ∘ f i) (fun i => (hg i).comp (hf i)) := by
  apply ext
  simp only [toMeasure_rearrange]
  exact Measure.map_map
    (Measurable.of_eval (fun i => (hg i).measurable.comp (measurable_pi_apply i)))
    (Measurable.of_eval (fun i => (hf i).measurable.comp (measurable_pi_apply i)))

/-- Inverse rearrangements recover the original copula. -/
theorem rearrange_inverse (C : Copula d) (f g : Fin d → I → I)
    (hf : ∀ i, MeasurePreserving (f i) volume volume)
    (hg : ∀ i, MeasurePreserving (g i) volume volume)
    (hgf : ∀ i, Function.LeftInverse (g i) (f i)) :
    (C.rearrange f hf).rearrange g hg = C := by
  rw [rearrange_rearrange]
  have he : (fun i => g i ∘ f i) = fun _ => id := by
    funext i u
    exact hgf i u
  simp only [he, rearrange_id]

@[simp] theorem rearrange_independence (f : Fin d → I → I)
    (hf : ∀ i, MeasurePreserving (f i) volume volume) :
    (independence d).rearrange f hf = independence d := by
  apply ext
  rw [toMeasure_rearrange, toMeasure_independence]
  exact (measurePreserving_pi (fun _ => volume) (fun _ => volume) hf).map_eq

/-- Complete dependence: the second coordinate is a measurable function of the first. -/
def IsCompletelyDependent (C : Copula 2) : Prop :=
  ∃ f : I → I, Measurable f ∧ ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)

/-- Mutual complete dependence requires functional dependence in both directions. -/
def IsMutuallyCompletelyDependent (C : Copula 2) : Prop :=
  C.IsCompletelyDependent ∧ C.transpose.IsCompletelyDependent

/-- The copula of a uniform variable and a uniform-preserving function of it. -/
noncomputable def graphCopula (f : I → I) (hf : MeasurePreserving f volume volume) : Copula 2 :=
  ofMap ⟨(volume : Measure I), inferInstance⟩ (fun u => ![u, f u])
    (Measurable.of_eval (fun i => by
      fin_cases i
      · exact measurable_id
      · exact hf.measurable)) (fun i => by
      fin_cases i
      · exact Measure.map_id
      · exact hf.map_eq)

@[simp] theorem toMeasure_graphCopula (f : I → I) (hf : MeasurePreserving f volume volume) :
    (graphCopula f hf).toMeasure = (volume : Measure I).map (fun u => ![u, f u]) := rfl

theorem ae_graphCopula (f : I → I) (hf : MeasurePreserving f volume volume) :
    ∀ᵐ x ∂(graphCopula f hf).toMeasure, x 1 = f (x 0) := by
  rw [toMeasure_graphCopula]
  have hmap : Measurable (fun u : I => ![u, f u]) := Measurable.of_eval (fun i => by
    fin_cases i
    · exact measurable_id
    · exact hf.measurable)
  apply (ae_map_iff hmap.aemeasurable
    (measurableSet_eq_fun (by fun_prop) (hf.measurable.comp (measurable_pi_apply 0)))).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

theorem isCompletelyDependent_graphCopula (f : I → I) (hf : MeasurePreserving f volume volume) :
    (graphCopula f hf).IsCompletelyDependent := ⟨f, hf.measurable, ae_graphCopula f hf⟩

theorem conditionalKernel_graphCopula (f : I → I) (hf : MeasurePreserving f volume volume) :
    (graphCopula f hf).conditionalKernel =ᵐ[volume] Kernel.deterministic f hf.measurable :=
  conditionalKernel_of_function _ hf.measurable (ae_graphCopula f hf)

/-- A functional response in a copula automatically preserves uniform volume. -/
theorem measurePreserving_of_ae_function (C : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) : MeasurePreserving f volume volume := by
  refine ⟨hf, ?_⟩
  calc
    (volume : Measure I).map f = (C.toMeasure.map (fun x => x 0)).map f := by rw [C.map_eval]
    _ = C.toMeasure.map (fun x => f (x 0)) := Measure.map_map hf (measurable_pi_apply 0)
    _ = C.toMeasure.map (fun x => x 1) := Measure.map_congr (h.mono (fun _ hx => hx.symm))
    _ = volume := C.map_eval 1

theorem eq_graphCopula_of_ae_function (C : Copula 2) {f : I → I}
    (hf : MeasurePreserving f volume volume) (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) :
    C = graphCopula f hf := by
  apply eq_of_conditionalKernel_ae_eq
  exact (C.conditionalKernel_of_function hf.measurable h).trans
    (conditionalKernel_graphCopula f hf).symm

theorem isCompletelyDependent_iff (C : Copula 2) :
    C.IsCompletelyDependent ↔ ∃ f : I → I, ∃ hf : MeasurePreserving f volume volume,
      C = graphCopula f hf := by
  constructor
  · rintro ⟨f, hf, h⟩
    exact ⟨f, C.measurePreserving_of_ae_function hf h,
      C.eq_graphCopula_of_ae_function _ h⟩
  · rintro ⟨f, hf, rfl⟩
    exact isCompletelyDependent_graphCopula f hf

theorem IsCompletelyDependent.chatterjeeXi_eq_one {C : Copula 2}
    (h : C.IsCompletelyDependent) : C.chatterjeeXi = 1 := by
  obtain ⟨f, hf, h⟩ := h
  exact C.chatterjeeXi_eq_one_of_function hf h

theorem IsCompletelyDependent.copulaCorrelationRatio_eq_one {C : Copula 2}
    (h : C.IsCompletelyDependent) : C.copulaCorrelationRatio = 1 := by
  obtain ⟨f, hf, h⟩ := h
  exact C.copulaCorrelationRatio_eq_one_of_function hf h

@[simp] theorem graphCopula_id : graphCopula id (MeasurePreserving.id volume) = comonotonic 2 := by
  apply ext
  rw [toMeasure_graphCopula, toMeasure_comonotonic]
  congr 1
  ext u i
  fin_cases i <;> rfl

@[simp] theorem graphCopula_symm :
    graphCopula unitInterval.symm unitInterval.measurePreserving_symm = countermonotonic := by
  apply ext
  rfl

/-- For deterministic transitions, the product follows ordinary function composition. -/
theorem markovProduct_graphCopula (f g : I → I)
    (hf : MeasurePreserving f volume volume) (hg : MeasurePreserving g volume volume) :
    (graphCopula f hf).markovProduct (graphCopula g hg) = graphCopula (g ∘ f) (hg.comp hf) := by
  apply eq_of_conditionalKernel_ae_eq
  have h := (graphCopula f hf).kernel_comp_ae_congr_left (conditionalKernel_graphCopula g hg)
  filter_upwards [conditionalKernel_markovProduct (graphCopula f hf) (graphCopula g hg),
    h, conditionalKernel_graphCopula f hf, conditionalKernel_graphCopula (g ∘ f) (hg.comp hf)]
    with u hu hgu hfu hgf
  rw [hu, hgu, Kernel.comp_apply, hfu, ← Kernel.comp_apply,
    Kernel.deterministic_comp_deterministic, hgf]

/-- A generalized shuffle acts on the second coordinate by a uniform-preserving
measurable bijection. In contrast, `rearrange` also allows noninvertible maps. -/
noncomputable def shuffle (C : Copula 2) (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) : Copula 2 :=
  C.rearrange ![id, (e : I → I)] (fun i => by
    fin_cases i
    · exact MeasurePreserving.id volume
    · exact he)

theorem toMeasure_shuffle (C : Copula 2) (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    (C.shuffle e he).toMeasure = C.toMeasure.map (fun x => ![x 0, e (x 1)]) := by
  rw [shuffle, toMeasure_rearrange]
  congr 1
  ext x i
  fin_cases i <;> rfl

@[simp] theorem shuffle_symm (C : Copula 2) (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    (C.shuffle e he).shuffle e.symm (MeasurePreserving.symm e he) = C := by
  unfold shuffle
  apply rearrange_inverse
  intro i u
  fin_cases i
  · rfl
  · exact e.symm_apply_apply u

@[simp] theorem shuffle_independence (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    (independence 2).shuffle e he = independence 2 := rearrange_independence _ _

@[simp] theorem shuffle_comonotonic (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    (comonotonic 2).shuffle e he = graphCopula e he := by
  apply ext
  rw [toMeasure_shuffle, toMeasure_comonotonic,
    Measure.map_map (by fun_prop) (by fun_prop), toMeasure_graphCopula]
  rfl

theorem transpose_graphCopula (e : I ≃ᵐ I) (he : MeasurePreserving e volume volume) :
    (graphCopula e he).transpose = graphCopula e.symm (MeasurePreserving.symm e he) := by
  apply ext
  rw [transpose, toMeasure_reindex, toMeasure_graphCopula,
    Measure.map_map (by fun_prop) (by fun_prop), toMeasure_graphCopula]
  conv_rhs => rw [← he.map_eq]
  rw [Measure.map_map (by fun_prop) e.measurable]
  congr 1
  ext u i
  fin_cases i
  · rfl
  · simp

theorem isMutuallyCompletelyDependent_graphCopula (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) : (graphCopula e he).IsMutuallyCompletelyDependent := by
  refine ⟨isCompletelyDependent_graphCopula e he, ?_⟩
  rw [transpose_graphCopula]
  exact isCompletelyDependent_graphCopula _ _

/-- A generalized shuffle of Min is mutually completely dependent. -/
theorem isMutuallyCompletelyDependent_shuffle_comonotonic (e : I ≃ᵐ I)
    (he : MeasurePreserving e volume volume) :
    ((comonotonic 2).shuffle e he).IsMutuallyCompletelyDependent := by
  rw [shuffle_comonotonic]
  exact isMutuallyCompletelyDependent_graphCopula e he

@[simp] theorem countermonotonic_markovProduct_countermonotonic :
    countermonotonic.markovProduct countermonotonic = comonotonic 2 := by
  rw [← graphCopula_symm, markovProduct_graphCopula]
  have he : unitInterval.symm ∘ unitInterval.symm = id := by
    funext u
    exact unitInterval.symm_symm u
  simp only [he, graphCopula_id]

/-- A shuffle by the interval reflection recovers the existing copula reflection. -/
@[simp] theorem shuffle_reflection (C : Copula 2) :
    C.shuffle unitInterval.symmMeasurableEquiv
      (by simpa only [unitInterval.coe_symmMeasurableEquiv] using unitInterval.measurePreserving_symm) =
      C.reflect {1} := by
  apply ext
  rw [toMeasure_shuffle, toMeasure_reflect]
  congr 1
  ext x i
  fin_cases i <;> simp [reflectPoint]

end ProbabilityTheory.Copula
