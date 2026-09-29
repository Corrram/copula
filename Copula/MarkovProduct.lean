/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Conditional
import Copula.Support

/-! # Bistochastic kernels and the Markov product

A Markov kernel preserving uniform volume determines a bivariate copula.
Composing these kernels defines the Darsow–Nguyen–Olsen Markov product:
`C.markovProduct D` follows first the transition of `C`, then that of `D`.
All constructions include singular copulas and are independent of null-set
choices of conditional kernels.
-/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- Construct a copula from a Markov kernel that preserves uniform volume. -/
noncomputable def ofKernel (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ (volume : Measure I) = volume) : Copula 2 :=
  ofMap ⟨(volume : Measure I) ⊗ₘ κ, inferInstance⟩ (fun p => ![p.1, p.2])
    (by fun_prop) (fun i => by
      fin_cases i
      · exact Measure.fst_compProd volume κ
      · exact (Measure.snd_compProd volume κ).trans hκ)

@[simp] theorem toMeasure_ofKernel (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ (volume : Measure I) = volume) :
    (ofKernel κ hκ).toMeasure = ((volume : Measure I) ⊗ₘ κ).map (fun p => ![p.1, p.2]) := rfl

theorem map_pair_ofKernel (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ (volume : Measure I) = volume) :
    (ofKernel κ hκ).toMeasure.map (fun x => (x 0, x 1)) = volume ⊗ₘ κ := by
  rw [toMeasure_ofKernel, Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

theorem conditionalKernel_ofKernel (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ (volume : Measure I) = volume) :
    (ofKernel κ hκ).conditionalKernel =ᵐ[volume] κ := by
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := (ofKernel κ hκ).toMeasure) (mα := inferInstance) (mβ := inferInstance)
    (measurable_pi_apply (0 : Fin 2)) (measurable_pi_apply (1 : Fin 2))
    (κ := κ) (by rw [map_eval, map_pair_ofKernel])
  simpa only [conditionalKernel, map_eval] using h

theorem ofKernel_congr {κ η : Kernel I I} [IsMarkovKernel κ] [IsMarkovKernel η]
    (hκ : κ ∘ₘ (volume : Measure I) = volume)
    (hη : η ∘ₘ (volume : Measure I) = volume) (h : κ =ᵐ[volume] η) :
    ofKernel κ hκ = ofKernel η hη := by
  apply ext
  simp only [toMeasure_ofKernel, Measure.compProd_congr h]

@[simp] theorem ofKernel_conditionalKernel (C : Copula 2) :
    ofKernel C.conditionalKernel C.conditionalKernel_comp_volume = C := by
  have h := compProd_map_condDistrib (μ := C.toMeasure)
    (mα := inferInstance) (mβ := inferInstance)
    (X := fun x : Fin 2 → I => x 0) (Y := fun x => x 1)
    (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
  rw [C.map_eval] at h
  apply ext
  rw [toMeasure_ofKernel, show volume ⊗ₘ C.conditionalKernel =
    C.toMeasure.map (fun x => (x 0, x 1)) from h,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun p : I × I => ![p.1, p.2]) ∘ (fun x : Fin 2 → I => (x 0, x 1)) = id := by
    ext x i; fin_cases i <;> rfl
  rw [he, Measure.map_id]

/-- A copula is determined by its conditional kernel up to uniform-null sets. -/
theorem eq_of_conditionalKernel_ae_eq {C D : Copula 2}
    (h : C.conditionalKernel =ᵐ[volume] D.conditionalKernel) : C = D := by
  simpa using ofKernel_congr C.conditionalKernel_comp_volume D.conditionalKernel_comp_volume h

theorem conditionalKernel_comonotonic :
    (comonotonic 2).conditionalKernel =ᵐ[volume] Kernel.id := by
  exact conditionalKernel_of_function _ measurable_id
    (ae_eval_eq_comonotonic.mono (fun _ h => h.symm))

/-- The Markov product follows `C` and then `D`, with the middle coordinate
integrated out. Independence is absorbing and comonotonicity is the identity. -/
noncomputable def markovProduct (C D : Copula 2) : Copula 2 :=
  ofKernel (D.conditionalKernel ∘ₖ C.conditionalKernel) (by
    rw [← Measure.comp_assoc, C.conditionalKernel_comp_volume, D.conditionalKernel_comp_volume])

theorem conditionalKernel_markovProduct (C D : Copula 2) :
    (C.markovProduct D).conditionalKernel =ᵐ[volume]
      D.conditionalKernel ∘ₖ C.conditionalKernel := conditionalKernel_ofKernel _ _

/-- The CDF of the product, in a kernel form valid without densities. -/
theorem cdf_markovProduct (C D : Copula 2) (u v : I) :
    (C.markovProduct D).cdf ![u, v] =
      ∫ t in Iic u, ((D.conditionalKernel ∘ₖ C.conditionalKernel) t).real (Iic v) :=
  (C.markovProduct D).cdf_eq_integral_kernel _ (conditionalKernel_markovProduct C D) u v

/-- Compose almost-everywhere equal kernels on the left of a uniform-preserving transition. -/
theorem kernel_comp_ae_congr_left (C : Copula 2) {κ η : Kernel I I}
    (h : κ =ᵐ[volume] η) : κ ∘ₖ C.conditionalKernel =ᵐ[volume] η ∘ₖ C.conditionalKernel := by
  have ha : ∀ᵐ u : I, κ =ᵐ[C.conditionalKernel u] η := by
    apply Measure.ae_ae_of_ae_comp
    rwa [C.conditionalKernel_comp_volume]
  filter_upwards [ha] with u hu
  exact Measure.bind_congr_right hu

theorem markovProduct_assoc (C D E : Copula 2) :
    (C.markovProduct D).markovProduct E = C.markovProduct (D.markovProduct E) := by
  apply eq_of_conditionalKernel_ae_eq
  have hl := conditionalKernel_markovProduct (C.markovProduct D) E
  have hr := conditionalKernel_markovProduct C (D.markovProduct E)
  have hm := C.kernel_comp_ae_congr_left (conditionalKernel_markovProduct D E)
  filter_upwards [hl, hr, conditionalKernel_markovProduct C D, hm] with u hlu hru hcu hmu
  rw [hlu, hru, hmu, Kernel.comp_apply, hcu, ← Kernel.comp_apply, Kernel.comp_assoc]

@[simp] theorem markovProduct_comonotonic (C : Copula 2) :
    C.markovProduct (comonotonic 2) = C := by
  apply eq_of_conditionalKernel_ae_eq
  exact (conditionalKernel_markovProduct C _).trans
    ((C.kernel_comp_ae_congr_left conditionalKernel_comonotonic).trans
      (by simp))

@[simp] theorem comonotonic_markovProduct (C : Copula 2) :
    (comonotonic 2).markovProduct C = C := by
  apply eq_of_conditionalKernel_ae_eq
  filter_upwards [conditionalKernel_markovProduct (comonotonic 2) C,
    conditionalKernel_comonotonic] with u hu hm
  rw [hu, Kernel.comp_apply, hm, ← Kernel.comp_apply, Kernel.comp_id]

@[simp] theorem markovProduct_independence (C : Copula 2) :
    C.markovProduct (independence 2) = independence 2 := by
  apply eq_of_conditionalKernel_ae_eq
  have h := C.kernel_comp_ae_congr_left conditionalKernel_independence
  filter_upwards [conditionalKernel_markovProduct C (independence 2), h,
    conditionalKernel_independence] with u hu hm hi
  rw [hu, hm, Kernel.const_comp', hi]

@[simp] theorem independence_markovProduct (C : Copula 2) :
    (independence 2).markovProduct C = independence 2 := by
  apply eq_of_conditionalKernel_ae_eq
  filter_upwards [conditionalKernel_markovProduct (independence 2) C,
    conditionalKernel_independence] with u hu hi
  rw [hu, Kernel.comp_apply, hi, ← Kernel.comp_apply,
    Kernel.comp_const, C.conditionalKernel_comp_volume]

end ProbabilityTheory.Copula
