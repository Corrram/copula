/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Vine.Quantile

/-! # Measurable families of copulas

These kernels allow a conditional pair copula to depend on the actual values
of the conditioning variables. Constant families recover the simplifying assumption.
-/

open MeasureTheory Set Function
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- A measurable family of copulas, parametrized by a measurable space. -/
structure Family (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  /-- The family of probability laws. -/
  kernel : Kernel Ω (Fin d → I)
  /-- Each law is a probability measure. -/
  markov : IsMarkovKernel kernel
  /-- Each coordinate is uniform at every parameter value. -/
  marginal (ω : Ω) (i : Fin d) : (kernel ω).map (fun x => x i) = volume

attribute [instance] Family.markov

namespace Family

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}

/-- The copula at a given parameter value. -/
def copula (F : Family Ω d) (ω : Ω) : Copula d where
  measure := ⟨F.kernel ω, inferInstance⟩
  marginal_eq := F.marginal ω

/-- A simplified (constant) conditional copula. -/
noncomputable def const (C : Copula d) : Family Ω d where
  kernel := Kernel.const Ω C.toMeasure
  markov := inferInstance
  marginal _ := C.map_eval

@[simp] theorem copula_const (C : Copula d) (ω : Ω) : (const C : Family Ω d).copula ω = C := by
  apply Copula.ext
  rfl

/-- Pull back a family along a measurable conditioning map. -/
def comap (F : Family Ω d) (f : Ω' → Ω) (hf : Measurable f) : Family Ω' d where
  kernel := F.kernel.comap f hf
  markov := inferInstance
  marginal ω := F.marginal (f ω)

/-- Assemble a family from copulas whose probability laws depend measurably on the parameter. -/
def ofCopulas (C : Ω → Copula d) (hC : Measurable (fun ω => (C ω).toMeasure)) :
    Family Ω d where
  kernel := ⟨fun ω => (C ω).toMeasure, hC⟩
  markov := ⟨fun ω => inferInstanceAs (IsProbabilityMeasure (C ω).toMeasure)⟩
  marginal ω := (C ω).map_eval

/-- Choose between two families on a measurable set of conditioning values. -/
noncomputable def piecewise (s : Set Ω) (hs : MeasurableSet s)
    (F G : Family Ω d) : Family Ω d := by
  classical
  refine ofCopulas (s.piecewise F.copula G.copula) ?_
  have he : (fun ω => (s.piecewise F.copula G.copula ω).toMeasure) =
      s.piecewise F.kernel G.kernel := by
    funext ω
    by_cases h : ω ∈ s <;> simp [Set.piecewise, h, copula, Copula.toMeasure]
  rw [he]
  exact F.kernel.measurable.piecewise hs G.kernel.measurable

@[simp] theorem copula_piecewise_of_mem (s : Set Ω) (hs : MeasurableSet s)
    (F G : Family Ω d) (ω : Ω) (hω : ω ∈ s) :
    (piecewise s hs F G).copula ω = F.copula ω := by
  apply Copula.ext
  simp [piecewise, ofCopulas, copula, Copula.toMeasure, Set.piecewise, hω]

@[simp] theorem copula_piecewise_of_notMem (s : Set Ω) (hs : MeasurableSet s)
    (F G : Family Ω d) (ω : Ω) (hω : ω ∉ s) :
    (piecewise s hs F G).copula ω = G.copula ω := by
  apply Copula.ext
  simp [piecewise, ofCopulas, copula, Copula.toMeasure, Set.piecewise, hω]

/-- A pair coordinate remains independent of the conditioning parameter before
the conditional quantile transform, even for a nonconstant family. -/
theorem map_fst_eval_compProd (F : Family Ω d) (μ : Measure Ω) [SFinite μ] (i : Fin d) :
    (μ ⊗ₘ F.kernel).map (fun p => (p.1, p.2 i)) = μ.prod (volume : Measure I) := by
  have hm : Measurable (fun p : Ω × (Fin d → I) => (p.1, p.2 i)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs),
    Measure.prod_apply hs]
  apply lintegral_congr
  intro ω
  rw [← F.marginal ω i, Measure.map_apply (measurable_pi_apply i)
    (measurable_prodMk_left hs)]
  rfl

end Family

namespace Vine

/-- Joint measurability of generalized quantiles of a Markov kernel. -/
theorem measurable_kernelQuantile {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω I) [IsMarkovKernel κ] :
    Measurable (fun p : Ω × I => unitQuantile (κ p.1) p.2) := by
  apply measurable_of_Iic
  intro v
  change MeasurableSet {p : Ω × I | unitQuantile (κ p.1) p.2 ≤ v}
  simp_rw [unitQuantile_le_iff]
  exact measurableSet_le measurable_snd.subtype_val
    ((κ.measurable_coe measurableSet_Iic).ennreal_toReal.comp measurable_fst)

/-- A uniform quantile coordinate reconstructs a kernel jointly with its parameter. -/
theorem map_kernelQuantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω I) [IsMarkovKernel κ] :
    (μ.prod (volume : Measure I)).map (fun p => (p.1, unitQuantile (κ p.1) p.2)) =
      μ ⊗ₘ κ := by
  have hm : Measurable (fun p : Ω × I => (p.1, unitQuantile (κ p.1) p.2)) :=
    measurable_fst.prodMk (measurable_kernelQuantile κ)
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), Measure.compProd_apply hs]
  apply lintegral_congr
  intro ω
  rw [← map_unitQuantile (κ ω), Measure.map_apply (measurable_unitQuantile _)
    (measurable_prodMk_left hs)]
  rfl

/-- Conditional copula coupling has exactly the requested one-dimensional kernels. -/
theorem map_family_quantile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (F : Family Ω 2)
    (κ : Kernel Ω I) [IsMarkovKernel κ] (i : Fin 2) :
    (μ ⊗ₘ F.kernel).map (fun p => (p.1, unitQuantile (κ p.1) (p.2 i))) = μ ⊗ₘ κ := by
  have hp : Measurable (fun p : Ω × (Fin 2 → I) => (p.1, p.2 i)) := by fun_prop
  have hq := measurable_fst.prodMk (measurable_kernelQuantile κ)
  calc
    _ = ((μ ⊗ₘ F.kernel).map (fun p => (p.1, p.2 i))).map
        (fun p => (p.1, unitQuantile (κ p.1) p.2)) := (Measure.map_map hq hp).symm
    _ = μ ⊗ₘ κ := by rw [F.map_fst_eval_compProd, map_kernelQuantile]

end Vine

end ProbabilityTheory.Copula
