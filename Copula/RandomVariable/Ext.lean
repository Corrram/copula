/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Sklar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Laws on real vectors are determined by their distribution functions

Lower orthants generate the Borel sigma algebra of `Fin d → ℝ` and form a pi-system of boxes.
This is the real-valued analogue of `Copula.ext_cdf` and is used for the random-variable
versions of Nelsen, *An Introduction to Copulas*, second edition, §2.4, §2.7 and §3.3.
-/

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Two probability measures on `Fin d → ℝ` with the same lower-orthant probabilities agree. -/
theorem ext_real_of_Iic {μ ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ x, μ.real (Iic x) = ν.real (Iic x)) : μ = ν := by
  classical
  let S : Fin d → Set (Set ℝ) := fun _ => range Iic
  have hgen (i : Fin d) : generateFrom (S i) = (inferInstance : MeasurableSpace ℝ) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic ℝ)).symm
  have hspan (i : Fin d) : IsCountablySpanning (S i) := by
    refine ⟨fun n : ℕ => Iic (n : ℝ), fun n => mem_range_self _, ?_⟩
    apply Subset.antisymm (subset_univ _)
    intro x _
    exact mem_iUnion.mpr ⟨⌈x⌉₊, Nat.le_ceil x⟩
  refine ext_of_generate_finite _ (generateFrom_eq_pi hgen hspan).symm
    (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ (by simp)
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ∀ i, ∃ u : ℝ, Iic u = s i := fun i => hs i (mem_univ i)
  choose u hu using hs'
  have hbox : Set.pi univ s = Iic u := by
    ext x
    simp only [mem_univ_pi, ← hu, mem_Iic, Pi.le_def]
  rw [hbox]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h u)

end ProbabilityTheory.Copula
