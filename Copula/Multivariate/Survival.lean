/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Reflection.Bivariate
import Copula.Rectangle
import Copula.Independence
import Copula.Comonotonic

/-!
# Survival functions, survival copulas and reflections in dimension `d`

For a `d`-copula `C` with law `P` of `U = (U₁, …, U_d)` (Nelsen 2006, §2.10 and the end of §2.6;
Durante–Sempi 2016, §1.7.2):

* the survival function `C̄(u) = P(U ≥ u)` is the `C`-volume of the box `[u, 1]`, i.e. the
  inclusion–exclusion sum `∑_{S} (-1)^{|S|} C(u_S, 1)` over the coordinate sets `S`
  (`survival_eq_rectangleIncrement`, `survival_eq_sum_powerset`);
* the survival copula `Ĉ` (the law of `1 - U`) satisfies `Ĉ(u) = C̄(1 - u)`
  (`cdf_survivalCopula_eq_survival`), hence
  `Ĉ(u) = ∑_{S} (-1)^{|S|} C((1 - u)_S, 1)` (`cdf_survivalCopula_eq_sum`);
* more generally, reflecting the coordinates in `s` gives the copula of
  `(1 - Uᵢ)_{i ∈ s}, (Uᵢ)_{i ∉ s}` whose CDF is a partial finite difference of `C`
  (`cdf_reflect`);
* `Π_d` and `M_d` are radially symmetric (`survivalCopula_independence`,
  `survivalCopula_comonotonic`).
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Former name of `partialIncrement_cdf` (now public in `Copula.Rectangle`). -/
alias partialIncrement_cdf_eq := partialIncrement_cdf

/-- **The survival function is the `C`-volume of `[u, 1]`.** -/
theorem survival_eq_rectangleIncrement (C : Copula d) (u : Fin d → I) :
    C.survival u = rectangleIncrement C.cdf u (fun _ => 1) := by
  rw [rectangleIncrement, C.partialIncrement_cdf u _ _ (fun _ => unitInterval.le_one'),
    C.survival_eq_strict]
  congr 1
  ext x
  simp only [mem_ofPred_eq, Finset.mem_univ, forall_const]
  exact ⟨fun h => ⟨fun _ => unitInterval.le_one', h⟩, fun h => h.2⟩

/-- **Inclusion–exclusion for the survival function** (Nelsen 2006, §2.10):
`C̄(u) = ∑_{S ⊆ {1,…,d}} (-1)^{|S|} C(v^S)` with `v^S_i = uᵢ` for `i ∈ S` and `1` otherwise. -/
theorem survival_eq_sum_powerset (C : Copula d) (u : Fin d → I) :
    C.survival u = ∑ t ∈ (Finset.univ : Finset (Fin d)).powerset,
      (-1 : ℝ) ^ t.card * C.cdf (corner u (fun _ => 1) t) := by
  rw [survival_eq_rectangleIncrement]
  rfl

/-- **CDF of a reflected copula.** Reflecting the coordinates in `s` gives the partial finite
difference of `C` over `s` between `1 - uᵢ` and `1`, with the other coordinates held at `uᵢ`. -/
theorem cdf_reflect (C : Copula d) (s : Finset (Fin d)) (u : Fin d → I) :
    (C.reflect s).cdf u =
      partialIncrement C.cdf (reflectPoint s u) (fun i => if i ∈ s then 1 else u i) s := by
  have hab : reflectPoint s u ≤ fun i => if i ∈ s then 1 else u i := by
    intro i
    by_cases hi : i ∈ s <;> simp [reflectPoint, hi, unitInterval.le_one']
  rw [C.partialIncrement_cdf _ _ _ hab, cdf, toMeasure_reflect,
    map_measureReal_apply (measurable_reflectPoint s) measurableSet_Iic]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ae_all_iff.2 (fun i => C.ae_eval_ne i (unitInterval.symm (u i)))] with x hx
  apply propext
  simp only [mem_preimage, mem_Iic, Pi.le_def, reflectPoint]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · by_cases hi : i ∈ s
      · simp [hi, unitInterval.le_one']
      · simpa [hi] using h i
    · have h' := h i
      simp only [hi, ↓reduceIte] at h' ⊢
      have hle : unitInterval.symm (u i) ≤ x i := by
        rw [← unitInterval.symm_symm (x i)]
        exact unitInterval.symm_le_symm.mpr h'
      exact lt_of_le_of_ne hle (hx i).symm
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i ∈ s
    · simp only [hi, ↓reduceIte]
      have := (h2 i hi).le
      simp only [hi, ↓reduceIte] at this
      rw [← unitInterval.symm_symm (u i)]
      exact unitInterval.symm_le_symm.mpr this
    · simpa [hi] using h1 i

/-- **The survival copula evaluates the survival function at the reflected point:**
`Ĉ(u) = C̄(1 - u)`. -/
theorem cdf_survivalCopula_eq_survival (C : Copula d) (u : Fin d → I) :
    C.survivalCopula.cdf u = C.survival (fun i => unitInterval.symm (u i)) := by
  rw [survival_eq_cdf_reflect, survivalCopula]
  congr 1
  funext i
  simp [reflectPoint]

/-- **Survival copula by inclusion–exclusion**:
`Ĉ(u) = ∑_{S} (-1)^{|S|} C(w^S)` with `w^S_i = 1 - uᵢ` for `i ∈ S` and `1` otherwise. -/
theorem cdf_survivalCopula_eq_sum (C : Copula d) (u : Fin d → I) :
    C.survivalCopula.cdf u = ∑ t ∈ (Finset.univ : Finset (Fin d)).powerset,
      (-1 : ℝ) ^ t.card * C.cdf (corner (fun i => unitInterval.symm (u i)) (fun _ => 1) t) := by
  rw [cdf_survivalCopula_eq_survival, survival_eq_sum_powerset]

/-- **`Π_d` is radially symmetric.** -/
@[simp]
theorem survivalCopula_independence (d : ℕ) :
    (independence d).survivalCopula = independence d := by
  apply ext
  rw [survivalCopula, toMeasure_reflect, toMeasure_independence]
  have h : reflectPoint (Finset.univ : Finset (Fin d)) =
      fun (x : Fin d → I) i => unitInterval.symm (x i) := by
    funext x i
    simp [reflectPoint]
  rw [h]
  exact (measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (fun _ => unitInterval.measurePreserving_symm)).map_eq

/-- **`M_d` is radially symmetric.** -/
@[simp]
theorem survivalCopula_comonotonic (d : ℕ) :
    (comonotonic d).survivalCopula = comonotonic d := by
  apply ext
  have hdiag : Measurable (fun (u : I) (_ : Fin d) => u) :=
    Measurable.of_eval fun _ => measurable_id
  rw [survivalCopula, toMeasure_reflect, toMeasure_comonotonic,
    Measure.map_map (measurable_reflectPoint _) hdiag]
  have h : reflectPoint (Finset.univ : Finset (Fin d)) ∘ (fun (u : I) (_ : Fin d) => u) =
      (fun (u : I) (_ : Fin d) => u) ∘ unitInterval.symm := by
    funext u i
    simp [reflectPoint]
  rw [h, ← Measure.map_map hdiag unitInterval.measurable_symm,
    unitInterval.measurePreserving_symm.map_eq]

end ProbabilityTheory.Copula
