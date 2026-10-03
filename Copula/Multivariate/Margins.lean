/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Transform
import Copula.Reflection
import Copula.Independence
import Copula.Comonotonic
import Copula.CDF.Extensionality
import Mathlib.Probability.Independence.Basic

/-!
# Margins of `d`-copulas and the independence copula

For a `d`-copula `C` and a coordinate map `ρ : Fin e → Fin d`, `C.reindex ρ` is the law of
`(X_{ρ 0}, …, X_{ρ (e-1)})`. When `ρ` is injective this is the `e`-dimensional margin of `C`
(Nelsen 2006, §2.10: the `k`-margins of a `d`-copula are `k`-copulas, obtained by setting the
remaining arguments equal to `1`). This module proves

* the CDF of any reindexed copula, `C.reindex ρ` at `v`, is `C` at the point `marginPoint ρ v`
  whose `i`-th coordinate is the minimum of the `v j` with `ρ j = i` (and `1` if there is none)
  (`cdf_reindex`); for injective `ρ` this is "set the other arguments to `1`"
  (`cdf_reindex_of_injective`);
* margins of `Π_d` are `Π_e` (`reindex_independence`), margins (and repetitions) of `M_d` are
  `M_e` (`reindex_comonotonic`), and margins commute with reflections (`reindex_reflect`), in
  particular with survival copulas (`reindex_survivalCopula`);
* the characterization of the independence copula: `C = Π_d` iff the coordinates are mutually
  independent under `C` (`eq_independence_iff_iIndepFun`) iff `C(u) = ∏ uᵢ`
  (`eq_independence_iff_cdf`) (Nelsen 2006, §2.10, in copula form).
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d e : ℕ}

/-- The point of `[0,1]^d` at which a `d`-copula is evaluated to obtain the CDF of `C.reindex ρ`
at `v`: coordinate `i` is the minimum of the `v j` with `ρ j = i`, and `1` if there is none. -/
noncomputable def marginPoint (ρ : Fin e → Fin d) (v : Fin e → I) (i : Fin d) : I :=
  ⨅ (j : Fin e) (_ : ρ j = i), v j

theorem le_marginPoint_iff (ρ : Fin e → Fin d) (v : Fin e → I) (x : Fin d → I) :
    x ≤ marginPoint ρ v ↔ ∀ j, x (ρ j) ≤ v j := by
  constructor
  · intro h j
    exact (h (ρ j)).trans (by unfold marginPoint; exact iInf_le_of_le j (iInf_le_of_le rfl le_rfl))
  · intro h i
    exact le_iInf₂ fun j hj => hj ▸ h j

theorem marginPoint_apply_of_injective {ρ : Fin e → Fin d} (hρ : Function.Injective ρ)
    (v : Fin e → I) (j : Fin e) : marginPoint ρ v (ρ j) = v j := by
  unfold marginPoint
  apply le_antisymm (iInf_le_of_le j (iInf_le_of_le rfl le_rfl))
  exact le_iInf₂ fun k hk => (hρ hk) ▸ le_rfl

theorem marginPoint_apply_of_notMem_range (ρ : Fin e → Fin d) (v : Fin e → I) {i : Fin d}
    (hi : i ∉ Set.range ρ) : marginPoint ρ v i = 1 := by
  apply le_antisymm unitInterval.le_one'
  exact le_iInf₂ fun j hj => absurd ⟨j, hj⟩ hi

/-- **CDF of a reindexed copula**: evaluate `C` at `marginPoint ρ v`. -/
theorem cdf_reindex (C : Copula d) (ρ : Fin e → Fin d) (v : Fin e → I) :
    (C.reindex ρ).cdf v = C.cdf (marginPoint ρ v) := by
  have hm : Measurable (fun (x : Fin d → I) (i : Fin e) => x (ρ i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ρ i)
  rw [cdf, toMeasure_reindex, map_measureReal_apply hm measurableSet_Iic, cdf]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, le_marginPoint_iff]
  exact Iff.rfl

/-- **Margins of a `d`-copula** (Nelsen 2006, §2.10): for injective `ρ`, the CDF of the margin
`C.reindex ρ` is obtained by putting `v j` in coordinate `ρ j` and `1` elsewhere. -/
theorem cdf_reindex_of_injective (C : Copula d) {ρ : Fin e → Fin d}
    (hρ : Function.Injective ρ) (v : Fin e → I) (x : Fin d → I)
    (hx : ∀ j, x (ρ j) = v j) (h1 : ∀ i, i ∉ Set.range ρ → x i = 1) :
    (C.reindex ρ).cdf v = C.cdf x := by
  rw [cdf_reindex]
  congr 1
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    rw [marginPoint_apply_of_injective hρ, hx]
  · rw [marginPoint_apply_of_notMem_range ρ v hi, h1 i hi]

/-- Bivariate margins: the `(i, j)` margin evaluated at `(s, t)`. -/
theorem cdf_reindex_pair (C : Copula d) {i j : Fin d} (hij : i ≠ j) (s t : I) :
    (C.reindex ![i, j]).cdf ![s, t] =
      C.cdf (Function.update (Function.update (fun _ => 1) i s) j t) := by
  have hρ : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  apply cdf_reindex_of_injective C hρ
  · intro k
    fin_cases k
    · simp [Function.update_of_ne hij]
    · simp
  · intro k hk
    have hki : k ≠ i := fun h => hk ⟨0, by simp [h]⟩
    have hkj : k ≠ j := fun h => hk ⟨1, by simp [h]⟩
    simp [Function.update_of_ne hki, Function.update_of_ne hkj]

/-- **Margins of the independence copula** are independence copulas. -/
theorem reindex_independence {ρ : Fin e → Fin d} (hρ : Function.Injective ρ) :
    (independence d).reindex ρ = independence e := by
  apply ext_cdf
  intro v
  rw [cdf_reindex, cdf_independence, cdf_independence]
  symm
  apply Fintype.prod_of_injective ρ hρ
  · intro i hi
    rw [marginPoint_apply_of_notMem_range ρ v hi, Set.Icc.coe_one]
  · intro j
    rw [marginPoint_apply_of_injective hρ]

/-- **Margins and repetitions of the comonotonic copula** are comonotonic. -/
theorem reindex_comonotonic (ρ : Fin e → Fin d) :
    (comonotonic d).reindex ρ = comonotonic e := by
  apply ext
  rw [toMeasure_reindex, toMeasure_comonotonic, toMeasure_comonotonic,
    Measure.map_map (Measurable.of_eval fun i => measurable_pi_apply (ρ i))
      (Measurable.of_eval fun _ => measurable_id : Measurable fun (u : I) (_ : Fin d) => u)]
  rfl

/-- **Margins commute with reflections**: reflecting the coordinates in `s` and then taking the
`ρ`-margin is the same as taking the margin and reflecting the coordinates mapped into `s`. -/
theorem reindex_reflect (C : Copula d) (s : Finset (Fin d)) (ρ : Fin e → Fin d) :
    (C.reflect s).reindex ρ = (C.reindex ρ).reflect (Finset.univ.filter fun j => ρ j ∈ s) := by
  apply ext
  have hm : Measurable (fun (x : Fin d → I) (i : Fin e) => x (ρ i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (ρ i)
  rw [toMeasure_reindex, toMeasure_reflect, toMeasure_reflect, toMeasure_reindex,
    Measure.map_map hm (measurable_reflectPoint s),
    Measure.map_map (measurable_reflectPoint _) hm]
  congr 1
  funext x j
  simp [reflectPoint]

/-- Margins of the survival copula are the survival copulas of the margins. -/
theorem reindex_survivalCopula (C : Copula d) (ρ : Fin e → Fin d) :
    (C.reflect Finset.univ).reindex ρ = (C.reindex ρ).reflect Finset.univ := by
  rw [reindex_reflect]
  congr 1
  ext j
  simp

/-! ### Characterization of the independence copula -/

/-- **`C = Π_d` iff the coordinates are mutually independent under `C`.** -/
theorem eq_independence_iff_iIndepFun (C : Copula d) :
    C = independence d ↔ iIndepFun (fun (i : Fin d) (x : Fin d → I) => x i) C.toMeasure := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)]
  simp only [map_eval]
  have hid : C.toMeasure.map (fun (x : Fin d → I) (i : Fin d) => x i) = C.toMeasure := by
    exact Measure.map_id
  rw [hid, ← toMeasure_independence]
  exact ⟨fun h => h ▸ rfl, fun h => ext h⟩

/-- **`C = Π_d` iff `C(u) = ∏ uᵢ` for all `u`.** -/
theorem eq_independence_iff_cdf (C : Copula d) :
    C = independence d ↔ ∀ u, C.cdf u = ∏ i, (u i : ℝ) := by
  constructor
  · rintro rfl u
    exact cdf_independence u
  · intro h
    exact ext_cdf fun u => by rw [h, cdf_independence]

end ProbabilityTheory.Copula
