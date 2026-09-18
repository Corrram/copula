/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Density
import Copula.Dependence.Examples

/-! # Conditional total positivity does not require an MTP2 density -/

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

theorem volume_cube_diagonal :
    (volume : Measure (Fin 2 → I)) {x | x 0 = x 1} = 0 := by
  have hs : MeasurableSet {p : I × I | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hp : (volume : Measure I).prod volume {p : I × I | p.1 = p.2} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hs
    apply Filter.Eventually.of_forall
    intro u
    have he : Prod.mk u ⁻¹' {p : I × I | p.1 = p.2} = {u} := by
      ext v; simp [eq_comm]
    simp [he]
  have h := (measurePreserving_finTwoArrow (volume : Measure I)).measure_preimage hs.nullMeasurableSet
  exact h.trans hp

/-- Comonotonicity has a TP2 conditional kernel, but no Lebesgue MTP2 density. -/
theorem not_hasMTP2Density_comonotonic : ¬ (comonotonic 2).HasMTP2Density := by
  intro h
  have hz := h.absolutelyContinuous volume_cube_diagonal
  have hm : (comonotonic 2).toMeasure {x | x 0 = x 1} = 1 := by
    rw [toMeasure_comonotonic, Measure.map_apply (by fun_prop)
      (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1))]
    simp
  rw [hm] at hz
  exact one_ne_zero hz

theorem isNQD_independence : (independence 2).IsNQD := by
  intro u v
  simp [cdf_independence, Fin.prod_univ_two]

theorem isNQD_countermonotonic : countermonotonic.IsNQD := by
  intro u v
  simp only [cdf_countermonotonic, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply max_le (mul_nonneg u.property.1 v.property.1)
  nlinarith [mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr v.property.2)]

theorem isPQD_and_isNQD_iff (C : Copula 2) :
    C.IsPQD ∧ C.IsNQD ↔ C = independence 2 := by
  constructor
  · rintro ⟨hp, hn⟩
    apply ext_cdf
    intro u
    have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
    have hx := le_antisymm (hn (u 0) (u 1)) (hp (u 0) (u 1))
    simpa [he, cdf_independence, Fin.prod_univ_two] using hx
  · rintro rfl
    exact ⟨isPQD_independence, isNQD_independence⟩

end ProbabilityTheory.Copula
