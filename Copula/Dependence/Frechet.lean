/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.Singular
import Copula.Families.Frechet
import Copula.Order.Orthant

/-! # Exact dependence classifications of Frechet mixtures -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)

theorem frechet_exchangeable : (Copula.frechet a b ha hb hab).IsExchangeable := by
  rw [Copula.isExchangeable_iff]
  intro u v
  simp only [Copula.cdf_frechet,
    (Copula.isExchangeable_iff _).mp Copula.isExchangeable_comonotonic u v,
    (Copula.isExchangeable_iff _).mp Copula.isExchangeable_countermonotonic u v,
    (Copula.isExchangeable_iff _).mp Copula.isExchangeable_independence u v]

theorem frechet_si_iff : (Copula.frechet a b ha hb hab).IsSI ↔ b = 0 := by
  constructor
  · intro h
    have ht := h Copula.unitHalf ⟨3 / 4, by constructor <;> norm_num⟩ 1
      ⟨1 / 4, by constructor <;> norm_num⟩ (by norm_num [Copula.unitHalf]) (by change (3 / 4 : ℝ) ≤ 1; norm_num)
    simp only [Copula.cdf_frechet, Copula.cdf_comonotonic_two,
      Copula.cdf_countermonotonic, Copula.cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    norm_num [Copula.unitHalf] at ht
    linarith
  · intro hb0 u v w t huv hvw
    have hm := Copula.isSI_comonotonic u v w t huv hvw
    have hp := Copula.isSI_independence u v w t huv hvw
    simp only [Copula.cdf_frechet, hb0, zero_mul, add_zero, sub_zero]
    have ha1 : 0 ≤ 1 - a := by linarith
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hm), mul_nonneg ha1 (sub_nonneg.mpr hp)]

theorem frechet_sd_iff : (Copula.frechet a b ha hb hab).IsSD ↔ a = 0 := by
  constructor
  · intro h
    have ht := h 0 ⟨1 / 4, by constructor <;> norm_num⟩ Copula.unitHalf
      ⟨1 / 4, by constructor <;> norm_num⟩ (by norm_num) (by norm_num [Copula.unitHalf])
    simp only [Copula.cdf_frechet, Copula.cdf_comonotonic_two,
      Copula.cdf_countermonotonic, Copula.cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    norm_num [Copula.unitHalf] at ht
    linarith
  · intro ha0 u v w t huv hvw
    have hm := Copula.isSD_countermonotonic u v w t huv hvw
    have hp := Copula.isSD_independence u v w t huv hvw
    simp only [Copula.cdf_frechet, ha0, zero_mul, zero_add, sub_zero]
    have hb1 : 0 ≤ 1 - b := by linarith
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hm), mul_nonneg hb1 (sub_nonneg.mpr hp)]

theorem frechet_ci_iff : (Copula.frechet a b ha hb hab).IsCI ↔ b = 0 := by
  rw [(frechet_exchangeable a b ha hb hab).isCI_iff, frechet_si_iff]

theorem frechet_cd_iff : (Copula.frechet a b ha hb hab).IsCD ↔ a = 0 := by
  rw [(frechet_exchangeable a b ha hb hab).isCD_iff, frechet_sd_iff]


/-- Measure-level identity, including singular component weights. -/
theorem frechet_measure : (Copula.frechet a b ha hb hab).toMeasure =
    ENNReal.ofReal a • (Copula.comonotonic 2).toMeasure +
      ENNReal.ofReal b • Copula.countermonotonic.toMeasure +
      ENNReal.ofReal (1 - a - b) • (Copula.independence 2).toMeasure := by
  let μ : Measure (Fin 2 → I) := ENNReal.ofReal a • (Copula.comonotonic 2).toMeasure +
    ENNReal.ofReal b • Copula.countermonotonic.toMeasure +
    ENNReal.ofReal (1 - a - b) • (Copula.independence 2).toMeasure
  have hc : 0 ≤ 1 - a - b := by linarith
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hc]
    norm_num
  have hμ (u : Fin 2 → I) : μ.real (Iic u) = (Copula.frechet a b ha hb hab).cdf u := by
    rw [Copula.cdf_frechet]
    simp only [μ, Measure.real, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
      ENNReal.toReal_ofReal hc, Copula.cdf]
    rfl
  let D := (Copula.frechet a b ha hb hab).isClassical_cdf.ofMeasure ⟨μ, inferInstance⟩ hμ
  have he : D = Copula.frechet a b ha hb hab := Copula.ext_cdf hμ
  rw [← he]
  rfl

private theorem volume_cube_antidiagonal :
    (volume : Measure (Fin 2 → I)) {x | x 1 = unitInterval.symm (x 0)} = 0 := by
  have hs : MeasurableSet {p : I × I | p.2 = unitInterval.symm p.1} :=
    measurableSet_eq_fun measurable_snd (unitInterval.continuous_symm.measurable.comp measurable_fst)
  have hp : (volume : Measure I).prod volume {p : I × I | p.2 = unitInterval.symm p.1} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hs
    apply Filter.Eventually.of_forall
    intro u
    have he : Prod.mk u ⁻¹' {p : I × I | p.2 = unitInterval.symm p.1} = {unitInterval.symm u} := rfl
    simp [he]
  have h := (measurePreserving_finTwoArrow (volume : Measure I)).measure_preimage hs.nullMeasurableSet
  exact h.trans hp

/-- A Frechet mixture is absolutely continuous exactly when both singular weights vanish. -/
theorem frechet_absolutelyContinuous_iff :
    (Copula.frechet a b ha hb hab).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hd := h Copula.volume_cube_diagonal
    have hw := h volume_cube_antidiagonal
    have hm : (Copula.comonotonic 2).toMeasure {x | x 0 = x 1} = 1 := by
      rw [Copula.toMeasure_comonotonic, Measure.map_apply (by fun_prop)
        (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1))]
      simp
    have hW : Copula.countermonotonic.toMeasure {x | x 1 = unitInterval.symm (x 0)} = 1 := by
      rw [Copula.toMeasure_countermonotonic, Measure.map_apply (by fun_prop)
        (measurableSet_eq_fun (measurable_pi_apply 1)
          (unitInterval.continuous_symm.measurable.comp (measurable_pi_apply 0)))]
      simp
    rw [frechet_measure a b ha hb hab] at hd hw
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hm, mul_one] at hd
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hW, mul_one] at hw
    have ha0 : ENNReal.ofReal a = 0 := (add_eq_zero.mp (add_eq_zero.mp hd).1).1
    have hb0 : ENNReal.ofReal b = 0 := (add_eq_zero.mp (add_eq_zero.mp hw).1).2
    exact ⟨le_antisymm (ENNReal.ofReal_eq_zero.mp ha0) ha,
      le_antisymm (ENNReal.ofReal_eq_zero.mp hb0) hb⟩
  · rintro ⟨rfl, rfl⟩
    have he : Copula.frechet 0 0 ha hb hab = Copula.independence 2 := by
      apply Copula.ext_cdf
      intro u
      simp [Copula.cdf_frechet]
    rw [he]
    exact Measure.AbsolutelyContinuous.rfl

/-- Density TP2 is possible only at independence, not at the singular M or W endpoints. -/
theorem frechet_density_tp2_iff :
    (Copula.frechet a b ha hb hab).HasMTP2Density ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    exact (frechet_absolutelyContinuous_iff a b ha hb hab).mp h.absolutelyContinuous
  · rintro ⟨rfl, rfl⟩
    have he : Copula.frechet 0 0 ha hb hab = Copula.independence 2 := by
      apply Copula.ext_cdf
      intro u
      simp [Copula.cdf_frechet]
    rw [he]
    exact Copula.hasMTP2Density_independence 2

theorem mardia_ci_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).IsCI ↔ θ = 0 ∨ θ = 1 := by
  rw [Copula.mardia, frechet_ci_iff]
  constructor
  · intro h
    have he : θ ^ 2 * (1 - θ) = 0 := by linarith
    rcases mul_eq_zero.mp he with hz | hz
    · exact Or.inl (eq_zero_of_pow_eq_zero hz)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem mardia_cd_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).IsCD ↔ θ = 0 ∨ θ = -1 := by
  rw [Copula.mardia, frechet_cd_iff]
  constructor
  · intro h
    have he : θ ^ 2 * (1 + θ) = 0 := by linarith
    rcases mul_eq_zero.mp he with hz | hz
    · exact Or.inl (eq_zero_of_pow_eq_zero hz)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

private theorem mardia_weights_zero (θ : ℝ) :
    (θ ^ 2 * (1 + θ) / 2 = 0 ∧ θ ^ 2 * (1 - θ) / 2 = 0) ↔ θ = 0 := by
  constructor
  · rintro ⟨ha, hb⟩
    have he : θ ^ 2 = 0 := by nlinarith
    exact eq_zero_of_pow_eq_zero he
  · rintro rfl
    norm_num

theorem mardia_absolutelyContinuous_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ θ = 0 := by
  rw [Copula.mardia, frechet_absolutelyContinuous_iff, mardia_weights_zero]

theorem mardia_density_tp2_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).HasMTP2Density ↔ θ = 0 := by
  rw [Copula.mardia, frechet_density_tp2_iff, mardia_weights_zero]

/-- A concrete incomparable pair proves the source's lack of parameter ordering. -/
theorem mardia_not_lowerOrthant_ordered :
    ¬(Copula.mardia (1 / 2) (by norm_num)).LowerOrthantLE (Copula.mardia 0 (by norm_num)) ∧
      ¬(Copula.mardia 0 (by norm_num)).LowerOrthantLE (Copula.mardia (1 / 2) (by norm_num)) := by
  constructor
  · intro h
    have ht := h ![⟨1 / 8, by constructor <;> norm_num⟩, ⟨1 / 8, by constructor <;> norm_num⟩]
    simp only [Copula.mardia, Copula.cdf_frechet, Copula.cdf_comonotonic_two,
      Copula.cdf_countermonotonic, Copula.cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    norm_num at ht
  · intro h
    have ht := h ![⟨1 / 8, by constructor <;> norm_num⟩, ⟨7 / 8, by constructor <;> norm_num⟩]
    simp only [Copula.mardia, Copula.cdf_frechet, Copula.cdf_comonotonic_two,
      Copula.cdf_countermonotonic, Copula.cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    norm_num at ht

end ProbabilityTheory.Copula
