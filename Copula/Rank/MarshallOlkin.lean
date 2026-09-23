import Copula.Families.MarshallOlkin
import Copula.Rank.SpearmanCDF
import Copula.Dependence.Density
import Mathlib.MeasureTheory.Integral.Prod

/-! # Spearman rho of the two-parameter Marshall–Olkin family -/

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace ProbabilityTheory.Copula
private theorem integral_unit_rpow_nonneg (p : ℝ) (hp : 0 ≤ p) :
    (∫ u : I, (u : ℝ) ^ p) = 1 / (p + 1) := by
  rw [Copula.integral_unitInterval (fun t : ℝ => t ^ p),
    integral_rpow (Or.inl (by linarith))]
  simp only [Real.one_rpow, Real.zero_rpow (show p + 1 ≠ 0 by linarith), sub_zero]

private theorem integral_unit_Iic_rpow_nonneg (p : ℝ) (hp : 0 ≤ p) (v : I) :
    (∫ u in Iic v, (u : ℝ) ^ p) = (v : ℝ) ^ (p + 1) / (p + 1) := by
  rw [Copula.integral_unit_Iic (fun t : ℝ => t ^ p) v,
    integral_rpow (Or.inl (by linarith))]
  simp only [Real.zero_rpow (show p + 1 ≠ 0 by linarith), sub_zero]

private theorem integral_cube_Iic_iterated {f : (Fin 2 → I) → ℝ}
    (hf : Integrable f) (u v : I) :
    (∫ x in Iic ![u, v], f x) = ∫ s in Iic u, ∫ t in Iic v, f ![s, t] := by
  have hm := (volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow
  have he := hm.setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding f (Iic ![u, v])
  have hs : MeasurableEquiv.finTwoArrow.symm ⁻¹' Iic ![u, v] = Iic u ×ˢ Iic v := by
    ext p
    change (∀ i : Fin 2, (![p.1, p.2] i) ≤ ![u, v] i) ↔ p.1 ≤ u ∧ p.2 ≤ v
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hs] at he
  rw [← he]
  have hi := hm.integrable_comp_of_integrable hf
  exact setIntegral_prod _ hi.integrableOn

private theorem marshallOlkin_zero_right (α : I) :
    marshallOlkin α 0 = independence 2 := by
  apply Copula.ext_cdf
  intro x
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  by_cases hu : x 0 = 0
  · simp [hu]
  have hup : (0 : ℝ) < x 0 :=
    lt_of_le_of_ne (x 0).property.1 (Ne.symm (fun he => hu (Subtype.ext he)))
  rw [cdf_marshallOlkin, cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.Icc.coe_zero, Real.rpow_zero, sub_zero, Real.rpow_one]
  rw [min_eq_left (Real.rpow_le_one (x 0).property.1 (x 0).property.2 α.property.1),
    ← mul_assoc, ← Real.rpow_add hup]
  simp

private noncomputable def moSwitch (α β u : I) (hb : 0 < (β : ℝ)) : I :=
  ⟨(u : ℝ) ^ ((α : ℝ) / (β : ℝ)),
    Real.rpow_nonneg u.property.1 _,
    Real.rpow_le_one u.property.1 u.property.2 (div_nonneg α.property.1 hb.le)⟩

private theorem moSwitch_power (α β u : I) (hb : 0 < (β : ℝ)) :
    ((moSwitch α β u hb : I) : ℝ) ^ (β : ℝ) = (u : ℝ) ^ (α : ℝ) := by
  change ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ (β : ℝ) = (u : ℝ) ^ (α : ℝ)
  rw [← Real.rpow_mul u.property.1]
  congr 1
  exact div_mul_cancel₀ _ hb.ne'

private theorem mo_cdf_of_le_switch (α β u v : I) (hb : 0 < (β : ℝ))
    (hv : v ≤ moSwitch α β u hb) :
    (Copula.marshallOlkin α β).cdf ![u, v] =
      (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) := by
  have hp : (v : ℝ) ^ (β : ℝ) ≤ (u : ℝ) ^ (α : ℝ) := by
    calc
      _ ≤ ((moSwitch α β u hb : I) : ℝ) ^ (β : ℝ) :=
        Real.rpow_le_rpow v.property.1 hv hb.le
      _ = _ := moSwitch_power α β u hb
  rw [Copula.cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [min_eq_right hp]
  have he : (v : ℝ) ^ (β : ℝ) * (v : ℝ) ^ (1 - (β : ℝ)) = (v : ℝ) := by
    rw [← Real.rpow_add_of_nonneg v.property.1 hb.le
      (show 0 ≤ 1 - (β : ℝ) by linarith [β.property.2])]
    simp
  calc
    _ = (u : ℝ) ^ (1 - (α : ℝ)) *
        ((v : ℝ) ^ (β : ℝ) * (v : ℝ) ^ (1 - (β : ℝ))) := by ring
    _ = _ := by rw [he]

private theorem mo_cdf_of_ge_switch (α β u v : I) (hb : 0 < (β : ℝ))
    (hv : moSwitch α β u hb ≤ v) :
    (Copula.marshallOlkin α β).cdf ![u, v] =
      (u : ℝ) * (v : ℝ) ^ (1 - (β : ℝ)) := by
  have hp : (u : ℝ) ^ (α : ℝ) ≤ (v : ℝ) ^ (β : ℝ) := by
    calc
      _ = ((moSwitch α β u hb : I) : ℝ) ^ (β : ℝ) :=
        (moSwitch_power α β u hb).symm
      _ ≤ _ := Real.rpow_le_rpow (moSwitch α β u hb).property.1 hv hb.le
  rw [Copula.cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [min_eq_left hp]
  have he : (u : ℝ) ^ (α : ℝ) * (u : ℝ) ^ (1 - (α : ℝ)) = (u : ℝ) := by
    rw [← Real.rpow_add_of_nonneg u.property.1 α.property.1
      (show 0 ≤ 1 - (α : ℝ) by linarith [α.property.2])]
    simp
  calc
    _ = ((u : ℝ) ^ (α : ℝ) * (u : ℝ) ^ (1 - (α : ℝ))) *
        (v : ℝ) ^ (1 - (β : ℝ)) := by ring
    _ = _ := by rw [he]

private theorem mo_section_integral (α β u : I) (hb : 0 < (β : ℝ)) :
    (∫ v : I, (Copula.marshallOlkin α β).cdf ![u, v]) =
      (u : ℝ) / (2 - (β : ℝ)) -
        (β : ℝ) / (2 * (2 - (β : ℝ))) *
          (u : ℝ) ^ (1 + (α : ℝ) * (2 - (β : ℝ)) / (β : ℝ)) := by
  let t := moSwitch α β u hb
  let p : ℝ := 1 - (β : ℝ)
  have hp : 0 ≤ p := by dsimp [p]; linarith [β.property.2]
  have hi : Integrable (fun v : I => (v : ℝ) ^ p) :=
    Copula.integrable_continuous_unit volume
      ((Real.continuous_rpow_const hp).comp continuous_subtype_val)
  have hiC : Integrable (fun v : I => (Copula.marshallOlkin α β).cdf ![u, v]) :=
    Copula.integrable_continuous_unit volume
      ((Copula.marshallOlkin α β).continuous_cdf.comp (by fun_prop))
  have hsplit := integral_add_compl (s := Iic t) measurableSet_Iic hiC
  rw [compl_Iic] at hsplit
  have hleft : (∫ v in Iic t, (Copula.marshallOlkin α β).cdf ![u, v]) =
      (u : ℝ) ^ (1 - (α : ℝ)) * ((t : ℝ) ^ 2 / 2) := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun v hv => mo_cdf_of_le_switch α β u v hb hv), integral_const_mul,
      Copula.integral_unit_Iic (fun z : ℝ => z) t, integral_id]
    ring
  have hrightPow : (∫ v in Ioi t, (v : ℝ) ^ p) =
      1 / (p + 1) - (t : ℝ) ^ (p + 1) / (p + 1) := by
    have he := integral_add_compl (s := Iic t) measurableSet_Iic hi
    rw [compl_Iic, integral_unit_Iic_rpow_nonneg p hp t] at he
    rw [integral_unit_rpow_nonneg p hp] at he
    linarith only [he]
  have hright : (∫ v in Ioi t, (Copula.marshallOlkin α β).cdf ![u, v]) =
      (u : ℝ) * (1 / (p + 1) - (t : ℝ) ^ (p + 1) / (p + 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => mo_cdf_of_ge_switch α β u v hb (le_of_lt hv)),
      integral_const_mul]
    exact congrArg ((u : ℝ) * ·) hrightPow
  have hq1 : (u : ℝ) ^ (1 - (α : ℝ)) * (t : ℝ) ^ 2 =
      (u : ℝ) ^ (1 + (α : ℝ) * (2 - (β : ℝ)) / (β : ℝ)) := by
    change (u : ℝ) ^ (1 - (α : ℝ)) *
      ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ 2 = _
    calc
      _ = (u : ℝ) ^ (1 - (α : ℝ)) *
          (u : ℝ) ^ (((α : ℝ) / (β : ℝ)) * (2 : ℝ)) := by
            rw [Real.rpow_mul u.property.1]
            norm_cast
      _ = (u : ℝ) ^ ((1 - (α : ℝ)) + ((α : ℝ) / (β : ℝ)) * 2) := by
            rw [Real.rpow_add_of_nonneg u.property.1
              (show 0 ≤ 1 - (α : ℝ) by linarith [α.property.2])
              (mul_nonneg (div_nonneg α.property.1 hb.le) (by norm_num : (0:ℝ) ≤ 2))]
      _ = _ := by
            congr 1
            field_simp
            ring
  have hq2 : (u : ℝ) * (t : ℝ) ^ (p + 1) =
      (u : ℝ) ^ (1 + (α : ℝ) * (2 - (β : ℝ)) / (β : ℝ)) := by
    change (u : ℝ) * ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ (p + 1) = _
    calc
      _ = (u : ℝ) ^ (1 : ℝ) *
          (u : ℝ) ^ (((α : ℝ) / (β : ℝ)) * (p + 1)) := by
            rw [Real.rpow_one, Real.rpow_mul u.property.1]
      _ = (u : ℝ) ^ (1 + ((α : ℝ) / (β : ℝ)) * (p + 1)) := by
            rw [Real.rpow_add_of_nonneg u.property.1 (by norm_num : (0:ℝ) ≤ 1)
              (mul_nonneg (div_nonneg α.property.1 hb.le) (by linarith : 0 ≤ p + 1))]
      _ = _ := by
            congr 1
            dsimp [p]
            field_simp
            ring
  have hd : p + 1 = 2 - (β : ℝ) := by dsimp [p]; ring
  have hd0 : 2 - (β : ℝ) ≠ 0 := by linarith [β.property.2]
  rw [hleft, hright] at hsplit
  calc
    _ = (u : ℝ) ^ (1 - (α : ℝ)) * ((t : ℝ) ^ 2 / 2) +
      (u : ℝ) * (1 / (p + 1) - (t : ℝ) ^ (p + 1) / (p + 1)) := hsplit.symm
    _ = ((u : ℝ) ^ (1 - (α : ℝ)) * (t : ℝ) ^ 2) / 2 +
      (u : ℝ) / (p + 1) - ((u : ℝ) * (t : ℝ) ^ (p + 1)) / (p + 1) := by ring
    _ = _ := by
      rw [hq1, hq2, hd]
      field_simp
      ring


theorem integral_marshallOlkin_cdf (α β : I) (hb : 0 < (β : ℝ)) :
    (∫ x : Fin 2 → I, (Copula.marshallOlkin α β).cdf x) =
      ((α : ℝ) + (β : ℝ)) / (2 * (2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ))) := by
  have hi := (Copula.marshallOlkin α β).integrable_cdf volume
  have he := integral_cube_Iic_iterated hi 1 1
  have htop : Iic (![(1 : I), 1]) = Set.univ := by
    ext x
    simp only [mem_Iic, mem_univ, iff_true, Pi.le_def, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨(x 0).property.2, (x 1).property.2⟩
  simp only [htop, Measure.restrict_univ, show Iic (1 : I) = Set.univ from Set.Iic_top] at he
  rw [he]
  simp_rw [mo_section_integral α β _ hb]
  let q : ℝ := 1 + (α : ℝ) * (2 - (β : ℝ)) / (β : ℝ)
  have hq : 0 ≤ q := by
    dsimp [q]
    have : 0 ≤ (α : ℝ) * (2 - (β : ℝ)) / (β : ℝ) := by
      apply div_nonneg (mul_nonneg α.property.1 (by linarith [β.property.2])) hb.le
    linarith
  have hiPow : Integrable (fun u : I => (u : ℝ) ^ q) :=
    Copula.integrable_continuous_unit volume
      ((Real.continuous_rpow_const hq).comp continuous_subtype_val)
  have hiId : Integrable (fun u : I => (u : ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  change (∫ u : I, (u : ℝ) / (2 - (β : ℝ)) -
    (β : ℝ) / (2 * (2 - (β : ℝ))) * (u : ℝ) ^ q) = _
  rw [integral_sub (hiId.div_const _)
      (hiPow.const_mul _), integral_div,
      integral_const_mul, Copula.integral_unit_id,
      integral_unit_rpow_nonneg q hq]
  have hb0 : (β : ℝ) ≠ 0 := hb.ne'
  have hd : 2 - (β : ℝ) ≠ 0 := by linarith [β.property.2]
  have hd2 : 2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ) ≠ 0 := by
    have h : 0 ≤ (α : ℝ) * (2 - (β : ℝ)) :=
      mul_nonneg α.property.1 (by linarith [β.property.2])
    nlinarith
  dsimp [q]
  have hd2' : (β : ℝ) * 2 - (β : ℝ) * (α : ℝ) + (α : ℝ) * 2 ≠ 0 := by
    convert hd2 using 1; ring
  field_simp [hb0, hd, hd2, hd2']
  rw [← mul_inv_cancel₀ hd2']
  ring

theorem marshallOlkin_spearmanRho_pos (α β : I) (hb : 0 < (β : ℝ)) :
    (Copula.marshallOlkin α β).spearmanRho =
      3 * (α : ℝ) * (β : ℝ) /
        (2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ)) := by
  rw [Copula.spearmanRho_eq_integral_cdf, Copula.toMeasure_independence]
  change 12 * (∫ x : Fin 2 → I, (Copula.marshallOlkin α β).cdf x) - 3 = _
  rw [integral_marshallOlkin_cdf α β hb]
  have hd : 2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ) ≠ 0 := by
    have h : 0 ≤ (α : ℝ) * (2 - (β : ℝ)) :=
      mul_nonneg α.property.1 (by linarith [β.property.2])
    nlinarith
  have hd' : (α : ℝ) * 2 - (α : ℝ) * (β : ℝ) + (β : ℝ) * 2 ≠ 0 := by
    convert hd using 1; ring
  field_simp [hd, hd']
  linear_combination 6 * (mul_inv_cancel₀ hd')

theorem marshallOlkin_spearmanRho (α β : I) :
    (Copula.marshallOlkin α β).spearmanRho =
      3 * (α : ℝ) * (β : ℝ) /
        (2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ)) := by
  by_cases hb : (β : ℝ) = 0
  · have hβ : β = 0 := Subtype.ext hb
    subst β
    rw [marshallOlkin_zero_right, Copula.spearmanRho_independence]
    norm_num
  · exact marshallOlkin_spearmanRho_pos α β (lt_of_le_of_ne β.property.1 (Ne.symm hb))
end ProbabilityTheory.Copula
