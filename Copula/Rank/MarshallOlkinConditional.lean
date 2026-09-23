import Copula.Rank.MarshallOlkin
import Copula.Rank.ConditionalDerivative

/-! # Conditional CDF of the two-parameter Marshall–Olkin family -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

private noncomputable def moResponseSwitch (α β v : I) (ha : 0 < (α : ℝ)) : I :=
  ⟨(v : ℝ) ^ ((β : ℝ) / (α : ℝ)),
    Real.rpow_nonneg v.property.1 _,
    Real.rpow_le_one v.property.1 v.property.2 (div_nonneg β.property.1 ha.le)⟩

private theorem moResponseSwitch_power (α β v : I) (ha : 0 < (α : ℝ)) :
    ((moResponseSwitch α β v ha : I) : ℝ) ^ (α : ℝ) = (v : ℝ) ^ (β : ℝ) := by
  change ((v : ℝ) ^ ((β : ℝ) / (α : ℝ))) ^ (α : ℝ) = (v : ℝ) ^ (β : ℝ)
  rw [← Real.rpow_mul v.property.1]
  congr 1
  exact div_mul_cancel₀ _ ha.ne'

private theorem mo_cdf_of_le_responseSwitch (α β u v : I) (ha : 0 < (α : ℝ))
    (hu : u ≤ moResponseSwitch α β v ha) :
    (Copula.marshallOlkin α β).cdf ![u, v] =
      (u : ℝ) * (v : ℝ) ^ (1 - (β : ℝ)) := by
  have hp : (u : ℝ) ^ (α : ℝ) ≤ (v : ℝ) ^ (β : ℝ) := by
    calc
      _ ≤ ((moResponseSwitch α β v ha : I) : ℝ) ^ (α : ℝ) :=
        Real.rpow_le_rpow u.property.1 hu ha.le
      _ = _ := moResponseSwitch_power α β v ha
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

private theorem mo_cdf_of_ge_responseSwitch (α β u v : I) (ha : 0 < (α : ℝ))
    (hu : moResponseSwitch α β v ha ≤ u) :
    (Copula.marshallOlkin α β).cdf ![u, v] =
      (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) := by
  have hp : (v : ℝ) ^ (β : ℝ) ≤ (u : ℝ) ^ (α : ℝ) := by
    calc
      _ = ((moResponseSwitch α β v ha : I) : ℝ) ^ (α : ℝ) :=
        (moResponseSwitch_power α β v ha).symm
      _ ≤ _ := Real.rpow_le_rpow (moResponseSwitch α β v ha).property.1 hu ha.le
  rw [Copula.cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [min_eq_right hp]
  have he : (v : ℝ) ^ (β : ℝ) * (v : ℝ) ^ (1 - (β : ℝ)) = (v : ℝ) := by
    rw [← Real.rpow_add_of_nonneg v.property.1 β.property.1
      (show 0 ≤ 1 - (β : ℝ) by linarith [β.property.2])]
    simp
  calc
    _ = (u : ℝ) ^ (1 - (α : ℝ)) *
        ((v : ℝ) ^ (β : ℝ) * (v : ℝ) ^ (1 - (β : ℝ))) := by ring
    _ = _ := by rw [he]

noncomputable def marshallOlkinConditional (α β u v : I) : ℝ :=
  if (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) then
    (v : ℝ) ^ (1 - (β : ℝ))
  else (1 - (α : ℝ)) * (u : ℝ) ^ (-(α : ℝ)) * (v : ℝ)

private theorem mo_power_lt_iff (α β u v : I) (ha : 0 < (α : ℝ)) :
    (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) ↔
      u < moResponseSwitch α β v ha := by
  change (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) ↔
    (u : ℝ) < ((moResponseSwitch α β v ha : I) : ℝ)
  rw [← moResponseSwitch_power α β v ha]
  exact Real.rpow_lt_rpow_iff u.property.1
    (moResponseSwitch α β v ha).property.1 ha

theorem conditionalCDF_marshallOlkin (α β v : I) (ha : 0 < (α : ℝ)) :
    (fun u => (Copula.marshallOlkin α β).conditionalCDF u v) =ᵐ[volume]
      fun u => marshallOlkinConditional α β u v := by
  let s := moResponseSwitch α β v ha
  filter_upwards [(Copula.marshallOlkin α β).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I), Measure.ae_ne volume (1:I),
    Measure.ae_ne volume s] with u hu hu0 hu1 hus
  rw [hu]
  have h0 : 0 < (u : ℝ) :=
    lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u : ℝ) < 1 :=
    lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  rcases lt_or_gt_of_ne hus with hus | hsu
  · rw [marshallOlkinConditional, ite_eq_left ((mo_power_lt_iff α β u v ha).mpr hus)]
    have he : Copula.cdfSection (Copula.marshallOlkin α β) v =ᶠ[𝓝 (u : ℝ)]
        (fun x => x * (v : ℝ) ^ (1 - (β : ℝ))) := by
      filter_upwards [Ioo_mem_nhds h0 h1,
        eventually_lt_nhds (show (u : ℝ) < s from hus)] with x hx hxs
      have hh := mo_cdf_of_le_responseSwitch α β
        (⟨x,hx.1.le,hx.2.le⟩:I) v ha hxs.le
      simpa only [Copula.cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩]
        using hh
    simpa using (((hasDerivAt_id (u : ℝ)).mul_const
      ((v : ℝ) ^ (1 - (β : ℝ)))).congr_of_eventuallyEq he).deriv
  · rw [marshallOlkinConditional,
      ite_eq_right ((mo_power_lt_iff α β u v ha).not.mpr (not_lt.mpr hsu.le))]
    have he : Copula.cdfSection (Copula.marshallOlkin α β) v =ᶠ[𝓝 (u : ℝ)]
        (fun x => x ^ (1 - (α : ℝ)) * (v : ℝ)) := by
      filter_upwards [Ioo_mem_nhds h0 h1,
        eventually_gt_nhds (show (s : ℝ) < u from hsu)] with x hx hsx
      have hh := mo_cdf_of_ge_responseSwitch α β
        (⟨x,hx.1.le,hx.2.le⟩:I) v ha hsx.le
      simpa only [Copula.cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩]
        using hh
    have hd := ((hasDerivAt_id (u : ℝ)).rpow_const
      (p := 1 - (α : ℝ)) (Or.inl h0.ne')).mul_const (v : ℝ)
    simpa only [id_eq,one_mul,show 1 - (α : ℝ) - 1 = -(α : ℝ) by ring]
      using (hd.congr_of_eventuallyEq he).deriv

theorem marshallOlkinConditional_measurable (α β : I) :
    Measurable (fun p : I × I => marshallOlkinConditional α β p.1 p.2) := by
  unfold marshallOlkinConditional
  exact ((measurable_subtype_coe.comp measurable_snd).pow_const _).ite
    (measurableSet_lt
      ((measurable_subtype_coe.comp measurable_fst).pow_const _)
      ((measurable_subtype_coe.comp measurable_snd).pow_const _))
    ((measurable_const.mul
      ((measurable_subtype_coe.comp measurable_fst).pow_const _)).mul
      (measurable_subtype_coe.comp measurable_snd))

theorem marshallOlkinConditional_sq_joint_integrable (α β : I)
    (ha : 0 < (α : ℝ)) :
    Integrable (fun p : I × I => marshallOlkinConditional α β p.2 p.1 ^ 2) := by
  have hc : Integrable (fun p : I × I =>
      (Copula.marshallOlkin α β).conditionalCDF p.2 p.1 ^ 2) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((Copula.marshallOlkin α β).measurable_conditionalCDF.pow_const 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [(Copula.marshallOlkin α β).conditionalCDF_nonneg p.2 p.1,
        (Copula.marshallOlkin α β).conditionalCDF_le_one p.2 p.1]
  apply hc.congr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    ((Copula.marshallOlkin α β).measurable_conditionalCDF.pow_const 2)
    (((marshallOlkinConditional_measurable α β).comp measurable_swap).pow_const 2))).mpr
  exact Eventually.of_forall fun v =>
    (conditionalCDF_marshallOlkin α β v ha).fun_comp (fun z => z ^ 2)

end ProbabilityTheory.Copula
