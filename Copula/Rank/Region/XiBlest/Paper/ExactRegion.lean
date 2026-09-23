import Copula.Rank.Region.XiBlest.Paper.HyperbolicCoefficients
import Copula.Rank.Region.XiBlest.Paper.StrictParameters

/-! # The exact region in the paper's explicit coefficient parametrization -/

open ProbabilityTheory Set Filter ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem formula_zero : xiFormula 0=0 ∧ nuFormula 0=0 := by norm_num [xiFormula,nuFormula]

/-- Equation (6), with the infinity endpoint written as the vertical segment. -/
theorem exact_region (x y : ℝ) : (x,y) ∈ attainableRegion ↔
    (x=1 ∧ |y| ≤ 1) ∨ ∃ b : ℝ, 0 ≤ b ∧ x=xiFormula b ∧ |y| ≤ nuFormula b := by
  constructor
  · rintro ⟨C,hx,hy⟩
    change C.chatterjeeXi=x at hx
    change blestNu C=y at hy
    have hx0 : 0 ≤ x := hx ▸ C.chatterjeeXi_nonneg
    have hx1 : x ≤ 1 := hx ▸ C.chatterjeeXi_le_one
    by_cases he1 : x=1
    · refine Or.inl ⟨he1,?_⟩
      rw [← hy]
      exact abs_le.mpr (blest_mem_Icc C)
    · apply Or.inr
      by_cases he0 : x=0
      · have hC := C.chatterjeeXi_eq_zero_iff.mp (hx.trans he0)
        have hy0 : y=0 := by rw [← hy,hC,blest_independence]
        exact ⟨0,le_rfl,he0.trans formula_zero.1.symm,by rw [hy0,formula_zero.2]; norm_num⟩
      · obtain ⟨b,hb,he⟩ := extremal_parameter_exists x ⟨lt_of_le_of_ne hx0 (Ne.symm he0),lt_of_le_of_ne hx1 he1⟩
        refine ⟨b,hb.le,he.symm.trans (extremal_coefficients b hb.le).1,?_⟩
        rw [← (extremal_coefficients b hb.le).2]
        apply (extremal_slice_iff b hb y).mp
        exact ⟨C,hx.trans he.symm,hy⟩
  · rintro (⟨rfl,hy⟩ | ⟨b,hb,rfl,hy⟩)
    · obtain ⟨C,hC,hCy⟩ := (xi_one_slice y).mpr (abs_le.mp hy)
      exact ⟨C,hC,hCy⟩
    · rcases eq_or_lt_of_le hb with hz | hp
      · subst b
        rw [formula_zero.1,formula_zero.2] at *
        have hy0 : y=0 := abs_nonpos_iff.mp hy
        exact ⟨Copula.independence 2,Copula.chatterjeeXi_independence,blest_independence.trans hy0.symm⟩
      · rw [← (extremal_coefficients b hb).1]
        apply (extremal_slice_iff b hp y).mpr
        rwa [(extremal_coefficients b hb).2]

theorem lower_boundary_unique (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi=xiFormula b) :
    blestNu C = -nuFormula b ↔ C=(extremalCopula b hb.le).reflect {1} := by
  constructor
  · intro hy
    have hr : blestNu (C.reflect {1})=blestNu (extremalCopula b hb.le) := by
      rw [blest_reflect_second,hy,(extremal_coefficients b hb.le).2,neg_neg]
    have he := (extremal_maximal_blest_eq_iff (C.reflect {1}) b hb (by
      rw [xi_reflect_second,hx,(extremal_coefficients b hb.le).1])).mp hr
    simpa only [Copula.reflect_reflect] using congrArg (fun D : Copula 2 => D.reflect {1}) he
  · rintro rfl
    rw [blest_reflect_second,(extremal_coefficients b hb.le).2]

theorem upper_boundary_unique (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi=xiFormula b) :
    blestNu C = nuFormula b ↔ C=extremalCopula b hb.le := by
  rw [← (extremal_coefficients b hb.le).2]
  exact extremal_maximal_blest_eq_iff C b hb (hx.trans (extremal_coefficients b hb.le).1.symm)

theorem formula_infinity_limits :
    Tendsto xiFormula atTop (𝓝 1) ∧ Tendsto nuFormula atTop (𝓝 1) := by
  have hbound (b : ℝ) (hb : 0 ≤ b) : xiFormula b ≤ 1 ∧ nuFormula b ≤ 1 := by
    rw [← (extremal_coefficients b hb).1,← (extremal_coefficients b hb).2]
    exact ⟨(extremalCopula b hb).chatterjeeXi_le_one,(blest_mem_Icc (extremalCopula b hb)).2⟩
  constructor
  · apply tendsto_order.mpr
    constructor
    · intro l hl
      obtain ⟨n,hn⟩ := (extremalSequence_xi.eventually_const_lt hl).exists
      filter_upwards [eventually_ge_atTop (((n : ℝ)+1)^2)] with b hb
      have hnon : 0 ≤ b := (sq_nonneg _).trans hb
      rw [← (extremal_coefficients b hnon).1]
      exact hn.trans_le (extremal_coefficients_monotone (sq_nonneg _) hnon hb).1
    · intro u hu
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
      exact (hbound b hb).1.trans_lt hu
  · apply tendsto_order.mpr
    constructor
    · intro l hl
      obtain ⟨n,hn⟩ := (extremalSequence_blest.eventually_const_lt hl).exists
      filter_upwards [eventually_ge_atTop (((n : ℝ)+1)^2)] with b hb
      have hnon : 0 ≤ b := (sq_nonneg _).trans hb
      rw [← (extremal_coefficients b hnon).2]
      exact hn.trans_le (extremal_coefficients_monotone (sq_nonneg _) hnon hb).2
    · intro u hu
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
      exact (hbound b hb).2.trans_lt hu

end ProbabilityTheory.Copula.RankRegion.XiBlest
