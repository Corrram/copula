import Copula.Rank.Region.XiBlest.Paper.RegionGeometry
import Copula.Rank.Region.XiBlest.Support.XiClosedRegion

open MeasureTheory ProbabilityTheory Set Filter ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem blest_tendsto_of_cdf (C : ℕ → Copula 2) (D : Copula 2)
    (hC : ∀ u v : I, Tendsto (fun n => (C n).cdf ![u,v]) atTop (𝓝 (D.cdf ![u,v]))) :
    Tendsto (fun n => blestNu (C n)) atTop (𝓝 (blestNu D)) := by
  have hp (x : Fin 2 → I) : Tendsto (fun n => (1-(x 0 : ℝ))*(C n).cdf x) atTop
      (𝓝 ((1-(x 0 : ℝ))*D.cdf x)) := by
    have he : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
    have h := (hC (x 0) (x 1)).const_mul (1-(x 0 : ℝ))
    simpa only [← he] using h
  have he := tendsto_integral_of_dominated_convergence (μ := (Copula.independence 2).toMeasure)
    (fun _ : Fin 2 → I => (1 : ℝ))
    (fun n => (blest_integrable (C n)).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (x 0).property.2) ((C n).cdf_nonneg _))]
      have h := mul_le_mul_of_nonneg_left ((C n).cdf_le_one x) (sub_nonneg.mpr (x 0).property.2)
      nlinarith [(x 0).property.1])
    (Eventually.of_forall hp)
  exact (he.const_mul 24).sub_const 2

/-- Theorem 1.1: the entire attained xi-Blest region is closed. -/
theorem attainable_region_closed : IsClosed attainableRegion :=
  isClosed_xiCoefficientRegion _ blest_tendsto_of_cdf fixed_coefficient_upward

theorem attainable_region_compact : IsCompact attainableRegion :=
  isCompact_xiCoefficientRegion _ attainable_region_closed (-1) 1 blest_mem_Icc

/-- Both extremal Blest values exist at every prescribed xi. Their formulas are a separate result. -/
theorem blest_extrema_attained (x : ℝ) (hx : x ∈ Icc 0 1) :
    ∃ L U : Copula 2, L.chatterjeeXi=x ∧ U.chatterjeeXi=x ∧
      ∀ D : Copula 2, D.chatterjeeXi=x → blestNu L ≤ blestNu D ∧ blestNu D ≤ blestNu U := by
  let a : I := ⟨Real.sqrt x,Real.sqrt_nonneg _,(Real.sqrt_le_one).mpr hx.2⟩
  let C := (Copula.comonotonic 2).mix (Copula.independence 2) a
  have hC : C.chatterjeeXi=x := by
    dsimp [C]
    rw [Copula.chatterjeeXi_mix_independence,Copula.chatterjeeXi_comonotonic,mul_one]
    exact Real.sq_sqrt hx.1
  obtain ⟨L,U,hL,hU,he⟩ := xi_slice_extrema _ attainable_region_compact C
  exact ⟨L,U,hL.trans hC,hU.trans hC,fun D hD => he D (hD.trans hC.symm)⟩

/-- The least xi is attained at every prescribed Blest coefficient. -/
theorem minimal_xi_attained (y : ℝ) (hy : y ∈ Icc (-1) 1) :
    ∃ C : Copula 2, blestNu C=y ∧
      ∀ D : Copula 2, blestNu D=y → C.chatterjeeXi ≤ D.chatterjeeXi := by
  obtain ⟨C,_,hC⟩ := (xi_one_slice y).mpr hy
  obtain ⟨L,hL,hmin⟩ := coefficient_slice_minimum _ attainable_region_compact C
  exact ⟨L,hL.trans hC,fun D hD => hmin D (hD.trans hC.symm)⟩

end ProbabilityTheory.Copula.RankRegion.XiBlest
