import Copula.Rank.Region.XiBlest.Paper.RightBoundary
import Copula.Rank.Region.XiBlest.Support.XiAffineRegion

/-! # Convexity and fixed-coefficient attainment in the xi region

The full xi=1 boundary supplies the witnesses required by the general
mixture proof. The curved extremal boundary is a separate obligation.
-/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiBlest.Support

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

def attainableRegion : Set (ℝ × ℝ) := xiCoefficientRegion blestNu

private theorem top_witness (C : Copula 2) :
    ∃ D : Copula 2, D.chatterjeeXi = 1 ∧ blestNu D = blestNu C :=
  (xi_one_slice _).mpr (blest_mem_Icc C)

/-- All xi values above an attained point occur at the same second coefficient. -/
theorem fixed_coefficient_upward (C : Copula 2) (x : ℝ) (hx : C.chatterjeeXi ≤ x) (hx1 : x ≤ 1) :
    ∃ D : Copula 2, D.chatterjeeXi = x ∧ blestNu D = blestNu C :=
  xi_upward_at_coefficient blestNu blest_mix top_witness C x hx hx1

/-- The full attainable region is convex, without assuming boundary attainment or closure. -/
theorem attainable_region_convex : Convex ℝ attainableRegion :=
  convex_xiCoefficientRegion blestNu blest_mix top_witness

end ProbabilityTheory.Copula.RankRegion.XiBlest
