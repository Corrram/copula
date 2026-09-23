import Copula.Rank.Region.XiBlest.Paper.ParameterCoverage
import Copula.Rank.Region.XiBlest.Support.QuadraticBandInjective

/-! # Strict coefficient monotonicity and uniqueness of every interior parameter -/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem extremal_coefficients_strictMono {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hbd : b < d) :
    (extremalCopula b hb).chatterjeeXi < (extremalCopula d hd).chatterjeeXi ∧
      blestNu (extremalCopula b hb) < blestNu (extremalCopula d hd) := by
  have hm := extremal_coefficients_monotone hb hd hbd.le
  have h1 := extremal_support (extremalCopula d hd) b hb
  have h2 := extremal_support (extremalCopula b hb) d hd
  have hne : extremalCopula d hd ≠ extremalCopula b hb := by
    intro he
    exact hbd.ne (quadraticBand_injective d b hd hb he).symm
  have heq := extremal_support_eq_iff (extremalCopula d hd) b hb
  have hn : blestNu (extremalCopula b hb) < blestNu (extremalCopula d hd) := by
    apply lt_of_le_of_ne hm.2
    intro he
    have hx : (extremalCopula b hb).chatterjeeXi=(extremalCopula d hd).chatterjeeXi := by nlinarith
    apply hne
    apply heq.mp
    rw [← he,hx]
  refine ⟨?_,hn⟩
  apply lt_of_le_of_ne hm.1
  intro hx
  rcases eq_or_lt_of_le hb with hz | hbpos
  · have hz' : b=0 := hz.symm
    apply hne
    apply heq.mp
    nlinarith
  · nlinarith

theorem extremal_finite_xi (b : ℝ) (hb : 0 ≤ b) : (extremalCopula b hb).chatterjeeXi < 1 := by
  have h := (extremal_coefficients_strictMono hb (show 0 ≤ b+1 by linarith) (show b < b+1 by linarith)).1
  exact h.trans_le (extremalCopula (b+1) (by linarith)).chatterjeeXi_le_one

theorem extremal_positive_xi (b : ℝ) (hb : 0 < b) : 0 < (extremalCopula b hb.le).chatterjeeXi := by
  have h := (extremal_coefficients_strictMono (b := 0) (by norm_num) hb.le hb).1
  rwa [extremal_zero,Copula.chatterjeeXi_independence] at h

/-- The source parameter is unique for every xi strictly between zero and one. -/
theorem extremal_parameter_unique (x : ℝ) (hx : x ∈ Ioo 0 1) :
    ∃! b : Ioi (0 : ℝ), (extremalCopula b b.property.le).chatterjeeXi=x := by
  obtain ⟨b,hb,he⟩ := extremal_parameter_exists x hx
  refine ⟨⟨b,hb⟩,he,?_⟩
  intro d hd
  apply Subtype.ext
  apply le_antisymm
  · by_contra hn
    have hh := (extremal_coefficients_strictMono hb.le d.property.le (lt_of_not_ge hn)).1
    rw [he,hd] at hh
    exact (lt_irrefl x) hh
  · by_contra hn
    have hh := (extremal_coefficients_strictMono d.property.le hb.le (lt_of_not_ge hn)).1
    rw [he,hd] at hh
    exact (lt_irrefl x) hh

end ProbabilityTheory.Copula.RankRegion.XiBlest
