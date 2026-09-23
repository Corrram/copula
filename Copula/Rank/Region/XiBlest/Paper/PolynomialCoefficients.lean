import Copula.Rank.Region.XiBlest.Paper.ParametricRegion
import Copula.Rank.Region.XiBlest.Support.QuadraticBandPolynomial

/-! # The polynomial coefficient branch and the exact maximum gap -/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem extremal_blest_noise (b : ℝ) (hb : 0 ≤ b) :
    blestNu (extremalCopula b hb) =
      12*(∫ p : I × I, squarePotential p.2*noiseMoment 1 (b*squareDelta p))-2 := by
  rw [blest_conditional_formula]
  have he (v : I) : (∫ u : I, (1-(u : ℝ))^2*(extremalCopula b hb).conditionalCDF u v) =
      ∫ u : I, squarePotential u*quadraticKernel b hb v u := by
    apply integral_congr_ae
    filter_upwards [quadraticBand_conditionalCDF b hb v] with u hu
    change (1-(u : ℝ))^2*(quadraticBand b hb).conditionalCDF u v = _
    rw [hu]
    rfl
  have hm := quadratic_kernel_moment_pair b hb squarePotential continuous_squarePotential 1
  simp only [pow_one] at hm
  simp_rw [he]
  rw [hm]

theorem extremal_coefficients_polynomial (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (extremalCopula b hb.1).chatterjeeXi=8*b^2*(7-3*b)/105 ∧
      blestNu (extremalCopula b hb.1)=4*b*(28-9*b)/105 := by
  refine ⟨quadraticBand_xi_polynomial b hb,?_⟩
  rw [extremal_blest_noise,integral_noise_weighted b hb]
  ring

theorem extremal_one_coefficients :
    (extremalCopula 1 (by norm_num)).chatterjeeXi=32/105 ∧
      blestNu (extremalCopula 1 (by norm_num))=76/105 := by
  have h := extremal_coefficients_polynomial 1 (by norm_num)
  norm_num at h ⊢
  exact h

theorem maximal_signed_gap (C : Copula 2) : blestNu C-C.chatterjeeXi ≤ 44/105 := by
  have h := extremal_support C 1 (by norm_num)
  rw [extremal_one_coefficients.1,extremal_one_coefficients.2] at h
  norm_num at h ⊢
  exact h

theorem maximal_signed_gap_eq_iff (C : Copula 2) :
    blestNu C-C.chatterjeeXi=44/105 ↔ C=extremalCopula 1 (by norm_num) := by
  have h := extremal_support_eq_iff C 1 (by norm_num)
  rw [extremal_one_coefficients.1,extremal_one_coefficients.2] at h
  norm_num at h ⊢
  exact h

theorem maximal_absolute_gap (C : Copula 2) : |blestNu C|-C.chatterjeeXi ≤ 44/105 := by
  have hp := maximal_signed_gap C
  have hn := maximal_signed_gap (C.reflect {1})
  rw [blest_reflect_second,xi_reflect_second] at hn
  rcases le_total 0 (blestNu C) with h | h
  · rwa [abs_of_nonneg h]
  · rwa [abs_of_nonpos h]

theorem maximal_absolute_gap_eq_iff (C : Copula 2) :
    |blestNu C|-C.chatterjeeXi=44/105 ↔
      C=extremalCopula 1 (by norm_num) ∨ C=(extremalCopula 1 (by norm_num)).reflect {1} := by
  constructor
  · intro he
    rcases le_total 0 (blestNu C) with h | h
    · rw [abs_of_nonneg h] at he
      exact Or.inl ((maximal_signed_gap_eq_iff C).mp he)
    · rw [abs_of_nonpos h] at he
      have hh : blestNu (C.reflect {1})-(C.reflect {1}).chatterjeeXi=44/105 := by
        rwa [blest_reflect_second,xi_reflect_second]
      have hc := (maximal_signed_gap_eq_iff (C.reflect {1})).mp hh
      apply Or.inr
      simpa only [Copula.reflect_reflect] using congrArg (fun D : Copula 2 => D.reflect {1}) hc
  · rintro (rfl | rfl)
    · rw [extremal_one_coefficients.1,extremal_one_coefficients.2]
      norm_num
    · rw [blest_reflect_second,xi_reflect_second,extremal_one_coefficients.1,extremal_one_coefficients.2]
      norm_num

end ProbabilityTheory.Copula.RankRegion.XiBlest
