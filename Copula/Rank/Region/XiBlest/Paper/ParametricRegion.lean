import Copula.Rank.Region.XiBlest.Paper.ParameterCoverage

/-! # The full region in terms of the constructed extremal family -/

open ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

theorem extremal_blest_nonneg (b : ℝ) (hb : 0 ≤ b) : 0 ≤ blestNu (extremalCopula b hb) := by
  have h := (extremal_coefficients_monotone (b := 0) (by norm_num) hb hb).2
  rwa [extremal_zero,blest_independence] at h

/-- Exact closed vertical slice at every positive-slope member, with actual witnesses. -/
theorem extremal_slice_iff (b : ℝ) (hb : 0 < b) (y : ℝ) :
    ((extremalCopula b hb.le).chatterjeeXi,y) ∈ attainableRegion ↔
      |y| ≤ blestNu (extremalCopula b hb.le) := by
  let C := extremalCopula b hb.le
  constructor
  · rintro ⟨D,hD,rfl⟩
    have h1 := extremal_maximal_blest D b hb hD.le
    have h2 := extremal_maximal_blest (D.reflect {1}) b hb (by rw [xi_reflect_second]; exact hD.le)
    rw [blest_reflect_second] at h2
    exact abs_le.mpr ⟨by linarith,h1⟩
  · intro hy
    change |y| ≤ blestNu C at hy
    have hc : 0 ≤ blestNu C := extremal_blest_nonneg b hb.le
    rcases eq_or_lt_of_le hc with hz | hp
    · have hy0 : y=0 := by rw [← hz] at hy; exact abs_nonpos_iff.mp hy
      exact ⟨C,rfl,by rw [hy0]; exact hz.symm⟩
    · let a : I := ⟨(y+blestNu C)/(2*blestNu C),
        div_nonneg (by linarith [(abs_le.mp hy).1]) (by positivity),
        (div_le_one (by positivity : 0 < 2*blestNu C)).mpr (by linarith [(abs_le.mp hy).2])⟩
      let D := C.mix (C.reflect {1}) a
      have hD : D.chatterjeeXi ≤ C.chatterjeeXi := by
        have h := C.chatterjeeXi_mix_le (C.reflect {1}) a
        rw [xi_reflect_second] at h
        nlinarith
      have hDy : blestNu D=y := by
        dsimp only [D]
        rw [blest_mix,blest_reflect_second]
        dsimp [a]
        field_simp
        ring
      obtain ⟨E,hE,hEy⟩ := fixed_coefficient_upward D C.chatterjeeXi hD C.chatterjeeXi_le_one
      exact ⟨E,hE,hEy.trans hDy⟩

/-- Every intermediate xi slice has a uniquely attaining upper boundary and its reflection. -/
theorem intermediate_slice_characterization (x : ℝ) (hx : x ∈ Ioo 0 1) :
    ∃ b : ℝ, ∃ hb : 0 < b,
      (extremalCopula b hb.le).chatterjeeXi=x ∧
      (∀ y : ℝ, (x,y) ∈ attainableRegion ↔ |y| ≤ blestNu (extremalCopula b hb.le)) ∧
      (∀ C : Copula 2, C.chatterjeeXi=x →
        (blestNu C=blestNu (extremalCopula b hb.le) ↔ C=extremalCopula b hb.le)) := by
  obtain ⟨b,hb,he⟩ := extremal_parameter_exists x hx
  refine ⟨b,hb,he,?_,?_⟩
  · intro y
    rw [← he]
    exact extremal_slice_iff b hb y
  · intro C hC
    exact extremal_maximal_blest_eq_iff C b hb (hC.trans he.symm)

end ProbabilityTheory.Copula.RankRegion.XiBlest
