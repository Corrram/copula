import Copula.Rank.Region.XiBlest.Paper.Optimization
import Copula.Rank.Region.XiBlest.Support.QuadraticMeanInverse

/-! # Constructed clamped extremizers and their unique optimality -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open ProbabilityTheory.Copula.RankRegion.XiBlest.Support

namespace ProbabilityTheory.Copula.RankRegion.XiBlest

noncomputable def extremalCopula (b : ℝ) (hb : 0 ≤ b) : Copula 2 := quadraticBand b hb

/-- The source's normalization parameter, including response thresholds 0 and 1. -/
noncomputable def extremalQ (b : ℝ) (hb : 0 < b) (v : I) : ℝ :=
  -quadraticIntercept b hb.le v / b

theorem extremal_normalization (b : ℝ) (hb : 0 < b) (v : I) :
    ∃! q : ℝ, q ∈ Icc (-1/b) 1 ∧
      (∫ t : I, unitClamp (b*((1-(t : ℝ))^2-q))) = (v : ℝ) := by
  have hi := quadraticIntercept_mem b hb.le v
  have he (q : ℝ) : (∫ t : I, unitClamp (b*((1-(t : ℝ))^2-q))) =
      quadraticMean b (-b*q) := by
    unfold quadraticMean
    congr 1; funext t; congr 1; ring
  refine ⟨extremalQ b hb v, ⟨?_, ?_⟩, ?_⟩
  · unfold extremalQ
    constructor
    · apply (div_le_div_iff_of_pos_right hb).mpr
      linarith [hi.2]
    · apply (div_le_one hb).mpr
      linarith [hi.1]
  · rw [he]
    have hq : -b * extremalQ b hb v = quadraticIntercept b hb.le v := by
      unfold extremalQ; field_simp
    rw [hq, quadraticIntercept_mean]
  · intro q hq
    have ha : -b*q ∈ Icc (-b) (1 : ℝ) := by
      constructor
      · nlinarith [hq.1.2]
      · have h := (div_le_iff₀ hb).mp hq.1.1
        nlinarith
    have hm := hq.2
    rw [he, ← quadraticIntercept_mean b hb.le v] at hm
    have hh := (quadraticMean_strictMonoOn hb.le).injOn ha hi hm
    unfold extremalQ
    apply (eq_div_iff hb.ne').mpr
    linarith

theorem extremalQ_antitone (b : ℝ) (hb : 0 < b) : Antitone (extremalQ b hb) := by
  intro v w hvw
  exact div_le_div_of_nonneg_right (neg_le_neg (quadraticIntercept_monotone b hb.le hvw)) hb.le

theorem extremal_kernel_measurable (b : ℝ) (hb : 0 ≤ b) :
    Measurable (fun p : I × I => quadraticKernel b hb p.2 p.1) := by
  have hm : Measurable (fun p : I × I => quadraticIntercept b hb p.2) :=
    (quadraticIntercept_monotone b hb).measurable.comp measurable_snd
  unfold quadraticKernel unitClamp
  fun_prop

theorem extremal_cdf (b : ℝ) (hb : 0 < b) (u v : I) :
    (extremalCopula b hb.le).cdf ![u,v] =
      ∫ t in Iic u, unitClamp (b*((1-(t : ℝ))^2-extremalQ b hb v)) := by
  rw [extremalCopula, quadraticBand_cdf]
  congr 1; funext t; congr 1
  unfold extremalQ
  field_simp
  ring

theorem extremal_conditionalCDF (b : ℝ) (hb : 0 < b) (v : I) :
    (fun u => (extremalCopula b hb.le).conditionalCDF u v) =ᵐ[volume]
      fun u => unitClamp (b*((1-(u : ℝ))^2-extremalQ b hb v)) := by
  filter_upwards [quadraticBand_conditionalCDF b hb.le v] with u hu
  rw [extremalCopula, hu]
  congr 1
  unfold extremalQ
  field_simp
  ring

theorem extremal_isSI (b : ℝ) (hb : 0 ≤ b) : (extremalCopula b hb).IsSI :=
  quadraticBand_isSI b hb

theorem extremal_support (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * blestNu C - C.chatterjeeXi ≤
      b * blestNu (extremalCopula b hb) - (extremalCopula b hb).chatterjeeXi :=
  clamped_blest_support C (extremalCopula b hb) b (Filter.Eventually.of_forall fun v =>
    ⟨quadraticIntercept b hb v, quadraticBand_conditionalCDF b hb v⟩)

theorem extremal_support_eq_iff (C : Copula 2) (b : ℝ) (hb : 0 ≤ b) :
    b * blestNu C - C.chatterjeeXi =
      b * blestNu (extremalCopula b hb) - (extremalCopula b hb).chatterjeeXi ↔
      C = extremalCopula b hb :=
  clamped_blest_support_eq_iff C (extremalCopula b hb) b (Filter.Eventually.of_forall fun v =>
    ⟨quadraticIntercept b hb v, quadraticBand_conditionalCDF b hb v⟩)

theorem extremal_maximal_blest (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi ≤ (extremalCopula b hb.le).chatterjeeXi) :
    blestNu C ≤ blestNu (extremalCopula b hb.le) := by
  have h := extremal_support C b hb.le
  nlinarith

theorem extremal_maximal_blest_eq_iff (C : Copula 2) (b : ℝ) (hb : 0 < b)
    (hx : C.chatterjeeXi = (extremalCopula b hb.le).chatterjeeXi) :
    blestNu C = blestNu (extremalCopula b hb.le) ↔ C = extremalCopula b hb.le := by
  refine ⟨fun hr => (extremal_support_eq_iff C b hb.le).mp ?_, fun he => he ▸ rfl⟩
  rw [hx, hr]

theorem extremal_zero : extremalCopula 0 (by norm_num) = Copula.independence 2 := by
  apply Copula.cdf_injective
  funext x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, extremalCopula, quadraticBand_cdf, Copula.cdf_independence]
  have he : unitClamp (quadraticIntercept 0 (by norm_num) (x 1)) = (x 1 : ℝ) := by
    simpa [quadraticMean] using quadraticIntercept_mean 0 (by norm_num) (x 1)
  simp only [zero_mul, add_zero, he, integral_const, Measure.real, Measure.restrict_apply_univ, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal (x 0).property.1, smul_eq_mul, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end ProbabilityTheory.Copula.RankRegion.XiBlest
