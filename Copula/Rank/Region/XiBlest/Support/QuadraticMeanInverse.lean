import Copula.Rank.Region.XiBlest.Support.QuadraticBand
import Copula.UnitInterval

/-! # Inverting the clamped mean on its effective parameter interval -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem quadraticMean_mem (b a : ℝ) : quadraticMean b a ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun u => (unitClamp_mem _).1)
  · have hi : Integrable (fun u : I => unitClamp (a+b*(1-(u : ℝ))^2)) :=
      Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
    simpa only [quadraticMean, integral_const, probReal_univ, one_smul] using integral_mono hi (integrable_const (1 : ℝ)) (fun u => (unitClamp_mem _).2)

/-- Strictness holds on the entire effective intercept range, including its endpoints. -/
theorem quadraticMean_strictMonoOn {b : ℝ} (hb : 0 ≤ b) :
    StrictMonoOn (quadraticMean b) (Icc (-b) (1 : ℝ)) := by
  intro a ha c hc hac
  apply lt_of_le_of_ne (quadraticMean_monotone b hac.le)
  intro he
  have hi (r : ℝ) : Integrable (fun u : I => unitClamp (r+b*(1-(u : ℝ))^2)) :=
    Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
  have hae := (integral_eq_iff_of_ae_le (hi a) (hi c)
    (Filter.Eventually.of_forall fun u => min_le_min le_rfl
      (max_le_max le_rfl (add_le_add_left hac.le _)))).mp he
  have hf := Measure.eq_of_ae_eq hae
    (show Continuous (fun u : I => unitClamp (a+b*(1-(u : ℝ))^2)) by unfold unitClamp; fun_prop)
    (show Continuous (fun u : I => unitClamp (c+b*(1-(u : ℝ))^2)) by unfold unitClamp; fun_prop)
  have hden : 0 < b+1 := by linarith
  let w : ℝ := (1-a)/(b+1)
  have hw0 : 0 ≤ w := div_nonneg (by linarith [ha.2]) hden.le
  have hw1 : w ≤ 1 := (div_le_one hden).mpr (by linarith [ha.1])
  have hs0 := Real.sqrt_nonneg w
  have hs1 : Real.sqrt w ≤ 1 := (Real.sqrt_le_one).mpr hw1
  let u : I := ⟨1-Real.sqrt w, by constructor <;> linarith⟩
  let z : ℝ := (a+b)/(b+1)
  have hz0 : 0 ≤ z := div_nonneg (by linarith [ha.1]) hden.le
  have hz1 : z < 1 := (div_lt_one hden).mpr (by linarith [hc.2])
  have heq : a+b*(1-(u : ℝ))^2 = z := by
    have hs := Real.sq_sqrt hw0
    dsimp only [u]
    ring_nf at hs ⊢
    dsimp [w, z] at hs ⊢
    field_simp at hs ⊢
    nlinarith
  have hh := congrFun hf u
  rw [heq] at hh
  have hzcl : unitClamp z = z := by
    unfold unitClamp; rw [max_eq_right hz0, min_eq_right hz1.le]
  rw [hzcl] at hh
  have hlt : z < unitClamp (c+b*(1-(u : ℝ))^2) := by
    unfold unitClamp
    apply lt_min hz1
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  linarith

theorem quadraticIntercept_mem (b : ℝ) (hb : 0 ≤ b) (v : I) :
    quadraticIntercept b hb v ∈ Icc (-b) (1 : ℝ) := by
  unfold quadraticIntercept
  split_ifs
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨by linarith, le_rfl⟩
  · exact (exists_quadratic_intercept b hb v).choose_spec.1

noncomputable def quadraticMeanUnit (b a : ℝ) : I := ⟨quadraticMean b a, quadraticMean_mem b a⟩

@[fun_prop] theorem continuous_quadraticMeanUnit (b : ℝ) : Continuous (quadraticMeanUnit b) :=
  (continuous_quadraticMean b).subtype_mk _

theorem quadraticIntercept_quadraticMean (b : ℝ) (hb : 0 ≤ b) {a : ℝ}
    (ha : a ∈ Icc (-b) (1 : ℝ)) :
    quadraticIntercept b hb (quadraticMeanUnit b a) = a := by
  apply (quadraticMean_strictMonoOn hb).injOn (quadraticIntercept_mem _ _ _) ha
  exact quadraticIntercept_mean b hb (quadraticMeanUnit b a)

theorem quadraticMean_le_iff (b : ℝ) (hb : 0 ≤ b) {a : ℝ}
    (ha : a ∈ Icc (-b) (1 : ℝ)) (v : I) :
    quadraticMean b a ≤ (v : ℝ) ↔ a ≤ quadraticIntercept b hb v := by
  rw [← quadraticIntercept_mean b hb v]
  exact (quadraticMean_strictMonoOn hb).le_iff_le ha (quadraticIntercept_mem _ _ _)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
