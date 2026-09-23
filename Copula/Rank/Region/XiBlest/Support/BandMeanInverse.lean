import Copula.Rank.Region.XiBlest.Support.DiagonalBand
import Copula.UnitInterval

/-! # Inverting the clamped mean on its effective parameter interval -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem clampedMean_mem (b a : ℝ) : clampedMean b a ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun u => (unitClamp_mem _).1)
  · have hi : Integrable (fun u : I => unitClamp (a-b*(u : ℝ))) :=
      Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
    simpa only [clampedMean, integral_const, probReal_univ, one_smul] using integral_mono hi (integrable_const (1 : ℝ)) (fun u => (unitClamp_mem _).2)

/-- Strictness holds on the entire effective intercept range, including its endpoints. -/
theorem clampedMean_strictMonoOn {b : ℝ} (hb : 0 ≤ b) :
    StrictMonoOn (clampedMean b) (Icc (0 : ℝ) (b+1)) := by
  intro a ha c hc hac
  apply lt_of_le_of_ne (clampedMean_monotone b hac.le)
  intro he
  have hi (r : ℝ) : Integrable (fun u : I => unitClamp (r-b*(u : ℝ))) :=
    Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
  have hae := (integral_eq_iff_of_ae_le (hi a) (hi c)
    (Filter.Eventually.of_forall fun u => min_le_min le_rfl
      (max_le_max le_rfl (sub_le_sub_right hac.le _)))).mp he
  have hf := Measure.eq_of_ae_eq hae
    (show Continuous (fun u : I => unitClamp (a-b*(u : ℝ))) by unfold unitClamp; fun_prop)
    (show Continuous (fun u : I => unitClamp (c-b*(u : ℝ))) by unfold unitClamp; fun_prop)
  have hden : 0 < b+1 := by linarith
  let u : I := ⟨a/(b+1), div_nonneg ha.1 hden.le,
    (div_le_one hden).mpr ha.2⟩
  have hu : (u : ℝ) < 1 := (div_lt_one hden).mpr (hac.trans_le hc.2)
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have heq : a-b*(u : ℝ) = (u : ℝ) := by dsimp [u]; field_simp; ring
  have hh := congrFun hf u
  rw [heq] at hh
  have hucl : unitClamp (u : ℝ) = (u : ℝ) := by
    unfold unitClamp; rw [max_eq_right hu0, min_eq_right hu.le]
  rw [hucl] at hh
  have hlt : (u : ℝ) < unitClamp (c-b*(u : ℝ)) := by
    unfold unitClamp
    apply lt_min hu
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  linarith

theorem bandIntercept_mem (b : ℝ) (hb : 0 ≤ b) (v : I) :
    bandIntercept b hb v ∈ Icc (0 : ℝ) (b+1) := by
  unfold bandIntercept
  split_ifs
  · exact ⟨le_rfl, by linarith⟩
  · exact ⟨by linarith, le_rfl⟩
  · exact (exists_clamped_intercept b hb v).choose_spec.1

noncomputable def clampedMeanUnit (b a : ℝ) : I := ⟨clampedMean b a, clampedMean_mem b a⟩

@[fun_prop] theorem continuous_clampedMeanUnit (b : ℝ) : Continuous (clampedMeanUnit b) :=
  (continuous_clampedMean b).subtype_mk _

theorem bandIntercept_clampedMean (b : ℝ) (hb : 0 ≤ b) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (b+1)) :
    bandIntercept b hb (clampedMeanUnit b a) = a := by
  apply (clampedMean_strictMonoOn hb).injOn (bandIntercept_mem _ _ _) ha
  exact bandIntercept_mean b hb (clampedMeanUnit b a)

theorem clampedMean_le_iff (b : ℝ) (hb : 0 ≤ b) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) (b+1)) (v : I) :
    clampedMean b a ≤ (v : ℝ) ↔ a ≤ bandIntercept b hb v := by
  rw [← bandIntercept_mean b hb v]
  exact (clampedMean_strictMonoOn hb).le_iff_le ha (bandIntercept_mem _ _ _)

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
