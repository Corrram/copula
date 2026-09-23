import Copula.Rank.Region.XiBlest.Support.StochasticRigidity
import Copula.Rank.Symmetry

/-! # Conditional moment bounds for stochastically increasing copulas

Concavity supplies an antitone version of every conditional CDF section.
The construction changes only a null set and does not assume a density.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

theorem exists_antitone_version {f : I → ℝ} {s : Set I}
    (hs : ∀ᵐ u : I, u ∈ s) (hf : ∀ u, f u ∈ Icc 0 1)
    (hm : AntitoneOn f s) :
    ∃ g : I → ℝ, Antitone g ∧ (∀ u, g u ∈ Icc 0 1) ∧ f =ᵐ[volume] g := by
  let t (u : I) : Set ℝ := insert 0 (f '' (s ∩ Ici u))
  have ht (u : I) : BddAbove (t u) := by
    refine ⟨1, ?_⟩
    rintro y (rfl | ⟨x, _, rfl⟩)
    · norm_num
    · exact (hf x).2
  have hn (u : I) : (t u).Nonempty := ⟨0, Or.inl rfl⟩
  refine ⟨fun u => sSup (t u), ?_, ?_, ?_⟩
  · intro u v huv
    apply csSup_le_csSup (ht u) (hn v)
    rintro y (rfl | ⟨x, hx, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨x, ⟨hx.1, huv.trans hx.2⟩, rfl⟩
  · intro u
    exact ⟨le_csSup (ht u) (Or.inl rfl), csSup_le (hn u) (by
      rintro y (rfl | ⟨x, _, rfl⟩)
      · norm_num
      · exact (hf x).2)⟩
  · filter_upwards [hs] with u hu
    apply le_antisymm
    · exact le_csSup (ht u) (Or.inr ⟨u, ⟨hu, mem_Ici.mpr le_rfl⟩, rfl⟩)
    · apply csSup_le (hn u)
      rintro y (rfl | ⟨x, hx, rfl⟩)
      · exact (hf u).1
      · exact hm hu hx.1 hx.2

theorem conditionalCDF_antitone_version (C : Copula 2) (hC : C.IsSI) (v : I) :
    ∃ g : I → ℝ, Antitone g ∧ (∀ u, g u ∈ Icc 0 1) ∧
      (fun u => C.conditionalCDF u v) =ᵐ[volume] g := by
  let s : Set I := {u | DifferentiableAt ℝ (Copula.cdfSection C v) (u : ℝ) ∧
    C.conditionalCDF u v = deriv (Copula.cdfSection C v) (u : ℝ)}
  apply exists_antitone_version (s := s)
    ((cdfSection_differentiable_ae C v).and (C.conditionalCDF_eq_deriv v))
    (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩)
  intro u hu w hw huw
  rcases eq_or_lt_of_le huw with rfl | huw
  · rfl
  · change C.conditionalCDF w v ≤ C.conditionalCDF u v
    rw [hu.2, hw.2]
    have hc := cdfSection_concave_of_isSI hC v
    exact (hc.deriv_le_slope u.property w.property huw hw.1).trans
      (hc.slope_le_deriv u.property w.property huw hu.1)

theorem integrable_unit_bounded {f : I → ℝ} (hf : Measurable f)
    (hb : ∀ u, f u ∈ Icc 0 1) : Integrable f := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb u).1] using (hb u).2

/-- A decreasing function in [0,1] has its second moment below its
lower-interval integral at its mean. -/
theorem integral_sq_le_lower_at_mean {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) (v : I) (hv : (∫ u : I, g u) = (v : ℝ)) :
    (∫ u : I, g u ^ 2) ≤ ∫ u in Iic v, g u := by
  classical
  have hi := integrable_unit_bounded hg.measurable hb
  have hsq : Integrable (fun u => g u ^ 2) :=
    integrable_unit_bounded (hg.measurable.pow_const 2)
      (fun u => ⟨sq_nonneg _, by nlinarith [(hb u).1, (hb u).2]⟩)
  let e : I → ℝ := (Iic v).indicator (fun _ => 1)
  have he : Integrable e := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have heq : (fun u => e u * g u) = (Iic v).indicator g := by
    funext u
    by_cases hu : u ∈ Iic v <;> simp [e, hu]
  have hge : Integrable (fun u => e u * g u) := by
    rw [heq]
    exact hi.indicator measurableSet_Iic
  have hm := integral_mono (hsq.sub hge) ((hi.sub he).const_mul (g v)) (fun u => by
    change g u ^ 2 - e u * g u ≤ g v * (g u - e u)
    dsimp [e]
    by_cases hu : u ≤ v
    · simp only [indicator_of_mem (mem_Iic.mpr hu), one_mul]
      nlinarith [hg hu, (hb u).2]
    · simp only [indicator_of_notMem (show u ∉ Iic v from hu), zero_mul, sub_zero]
      nlinarith [hg (le_of_not_ge hu), (hb u).1])
  have heval : (∫ u : I, e u) = (v : ℝ) := by
    simp [e, integral_indicator measurableSet_Iic, integral_const, Measure.real,
      unitInterval.volume_Iic, ENNReal.toReal_ofReal v.property.1]
  have hgev : (∫ u : I, e u * g u) = ∫ u in Iic v, g u := by
    rw [heq, integral_indicator measurableSet_Iic]
  simp only [Pi.sub_apply] at hm
  rw [integral_sub hsq hge, integral_const_mul, integral_sub hi he, hv, heval, hgev] at hm
  linarith

theorem conditionalCDF_sq_le_diagonal (C : Copula 2) (hC : C.IsSI) (v : I) :
    (∫ u : I, C.conditionalCDF u v ^ 2) ≤ C.cdf ![v, v] := by
  obtain ⟨g, hg, hb, he⟩ := conditionalCDF_antitone_version C hC v
  have hm : (∫ u : I, g u) = (v : ℝ) :=
    (integral_congr_ae he).symm.trans (C.integral_conditionalCDF v)
  have hi := integral_sq_le_lower_at_mean hg hb v hm
  rw [C.cdf_eq_integral_conditionalCDF]
  convert hi using 1
  · exact integral_congr_ae (he.fun_comp (fun z : ℝ => z ^ 2))
  · exact integral_congr_ae (ae_restrict_of_ae he)

theorem xi_le_footrule_of_isSI (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ≤ C.spearmanFootrule := by
  have hi := integral_mono C.integrable_integral_conditionalCDF_sq
    C.integrable_diagonal_cdf
    (conditionalCDF_sq_le_diagonal C hC)
  unfold Copula.chatterjeeXi Copula.spearmanFootrule
  linarith

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
