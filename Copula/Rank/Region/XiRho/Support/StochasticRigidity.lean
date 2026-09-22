import Copula.Rank.ConditionalDerivative
import Copula.Rank.Region.XiRho.Support.XiReflection
import Copula.Dependence.ConditionalMonotonicity
import Copula.Rank.Region.XiRho.Support.AETotalPositivity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Stochastic monotonicity and maximal Chatterjee xi

The proof applies to arbitrary copulas, including singular ones. Maximal xi
makes the conditional CDF binary almost everywhere. Concavity then forces
each CDF section to equal the comonotonic section.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.XiRho.Support

theorem conditionalCDF_binary_of_xi_one {C : Copula 2} (h : C.chatterjeeXi = 1) :
    ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v = 0 ∨ C.conditionalCDF u v = 1 := by
  have hi : Integrable (fun v : I => (v : ℝ) - ∫ u : I, C.conditionalCDF u v ^ 2) :=
    (Copula.integrable_continuous_unit volume continuous_subtype_val).sub C.integrable_integral_conditionalCDF_sq
  have hn (v : I) : 0 ≤ (v : ℝ) - ∫ u : I, C.conditionalCDF u v ^ 2 :=
    sub_nonneg.mpr (C.integral_conditionalCDF_sq_le v)
  have hz : (∫ v : I, (v : ℝ) - ∫ u : I, C.conditionalCDF u v ^ 2) = 0 := by
    rw [integral_sub (Copula.integrable_continuous_unit volume continuous_subtype_val)
      C.integrable_integral_conditionalCDF_sq, Copula.integral_unit_id]
    unfold Copula.chatterjeeXi at h
    linarith
  have ha := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
  filter_upwards [ha] with v hv
  have hz' : (∫ u : I, C.conditionalCDF u v - C.conditionalCDF u v ^ 2) = 0 := by
    rw [integral_sub (C.integrable_conditionalCDF v) (C.integrable_conditionalCDF_sq v),
      C.integral_conditionalCDF]
    exact hv
  have hn' (u : I) : 0 ≤ C.conditionalCDF u v - C.conditionalCDF u v ^ 2 := by
    nlinarith [C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v]
  have hb := (integral_eq_zero_iff_of_nonneg hn'
    ((C.integrable_conditionalCDF v).sub (C.integrable_conditionalCDF_sq v))).mp hz'
  filter_upwards [hb] with u hu
  simp only [Pi.zero_apply] at hu
  have hp : C.conditionalCDF u v * (C.conditionalCDF u v - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

theorem cdfSection_concave_of_isSI {C : Copula 2} (hC : C.IsSI) (v : I) :
    ConcaveOn ℝ (Icc 0 1) (Copula.cdfSection C v) := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc 0 1)
  intro x y z hx hz hxy hyz
  have hy : y ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hxy.le, hyz.le.trans hz.2⟩
  have h := hC ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ v hxy.le hyz.le
  dsimp [Copula.cdfSection]
  rw [projIcc_of_mem zero_le_one hx, projIcc_of_mem zero_le_one hy,
    projIcc_of_mem zero_le_one hz]
  apply (div_le_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy)).mpr
  dsimp at h
  nlinarith only [h]

theorem cdfSection_differentiable_ae (C : Copula 2) (v : I) :
    ∀ᵐ u : I, DifferentiableAt ℝ (Copula.cdfSection C v) (u : ℝ) := by
  have hm : Monotone (Copula.cdfSection C v) := by
    intro x y hxy
    apply C.monotone_cdf
    intro i
    fin_cases i
    · exact monotone_projIcc zero_le_one hxy
    · exact le_rfl
  have ha := ae_restrict_of_ae (s := Icc (0 : ℝ) 1) hm.ae_differentiableAt
  rw [← unitInterval.measurePreserving_coe.map_eq] at ha
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable ha

theorem cdf_eq_min_of_isSI_binary {C : Copula 2} (hC : C.IsSI) (v : I)
    (hb : ∀ᵐ u : I, C.conditionalCDF u v = 0 ∨ C.conditionalCDF u v = 1) (u : I) :
    C.cdf ![u, v] = min (u : ℝ) (v : ℝ) := by
  apply le_antisymm (le_min (C.cdf_le_coord ![u, v] 0) (C.cdf_le_coord ![u, v] 1))
  by_contra hn
  have hlt : C.cdf ![u, v] < min (u : ℝ) (v : ℝ) := lt_of_not_ge hn
  have hcu : C.cdf ![u, v] < (u : ℝ) := hlt.trans_le (min_le_left _ _)
  have hcv : C.cdf ![u, v] < (v : ℝ) := hlt.trans_le (min_le_right _ _)
  have hu0 : 0 < (u : ℝ) := (C.cdf_nonneg _).trans_lt hcu
  have hu1 : (u : ℝ) < 1 := by
    apply lt_of_le_of_ne u.property.2
    intro he
    have hu : u = 1 := Subtype.ext he
    rw [hu, Copula.cdf_two_one_left] at hcv
    exact (lt_irrefl _ hcv)
  let δ : ℝ := min (1 - (u : ℝ)) ((v : ℝ) - C.cdf ![u, v]) / 2
  have hd : 0 < δ := by dsimp [δ]; positivity
  have hd₁ : 2 * δ ≤ 1 - (u : ℝ) := by
    dsimp [δ]
    linarith [min_le_left (1 - (u : ℝ)) ((v : ℝ) - C.cdf ![u, v])]
  have hd₂ : 2 * δ ≤ (v : ℝ) - C.cdf ![u, v] := by
    dsimp [δ]
    linarith [min_le_right (1 - (u : ℝ)) ((v : ℝ) - C.cdf ![u, v])]
  let w : I := ⟨(u : ℝ) + δ, by constructor <;> linarith [u.property.1]⟩
  have huw : u < w := by change (u : ℝ) < (u : ℝ) + δ; linarith
  have ha : ∀ᵐ x : I, (C.conditionalCDF x v = 0 ∨ C.conditionalCDF x v = 1) ∧
      DifferentiableAt ℝ (Copula.cdfSection C v) (x : ℝ) ∧
      C.conditionalCDF x v = deriv (Copula.cdfSection C v) (x : ℝ) :=
    hb.and ((cdfSection_differentiable_ae C v).and (C.conditionalCDF_eq_deriv v))
  obtain ⟨x, hx, hbin, hdiff, hderiv⟩ := exists_mem_Ioo_of_ae huw ha
  have hux : (u : ℝ) < (x : ℝ) := hx.1
  have hxw : (x : ℝ) < (u : ℝ) + δ := hx.2
  have hx0 : 0 < (x : ℝ) := hu0.trans hux
  have hx1 : (x : ℝ) < 1 := by linarith
  have hlip := C.cdf_sub_le_sum_abs ![x, v] ![u, v]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_self, abs_zero, add_zero,
    abs_of_nonneg (sub_nonneg.mpr hux.le)] at hlip
  have hxcv : C.cdf ![x, v] < (v : ℝ) := by linarith
  have hltu := hC.isLTD u x v hx.1.le
  have hxcx : C.cdf ![x, v] < (x : ℝ) := by
    nlinarith [mul_pos hx0 (sub_pos.mpr hcu)]
  have hc := cdfSection_concave_of_isSI hC v
  have hleft := hc.deriv_le_slope (by norm_num : (0 : ℝ) ∈ Icc 0 1) x.property hx0 hdiff
  have hright := hc.slope_le_deriv x.property (by norm_num : (1 : ℝ) ∈ Icc 0 1) hx1 hdiff
  have hzero : Copula.cdfSection C v 0 = 0 := by
    change Copula.cdfSection C v ((0 : I) : ℝ) = 0
    simp [Copula.cdfSection]
  have hone : Copula.cdfSection C v 1 = (v : ℝ) := by
    change Copula.cdfSection C v ((1 : I) : ℝ) = (v : ℝ)
    simp [Copula.cdfSection]
  have hxval : Copula.cdfSection C v (x : ℝ) = C.cdf ![x, v] := by simp [Copula.cdfSection]
  rw [slope_def_field, hzero, hxval, sub_zero, sub_zero, ← hderiv] at hleft
  rw [slope_def_field, hone, hxval, ← hderiv] at hright
  rcases hbin with h0 | h1
  · rw [h0] at hright
    have hp : 0 < ((v : ℝ) - C.cdf ![x, v]) / (1 - (x : ℝ)) :=
      div_pos (sub_pos.mpr hxcv) (sub_pos.mpr hx1)
    linarith
  · rw [h1] at hleft
    have hp : C.cdf ![x, v] / (x : ℝ) < 1 := (div_lt_one hx0).mpr hxcx
    linarith

/-- In the SI class, maximal xi characterizes comonotonicity. -/
theorem isSI_xi_eq_one_iff (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = 1 ↔ C = Copula.comonotonic 2 := by
  constructor
  · intro hxi
    have hb := conditionalCDF_binary_of_xi_one hxi
    apply Copula.ext_cdf
    intro x
    have ha : (fun v : I => C.cdf ![x 0, v]) =ᵐ[volume] fun v => min (x 0 : ℝ) (v : ℝ) := by
      filter_upwards [hb] with v hv
      exact cdf_eq_min_of_isSI_binary hC v hv (x 0)
    let f : ℝ → ℝ := fun t => C.cdf ![x 0, projIcc 0 1 zero_le_one t]
    let g : ℝ → ℝ := fun t => min (x 0 : ℝ) (projIcc 0 1 zero_le_one t : ℝ)
    have he' : f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] g := by
      rw [← unitInterval.measurePreserving_coe.map_eq]
      apply (ae_map_iff measurable_subtype_coe.aemeasurable
        (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
      simp only [f, g, projIcc_val]
      exact ha
    have he := Measure.eqOn_of_ae_eq he' (show Continuous f by fun_prop).continuousOn
      (show Continuous g by fun_prop).continuousOn
      (show Icc (0 : ℝ) 1 ⊆ closure (interior (Icc (0 : ℝ) 1)) by
        rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])
    have hx : C.cdf ![x 0, x 1] = min (x 0 : ℝ) (x 1 : ℝ) := by
      simpa only [f, g, projIcc_val] using he (x 1).property
    have hvec : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
    simpa only [hvec, Copula.cdf_comonotonic_two] using hx
  · rintro rfl
    exact Copula.chatterjeeXi_comonotonic

/-- In the SD class, maximal xi characterizes countermonotonicity. -/
theorem isSD_xi_eq_one_iff (C : Copula 2) (hC : C.IsSD) :
    C.chatterjeeXi = 1 ↔ C = Copula.countermonotonic := by
  constructor
  · intro hxi
    have he : C.reflect {1} = Copula.comonotonic 2 :=
      (isSI_xi_eq_one_iff _ ((Copula.isSI_reflect_second_iff C).mpr hC)).mp
        (by rw [xi_reflect_second, hxi])
    have hr := congrArg (fun D : Copula 2 => D.reflect {1}) he
    simpa only [Copula.reflect_reflect, Copula.reflect_comonotonic_eq_countermonotonic] using hr
  · rintro rfl
    exact Copula.chatterjeeXi_countermonotonic

end ProbabilityTheory.Copula.RankRegion.XiRho.Support
