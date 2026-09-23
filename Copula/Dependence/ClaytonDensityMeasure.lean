/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.ClaytonDensityFormula
import Copula.Dependence.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open ProbabilityTheory Real MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula


private noncomputable def claytonBaseReal (θ u v : ℝ) : ℝ :=
  u ^ (-θ) + v ^ (-θ) - 1

private theorem claytonBaseReal_pos (θ u v : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    0 < claytonBaseReal θ u v := by
  have hx : 1 ≤ u ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
  have hy : 1 ≤ v ^ (-θ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
  dsimp [claytonBaseReal]
  linarith

/-- The analytic expression below is the CDF of the actual positive-Clayton
copula on strictly positive unit coordinates. -/
theorem clayton_cdf_positive_eq_analytic
    (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    (clayton 2 θ hθ).cdf ![u, v] =
      (claytonBaseReal θ (u : ℝ) (v : ℝ)) ^ (-1 / θ) := by
  simpa only [claytonBaseReal] using cdf_clayton_two_pos θ hθ u v hu hv

/-- The actual positive-Clayton CDF formula has the expected first partial
derivative on the positive unit square. -/
theorem clayton_cdf_formula_hasDerivAt_first
    (θ u v : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    HasDerivAt (fun x : ℝ => (claytonBaseReal θ x v) ^ (-1 / θ))
      (u ^ (-θ - 1) * (claytonBaseReal θ u v) ^ (-1 / θ - 1)) u := by
  have hb := claytonBaseReal_pos θ u v hθ hu hv hu1 hv1
  have huPow : HasDerivAt (fun x : ℝ => x ^ (-θ))
      ((-θ) * u ^ (-θ - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hbase : HasDerivAt (fun x : ℝ => claytonBaseReal θ x v)
      ((-θ) * u ^ (-θ - 1)) u := by
    convert (huPow.add_const ((v ^ (-θ)) - 1)) using 1
    funext x
    simp only [claytonBaseReal]
    ring
  have hp := hbase.rpow_const (Or.inl hb.ne') (p := -1 / θ)
  convert hp using 1
  field_simp [hθ.ne']

/-- The mixed derivative of the positive-Clayton CDF formula is its standard
density formula on the positive unit square. -/
theorem clayton_cdf_formula_hasDerivAt_second
    (θ u v : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    HasDerivAt (fun y : ℝ =>
      u ^ (-θ - 1) * (claytonBaseReal θ u y) ^ (-1 / θ - 1))
      ((1 + θ) * u ^ (-θ - 1) * v ^ (-θ - 1) *
        (claytonBaseReal θ u v) ^ (-2 - 1 / θ)) v := by
  have hb := claytonBaseReal_pos θ u v hθ hu hv hu1 hv1
  have hvPow : HasDerivAt (fun y : ℝ => y ^ (-θ))
      ((-θ) * v ^ (-θ - 1)) v :=
    Real.hasDerivAt_rpow_const (Or.inl hv.ne')
  have hbase : HasDerivAt (fun y : ℝ => claytonBaseReal θ u y)
      ((-θ) * v ^ (-θ - 1)) v := by
    convert (hvPow.const_add (u ^ (-θ) - 1)) using 1
    funext y
    simp only [claytonBaseReal]
    ring
  have hp := hbase.rpow_const (Or.inl hb.ne') (p := -1 / θ - 1)
  have hd := hp.const_mul (u ^ (-θ - 1))
  convert hd using 1
  field_simp [hθ.ne']
  ring_nf

/-- The analytic mixed derivative is exactly the explicit Clayton
density formula at every strictly positive coordinate. -/
theorem clayton_mixed_derivative_eq_densityFormula
    (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    deriv (fun y : ℝ =>
      (u : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (u : ℝ) y) ^ (-1 / θ - 1)) (v : ℝ) =
      claytonDensityFormula θ ![u, v] := by
  have hd := (clayton_cdf_formula_hasDerivAt_second θ u v hθ hu hv
    u.property.2 v.property.2).deriv
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    norm_num at hu
  have hv0 : v ≠ 0 := by
    intro h
    subst v
    norm_num at hv
  calc
    _ = (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1) *
      (claytonBaseReal θ (u : ℝ) (v : ℝ)) ^ (-2 - 1 / θ) := hd
    _ = claytonDensityFormula θ ![u, v] := by
      change (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (u : ℝ) (v : ℝ)) ^ (-2 - 1 / θ) =
        (1 + θ) * (u : ℝ) ^ (-θ - 1) * (v : ℝ) ^ (-θ - 1) *
          (if u = 0 ∨ v = 0 then 0 else
            ((u : ℝ) ^ (-θ) + (v : ℝ) ^ (-θ) - 1) ^ (-2 - 1 / θ))
      simp [claytonBaseReal, hu0, hv0]

/-- On a positive rectangle, integrating the mixed derivative in the second
coordinate recovers the first-derivative increment. -/
theorem clayton_density_formula_integral_second
    (θ u a b : ℝ) (hθ : 0 < θ)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ y in a..b,
      (1 + θ) * u ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ u y) ^ (-2 - 1 / θ)) =
      u ^ (-θ - 1) * (claytonBaseReal θ u b) ^ (-1 / θ - 1) -
        u ^ (-θ - 1) * (claytonBaseReal θ u a) ^ (-1 / θ - 1) := by
  let f : ℝ → ℝ := fun y =>
    u ^ (-θ - 1) * (claytonBaseReal θ u y) ^ (-1 / θ - 1)
  let g : ℝ → ℝ := fun y =>
    (1 + θ) * u ^ (-θ - 1) * y ^ (-θ - 1) *
      (claytonBaseReal θ u y) ^ (-2 - 1 / θ)
  have hderiv (y : ℝ) (hy : y ∈ Set.uIcc a b) : HasDerivAt f (g y) y := by
    have hy' : y ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hy
    exact clayton_cdf_formula_hasDerivAt_second θ u y hθ hu
      (ha.trans_le hy'.1) hu1 (hy'.2.trans hb1)
  have hpow : ContinuousOn (fun y : ℝ => y ^ (-θ)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun y hy => Or.inl
      (ne_of_gt (ha.trans_le hy.1)))
  have hbase : ContinuousOn (fun y : ℝ => claytonBaseReal θ u y)
      (Set.Icc a b) := by
    have hc : ContinuousOn (fun _ : ℝ => u ^ (-θ)) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := continuousOn_const
    convert (hc.add hpow).sub h1 using 1
    funext y
    simp [claytonBaseReal]
  have hpow2 : ContinuousOn (fun y : ℝ => y ^ (-θ - 1)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun y hy => Or.inl
      (ne_of_gt (ha.trans_le hy.1)))
  have hpow3 : ContinuousOn (fun y : ℝ =>
      (claytonBaseReal θ u y) ^ (-2 - 1 / θ)) (Set.Icc a b) :=
    hbase.rpow_const (fun y hy => Or.inl
      ((claytonBaseReal_pos θ u y hθ hu (ha.trans_le hy.1)
        hu1 (hy.2.trans hb1)).ne'))
  have hg : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact (continuousOn_const.mul hpow2).mul hpow3
  have hg' : ContinuousOn g (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hg'.intervalIntegrable

/-- Integrating the first partial derivative over a positive interval
recovers the Clayton CDF formula increment. -/
theorem clayton_cdf_formula_integral_first
    (θ v a b : ℝ) (hθ : 0 < θ)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    (∫ x in a..b,
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1)) =
      (claytonBaseReal θ b v) ^ (-1 / θ) -
        (claytonBaseReal θ a v) ^ (-1 / θ) := by
  let f : ℝ → ℝ := fun x =>
    (claytonBaseReal θ x v) ^ (-1 / θ)
  let g : ℝ → ℝ := fun x =>
    x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1)
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc a b) : HasDerivAt f (g x) x := by
    have hx' : x ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hx
    exact clayton_cdf_formula_hasDerivAt_first θ x v hθ
      (ha.trans_le hx'.1) hv (hx'.2.trans hb1) hv1
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-θ)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hbase : ContinuousOn (fun x : ℝ => claytonBaseReal θ x v)
      (Set.Icc a b) := by
    have hc : ContinuousOn (fun _ : ℝ => v ^ (-θ)) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := continuousOn_const
    convert (hpow.add hc).sub h1 using 1
    funext x
    simp [claytonBaseReal]
  have hpow2 : ContinuousOn (fun x : ℝ => x ^ (-θ - 1)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hpow3 : ContinuousOn (fun x : ℝ =>
      (claytonBaseReal θ x v) ^ (-1 / θ - 1)) (Set.Icc a b) :=
    hbase.rpow_const (fun x hx => Or.inl
      ((claytonBaseReal_pos θ x v hθ (ha.trans_le hx.1) hv
        (hx.2.trans hb1) hv1).ne'))
  have hg : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact hpow2.mul hpow3
  have hg' : ContinuousOn g (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hg'.intervalIntegrable

private theorem clayton_first_derivative_intervalIntegrable
    (θ v a b : ℝ) (hθ : 0 < θ)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    IntervalIntegrable (fun x : ℝ =>
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1))
      volume a b := by
  have hpow : ContinuousOn (fun x : ℝ => x ^ (-θ)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hbase : ContinuousOn (fun x : ℝ => claytonBaseReal θ x v)
      (Set.Icc a b) := by
    have hc : ContinuousOn (fun _ : ℝ => v ^ (-θ)) (Set.Icc a b) := continuousOn_const
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := continuousOn_const
    convert (hpow.add hc).sub h1 using 1
    funext x
    simp [claytonBaseReal]
  have hpow2 : ContinuousOn (fun x : ℝ => x ^ (-θ - 1)) (Set.Icc a b) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl
      (ne_of_gt (ha.trans_le hx.1)))
  have hpow3 : ContinuousOn (fun x : ℝ =>
      (claytonBaseReal θ x v) ^ (-1 / θ - 1)) (Set.Icc a b) :=
    hbase.rpow_const (fun x hx => Or.inl
      ((claytonBaseReal_pos θ x v hθ (ha.trans_le hx.1) hv
        (hx.2.trans hb1) hv1).ne'))
  have hg : ContinuousOn (fun x : ℝ =>
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1))
      (Set.Icc a b) := hpow2.mul hpow3
  have hg' : ContinuousOn (fun x : ℝ =>
      x ^ (-θ - 1) * (claytonBaseReal θ x v) ^ (-1 / θ - 1))
      (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hg
  exact hg'.intervalIntegrable (μ := (volume : MeasureTheory.Measure ℝ))

private theorem integral_fin_two_unit (f : (Fin 2 → I) → ℝ)
    (hf : Integrable f) :
    (∫ x, f x) = ∫ u : I, ∫ v : I, f ![u, v] := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  have hp : MeasurePreserving e (volume : Measure (Fin 2 → I))
      (volume : Measure (I × I)) := volume_preserving_finTwoArrow I
  have hi : Integrable (fun p : I × I => f (e.symm p)) :=
    hp.symm.integrable_comp_of_integrable hf
  have h := hp.integral_comp' (fun p : I × I => f (e.symm p))
  rw [Measure.volume_eq_prod I I] at hi h
  rw [integral_prod _ hi] at h
  have heta (x : Fin 2 → I) : ![x 0, x 1] = x := by
    ext i
    fin_cases i <;> simp
  simpa [e, MeasurableEquiv.finTwoArrow, heta] using h

private theorem integral_unit_Ioc_real (f : ℝ → ℝ) (a b : I) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, f (t : ℝ)) =
      ∫ t in (a : ℝ)..(b : ℝ), f t := by
  classical
  rw [← integral_indicator measurableSet_Ioc]
  have he : (Set.Ioc a b).indicator (fun t : I => f (t : ℝ)) =
      fun t : I => (Set.Ioc (a : ℝ) (b : ℝ)).indicator f (t : ℝ) := rfl
  rw [he, integral_unitInterval, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hab]
  have hs : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioc (a : ℝ) (b : ℝ) =
      Set.Ioc (a : ℝ) (b : ℝ) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨⟨lt_of_le_of_lt a.property.1 h.1,
        h.2.trans b.property.2⟩, h⟩
  rw [hs]

private theorem integral_cube_Ioc_two (f : (Fin 2 → I) → ℝ)
    (a b c d : I)
    (hf : IntegrableOn f
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)))) :
    (∫ x in Set.pi Set.univ
      (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)), f x) =
      ∫ u in Set.Ioc a b, ∫ v in Set.Ioc c d, f ![u, v] := by
  classical
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))
  have hs : MeasurableSet s := by
    dsimp [s]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => by fin_cases i <;> simp)
  change (∫ x in s, f x) = _
  rw [← integral_indicator hs, integral_fin_two_unit _ (hf.integrable_indicator hs)]
  have he (u v : I) : s.indicator f ![u, v] =
      (Set.Ioc a b).indicator
        (fun u : I => (Set.Ioc c d).indicator (fun v : I => f ![u, v]) v) u := by
    have hmem : (![u, v] ∈ s) ↔ u ∈ Set.Ioc a b ∧ v ∈ Set.Ioc c d := by
      simp [s, Set.mem_pi, Fin.forall_fin_two]
    by_cases hu : u ∈ Set.Ioc a b <;> by_cases hv : v ∈ Set.Ioc c d
    all_goals simp [Set.indicator, hmem, hu, hv]
  change (∫ u : I, ∫ v : I, s.indicator f ![u, v]) = _
  simp_rw [he]
  simp_rw [integral_indicator₂]
  rw [integral_indicator measurableSet_Ioc]
  simp_rw [integral_indicator measurableSet_Ioc]

private theorem integral_cube_Ioc_two_real (F : ℝ → ℝ → ℝ)
    (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d)
    (hF : IntegrableOn
      (fun x : Fin 2 → I => F (x 0 : ℝ) (x 1 : ℝ))
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)))) :
    (∫ x in Set.pi Set.univ
      (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)),
      F (x 0 : ℝ) (x 1 : ℝ)) =
      ∫ u in (a : ℝ)..(b : ℝ), ∫ v in (c : ℝ)..(d : ℝ), F u v := by
  calc
    _ = ∫ u in Set.Ioc a b, ∫ v in Set.Ioc c d,
        F (u : ℝ) (v : ℝ) := integral_cube_Ioc_two _ a b c d hF
    _ = ∫ u in Set.Ioc a b, ∫ v in (c : ℝ)..(d : ℝ),
        F (u : ℝ) v := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u _
      exact integral_unit_Ioc_real (fun v => F (u : ℝ) v) c d hcd
    _ = _ := integral_unit_Ioc_real
      (fun u => ∫ v in (c : ℝ)..(d : ℝ), F u v) a b hab

private theorem clayton_density_real_continuousOn_rectangle
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hc : 0 < (c : ℝ)) :
    ContinuousOn (fun x : Fin 2 → I =>
      (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ))
      (Set.pi Set.univ (fun i : Fin 2 => Set.Icc (![a, c] i) (![b, d] i))) := by
  let t : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Icc (![a, c] i) (![b, d] i))
  have hpos0 (x : Fin 2 → I) (hx : x ∈ t) : 0 < (x 0 : ℝ) := by
    have hx0 := (Set.mem_pi.mp hx) 0 (by simp)
    have hx0' : a ≤ x 0 := by simpa using hx0.1
    exact ha.trans_le hx0'
  have hpos1 (x : Fin 2 → I) (hx : x ∈ t) : 0 < (x 1 : ℝ) := by
    have hx1 := (Set.mem_pi.mp hx) 1 (by simp)
    have hx1' : c ≤ x 1 := by simpa using hx1.1
    exact hc.trans_le hx1'
  have hcoord0 : Continuous (fun x : Fin 2 → I => (x 0 : ℝ)) := by fun_prop
  have hcoord1 : Continuous (fun x : Fin 2 → I => (x 1 : ℝ)) := by fun_prop
  have hpow0 : ContinuousOn (fun x : Fin 2 → I => (x 0 : ℝ) ^ (-θ)) t :=
    hcoord0.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos0 x hx)))
  have hpow1 : ContinuousOn (fun x : Fin 2 → I => (x 1 : ℝ) ^ (-θ)) t :=
    hcoord1.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos1 x hx)))
  have hbase : ContinuousOn (fun x : Fin 2 → I =>
      claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) t := by
    have hconst : ContinuousOn (fun _ : Fin 2 → I => (1 : ℝ)) t :=
      continuousOn_const
    convert (hpow0.add hpow1).sub hconst using 1
    funext x
    simp [claytonBaseReal]
  have hpow0' : ContinuousOn (fun x : Fin 2 → I =>
      (x 0 : ℝ) ^ (-θ - 1)) t :=
    hcoord0.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos0 x hx)))
  have hpow1' : ContinuousOn (fun x : Fin 2 → I =>
      (x 1 : ℝ) ^ (-θ - 1)) t :=
    hcoord1.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos1 x hx)))
  have hbasepow : ContinuousOn (fun x : Fin 2 → I =>
      (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ)) t :=
    hbase.rpow_const (fun x hx => Or.inl
      ((claytonBaseReal_pos θ (x 0 : ℝ) (x 1 : ℝ) hθ
        (hpos0 x hx) (hpos1 x hx) (x 0).property.2 (x 1).property.2).ne'))
  change ContinuousOn _ t
  exact ((continuousOn_const.mul hpow0').mul hpow1').mul hbasepow

private theorem clayton_density_real_integrableOn_positive_rectangle
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hc : 0 < (c : ℝ)) :
    IntegrableOn (fun x : Fin 2 → I =>
      (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ))
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) := by
  let t : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Icc (![a, c] i) (![b, d] i))
  have ht : IsCompact t := by
    dsimp [t]
    apply isCompact_univ_pi
    intro i
    fin_cases i <;> exact isCompact_Icc
  have hi : IntegrableOn (fun x : Fin 2 → I =>
      (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ))
      t := (clayton_density_real_continuousOn_rectangle θ hθ a b c d ha hc)
        |>.integrableOn_compact (μ := (volume : Measure (Fin 2 → I))) ht
  apply hi.mono_set
  intro x hx
  apply Set.mem_pi.mpr
  intro i hi'
  exact Set.Ioc_subset_Icc_self ((Set.mem_pi.mp hx) i hi')

/-- The analytic Clayton density integrates to the exact CDF rectangle
increment on every rectangle bounded away from both axes. -/
theorem clayton_density_formula_positive_rectangle
    (θ a b c d : ℝ) (hθ : 0 < θ)
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hcd : c ≤ d) (hd1 : d ≤ 1) :
    (∫ x in a..b, ∫ y in c..d,
      (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      (claytonBaseReal θ b d) ^ (-1 / θ) -
        (claytonBaseReal θ a d) ^ (-1 / θ) -
        (claytonBaseReal θ b c) ^ (-1 / θ) +
        (claytonBaseReal θ a c) ^ (-1 / θ) := by
  have hinner :
      (∫ x in a..b, ∫ y in c..d,
        (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
          (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      ∫ x in a..b,
        x ^ (-θ - 1) * (claytonBaseReal θ x d) ^ (-1 / θ - 1) -
          x ^ (-θ - 1) * (claytonBaseReal θ x c) ^ (-1 / θ - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hx
    exact clayton_density_formula_integral_second θ x c d hθ
      (ha.trans_le hx'.1) (hx'.2.trans hb1) hc hcd hd1
  rw [hinner, intervalIntegral.integral_sub
    (clayton_first_derivative_intervalIntegrable θ d a b hθ
      (hc.trans_le hcd) hd1 ha hab hb1)
    (clayton_first_derivative_intervalIntegrable θ c a b hθ
      hc (hcd.trans hd1) ha hab hb1),
    clayton_cdf_formula_integral_first θ d a b hθ
      (hc.trans_le hcd) hd1 ha hab hb1,
    clayton_cdf_formula_integral_first θ c a b hθ
      hc (hcd.trans hd1) ha hab hb1]
  ring

/-- On positive rectangles, the analytic density integrates to the mass of
that rectangle under the actual Clayton copula measure. -/
theorem clayton_density_formula_positive_rectangle_eq_measure
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hab : a ≤ b)
    (hc : 0 < (c : ℝ)) (hcd : c ≤ d) :
    (∫ x in (a : ℝ)..(b : ℝ), ∫ y in (c : ℝ)..(d : ℝ),
      (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      (clayton 2 θ hθ).toMeasure.real
        (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) := by
  have hrect := clayton_density_formula_positive_rectangle θ
    (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) hθ ha hab b.property.2 hc hcd d.property.2
  rw [hrect, (clayton 2 θ hθ).measureReal_rectangle_two
    ![a, c] ![b, d] (by simpa [Pi.le_def, Fin.forall_fin_two] using And.intro hab hcd)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [clayton_cdf_positive_eq_analytic θ hθ b d (ha.trans_le hab) (hc.trans_le hcd),
    clayton_cdf_positive_eq_analytic θ hθ a d ha (hc.trans_le hcd),
    clayton_cdf_positive_eq_analytic θ hθ b c (ha.trans_le hab) hc,
    clayton_cdf_positive_eq_analytic θ hθ a c ha hc]

private theorem clayton_densityFormula_eq_real_of_pos
    (θ : ℝ) (x : Fin 2 → I)
    (hx0 : 0 < (x 0 : ℝ)) (hx1 : 0 < (x 1 : ℝ)) :
    claytonDensityFormula θ x =
      (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
        (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ) := by
  have hx0ne : x 0 ≠ 0 := by
    intro he
    exact (ne_of_gt hx0) (congrArg Subtype.val he)
  have hx1ne : x 1 ≠ 0 := by
    intro he
    exact (ne_of_gt hx1) (congrArg Subtype.val he)
  change (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
    (if x 0 = 0 ∨ x 1 = 0 then 0 else
      ((x 0 : ℝ) ^ (-θ) + (x 1 : ℝ) ^ (-θ) - 1) ^ (-2 - 1 / θ)) = _
  simp [hx0ne, hx1ne, claytonBaseReal]

private theorem clayton_densityFormula_integrableOn_positive_rectangle
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hc : 0 < (c : ℝ)) :
    IntegrableOn (claytonDensityFormula θ)
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) := by
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))
  have hs : MeasurableSet s := by
    dsimp [s]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => by fin_cases i <;> simp)
  have hi := clayton_density_real_integrableOn_positive_rectangle
    θ hθ a b c d ha hc
  apply hi.congr_fun _ hs
  intro x hx
  have hx0 := (Set.mem_pi.mp hx) 0 (by simp)
  have hx1 := (Set.mem_pi.mp hx) 1 (by simp)
  have hx0' : a < x 0 := by simpa using hx0.1
  have hx1' : c < x 1 := by simpa using hx1.1
  exact (clayton_densityFormula_eq_real_of_pos θ x
    (ha.trans hx0') (hc.trans hx1')).symm

/-- The package's Clayton density candidate has exactly the actual copula
measure on every positive half-open rectangle in the unit square. -/
theorem clayton_densityFormula_positive_rectangle_eq_measure
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hab : a ≤ b)
    (hc : 0 < (c : ℝ)) (hcd : c ≤ d) :
    (∫ x in Set.pi Set.univ
      (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i)),
      claytonDensityFormula θ x) =
      (clayton 2 θ hθ).toMeasure.real
        (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) := by
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))
  have hs : MeasurableSet s := by
    dsimp [s]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => by fin_cases i <;> simp)
  have hpoint (x : Fin 2 → I) (hx : x ∈ s) :
      claytonDensityFormula θ x =
        (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
          (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ) := by
    have hx0 := (Set.mem_pi.mp hx) 0 (by simp)
    have hx1 := (Set.mem_pi.mp hx) 1 (by simp)
    have hx0' : a < x 0 := by simpa using hx0.1
    have hx1' : c < x 1 := by simpa using hx1.1
    have hx0pos : 0 < (x 0 : ℝ) := ha.trans hx0'
    have hx1pos : 0 < (x 1 : ℝ) := hc.trans hx1'
    have hx0ne : x 0 ≠ 0 := by
      intro he
      exact (ne_of_gt hx0pos) (congrArg Subtype.val he)
    have hx1ne : x 1 ≠ 0 := by
      intro he
      exact (ne_of_gt hx1pos) (congrArg Subtype.val he)
    change (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
      (if x 0 = 0 ∨ x 1 = 0 then 0 else
        ((x 0 : ℝ) ^ (-θ) + (x 1 : ℝ) ^ (-θ) - 1) ^ (-2 - 1 / θ)) = _
    simp [hx0ne, hx1ne, claytonBaseReal]
  change (∫ x in s, claytonDensityFormula θ x) = _
  calc
    _ = ∫ x in s,
        (1 + θ) * (x 0 : ℝ) ^ (-θ - 1) * (x 1 : ℝ) ^ (-θ - 1) *
          (claytonBaseReal θ (x 0 : ℝ) (x 1 : ℝ)) ^ (-2 - 1 / θ) := by
      exact setIntegral_congr_fun hs hpoint
    _ = ∫ u in (a : ℝ)..(b : ℝ), ∫ v in (c : ℝ)..(d : ℝ),
        (1 + θ) * u ^ (-θ - 1) * v ^ (-θ - 1) *
          (claytonBaseReal θ u v) ^ (-2 - 1 / θ) := by
      exact integral_cube_Ioc_two_real
        (fun u v => (1 + θ) * u ^ (-θ - 1) * v ^ (-θ - 1) *
          (claytonBaseReal θ u v) ^ (-2 - 1 / θ)) a b c d hab hcd
        (clayton_density_real_integrableOn_positive_rectangle θ hθ a b c d ha hc)
    _ = _ := clayton_density_formula_positive_rectangle_eq_measure
      θ hθ a b c d ha hab hc hcd

/-- The measure built from the explicit density formula agrees with the
Clayton copula measure on each positive half-open rectangle. -/
theorem clayton_withDensity_positive_rectangle_eq_measure
    (θ : ℝ) (hθ : 0 < θ) (a b c d : I)
    (ha : 0 < (a : ℝ)) (hab : a ≤ b)
    (hc : 0 < (c : ℝ)) (hcd : c ≤ d) :
    ((volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x)))
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) =
      (clayton 2 θ hθ).toMeasure
        (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))) := by
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a, c] i) (![b, d] i))
  have hs : MeasurableSet s := by
    dsimp [s]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => by fin_cases i <;> simp)
  have hi := clayton_densityFormula_integrableOn_positive_rectangle
    θ hθ a b c d ha hc
  have hn : 0 ≤ᵐ[(volume : Measure (Fin 2 → I)).restrict s]
      claytonDensityFormula θ :=
    Filter.Eventually.of_forall (claytonDensityFormula_nonneg θ hθ)
  change ((volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x))) s = _
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hi hn,
    clayton_densityFormula_positive_rectangle_eq_measure θ hθ a b c d
      ha hab hc hcd]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- The candidate-density measure assigns zero mass to either coordinate
axis, as does every copula measure. -/
theorem clayton_withDensity_axis_zero (θ : ℝ) (i : Fin 2) :
    ((volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x)))
      {x | x i = 0} = 0 := by
  have hv : (volume : Measure (Fin 2 → I)) {x | x i = 0} = 0 := by
    change (independence 2).toMeasure
      ((fun x : Fin 2 → I => x i) ⁻¹' ({0} : Set I)) = 0
    rw [(independence 2).measure_preimage_eval i
      (measurableSet_singleton (0 : I))]
    simp
  exact (withDensity_absolutelyContinuous _ _) hv

private noncomputable def claytonCutoff (u v : I) (n : ℕ) : I := by
  let q : ℝ := min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1)
  have hq0 : 0 ≤ q := div_nonneg (le_min u.property.1 v.property.1) (by positivity)
  have hq1 : q ≤ 1 := by
    have hmin : min (u : ℝ) (v : ℝ) ≤ 1 :=
      (min_le_left _ _).trans u.property.2
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (div_le_self (le_min u.property.1 v.property.1) hden).trans hmin
  exact ⟨q, hq0, hq1⟩

private theorem claytonCutoff_pos (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) (n : ℕ) :
    0 < (claytonCutoff u v n : ℝ) := by
  change 0 < min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1)
  exact div_pos (lt_min hu hv) (by positivity)

private theorem claytonCutoff_le_left (u v : I) (n : ℕ) :
    claytonCutoff u v n ≤ u := by
  change min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1) ≤ (u : ℝ)
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (div_le_self (le_min u.property.1 v.property.1) hden).trans
    (min_le_left _ _)

private theorem claytonCutoff_le_right (u v : I) (n : ℕ) :
    claytonCutoff u v n ≤ v := by
  change min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1) ≤ (v : ℝ)
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (div_le_self (le_min u.property.1 v.property.1) hden).trans
    (min_le_right _ _)

private theorem claytonCutoff_tendsto_zero (u v : I) :
    Filter.Tendsto (fun n : ℕ => (claytonCutoff u v n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (min (u : ℝ) (v : ℝ))
  convert h using 1 <;> simp [claytonCutoff, div_eq_mul_inv]

private theorem claytonCutoff_antitone (u v : I) :
    Antitone (claytonCutoff u v) := by
  intro m n hmn
  change min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1) ≤
    min (u : ℝ) (v : ℝ) / ((m : ℝ) + 1)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hden : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  have hq : 0 ≤ min (u : ℝ) (v : ℝ) := le_min u.property.1 v.property.1
  simpa only [div_eq_mul_inv, one_mul] using
    (mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1) hden) hq)

private def claytonCutoffRect (u v : I) (n : ℕ) : Set (Fin 2 → I) :=
  Set.pi Set.univ (fun i : Fin 2 =>
    Set.Ioc (claytonCutoff u v n) (![u, v] i))

private theorem claytonCutoffRect_mono (u v : I) :
    Monotone (claytonCutoffRect u v) := by
  intro m n hmn x hx
  apply Set.mem_pi.mpr
  intro i hi
  have hxi := (Set.mem_pi.mp hx) i hi
  exact ⟨lt_of_le_of_lt (claytonCutoff_antitone u v hmn) hxi.1, hxi.2⟩

private theorem claytonCutoffRect_iUnion (u v : I) :
    (⋃ n : ℕ, claytonCutoffRect u v n) =
      Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_pi.mpr
    intro i hi
    have hxi := (Set.mem_pi.mp hn) i hi
    exact ⟨lt_of_le_of_lt (claytonCutoff u v n).property.1 hxi.1, hxi.2⟩
  · intro hx
    have hx0 := (Set.mem_pi.mp hx) 0 (by simp)
    have hx1 := (Set.mem_pi.mp hx) 1 (by simp)
    have hx0' : 0 < (x 0 : ℝ) := by simpa using hx0.1
    have hx1' : 0 < (x 1 : ℝ) := by simpa using hx1.1
    have h0 := (claytonCutoff_tendsto_zero u v).eventually_lt_const hx0'
    have h1 := (claytonCutoff_tendsto_zero u v).eventually_lt_const hx1'
    obtain ⟨n, hn0, hn1⟩ := (h0.and h1).exists
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    apply Set.mem_pi.mpr
    intro i hi
    fin_cases i
    · exact ⟨hn0, by simpa using hx0.2⟩
    · exact ⟨hn1, by simpa using hx1.2⟩

/-- The candidate's `withDensity` measure agrees with the Clayton
copula measure on every positive lower orthant. -/
theorem clayton_withDensity_positive_lowerOrthant_eq_measure
    (θ : ℝ) (hθ : 0 < θ) (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) :
    ((volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x)))
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i))) =
      (clayton 2 θ hθ).toMeasure
        (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i))) := by
  let ν : Measure (Fin 2 → I) :=
    (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x))
  let μ : Measure (Fin 2 → I) := (clayton 2 θ hθ).toMeasure
  change ν _ = μ _
  rw [← claytonCutoffRect_iUnion u v,
    (claytonCutoffRect_mono u v).measure_iUnion (μ := ν),
    (claytonCutoffRect_mono u v).measure_iUnion (μ := μ)]
  apply iSup_congr
  intro n
  have hset : Set.pi Set.univ (fun i : Fin 2 =>
      Set.Ioc (![claytonCutoff u v n, claytonCutoff u v n] i) (![u, v] i)) =
      claytonCutoffRect u v n := by
    ext x
    simp [claytonCutoffRect, Set.mem_pi, Fin.forall_fin_two]
  have h := clayton_withDensity_positive_rectangle_eq_measure θ hθ
    (claytonCutoff u v n) u (claytonCutoff u v n) v
    (claytonCutoff_pos u v hu hv n) (claytonCutoff_le_left u v n)
    (claytonCutoff_pos u v hu hv n) (claytonCutoff_le_right u v n)
  simpa [ν, μ, hset] using h

private theorem copula_axis_zero (C : Copula 2) (i : Fin 2) :
    C.toMeasure {x | x i = 0} = 0 := by
  change C.toMeasure ((fun x : Fin 2 → I => x i) ⁻¹' ({0} : Set I)) = 0
  rw [C.measure_preimage_eval i (measurableSet_singleton (0 : I))]
  simp

private theorem measure_Iic_eq_positiveIoc
    (δ : Measure (Fin 2 → I))
    (h0 : δ {x | x 0 = 0} = 0)
    (h1 : δ {x | x 1 = 0} = 0)
    (u v : I) :
    δ (Set.Iic ![u, v]) =
      δ (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i))) := by
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i))
  have hs : s ⊆ Set.Iic ![u, v] := by
    intro x hx
    change x ≤ ![u, v]
    intro i
    exact ((Set.mem_pi.mp hx) i (by simp)).2
  have hdiff : Set.Iic ![u, v] \ s ⊆
      {x : Fin 2 → I | x 0 = 0} ∪ {x | x 1 = 0} := by
    intro x hx
    by_contra haxes
    have hne : x 0 ≠ 0 ∧ x 1 ≠ 0 := by simpa using haxes
    have hp0 : (0 : I) < x 0 :=
      lt_of_le_of_ne (by exact_mod_cast (x 0).property.1) (Ne.symm hne.1)
    have hp1 : (0 : I) < x 1 :=
      lt_of_le_of_ne (by exact_mod_cast (x 1).property.1) (Ne.symm hne.2)
    have hxs : x ∈ s := by
      apply Set.mem_pi.mpr
      intro i hi
      fin_cases i
      · exact ⟨hp0, hx.1 0⟩
      · exact ⟨hp1, hx.1 1⟩
    exact hx.2 hxs
  have hnull : δ (Set.Iic ![u, v] \ s) = 0 :=
    measure_mono_null hdiff (measure_union_null h0 h1)
  exact (measure_eq_measure_of_null_sdiff hs hnull).symm

/-- The candidate's `withDensity` measure and the actual Clayton
copula measure agree on every closed lower orthant, including the axes. -/
theorem clayton_withDensity_lowerOrthant_eq_measure
    (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    ((volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x)))
      (Set.Iic ![u, v]) =
      (clayton 2 θ hθ).toMeasure (Set.Iic ![u, v]) := by
  let ν : Measure (Fin 2 → I) :=
    (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x))
  let C := clayton 2 θ hθ
  change ν (Set.Iic ![u, v]) = C.toMeasure (Set.Iic ![u, v])
  rw [measure_Iic_eq_positiveIoc ν
      (clayton_withDensity_axis_zero θ 0)
      (clayton_withDensity_axis_zero θ 1) u v,
    measure_Iic_eq_positiveIoc C.toMeasure
      (copula_axis_zero C 0) (copula_axis_zero C 1) u v]
  by_cases hu : 0 < (u : ℝ)
  · by_cases hv : 0 < (v : ℝ)
    · exact clayton_withDensity_positive_lowerOrthant_eq_measure θ hθ u v hu hv
    · have hv0 : v = 0 := by
        apply Subtype.ext
        exact le_antisymm (le_of_not_gt hv) v.property.1
      subst v
      have hs : Set.pi Set.univ (fun i : Fin 2 =>
          Set.Ioc 0 (![u, 0] i)) = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h := (Set.mem_pi.mp hx) 1 (by simp)
        have h' : x 1 ∈ Set.Ioc (0 : I) 0 := h
        exact (not_lt_of_ge h'.2) h'.1
      simp [hs]
  · have hu0 : u = 0 := by
      apply Subtype.ext
      exact le_antisymm (le_of_not_gt hu) u.property.1
    subst u
    have hs : Set.pi Set.univ (fun i : Fin 2 =>
        Set.Ioc 0 (![0, v] i)) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have h := (Set.mem_pi.mp hx) 0 (by simp)
      have h' : x 0 ∈ Set.Ioc (0 : I) 0 := h
      exact (not_lt_of_ge h'.2) h'.1
    simp [hs]

/-- The explicit positive-Clayton density formula generates exactly the
copula's probability measure on the full unit square. -/
theorem clayton_toMeasure_eq_withDensity_positive
    (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal (claytonDensityFormula θ x)) := by
  let C := clayton 2 θ hθ
  let ν : Measure (Fin 2 → I) :=
    (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (claytonDensityFormula θ x))
  have htop : Set.Iic ![(1 : I), 1] = Set.univ := by
    ext x
    simp [Set.mem_Iic, Pi.le_def, Fin.forall_fin_two, unitInterval.le_one']
  have hprob : IsProbabilityMeasure ν := ⟨by
    have h := clayton_withDensity_lowerOrthant_eq_measure θ hθ 1 1
    change ν (Set.Iic ![(1 : I), 1]) = C.toMeasure (Set.Iic ![(1 : I), 1]) at h
    simpa [htop] using h⟩
  have hμ (u : Fin 2 → I) : ν.real (Set.Iic u) = C.cdf u := by
    have h := clayton_withDensity_lowerOrthant_eq_measure θ hθ (u 0) (u 1)
    have heta : ![u 0, u 1] = u := by
      ext i
      fin_cases i <;> simp
    rw [heta] at h
    change ν.real (Set.Iic u) = C.toMeasure.real (Set.Iic u)
    exact congrArg ENNReal.toReal h
  let D := C.isClassical_cdf.ofMeasure ⟨ν, hprob⟩ hμ
  have he : D = C := cdf_injective
    (C.isClassical_cdf.cdf_ofMeasure ⟨ν, hprob⟩ hμ)
  change C.toMeasure = ν
  rw [← he]
  rfl

/-- Positive Clayton has an actual nonnegative MTP2 density, given by the
the explicit formula above. -/
theorem clayton_positive_density_tp2
    (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).HasMTP2Density := by
  refine ⟨claytonDensityFormula θ,
    measurable_claytonDensityFormula θ,
    claytonDensityFormula_nonneg θ hθ,
    isMTP2_claytonDensityFormula_positive θ hθ, ?_⟩
  exact clayton_toMeasure_eq_withDensity_positive θ hθ

/-- Positive Clayton is absolutely continuous with respect to uniform
volume on the unit square. -/
theorem clayton_positive_absolutelyContinuous
    (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).toMeasure ≪
      (volume : Measure (Fin 2 → I)) :=
  (clayton_positive_density_tp2 θ hθ).absolutelyContinuous

/-- The density's mass on the positive square with lower cutoff `r`
reaches the Clayton copula's corresponding square mass. -/
theorem clayton_density_formula_cutoff_square
    (θ : ℝ) (hθ : 0 < θ) (r : I) (hr : 0 < (r : ℝ)) :
    (∫ x in (r : ℝ)..1, ∫ y in (r : ℝ)..1,
      (1 + θ) * x ^ (-θ - 1) * y ^ (-θ - 1) *
        (claytonBaseReal θ x y) ^ (-2 - 1 / θ)) =
      1 - 2 * (r : ℝ) + (clayton 2 θ hθ).cdf ![r, r] := by
  have h := clayton_density_formula_positive_rectangle_eq_measure θ hθ
    r 1 r 1 hr (unitInterval.le_one _) hr (unitInterval.le_one _)
  rw [(clayton 2 θ hθ).measureReal_rectangle_two
    ![r, r] ![1, 1] (by simp [Pi.le_def, Fin.forall_fin_two, unitInterval.le_one'])] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    cdf_two_one_left, cdf_two_one_right] at h
  norm_num at h
  convert h using 1 <;> ring_nf


end ProbabilityTheory.Copula
