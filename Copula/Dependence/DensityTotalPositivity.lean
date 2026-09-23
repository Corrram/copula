/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Dependence.Density
import Copula.Dependence.ClaytonTotalPositivity
import Copula.Dependence.Singular
import Copula.Dependence.FGMDensity
import Copula.Families.Nelsen7
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

/-! # Density total positivity and quadrant dependence

The four-quadrant determinant is obtained by successive nonnegative
integrations of the pointwise MTP2 inequality. Uniform copula marginals then
turn that determinant into positive quadrant dependence. This excludes every
negative Clayton parameter from the `HasMTP2Density` class, irrespective of
which almost-everywhere density version is chosen.
-/

namespace ProbabilityTheory.Copula

private theorem lintegral_cross
    (F : I → I → ENNReal)
    (hF : Measurable (Function.uncurry F))
    (hTP : ∀ a b c d : I, a ≤ b → c ≤ d →
      F a d * F b c ≤ F a c * F b d)
    (u v : I) :
    (∫⁻ x in Iic u, ∫⁻ y in Ioi v, F x y) *
      (∫⁻ x in Ioi u, ∫⁻ y in Iic v, F x y) ≤
    (∫⁻ x in Iic u, ∫⁻ y in Iic v, F x y) *
      (∫⁻ x in Ioi u, ∫⁻ y in Ioi v, F x y) := by
  let μL : Measure I := (volume : Measure I).restrict (Iic u)
  let μH : Measure I := (volume : Measure I).restrict (Ioi u)
  let νL : Measure I := (volume : Measure I).restrict (Iic v)
  let νH : Measure I := (volume : Measure I).restrict (Ioi v)
  let L : I → ENNReal := fun x => ∫⁻ y, F x y ∂νL
  let H : I → ENNReal := fun x => ∫⁻ y, F x y ∂νH
  have hsection (x : I) : Measurable (F x) := by
    simpa [Function.uncurry, Function.comp_def] using
      hF.comp (measurable_const.prodMk measurable_id :
        Measurable (fun y : I => (x, y)))
  have hL : Measurable L := Measurable.lintegral_prod_right (ν := νL) hF
  have hH : Measurable H := Measurable.lintegral_prod_right (ν := νH) hF
  have hpoint (x x' y : I) (hx : x ≤ u) (hx' : u < x') (hy : y ≤ v) :
      F x' y * H x ≤ F x y * H x' := by
    have hmono :
        (∫⁻ y', F x' y * F x y' ∂νH) ≤
          (∫⁻ y', F x y * F x' y' ∂νH) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y' hy'
      calc
        F x' y * F x y' = F x y' * F x' y := mul_comm _ _
        _ ≤ F x y * F x' y' := hTP x x' y y' (hx.trans hx'.le) (hy.trans hy'.le)
    rw [lintegral_const_mul (F x' y) (hsection x),
      lintegral_const_mul (F x y) (hsection x')] at hmono
    exact hmono
  have hpair (x x' : I) (hx : x ≤ u) (hx' : u < x') :
      L x' * H x ≤ L x * H x' := by
    have hmono :
        (∫⁻ y, F x' y * H x ∂νL) ≤
          (∫⁻ y, F x y * H x' ∂νL) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with y hy
      exact hpoint x x' y hx hx' hy
    rw [lintegral_mul_const (H x) (hsection x'),
      lintegral_mul_const (H x') (hsection x)] at hmono
    exact hmono
  have hsingle (x : I) (hx : x ≤ u) :
      (∫⁻ x', L x' ∂μH) * H x ≤
        L x * (∫⁻ x', H x' ∂μH) := by
    have hmono :
        (∫⁻ x', L x' * H x ∂μH) ≤
          (∫⁻ x', L x * H x' ∂μH) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x' hx'
      exact hpair x x' hx hx'
    rw [lintegral_mul_const (H x) hL,
      lintegral_const_mul (L x) hH] at hmono
    exact hmono
  have hmono :
      (∫⁻ x, (∫⁻ x', L x' ∂μH) * H x ∂μL) ≤
        (∫⁻ x, L x * (∫⁻ x', H x' ∂μH) ∂μL) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact hsingle x hx
  rw [lintegral_const_mul _ hH, lintegral_mul_const _ hL] at hmono
  change (∫⁻ x, H x ∂μL) * (∫⁻ x, L x ∂μH) ≤
    (∫⁻ x, L x ∂μL) * (∫⁻ x, H x ∂μH)
  simpa only [mul_comm] using hmono

private theorem lintegral_fin_two_unit (g : (Fin 2 → I) → ENNReal)
    (hg : Measurable g) :
    (∫⁻ x, g x) = ∫⁻ u : I, ∫⁻ v : I, g ![u, v] := by
  let e : (Fin 2 → I) ≃ᵐ I × I := MeasurableEquiv.finTwoArrow
  have hp : MeasurePreserving e (volume : Measure (Fin 2 → I))
      (volume : Measure (I × I)) := volume_preserving_finTwoArrow I
  have h := hp.symm.lintegral_comp hg
  rw [Measure.volume_eq_prod I I] at h
  rw [lintegral_prod (fun z => g (e.symm z))
    (hg.comp e.symm.measurable).aemeasurable] at h
  simpa [e, MeasurableEquiv.finTwoArrow] using h.symm

private theorem lintegral_cube_rect (F : I → I → ENNReal)
    (hF : Measurable (Function.uncurry F)) (s t : Set I)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (∫⁻ x in {x : Fin 2 → I | x 0 ∈ s ∧ x 1 ∈ t}, F (x 0) (x 1)) =
      ∫⁻ u in s, ∫⁻ v in t, F u v := by
  let r : Set (Fin 2 → I) := {x | x 0 ∈ s ∧ x 1 ∈ t}
  have hr : MeasurableSet r :=
    (hs.preimage (measurable_pi_apply 0)).inter
      (ht.preimage (measurable_pi_apply 1))
  have hG : Measurable (fun x : Fin 2 → I => F (x 0) (x 1)) := by
    simpa [Function.uncurry, Function.comp_def] using
      hF.comp (((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)) :
        Measurable (fun x : Fin 2 → I => (x 0, x 1)))
  change (∫⁻ x in r, F (x 0) (x 1)) = _
  rw [← lintegral_indicator hr,
    lintegral_fin_two_unit _ (hG.indicator hr)]
  have he (u v : I) : r.indicator (fun x : Fin 2 → I => F (x 0) (x 1)) ![u, v] =
      s.indicator (fun u' : I => t.indicator (F u') v) u := by
    by_cases hu : u ∈ s <;> by_cases hv : v ∈ t
    all_goals simp [Set.indicator, r, hu, hv]
  simp_rw [he]
  have hi (u : I) :
      (∫⁻ v, s.indicator (fun u' : I => t.indicator (F u') v) u) =
        s.indicator (fun u' : I => ∫⁻ v, t.indicator (F u') v) u := by
    by_cases hu : u ∈ s <;> simp [Set.indicator, hu]
  simp_rw [hi]
  simp_rw [lintegral_indicator ht]
  rw [lintegral_indicator hs]

private theorem quadrant_mass_inequality (A B D E : ENNReal)
    (h : D * B ≤ A * E) :
    (A + D) * (A + B) ≤ A * (A + B + D + E) := by
  calc
    (A + D) * (A + B) = A * (A + B + D) + D * B := by ring
    _ ≤ A * (A + B + D) + A * E := add_le_add_right h _
    _ = A * (A + B + D + E) := by ring

private theorem pqd_of_quadrant_cross {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (P Q : Set α) (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (hcross : μ (P ∩ Qᶜ) * μ (Pᶜ ∩ Q) ≤
      μ (P ∩ Q) * μ (Pᶜ ∩ Qᶜ)) :
    μ.real P * μ.real Q ≤ μ.real (P ∩ Q) := by
  let A : ℝ := μ.real (P ∩ Q)
  let B : ℝ := μ.real (Pᶜ ∩ Q)
  let D : ℝ := μ.real (P ∩ Qᶜ)
  let E : ℝ := μ.real (Pᶜ ∩ Qᶜ)
  have hcrossR : D * B ≤ A * E := by
    have h := ENNReal.toReal_mono (by finiteness) hcross
    simpa only [Measure.real, ENNReal.toReal_mul, A, B, D, E] using h
  have hRP : A + D = μ.real P := by
    simpa only [A, D, sdiff_eq] using
      (measureReal_inter_add_sdiff (μ := μ) (s := P) hQ)
  have hRQ : A + B = μ.real Q := by
    simpa only [A, B, sdiff_eq, inter_comm] using
      (measureReal_inter_add_sdiff (μ := μ) (s := Q) hP)
  have hRnotP : B + E = μ.real Pᶜ := by
    simpa only [B, E, sdiff_eq] using
      (measureReal_inter_add_sdiff (μ := μ) (s := Pᶜ) hQ)
  have htotal : A + B + D + E = 1 := by
    have hc := measureReal_add_measureReal_compl (μ := μ) hP
    rw [probReal_univ] at hc
    linarith
  calc
    μ.real P * μ.real Q = (A + D) * (A + B) := by rw [hRP, hRQ]
    _ ≤ A * (A + B + D + E) := by
      calc
        _ = A * (A + B + D) + D * B := by ring
        _ ≤ A * (A + B + D) + A * E := add_le_add_right hcrossR _
        _ = _ := by ring
    _ = μ.real (P ∩ Q) := by rw [htotal]; simp [A]

/-- A copula with an MTP2 Lebesgue density is positively quadrant dependent. -/
theorem hasMTP2Density_isPQD (C : Copula 2) (h : C.HasMTP2Density) :
    C.IsPQD := by
  obtain ⟨f, hf, hn, hm, heq⟩ := h
  let F : I → I → ENNReal := fun u v => ENNReal.ofReal (f ![u, v])
  have hF : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hTP : ∀ a b c d : I, a ≤ b → c ≤ d →
      F a d * F b c ≤ F a c * F b d := by
    intro a b c d hab hcd
    have ht := (isMTP2_fin_two_iff f).mp hm a b c d hab hcd
    have hl : 0 ≤ f ![a, d] := hn _
    have hr : 0 ≤ f ![a, c] := hn _
    dsimp [F]
    rw [← ENNReal.ofReal_mul hl, ← ENNReal.ofReal_mul hr]
    exact ENNReal.ofReal_le_ofReal ht
  have hrect (s t : Set I) (hs : MeasurableSet s) (ht : MeasurableSet t) :
      C.toMeasure {x : Fin 2 → I | x 0 ∈ s ∧ x 1 ∈ t} =
        ∫⁻ u in s, ∫⁻ v in t, F u v := by
    let r : Set (Fin 2 → I) := {x | x 0 ∈ s ∧ x 1 ∈ t}
    have hr : MeasurableSet r :=
      (hs.preimage (measurable_pi_apply 0)).inter
        (ht.preimage (measurable_pi_apply 1))
    rw [heq, withDensity_apply _ hr]
    have hfun : (fun x : Fin 2 → I => ENNReal.ofReal (f x)) =
        (fun x : Fin 2 → I => F (x 0) (x 1)) := by
      funext x
      have hx : ![x 0, x 1] = x := by
        ext i
        fin_cases i <;> rfl
      simp [F, hx]
    rw [hfun]
    exact lintegral_cube_rect F hF s t hs ht
  intro u v
  let P : Set (Fin 2 → I) := {x | x 0 ≤ u}
  let Q : Set (Fin 2 → I) := {x | x 1 ≤ v}
  have hP : MeasurableSet P := by
    change MeasurableSet ((fun x : Fin 2 → I => x 0) ⁻¹' Iic u)
    exact measurableSet_Iic.preimage (measurable_pi_apply 0)
  have hQ : MeasurableSet Q := by
    change MeasurableSet ((fun x : Fin 2 → I => x 1) ⁻¹' Iic v)
    exact measurableSet_Iic.preimage (measurable_pi_apply 1)
  have hA : P ∩ Q = {x : Fin 2 → I | x 0 ∈ Iic u ∧ x 1 ∈ Iic v} := by
    ext x
    simp [P, Q]
  have hB : Pᶜ ∩ Q = {x : Fin 2 → I | x 0 ∈ Ioi u ∧ x 1 ∈ Iic v} := by
    ext x
    simp [P, Q, not_le]
  have hD : P ∩ Qᶜ = {x : Fin 2 → I | x 0 ∈ Iic u ∧ x 1 ∈ Ioi v} := by
    ext x
    simp [P, Q, not_le]
  have hE : Pᶜ ∩ Qᶜ = {x : Fin 2 → I | x 0 ∈ Ioi u ∧ x 1 ∈ Ioi v} := by
    ext x
    simp [P, Q, not_le]
  have hcross : C.toMeasure (P ∩ Qᶜ) * C.toMeasure (Pᶜ ∩ Q) ≤
      C.toMeasure (P ∩ Q) * C.toMeasure (Pᶜ ∩ Qᶜ) := by
    rw [hD, hB, hA, hE,
      hrect (Iic u) (Ioi v) measurableSet_Iic measurableSet_Ioi,
      hrect (Ioi u) (Iic v) measurableSet_Ioi measurableSet_Iic,
      hrect (Iic u) (Iic v) measurableSet_Iic measurableSet_Iic,
      hrect (Ioi u) (Ioi v) measurableSet_Ioi measurableSet_Ioi]
    exact lintegral_cross F hF hTP u v
  have hcore := pqd_of_quadrant_cross C.toMeasure P Q hP hQ hcross
  have hPset : P = Iic ![u, 1] := by
    ext x
    simp [P, Pi.le_def, Fin.forall_fin_two, unitInterval.le_one']
  have hQset : Q = Iic ![1, v] := by
    ext x
    simp [Q, Pi.le_def, Fin.forall_fin_two, unitInterval.le_one']
  have hAset : P ∩ Q = Iic ![u, v] := by
    ext x
    simp [P, Q, Pi.le_def, Fin.forall_fin_two]
  have hinter : Iic ![u, 1] ∩ Iic ![1, v] = Iic ![u, v] := by
    simpa only [hPset, hQset] using hAset
  rw [hPset, hQset, hinter] at hcore
  change C.cdf ![u, 1] * C.cdf ![1, v] ≤ C.cdf ![u, v] at hcore
  simpa using hcore

/-- No negative Clayton parameter admits an MTP2 density version, including
interior parameters, without any assumption on absolute continuity. -/
theorem clayton_negative_not_density_tp2 (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    ¬(claytonNegative θ hθ hn).HasMTP2Density := by
  intro h
  exact not_isPQD_clayton_negative θ hθ hn
    (hasMTP2Density_isPQD _ h)

/-- A conditionally decreasing copula with an MTP2 density must be
independence, since CD implies NQD whereas MTP2 density implies PQD. -/
theorem isCD_eq_independence_of_hasMTP2Density (C : Copula 2)
    (hCD : C.IsCD) (hM : C.HasMTP2Density) : C = independence 2 :=
  (isPQD_and_isNQD_iff C).mp
    ⟨hasMTP2Density_isPQD C hM, hCD.isNQD⟩

/-- The Nelsen 7 family has an MTP2 density exactly at its independence
endpoint; this includes the singular lower endpoint and all interior values. -/
theorem nelsen7_density_tp2_iff (θ : I) :
    (nelsen7 θ).HasMTP2Density ↔ θ = 1 := by
  constructor
  · intro h
    have he := isCD_eq_independence_of_hasMTP2Density
      (nelsen7 θ) (isCD_nelsen7 θ) h
    exact (isCI_nelsen7_iff θ).mp (he ▸ isCI_independence)
  · intro h
    subst θ
    rw [nelsen7_one]
    exact hasMTP2Density_independence 2

/-- For FGM, the actual copula has an MTP2 density exactly for
nonnegative parameters. The negative exclusion applies to every possible
density version, not just the displayed polynomial formula. -/
theorem fgm_hasMTP2Density_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (fgm θ hθ).HasMTP2Density ↔ 0 ≤ θ := by
  constructor
  · intro h
    by_contra hn
    have hneg : θ < 0 := lt_of_not_ge hn
    have hCD : (fgm θ hθ).IsCD :=
      (isCD_fgm_iff θ hθ).mpr hneg.le
    have he := isCD_eq_independence_of_hasMTP2Density _ hCD h
    have hCI : (fgm θ hθ).IsCI := he ▸ isCI_independence
    exact hn ((isCI_fgm_iff θ hθ).mp hCI)
  · exact hasMTP2Density_fgm θ hθ

end ProbabilityTheory.Copula
