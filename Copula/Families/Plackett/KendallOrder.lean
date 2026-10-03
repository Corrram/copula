/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Order
import Copula.Families.Plackett.Spearman
import Copula.Families.Plackett.Kendall
import Copula.Order.StrictKendall
import Copula.Order.StrictSpearman
import Copula.Concordance.Continuity
import Copula.Rectangle

/-! # Monotonicity, sign and limits of Kendall's tau and Spearman's rho for the Plackett family

For the Plackett copulas `C_θ`, `θ > 0` (`Copula.Families.Plackett.Basic`; Nelsen 2006, §3.3.1):

* the Plackett density is positive, so every nondegenerate rectangle has positive
  `C_θ`-mass (`plackettCDF_rectangle_pos`) and `C_θ` has full support
  (`isOpenPosMeasure_plackett`);
* `θ ↦ C_θ` is injective (`plackett_injective`, via Blomqvist's beta);
* Kendall's tau and Spearman's rho are strictly increasing in `θ`
  (`kendallTau_plackett_lt_iff`, `kendallTau_plackett_strictMono`,
  `spearmanRho_plackett_lt_iff`, `spearmanRho_plackett_strictMono`). For tau this uses the
  concordance ordering `plackett_lowerOrthantLE` together with the strict monotonicity of
  tau under full support (`LowerOrthantLE.kendallTau_lt_of_isOpenPosMeasure_right`);
* signs: `τ(C_1) = ρ(C_1) = 0`, `τ(C_θ) > 0 ↔ θ > 1`, `τ(C_θ) < 0 ↔ θ < 1`, and likewise for
  rho; both lie in the open interval `(-1, 1)`;
* limits: `C_θ → M` as `θ → ∞` and `C_θ → W` as `θ → 0⁺` pointwise, hence
  `τ(C_θ), ρ(C_θ) → 1` as `θ → ∞` and `τ(C_θ), ρ(C_θ) → -1` as `θ → 0⁺`
  (`tendsto_kendallTau_plackett_atTop`, `tendsto_kendallTau_plackett_zero`, and the rho
  analogues), by continuity of the coefficients under pointwise convergence
  (`tendsto_kendallTau_of_tendsto`).

The limits are stated for an arbitrary parametrization `θ : α → ℝ` with positive values
along a countably generated filter (e.g. sequences).
-/

open MeasureTheory Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

/-! ## Positive rectangle masses and full support -/

/-- The Plackett partial derivative `∂C_θ/∂v` is strictly increasing in `u`. -/
theorem plackettDeriv_strictMonoOn {θ v : ℝ} (hθ : 0 < θ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    StrictMonoOn (fun u => plackettDeriv θ u v) (Icc 0 1) := by
  have hd : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun u => plackettDeriv θ u v) (plackettDensity θ x v) x :=
    fun x hx => hasDerivAt_plackettDeriv_left (plackettDisc_pos hθ hx.1 hx.2 hv0 hv1)
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hd x (Ioo_subset_Icc_self hx)).deriv]
    exact plackettDensity_pos hθ hx.1.le hx.2.le hv0 hv1

/-- Every nondegenerate rectangle in the unit square has positive Plackett mass. -/
theorem plackettCDF_rectangle_pos {θ : ℝ} (hθ : 0 < θ) {a b c e : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (hc : 0 ≤ c) (hce : c < e) (he : e ≤ 1) :
    0 < plackettCDF θ b e - plackettCDF θ a e - plackettCDF θ b c + plackettCDF θ a c := by
  have hd : ∀ v ∈ Icc c e, HasDerivAt (fun y => plackettCDF θ b y - plackettCDF θ a y)
      (plackettDeriv θ b v - plackettDeriv θ a v) v := fun v hv =>
    (hasDerivAt_plackettCDF_right_of_mem hθ (ha.trans hab.le) hb (hc.trans hv.1)
      (hv.2.trans he)).sub
      (hasDerivAt_plackettCDF_right_of_mem hθ ha (hab.le.trans hb) (hc.trans hv.1)
        (hv.2.trans he))
  have hsm : StrictMonoOn (fun y => plackettCDF θ b y - plackettCDF θ a y) (Icc c e) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc c e)
    · exact fun v hv => (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hd v (Ioo_subset_Icc_self hv)).deriv]
      exact sub_pos.mpr (plackettDeriv_strictMonoOn hθ (hc.trans hv.1.le) (hv.2.le.trans he)
        ⟨ha, hab.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩ hab)
  have := hsm ⟨le_rfl, hce.le⟩ ⟨hce.le, le_rfl⟩ hce
  simp only at this
  linarith

/-- **Full support of the Plackett copula**: its measure charges every nonempty open subset of
the unit square. -/
instance isOpenPosMeasure_plackett (θ : ℝ) (hθ : 0 < θ) :
    (plackett θ hθ).toMeasure.IsOpenPosMeasure where
  open_pos U hU hne := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
    set δ := min (ε / 2) (1 / 4) with hδdef
    have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
    let a : Fin 2 → I := fun i => projIcc 0 1 zero_le_one ((x i : ℝ) - δ)
    let b : Fin 2 → I := fun i => projIcc 0 1 zero_le_one ((x i : ℝ) + δ)
    have ha_eq (i : Fin 2) : (a i : ℝ) = max 0 (min 1 ((x i : ℝ) - δ)) := rfl
    have hb_eq (i : Fin 2) : (b i : ℝ) = max 0 (min 1 ((x i : ℝ) + δ)) := rfl
    have hab (i : Fin 2) : (a i : ℝ) < b i := by
      have hx0 := (x i).2.1
      have hx1 := (x i).2.2
      rw [ha_eq, hb_eq]
      exact max_lt (lt_of_lt_of_le (lt_min one_pos (by linarith)) (le_max_right _ _))
        (lt_of_le_of_lt (min_le_right _ _)
          (lt_of_lt_of_le (lt_min (by linarith) (by linarith)) (le_max_right _ _)))
    have hsub : Set.pi univ (fun i => Ioc (a i) (b i)) ⊆ U := by
      intro y hy
      apply hball
      rw [Metric.mem_ball, dist_pi_lt_iff hε]
      intro i
      have hyi := hy i (mem_univ i)
      have h1 : (a i : ℝ) < y i := hyi.1
      have h2 : (y i : ℝ) ≤ b i := hyi.2
      have hx0 := (x i).2.1
      have hx1 := (x i).2.2
      have ha' : (x i : ℝ) - δ ≤ a i := by
        rw [ha_eq]; exact (le_min (by linarith) le_rfl).trans (le_max_right _ _)
      have hb' : (b i : ℝ) ≤ x i + δ := by
        rw [hb_eq]; exact max_le (by linarith) (min_le_right _ _)
      rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hpos : 0 < (plackett θ hθ).toMeasure.real (Set.pi univ (fun i => Ioc (a i) (b i))) := by
      rw [measureReal_rectangle_two _ a b (fun i => (hab i).le)]
      simp only [cdf_plackett, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact plackettCDF_rectangle_pos hθ (a 0).2.1 (hab 0) (b 0).2.2 (a 1).2.1 (hab 1) (b 1).2.2
    intro h0
    have hnull := measure_mono_null hsub h0
    rw [measureReal_def, hnull] at hpos
    simp at hpos

/-! ## Injectivity of the parametrization -/

/-- Different parameters give different Plackett copulas. -/
theorem plackett_ne {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (h : θ ≠ θ') :
    plackett θ hθ ≠ plackett θ' hθ' := by
  intro he
  rcases lt_or_gt_of_ne h with h | h
  · have := blomqvistBeta_plackett_strictMono hθ hθ' h
    rw [he] at this
    exact lt_irrefl _ this
  · have := blomqvistBeta_plackett_strictMono hθ' hθ h
    rw [he] at this
    exact lt_irrefl _ this

theorem plackett_injective {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    plackett θ hθ = plackett θ' hθ' ↔ θ = θ' := by
  refine ⟨fun he => ?_, fun he => by subst he; rfl⟩
  by_contra hne
  exact plackett_ne hθ hθ' hne he

/-! ## Kendall's tau: strict monotonicity and sign -/

/-- **Kendall's tau of the Plackett family is strictly increasing in `θ`.** -/
theorem kendallTau_plackett_lt {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (h : θ < θ') :
    (plackett θ hθ).kendallTau < (plackett θ' hθ').kendallTau :=
  (plackett_lowerOrthantLE hθ hθ' h.le).kendallTau_lt_of_isOpenPosMeasure_right
    (plackett_ne hθ hθ' h.ne)

theorem kendallTau_plackett_strictMono :
    StrictMono (fun θ : Ioi (0 : ℝ) => (plackett θ θ.2).kendallTau) :=
  fun _ _ h => kendallTau_plackett_lt _ _ h

theorem kendallTau_plackett_lt_iff {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    (plackett θ hθ).kendallTau < (plackett θ' hθ').kendallTau ↔ θ < θ' := by
  refine ⟨fun h => ?_, kendallTau_plackett_lt hθ hθ'⟩
  by_contra! hle
  rcases hle.lt_or_eq with hlt | heq
  · exact lt_asymm h (kendallTau_plackett_lt hθ' hθ hlt)
  · subst heq; exact lt_irrefl _ h

theorem kendallTau_plackett_le_iff {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    (plackett θ hθ).kendallTau ≤ (plackett θ' hθ').kendallTau ↔ θ ≤ θ' := by
  rw [← not_lt, kendallTau_plackett_lt_iff hθ' hθ, not_lt]

theorem kendallTau_plackett_inj {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    (plackett θ hθ).kendallTau = (plackett θ' hθ').kendallTau ↔ θ = θ' := by
  rw [le_antisymm_iff, le_antisymm_iff, kendallTau_plackett_le_iff, kendallTau_plackett_le_iff]

/-- `τ(C_1) = 0`. -/
@[simp] theorem kendallTau_plackett_one : (plackett 1 one_pos).kendallTau = 0 := by
  rw [plackett_one, kendallTau_independence]

theorem kendallTau_plackett_pos_iff {θ : ℝ} (hθ : 0 < θ) :
    0 < (plackett θ hθ).kendallTau ↔ 1 < θ := by
  rw [← kendallTau_plackett_one, kendallTau_plackett_lt_iff]

theorem kendallTau_plackett_neg_iff {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).kendallTau < 0 ↔ θ < 1 := by
  rw [← kendallTau_plackett_one, kendallTau_plackett_lt_iff]

theorem kendallTau_plackett_eq_zero_iff {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).kendallTau = 0 ↔ θ = 1 := by
  rw [← kendallTau_plackett_one, kendallTau_plackett_inj]

/-- Kendall's tau of a Plackett copula lies in the open interval `(-1, 1)`. -/
theorem kendallTau_plackett_mem_Ioo {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).kendallTau ∈ Ioo (-1) 1 := by
  have hl := kendallTau_plackett_lt (half_pos hθ) hθ (half_lt_self hθ)
  have hu := kendallTau_plackett_lt hθ (by linarith : 0 < θ + 1) (lt_add_one θ)
  exact ⟨(kendallTau_mem_Icc _).1.trans_lt hl, hu.trans_le (kendallTau_mem_Icc _).2⟩

/-! ## Spearman's rho: strict monotonicity and sign -/

/-- **Spearman's rho of the Plackett family is strictly increasing in `θ`.** -/
theorem spearmanRho_plackett_lt {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') (h : θ < θ') :
    (plackett θ hθ).spearmanRho < (plackett θ' hθ').spearmanRho :=
  (plackett_lowerOrthantLE hθ hθ' h.le).spearmanRho_lt (plackett_ne hθ hθ' h.ne)

theorem spearmanRho_plackett_strictMono :
    StrictMono (fun θ : Ioi (0 : ℝ) => (plackett θ θ.2).spearmanRho) :=
  fun _ _ h => spearmanRho_plackett_lt _ _ h

theorem spearmanRho_plackett_lt_iff {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    (plackett θ hθ).spearmanRho < (plackett θ' hθ').spearmanRho ↔ θ < θ' := by
  refine ⟨fun h => ?_, spearmanRho_plackett_lt hθ hθ'⟩
  by_contra! hle
  rcases hle.lt_or_eq with hlt | heq
  · exact lt_asymm h (spearmanRho_plackett_lt hθ' hθ hlt)
  · subst heq; exact lt_irrefl _ h

theorem spearmanRho_plackett_le_iff {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    (plackett θ hθ).spearmanRho ≤ (plackett θ' hθ').spearmanRho ↔ θ ≤ θ' := by
  rw [← not_lt, spearmanRho_plackett_lt_iff hθ' hθ, not_lt]

theorem spearmanRho_plackett_inj {θ θ' : ℝ} (hθ : 0 < θ) (hθ' : 0 < θ') :
    (plackett θ hθ).spearmanRho = (plackett θ' hθ').spearmanRho ↔ θ = θ' := by
  rw [le_antisymm_iff, le_antisymm_iff, spearmanRho_plackett_le_iff, spearmanRho_plackett_le_iff]

theorem spearmanRho_plackett_pos_iff {θ : ℝ} (hθ : 0 < θ) :
    0 < (plackett θ hθ).spearmanRho ↔ 1 < θ := by
  rw [← spearmanRho_plackett_one, spearmanRho_plackett_lt_iff]

theorem spearmanRho_plackett_neg_iff {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).spearmanRho < 0 ↔ θ < 1 := by
  rw [← spearmanRho_plackett_one, spearmanRho_plackett_lt_iff]

theorem spearmanRho_plackett_eq_zero_iff {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).spearmanRho = 0 ↔ θ = 1 := by
  rw [← spearmanRho_plackett_one, spearmanRho_plackett_inj]

/-- Spearman's rho of a Plackett copula lies in the open interval `(-1, 1)`. -/
theorem spearmanRho_plackett_mem_Ioo {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).spearmanRho ∈ Ioo (-1) 1 := by
  have hl := spearmanRho_plackett_lt (half_pos hθ) hθ (half_lt_self hθ)
  have hu := spearmanRho_plackett_lt hθ (by linarith : 0 < θ + 1) (lt_add_one θ)
  exact ⟨(spearmanRho_mem_Icc _).1.trans_lt hl, hu.trans_le (spearmanRho_mem_Icc _).2⟩

/-! ## Limits -/

section Limits

variable {α : Type*} {l : Filter α}

/-- `C_θ → M` pointwise along any parametrization with `θ → ∞`. -/
theorem tendsto_plackett_cdf_atTop (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).cdf u) l (𝓝 ((comonotonic 2).cdf u)) := by
  have hu : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  simp only [cdf_plackett]
  rw [← hu]
  exact (tendsto_plackettCDF_atTop (u 0) (u 1)).comp hlim

/-- `C_θ → W` pointwise along any positive parametrization with `θ → 0`. -/
theorem tendsto_plackett_cdf_zero (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l (𝓝 0)) (u : Fin 2 → I) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).cdf u) l (𝓝 (countermonotonic.cdf u)) := by
  have hu : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
  have hlim' : Tendsto θ l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hθ⟩
  simp only [cdf_plackett]
  rw [← hu]
  exact (tendsto_plackettCDF_zero (u 0) (u 1)).comp hlim'

variable [l.IsCountablyGenerated]

/-- `τ(C_θ) → 1` as `θ → ∞`. -/
theorem tendsto_kendallTau_plackett_atTop (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l atTop) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).kendallTau) l (𝓝 1) := by
  simpa using tendsto_kendallTau_of_tendsto (fun a => plackett (θ a) (hθ a)) (comonotonic 2)
    (tendsto_plackett_cdf_atTop θ hθ hlim)

/-- `τ(C_θ) → -1` as `θ → 0⁺`. -/
theorem tendsto_kendallTau_plackett_zero (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l (𝓝 0)) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).kendallTau) l (𝓝 (-1)) := by
  simpa using tendsto_kendallTau_of_tendsto (fun a => plackett (θ a) (hθ a)) countermonotonic
    (tendsto_plackett_cdf_zero θ hθ hlim)

/-- `ρ(C_θ) → 1` as `θ → ∞`. -/
theorem tendsto_spearmanRho_plackett_atTop (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l atTop) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).spearmanRho) l (𝓝 1) := by
  simpa using tendsto_spearmanRho_of_tendsto (fun a => plackett (θ a) (hθ a)) (comonotonic 2)
    (tendsto_plackett_cdf_atTop θ hθ hlim)

/-- `ρ(C_θ) → -1` as `θ → 0⁺`. -/
theorem tendsto_spearmanRho_plackett_zero (θ : α → ℝ) (hθ : ∀ a, 0 < θ a)
    (hlim : Tendsto θ l (𝓝 0)) :
    Tendsto (fun a => (plackett (θ a) (hθ a)).spearmanRho) l (𝓝 (-1)) := by
  simpa using tendsto_spearmanRho_of_tendsto (fun a => plackett (θ a) (hθ a)) countermonotonic
    (tendsto_plackett_cdf_zero θ hθ hlim)

end Limits

end ProbabilityTheory.Copula
