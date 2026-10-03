/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.ExtremeValue.Pickands
import Copula.Archimedean.TailDependence
import Copula.Archimedean.Exponential
import Copula.Rank.Basic

/-! # Archimax copulas

Capéraà, Fougères and Genest (2000) combine an Archimedean generator with a Pickands dependence
function. For a bivariate Archimedean generator `g` (inverse generator `ψ = g.toFun`, generator
`φ = g.invFun`) and a Pickands function `A`, the *Archimax copula* is

`C_{ψ,A}(u,v) = ψ(ℓ_A(φ(u), φ(v))) = ψ((φ(u) + φ(v)) A(φ(v) / (φ(u) + φ(v))))`

on `(0,1]²` (zero on the lower edges), where `ℓ_A = pickandsTail A` is the stable tail
dependence function. We use the library's convention for `A` (that of `pickandsCopula`, where
`C_A(u,v) = exp(-ℓ_A(-log u, -log v))`); Capéraà–Fougères–Genest write `A(φ(u)/(φ(u)+φ(v)))`,
i.e. their `A` is our `t ↦ A(1 - t)` (`archimaxCopula_comp_one_sub` relates the two).

Main results:
* `archimaxCopula g A hA`: `C_{ψ,A}` is a copula (Capéraà–Fougères–Genest 2000, Proposition 1).
  The proof is elementary: `ℓ_A` is nondecreasing and submodular, and `ψ` is convex and
  nonincreasing, so `ψ ∘ ℓ_A` is supermodular (this is the argument behind `exp ∘ (-ℓ_A)` for the
  extreme-value case).
* `archimaxCopula_const_one`: `A ≡ 1` gives the Archimedean copula `g.copula`;
  `archimaxCopula_exponentialGenerator`: `ψ = exp(-·)` gives the extreme-value copula
  `pickandsCopula A`; `archimaxCopula_max`: `A = max(t, 1-t)` gives `M` for every generator.
* `archimaxCopula_lowerOrthantLE`: `A ≤ B` implies `C_{ψ,B} ≤ C_{ψ,A}`; in particular
  `g.copula ≤ C_{ψ,A}` (`generator_lowerOrthantLE_archimaxCopula`).
* `transpose_archimaxCopula`: the transpose is the Archimax copula of `t ↦ A(1 - t)`.
* `diagonal_archimaxCopula`: the diagonal is `ψ(2A(1/2) φ(t))`, hence Blomqvist's
  `β = 4ψ(2A(1/2) φ(1/2)) - 1` (`blomqvistBeta_archimaxCopula`).
* Tail dependence (Capéraà–Fougères–Genest 2000, Section 4): if `ψ` has a finite nonzero right
  derivative at `0` then `λ_U = 2(1 - A(1/2))`
  (`hasUpperTailDependence_archimaxCopula_of_hasDerivWithinAt`); in general
  `λ_U = 2 - lim_{x→0+} (1 - ψ(2A(1/2)x)) / (1 - ψ(x))`
  (`hasUpperTailDependence_archimaxCopula_of_tendsto`), and for a strict generator
  `λ_L = lim_{x→∞} ψ(2A(1/2)x) / ψ(x)` (`hasLowerTailDependence_archimaxCopula_of_tendsto`).

References: P. Capéraà, A.-L. Fougères and C. Genest, *Bivariate distributions with given
extreme value attractor*, J. Multivariate Anal. 72 (2000) 30–49; F. Durante and C. Sempi,
*Principles of Copula Theory* (2016), Section 6.6 (Archimax copulas).
-/

open Set Filter
open scoped unitInterval Topology

namespace ProbabilityTheory.Copula

namespace BivariateGenerator

variable (g : BivariateGenerator) {A : ℝ → ℝ}

private theorem coe_pos_of_ne' {u : I} (hu : u ≠ 0) : (0 : ℝ) < u :=
  lt_of_le_of_ne u.2.1 (fun h => hu (Subtype.ext h.symm))

/-- The Archimax CDF `ψ(ℓ_A(φ(u), φ(v)))`, zero on the lower edges. -/
noncomputable def archimaxCDF (A : ℝ → ℝ) (u v : I) : ℝ :=
  if u = 0 ∨ v = 0 then 0 else g.toFun (pickandsTail A (g.invFun u) (g.invFun v))

theorem archimaxCDF_of_ne {u v : I} (hu : u ≠ 0) (hv : v ≠ 0) :
    g.archimaxCDF A u v = g.toFun (pickandsTail A (g.invFun u) (g.invFun v)) := by
  rw [archimaxCDF, ite_eq_right (not_or.2 ⟨hu, hv⟩)]

@[simp] theorem archimaxCDF_zero_left (A : ℝ → ℝ) (v : I) : g.archimaxCDF A 0 v = 0 := by
  simp [archimaxCDF]

@[simp] theorem archimaxCDF_zero_right (A : ℝ → ℝ) (u : I) : g.archimaxCDF A u 0 = 0 := by
  simp [archimaxCDF]

theorem archimaxCDF_nonneg (A : ℝ → ℝ) (u v : I) (hA : IsPickandsFunction A) :
    0 ≤ g.archimaxCDF A u v := by
  by_cases h : u = 0 ∨ v = 0
  · simp [archimaxCDF, h]
  · push Not at h
    rw [g.archimaxCDF_of_ne h.1 h.2]
    exact g.nonneg _ (pickandsTail_nonneg hA (g.inv_nonneg u h.1) (g.inv_nonneg v h.2))

theorem archimaxCDF_one_left (hA : IsPickandsFunction A) (v : I) : g.archimaxCDF A 1 v = v := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [g.archimaxCDF_of_ne one_ne_zero hv, g.inv_one, pickandsTail_zero_left hA,
      g.right_inv v hv]

theorem archimaxCDF_one_right (hA : IsPickandsFunction A) (u : I) :
    g.archimaxCDF A u 1 = u := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [g.archimaxCDF_of_ne hu one_ne_zero, g.inv_one, pickandsTail_zero_right hA,
      g.right_inv u hu]

theorem archimaxCDF_mono (hA : IsPickandsFunction A) {u u' v v' : I} (hu : u ≤ u')
    (hv : v ≤ v') : g.archimaxCDF A u v ≤ g.archimaxCDF A u' v' := by
  by_cases h : u = 0 ∨ v = 0
  · rw [archimaxCDF, ite_eq_left h]
    exact g.archimaxCDF_nonneg A u' v' hA
  push Not at h
  have hu' : u' ≠ 0 := fun h' => h.1 (le_antisymm (h' ▸ hu) unitInterval.nonneg')
  have hv' : v' ≠ 0 := fun h' => h.2 (le_antisymm (h' ▸ hv) unitInterval.nonneg')
  rw [g.archimaxCDF_of_ne h.1 h.2, g.archimaxCDF_of_ne hu' hv']
  have hx' := g.inv_nonneg u' hu'
  have hy' := g.inv_nonneg v' hv'
  have hxx := g.inv_antitone u u' h.1 hu
  have hyy := g.inv_antitone v v' h.2 hv
  apply g.antitone (pickandsTail_nonneg hA hx' hy')
    (pickandsTail_nonneg hA (g.inv_nonneg u h.1) (g.inv_nonneg v h.2))
  exact (pickandsTail_mono_left hA hx' hxx hy').trans
    (pickandsTail_mono_right hA (hx'.trans hxx) hy' hyy)

/-- Supermodularity of `ψ ∘ ℓ`: for a convex nonincreasing `ψ` on `[0,∞)`, `p ≤ r`, `p ≤ s`,
`0 ≤ q ≤ r + s - p` imply `ψ(r) + ψ(s) ≤ ψ(p) + ψ(q)`. -/
theorem add_le_add_of_submodular {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpr : p ≤ r)
    (hps : p ≤ s) (hqrs : q ≤ r + s - p) :
    g.toFun r + g.toFun s ≤ g.toFun p + g.toFun q := by
  have h1 := convex_increment g.convex le_rfl hp (sub_nonneg.2 hpr) hps
  have h2 := g.antitone hq (show r + s - p ∈ Ici (0 : ℝ) by
    simp only [mem_Ici]; linarith) hqrs
  simp only [zero_add, sub_add_cancel] at h1
  have he : r - p + s = r + s - p := by ring
  rw [he] at h1
  linarith

theorem archimaxCDF_rect (hA : IsPickandsFunction A) {a b c e : I} (hab : a ≤ b)
    (hce : c ≤ e) :
    0 ≤ g.archimaxCDF A b e - g.archimaxCDF A a e - g.archimaxCDF A b c +
      g.archimaxCDF A a c := by
  by_cases ha : a = 0
  · rw [ha, archimaxCDF_zero_left, archimaxCDF_zero_left]
    linarith [g.archimaxCDF_mono hA (le_refl b) hce]
  by_cases hc : c = 0
  · rw [hc, archimaxCDF_zero_right, archimaxCDF_zero_right]
    linarith [g.archimaxCDF_mono hA hab (le_refl e)]
  have hb : b ≠ 0 := fun h => ha (le_antisymm (h ▸ hab) unitInterval.nonneg')
  have he : e ≠ 0 := fun h => hc (le_antisymm (h ▸ hce) unitInterval.nonneg')
  rw [g.archimaxCDF_of_ne hb he, g.archimaxCDF_of_ne ha he, g.archimaxCDF_of_ne hb hc,
    g.archimaxCDF_of_ne ha hc]
  have hx := g.inv_nonneg b hb
  have hy := g.inv_nonneg e he
  have hxx := g.inv_antitone a b ha hab
  have hyy := g.inv_antitone c e hc hce
  have hsub := pickandsTail_submodular hA hx hxx hy hyy
  have h1 := pickandsTail_mono_left hA hx hxx hy
  have h2 := pickandsTail_mono_right hA hx hy hyy
  have := g.add_le_add_of_submodular (pickandsTail_nonneg hA hx hy)
    (pickandsTail_nonneg hA (hx.trans hxx) (hy.trans hyy)) h1 h2 (by linarith)
  linarith

/-- The **Archimax copula** `C_{ψ,A}(u,v) = ψ(ℓ_A(φ(u), φ(v)))` of a bivariate Archimedean
generator and a Pickands dependence function (Capéraà–Fougères–Genest 2000). -/
noncomputable def archimaxCopula (A : ℝ → ℝ) (hA : IsPickandsFunction A) : Copula 2 :=
  ofClassical _ (IsClassical.ofBivariate (g.archimaxCDF A) (g.archimaxCDF_zero_left A)
    (g.archimaxCDF_zero_right A) (g.archimaxCDF_one_left hA) (g.archimaxCDF_one_right hA)
    (fun _ _ _ _ hab hce => g.archimaxCDF_rect hA hab hce))

theorem cdf_archimaxCopula (hA : IsPickandsFunction A) (u : Fin 2 → I) :
    (g.archimaxCopula A hA).cdf u = g.archimaxCDF A (u 0) (u 1) := by
  rw [archimaxCopula, cdf_ofClassical]

theorem cdf_archimaxCopula_two (hA : IsPickandsFunction A) (u v : I) :
    (g.archimaxCopula A hA).cdf ![u, v] = g.archimaxCDF A u v := by
  rw [cdf_archimaxCopula]
  rfl

/-- The Capéraà–Fougères–Genest formula
`C(u,v) = ψ((φ(u) + φ(v)) A(φ(v) / (φ(u) + φ(v))))` on `(0,1]²`. -/
theorem cdf_archimaxCopula_eq (hA : IsPickandsFunction A) {u v : I} (hu : u ≠ 0)
    (hv : v ≠ 0) :
    (g.archimaxCopula A hA).cdf ![u, v] =
      g.toFun ((g.invFun u + g.invFun v) * A (g.invFun v / (g.invFun u + g.invFun v))) := by
  rw [cdf_archimaxCopula_two, g.archimaxCDF_of_ne hu hv, pickandsTail]

/-! ### Special cases -/

/-- `A ≡ 1` gives the Archimedean copula of the generator. -/
theorem archimaxCopula_const_one :
    g.archimaxCopula (fun _ => 1) isPickandsFunction_const_one = g.copula := by
  apply ext_cdf_two
  intro u v
  rw [cdf_archimaxCopula_two, cdf_copula]
  by_cases h : u = 0 ∨ v = 0
  · simp [archimaxCDF, BivariateGenerator.cdf, h]
  · push Not at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [g.archimaxCDF_of_ne h.1 h.2, BivariateGenerator.cdf, ite_eq_right (not_or.2 h),
      pickandsTail, mul_one]

/-- `ψ = exp(-·)` (`φ = -log`) gives the extreme-value copula `C_A`. -/
theorem _root_.ProbabilityTheory.Copula.archimaxCopula_exponentialGenerator
    (hA : IsPickandsFunction A) :
    exponentialGenerator.archimaxCopula A hA = pickandsCopula A hA := by
  apply ext_cdf_two
  intro u v
  rw [cdf_archimaxCopula_two, cdf_pickandsCopula_two]
  rfl

/-- `A(t) = max(t, 1-t)` gives the upper Fréchet bound `M`, whatever the generator. -/
theorem archimaxCopula_max :
    g.archimaxCopula (fun t => max t (1 - t)) isPickandsFunction_max = comonotonic 2 := by
  apply ext_cdf_two
  intro u v
  rw [cdf_archimaxCopula_two, cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases h : u = 0 ∨ v = 0
  · rcases h with h | h <;> simp [h, u.2.1, v.2.1]
  push Not at h
  rw [g.archimaxCDF_of_ne h.1 h.2, pickandsTail_max (g.inv_nonneg u h.1) (g.inv_nonneg v h.2)]
  rcases le_total (g.invFun u) (g.invFun v) with huv | huv
  · rw [max_eq_right huv, g.right_inv v h.2]
    have := g.antitone (g.inv_nonneg u h.1) (g.inv_nonneg v h.2) huv
    rw [g.right_inv v h.2, g.right_inv u h.1] at this
    exact (min_eq_right this).symm
  · rw [max_eq_left huv, g.right_inv u h.1]
    have := g.antitone (g.inv_nonneg v h.2) (g.inv_nonneg u h.1) huv
    rw [g.right_inv v h.2, g.right_inv u h.1] at this
    exact (min_eq_left this).symm

/-! ### Order -/

/-- A pointwise larger Pickands function gives a pointwise smaller Archimax copula. -/
theorem archimaxCopula_lowerOrthantLE {B : ℝ → ℝ} (hA : IsPickandsFunction A)
    (hB : IsPickandsFunction B) (h : ∀ t ∈ Icc (0 : ℝ) 1, A t ≤ B t) :
    (g.archimaxCopula B hB).LowerOrthantLE (g.archimaxCopula A hA) := by
  intro u
  rw [cdf_archimaxCopula, cdf_archimaxCopula]
  by_cases h0 : u 0 = 0 ∨ u 1 = 0
  · simp [archimaxCDF, h0]
  push Not at h0
  rw [g.archimaxCDF_of_ne h0.1 h0.2, g.archimaxCDF_of_ne h0.1 h0.2]
  have hx := g.inv_nonneg _ h0.1
  have hy := g.inv_nonneg _ h0.2
  exact g.antitone (pickandsTail_nonneg hA hx hy) (pickandsTail_nonneg hB hx hy)
    (pickandsTail_le_of_le h hx hy)

/-- Every Archimax copula dominates the Archimedean copula of its generator. -/
theorem generator_lowerOrthantLE_archimaxCopula (hA : IsPickandsFunction A) :
    g.copula.LowerOrthantLE (g.archimaxCopula A hA) := by
  rw [← g.archimaxCopula_const_one]
  exact g.archimaxCopula_lowerOrthantLE hA isPickandsFunction_const_one hA.le_one

/-- The transpose of an Archimax copula is the Archimax copula of `t ↦ A(1 - t)`. -/
theorem transpose_archimaxCopula (hA : IsPickandsFunction A) :
    (g.archimaxCopula A hA).transpose = g.archimaxCopula (fun t => A (1 - t)) hA.comp_one_sub := by
  apply ext_cdf_two
  intro u v
  rw [cdf_transpose, cdf_archimaxCopula_two, cdf_archimaxCopula_two]
  by_cases h : u = 0 ∨ v = 0
  · rcases h with h | h <;> simp [h]
  push Not at h
  rw [g.archimaxCDF_of_ne h.2 h.1, g.archimaxCDF_of_ne h.1 h.2, pickandsTail_swap]

/-- The Capéraà–Fougères–Genest convention: with `A' (t) = A (1 - t)`, the copula is
`ψ((φ(u) + φ(v)) A'(φ(u) / (φ(u) + φ(v))))`. -/
theorem cdf_archimaxCopula_comp_one_sub (hA : IsPickandsFunction A) {u v : I} (hu : u ≠ 0)
    (hv : v ≠ 0) :
    (g.archimaxCopula (fun t => A (1 - t)) hA.comp_one_sub).cdf ![u, v] =
      g.toFun ((g.invFun u + g.invFun v) * A (g.invFun u / (g.invFun u + g.invFun v))) := by
  rw [cdf_archimaxCopula_two, g.archimaxCDF_of_ne hu hv, ← pickandsTail_swap, pickandsTail,
    add_comm (g.invFun v)]

/-! ### Diagonal, Blomqvist's beta and tail dependence -/

/-- The diagonal section `δ(t) = ψ(2A(1/2) φ(t))` for `t ≠ 0`. -/
theorem diagonal_archimaxCopula (hA : IsPickandsFunction A) {t : I} (ht : t ≠ 0) :
    (g.archimaxCopula A hA).diagonal t = g.toFun (2 * A (1 / 2) * g.invFun t) := by
  rw [diagonal, cdf_archimaxCopula_two, g.archimaxCDF_of_ne ht ht, pickandsTail]
  rcases eq_or_lt_of_le (g.inv_nonneg t ht) with h0 | h0
  · rw [← h0]
    simp
  · have hx : g.invFun t / (g.invFun t + g.invFun t) = 1 / 2 := by
      field_simp
      ring
    rw [hx]
    ring_nf

/-- **Blomqvist's beta** of an Archimax copula: `β = 4ψ(2A(1/2) φ(1/2)) - 1`. -/
theorem blomqvistBeta_archimaxCopula (hA : IsPickandsFunction A) :
    (g.archimaxCopula A hA).blomqvistBeta =
      4 * g.toFun (2 * A (1 / 2) * g.invFun unitHalf) - 1 := by
  have h := g.diagonal_archimaxCopula hA (t := unitHalf) (by
    intro h
    have := congrArg Subtype.val h
    norm_num [unitHalf] at this)
  rw [blomqvistBeta, ← h, diagonal]

/-- The left derivative of the Archimax diagonal at one: if
`(1 - ψ(κx)) / (1 - ψ(x)) → m` as `x → 0+` with `κ = 2A(1/2)`, then `δ'(1⁻) = m`. -/
theorem hasDerivWithinAt_diagonal_archimaxCopula_one (hA : IsPickandsFunction A) {m : ℝ}
    (h : Tendsto (fun x => (1 - g.toFun (2 * A (1 / 2) * x)) / (1 - g.toFun x)) (𝓝[>] 0)
      (𝓝 m)) :
    HasDerivWithinAt (fun x => (g.archimaxCopula A hA).diagonal (projIcc 0 1 zero_le_one x)) m
      (Icc 0 1) 1 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine (h.comp g.tendsto_invFunReal_one).congr' ?_
  have hpos : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), x ∈ Icc (0 : ℝ) 1 \ {1} := self_mem_nhdsWithin
    have h2 : ∀ᶠ x in 𝓝[Icc 0 1 \ {1}] (1 : ℝ), (0 : ℝ) < x :=
      nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)
    filter_upwards [h1, h2] with x hx hx0
    exact ⟨hx0, lt_of_le_of_ne hx.1.2 hx.2⟩
  filter_upwards [hpos] with x hx
  let u : I := ⟨x, hx.1.le, hx.2.le⟩
  have hu : u ≠ 0 := fun h => hx.1.ne' (congrArg Subtype.val h)
  have hxu : g.invFunReal x = g.invFun u := g.invFunReal_coe u
  have hpx : projIcc 0 1 zero_le_one x = u := projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩
  have hp1 : projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := projIcc_right zero_le_one
  have hd1 : (g.archimaxCopula A hA).diagonal 1 = 1 := by
    rw [diagonal, cdf_archimaxCopula_two, g.archimaxCDF_one_left hA]
    rfl
  simp only [Function.comp_apply, slope_def_field, hxu, hpx, hp1, hd1,
    g.diagonal_archimaxCopula hA hu]
  have hr : g.toFun (g.invFun u) = x := g.right_inv u hu
  rw [hr]
  have hn : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.ne
  have hn' : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.ne'
  field_simp
  ring

/-- **Upper tail dependence of Archimax copulas** (Capéraà–Fougères–Genest 2000):
`λ_U = 2 - lim_{x → 0+} (1 - ψ(2A(1/2) x)) / (1 - ψ(x))` whenever the limit exists. -/
theorem hasUpperTailDependence_archimaxCopula_of_tendsto (hA : IsPickandsFunction A) {m : ℝ}
    (h : Tendsto (fun x => (1 - g.toFun (2 * A (1 / 2) * x)) / (1 - g.toFun x)) (𝓝[>] 0)
      (𝓝 m)) :
    (g.archimaxCopula A hA).HasUpperTailDependence (2 - m) :=
  hasUpperTailDependence_of_hasDerivWithinAt (fun t => by rw [projIcc_val])
    (g.hasDerivWithinAt_diagonal_archimaxCopula_one hA h)

/-- If `ψ` has a finite nonzero right derivative at `0`, then
`(1 - ψ(κx)) / (1 - ψ(x)) → κ` as `x → 0+` for every `κ > 0`. -/
theorem tendsto_archimaxRatio_of_hasDerivWithinAt {d κ : ℝ}
    (hd : HasDerivWithinAt g.toFun d (Ici 0) 0) (hd0 : d ≠ 0) (hκ : 0 < κ) :
    Tendsto (fun x => (1 - g.toFun (κ * x)) / (1 - g.toFun x)) (𝓝[>] 0) (𝓝 κ) := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope.1 hd)
  have hfilt : 𝓝[Ici (0 : ℝ) \ {0}] (0 : ℝ) = 𝓝[>] 0 := by
    congr 1
    ext x
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
  rw [hfilt] at hs
  have h2 : Tendsto (fun x : ℝ => κ * x) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => κ * x) (𝓝 0) (𝓝 (κ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos hκ (show (0 : ℝ) < x from hx)
  have hA := (hs.comp h2).const_mul κ
  have hq := hA.div hs hd0
  have hlim : κ * d / d = κ := by field_simp
  rw [hlim] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [Pi.div_apply, Function.comp_apply]
  rw [slope_def_field, slope_def_field, sub_zero, sub_zero, g.toFun_zero]
  by_cases hB : g.toFun x - 1 = 0
  · have hB' : 1 - g.toFun x = 0 := by linarith
    rw [hB, hB', zero_div, div_zero, div_zero]
  · have hB' : 1 - g.toFun x ≠ 0 := fun h => hB (by linarith)
    field_simp
    ring

/-- **Upper tail coefficient `λ_U = 2(1 - A(1/2))`** of an Archimax copula whose inverse
generator has a finite nonzero right derivative at `0` (equivalently `φ'(1⁻) ≠ 0`; the
Archimedean part then has no upper tail dependence and the tail behaviour is that of the
extreme-value attractor `C_A`, Capéraà–Fougères–Genest 2000, Section 4). -/
theorem hasUpperTailDependence_archimaxCopula_of_hasDerivWithinAt (hA : IsPickandsFunction A)
    {d : ℝ} (hd : HasDerivWithinAt g.toFun d (Ici 0) 0) (hd0 : d ≠ 0) :
    (g.archimaxCopula A hA).HasUpperTailDependence (2 * (1 - A (1 / 2))) := by
  have hκ : 0 < 2 * A (1 / 2) := by
    have := hA.half_le (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    linarith
  have h := g.hasUpperTailDependence_archimaxCopula_of_tendsto hA
    (g.tendsto_archimaxRatio_of_hasDerivWithinAt hd hd0 hκ)
  convert h using 1
  ring

/-- The lower tail ratio along the generator: `δ(t) / t = ψ(2A(1/2) φ(t)) / ψ(φ(t))`. -/
theorem lowerTailRatio_archimaxCopula (hA : IsPickandsFunction A) {t : I} (ht : t ≠ 0) :
    (g.archimaxCopula A hA).lowerTailRatio t =
      g.toFun (2 * A (1 / 2) * g.invFun t) / g.toFun (g.invFun t) := by
  rw [lowerTailRatio, g.diagonal_archimaxCopula hA ht, g.right_inv t ht]

/-- **Lower tail dependence of Archimax copulas** with a strict generator:
`λ_L = lim_{x → ∞} ψ(2A(1/2) x) / ψ(x)` whenever this limit exists. -/
theorem hasLowerTailDependence_archimaxCopula_of_tendsto (hA : IsPickandsFunction A)
    (hg : g.IsStrict) {l : ℝ}
    (h : Tendsto (fun x => g.toFun (2 * A (1 / 2) * x) / g.toFun x) atTop (𝓝 l)) :
    (g.archimaxCopula A hA).HasLowerTailDependence l := by
  unfold HasLowerTailDependence
  refine (h.comp hg.tendsto_invFun_atTop).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (g.lowerTailRatio_archimaxCopula hA (ne_of_gt ht)).symm

end BivariateGenerator

end ProbabilityTheory.Copula
