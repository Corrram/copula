/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.FGM
import Copula.Dependence.Basic
import Copula.Rectangle
import Copula.Rank.Basic
import Copula.Reflection.Bivariate

/-!
# Copulas with quadratic sections

A bivariate copula has *quadratic sections in `u`* if every vertical section `u ↦ C(u, v)` is a
polynomial of degree at most two (Nelsen, *An Introduction to Copulas*, 2nd ed., §3.2.5). The
boundary conditions force the form

`C(u, v) = u v + ψ(v) u (1 - u)`,

and this function is a copula if and only if `ψ(0) = ψ(1) = 0` and `ψ` is `1`-Lipschitz
(`IsQuadraticSectionFunction`).

Main results:

* `quadraticSectionCopula ψ hψ` with `cdf_quadraticSectionCopula`;
* `exists_copula_quadraticSection_iff`: the formula `u v + ψ(v) u (1 - u)` is the CDF of a copula
  if and only if `ψ` satisfies the two conditions (both directions);
* `eq_quadraticSectionCopula_of_quadratic`: a copula whose vertical sections are quadratic
  polynomials `a(v) u² + b(v) u + c(v)` is `quadraticSectionCopula (-a)`;
* `quadraticSectionCopula_eq_fgm_of_transpose`, `quadratic_sections_both_iff_fgm`: a copula has
  quadratic sections in both `u` and `v` if and only if it is a Farlie–Gumbel–Morgenstern copula.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The admissibility conditions for the coefficient function of a copula with quadratic sections
in `u`: `ψ(0) = ψ(1) = 0` and `ψ` is `1`-Lipschitz. -/
structure IsQuadraticSectionFunction (ψ : I → ℝ) : Prop where
  /-- Vanishing at zero. -/
  zero : ψ 0 = 0
  /-- Vanishing at one. -/
  one : ψ 1 = 0
  /-- The Lipschitz condition. -/
  lipschitz : ∀ s t : I, |ψ t - ψ s| ≤ |(t : ℝ) - s|

/-- The function `u v + ψ(v) u (1 - u)`. -/
def quadraticSectionCDF (ψ : I → ℝ) (u v : I) : ℝ :=
  (u : ℝ) * v + ψ v * ((u : ℝ) * (1 - u))

private theorem quadraticSection_rect (ψ : I → ℝ) (a b c e : I) :
    quadraticSectionCDF ψ b e - quadraticSectionCDF ψ a e - quadraticSectionCDF ψ b c +
        quadraticSectionCDF ψ a c =
      ((b : ℝ) - a) * (((e : ℝ) - c) + (ψ e - ψ c) * (1 - a - b)) := by
  unfold quadraticSectionCDF; ring

theorem IsQuadraticSectionFunction.isClassical {ψ : I → ℝ} (hψ : IsQuadraticSectionFunction ψ) :
    IsClassical (fun u : Fin 2 → I => quadraticSectionCDF ψ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (quadraticSectionCDF ψ)
  · intro v; simp [quadraticSectionCDF]
  · intro u; simp [quadraticSectionCDF, hψ.zero]
  · intro v; simp [quadraticSectionCDF]
  · intro u; simp [quadraticSectionCDF, hψ.one]
  · intro a b c e hab hce
    rw [quadraticSection_rect]
    have hab' : (a : ℝ) ≤ b := hab
    have hce' : (c : ℝ) ≤ e := hce
    have h1 : |1 - (a : ℝ) - b| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [a.property.1, a.property.2, b.property.1, b.property.2]
    have h2 : |(ψ e - ψ c) * (1 - a - b)| ≤ (e : ℝ) - c := by
      rw [abs_mul]
      calc |ψ e - ψ c| * |1 - (a : ℝ) - b| ≤ |ψ e - ψ c| * 1 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ ≤ (e : ℝ) - c := by
          rw [mul_one]
          exact (hψ.lipschitz c e).trans_eq (abs_of_nonneg (by linarith))
    have h3 := neg_abs_le ((ψ e - ψ c) * (1 - a - b))
    exact mul_nonneg (by linarith) (by linarith)

/-- The copula `u v + ψ(v) u (1 - u)` with quadratic sections in `u`. -/
noncomputable def quadraticSectionCopula (ψ : I → ℝ) (hψ : IsQuadraticSectionFunction ψ) :
    Copula 2 :=
  ofClassical _ hψ.isClassical

@[simp] theorem cdf_quadraticSectionCopula (ψ : I → ℝ) (hψ : IsQuadraticSectionFunction ψ)
    (u : Fin 2 → I) :
    (quadraticSectionCopula ψ hψ).cdf u = quadraticSectionCDF ψ (u 0) (u 1) :=
  congrFun (cdf_ofClassical _ hψ.isClassical) u

theorem cdf_quadraticSectionCopula_two (ψ : I → ℝ) (hψ : IsQuadraticSectionFunction ψ)
    (u v : I) : (quadraticSectionCopula ψ hψ).cdf ![u, v] = quadraticSectionCDF ψ u v := by
  simp

/-- Nonnegative bivariate rectangle increments of a copula CDF. -/
theorem cdf_rectangle_nonneg (C : Copula 2) {a b c e : I} (hab : a ≤ b) (hce : c ≤ e) :
    0 ≤ C.cdf ![b, e] - C.cdf ![a, e] - C.cdf ![b, c] + C.cdf ![a, c] := by
  have hle : (![a, c] : Fin 2 → I) ≤ ![b, e] := by
    intro i; fin_cases i
    · exact hab
    · exact hce
  have h := C.rectangleIncrement_cdf_nonneg ![a, c] ![b, e] hle
  rw [rectangleIncrement_two] at h
  simpa using h

/-- If `x (1 - ε) ≤ y` for all `ε ∈ (0, 1]` and `0 ≤ y`, then `x ≤ y`. -/
private theorem le_of_forall_mul_one_sub {x y : ℝ} (hy : 0 ≤ y)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → x * (1 - ε) ≤ y) : x ≤ y := by
  by_contra hxy
  push Not at hxy
  have hx : 0 < x := hy.trans_lt hxy
  have hε1 : 0 < (x - y) / (2 * x) := div_pos (by linarith) (by linarith)
  have hε2 : (x - y) / (2 * x) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have := h _ hε1 hε2
  have e : x * (1 - (x - y) / (2 * x)) = (x + y) / 2 := by
    field_simp; ring
  rw [e] at this
  linarith

/-- **Nelsen §3.2.5: characterization of copulas with quadratic sections.** The function
`u v + ψ(v) u (1 - u)` is the CDF of a copula if and only if `ψ(0) = ψ(1) = 0` and
`|ψ(t) - ψ(s)| ≤ |t - s|`. -/
theorem exists_copula_quadraticSection_iff (ψ : I → ℝ) :
    (∃ C : Copula 2, ∀ u v : I, C.cdf ![u, v] = quadraticSectionCDF ψ u v) ↔
      IsQuadraticSectionFunction ψ := by
  refine ⟨fun ⟨C, hC⟩ => ?_, fun hψ => ⟨_, cdf_quadraticSectionCopula_two ψ hψ⟩⟩
  have hh : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · have h := hC unitHalf 0
    rw [C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl] at h
    simp only [quadraticSectionCDF, hh, Set.Icc.coe_zero] at h
    linarith
  · have h := hC unitHalf 1
    rw [cdf_two_one_right] at h
    simp only [quadraticSectionCDF, hh, Set.Icc.coe_one] at h
    linarith
  · -- Lipschitz: rectangles `[0, ε] × [s, t]` and `[1 - ε, 1] × [s, t]`.
    intro s t
    have key : ∀ c e : I, c ≤ e → |ψ e - ψ c| ≤ (e : ℝ) - c := by
      intro c e hce
      have hce' : (c : ℝ) ≤ e := hce
      apply le_of_forall_mul_one_sub (by linarith)
      intro ε hε0 hε1
      let a₀ : I := ⟨ε, hε0.le, hε1⟩
      let b₀ : I := ⟨1 - ε, by linarith, by linarith⟩
      have h1 := C.cdf_rectangle_nonneg (unitInterval.nonneg' (t := a₀)) hce
      have h2 := C.cdf_rectangle_nonneg (unitInterval.le_one' (t := b₀)) hce
      rw [hC, hC, hC, hC, quadraticSection_rect] at h1 h2
      simp only [Set.Icc.coe_zero, Set.Icc.coe_one] at h1 h2
      have ha₀ : ((a₀ : I) : ℝ) = ε := rfl
      have hb₀ : ((b₀ : I) : ℝ) = 1 - ε := rfl
      rw [ha₀] at h1
      rw [hb₀] at h2
      have h1' : 0 ≤ ((e : ℝ) - c) + (ψ e - ψ c) * (1 - ε) := by
        have := (mul_nonneg_iff_of_pos_left hε0).mp (by linarith : 0 ≤ ε * (((e : ℝ) - c) +
          (ψ e - ψ c) * (1 - 0 - ε)))
        linarith
      have h2' : 0 ≤ ((e : ℝ) - c) - (ψ e - ψ c) * (1 - ε) := by
        have := (mul_nonneg_iff_of_pos_left hε0).mp (by nlinarith : 0 ≤ ε * (((e : ℝ) - c) +
          (ψ e - ψ c) * (1 - (1 - ε) - 1)))
        linarith
      rcases le_total 0 (ψ e - ψ c) with hd | hd
      · rw [abs_of_nonneg hd]; linarith
      · rw [abs_of_nonpos hd]; linarith
    rcases le_total s t with hst | hts
    · exact (key s t hst).trans_eq (abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))).symm
    · rw [abs_sub_comm, abs_sub_comm (t : ℝ)]
      exact (key t s hts).trans_eq (abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ s from hts))).symm

/-- **Copulas with quadratic sections in `u`** (Nelsen §3.2.5): if every vertical section of `C`
is a quadratic polynomial `u ↦ a(v) u² + b(v) u + c(v)`, then `C(u,v) = u v + ψ(v) u (1 - u)` with
`ψ = -a`, and `ψ` satisfies the admissibility conditions. -/
theorem eq_quadraticSectionCopula_of_quadratic (C : Copula 2) (a b c : I → ℝ)
    (h : ∀ u v : I, C.cdf ![u, v] = a v * (u : ℝ) ^ 2 + b v * u + c v) :
    ∃ hψ : IsQuadraticSectionFunction (fun v => -a v),
      C = quadraticSectionCopula (fun v => -a v) hψ := by
  have hform : ∀ u v : I, C.cdf ![u, v] = quadraticSectionCDF (fun v => -a v) u v := by
    intro u v
    have h0 := h 0 v
    have h1 := h 1 v
    rw [C.cdf_eq_zero_of_coord_eq_zero _ 0 rfl] at h0
    rw [cdf_two_one_left] at h1
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one] at h0 h1
    rw [h u v, quadraticSectionCDF]
    have hc : c v = 0 := by linarith
    have hb : b v = v - a v := by linarith
    rw [hc, hb]
    ring
  have hψ : IsQuadraticSectionFunction (fun v => -a v) :=
    (exists_copula_quadraticSection_iff _).mp ⟨C, hform⟩
  refine ⟨hψ, ext_cdf_two fun u v => ?_⟩
  rw [hform, cdf_quadraticSectionCopula_two]

/-- The FGM copula has quadratic sections, with `ψ(v) = θ v (1 - v)`. -/
theorem fgmCDF_eq_quadraticSectionCDF (θ : ℝ) (u v : I) :
    fgmCDF θ u v = quadraticSectionCDF (fun v => θ * ((v : ℝ) * (1 - v))) u v := by
  unfold fgmCDF quadraticSectionCDF; ring

/-- **Quadratic sections in both variables force the FGM family** (Nelsen §3.2.5): if the
copula `u v + ψ(v) u (1 - u)` also equals `u v + φ(u) v (1 - v)` for some `φ`, then it is the FGM
copula with parameter `θ = 4 φ(1/2)` and `|θ| ≤ 1`. -/
theorem quadraticSectionCopula_eq_fgm {ψ φ : I → ℝ} (hψ : IsQuadraticSectionFunction ψ)
    (h : ∀ u v : I, quadraticSectionCDF ψ u v = (u : ℝ) * v + φ u * ((v : ℝ) * (1 - v))) :
    ∃ hθ : |4 * φ unitHalf| ≤ 1, quadraticSectionCopula ψ hψ = fgm (4 * φ unitHalf) hθ := by
  have hh : ((unitHalf : I) : ℝ) = 1 / 2 := rfl
  set θ := 4 * φ unitHalf with hθdef
  -- `ψ(v) = θ v (1 - v)`, read off at `u = 1/2`.
  have hψθ : ∀ v : I, ψ v = θ * ((v : ℝ) * (1 - v)) := by
    intro v
    have := h unitHalf v
    simp only [quadraticSectionCDF, hh] at this
    rw [hθdef]
    linarith
  have hθ : |θ| ≤ 1 := by
    -- From `|ψ(v) - ψ(0)| ≤ v` at `v = ε`: `|θ| (1 - ε) ≤ 1`.
    apply le_of_forall_mul_one_sub zero_le_one
    intro ε hε0 hε1
    let e₀ : I := ⟨ε, hε0.le, hε1⟩
    have hl := hψ.lipschitz 0 e₀
    have he₀ : ((e₀ : I) : ℝ) = ε := rfl
    rw [hψθ e₀, hψ.zero, he₀, Set.Icc.coe_zero, sub_zero, sub_zero, abs_of_pos hε0, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ ε * (1 - ε) by nlinarith)] at hl
    have : |θ| * (1 - ε) * ε ≤ 1 * ε := by
      linarith [show |θ| * (ε * (1 - ε)) = |θ| * (1 - ε) * ε by ring]
    exact le_of_mul_le_mul_right this hε0
  refine ⟨hθ, ext_cdf_two fun u v => ?_⟩
  rw [cdf_quadraticSectionCopula_two, cdf_fgm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fgmCDF_eq_quadraticSectionCDF]
  unfold quadraticSectionCDF
  rw [hψθ]

/-- **A copula has quadratic sections in both `u` and `v` iff it is an FGM copula**
(Nelsen §3.2.5). -/
theorem quadratic_sections_both_iff_fgm (C : Copula 2) :
    ((∃ ψ : I → ℝ, ∀ u v : I, C.cdf ![u, v] = quadraticSectionCDF ψ u v) ∧
        ∃ φ : I → ℝ, ∀ u v : I, C.cdf ![u, v] = (u : ℝ) * v + φ u * ((v : ℝ) * (1 - v))) ↔
      ∃ (θ : ℝ) (hθ : |θ| ≤ 1), C = fgm θ hθ := by
  constructor
  · rintro ⟨⟨ψ, hψC⟩, ⟨φ, hφC⟩⟩
    have hψ : IsQuadraticSectionFunction ψ := (exists_copula_quadraticSection_iff ψ).mp ⟨C, hψC⟩
    have hC : C = quadraticSectionCopula ψ hψ :=
      ext_cdf_two fun u v => by rw [hψC, cdf_quadraticSectionCopula_two]
    obtain ⟨hθ, hfgm⟩ := quadraticSectionCopula_eq_fgm hψ
      (φ := φ) fun u v => by rw [← hψC, hφC]
    exact ⟨_, hθ, hC.trans hfgm⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨⟨fun v => θ * ((v : ℝ) * (1 - v)), fun u v => ?_⟩,
      ⟨fun u => θ * ((u : ℝ) * (1 - u)), fun u v => ?_⟩⟩
    · rw [cdf_fgm]
      exact fgmCDF_eq_quadraticSectionCDF θ u v
    · rw [cdf_fgm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fgmCDF]
      ring

end ProbabilityTheory.Copula
