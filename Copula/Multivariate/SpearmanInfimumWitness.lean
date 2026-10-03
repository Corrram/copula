/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Multivariate.SpearmanInfimumThree
import Copula.Rearrangement

/-!
# An explicit trivariate copula with small Spearman's rho

We construct an explicit 3-copula `witness` with `∫ witness dΠ = 247/4500`, hence
`ρ₃(witness) = 8 · 247/4500 - 1 = -631/1125 ≈ -0.560889` (`multivariateSpearmanRho_witness`).
Together with the dual bound of `Copula.Multivariate.SpearmanInfimumThree` this gives

`-0.56158 ≤ inf { ρ₃(C) } ≤ -631/1125`   (`spearmanRho_three_infimum_bounds`).

## The construction

Let `T` be uniform on `[0, 1]` and

* `G(t) = 1 - t` on `[0, 1/3]`, `2t - 2/3` on `(1/3, 7/15]`, `t - 1/5` on `(7/15, 2/3]`,
  `2t - 4/3` on `(2/3, 4/5]`, `t - 1/3` on `(4/5, 1]` (`witnessReal`);
* `R(t) = t + 2/3 (mod 1)` (`rotReal`).

Both preserve the uniform distribution (`measurePreserving_witnessMap`,
`measurePreserving_rotMap`), so `U = (G(T), G(R(T)), G(R(R(T))))` has uniform marginals; its
law is `witness`. The support consists of six segments: the three *tail* segments
`(1 - y, 2y, 2y)`, `y ∈ [0, 2/15]` (and cyclic permutations), which are the exact tail structure
of the Bernard–Jiang–Wang minimizer with `c = 2/15`, and three *middle* segments on the cells of
`[4/15, 13/15]` cut into thirds, each comonotone in two coordinates and countermonotone in the
third. This is the optimum among such block designs with five cells per axis (found by linear
programming); the exact infimum `≈ -0.5615741` would require a joint mix in the middle.

The proof that `G` and `R` preserve Lebesgue measure checks `∫₀¹ ψ(G t) dt = ∫₀¹ ψ` for continuous
`ψ` piece by piece (affine change of variables), which identifies the image measure through
integrals of bounded continuous functions.
-/

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

namespace SpearmanInfimum

/-! ### Measure-preserving piecewise affine maps -/

/-- A real map `G` restricting to a self-map `g` of `[0,1]` preserves Lebesgue measure as soon
as `∫₀¹ ψ(G t) dt = ∫₀¹ ψ` for every continuous `ψ`. -/
theorem measurePreserving_of_integral_comp {g : I → I} {G : ℝ → ℝ} (hg : Measurable g)
    (hgG : ∀ t : I, (g t : ℝ) = G t)
    (hG : ∀ ψ : ℝ → ℝ, Continuous ψ → ∫ t in (0 : ℝ)..1, ψ (G t) = ∫ x in (0 : ℝ)..1, ψ x) :
    MeasurePreserving g volume volume := by
  refine ⟨hg, ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => ?_⟩
  rw [integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable]
  set ψ : ℝ → ℝ := fun x => φ (projIcc 0 1 zero_le_one x) with hψ
  have hψc : Continuous ψ := φ.continuous.comp continuous_projIcc
  have h1 : ∀ t : I, φ (g t) = ψ (G t) := by
    intro t
    simp only [hψ, ← hgG t, projIcc_val]
  have h2 : ∀ t : I, φ t = ψ t := by
    intro t
    simp only [hψ, projIcc_val]
  simp only [h1, h2]
  rw [integral_unitInterval (fun t => ψ (G t)), integral_unitInterval ψ]
  exact hG ψ hψc

/-- The rotation `R(t) = t + 2/3 (mod 1)` on `[0, 1]`. -/
noncomputable def rotReal (t : ℝ) : ℝ := if t ≤ 1 / 3 then t + 2 / 3 else t - 1 / 3

/-- The piecewise affine map `G`. -/
noncomputable def witnessReal (t : ℝ) : ℝ :=
  if t ≤ 1 / 3 then 1 - t else if t ≤ 7 / 15 then 2 * t - 2 / 3 else if t ≤ 2 / 3 then t - 1 / 5
  else if t ≤ 4 / 5 then 2 * t - 4 / 3 else t - 1 / 3

theorem measurable_rotReal : Measurable rotReal :=
  Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

theorem measurable_witnessReal : Measurable witnessReal :=
  Measurable.ite measurableSet_Iic (by fun_prop) (Measurable.ite measurableSet_Iic (by fun_prop)
    (Measurable.ite measurableSet_Iic (by fun_prop)
      (Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop))))

theorem rotReal_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : rotReal t ∈ Icc (0 : ℝ) 1 := by
  unfold rotReal
  split_ifs <;> constructor <;> linarith [ht.1, ht.2]

theorem witnessReal_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : witnessReal t ∈ Icc (0 : ℝ) 1 := by
  unfold witnessReal
  split_ifs <;> constructor <;> linarith [ht.1, ht.2]

/-- Integral of `ψ` composed with an affine map on a piece where `G` is affine. -/
private theorem integral_piece {G : ℝ → ℝ} (ψ : ℝ → ℝ) {a b α β : ℝ} (hab : a ≤ b) (hα : α ≠ 0)
    (hG : ∀ t ∈ Ioc a b, G t = α * t + β) :
    ∫ t in a..b, ψ (G t) = α⁻¹ * ∫ x in (α * a + β)..(α * b + β), ψ x := by
  rw [← smul_eq_mul, ← intervalIntegral.integral_comp_mul_add ψ hα β]
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [uIoc_of_le hab] at ht
  rw [hG t ht]

private theorem intervalIntegrable_piece {G : ℝ → ℝ} {ψ : ℝ → ℝ} (hψ : Continuous ψ) {a b α β : ℝ}
    (hab : a ≤ b) (hG : ∀ t ∈ Ioc a b, G t = α * t + β) :
    IntervalIntegrable (fun t => ψ (G t)) volume a b := by
  have hc : Continuous (fun t => ψ (α * t + β)) := by fun_prop
  refine IntervalIntegrable.congr ?_ (hc.intervalIntegrable a b)
  intro t ht
  rw [uIoc_of_le hab] at ht
  simp [hG t ht]

theorem integral_comp_rotReal (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    ∫ t in (0 : ℝ)..1, ψ (rotReal t) = ∫ x in (0 : ℝ)..1, ψ x := by
  have h1 : ∀ t ∈ Ioc (0 : ℝ) (1 / 3), rotReal t = 1 * t + 2 / 3 := by
    intro t ht; simp only [rotReal, ht.2, ↓reduceIte]; ring
  have h2 : ∀ t ∈ Ioc (1 / 3 : ℝ) 1, rotReal t = 1 * t + (-1 / 3) := by
    intro t ht; simp only [rotReal, not_le.2 ht.1, ↓reduceIte]; ring
  have hc := fun a b => hψ.intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_piece hψ (by norm_num) h1) (intervalIntegrable_piece hψ (by norm_num) h2),
    integral_piece ψ (by norm_num) one_ne_zero h1, integral_piece ψ (by norm_num) one_ne_zero h2]
  norm_num
  rw [add_comm, intervalIntegral.integral_add_adjacent_intervals (hc _ _) (hc _ _)]

theorem integral_comp_witnessReal (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    ∫ t in (0 : ℝ)..1, ψ (witnessReal t) = ∫ x in (0 : ℝ)..1, ψ x := by
  have h1 : ∀ t ∈ Ioc (0 : ℝ) (1 / 3), witnessReal t = -1 * t + 1 := by
    intro t ht; simp only [witnessReal, ht.2, ↓reduceIte]; ring
  have h2 : ∀ t ∈ Ioc (1 / 3 : ℝ) (7 / 15), witnessReal t = 2 * t + (-2 / 3) := by
    intro t ht
    simp only [witnessReal, not_le.2 ht.1, ht.2, ↓reduceIte]; ring
  have h3 : ∀ t ∈ Ioc (7 / 15 : ℝ) (2 / 3), witnessReal t = 1 * t + (-1 / 5) := by
    intro t ht
    simp only [witnessReal, (not_le.2 ht.1), (not_le.2 (by linarith [ht.1] :
      (1 / 3 : ℝ) < t)), ht.2, ↓reduceIte]; ring
  have h4 : ∀ t ∈ Ioc (2 / 3 : ℝ) (4 / 5), witnessReal t = 2 * t + (-4 / 3) := by
    intro t ht
    simp only [witnessReal, (not_le.2 ht.1), (not_le.2 (by linarith [ht.1] :
      (1 / 3 : ℝ) < t)), (not_le.2 (by linarith [ht.1] : (7 / 15 : ℝ) < t)), ht.2, ↓reduceIte]
    ring
  have h5 : ∀ t ∈ Ioc (4 / 5 : ℝ) 1, witnessReal t = 1 * t + (-1 / 3) := by
    intro t ht
    simp only [witnessReal, (not_le.2 ht.1), (not_le.2 (by linarith [ht.1] :
      (1 / 3 : ℝ) < t)), (not_le.2 (by linarith [ht.1] : (7 / 15 : ℝ) < t)),
      (not_le.2 (by linarith [ht.1] : (2 / 3 : ℝ) < t)), ↓reduceIte]
    ring
  have hc := fun a b => hψ.intervalIntegrable (μ := volume) a b
  have i1 := intervalIntegrable_piece hψ (by norm_num) h1
  have i2 := intervalIntegrable_piece hψ (by norm_num) h2
  have i3 := intervalIntegrable_piece hψ (by norm_num) h3
  have i4 := intervalIntegrable_piece hψ (by norm_num) h4
  have i5 := intervalIntegrable_piece hψ (by norm_num) h5
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 ((i2.trans i3).trans (i4.trans i5)),
    ← intervalIntegral.integral_add_adjacent_intervals (i2.trans i3) (i4.trans i5),
    ← intervalIntegral.integral_add_adjacent_intervals i2 i3,
    ← intervalIntegral.integral_add_adjacent_intervals i4 i5,
    integral_piece ψ (by norm_num) (by norm_num) h1,
    integral_piece ψ (by norm_num) (by norm_num) h2,
    integral_piece ψ (by norm_num) (by norm_num) h3,
    integral_piece ψ (by norm_num) (by norm_num) h4,
    integral_piece ψ (by norm_num) (by norm_num) h5]
  norm_num
  rw [intervalIntegral.integral_symm (2 / 3) 1]
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hc 0 (4 / 15)) (hc (4 / 15) (7 / 15))
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hc 0 (7 / 15)) (hc (7 / 15) (2 / 3))
  have e3 := intervalIntegral.integral_add_adjacent_intervals (hc 0 (2 / 3)) (hc (2 / 3) 1)
  linarith

/-- `R` as a self-map of `[0, 1]`. -/
noncomputable def rotMap (t : I) : I := projIcc 0 1 zero_le_one (rotReal t)

/-- `G` as a self-map of `[0, 1]`. -/
noncomputable def witnessMap (t : I) : I := projIcc 0 1 zero_le_one (witnessReal t)

theorem coe_rotMap (t : I) : (rotMap t : ℝ) = rotReal t := by
  rw [rotMap, projIcc_of_mem _ (rotReal_mem t.2)]

theorem coe_witnessMap (t : I) : (witnessMap t : ℝ) = witnessReal t := by
  rw [witnessMap, projIcc_of_mem _ (witnessReal_mem t.2)]

theorem measurePreserving_rotMap : MeasurePreserving rotMap volume volume :=
  measurePreserving_of_integral_comp
    (continuous_projIcc.measurable.comp (measurable_rotReal.comp measurable_subtype_coe))
    coe_rotMap integral_comp_rotReal

theorem measurePreserving_witnessMap : MeasurePreserving witnessMap volume volume :=
  measurePreserving_of_integral_comp
    (continuous_projIcc.measurable.comp (measurable_witnessReal.comp measurable_subtype_coe))
    coe_witnessMap integral_comp_witnessReal

/-- The three coordinate maps `G`, `G ∘ R`, `G ∘ R ∘ R`. -/
noncomputable def witnessCoord : Fin 3 → I → I :=
  ![witnessMap, witnessMap ∘ rotMap, witnessMap ∘ rotMap ∘ rotMap]

theorem measurePreserving_witnessCoord (i : Fin 3) :
    MeasurePreserving (witnessCoord i) volume volume := by
  fin_cases i
  · exact measurePreserving_witnessMap
  · exact measurePreserving_witnessMap.comp measurePreserving_rotMap
  · exact (measurePreserving_witnessMap.comp measurePreserving_rotMap).comp
      measurePreserving_rotMap

/-- **The explicit witness copula**: the law of `(G(T), G(R(T)), G(R(R(T))))`, `T` uniform. -/
noncomputable def witness : Copula 3 :=
  (comonotonic 3).rearrange witnessCoord measurePreserving_witnessCoord

/-! ### The value of `∫ witness dΠ` -/

/-- The integrand `F(t) = (1 - G t)(1 - G(R t))(1 - G(R(R t)))`. -/
noncomputable def witnessIntegrand (t : ℝ) : ℝ :=
  (1 - witnessReal t) * (1 - witnessReal (rotReal t)) * (1 - witnessReal (rotReal (rotReal t)))

theorem integral_witness_eq :
    ∫ u, witness.cdf u ∂(independence 3).toMeasure = ∫ t in (0 : ℝ)..1, witnessIntegrand t := by
  have hX : Measurable (fun x : Fin 3 → I => fun i => witnessCoord i (x i)) :=
    Measurable.of_eval fun i =>
      (measurePreserving_witnessCoord i).measurable.comp (measurable_pi_apply i)
  have hP : Continuous (fun y : Fin 3 → I => ∏ i, (1 - (y i : ℝ))) :=
    continuous_finsetProd _ fun i _ =>
      continuous_const.sub (continuous_subtype_val.comp (continuous_apply i))
  have hF : Measurable (fun x : Fin 3 → I =>
      ∏ i, (1 - (((fun i => witnessCoord i (x i)) i : I) : ℝ))) := hP.measurable.comp hX
  have hD : Measurable (fun u : I => fun _ : Fin 3 => u) :=
    Measurable.of_eval fun _ => measurable_id
  rw [integral_cdf_independence_eq_prod, witness, toMeasure_rearrange,
    integral_map hX.aemeasurable hP.aestronglyMeasurable, toMeasure_comonotonic,
    integral_map hD.aemeasurable (hF.aestronglyMeasurable (μ := _)),
    ← integral_unitInterval witnessIntegrand]
  congr 1
  funext t
  simp only [Fin.prod_univ_three, witnessCoord, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Function.comp,
    coe_witnessMap, coe_rotMap, witnessIntegrand]

/-- Integral of a cubic polynomial. -/
private theorem integral_cubic (a b c₀ c₁ c₂ c₃ : ℝ) :
    ∫ t in a..b, (c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) =
      c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 + c₂ * (b ^ 3 - a ^ 3) / 3 +
        c₃ * (b ^ 4 - a ^ 4) / 4 := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt
      (fun t : ℝ => c₀ * t + c₁ * t ^ 2 / 2 + c₂ * t ^ 3 / 3 + c₃ * t ^ 4 / 4)
      (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) x := by
    intro x _
    have := ((((hasDerivAt_id x).const_mul c₀).add (((hasDerivAt_pow 2 x).const_mul c₁).div_const
      2)).add (((hasDerivAt_pow 3 x).const_mul c₂).div_const 3)).add
      (((hasDerivAt_pow 4 x).const_mul c₃).div_const 4)
    convert this using 1
    · funext t
      simp only [Pi.add_apply, id]
    · norm_num
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
    apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- On a piece `(a, b]` where the integrand is the cubic `c₀ + c₁ t + c₂ t² + c₃ t³`. -/
private theorem integral_witnessIntegrand_piece {a b c₀ c₁ c₂ c₃ : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Ioc a b, witnessIntegrand t = c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) :
    IntervalIntegrable witnessIntegrand volume a b ∧
      ∫ t in a..b, witnessIntegrand t = c₀ * (b - a) + c₁ * (b ^ 2 - a ^ 2) / 2 +
        c₂ * (b ^ 3 - a ^ 3) / 3 + c₃ * (b ^ 4 - a ^ 4) / 4 := by
  have heq : EqOn (fun t => c₀ + c₁ * t + c₂ * t ^ 2 + c₃ * t ^ 3) witnessIntegrand (uIoc a b) := by
    intro t ht
    rw [uIoc_of_le hab] at ht
    exact (h t ht).symm
  refine ⟨IntervalIntegrable.congr heq (by apply Continuous.intervalIntegrable; fun_prop), ?_⟩
  rw [← integral_cubic]
  exact intervalIntegral.integral_congr_ae
    (Filter.Eventually.of_forall fun t ht => (heq ht).symm)

private theorem r1 {x : ℝ} (h : x ≤ 1 / 3) : rotReal x = x + 2 / 3 := by
  simp only [rotReal, h, ↓reduceIte]

private theorem r2 {x : ℝ} (h : 1 / 3 < x) : rotReal x = x - 1 / 3 := by
  simp only [rotReal, not_le.2 h, ↓reduceIte]

private theorem w1 {x : ℝ} (h : x ≤ 1 / 3) : witnessReal x = 1 - x := by
  simp only [witnessReal, h, ↓reduceIte]

private theorem w2 {x : ℝ} (h : 1 / 3 < x) (h' : x ≤ 7 / 15) : witnessReal x = 2 * x - 2 / 3 := by
  simp only [witnessReal, not_le.2 h, h', ↓reduceIte]

private theorem w3 {x : ℝ} (h : 7 / 15 < x) (h' : x ≤ 2 / 3) : witnessReal x = x - 1 / 5 := by
  simp only [witnessReal, not_le.2 (by linarith : (1 / 3 : ℝ) < x), not_le.2 h, h', ↓reduceIte]

private theorem w4 {x : ℝ} (h : 2 / 3 < x) (h' : x ≤ 4 / 5) : witnessReal x = 2 * x - 4 / 3 := by
  simp only [witnessReal, not_le.2 (by linarith : (1 / 3 : ℝ) < x),
    not_le.2 (by linarith : (7 / 15 : ℝ) < x), not_le.2 h, h', ↓reduceIte]

private theorem w5 {x : ℝ} (h : 4 / 5 < x) : witnessReal x = x - 1 / 3 := by
  simp only [witnessReal, not_le.2 (by linarith : (1 / 3 : ℝ) < x),
    not_le.2 (by linarith : (7 / 15 : ℝ) < x), not_le.2 (by linarith : (2 / 3 : ℝ) < x),
    not_le.2 h, ↓reduceIte]

private theorem piece1 : IntervalIntegrable witnessIntegrand volume (0) (2 / 15) ∧
    ∫ t in (0 : ℝ)..(2 / 15), witnessIntegrand t = (0) * ((2 / 15) - (0)) +
      (1) * ((2 / 15) ^ 2 - (0) ^ 2) / 2 + (-4) * ((2 / 15) ^ 3 - (0) ^ 3) / 3 +
        (4) * ((2 / 15) ^ 4 - (0) ^ 4) / 4 := by
  apply integral_witnessIntegrand_piece (by norm_num)
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  simp only [witnessIntegrand]
  rw [r1 (by linarith), r2 (by linarith), w1 (by linarith), w4 (by linarith) (by linarith),
    w2 (by linarith) (by linarith)]
  ring

private theorem piece2 : IntervalIntegrable witnessIntegrand volume (2 / 15) (1 / 3) ∧
    ∫ t in (2 / 15 : ℝ)..(1 / 3), witnessIntegrand t = (0) * ((1 / 3) - (2 / 15)) +
      (26 / 45) * ((1 / 3) ^ 2 - (2 / 15) ^ 2) / 2 + (-23 / 15) * ((1 / 3) ^ 3 - (2 / 15) ^ 3) / 3 +
        (1) * ((1 / 3) ^ 4 - (2 / 15) ^ 4) / 4 := by
  apply integral_witnessIntegrand_piece (by norm_num)
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  simp only [witnessIntegrand]
  rw [r1 (by linarith), r2 (by linarith), w1 (by linarith), w5 (by linarith),
    w3 (by linarith) (by linarith)]
  ring

private theorem piece3 : IntervalIntegrable witnessIntegrand volume (1 / 3) (7 / 15) ∧
    ∫ t in (1 / 3 : ℝ)..(7 / 15), witnessIntegrand t = (-25 / 27) * ((7 / 15) - (1 / 3)) +
      (5) * ((7 / 15) ^ 2 - (1 / 3) ^ 2) / 2 + (-8) * ((7 / 15) ^ 3 - (1 / 3) ^ 3) / 3 +
        (4) * ((7 / 15) ^ 4 - (1 / 3) ^ 4) / 4 := by
  apply integral_witnessIntegrand_piece (by norm_num)
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  simp only [witnessIntegrand]
  rw [r2 (by linarith), r1 (by linarith), w2 (by linarith) (by linarith), w1 (by linarith),
    w4 (by linarith) (by linarith)]
  ring

private theorem piece4 : IntervalIntegrable witnessIntegrand volume (7 / 15) (2 / 3) ∧
    ∫ t in (7 / 15 : ℝ)..(2 / 3), witnessIntegrand t = (-2 / 5) * ((2 / 3) - (7 / 15)) +
      (29 / 15) * ((2 / 3) ^ 2 - (7 / 15) ^ 2) / 2 + (-38 / 15) * ((2 / 3) ^ 3 - (7 / 15) ^ 3) / 3 +
        (1) * ((2 / 3) ^ 4 - (7 / 15) ^ 4) / 4 := by
  apply integral_witnessIntegrand_piece (by norm_num)
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  simp only [witnessIntegrand]
  rw [r2 (by linarith), r1 (by linarith), w3 (by linarith) (by linarith), w1 (by linarith),
    w5 (by linarith)]
  ring

private theorem piece5 : IntervalIntegrable witnessIntegrand volume (2 / 3) (4 / 5) ∧
    ∫ t in (2 / 3 : ℝ)..(4 / 5), witnessIntegrand t = (-98 / 27) * ((4 / 5) - (2 / 3)) +
      (35 / 3) * ((4 / 5) ^ 2 - (2 / 3) ^ 2) / 2 + (-12) * ((4 / 5) ^ 3 - (2 / 3) ^ 3) / 3 +
        (4) * ((4 / 5) ^ 4 - (2 / 3) ^ 4) / 4 := by
  apply integral_witnessIntegrand_piece (by norm_num)
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  simp only [witnessIntegrand]
  rw [r2 (by linarith), r2 (by linarith), w4 (by linarith) (by linarith),
    w2 (by linarith) (by linarith), w1 (by linarith)]
  ring

private theorem piece6 : IntervalIntegrable witnessIntegrand volume (4 / 5) (1) ∧
    ∫ t in (4 / 5 : ℝ)..(1), witnessIntegrand t = (-184 / 135) * ((1) - (4 / 5)) +
      (178 / 45) * ((1) ^ 2 - (4 / 5) ^ 2) / 2 + (-53 / 15) * ((1) ^ 3 - (4 / 5) ^ 3) / 3 +
        (1) * ((1) ^ 4 - (4 / 5) ^ 4) / 4 := by
  apply integral_witnessIntegrand_piece (by norm_num)
  intro t ht
  obtain ⟨h1, h2⟩ := ht
  simp only [witnessIntegrand]
  rw [r2 (by linarith), r2 (by linarith), w5 (by linarith), w3 (by linarith) (by linarith),
    w1 (by linarith)]
  ring

/-- **`∫ witness dΠ = 247/4500`**. -/
theorem integral_cdf_witness :
    ∫ u, witness.cdf u ∂(independence 3).toMeasure = 247 / 4500 := by
  rw [integral_witness_eq]
  obtain ⟨i1, e1⟩ := piece1
  obtain ⟨i2, e2⟩ := piece2
  obtain ⟨i3, e3⟩ := piece3
  obtain ⟨i4, e4⟩ := piece4
  obtain ⟨i5, e5⟩ := piece5
  obtain ⟨i6, e6⟩ := piece6
  rw [← intervalIntegral.integral_add_adjacent_intervals i1
      (i2.trans (i3.trans (i4.trans (i5.trans i6)))),
    ← intervalIntegral.integral_add_adjacent_intervals i2 (i3.trans (i4.trans (i5.trans i6))),
    ← intervalIntegral.integral_add_adjacent_intervals i3 (i4.trans (i5.trans i6)),
    ← intervalIntegral.integral_add_adjacent_intervals i4 (i5.trans i6),
    ← intervalIntegral.integral_add_adjacent_intervals i5 i6, e1, e2, e3, e4, e5, e6]
  norm_num

/-- **`ρ₃(witness) = -631/1125 ≈ -0.560889`**. -/
theorem multivariateSpearmanRho_witness : witness.multivariateSpearmanRho = -631 / 1125 := by
  rw [multivariateSpearmanRho_three_eq, integral_cdf_witness]
  norm_num

/-- **Bounds for the infimum of trivariate Spearman's rho**: every 3-copula has
`ρ₃ ≥ -0.56158`, and the explicit copula `witness` has `ρ₃ = -631/1125 ≈ -0.560889`. -/
theorem spearmanRho_three_infimum_bounds :
    (∀ C : Copula 3, (-0.56158 : ℝ) ≤ C.multivariateSpearmanRho) ∧
      ∃ C : Copula 3, C.multivariateSpearmanRho = -631 / 1125 :=
  ⟨neg_056158_le_multivariateSpearmanRho_three, witness, multivariateSpearmanRho_witness⟩

/-- The infimum of `ρ₃` over all 3-copulas lies in `[-0.56158, -631/1125]`. -/
theorem sInf_multivariateSpearmanRho_three_mem :
    sInf (Set.range fun C : Copula 3 => C.multivariateSpearmanRho) ∈
      Icc (-0.56158 : ℝ) (-631 / 1125) := by
  have hbdd : BddBelow (Set.range fun C : Copula 3 => C.multivariateSpearmanRho) :=
    ⟨-0.56158, by rintro _ ⟨C, rfl⟩; exact neg_056158_le_multivariateSpearmanRho_three C⟩
  constructor
  · exact le_csInf (Set.range_nonempty _) (by
      rintro _ ⟨C, rfl⟩; exact neg_056158_le_multivariateSpearmanRho_three C)
  · rw [← multivariateSpearmanRho_witness]
    exact csInf_le hbdd ⟨witness, rfl⟩

end SpearmanInfimum

end ProbabilityTheory.Copula
