/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Patchwork.Approximation
import Copula.Rank.ConditionalDerivative
import Copula.Reflection.Bivariate

/-! # Gluing copulas side by side

The gluing construction of Siburg and Stoimenov (*Gluing copulas*, Communications in
Statistics – Theory and Methods 37 (2008)), in its `n`-fold form along the first coordinate.
For an interval partition `0 = a₀ < a₁ < ⋯ < aₙ = 1` of `[0,1]` with cell widths
`pᵢ = aᵢ - aᵢ₋₁` and copulas `C₁, …, Cₙ`, the glued copula is

`C(u,v) = aᵢ₋₁ v + pᵢ Cᵢ((u - aᵢ₋₁) / pᵢ, v)` for `aᵢ₋₁ ≤ u ≤ aᵢ`

(`cdf_gluing_of_mem`). It is realized as the patchwork `∑ᵢ pᵢ Cᵢ(coordᵢ(u), v)` with the
clipped local coordinates of the partition (`cdf_gluing`). On the `i`-th strip its deviation
from independence is the rescaled deviation `pᵢ (Cᵢ - Π)(coordᵢ(u), v)`
(`cdf_gluing_sub_mul_of_mem`), and inside the strip its partial derivative in `u` is the
rescaled partial derivative of `Cᵢ` (`deriv_cdfSection_gluing_of_mem`).

We also record some general partition calculus (maximal width, splitting `∫₀¹` along the cells,
the affine change of variables on a cell) and the Lipschitz regularity of CDF sections.
-/

open MeasureTheory Set Filter Topology
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {n : ℕ}

/-! ## Partitions: index positivity, the maximal width, and integration over cells -/

namespace IntervalPartition

theorem pos (P : IntervalPartition n) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have h : (0 : I) = 1 := P.zero.symm.trans (by simpa using P.one)
    exact absurd h zero_ne_one
  · exact h

theorem univ_nonempty (P : IntervalPartition n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  Finset.univ_nonempty_iff.mpr ⟨⟨0, P.pos⟩⟩

/-- The largest cell width `max_i p_i` of a partition. -/
noncomputable def maxWidth (P : IntervalPartition n) : ℝ :=
  Finset.univ.sup' P.univ_nonempty P.width

theorem width_le_maxWidth (P : IntervalPartition n) (i : Fin n) :
    P.width i ≤ P.maxWidth :=
  Finset.le_sup' P.width (Finset.mem_univ i)

theorem exists_width_eq_maxWidth (P : IntervalPartition n) :
    ∃ i, P.width i = P.maxWidth := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' P.univ_nonempty P.width
  exact ⟨i, hi.symm⟩

theorem maxWidth_pos (P : IntervalPartition n) : 0 < P.maxWidth := by
  obtain ⟨i, hi⟩ := P.exists_width_eq_maxWidth
  rw [← hi]; exact P.width_pos i

theorem maxWidth_le_one (P : IntervalPartition n) : P.maxWidth ≤ 1 := by
  obtain ⟨i, hi⟩ := P.exists_width_eq_maxWidth
  rw [← hi, ← P.sum_width]
  exact Finset.single_le_sum (fun j _ => (P.width_pos j).le) (Finset.mem_univ i)

theorem sum_pow_le_one (P : IntervalPartition n) (e : ℕ) (he : 1 ≤ e) :
    ∑ i, P.width i ^ e ≤ 1 := by
  calc ∑ i, P.width i ^ e ≤ ∑ i, P.width i := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_of_le_one (P.width_pos i).le
          ((P.width_le_maxWidth i).trans P.maxWidth_le_one) (by omega)
    _ = 1 := P.sum_width

theorem sum_pow_pos (P : IntervalPartition n) (e : ℕ) :
    0 < ∑ i, P.width i ^ e := by
  obtain ⟨i, _⟩ := P.exists_width_eq_maxWidth
  exact lt_of_lt_of_le (pow_pos (P.width_pos i) e)
    (Finset.single_le_sum (fun j _ => (pow_pos (P.width_pos j) e).le) (Finset.mem_univ i))

/-- The points of a partition, indexed by natural numbers (constantly `1` beyond `n`). -/
noncomputable def pt (P : IntervalPartition n) (k : ℕ) : ℝ :=
  if h : k < n + 1 then (P.point ⟨k, h⟩ : ℝ) else 1

theorem pt_zero (P : IntervalPartition n) : P.pt 0 = 0 := by
  simp [IntervalPartition.pt, P.zero]

theorem pt_n (P : IntervalPartition n) : P.pt n = 1 := by
  simp only [IntervalPartition.pt, Nat.lt_succ_self n, dite_true]
  exact congrArg Subtype.val P.one

theorem pt_castSucc (P : IntervalPartition n) (i : Fin n) :
    P.pt i = P.point i.castSucc := by
  simp [IntervalPartition.pt, i.isLt.trans (Nat.lt_succ_self n)]
  rfl

theorem pt_succ (P : IntervalPartition n) (i : Fin n) :
    P.pt (i + 1) = P.point i.succ := by
  simp [IntervalPartition.pt, Nat.succ_lt_succ i.isLt]
  rfl

theorem cell_le (P : IntervalPartition n) (i : Fin n) :
    (P.point i.castSucc : ℝ) ≤ P.point i.succ := (P.strictMono Fin.castSucc_lt_succ).le

/-- Splitting `∫₀¹` along the cells of a partition. -/
theorem integral_eq_sum_cells (P : IntervalPartition n) (f : ℝ → ℝ)
    (hf : ∀ i : Fin n, IntervalIntegrable f volume (P.point i.castSucc) (P.point i.succ)) :
    (∫ t in (0 : ℝ)..1, f t) =
      ∑ i : Fin n, ∫ t in (P.point i.castSucc : ℝ)..P.point i.succ, f t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := P.pt) (n := n) (fun k hk => by
      rw [show k = ((⟨k, hk⟩ : Fin n) : ℕ) from rfl, P.pt_castSucc, P.pt_succ]
      exact hf _)
  rw [P.pt_zero, P.pt_n] at h
  rw [← h, Finset.sum_range]
  congr 1
  funext i
  rw [P.pt_castSucc, P.pt_succ]

/-- The affine change of variables on one cell. -/
theorem integral_cell_comp (P : IntervalPartition n) (i : Fin n) (g : ℝ → ℝ) :
    (∫ t in (P.point i.castSucc : ℝ)..P.point i.succ, g ((t - P.point i.castSucc) / P.width i)) =
      P.width i * ∫ s in (0 : ℝ)..1, g s := by
  have hw := P.width_pos i
  have h := intervalIntegral.integral_comp_div_sub g hw.ne' ((P.point i.castSucc : ℝ) / P.width i)
    (a := P.point i.castSucc) (b := P.point i.succ)
  simp_rw [← sub_div] at h
  rw [h, smul_eq_mul]
  congr 2
  · ring
  · have := hw
    unfold IntervalPartition.width at this ⊢
    exact div_self this.ne'

theorem coord_of_lt (P : IntervalPartition n) {i j : Fin n} (hji : j < i) (u : I)
    (hl : P.point i.castSucc ≤ u) : P.coord j u = 1 :=
  P.coord_of_ge j u ((P.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hji)).trans hl)

theorem coord_of_gt (P : IntervalPartition n) {i j : Fin n} (hij : i < j) (u : I)
    (hr : u ≤ P.point i.succ) : P.coord j u = 0 :=
  P.coord_of_le j u (hr.trans (P.strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)))

end IntervalPartition

/-! ## The glued copula -/

/-- Patchwork data for gluing `n` scaled copulas side by side in the first coordinate:
weights `pᵢ = width i`, first coordinates the clipped cell coordinates, second coordinates
untouched. -/
noncomputable def gluingData (P : IntervalPartition n) : PatchworkData (Fin n) where
  weight := P.width
  nonneg i := (P.width_pos i).le
  first := P.coord
  second _ := id
  first_mono := P.coord_mono
  second_mono _ := monotone_id
  first_zero := P.coord_zero
  second_zero _ := rfl
  first_one := P.coord_one
  second_one _ := rfl
  first_margin := P.sum_width_mul_coord
  second_margin v := by simp only [id]; rw [← Finset.sum_mul, P.sum_width, one_mul]

/-- The gluing of the copulas `C i`, scaled to the cells of `P`, along the first coordinate
(Siburg–Stoimenov). -/
noncomputable def gluing (P : IntervalPartition n) (C : Fin n → Copula 2) : Copula 2 :=
  (gluingData P).copula C

theorem cdf_gluing (P : IntervalPartition n) (C : Fin n → Copula 2) (u v : I) :
    (gluing P C).cdf ![u, v] = ∑ i, P.width i * (C i).cdf ![P.coord i u, v] := by
  simp [gluing, PatchworkData.cdf_copula, PatchworkData.cdf, gluingData]

/-- The deviation of the glued copula from independence, as a weighted sum. -/
theorem cdf_gluing_sub_mul (P : IntervalPartition n) (C : Fin n → Copula 2) (u v : I) :
    (gluing P C).cdf ![u, v] - (u : ℝ) * v =
      ∑ i, P.width i * ((C i).cdf ![P.coord i u, v] - (P.coord i u : ℝ) * v) := by
  rw [cdf_gluing]
  conv_lhs => rw [← P.sum_width_mul_coord u]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  congr 1
  funext i
  ring

/-- On the `i`-th strip only the `i`-th copula deviates from independence. -/
theorem cdf_gluing_sub_mul_of_mem (P : IntervalPartition n) (C : Fin n → Copula 2) (i : Fin n)
    (u v : I) (hl : P.point i.castSucc ≤ u) (hr : u ≤ P.point i.succ) :
    (gluing P C).cdf ![u, v] - (u : ℝ) * v =
      P.width i * ((C i).cdf ![P.coord i u, v] - (P.coord i u : ℝ) * v) := by
  rw [cdf_gluing_sub_mul]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [P.coord_of_lt h u hl]; simp
    · rw [P.coord_of_gt h u hr]; simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The Siburg–Stoimenov formula: on the strip `aᵢ₋₁ ≤ u ≤ aᵢ`,
`C(u,v) = aᵢ₋₁ v + pᵢ Cᵢ((u - aᵢ₋₁)/pᵢ, v)`. -/
theorem cdf_gluing_of_mem (P : IntervalPartition n) (C : Fin n → Copula 2) (i : Fin n)
    (u v : I) (hl : P.point i.castSucc ≤ u) (hr : u ≤ P.point i.succ) :
    (gluing P C).cdf ![u, v] =
      (P.point i.castSucc : ℝ) * v + P.width i * (C i).cdf ![P.coord i u, v] := by
  have h := cdf_gluing_sub_mul_of_mem P C i u v hl hr
  have hc : P.width i * (P.coord i u : ℝ) = (u : ℝ) - P.point i.castSucc := by
    rw [P.coe_coord_of_mem i u hl hr]
    field_simp [(P.width_pos i).ne']
  have hc' : P.width i * ((P.coord i u : ℝ) * v) = ((u : ℝ) - P.point i.castSucc) * v := by
    rw [← mul_assoc, hc]
  linear_combination h - hc'

/-- Gluing copies of the independence copula gives the independence copula. -/
@[simp] theorem gluing_independence (P : IntervalPartition n) :
    gluing P (fun _ => independence 2) = independence 2 := by
  apply ext_cdf_two
  intro u v
  have h := cdf_gluing_sub_mul P (fun _ => independence 2) u v
  simp only [cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, mul_zero, Finset.sum_const_zero] at h ⊢
  linarith

/-! ## Regularity of CDF sections -/

theorem lipschitzWith_cdfSection (D : Copula 2) (v : I) : LipschitzWith 1 (cdfSection D v) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
  unfold cdfSection
  have h1 := D.abs_cdf_sub_le_sum_abs ![projIcc 0 1 zero_le_one s, v]
    ![projIcc 0 1 zero_le_one t, v]
  have h2 := (LipschitzWith.projIcc (zero_le_one : (0 : ℝ) ≤ 1)).dist_le_mul s t
  rw [NNReal.coe_one, one_mul, Real.dist_eq, Subtype.dist_eq, Real.dist_eq] at h2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
    abs_zero, add_zero] at h1
  exact h1.trans h2

theorem abs_deriv_cdfSection_le_one (D : Copula 2) (v : I) (t : ℝ) :
    |deriv (cdfSection D v) t| ≤ 1 := by
  by_cases h : DifferentiableAt ℝ (cdfSection D v) t
  · have := h.hasDerivAt.le_of_lipschitz (lipschitzWith_cdfSection D v)
    simpa using this
  · rw [deriv_zero_of_not_differentiableAt h]
    simp

theorem intervalIntegrable_deriv_cdfSection_sq (D : Copula 2) (v : I) (a b : ℝ) :
    IntervalIntegrable (fun t => deriv (cdfSection D v) t ^ 2) volume a b := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_deriv _).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_deriv_cdfSection_le_one D v t)

/-! ## Sections of the glued copula -/

/-- On the closed `i`-th strip, the CDF section of the glued copula is an affine
reparametrization of the CDF section of `C i` plus `aᵢ₋₁ v`. -/
theorem cdfSection_gluing_of_mem (P : IntervalPartition n) (C : Fin n → Copula 2) (i : Fin n)
    (v : I) {t : ℝ} (hl : (P.point i.castSucc : ℝ) ≤ t) (hr : t ≤ P.point i.succ) :
    cdfSection (gluing P C) v t =
      P.width i * cdfSection (C i) v ((P.width i)⁻¹ * (t - P.point i.castSucc)) +
        (P.point i.castSucc : ℝ) * v := by
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(P.point i.castSucc).property.1.trans hl, hr.trans (P.point i.succ).property.2⟩
  let u : I := ⟨t, ht⟩
  have hu : projIcc 0 1 zero_le_one t = u := projIcc_of_mem zero_le_one ht
  unfold cdfSection
  rw [hu, cdf_gluing_of_mem P C i u v hl hr, add_comm, ← div_eq_inv_mul]
  rfl

/-- Inside the `i`-th strip, `∂₁C(t, v) = ∂₁Cᵢ((t - aᵢ₋₁)/pᵢ, v)` for the glued copula. -/
theorem deriv_cdfSection_gluing_of_mem (P : IntervalPartition n) (C : Fin n → Copula 2)
    (i : Fin n) (v : I) {t : ℝ} (hl : (P.point i.castSucc : ℝ) < t) (hr : t < P.point i.succ) :
    deriv (cdfSection (gluing P C) v) t =
      deriv (cdfSection (C i) v) ((t - P.point i.castSucc) / P.width i) := by
  have hw := P.width_pos i
  set a : ℝ := ((P.point i.castSucc : I) : ℝ)
  have hev : cdfSection (gluing P C) v =ᶠ[𝓝 t]
      fun s => P.width i * cdfSection (C i) v ((P.width i)⁻¹ * (s - a)) + a * v := by
    filter_upwards [Ioo_mem_nhds hl hr] with s hs
    exact cdfSection_gluing_of_mem P C i v hs.1.le hs.2.le
  rw [hev.deriv_eq, deriv_add_const, deriv_const_mul_field]
  have h1 : deriv (fun s => cdfSection (C i) v ((P.width i)⁻¹ * (s - a))) t =
      deriv (fun s => cdfSection (C i) v ((P.width i)⁻¹ * s)) (t - a) :=
    deriv_comp_sub_const (fun s => cdfSection (C i) v ((P.width i)⁻¹ * s)) a t
  rw [h1, deriv_comp_mul_left, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul,
    inv_mul_eq_div]

end ProbabilityTheory.Copula
