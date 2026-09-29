/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Countable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # General ordinal sums

Nelsen, *An Introduction to Copulas*, 2nd ed., Definition 3.2.1: let `{(a_k, b_k)}` be a family
of pairwise disjoint open subintervals of `[0,1]` and let `C_k` be copulas. The ordinal sum of
the `C_k` with respect to the intervals is the copula
```text
C(u,v) = a_k + (b_k - a_k) C_k((u - a_k)/(b_k - a_k), (v - a_k)/(b_k - a_k))  on [a_k, b_k]²,
C(u,v) = min(u, v)                                                          elsewhere.
```
The index type is arbitrary (necessarily at most countably many intervals are nonempty, but no
countability assumption is needed), so the construction covers finite and countable families
and intervals that do not exhaust `[0,1]`.

## Construction

Write `w_k = b_k - a_k` and `c_k(u) = clamp((u - a_k)/w_k, 0, 1)`. The CDF is assembled as
```text
C(u,v) = min(g(u), g(v)) + ∑' k, w_k C_k(c_k(u), c_k(v)),   g(u) = u - ∑' k, w_k c_k(u).
```
Here `g(u)` is the Lebesgue measure of `[0,u]` outside the intervals (the mass that `M` puts on
the residual part of the diagonal). Disjointness enters through the finite estimate
`∑_{k ∈ s} |[x,y] ∩ (a_k, b_k)| ≤ y - x`, proved with Lebesgue measure; it gives summability of
the widths and monotonicity of `g`. Two-increasingness holds termwise.

## Main declarations

* `OrdinalIntervals ι`: pairwise disjoint nondegenerate open subintervals of `[0,1]`.
* `generalOrdinalSum J C`, `cdf_generalOrdinalSum`.
* `cdf_generalOrdinalSum_eq_min_sub`: `C(u,v) = min(u,v) - ∑' k, w_k (M - C_k)(c_k u, c_k v)`.
-/

open Set MeasureTheory
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-- A family of pairwise disjoint nonempty open subintervals `(left k, right k)` of `[0,1]`
(Nelsen, Definition 3.2.1). -/
structure OrdinalIntervals (ι : Type*) where
  left : ι → I
  right : ι → I
  left_lt_right : ∀ k, left k < right k
  disjoint : Pairwise fun k l => right k ≤ left l ∨ right l ≤ left k

namespace OrdinalIntervals

variable {ι : Type*} (J : OrdinalIntervals ι)

/-- Length of the `k`th interval. -/
def width (k : ι) : ℝ := (J.right k : ℝ) - J.left k

theorem width_pos (k : ι) : 0 < J.width k := sub_pos.mpr (J.left_lt_right k)

/-- The clipped affine coordinate of the `k`th interval. -/
noncomputable def coord (k : ι) (u : I) : I :=
  projIcc 0 1 zero_le_one (((u : ℝ) - J.left k) / J.width k)

theorem coord_mono (k : ι) : Monotone (J.coord k) := by
  intro u v huv
  change (u : ℝ) ≤ v at huv
  exact monotone_projIcc zero_le_one
    (div_le_div_of_nonneg_right (sub_le_sub_right huv _) (J.width_pos k).le)

theorem coord_of_le (k : ι) {u : I} (hu : u ≤ J.left k) : J.coord k u = 0 :=
  projIcc_of_le_left zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (J.width_pos k).le)

theorem coord_of_ge (k : ι) {u : I} (hu : J.right k ≤ u) : J.coord k u = 1 := by
  change (J.right k : ℝ) ≤ u at hu
  apply projIcc_of_right_le zero_le_one
  apply (one_le_div (J.width_pos k)).2
  exact sub_le_sub_right hu _

@[simp] theorem coord_zero (k : ι) : J.coord k 0 = 0 := J.coord_of_le k (J.left k).property.1

@[simp] theorem coord_one (k : ι) : J.coord k 1 = 1 := J.coord_of_ge k (J.right k).property.2

theorem coe_coord_of_mem (k : ι) {u : I} (hl : J.left k ≤ u) (hr : u ≤ J.right k) :
    (J.coord k u : ℝ) = ((u : ℝ) - J.left k) / J.width k := by
  change (J.left k : ℝ) ≤ u at hl
  change (u : ℝ) ≤ J.right k at hr
  have hw := J.width_pos k
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one
    ⟨div_nonneg (sub_nonneg.mpr hl) hw.le,
      (div_le_one hw).2 (by simp only [width]; linarith)⟩)

/-- On its interval, the coordinate inverts the affine map `s ↦ a_k + w_k s`. -/
theorem left_add_width_mul_coord (k : ι) {u : I} (hl : J.left k ≤ u) (hr : u ≤ J.right k) :
    (J.left k : ℝ) + J.width k * J.coord k u = u := by
  rw [J.coe_coord_of_mem k hl hr, mul_div_cancel₀ _ (J.width_pos k).ne']
  ring

theorem width_mul_coord (k : ι) (u : I) :
    J.width k * (J.coord k u : ℝ) = min (u : ℝ) (J.right k) - min (u : ℝ) (J.left k) := by
  have hab : (J.left k : ℝ) ≤ J.right k := (J.left_lt_right k).le
  rcases le_total u (J.left k) with hu | hu
  · rw [J.coord_of_le k hu]
    change (u : ℝ) ≤ J.left k at hu
    rw [min_eq_left (hu.trans hab), min_eq_left hu]
    simp
  · rcases le_total u (J.right k) with hv | hv
    · rw [J.coe_coord_of_mem k hu hv]
      change (J.left k : ℝ) ≤ u at hu
      change (u : ℝ) ≤ J.right k at hv
      rw [min_eq_left hv, min_eq_right hu]
      exact mul_div_cancel₀ _ (J.width_pos k).ne'
    · rw [J.coord_of_ge k hv]
      change (J.left k : ℝ) ≤ u at hu
      change (J.right k : ℝ) ≤ u at hv
      rw [min_eq_right hv, min_eq_right hu]
      simp [width]

theorem width_mul_coord_nonneg (k : ι) (u : I) : 0 ≤ J.width k * (J.coord k u : ℝ) :=
  mul_nonneg (J.width_pos k).le (J.coord k u).property.1

theorem width_mul_coord_le (k : ι) (u : I) : J.width k * (J.coord k u : ℝ) ≤ J.width k :=
  mul_le_of_le_one_right (J.width_pos k).le (J.coord k u).property.2

/-! ### Disjointness and summability -/

private theorem increment_eq (a b x y : ℝ) (hab : a ≤ b) (hxy : x ≤ y) :
    (min y b - min y a) - (min x b - min x a) = max (min b y - max a x) 0 := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Finitely many disjoint intervals meet `[x, y]` in total length at most `y - x`. -/
theorem sum_inter_le (s : Finset ι) {x y : ℝ} (hxy : x ≤ y) :
    ∑ k ∈ s, max (min (J.right k : ℝ) y - max (J.left k : ℝ) x) 0 ≤ y - x := by
  have hset : ∀ k, max (min (J.right k : ℝ) y - max (J.left k : ℝ) x) 0 =
      volume.real (Ioc (max (J.left k : ℝ) x) (min (J.right k : ℝ) y)) := fun k => by
    rw [Real.volume_real_Ioc]
  simp_rw [hset]
  have hd : (s : Set ι).PairwiseDisjoint
      (fun k => Ioc (max (J.left k : ℝ) x) (min (J.right k : ℝ) y)) := by
    intro k _ l _ hkl
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    simp only [mem_Ioc] at hz hz'
    rcases J.disjoint hkl with h | h
    · have h1 : z ≤ (J.right k : ℝ) := hz.2.trans (min_le_left _ _)
      have h2 : (J.left l : ℝ) < z := lt_of_le_of_lt (le_max_left _ _) hz'.1
      change (J.right k : ℝ) ≤ J.left l at h
      linarith
    · have h1 : z ≤ (J.right l : ℝ) := hz'.2.trans (min_le_left _ _)
      have h2 : (J.left k : ℝ) < z := lt_of_le_of_lt (le_max_left _ _) hz.1
      change (J.right l : ℝ) ≤ J.left k at h
      linarith
  rw [← measureReal_biUnion_finset hd (fun _ _ => measurableSet_Ioc)
    (fun _ _ => measure_Ioc_lt_top.ne), ← Real.volume_real_Ioc_of_le hxy]
  apply measureReal_mono
  · intro z hz
    simp only [mem_iUnion, mem_Ioc] at hz
    obtain ⟨k, _, h1, h2⟩ := hz
    exact ⟨lt_of_le_of_lt (le_max_right _ _) h1, h2.trans (min_le_right _ _)⟩
  · exact measure_Ioc_lt_top.ne

/-- The increments of the weighted coordinates between `u ≤ v` add up to at most `v - u`. -/
theorem sum_increment_le (s : Finset ι) {u v : I} (huv : u ≤ v) :
    ∑ k ∈ s, (J.width k * (J.coord k v : ℝ) - J.width k * J.coord k u) ≤ (v : ℝ) - u := by
  refine le_trans (le_of_eq ?_) (J.sum_inter_le s (show (u : ℝ) ≤ v from huv))
  apply Finset.sum_congr rfl
  intro k _
  rw [J.width_mul_coord, J.width_mul_coord]
  exact increment_eq _ _ _ _ (J.left_lt_right k).le huv

theorem increment_nonneg (k : ι) {u v : I} (huv : u ≤ v) :
    0 ≤ J.width k * (J.coord k v : ℝ) - J.width k * J.coord k u :=
  sub_nonneg.mpr (mul_le_mul_of_nonneg_left (J.coord_mono k huv) (J.width_pos k).le)

theorem sum_width_le_one (s : Finset ι) : ∑ k ∈ s, J.width k ≤ 1 := by
  have h := J.sum_increment_le s (zero_le_one (α := I))
  simpa [coord_zero, coord_one] using h

theorem summable_width : Summable J.width :=
  summable_of_sum_le (fun k => (J.width_pos k).le) J.sum_width_le_one

theorem tsum_width_le_one : ∑' k, J.width k ≤ 1 :=
  Real.tsum_le_of_sum_le (fun k => (J.width_pos k).le) J.sum_width_le_one

/-- Summability of any family dominated by the widths. -/
theorem summable_of_abs_le {f : ι → ℝ} (hf : ∀ k, |f k| ≤ J.width k) : Summable f :=
  Summable.of_norm_bounded J.summable_width fun k => by simpa [Real.norm_eq_abs] using hf k

theorem summable_width_mul_coord (u : I) : Summable fun k => J.width k * (J.coord k u : ℝ) :=
  J.summable_of_abs_le fun k => by
    rw [abs_of_nonneg (J.width_mul_coord_nonneg k u)]
    exact J.width_mul_coord_le k u

/-! ### The residual diagonal mass -/

/-- The Lebesgue measure of `[0,u]` outside the intervals: `u - ∑' k, w_k c_k(u)`. -/
noncomputable def gap (u : I) : ℝ := (u : ℝ) - ∑' k, J.width k * (J.coord k u : ℝ)

theorem gap_mono : Monotone J.gap := by
  intro u v huv
  have hs := (J.summable_width_mul_coord v).sub (J.summable_width_mul_coord u)
  have h : ∑' k, (J.width k * (J.coord k v : ℝ) - J.width k * J.coord k u) ≤ (v : ℝ) - u :=
    Real.tsum_le_of_sum_le (fun k => J.increment_nonneg k huv) (fun s => J.sum_increment_le s huv)
  rw [Summable.tsum_sub (J.summable_width_mul_coord v) (J.summable_width_mul_coord u)] at h
  have _ := hs
  simp only [gap]
  linarith

@[simp] theorem gap_zero : J.gap 0 = 0 := by simp [gap]

theorem gap_nonneg (u : I) : 0 ≤ J.gap u := J.gap_zero ▸ J.gap_mono (show (0 : I) ≤ u from u.property.1)

theorem gap_min (u v : I) : J.gap (min u v) = min (J.gap u) (J.gap v) := J.gap_mono.map_min

end OrdinalIntervals

/-! ### The general ordinal sum -/

private theorem min_increment_nonneg {X Y Z T : ℝ} (hXY : X ≤ Y) (hZT : Z ≤ T) :
    0 ≤ min Y T - min X T - min Y Z + min X Z := by
  simp only [min_def]
  split_ifs <;> linarith

namespace OrdinalIntervals

variable {ι : Type*} (J : OrdinalIntervals ι)

theorem summable_cdf (C : ι → Copula 2) (u v : I) :
    Summable fun k => J.width k * (C k).cdf ![J.coord k u, J.coord k v] :=
  J.summable_of_abs_le fun k => by
    rw [abs_of_nonneg (mul_nonneg (J.width_pos k).le ((C k).cdf_nonneg _))]
    exact mul_le_of_le_one_right (J.width_pos k).le ((C k).cdf_le_one _)

/-- The CDF of the ordinal sum. -/
noncomputable def cdf (C : ι → Copula 2) (u v : I) : ℝ :=
  min (J.gap u) (J.gap v) + ∑' k, J.width k * (C k).cdf ![J.coord k u, J.coord k v]

theorem isClassical (C : ι → Copula 2) :
    IsClassical (fun u : Fin 2 → I => J.cdf C (u 0) (u 1)) := by
  have hleft (v : I) : J.cdf C 1 v = v := by
    have hm : min (J.gap 1) (J.gap v) = J.gap v := min_eq_right (J.gap_mono v.property.2)
    simp only [cdf, hm]
    simp only [coord_one, cdf_two_one_left, gap]
    ring
  have hright (u : I) : J.cdf C u 1 = u := by
    have hm : min (J.gap u) (J.gap 1) = J.gap u := min_eq_left (J.gap_mono u.property.2)
    simp only [cdf, hm]
    simp only [coord_one, cdf_two_one_right, gap]
    ring
  apply IsClassical.ofBivariate
  · intro v; simp [cdf, min_eq_left (J.gap_nonneg v)]
  · intro u; simp [cdf, min_eq_right (J.gap_nonneg u)]
  · exact hleft
  · exact hright
  · intro a b c d hab hcd
    have h (k : ι) := (C k).rectangleIncrement_cdf_nonneg
      ![J.coord k a, J.coord k c] ![J.coord k b, J.coord k d] (by
        intro i; fin_cases i
        · exact J.coord_mono k hab
        · exact J.coord_mono k hcd)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have ht : 0 ≤ ∑' k, J.width k * ((C k).cdf ![J.coord k b, J.coord k d] -
        (C k).cdf ![J.coord k a, J.coord k d] - (C k).cdf ![J.coord k b, J.coord k c] +
        (C k).cdf ![J.coord k a, J.coord k c]) :=
      tsum_nonneg (fun k => mul_nonneg (J.width_pos k).le (h k))
    simp only [mul_add, mul_sub] at ht
    rw [Summable.tsum_add ((J.summable_cdf C b d).sub (J.summable_cdf C a d) |>.sub
        (J.summable_cdf C b c)) (J.summable_cdf C a c),
      Summable.tsum_sub ((J.summable_cdf C b d).sub (J.summable_cdf C a d)) (J.summable_cdf C b c),
      Summable.tsum_sub (J.summable_cdf C b d) (J.summable_cdf C a d)] at ht
    have hm := min_increment_nonneg (J.gap_mono hab) (J.gap_mono hcd)
    simp only [cdf]
    linarith

end OrdinalIntervals

/-- **General ordinal sum** (Nelsen, Definition 3.2.1): the copula equal to
`a_k + w_k C_k((u - a_k)/w_k, (v - a_k)/w_k)` on the squares `[a_k, b_k]²` and to `M` elsewhere. -/
noncomputable def generalOrdinalSum {ι : Type*} (J : OrdinalIntervals ι) (C : ι → Copula 2) :
    Copula 2 :=
  ofClassical _ (J.isClassical C)

private theorem coe_min_I (u v : I) : ((min u v : I) : ℝ) = min (u : ℝ) v := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, min_eq_left (show (u : ℝ) ≤ v from h)]
  · rw [min_eq_right h, min_eq_right (show (v : ℝ) ≤ u from h)]

section Formulas

variable {ι : Type*} (J : OrdinalIntervals ι) (C : ι → Copula 2)

@[simp] theorem cdf_generalOrdinalSum (u : Fin 2 → I) :
    (generalOrdinalSum J C).cdf u =
      min (J.gap (u 0)) (J.gap (u 1)) +
        ∑' k, J.width k * (C k).cdf ![J.coord k (u 0), J.coord k (u 1)] :=
  congrFun (cdf_ofClassical _ _) u

theorem cdf_generalOrdinalSum_two (u v : I) :
    (generalOrdinalSum J C).cdf ![u, v] =
      min (J.gap u) (J.gap v) + ∑' k, J.width k * (C k).cdf ![J.coord k u, J.coord k v] :=
  cdf_generalOrdinalSum J C ![u, v]

/-- The defect of the `k`th block from `M`: `w_k (M - C_k)(c_k u, c_k v)`. -/
noncomputable def OrdinalIntervals.defect (k : ι) (u v : I) : ℝ :=
  J.width k * (min (J.coord k u : ℝ) (J.coord k v) - (C k).cdf ![J.coord k u, J.coord k v])

theorem OrdinalIntervals.summable_defect (u v : I) : Summable fun k => J.defect C k u v := by
  simp only [OrdinalIntervals.defect, mul_sub]
  refine Summable.sub ?_ (J.summable_cdf C u v)
  refine (J.summable_width_mul_coord (min u v)).congr fun k => ?_
  rw [(J.coord_mono k).map_min, coe_min_I]

/-- The ordinal sum as `M` minus the defects of the blocks. -/
theorem cdf_generalOrdinalSum_eq_min_sub (u v : I) :
    (generalOrdinalSum J C).cdf ![u, v] = min (u : ℝ) v - ∑' k, J.defect C k u v := by
  rw [cdf_generalOrdinalSum_two, ← J.gap_min, OrdinalIntervals.gap]
  have hmin : ((min u v : I) : ℝ) = min (u : ℝ) v := coe_min_I u v
  have hc (k : ι) : J.width k * ((J.coord k (min u v) : I) : ℝ) =
      J.width k * min (J.coord k u : ℝ) (J.coord k v) := by
    rw [(J.coord_mono k).map_min, coe_min_I]
  simp_rw [hmin, hc]
  have hs : Summable fun k => J.width k * min (J.coord k u : ℝ) (J.coord k v) :=
    (J.summable_width_mul_coord (min u v)).congr fun k => by rw [← hc]
  simp only [OrdinalIntervals.defect, mul_sub]
  rw [Summable.tsum_sub hs (J.summable_cdf C u v)]
  ring

end Formulas

end ProbabilityTheory.Copula
