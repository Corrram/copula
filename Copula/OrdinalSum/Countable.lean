/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.OrdinalSum.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Countable ordinal sums along an increasing partition

This constructor permits infinitely many adjacent positive-length blocks,
starting at zero with endpoints tending to one. Its CDF is an absolutely
convergent series. Arbitrary disjoint interval families with a residual
comonotonic part are a different, more general construction.
-/

open Set Filter
open scoped unitInterval BigOperators Topology

namespace ProbabilityTheory.Copula

/-- An increasing sequence of partition endpoints exhausting the unit interval. -/
structure CountableIntervalPartition where
  point : ℕ → I
  strictMono : StrictMono point
  zero : point 0 = 0
  tendsto_one : Tendsto (fun k => (point k : ℝ)) atTop (𝓝 1)

namespace CountableIntervalPartition

/-- Length of the `k`th block. -/
def width (P : CountableIntervalPartition) (k : ℕ) : ℝ :=
  (P.point (k + 1) : ℝ) - P.point k

theorem width_pos (P : CountableIntervalPartition) (k : ℕ) : 0 < P.width k :=
  sub_pos.mpr (P.strictMono (Nat.lt_succ_self k))

/-- Clipped local coordinate on a countable partition block. -/
noncomputable def coord (P : CountableIntervalPartition) (k : ℕ) (u : I) : I :=
  projIcc 0 1 zero_le_one (((u : ℝ) - P.point k) / P.width k)

theorem coord_mono (P : CountableIntervalPartition) (k : ℕ) : Monotone (P.coord k) := by
  intro u v huv
  change (u : ℝ) ≤ v at huv
  exact monotone_projIcc zero_le_one
    (div_le_div_of_nonneg_right (sub_le_sub_right huv _) (P.width_pos k).le)

theorem coord_of_le (P : CountableIntervalPartition) (k : ℕ) (u : I)
    (hu : u ≤ P.point k) : P.coord k u = 0 :=
  projIcc_of_le_left zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu) (P.width_pos k).le)

theorem coord_of_ge (P : CountableIntervalPartition) (k : ℕ) (u : I)
    (hu : P.point (k + 1) ≤ u) : P.coord k u = 1 := by
  change (P.point (k + 1) : ℝ) ≤ u at hu
  apply projIcc_of_right_le zero_le_one
  exact (one_le_div (P.width_pos k)).2 (sub_le_sub_right hu _)

@[simp] theorem coord_zero (P : CountableIntervalPartition) (k : ℕ) : P.coord k 0 = 0 :=
  P.coord_of_le k 0 (P.point k).property.1

@[simp] theorem coord_one (P : CountableIntervalPartition) (k : ℕ) : P.coord k 1 = 1 :=
  P.coord_of_ge k 1 (P.point (k + 1)).property.2

theorem width_mul_coord (P : CountableIntervalPartition) (k : ℕ) (u : I) :
    P.width k * (P.coord k u : ℝ) =
      min (u : ℝ) (P.point (k + 1)) - min (u : ℝ) (P.point k) := by
  have hab : (P.point k : ℝ) ≤ P.point (k + 1) := (P.strictMono (Nat.lt_succ_self k)).le
  rcases le_total u (P.point k) with hu | hu
  · rw [P.coord_of_le k u hu]
    change (u : ℝ) ≤ P.point k at hu
    rw [min_eq_left (hu.trans hab), min_eq_left hu]
    simp
  · rcases le_total u (P.point (k + 1)) with hv | hv
    · have hc : (P.coord k u : ℝ) = ((u : ℝ) - P.point k) / P.width k := by
        change (P.point k : ℝ) ≤ u at hu
        change (u : ℝ) ≤ P.point (k + 1) at hv
        exact congrArg Subtype.val (projIcc_of_mem zero_le_one
          ⟨div_nonneg (sub_nonneg.mpr hu) (P.width_pos k).le,
            (div_le_one (P.width_pos k)).2 (sub_le_sub_right hv _)⟩)
      change (P.point k : ℝ) ≤ u at hu
      change (u : ℝ) ≤ P.point (k + 1) at hv
      rw [hc, min_eq_left hv, min_eq_right hu]
      exact mul_div_cancel₀ _ (P.width_pos k).ne'
    · rw [P.coord_of_ge k u hv]
      change (P.point k : ℝ) ≤ u at hu
      change (P.point (k + 1) : ℝ) ≤ u at hv
      rw [min_eq_right hv, min_eq_right hu]
      change P.width k * 1 = _
      rw [mul_one]
      rfl

/-- The weighted local coordinates have exactly the uniform marginal CDF. -/
theorem hasSum_width_mul_coord (P : CountableIntervalPartition) (u : I) :
    HasSum (fun k => P.width k * (P.coord k u : ℝ)) (u : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => mul_nonneg (P.width_pos k).le (P.coord k u).property.1) _).2
  simp_rw [P.width_mul_coord, Finset.sum_range_sub (fun k => min (u : ℝ) (P.point k))]
  have h := (tendsto_const_nhds (x := (u : ℝ))).min P.tendsto_one
  simpa [P.zero, min_eq_left u.property.2, min_eq_right u.property.1] using h

theorem hasSum_width (P : CountableIntervalPartition) : HasSum P.width 1 := by
  simpa using P.hasSum_width_mul_coord 1

/-- Absolute convergence of the weighted local CDF series. -/
theorem summable_cdf (P : CountableIntervalPartition) (C : ℕ → Copula 2) (u v : I) :
    Summable (fun k => P.width k * (C k).cdf ![P.coord k u, P.coord k v]) :=
  Summable.of_nonneg_of_le
    (fun k => mul_nonneg (P.width_pos k).le ((C k).cdf_nonneg _))
    (fun k => (mul_le_mul_of_nonneg_left ((C k).cdf_le_one _) (P.width_pos k).le).trans_eq
      (mul_one _)) P.hasSum_width.summable

/-- The CDF series for the countable ordinal sum. -/
noncomputable def cdf (P : CountableIntervalPartition) (C : ℕ → Copula 2) (u v : I) : ℝ :=
  ∑' k, P.width k * (C k).cdf ![P.coord k u, P.coord k v]

theorem isClassical (P : CountableIntervalPartition) (C : ℕ → Copula 2) :
    IsClassical (fun u : Fin 2 → I => P.cdf C (u 0) (u 1)) := by
  apply IsClassical.ofBivariate
  · intro v; simp [cdf]
  · intro u; simp [cdf]
  · intro v; simpa [cdf] using (P.hasSum_width_mul_coord v).tsum_eq
  · intro u; simpa [cdf] using (P.hasSum_width_mul_coord u).tsum_eq
  · intro a b c d hab hcd
    have h (k : ℕ) := (C k).rectangleIncrement_cdf_nonneg
      ![P.coord k a, P.coord k c] ![P.coord k b, P.coord k d] (by
        intro i; fin_cases i
        · exact P.coord_mono k hab
        · exact P.coord_mono k hcd)
    simp only [rectangleIncrement_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have ht : 0 ≤ ∑' k, P.width k * ((C k).cdf ![P.coord k b, P.coord k d] -
        (C k).cdf ![P.coord k a, P.coord k d] - (C k).cdf ![P.coord k b, P.coord k c] +
        (C k).cdf ![P.coord k a, P.coord k c]) :=
      tsum_nonneg (fun k => mul_nonneg (P.width_pos k).le (h k))
    simp only [mul_add, mul_sub] at ht
    rw [Summable.tsum_add ((P.summable_cdf C b d).sub (P.summable_cdf C a d) |>.sub
        (P.summable_cdf C b c)) (P.summable_cdf C a c),
      Summable.tsum_sub ((P.summable_cdf C b d).sub (P.summable_cdf C a d)) (P.summable_cdf C b c),
      Summable.tsum_sub (P.summable_cdf C b d) (P.summable_cdf C a d)] at ht
    exact ht

/-- The concrete countable partition with endpoints `1 - (1/2)^k`. -/
noncomputable def dyadic : CountableIntervalPartition where
  point k := ⟨1 - (1 / 2 : ℝ) ^ k, by
    constructor
    · exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
    · linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]⟩
  strictMono := by
    apply strictMono_nat_of_lt_succ
    intro k
    change 1 - (1 / 2 : ℝ) ^ k < 1 - (1 / 2 : ℝ) ^ (k + 1)
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
  zero := by apply Subtype.ext; simp
  tendsto_one := by
    have h : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h.const_sub 1

end CountableIntervalPartition

/-- Countable ordinal sum on adjacent blocks with endpoints tending to one. -/
noncomputable def countableOrdinalSum (P : CountableIntervalPartition) (C : ℕ → Copula 2) :
    Copula 2 := ofClassical _ (P.isClassical C)

@[simp] theorem cdf_countableOrdinalSum (P : CountableIntervalPartition) (C : ℕ → Copula 2)
    (u : Fin 2 → I) :
    (countableOrdinalSum P C).cdf u =
      ∑' k, P.width k * (C k).cdf ![P.coord k (u 0), P.coord k (u 1)] :=
  congrFun (cdf_ofClassical _ _) u

/-- Countable ordinal sum of independent blocks. -/
noncomputable def countableOrdinalSumPi (P : CountableIntervalPartition) : Copula 2 :=
  countableOrdinalSum P (fun _ => independence 2)

theorem cdf_countableOrdinalSumPi (P : CountableIntervalPartition) (u v : I) :
    (countableOrdinalSumPi P).cdf ![u, v] =
      ∑' k, P.width k * ((P.coord k u : ℝ) * (P.coord k v : ℝ)) := by
  simp [countableOrdinalSumPi, cdf_independence, Fin.prod_univ_two]

@[simp] theorem countableOrdinalSum_comonotonic (P : CountableIntervalPartition) :
    countableOrdinalSum P (fun _ => comonotonic 2) = comonotonic 2 := by
  apply ext_cdf
  intro u
  simp only [cdf_countableOrdinalSum, cdf_comonotonic_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases le_total (u 0) (u 1) with h | h
  · simp_rw [min_eq_left (show (P.coord _ (u 0) : ℝ) ≤ P.coord _ (u 1) from P.coord_mono _ h)]
    rw [(P.hasSum_width_mul_coord (u 0)).tsum_eq, min_eq_left (show (u 0 : ℝ) ≤ u 1 from h)]
  · simp_rw [min_eq_right (show (P.coord _ (u 1) : ℝ) ≤ P.coord _ (u 0) from P.coord_mono _ h)]
    rw [(P.hasSum_width_mul_coord (u 1)).tsum_eq, min_eq_right (show (u 1 : ℝ) ≤ u 0 from h)]

end ProbabilityTheory.Copula
