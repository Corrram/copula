/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.Mixture
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Topology.Instances.AddCircle.Defs

/-! # Algebraic certificates for the rho–footrule transport spline

The four pieces of the periodic potential in Ansari–Rockel, Definition 5.1,
are parametrized by their interval coordinates. Nonnegative square
certificates prove the dual inequality on one period.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule.UpperSpline

noncomputable def period (n v w : ℝ) : ℝ := 2 * w + (2 * n + 1) * v

noncomputable def offset (n v w : ℝ) : ℝ :=
  -(w ^ 2 + 2 * (n + 1) * w * v + n * (n + 1) * v ^ 2) / 2

noncomputable def piecePoint (n v w : ℝ) : Fin 4 → ℝ → ℝ
  | 0, s => w * s
  | 1, s => w + n * v * s
  | 2, s => w + n * v + w * s
  | 3, s => 2 * w + n * v + (n + 1) * v * s

noncomputable def pieceValue (n v w : ℝ) : Fin 4 → ℝ → ℝ
  | 0, s => offset n v w + v * w * s
  | 1, s => offset n v w + v * w + n * v ^ 2 * (s - s ^ 2)
  | 2, s => offset n v w + v * w - v * w * s
  | 3, s => offset n v w + (n + 1) * v ^ 2 * (s ^ 2 - s)

theorem ordered_piece_cost_le {n v w s t : ℝ}
    (hn : 0 ≤ n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (i j : Fin 4) (hij : i ≤ j) :
    pieceValue n v w i s + pieceValue n v w j t ≤
      (piecePoint n v w j t - piecePoint n v w i s) ^ 2 -
        period n v w * (piecePoint n v w j t - piecePoint n v w i s) := by
  have hs0 := hs.1
  have ht0 := ht.1
  have hs1 : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hst : 0 ≤ s - t + 1 := by linarith [ht.2]
  apply sub_nonneg.mp
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · calc
      0 ≤ w ^ 2 * (s - t + 1) ^ 2 + 2 * w * v * (n * (s - t + 1) + (1 - t)) + n * (n + 1) * v ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 * s ^ 2 + 2 * n * w * v * s * (1 - t) + n * (n + 1) * v ^ 2 * (1 - t) ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 * (s - t) ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 * (1 - s) ^ 2 + 2 * (n + 1) * w * v * t * (1 - s) + n * (n + 1) * v ^ 2 * t ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 + 2 * n * w * v * (s - t + 1) + n * v ^ 2 * (n * (s - t + 1) ^ 2 + s ^ 2 + (1 - t) ^ 2) := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 * (1 - t) ^ 2 + 2 * n * w * v * s * (1 - t) + n * (n + 1) * v ^ 2 * s ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ n * (n + 1) * v ^ 2 * (s - t) ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 * (s - t + 1) ^ 2 + 2 * w * v * (n * (s - t + 1) + s) + n * (n + 1) * v ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 * s ^ 2 + 2 * (n + 1) * w * v * s * (1 - t) + n * (n + 1) * v ^ 2 * (1 - t) ^ 2 := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring
  · calc
      0 ≤ w ^ 2 + 2 * (n + 1) * w * v * (s - t + 1) + (n + 1) * v ^ 2 * (n * (s - t + 1) ^ 2 + 2 * s * (1 - t)) := by positivity
      _ = _ := by simp only [piecePoint, pieceValue, offset, period]; ring

theorem piecePoint_mem {n v w : ℝ} (hn : 0 ≤ n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (i : Fin 4) (s : I) :
    piecePoint n v w i 0 ≤ piecePoint n v w i s ∧
      piecePoint n v w i s ≤ piecePoint n v w i 1 := by
  have h0 := s.property.1
  have h1 := s.property.2
  have hnv := mul_nonneg hn hv
  have hnv' := mul_nonneg (show 0 ≤ n + 1 by linarith) hv
  fin_cases i <;> dsimp [piecePoint] <;>
    constructor <;> nlinarith [mul_nonneg hw h0, mul_nonneg hw (sub_nonneg.mpr h1),
      mul_nonneg hnv h0, mul_nonneg hnv (sub_nonneg.mpr h1),
      mul_nonneg hnv' h0, mul_nonneg hnv' (sub_nonneg.mpr h1)]

theorem piecePoint_order {n v w : ℝ} (hn : 0 ≤ n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (i j : Fin 4) (hij : i < j) (s t : I) :
    piecePoint n v w i s ≤ piecePoint n v w j t := by
  have h1 := (piecePoint_mem hn hv hw i s).2
  have h2 := (piecePoint_mem hn hv hw j t).1
  apply h1.trans
  apply le_trans _ h2
  fin_cases i <;> fin_cases j <;> norm_num at hij <;>
    dsimp [piecePoint] <;> nlinarith [mul_nonneg hn hv]

theorem piece_cost_le {n v w : ℝ} (hn : 0 ≤ n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (i j : Fin 4) (s t : I) :
    pieceValue n v w i s + pieceValue n v w j t ≤
      (piecePoint n v w j t - piecePoint n v w i s) ^ 2 -
        period n v w * |piecePoint n v w j t - piecePoint n v w i s| := by
  wlog hxy : piecePoint n v w i s ≤ piecePoint n v w j t generalizing i j s t
  · have h := this j i t s (le_of_not_ge hxy)
    rw [abs_sub_comm, sub_sq_comm] at h
    simpa only [add_comm] using h
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
  by_cases hij : i ≤ j
  · exact ordered_piece_cost_le hn hv hw s.property t.property i j hij
  · have he := le_antisymm hxy (piecePoint_order hn hv hw j i (lt_of_not_ge hij) t s)
    have h := ordered_piece_cost_le hn hv hw t.property s.property j i (le_of_not_ge hij)
    rw [he] at h ⊢
    simpa only [add_comm] using h


/-- A continuous hinge-square formula for one period of the dual potential. -/
noncomputable def basePotential (n v w x : ℝ) : ℝ :=
  offset n v w + v * x - (max 0 (x - w)) ^ 2 / n +
    (max 0 (x - (w + n * v))) ^ 2 / n +
    (max 0 (x - (2 * w + n * v))) ^ 2 / (n + 1)

@[fun_prop] theorem continuous_basePotential (n v w : ℝ) :
    Continuous (basePotential n v w) := by
  unfold basePotential
  fun_prop

theorem basePotential_piecePoint {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (i : Fin 4) (s : I) :
    basePotential n v w (piecePoint n v w i s) = pieceValue n v w i s := by
  have hs0 := s.property.1
  have hs1 := s.property.2
  have hnv := mul_nonneg hn.le hv
  have hws0 := mul_nonneg hw hs0
  have hws1 := mul_nonneg hw (sub_nonneg.mpr hs1)
  have hns0 := mul_nonneg hnv hs0
  have hns1 := mul_nonneg hnv (sub_nonneg.mpr hs1)
  have hvs0 := mul_nonneg hv hs0
  have hvs1 := mul_nonneg hv (sub_nonneg.mpr hs1)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hn1 : n + 1 ≠ 0 := by linarith
  fin_cases i <;> dsimp [basePotential, piecePoint, pieceValue]
  · rw [max_eq_left (by nlinarith : w * (s : ℝ) - w ≤ 0),
      max_eq_left (by nlinarith : w * (s : ℝ) - (w + n * v) ≤ 0),
      max_eq_left (by nlinarith : w * (s : ℝ) - (2 * w + n * v) ≤ 0)]
    ring
  · rw [max_eq_right (by nlinarith : 0 ≤ w + n * v * (s : ℝ) - w),
      max_eq_left (by nlinarith : w + n * v * (s : ℝ) - (w + n * v) ≤ 0),
      max_eq_left (by nlinarith : w + n * v * (s : ℝ) - (2 * w + n * v) ≤ 0)]
    field_simp; ring
  · rw [max_eq_right (by nlinarith : 0 ≤ w + n * v + w * (s : ℝ) - w),
      max_eq_right (by nlinarith : 0 ≤ w + n * v + w * (s : ℝ) - (w + n * v)),
      max_eq_left (by nlinarith : w + n * v + w * (s : ℝ) - (2 * w + n * v) ≤ 0)]
    field_simp; ring
  · rw [max_eq_right (by nlinarith : 0 ≤ 2 * w + n * v + (n + 1) * v * (s : ℝ) - w),
      max_eq_right (by nlinarith : 0 ≤ 2 * w + n * v + (n + 1) * v * (s : ℝ) - (w + n * v)),
      max_eq_right (by nlinarith : 0 ≤ 2 * w + n * v + (n + 1) * v * (s : ℝ) - (2 * w + n * v))]
    field_simp; ring

theorem exists_piecePoint {n v w x : ℝ}
    (hx : x ∈ Set.Icc 0 (period n v w)) :
    ∃ (i : Fin 4) (s : I), piecePoint n v w i s = x := by
  by_cases h0 : x ≤ w
  · obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := x)
      (f := fun s : I => piecePoint n v w 0 s) (by dsimp [piecePoint]; fun_prop)
      (by simpa [piecePoint] using hx.1) (by simpa [piecePoint] using h0)
    exact ⟨0, s, hs⟩
  by_cases h1 : x ≤ w + n * v
  · obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := x)
      (f := fun s : I => piecePoint n v w 1 s) (by dsimp [piecePoint]; fun_prop)
      (by dsimp [piecePoint]; norm_num; linarith) (by simpa [piecePoint] using h1)
    exact ⟨1, s, hs⟩
  by_cases h2 : x ≤ 2 * w + n * v
  · obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := x)
      (f := fun s : I => piecePoint n v w 2 s) (by dsimp [piecePoint]; fun_prop)
      (by dsimp [piecePoint]; norm_num; linarith)
      (by dsimp [piecePoint]; norm_num; linarith)
    exact ⟨2, s, hs⟩
  · obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := x)
      (f := fun s : I => piecePoint n v w 3 s) (by dsimp [piecePoint]; fun_prop)
      (by dsimp [piecePoint]; norm_num; linarith)
      (by dsimp [piecePoint]; norm_num; dsimp [period] at hx; linarith [hx.2])
    exact ⟨3, s, hs⟩

theorem basePotential_feasible {n v w x y : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hx : x ∈ Set.Icc 0 (period n v w)) (hy : y ∈ Set.Icc 0 (period n v w)) :
    basePotential n v w x + basePotential n v w y ≤ (y - x) ^ 2 - period n v w * |y - x| := by
  obtain ⟨i, s, rfl⟩ := exists_piecePoint hx
  obtain ⟨j, t, rfl⟩ := exists_piecePoint hy
  rw [basePotential_piecePoint hn hv hw, basePotential_piecePoint hn hv hw]
  exact piece_cost_le hn.le hv hw i j s t

theorem basePotential_endpoints {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    basePotential n v w 0 = basePotential n v w (period n v w) := by
  have h0 := basePotential_piecePoint hn hv hw 0 0
  have h1 := basePotential_piecePoint hn hv hw 3 1
  norm_num [piecePoint, pieceValue] at h0 h1
  rw [h0, show period n v w = 2 * w + n * v + (n + 1) * v by unfold period; ring, h1]


/-- Integer translations can only increase the distance cost from its fundamental cell. -/
theorem quadratic_translate_le {p d : ℝ} (hp : 0 < p) (hd0 : 0 ≤ d) (hd1 : d ≤ p) (k : ℤ) :
    d ^ 2 - p * d ≤ (d + (k : ℝ) * p) ^ 2 - p * |d + (k : ℝ) * p| := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · by_cases hk1 : k = -1
    · subst k
      norm_num
      rw [abs_of_nonpos (by linarith)]
      nlinarith only
    · have hk2 : k ≤ -2 := by omega
      have hk2r : (k : ℝ) ≤ -2 := by exact_mod_cast hk2
      have hkp : (k : ℝ) * p ≤ -2 * p := mul_le_mul_of_nonneg_right hk2r hp.le
      rw [abs_of_nonpos (by linarith)]
      have hprod := mul_nonneg_of_nonpos_of_nonpos
        (show (k + 1 : ℝ) * p ≤ 0 by nlinarith)
        (show 2 * d + (k : ℝ) * p ≤ 0 by linarith)
      nlinarith only [hprod]
  · norm_num [abs_of_nonneg hd0]
  · have hk1 : 1 ≤ k := by omega
    have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hkp : 0 ≤ (k : ℝ) * p := mul_nonneg (by linarith) hp.le
    rw [abs_of_nonneg (by linarith)]
    have hprod := mul_nonneg hkp
      (show 0 ≤ 2 * d + ((k : ℝ) - 1) * p by positivity)
    nlinarith only [hprod]

/-- The potential extended periodically to the real line. -/
noncomputable def potential (n v w : ℝ) (hp : 0 < period n v w) (x : ℝ) : ℝ :=
  basePotential n v w (toIcoMod hp 0 x)

theorem potential_periodic (n v w : ℝ) (hp : 0 < period n v w) :
    Function.Periodic (potential n v w hp) (period n v w) := by
  intro x
  unfold potential
  rw [toIcoMod_add_right]

@[fun_prop] theorem continuous_potential {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) : Continuous (potential n v w hp) := by
  let : Fact (0 < period n v w) := ⟨hp⟩
  have hc := (AddCircle.liftIco_zero_continuous (basePotential_endpoints hn hv hw)
    (continuous_basePotential n v w).continuousOn).comp (AddCircle.continuous_mk' (period n v w))
  exact hc

theorem potential_eq_base {n v w x : ℝ} (hp : 0 < period n v w)
    (hx : x ∈ Set.Ico 0 (period n v w)) :
    potential n v w hp x = basePotential n v w x := by
  unfold potential
  rw [(toIcoMod_eq_self hp).mpr (by simpa only [zero_add] using hx)]

/-- The source's global dual inequality, including pairs in different periods. -/
theorem potential_feasible {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) (x y : ℝ) :
    potential n v w hp x + potential n v w hp y ≤
      (y - x) ^ 2 - period n v w * |y - x| := by
  wlog hxy : toIcoMod hp 0 x ≤ toIcoMod hp 0 y generalizing x y
  · have h := this y x (le_of_not_ge hxy)
    rw [abs_sub_comm, sub_sq_comm] at h
    simpa only [add_comm] using h
  have hx := toIcoMod_mem_Ico' hp x
  have hy := toIcoMod_mem_Ico' hp y
  have hbase := basePotential_feasible hn hv hw ⟨hx.1, hx.2.le⟩ ⟨hy.1, hy.2.le⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hbase
  have hcost := quadratic_translate_le hp (sub_nonneg.mpr hxy)
    (show toIcoMod hp 0 y - toIcoMod hp 0 x ≤ period n v w by linarith [hx.1, hy.2])
    (toIcoDiv hp 0 y - toIcoDiv hp 0 x)
  have he : toIcoMod hp 0 y - toIcoMod hp 0 x +
      ((toIcoDiv hp 0 y - toIcoDiv hp 0 x : ℤ) : ℝ) * period n v w = y - x := by
    have hx' := toIcoMod_add_toIcoDiv_mul hp 0 x
    have hy' := toIcoMod_add_toIcoDiv_mul hp 0 y
    push_cast
    linarith
  rw [he] at hcost
  exact hbase.trans hcost

end ProbabilityTheory.Copula.RankRegion.RhoFootrule.UpperSpline

