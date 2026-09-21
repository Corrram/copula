/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperContact

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule.UpperSpline

theorem quadratic_unit_lipschitz (s t : I) :
    |((s : ℝ) - (s : ℝ) ^ 2) - ((t : ℝ) - (t : ℝ) ^ 2)| ≤ |(s : ℝ) - t| := by
  rw [show ((s : ℝ) - (s : ℝ) ^ 2) - ((t : ℝ) - (t : ℝ) ^ 2) =
    ((s : ℝ) - t) * (1 - (s : ℝ) - t) by ring, abs_mul]
  have h : |1 - (s : ℝ) - t| ≤ 1 := abs_le.mpr
    ⟨by linarith [s.property.2, t.property.2], by linarith [s.property.1, t.property.1]⟩
  nlinarith only [mul_le_mul_of_nonneg_left h (abs_nonneg ((s : ℝ) - t))]

theorem pieceValue_lipschitz {n v w : ℝ} (hn : 0 ≤ n) (hv : 0 ≤ v) (_hw : 0 ≤ w)
    (i : Fin 4) (s t : I) :
    |pieceValue n v w i s - pieceValue n v w i t| ≤
      v * |piecePoint n v w i s - piecePoint n v w i t| := by
  fin_cases i
  · change |(offset n v w + v * w * (s : ℝ)) - (offset n v w + v * w * (t : ℝ))| ≤
      v * |w * (s : ℝ) - w * (t : ℝ)|
    rw [show (offset n v w + v * w * (s : ℝ)) - (offset n v w + v * w * (t : ℝ)) =
      v * (w * (s : ℝ) - w * (t : ℝ)) by ring, abs_mul, abs_of_nonneg hv]
  · change |pieceValue n v w 1 s - pieceValue n v w 1 t| ≤ v * |piecePoint n v w 1 s - piecePoint n v w 1 t|
    have he : pieceValue n v w 1 s - pieceValue n v w 1 t =
        n * v ^ 2 * (((s : ℝ) - (s : ℝ) ^ 2) - ((t : ℝ) - (t : ℝ) ^ 2)) := by
      dsimp [pieceValue]; ring
    have hp : piecePoint n v w 1 s - piecePoint n v w 1 t = n * v * ((s : ℝ) - t) := by
      dsimp [piecePoint]; ring
    rw [he, hp]
    simp only [abs_mul, abs_pow, abs_of_nonneg hn, abs_of_nonneg hv]
    nlinarith only [mul_le_mul_of_nonneg_left (quadratic_unit_lipschitz s t)
      (mul_nonneg hn (sq_nonneg v))]
  · change |pieceValue n v w 2 s - pieceValue n v w 2 t| ≤ v * |piecePoint n v w 2 s - piecePoint n v w 2 t|
    have he : pieceValue n v w 2 s - pieceValue n v w 2 t =
        -v * (piecePoint n v w 2 s - piecePoint n v w 2 t) := by
      dsimp [pieceValue, piecePoint]; ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg hv]
  · change |pieceValue n v w 3 s - pieceValue n v w 3 t| ≤ v * |piecePoint n v w 3 s - piecePoint n v w 3 t|
    have he : pieceValue n v w 3 s - pieceValue n v w 3 t =
        -((n + 1) * v ^ 2) * (((s : ℝ) - (s : ℝ) ^ 2) - ((t : ℝ) - (t : ℝ) ^ 2)) := by
      dsimp [pieceValue]; ring
    have hp : piecePoint n v w 3 s - piecePoint n v w 3 t = (n + 1) * v * ((s : ℝ) - t) := by
      dsimp [piecePoint]; ring
    rw [he, hp, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (mul_nonneg (by linarith) (sq_nonneg v)),
      abs_of_nonneg (mul_nonneg (by linarith) hv)]
    nlinarith only [mul_le_mul_of_nonneg_left (quadratic_unit_lipschitz s t)
      (mul_nonneg (show 0 ≤ n + 1 by linarith) (sq_nonneg v))]

private theorem join_lipschitz {a b c L : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hleft : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ L * |x - y|)
    (hright : ∀ x ∈ Set.Icc b c, ∀ y ∈ Set.Icc b c, |f x - f y| ≤ L * |x - y|) :
    ∀ x ∈ Set.Icc a c, ∀ y ∈ Set.Icc a c, |f x - f y| ≤ L * |x - y| := by
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y hy x hx (le_of_not_ge hxy)
  by_cases hyb : y ≤ b
  · exact hleft x ⟨hx.1, hxy.trans hyb⟩ y ⟨hy.1, hyb⟩
  by_cases hbx : b ≤ x
  · exact hright x ⟨hbx, hx.2⟩ y ⟨hbx.trans hxy, hy.2⟩
  have hxb := le_of_not_ge hbx
  have hby := le_of_not_ge hyb
  have h1 := hleft x ⟨hx.1, hxb⟩ b ⟨hab, le_rfl⟩
  have h2 := hright b ⟨le_rfl, hbc⟩ y ⟨hby, hy.2⟩
  have ht := abs_add_le (f x - f b) (f b - f y)
  rw [sub_add_sub_cancel] at ht
  rw [abs_of_nonpos (sub_nonpos.mpr hxb)] at h1
  rw [abs_of_nonpos (sub_nonpos.mpr hby)] at h2
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  nlinarith only [h1, h2, ht]

theorem basePotential_piece_lipschitz {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (i : Fin 4) (x : ℝ) (hx : x ∈ Set.Icc (piecePoint n v w i 0) (piecePoint n v w i 1))
    (y : ℝ) (hy : y ∈ Set.Icc (piecePoint n v w i 0) (piecePoint n v w i 1)) :
    |basePotential n v w x - basePotential n v w y| ≤ v * |x - y| := by
  have hc : Continuous (fun s : I => piecePoint n v w i s) := by fin_cases i <;> dsimp [piecePoint] <;> fun_prop
  obtain ⟨s, rfl⟩ := exists_unitInterval_eq hc hx.1 hx.2
  obtain ⟨t, rfl⟩ := exists_unitInterval_eq hc hy.1 hy.2
  rw [basePotential_piecePoint hn hv hw, basePotential_piecePoint hn hv hw]
  exact pieceValue_lipschitz hn.le hv hw i s t

theorem basePotential_lipschitz {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (period n v w))
    (y : ℝ) (hy : y ∈ Set.Icc 0 (period n v w)) :
    |basePotential n v w x - basePotential n v w y| ≤ v * |x - y| := by
  have h0 := basePotential_piece_lipschitz hn hv hw 0
  have h1 := basePotential_piece_lipschitz hn hv hw 1
  have h2 := basePotential_piece_lipschitz hn hv hw 2
  have h3 := basePotential_piece_lipschitz hn hv hw 3
  norm_num only [piecePoint, mul_zero, mul_one, add_zero] at h0 h1 h2 h3
  have hnv := mul_nonneg hn.le hv
  have h01 := join_lipschitz hw (show w ≤ w + n * v by linarith) h0 h1
  have h012 := join_lipschitz (show 0 ≤ w + n * v by positivity)
    (show w + n * v ≤ w + n * v + w by linarith) h01 h2
  have hj : w + n * v + w = 2 * w + n * v := by ring
  rw [hj] at h012
  have hall := join_lipschitz (show 0 ≤ 2 * w + n * v by positivity)
    (show 2 * w + n * v ≤ 2 * w + n * v + (n + 1) * v by exact le_add_of_nonneg_right (mul_nonneg (by linarith) hv)) h012 h3
  have he : 2 * w + n * v + (n + 1) * v = period n v w := by unfold period; ring
  rw [he] at hall
  exact hall x hx y hy


/-- The periodic extension preserves the sharp Lipschitz constant, including across its seams. -/
theorem potential_lipschitz {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) :
    LipschitzWith ⟨v, hv⟩ (potential n v w hp) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |potential n v w hp x - potential n v w hp y| ≤ v * |x - y|
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this y x (le_of_not_ge hxy)
  let X := toIcoMod hp 0 x
  let Y := toIcoMod hp 0 y
  let k : ℤ := toIcoDiv hp 0 y - toIcoDiv hp 0 x
  have hX : X ∈ Set.Ico 0 (period n v w) := toIcoMod_mem_Ico' hp x
  have hY : Y ∈ Set.Ico 0 (period n v w) := toIcoMod_mem_Ico' hp y
  have hd : y - x = Y - X + (k : ℝ) * period n v w := by
    have hx := toIcoMod_add_toIcoDiv_mul hp 0 x
    have hy := toIcoMod_add_toIcoDiv_mul hp 0 y
    dsimp [X, Y, k]
    push_cast
    linarith
  have hk : 0 ≤ k := by
    by_contra h
    have hh : k ≤ -1 := by omega
    have hr : (k : ℝ) ≤ -1 := by exact_mod_cast hh
    have hm := mul_le_mul_of_nonneg_right hr hp.le
    nlinarith only [hd, hxy, hX.1, hY.2, hm]
  change |basePotential n v w X - basePotential n v w Y| ≤ v * |x - y|
  rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
  by_cases hXY : X ≤ Y
  · have hb := basePotential_lipschitz hn hv hw X ⟨hX.1, hX.2.le⟩ Y ⟨hY.1, hY.2.le⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hXY), neg_sub] at hb
    have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
    have hs : Y - X ≤ y - x := by nlinarith only [hd, mul_nonneg hkR hp.le]
    exact hb.trans (mul_le_mul_of_nonneg_left hs hv)
  · have hk1 : 1 ≤ k := by
      by_contra h
      have hz : k = 0 := by omega
      rw [hz, Int.cast_zero, zero_mul, add_zero] at hd
      linarith
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have h1 := basePotential_lipschitz hn hv hw X ⟨hX.1, hX.2.le⟩
      (period n v w) ⟨hp.le, le_rfl⟩
    have h2 := basePotential_lipschitz hn hv hw 0 ⟨le_rfl, hp.le⟩ Y ⟨hY.1, hY.2.le⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hX.2.le), neg_sub, ← basePotential_endpoints hn hv hw] at h1
    rw [zero_sub, abs_neg, abs_of_nonneg hY.1] at h2
    have ht := abs_add_le (basePotential n v w X - basePotential n v w 0)
      (basePotential n v w 0 - basePotential n v w Y)
    rw [sub_add_sub_cancel] at ht
    have hs : period n v w - X + Y ≤ y - x := by
      nlinarith only [hd, mul_le_mul_of_nonneg_right hkR hp.le]
    have hm := mul_le_mul_of_nonneg_left hs hv
    nlinarith only [h1, h2, ht, hm]

end ProbabilityTheory.Copula.RankRegion.RhoFootrule.UpperSpline
