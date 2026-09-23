import Copula.Rank.Region.TauFootruleBeta.Support.Shuffle
import Copula.Rank.Region.TauFootruleBeta.Paper.LowerJointFace

/-! # Proposition 3.3: the six-strip upper seed

These are exactly the six positive-slope segments in the paper, including
the degenerate endpoint shuffles. All coefficients use the resulting copula.
-/

open MeasureTheory ProbabilityTheory Set ProbabilityTheory.Copula.RankRegion.TauFootruleBeta.Support
open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.TauFootruleBeta

noncomputable def upperSeedStrip (q : ℝ) (hq : q ∈ Icc 0 (1 / 4))
    (i : Fin 6) : ShuffleStrip where
  x := ![0, q, 1 / 2 - q, 1 / 2, 1 / 2 + q, 1 - q] i
  y := ![1 / 2 - q, 1 / 2 + q, 0, 1 - q, q, 1 / 2] i
  width := ![q, 1 / 2 - 2 * q, q, q, 1 / 2 - 2 * q, q] i
  x_nonneg := by fin_cases i <;> dsimp <;> linarith [hq.1, hq.2]
  y_nonneg := by fin_cases i <;> dsimp <;> linarith [hq.1, hq.2]
  width_nonneg := by fin_cases i <;> dsimp <;> linarith [hq.1, hq.2]
  x_end := by fin_cases i <;> dsimp <;> linarith [hq.1, hq.2]
  y_end := by fin_cases i <;> dsimp <;> linarith [hq.1, hq.2]

noncomputable def upperSeedShuffle (q : ℝ) (hq : q ∈ Icc 0 (1 / 4)) :
    PositiveShuffle 6 where
  strip := upperSeedStrip q hq
  total := by simp [upperSeedStrip, Fin.sum_univ_succ]; ring
  tile_x := by
    intro u
    simp_rw [stripCut_eq_min_sub (upperSeedStrip q hq _).width_nonneg]
    simp only [upperSeedStrip, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    ring_nf
    rw [min_eq_right u.property.1, min_eq_left u.property.2]
    ring
  tile_y := by
    intro u
    simp_rw [stripCut_eq_min_sub (upperSeedStrip q hq _).width_nonneg]
    simp only [upperSeedStrip, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    ring_nf
    rw [min_eq_right u.property.1, min_eq_left u.property.2]
    ring

noncomputable def upperSeed (q : ℝ) (hq : q ∈ Icc 0 (1 / 4)) : Copula 2 :=
  (upperSeedShuffle q hq).copula

theorem upperSeed_footrule (q : ℝ) (hq : q ∈ Icc 0 (1 / 4)) :
    (upperSeed q hq).spearmanFootrule = 12 * q ^ 2 - 1 / 2 := by
  rw [upperSeed, PositiveShuffle.footrule]
  simp only [upperSeedShuffle, upperSeedStrip, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [abs_of_nonpos (by linarith [hq.2] : 0 - (1 / 2 - q) ≤ 0),
    abs_of_nonpos (by linarith : q - (1 / 2 + q) ≤ 0),
    abs_of_nonneg (by linarith [hq.2] : 0 ≤ 1 / 2 - q - 0),
    abs_of_nonpos (by linarith [hq.2] : 1 / 2 - (1 - q) ≤ 0),
    abs_of_nonneg (by linarith : 0 ≤ 1 / 2 + q - q),
    abs_of_nonneg (by linarith [hq.2] : 0 ≤ 1 - q - 1 / 2)]
  ring

theorem upperSeed_beta (q : ℝ) (hq : q ∈ Icc 0 (1 / 4)) :
    (upperSeed q hq).blomqvistBeta = 8 * q - 1 := by
  rw [Copula.blomqvistBeta, upperSeed, PositiveShuffle.cdf]
  simp only [upperSeedShuffle, upperSeedStrip, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  change 4 * (min (stripCut q 0 (1 / 2)) (stripCut q (1 / 2 - q) (1 / 2)) +
    (min (stripCut (1 / 2 - 2 * q) q (1 / 2))
      (stripCut (1 / 2 - 2 * q) (1 / 2 + q) (1 / 2)) +
    (min (stripCut q (1 / 2 - q) (1 / 2)) (stripCut q 0 (1 / 2)) +
    (min (stripCut q (1 / 2) (1 / 2)) (stripCut q (1 - q) (1 / 2)) +
    (min (stripCut (1 / 2 - 2 * q) (1 / 2 + q) (1 / 2))
      (stripCut (1 / 2 - 2 * q) q (1 / 2)) +
    min (stripCut q (1 - q) (1 / 2)) (stripCut q (1 / 2) (1 / 2))))))) - 1 = _
  have h1 : stripCut q 0 (1 / 2) = q := stripCut_full (by linarith [hq.2])
  have h2 : stripCut q (1 / 2 - q) (1 / 2) = q := stripCut_full (by linarith)
  have h3 : stripCut (1 / 2 - 2 * q) q (1 / 2) = 1 / 2 - 2 * q :=
    stripCut_full (by linarith [hq.1])
  have h4 : stripCut (1 / 2 - 2 * q) (1 / 2 + q) (1 / 2) = 0 :=
    stripCut_zero (by linarith [hq.2]) (by linarith [hq.1])
  have h5 : stripCut q (1 / 2) (1 / 2) = 0 := stripCut_zero hq.1 le_rfl
  have h6 : stripCut q (1 - q) (1 / 2) = 0 := stripCut_zero hq.1 (by linarith [hq.2])
  rw [h1, h2, h3, h4, h5, h6]
  rw [min_self, min_eq_right (by linarith [hq.2] : 0 ≤ 1 / 2 - 2 * q),
    min_eq_left (by linarith [hq.2] : 0 ≤ 1 / 2 - 2 * q), min_self]
  ring

def upperSeedPermutation : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem upperSeed_tau (q : ℝ) (hq : q ∈ Icc 0 (1 / 4)) :
    (upperSeed q hq).kendallTau = 8 * q ^ 2 := by
  have hx : ∀ i j : Fin 6, i < j →
      (upperSeedStrip q hq i).x + (upperSeedStrip q hq i).width ≤
        (upperSeedStrip q hq j).x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [upperSeedStrip] at * <;> linarith [hq.1, hq.2]
  have hy : ∀ i j : Fin 6, upperSeedPermutation i < upperSeedPermutation j →
      (upperSeedStrip q hq i).y + (upperSeedStrip q hq i).width ≤
        (upperSeedStrip q hq j).y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [upperSeedStrip, upperSeedPermutation] at * <;> linarith [hq.1, hq.2]
  rw [upperSeed, PositiveShuffle.tau _ upperSeedPermutation hx hy]
  norm_num [upperSeedShuffle, upperSeedStrip, upperSeedPermutation, Fin.sum_univ_succ]
  ring

theorem upperSeed_coefficients (q : ℝ) (hq : q ∈ Icc 0 (1 / 4)) :
    (upperSeed q hq).kendallTau = 8 * q ^ 2 ∧
      (upperSeed q hq).spearmanFootrule = 12 * q ^ 2 - 1 / 2 ∧
      (upperSeed q hq).blomqvistBeta = 8 * q - 1 :=
  ⟨upperSeed_tau q hq, upperSeed_footrule q hq, upperSeed_beta q hq⟩

end ProbabilityTheory.Copula.RankRegion.TauFootruleBeta
