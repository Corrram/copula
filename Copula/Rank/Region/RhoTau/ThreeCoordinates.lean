/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Three-coordinate minimization

The replacement step in Schreyer–Paulin–Trutschnig, Lemma 4.2, is
expressed directly with a quadratic discriminant. It preserves the first
two power sums and strictly decreases the third power sum whenever three
positive coordinates have a unique largest member.
-/

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

theorem improve_three_coordinates {x y z : ℝ} (hxy : y < x) (hyz : z ≤ y)
    (hz : 0 < z) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a + b + c = x + y + z ∧ a ^ 2 + b ^ 2 + c ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 ∧
      a ^ 3 + b ^ 3 + c ^ 3 < x ^ 3 + y ^ 3 + z ^ 3 := by
  let e := min ((x - y) / 2) (z / 2)
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have hed : e < x - y := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hez : e < z := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let D := (x - z) ^ 2 + 2 * (x + z - 2 * y) * e - 3 * e ^ 2
  have hD : 0 < D := by
    have hp := mul_pos he (sub_pos.mpr hed)
    dsimp [D]
    nlinarith [sq_nonneg (x - z - e)]
  have hroot := Real.sq_sqrt hD.le
  have hroot0 := Real.sqrt_nonneg D
  have hx : 0 < x := lt_trans (lt_of_lt_of_le hz hyz) hxy
  have hsum : 0 < x + z - e := by linarith
  have hprod : 0 < x * z - (x + z - y) * e + e ^ 2 := by
    have hp := mul_pos hx (sub_pos.mpr hez)
    have hn := mul_nonneg (sub_nonneg.mpr hyz) he.le
    nlinarith [sq_nonneg e]
  have hrootlt : Real.sqrt D < x + z - e := by
    dsimp [D] at hroot
    nlinarith
  refine ⟨(x + z - e + Real.sqrt D) / 2, y + e,
    (x + z - e - Real.sqrt D) / 2, by positivity, by linarith,
    by linarith, by ring, ?_, ?_⟩
  · dsimp [D] at hroot
    nlinarith
  · have hdrop := mul_pos (mul_pos he (sub_pos.mpr hed))
      (show 0 < y - z + e by linarith)
    have hrootmul := congrArg (fun v : ℝ => v * (x + z - e)) hroot
    dsimp [D] at hrootmul
    nlinarith

end ProbabilityTheory.Copula.RankRegion.RhoTau
