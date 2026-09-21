import Copula.Checkerboard
import Copula.Shuffle
import Copula.Bernstein
import Copula.OrdinalSum.Countable

/-! Public construction examples: non-square grids, zero cells, signed
shuffles, positive Bernstein degrees, and an infinite ordinal partition. -/

noncomputable section

open ProbabilityTheory
open scoped unitInterval

namespace CopulaApproximationTest

private def half : I := ⟨1 / 2, by norm_num, by norm_num⟩
private def quarter : I := ⟨1 / 4, by norm_num, by norm_num⟩
private def two := Copula.IntervalPartition.uniform 2 (by decide)
private def three := Copula.IntervalPartition.uniform 3 (by decide)

-- Rectangular grids are accepted, with normalization in cell probabilities.
example : (Copula.CellMass.product two three).checkerboard = Copula.independence 2 := by simp

-- Zero cell probabilities are allowed: this diagonal matrix has two empty cells.
private def diagonalMass : Copula.CellMass two two where
  mass i j := if i = j then 1 / 2 else 0
  nonneg i j := by split <;> norm_num
  row_sum i := by simp [two]
  col_sum j := by simp [two]

example : diagonalMass.checkerboard.cdf ![half, half] = 1 / 2 := by
  norm_num [Copula.CellMass.cdf_checkerboard, diagonalMass, two, half,
    Copula.IntervalPartition.coord, Copula.IntervalPartition.width,
    Copula.IntervalPartition.uniform, Fin.sum_univ_two, Set.projIcc]

example : (Copula.ordinalSumPi two).cdf ![half, half] = 1 / 2 := by
  norm_num [Copula.cdf_ordinalSumPi, two, half,
    Copula.IntervalPartition.coord, Copula.IntervalPartition.width,
    Copula.IntervalPartition.uniform, Fin.sum_univ_two, Set.projIcc]

-- Empty finite partitions cannot satisfy the endpoint requirements.
example (P : Copula.IntervalPartition 0) : False := by
  have h : (0 : I) = 1 := P.zero.symm.trans (by simpa using P.one)
  exact zero_ne_one h

-- Straight identity shuffles give M; reflected segments are also supported.
example : Copula.shuffleOfMin two two (Equiv.refl _) (fun _ => rfl) (fun _ => false) =
    Copula.comonotonic 2 := by simp

example : (Copula.shuffleOfMin two two (Equiv.refl _) (fun _ => rfl)
    (fun _ => true)).cdf ![quarter, quarter] = 0 := by
  norm_num [Copula.cdf_shuffleOfMin, two, quarter,
    Copula.IntervalPartition.coord, Copula.IntervalPartition.width,
    Copula.IntervalPartition.uniform, Fin.sum_univ_two, Set.projIcc]

example : (Copula.uniformShuffleOfMin 2 (by decide) (Equiv.swap 0 1)).cdf ![half, half] = 0 := by
  norm_num [Copula.uniformShuffleOfMin, Copula.cdf_shuffleOfMin, half,
    Copula.IntervalPartition.coord, Copula.IntervalPartition.width,
    Copula.IntervalPartition.uniform, Fin.sum_univ_two, Set.projIcc]

-- Unequal source and target strip widths are matched by the permutation.
private def oneThird : I := ⟨1 / 3, by norm_num, by norm_num⟩
private def twoThirds : I := ⟨2 / 3, by norm_num, by norm_num⟩
private def unevenSource := Copula.IntervalPartition.binary oneThird
  (by change (0 : ℝ) < 1 / 3; norm_num) (by change (1 / 3 : ℝ) < 1; norm_num)
private def unevenTarget := Copula.IntervalPartition.binary twoThirds
  (by change (0 : ℝ) < 2 / 3; norm_num) (by change (2 / 3 : ℝ) < 1; norm_num)
private theorem uneven_match (i : Fin 2) :
    unevenSource.width i = unevenTarget.width (Equiv.swap 0 1 i) := by
  fin_cases i <;> norm_num [unevenSource, unevenTarget, Copula.IntervalPartition.binary,
    Copula.IntervalPartition.width, oneThird, twoThirds]

example : (Copula.shuffleOfMin unevenSource unevenTarget (Equiv.swap 0 1) uneven_match
    (fun _ => false)).cdf ![oneThird, twoThirds] = 0 := by
  norm_num [Copula.cdf_shuffleOfMin, unevenSource, unevenTarget, oneThird, twoThirds,
    Copula.IntervalPartition.coord, Copula.IntervalPartition.width,
    Copula.IntervalPartition.binary, Fin.sum_univ_two, Set.projIcc]

-- Sampling and refilling preserves the given copula's grid values.
example (C : Copula 2) (i : Fin 3) (j : Fin 4) :
    (C.checkerboard two three).cdf ![two.point i, three.point j] =
      C.cdf ![two.point i, three.point j] := by simp

example (C : Copula 2) (i : Fin 3) (j : Fin 4) :
    (C.checkMin two three).cdf ![two.point i, three.point j] =
      C.cdf ![two.point i, three.point j] := by simp

-- A genuinely non-independent Bernstein polynomial (M of degree 2).
example : ((Copula.comonotonic 2).bernstein 2 2 (by decide) (by decide)).cdf ![half, half] =
    5 / 16 := by
  rw [Copula.cdf_bernstein, Copula.bernsteinCDF_eq_sum]
  simp only [Copula.cdf_comonotonic_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Fin.sum_univ_succ, _root_.bernstein.z, _root_.bernstein_apply, half]

example (C : Copula 2) : C.bernstein 1 1 (by decide) (by decide) = Copula.independence 2 := by simp

example : (Copula.independence 2).bernstein 2 3 (by decide) (by decide) =
    Copula.independence 2 := by simp

-- The countable constructor has an explicit, inhabited partition API.
example : Copula.countableOrdinalSum Copula.CountableIntervalPartition.dyadic
    (fun _ => Copula.comonotonic 2) = Copula.comonotonic 2 := by simp

example (u : I) : (Copula.countableOrdinalSumPi Copula.CountableIntervalPartition.dyadic).cdf
    ![u, 1] = u := by simp

example (C D : Copula 2) :
    Copula.finiteOrdinalSum (Copula.IntervalPartition.binary half (by change (0 : ℝ) < 1 / 2; norm_num)
      (by change (1 / 2 : ℝ) < 1; norm_num)) ![C, D] = C.ordinalSum D half :=
  Copula.finiteOrdinalSum_binary C D _ _ _

end CopulaApproximationTest
