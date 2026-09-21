/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperSpline

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule.UpperSpline

theorem potential_eq_base_closed {n v w x : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) (hx : x ∈ Set.Icc 0 (period n v w)) :
    potential n v w hp x = basePotential n v w x := by
  by_cases he : x = period n v w
  · subst x
    have hh := potential_periodic n v w hp 0
    rw [zero_add] at hh
    rw [hh, potential_eq_base hp ⟨le_rfl, hp⟩, basePotential_endpoints hn hv hw]
  · exact potential_eq_base hp ⟨hx.1, lt_of_le_of_ne hx.2 he⟩

theorem potential_piecePoint {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) (i : Fin 4) (s : I) :
    potential n v w hp (piecePoint n v w i s) = pieceValue n v w i s := by
  rw [potential_eq_base_closed hn hv hw hp, basePotential_piecePoint hn hv hw]
  have hm := piecePoint_mem hn.le hv hw i s
  have hnv := mul_nonneg hn.le hv
  fin_cases i <;> dsimp [piecePoint, period] at hm ⊢ <;> constructor <;> nlinarith only [hm.1, hm.2, hw, hv, hnv]

theorem potential_translated_piecePoint {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : 0 < period n v w) (k : ℕ) (i : Fin 4) (s : I) :
    potential n v w hp ((k : ℝ) * period n v w + piecePoint n v w i s) =
      pieceValue n v w i s := by
  rw [add_comm, (potential_periodic n v w hp).nat_mul k,
    potential_piecePoint hn hv hw hp]

end ProbabilityTheory.Copula.RankRegion.RhoFootrule.UpperSpline
