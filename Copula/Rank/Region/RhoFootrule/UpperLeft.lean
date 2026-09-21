/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoFootrule.UpperContact
import Copula.Rank.Region.FinitePathCoupling

open MeasureTheory
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoFootrule

open UpperSpline

structure LeftData where
  N : ℕ
  N_pos : 0 < N
  v : ℝ
  w : ℝ
  v_nonneg : 0 ≤ v
  w_nonneg : 0 ≤ w
  normalized : 2 * (N : ℝ) * (w + (N + 1) * v) = 1

namespace LeftData

variable (S : LeftData)

theorem period_nonneg : 0 ≤ period S.N S.v S.w := by
  unfold period
  exact add_nonneg (mul_nonneg (by norm_num) S.w_nonneg)
    (mul_nonneg (by positivity) S.v_nonneg)

theorem end_eq_one : (S.N : ℝ) * period S.N S.v S.w + S.N * S.v = 1 := by
  unfold period
  nlinarith only [S.normalized]

theorem period_pos : 0 < period S.N S.v S.w := by
  have hv := S.v_nonneg
  have hw := S.w_nonneg
  have hn : (0 : ℝ) ≤ S.N := Nat.cast_nonneg _
  have hnv := mul_nonneg hn hv
  have he := S.end_eq_one
  have hp := S.period_nonneg
  by_contra h
  have hz : period S.N S.v S.w = 0 := le_antisymm (le_of_not_gt h) hp
  rw [hz, mul_zero, zero_add] at he
  have hh : period S.N S.v S.w = 2 * S.w + 2 * S.N * S.v + S.v := by unfold period; ring
  rw [hz] at hh
  linarith

noncomputable def phase (k : ℕ) (i : Fin 4) (s : ℝ) : ℝ :=
  (k : ℝ) * period S.N S.v S.w + piecePoint S.N S.v S.w i s - S.w

theorem phase_mem (k : ℕ) (i : Fin 4) (s : I) (hk : k ≤ S.N)
    (hi0 : i = 0 → 0 < k) (hi2 : i = 2 ∨ i = 3 → k < S.N) :
    S.phase k i s ∈ Set.Icc 0 1 := by
  have hn : (0 : ℝ) ≤ S.N := Nat.cast_nonneg _
  have hv := S.v_nonneg
  have hw := S.w_nonneg
  have hnv := mul_nonneg hn hv
  have hm := piecePoint_mem hn hv hw i s
  have hkp := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ S.N by exact_mod_cast hk) S.period_nonneg
  have hkn := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) S.period_nonneg
  have he := S.end_eq_one
  have hp : period S.N S.v S.w = 2 * S.w + 2 * S.N * S.v + S.v := by unfold period; ring
  fin_cases i
  · have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hi0 rfl
    have hh := mul_le_mul_of_nonneg_right hk0 S.period_nonneg
    dsimp [phase, piecePoint] at hm ⊢
    constructor <;> nlinarith only [hm.1, hm.2, hkp, he, hp, hh, hw, hnv, hv]
  · dsimp [phase, piecePoint] at hm ⊢
    constructor <;> nlinarith only [hm.1, hm.2, hkp, hkn, he]
  · have hk1 : (k : ℝ) + 1 ≤ S.N := by exact_mod_cast Nat.add_one_le_iff.mpr (hi2 (Or.inl rfl))
    have hh := mul_le_mul_of_nonneg_right hk1 S.period_nonneg
    dsimp [phase, piecePoint] at hm ⊢
    constructor <;> nlinarith only [hm.1, hm.2, hkn, he, hp, hh, hw, hnv, hv]
  · have hk1 : (k : ℝ) + 1 ≤ S.N := by exact_mod_cast Nat.add_one_le_iff.mpr (hi2 (Or.inr rfl))
    have hh := mul_le_mul_of_nonneg_right hk1 S.period_nonneg
    dsimp [phase, piecePoint] at hm ⊢
    constructor <;> nlinarith only [hm.1, hm.2, hkn, he, hp, hh, hw, hnv, hv]

noncomputable def point (k : ℕ) (i : Fin 4) (hk : k ≤ S.N)
    (hi0 : i = 0 → 0 < k) (hi2 : i = 2 ∨ i = 3 → k < S.N) (s : I) : I :=
  ⟨S.phase k i s, S.phase_mem k i s hk hi0 hi2⟩

@[fun_prop] theorem continuous_point (k : ℕ) (i : Fin 4) (hk : k ≤ S.N)
    (hi0 : i = 0 → 0 < k) (hi2 : i = 2 ∨ i = 3 → k < S.N) :
    Continuous (S.point k i hk hi0 hi2) := by
  fin_cases i <;> unfold point <;> dsimp [phase, piecePoint] <;> fun_prop

abbrev Index := Fin S.N ⊕ (Fin S.N ⊕ Fin S.N)

noncomputable def weight : S.Index → ℝ
  | .inl _ => S.w
  | .inr (.inl k) => (S.N - (k : ℝ)) * S.v
  | .inr (.inr k) => ((k : ℝ) + 1) * S.v

theorem weight_nonneg (i : S.Index) : 0 ≤ S.weight i := by
  rcases i with k | k | k
  · exact S.w_nonneg
  · exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast k.isLt.le)) S.v_nonneg
  · exact mul_nonneg (by positivity) S.v_nonneg

noncomputable def path : S.Index → I → (Fin 2 → I)
  | .inl k, s => ![S.point k 2 (by omega) (by norm_num) (fun _ => k.isLt) s,
      S.point (k + 1) 0 (by omega) (by omega) (by norm_num) s]
  | .inr (.inl k), s => ![S.point k 1 (by omega) (by norm_num) (by norm_num) s,
      S.point k 3 (by omega) (by norm_num) (fun _ => k.isLt) s]
  | .inr (.inr k), s => ![S.point k 3 (by omega) (by norm_num) (fun _ => k.isLt) s,
      S.point (k + 1) 1 (by omega) (by norm_num) (by norm_num) s]

@[fun_prop] theorem continuous_path (i : S.Index) : Continuous (S.path i) := by
  rcases i with k | k | k <;> fun_prop [path]

noncomputable def symmetricPath (i : S.Index × Bool) (s : I) : Fin 2 → I :=
  if i.2 then ![S.path i.1 s 1, S.path i.1 s 0] else S.path i.1 s

@[fun_prop] theorem continuous_symmetricPath (i : S.Index × Bool) :
    Continuous (S.symmetricPath i) := by
  rcases i with ⟨i, b⟩
  cases b
  · exact S.continuous_path i
  · change Continuous (fun s : I => ![S.path i s 1, S.path i s 0])
    fun_prop

end LeftData
end ProbabilityTheory.Copula.RankRegion.RhoFootrule
