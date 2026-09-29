/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Shuffle

/-! # Straight shuffles of `M` from weight vectors with zero entries

Nelsen, *An Introduction to Copulas*, 2nd ed., §3.2.3, describes a straight shuffle of `M` by a
partition of `[0,1]` into consecutive source intervals together with a permutation that puts the
intervals into a new order. In approximation arguments (Nelsen, Theorem 3.2.2) the natural
partitions contain intervals of length zero, which `IntervalPartition` excludes.

Here a straight shuffle is described by a weight vector `w : Fin M → ℝ` (nonnegative, summing to
one; zero entries allowed) listing the source intervals from left to right, and a permutation `π`
of `Fin M` giving the order of the pieces on the target axis. Piece `k` is the diagonal segment of
the square `[s_k, s_k + w_k] × [t_k, t_k + w_k]`, where `s_k = ∑_{j < k} w_j` and
`t_k = ∑_{π j < π k} w_j`.

`weightShuffle w hw0 hw1 π` is defined as an honest `shuffleOfMin` after the zero-length pieces
are discarded (the positive pieces are enumerated in increasing order by `Finset.orderIsoOfFin`),
so it is a shuffle of `M` in the sense of the library. Its CDF is
`∑_k min (clipLength (u - s_k) w_k) (clipLength (v - t_k) w_k)` with
`clipLength x w = min (max x 0) w` (`cdf_weightShuffle`).

## Main declarations

* `IsShuffleOfMin`, `IsStraightShuffleOfMin`: the classes of (straight) shuffles of `M`.
* `clipLength`, `prefixSum`, `sum_clipLength_prefixSum`: telescoping of consecutive intervals.
* `IntervalPartition.ofWeights`: the partition formed by the positive weights.
* `weightShuffle`, `cdf_weightShuffle`, `isStraightShuffleOfMin_weightShuffle`.
-/

open Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-! ### Shuffles of `M` as a class of copulas -/

/-- `S` is a shuffle of `M`: a finite shuffle of min in the sense of `shuffleOfMin`, with an
arbitrary orientation of every segment (Nelsen, §3.2.3). -/
def IsShuffleOfMin (S : Copula 2) : Prop :=
  ∃ (n : ℕ) (P Q : IntervalPartition n) (perm : Equiv.Perm (Fin n))
    (hwidth : ∀ i, P.width i = Q.width (perm i)) (flipped : Fin n → Bool),
    S = shuffleOfMin P Q perm hwidth flipped

/-- `S` is a straight shuffle of `M`: a finite shuffle of min in which every segment keeps its
increasing orientation. -/
def IsStraightShuffleOfMin (S : Copula 2) : Prop :=
  ∃ (n : ℕ) (P Q : IntervalPartition n) (perm : Equiv.Perm (Fin n))
    (hwidth : ∀ i, P.width i = Q.width (perm i)),
    S = shuffleOfMin P Q perm hwidth (fun _ => false)

theorem IsStraightShuffleOfMin.isShuffleOfMin {S : Copula 2} (h : S.IsStraightShuffleOfMin) :
    S.IsShuffleOfMin := by
  obtain ⟨n, P, Q, perm, hwidth, rfl⟩ := h
  exact ⟨n, P, Q, perm, hwidth, _, rfl⟩

theorem isStraightShuffleOfMin_shuffleOfMin {n : ℕ} (P Q : IntervalPartition n)
    (perm : Equiv.Perm (Fin n)) (hwidth : ∀ i, P.width i = Q.width (perm i)) :
    (shuffleOfMin P Q perm hwidth (fun _ => false)).IsStraightShuffleOfMin :=
  ⟨n, P, Q, perm, hwidth, rfl⟩

theorem isShuffleOfMin_shuffleOfMin {n : ℕ} (P Q : IntervalPartition n)
    (perm : Equiv.Perm (Fin n)) (hwidth : ∀ i, P.width i = Q.width (perm i))
    (flipped : Fin n → Bool) :
    (shuffleOfMin P Q perm hwidth flipped).IsShuffleOfMin :=
  ⟨n, P, Q, perm, hwidth, flipped, rfl⟩

/-- `M` itself is the trivial straight shuffle. -/
theorem isStraightShuffleOfMin_comonotonic : (comonotonic 2).IsStraightShuffleOfMin := by
  refine ⟨1, IntervalPartition.uniform 1 one_pos, IntervalPartition.uniform 1 one_pos,
    Equiv.refl _, fun _ => rfl, ?_⟩
  exact (shuffleOfMin_refl _).symm

/-! ### Clipped lengths and prefix sums -/

/-- The length of the part of a segment of length `w` that lies below `x`, when the segment
starts at `0`: `min (max x 0) w`. -/
def clipLength (x w : ℝ) : ℝ := min (max x 0) w

theorem clipLength_nonneg (x : ℝ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ clipLength x w :=
  le_min (le_max_right _ _) hw

theorem clipLength_le (x w : ℝ) : clipLength x w ≤ w := min_le_right _ _

theorem clipLength_of_nonpos {x : ℝ} (w : ℝ) (hx : x ≤ 0) (hw : 0 ≤ w) : clipLength x w = 0 := by
  rw [clipLength, max_eq_right hx, min_eq_left hw]

theorem clipLength_of_le {x w : ℝ} (hwx : w ≤ x) (hw : 0 ≤ w) : clipLength x w = w := by
  rw [clipLength, max_eq_left (hw.trans hwx), min_eq_right hwx]

@[simp] theorem clipLength_zero_right (x : ℝ) : clipLength x 0 = 0 :=
  min_eq_right (le_max_right _ _)

theorem monotone_clipLength (w : ℝ) : Monotone (fun x => clipLength x w) :=
  fun _ _ h => min_le_min_right _ (max_le_max_right _ h)

theorem clipLength_min (x y w : ℝ) :
    clipLength (min x y) w = min (clipLength x w) (clipLength y w) :=
  (monotone_clipLength w).map_min

/-- Two consecutive segments of lengths `W` and `w` form one segment of length `W + w`. -/
theorem clipLength_add (x : ℝ) {W w : ℝ} (hW : 0 ≤ W) (hw : 0 ≤ w) :
    clipLength x W + clipLength (x - W) w = clipLength x (W + w) := by
  simp only [clipLength]
  rcases le_total x 0 with h0 | h0
  · rw [max_eq_right h0, max_eq_right (by linarith), min_eq_left hW, min_eq_left hw,
      min_eq_left (by linarith)]
    ring
  rw [max_eq_left h0]
  rcases le_total x W with h1 | h1
  · rw [max_eq_right (by linarith), min_eq_left h1, min_eq_left hw, min_eq_left (by linarith)]
    ring
  rw [max_eq_left (by linarith), min_eq_right h1]
  rcases le_total (x - W) w with h2 | h2
  · rw [min_eq_left h2, min_eq_left (by linarith)]
    ring
  · rw [min_eq_right h2, min_eq_right (by linarith)]

/-- The CDF contribution of a segment starting at `s` of length `w`, written with minima. -/
theorem min_sub_min_eq_clipLength (u s : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    min u (s + w) - min u s = clipLength (u - s) w := by
  simp only [clipLength]
  rcases le_total u s with h0 | h0
  · rw [min_eq_left (by linarith), min_eq_left h0, max_eq_right (by linarith),
      min_eq_left hw]
    ring
  rw [min_eq_right h0, max_eq_left (by linarith)]
  rcases le_total u (s + w) with h1 | h1
  · rw [min_eq_left h1, min_eq_left (by linarith)]
  · rw [min_eq_right h1, min_eq_right (by linarith)]
    ring

variable {M : ℕ}

/-- The sum of the weights with index below `t`. -/
def prefixSum (w : Fin M → ℝ) (t : ℕ) : ℝ := ∑ j : Fin M, if j.val < t then w j else 0

@[simp] theorem prefixSum_zero (w : Fin M → ℝ) : prefixSum w 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_of_le (w : Fin M → ℝ) {t : ℕ} (ht : M ≤ t) : prefixSum w t = ∑ j, w j :=
  Finset.sum_congr rfl fun j _ => by simp [j.isLt.trans_le ht]

theorem prefixSum_nonneg {w : Fin M → ℝ} (hw : ∀ k, 0 ≤ w k) (t : ℕ) : 0 ≤ prefixSum w t :=
  Finset.sum_nonneg fun j _ => by split_ifs; exacts [hw j, le_rfl]

theorem prefixSum_le_sum {w : Fin M → ℝ} (hw : ∀ k, 0 ≤ w k) (t : ℕ) :
    prefixSum w t ≤ ∑ j, w j :=
  Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, hw j]

theorem prefixSum_mono {w : Fin M → ℝ} (hw : ∀ k, 0 ≤ w k) : Monotone (prefixSum w) := by
  intro t t' h
  apply Finset.sum_le_sum
  intro j _
  by_cases h1 : j.val < t
  · simp [h1, h1.trans_le h]
  · simp only [h1, ite_false]
    split_ifs
    exacts [hw j, le_rfl]

theorem prefixSum_succ (w : Fin M → ℝ) (k : Fin M) :
    prefixSum w (k.val + 1) = prefixSum w k.val + w k := by
  have hk : w k = ∑ j, if j = k then w j else 0 := by simp
  simp only [prefixSum]
  rw [hk, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjk : j = k
  · subst hjk; simp
  · have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    by_cases hlt : j.val < k.val
    · simp [hlt, Nat.lt_succ_of_lt hlt, hjk]
    · have : ¬ j.val < k.val + 1 := by omega
      simp [hlt, this, hjk]

theorem prefixSum_castSucc (w : Fin (M + 1) → ℝ) {t : ℕ} (ht : t ≤ M) :
    prefixSum w t = prefixSum (fun j => w j.castSucc) t := by
  simp only [prefixSum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  simp [show ¬ M < t by omega]

/-- Consecutive segments with lengths `w 0, w 1, …` fill a segment of the total length. -/
theorem sum_clipLength_prefixSum (w : Fin M → ℝ) (hw : ∀ k, 0 ≤ w k) (x : ℝ) :
    ∑ k : Fin M, clipLength (x - prefixSum w k.val) (w k) = clipLength x (∑ k, w k) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h1 : ∀ k : Fin M, prefixSum w (k.castSucc : Fin (M + 1)) =
        prefixSum (fun j => w j.castSucc) k := fun k =>
      prefixSum_castSucc w (by simp only [Fin.val_castSucc]; exact k.isLt.le)
    simp_rw [h1]
    rw [ih (fun j => w j.castSucc) (fun j => hw _), Fin.val_last,
      prefixSum_castSucc w le_rfl, prefixSum_of_le _ le_rfl]
    exact clipLength_add x (Finset.sum_nonneg fun j _ => hw _) (hw _)

/-! ### The partition of the positive weights -/

/-- The indices of the positive weights. -/
noncomputable def posWeights (w : Fin M → ℝ) : Finset (Fin M) := Finset.univ.filter fun k => 0 < w k

theorem mem_posWeights {w : Fin M → ℝ} {k : Fin M} : k ∈ posWeights w ↔ 0 < w k := by
  simp [posWeights]

section OfWeights

variable (w : Fin M → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) {N : ℕ}
  (hN : (posWeights w).card = N)

/-- The `j`th positive weight index, in increasing order. -/
noncomputable def posIndex (j : Fin N) : Fin M := ((posWeights w).orderIsoOfFin hN j : Fin M)

theorem posIndex_strictMono : StrictMono (posIndex w hN) := fun _ _ h =>
  ((posWeights w).orderIsoOfFin hN).strictMono h

theorem posIndex_pos (j : Fin N) : 0 < w (posIndex w hN j) :=
  mem_posWeights.1 ((posWeights w).orderIsoOfFin hN j).property

theorem exists_posIndex_eq {k : Fin M} (hk : 0 < w k) : ∃ j, posIndex w hN j = k :=
  ⟨((posWeights w).orderIsoOfFin hN).symm ⟨k, mem_posWeights.2 hk⟩, by simp [posIndex]⟩

include hw0 in
/-- Sums over all indices reduce to sums over the positive weights. -/
theorem sum_posIndex (g : Fin M → ℝ) (hg : ∀ k, w k = 0 → g k = 0) :
    ∑ j, g (posIndex w hN j) = ∑ k, g k := by
  apply Fintype.sum_of_injective _ (posIndex_strictMono w hN).injective
  · intro k hk
    apply hg
    by_contra hne
    exact hk (exists_posIndex_eq w hN (lt_of_le_of_ne (hw0 k) (Ne.symm hne)))
  · intro j; rfl

include hw0 in
theorem prefixSum_posIndex (j : Fin N) :
    prefixSum (fun j => w (posIndex w hN j)) j.val = prefixSum w (posIndex w hN j).val := by
  simp only [prefixSum]
  rw [← sum_posIndex w hw0 hN]
  · apply Finset.sum_congr rfl
    intro i _
    have : i.val < j.val ↔ (posIndex w hN i).val < (posIndex w hN j).val := by
      rw [← Fin.lt_def, ← Fin.lt_def]
      exact (posIndex_strictMono w hN).lt_iff_lt.symm
    simp only [this]
  · intro k hk
    simp [hk]

include hw0 hw1 in
theorem prefixSum_posIndex_le_one (t : ℕ) :
    prefixSum (fun j => w (posIndex w hN j)) t ≤ 1 := by
  refine (prefixSum_le_sum (fun j => hw0 _) t).trans ?_
  rw [sum_posIndex w hw0 hN w (fun _ h => h), hw1]

/-- The interval partition whose cells are the positive weights, in increasing order. -/
noncomputable def IntervalPartition.ofWeights : IntervalPartition N where
  point i := ⟨prefixSum (fun j => w (posIndex w hN j)) i,
    prefixSum_nonneg (fun j => hw0 _) i, prefixSum_posIndex_le_one w hw0 hw1 hN i⟩
  strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    change prefixSum _ i.castSucc.val < prefixSum _ i.succ.val
    rw [Fin.val_succ, prefixSum_succ, Fin.val_castSucc]
    linarith [posIndex_pos w hN i]
  zero := by apply Subtype.ext; simp
  one := by
    apply Subtype.ext
    change prefixSum _ (Fin.last N).val = 1
    rw [prefixSum_of_le _ (by simp), sum_posIndex w hw0 hN w (fun _ h => h), hw1]

theorem IntervalPartition.width_ofWeights (j : Fin N) :
    (IntervalPartition.ofWeights w hw0 hw1 hN).width j = w (posIndex w hN j) := by
  change prefixSum _ j.succ.val - prefixSum _ j.castSucc.val = _
  rw [Fin.val_succ, prefixSum_succ, Fin.val_castSucc]
  ring

theorem IntervalPartition.point_ofWeights_castSucc (j : Fin N) :
    ((IntervalPartition.ofWeights w hw0 hw1 hN).point j.castSucc : ℝ) =
      prefixSum w (posIndex w hN j).val := by
  change prefixSum _ j.castSucc.val = _
  rw [Fin.val_castSucc]
  exact prefixSum_posIndex w hw0 hN j

theorem IntervalPartition.width_mul_coord_ofWeights (j : Fin N) (u : I) :
    (IntervalPartition.ofWeights w hw0 hw1 hN).width j *
        ((IntervalPartition.ofWeights w hw0 hw1 hN).coord j u : ℝ) =
      clipLength (u - prefixSum w (posIndex w hN j).val) (w (posIndex w hN j)) := by
  set P := IntervalPartition.ofWeights w hw0 hw1 hN
  rw [P.width_mul_coord]
  have hs : (P.point j.succ : ℝ) = P.point j.castSucc + P.width j := by
    simp only [IntervalPartition.width]; ring
  rw [hs, IntervalPartition.width_ofWeights, IntervalPartition.point_ofWeights_castSucc]
  exact min_sub_min_eq_clipLength _ _ (hw0 _)

end OfWeights

/-! ### The shuffle of a weight vector -/

section Shuffle

variable (w : Fin M → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1) (π : Equiv.Perm (Fin M))

/-- The weights listed in target order. -/
def targetWeights (k : Fin M) : ℝ := w (π.symm k)

include hw0 in
theorem targetWeights_nonneg (k : Fin M) : 0 ≤ targetWeights w π k := hw0 _

include hw1 in
theorem sum_targetWeights : ∑ k, targetWeights w π k = 1 := by
  rw [← hw1]
  exact Equiv.sum_comp π.symm w

theorem mem_posWeights_iff_perm (k : Fin M) :
    k ∈ posWeights w ↔ π k ∈ posWeights (targetWeights w π) := by
  simp [mem_posWeights, targetWeights]

theorem card_posWeights_targetWeights :
    (posWeights (targetWeights w π)).card = (posWeights w).card := by
  refine (Finset.card_bij (fun k _ => π.symm k) ?_ ?_ ?_)
  · intro k hk
    simpa [mem_posWeights, targetWeights] using hk
  · intro a _ b _ h
    exact π.symm.injective h
  · intro k hk
    exact ⟨π k, by simpa [mem_posWeights, targetWeights] using hk, by simp⟩

/-- The target offset of piece `k`: the total weight of the pieces placed before it. -/
def targetOffset (k : Fin M) : ℝ := prefixSum (targetWeights w π) (π k).val

theorem targetOffset_eq (k : Fin M) :
    targetOffset w π k = ∑ j, if (π j).val < (π k).val then w j else 0 := by
  simp only [targetOffset, prefixSum, targetWeights]
  exact (Equiv.sum_comp π (fun l => if l.val < (π k).val then w (π.symm l) else 0)).symm.trans
    (by simp)

/-- The source partition of the positive pieces. -/
noncomputable def shuffleSource : IntervalPartition (posWeights w).card :=
  IntervalPartition.ofWeights w hw0 hw1 rfl

/-- The target partition of the positive pieces. -/
noncomputable def shuffleTarget : IntervalPartition (posWeights w).card :=
  IntervalPartition.ofWeights (targetWeights w π) (targetWeights_nonneg w hw0 π)
    (sum_targetWeights w hw1 π) (card_posWeights_targetWeights w π)

/-- The permutation of the positive pieces induced by `π`. -/
noncomputable def shufflePerm : Equiv.Perm (Fin (posWeights w).card) :=
  ((posWeights w).orderIsoOfFin rfl).toEquiv.trans
    ((π.subtypeEquiv (mem_posWeights_iff_perm w π)).trans
      ((posWeights (targetWeights w π)).orderIsoOfFin
        (card_posWeights_targetWeights w π)).toEquiv.symm)

theorem posIndex_shufflePerm (j : Fin (posWeights w).card) :
    posIndex (targetWeights w π) (card_posWeights_targetWeights w π) (shufflePerm w π j) =
      π (posIndex w rfl j) := by
  simp [posIndex, shufflePerm]

theorem shuffle_hwidth (j : Fin (posWeights w).card) :
    (shuffleSource w hw0 hw1).width j =
      (shuffleTarget w hw0 hw1 π).width (shufflePerm w π j) := by
  rw [shuffleSource, shuffleTarget, IntervalPartition.width_ofWeights,
    IntervalPartition.width_ofWeights, posIndex_shufflePerm]
  simp [targetWeights]

/-- The straight shuffle of `M` with source weights `w` (in order) and target order `π`.
Pieces of weight zero are discarded, so this is a genuine `shuffleOfMin`. -/
noncomputable def weightShuffle : Copula 2 :=
  shuffleOfMin (shuffleSource w hw0 hw1) (shuffleTarget w hw0 hw1 π) (shufflePerm w π)
    (shuffle_hwidth w hw0 hw1 π) (fun _ => false)

theorem isStraightShuffleOfMin_weightShuffle :
    (weightShuffle w hw0 hw1 π).IsStraightShuffleOfMin :=
  isStraightShuffleOfMin_shuffleOfMin _ _ _ _

/-- CDF of a weight shuffle: piece `k` contributes the length of its diagonal segment below
`(u, v)`. -/
theorem cdf_weightShuffle (u v : I) :
    (weightShuffle w hw0 hw1 π).cdf ![u, v] =
      ∑ k : Fin M, min (clipLength (u - prefixSum w k.val) (w k))
        (clipLength (v - targetOffset w π k) (w k)) := by
  rw [weightShuffle, cdf_shuffleOfMin]
  simp only [Bool.false_eq_true, ite_false]
  have hterm (j : Fin (posWeights w).card) :
      (shuffleSource w hw0 hw1).width j * min ((shuffleSource w hw0 hw1).coord j u : ℝ)
          ((shuffleTarget w hw0 hw1 π).coord (shufflePerm w π j) v : ℝ) =
        min (clipLength (u - prefixSum w (posIndex w rfl j).val) (w (posIndex w rfl j)))
          (clipLength (v - targetOffset w π (posIndex w rfl j)) (w (posIndex w rfl j))) := by
    rw [mul_min_of_nonneg _ _ ((shuffleSource w hw0 hw1).width_pos j).le]
    congr 1
    · exact IntervalPartition.width_mul_coord_ofWeights w hw0 hw1 rfl j u
    · rw [shuffle_hwidth w hw0 hw1 π j, shuffleTarget,
        IntervalPartition.width_mul_coord_ofWeights, posIndex_shufflePerm]
      simp [targetWeights, targetOffset]
  simp_rw [hterm]
  exact sum_posIndex w hw0 rfl (fun k => min (clipLength (u - prefixSum w k.val) (w k))
    (clipLength (v - targetOffset w π k) (w k))) (fun k hk => by simp [hk])

end Shuffle

end ProbabilityTheory.Copula
