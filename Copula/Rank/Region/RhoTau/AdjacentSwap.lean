/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PairFlip
import Copula.Rank.Region.RhoTau.Reindex

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {n : ℕ}

theorem adjacent_swap_lt {p q : Fin n} (hpq : q.val = p.val + 1) (i j : Fin n)
    (h : ¬((i = p ∧ j = q) ∨ (i = q ∧ j = p))) :
    Equiv.swap p q i < Equiv.swap p q j ↔ i < j := by
  have hne : p ≠ q := by intro he; subst q; omega
  by_cases hip : i = p <;> by_cases hiq : i = q <;>
    by_cases hjp : j = p <;> by_cases hjq : j = q <;>
    simp_all [Equiv.swap_apply_def]
  all_goals omega

theorem adjacent_extremal_opposite (π : Equiv.Perm (Fin (n + 2)))
    {p q : Fin (n + 2)} (hgap : q.val = p.val + 1)
    (hp : π p = 0) (hq : π q = Fin.last (n + 1))
    (i : Fin (n + 2)) (hip : i ≠ p) (hiq : i ≠ q) :
    (permutationSigns π).edge p i = -(permutationSigns π).edge q i := by
  have hzval : (0 : Fin (n + 2)).val = 0 := rfl
  have hlval : (Fin.last (n + 1)).val = n + 1 := rfl
  have hi0 : π i ≠ 0 := fun he => hip (π.injective (he.trans hp.symm))
  have hi1 : π i ≠ Fin.last (n + 1) := fun he => hiq (π.injective (he.trans hq.symm))
  have hi0' : 0 < π i := by omega
  have hi1' : π i < Fin.last (n + 1) := by omega
  have hor : i < p ∨ q < i := by omega
  rcases hor with h | h
  · have hiq' : i < q := by omega
    simp [permutationSigns, IsInversion, hp, hq, hi0', hi1', h, hiq',
      not_lt_of_ge h.le, not_lt_of_ge hiq'.le, not_lt_of_ge hi0'.le,
      not_lt_of_ge hi1'.le]
  · have hpi : p < i := by omega
    simp [permutationSigns, IsInversion, hp, hq, hi0', hi1', h, hpi,
      not_lt_of_ge h.le, not_lt_of_ge hpi.le, not_lt_of_ge hi0'.le,
      not_lt_of_ge hi1'.le]

/-- Swapping the adjacent minimum and maximum flips exactly one signed edge,
after relabeling the weights by the same transposition. -/
theorem adjacent_extremal_flip (π : Equiv.Perm (Fin (n + 2)))
    {p q : Fin (n + 2)} (hgap : q.val = p.val + 1)
    (hp : π p = 0) (hq : π q = Fin.last (n + 1)) :
    (permutationSigns ((Equiv.swap p q).trans π)).relabel (Equiv.swap p q) =
      (permutationSigns π).flipPair p q (by intro he; subst q; omega) := by
  have hpq : p < q := by omega
  have h01 : (0 : Fin (n + 2)) < Fin.last (n + 1) := by
    change 0 < n + 1
    omega
  apply SignData.ext_edge
  intro i j
  by_cases hij : (i = p ∧ j = q) ∨ (i = q ∧ j = p)
  · rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [SignData.relabel, SignData.flipPair, permutationSigns, IsInversion,
        Equiv.trans_apply, hp, hq, hpq, h01, ne_of_lt hpq, Ne.symm (ne_of_lt hpq)]
  · have hji : ¬((j = p ∧ i = q) ∨ (j = q ∧ i = p)) := by tauto
    simp only [SignData.relabel, SignData.flipPair, hij, ite_false, permutationSigns,
      IsInversion, Equiv.trans_apply, Equiv.swap_apply_self,
      adjacent_swap_lt hgap i j hij, adjacent_swap_lt hgap j i hji]
    rfl


/-- A strictly positive weighted permutation with adjacent extremal entries
cannot minimize b at fixed a when a third strip is present. -/
theorem adjacent_extremal_improvement (π : Equiv.Perm (Fin (n + 2)))
    (u : Fin (n + 2) → ℝ) (hu : ∀ i, 0 < u i)
    {p q : Fin (n + 2)} (hgap : q.val = p.val + 1)
    (hp : π p = 0) (hq : π q = Fin.last (n + 1))
    (hthird : ∃ k : Fin (n + 2), k ≠ p ∧ k ≠ q) :
    ∃ σ : Equiv.Perm (Fin (n + 2)), ∃ w : Fin (n + 2) → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = ∑ i, u i ∧
      (permutationSigns σ).a w = (permutationSigns π).a u ∧
      (permutationSigns σ).b w < (permutationSigns π).b u := by
  classical
  have hpq : p < q := by omega
  have hne := ne_of_lt hpq
  let v : Fin (n + 2) → ℝ := fun i => if i = p ∨ i = q then 0 else u i
  have hv (i : Fin (n + 2)) : 0 ≤ v i := by
    dsimp [v]
    split
    · exact le_rfl
    · exact (hu i).le
  have hvp : v p = 0 := by simp [v]
  have hvq : v q = 0 := by simp [v]
  have hrest : 0 < ∑ i, v i := by
    obtain ⟨k, hkp, hkq⟩ := hthird
    have hk : 0 < v k := by simpa [v, hkp, hkq] using hu k
    exact hk.trans_le (Finset.single_le_sum (fun i _ => hv i) (Finset.mem_univ k))
  have hed : (permutationSigns π).edge p q = -1 := by
    apply edge_of_inversion_zero
    apply inversion_of_increasing π hpq
    rw [hp, hq]
    change 0 < n + 1
    omega
  obtain ⟨X, Y, hX, hY, hsum, ha, hb⟩ :=
    (permutationSigns π).extremal_pair_improvement p q hne v hv hvp hvq hed
      (fun i hip hiq => adjacent_extremal_opposite π hgap hp hq i hip hiq)
      (u p) (u q) (hu p) (hu q) hrest
  have huform : v + (u p • spike p + u q • spike q) = u := by
    funext i
    by_cases hip : i = p
    · subst i; simp [v, spike, hne]
    by_cases hiq : i = q
    · subst i; simp [v, spike, Ne.symm hne]
    simp [v, spike, hip, hiq]
  let V := v + (X • spike p + Y • spike q)
  let σ := (Equiv.swap p q).trans π
  let w := V ∘ Equiv.swap p q
  have hwform : w ∘ Equiv.swap p q = V := by funext i; simp [w]
  have hflip : (permutationSigns σ).relabel (Equiv.swap p q) =
      (permutationSigns π).flipPair p q hne := adjacent_extremal_flip π hgap hp hq
  have ha' := (permutationSigns σ).a_relabel (Equiv.swap p q) w
  have hb' := (permutationSigns σ).b_relabel (Equiv.swap p q) w
  rw [hflip, hwform] at ha' hb'
  rw [huform] at ha hb
  refine ⟨σ, w, ?_, ?_, ha'.symm.trans ha, ?_⟩
  · intro i
    dsimp [w, V]
    exact add_nonneg (hv _) (add_nonneg
      (mul_nonneg hX (by dsimp [spike]; split <;> norm_num))
      (mul_nonneg hY (by dsimp [spike]; split <;> norm_num)))
  · have hs := congrArg (fun f : Fin (n + 2) → ℝ => ∑ i, f i) huform
    dsimp [w]
    rw [Equiv.sum_comp (Equiv.swap p q) V]
    simp only [V, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, sum_spike, mul_one] at hs ⊢
    linarith
  · exact hb'.symm.trans_lt hb

end ProbabilityTheory.Copula.RankRegion.RhoTau
