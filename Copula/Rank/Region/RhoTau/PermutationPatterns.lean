/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-! # Pattern avoidance in the permutation reduction

The non-endpoint case of Schreyer–Paulin–Trutschnig, Lemma 4.9.
The two excluded patterns are 123 and 3412.
-/

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {n : ℕ}

def NoIncreasingTriple (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k, i < j → j < k → ¬(π i < π j ∧ π j < π k)

def No3412 (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k l, i < j → j < k → k < l → ¬(π k < π l ∧ π l < π i ∧ π i < π j)

def TwoDecreasingBlocks (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ c : Fin n, ∀ i j, i < j → (j ≤ c ∨ c < i) → π j < π i

theorem NoIncreasingTriple.inverse {π : Equiv.Perm (Fin n)} (h : NoIncreasingTriple π) :
    NoIncreasingTriple π.symm := by
  intro i j k hij hjk hp
  apply h (π.symm i) (π.symm j) (π.symm k) hp.1 hp.2
  simpa using And.intro hij hjk

theorem min_before_max_blocks (π : Equiv.Perm (Fin (n + 2)))
    (h : NoIncreasingTriple π) (horder : π.symm 0 < π.symm (Fin.last (n + 1))) :
    TwoDecreasingBlocks π := by
  have hzval : (0 : Fin (n + 2)).val = 0 := rfl
  have hlval : (Fin.last (n + 1)).val = n + 1 := rfl
  let lo := π.symm 0
  let hi := π.symm (Fin.last (n + 1))
  have hlo : π lo = 0 := π.apply_symm_apply _
  have hhi : π hi = Fin.last (n + 1) := π.apply_symm_apply _
  have hgap : hi.val = lo.val + 1 := by
    by_contra he
    have hroom : lo.val + 1 < n + 2 := by omega
    let j : Fin (n + 2) := ⟨lo.val + 1, hroom⟩
    have hjval : j.val = lo.val + 1 := rfl
    have hlj : lo < j := by omega
    have hjh : j < hi := by omega
    have hj0 : π j ≠ 0 := by
      intro heq
      have hjlo := π.injective (heq.trans hlo.symm)
      exact (ne_of_gt hlj) hjlo
    have hjmax : π j ≠ Fin.last (n + 1) := by
      intro heq
      have hjhi := π.injective (heq.trans hhi.symm)
      exact (ne_of_lt hjh) hjhi
    apply h lo j hi hlj hjh
    rw [hlo, hhi]
    constructor <;> omega
  refine ⟨lo, ?_⟩
  intro i j hij hc
  have hne : π i ≠ π j := fun he => (ne_of_lt hij) (π.injective he)
  by_contra hbad
  have hinc : π i < π j := lt_of_le_of_ne (le_of_not_gt hbad) hne
  rcases hc with hjlo | hli
  · have hjhi : j < hi := by omega
    have hjmax : π j ≠ Fin.last (n + 1) := by
      intro he
      exact (ne_of_lt hjhi) (π.injective (he.trans hhi.symm))
    apply h i j hi hij hjhi
    refine ⟨hinc, ?_⟩
    rw [hhi]
    omega
  · have hi0 : π i ≠ 0 := by
      intro he
      exact (ne_of_gt hli) (π.injective (he.trans hlo.symm))
    apply h lo i j hli hij
    refine ⟨?_, hinc⟩
    rw [hlo]
    omega

/-- Unless an endpoint can be stripped off, the permutation or its inverse
splits into two decreasing blocks. -/
theorem avoiding_patterns_blocks (π : Equiv.Perm (Fin (n + 2)))
    (h123 : NoIncreasingTriple π) (h3412 : No3412 π)
    (hfirst : π 0 ≠ Fin.last (n + 1)) (hlast : π (Fin.last (n + 1)) ≠ 0) :
    TwoDecreasingBlocks π ∨ TwoDecreasingBlocks π.symm := by
  have hzval : (0 : Fin (n + 2)).val = 0 := rfl
  have hlval : (Fin.last (n + 1)).val = n + 1 := rfl
  by_cases ho : π.symm 0 < π.symm (Fin.last (n + 1))
  · exact Or.inl (min_before_max_blocks π h123 ho)
  have hne : π.symm 0 ≠ π.symm (Fin.last (n + 1)) := by
    intro he
    have hh := π.symm.injective he
    have : (0 : Fin (n + 2)).val = (Fin.last (n + 1)).val := congrArg Fin.val hh
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  have hreverse : π.symm (Fin.last (n + 1)) < π.symm 0 :=
    lt_of_le_of_ne (le_of_not_gt ho) (Ne.symm hne)
  have hfirstpos : 0 < π.symm (Fin.last (n + 1)) := by
    by_contra hh
    have he : π.symm (Fin.last (n + 1)) = 0 := by omega
    have he' := congrArg π he
    simp only [Equiv.apply_symm_apply] at he'
    exact hfirst he'.symm
  have hlastlt : π.symm 0 < Fin.last (n + 1) := by
    by_contra hh
    have he : π.symm 0 = Fin.last (n + 1) := by omega
    have he' := congrArg π he
    simp only [Equiv.apply_symm_apply] at he'
    exact hlast he'.symm
  have hends : π 0 < π (Fin.last (n + 1)) := by
    by_contra hh
    have hnends : π 0 ≠ π (Fin.last (n + 1)) := by
      intro he
      have hv := congrArg Fin.val (π.injective he)
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    have hlt : π (Fin.last (n + 1)) < π 0 :=
      lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hnends)
    apply h3412 0 (π.symm (Fin.last (n + 1))) (π.symm 0) (Fin.last (n + 1))
      hfirstpos hreverse hlastlt
    simp only [Equiv.apply_symm_apply]
    exact ⟨by omega, hlt, by omega⟩
  apply Or.inr
  apply min_before_max_blocks π.symm h123.inverse
  simpa using hends


theorem extrema_orientation (π : Equiv.Perm (Fin (n + 2)))
    (h3412 : No3412 π) (hfirst : π 0 ≠ Fin.last (n + 1))
    (hlast : π (Fin.last (n + 1)) ≠ 0) :
    π.symm 0 < π.symm (Fin.last (n + 1)) ∨ π 0 < π (Fin.last (n + 1)) := by
  have hzval : (0 : Fin (n + 2)).val = 0 := rfl
  have hlval : (Fin.last (n + 1)).val = n + 1 := rfl
  by_cases ho : π.symm 0 < π.symm (Fin.last (n + 1))
  · exact Or.inl ho
  have hne : π.symm 0 ≠ π.symm (Fin.last (n + 1)) := by
    intro he
    have hh := congrArg Fin.val (π.symm.injective he)
    simp only [Fin.val_zero, Fin.val_last] at hh
    omega
  have hreverse : π.symm (Fin.last (n + 1)) < π.symm 0 :=
    lt_of_le_of_ne (le_of_not_gt ho) (Ne.symm hne)
  have hfirstpos : 0 < π.symm (Fin.last (n + 1)) := by
    by_contra hh
    have he : π.symm (Fin.last (n + 1)) = 0 := by omega
    have he' := congrArg π he
    simp only [Equiv.apply_symm_apply] at he'
    exact hfirst he'.symm
  have hlastlt : π.symm 0 < Fin.last (n + 1) := by
    by_contra hh
    have he : π.symm 0 = Fin.last (n + 1) := by omega
    have he' := congrArg π he
    simp only [Equiv.apply_symm_apply] at he'
    exact hlast he'.symm
  apply Or.inr
  by_contra hh
  have hnends : π 0 ≠ π (Fin.last (n + 1)) := by
    intro he
    have hv := congrArg Fin.val (π.injective he)
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  have hlt : π (Fin.last (n + 1)) < π 0 :=
    lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm hnends)
  apply h3412 0 (π.symm (Fin.last (n + 1))) (π.symm 0) (Fin.last (n + 1))
    hfirstpos hreverse hlastlt
  simp only [Equiv.apply_symm_apply]
  exact ⟨by omega, hlt, by omega⟩

theorem extremal_entries_adjacent (π : Equiv.Perm (Fin (n + 2)))
    (h : NoIncreasingTriple π) (ho : π.symm 0 < π.symm (Fin.last (n + 1))) :
    (π.symm (Fin.last (n + 1))).val = (π.symm 0).val + 1 := by
  have hzval : (0 : Fin (n + 2)).val = 0 := rfl
  have hlval : (Fin.last (n + 1)).val = n + 1 := rfl
  let lo := π.symm 0
  let hi := π.symm (Fin.last (n + 1))
  have hlo : π lo = 0 := π.apply_symm_apply _
  have hhi : π hi = Fin.last (n + 1) := π.apply_symm_apply _
  by_contra he
  have hroom : lo.val + 1 < n + 2 := by omega
  let j : Fin (n + 2) := ⟨lo.val + 1, hroom⟩
  have hjval : j.val = lo.val + 1 := rfl
  have hlj : lo < j := by omega
  have hjh : j < hi := by omega
  have hj0 : π j ≠ 0 := by
    intro heq
    exact (ne_of_gt hlj) (π.injective (heq.trans hlo.symm))
  have hjmax : π j ≠ Fin.last (n + 1) := by
    intro heq
    exact (ne_of_lt hjh) (π.injective (heq.trans hhi.symm))
  apply h lo j hi hlj hjh
  rw [hlo, hhi]
  constructor <;> omega

end ProbabilityTheory.Copula.RankRegion.RhoTau
