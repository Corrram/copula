/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.ThreeCoordinates
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Minimizing the third power sum at fixed first and second power sums -/

open scoped BigOperators
open Set

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {ι : Type*} [Fintype ι]

def momentFibre (q : ℝ) : Set (ι → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 ∧ ∑ i, (u i) ^ 2 = q}

theorem isCompact_momentFibre (q : ℝ) : IsCompact (momentFibre (ι := ι) q) := by
  have hc : IsClosed (momentFibre (ι := ι) q) := by
    have hnonneg : IsClosed {u : ι → ℝ | ∀ i, 0 ≤ u i} :=
      by
        simpa only [Set.ofPred_forall] using
          (isClosed_iInter fun i : ι =>
            isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply i))
    exact hnonneg.inter ((isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const))
  apply isCompact_Icc.of_isClosed_subset hc
  intro u hu
  refine ⟨hu.1, fun i => ?_⟩
  have h := Finset.single_le_sum (s := Finset.univ) (f := u)
    (fun j _ => hu.1 j) (Finset.mem_univ i)
  simpa only [hu.2.1, Pi.one_apply] using h

theorem exists_min_powerSum_three (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ v : ι → ℝ, v ∈ momentFibre (∑ i, (u i) ^ 2) ∧
      (∑ i, (v i) ^ 3) ≤ ∑ i, (u i) ^ 3 ∧
      ∀ (w : ι → ℝ), w ∈ momentFibre (∑ i, (u i) ^ 2) → (∑ i, (v i) ^ 3) ≤ ∑ i, (w i) ^ 3 := by
  have hmem : u ∈ momentFibre (∑ i, (u i) ^ 2) := ⟨hu, hs, rfl⟩
  obtain ⟨v, hv, hmin⟩ := (isCompact_momentFibre (ι := ι) (∑ i, (u i) ^ 2)).exists_isMinOn
    ⟨u, hmem⟩ (by fun_prop : ContinuousOn (fun w : ι → ℝ => ∑ i, (w i) ^ 3) _)
  exact ⟨v, hv, hmin hmem, fun w hw => hmin hw⟩

variable [DecidableEq ι]

def replaceThree (u : ι → ℝ) (i j k : ι) (a b c : ℝ) : ι → ℝ :=
  Function.update (Function.update (Function.update u i a) j b) k c

theorem sum_replaceThree (u : ι → ℝ) (i j k : ι) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a b c : ℝ) (f : ℝ → ℝ) :
    (∑ l, f (replaceThree u i j k a b c l)) =
      (∑ l, f (u l)) - f (u i) - f (u j) - f (u k) + f a + f b + f c := by
  have hupdate (v : ι → ℝ) (l : ι) (r : ℝ) :
      (∑ m, f (Function.update v l r m)) = (∑ m, f (v m)) - f (v l) + f r := by
    rw [show (fun m => f (Function.update v l r m)) =
      Function.update (fun m => f (v m)) l (f r) by
        funext m; by_cases h : m = l <;> simp [h]]
    rw [Finset.sum_update_of_mem (Finset.mem_univ l), Finset.sdiff_singleton_eq_erase]
    have h := Finset.sum_erase_add Finset.univ (fun m => f (v m)) (Finset.mem_univ l)
    linarith
  simp only [replaceThree, hupdate, Function.update_of_ne (Ne.symm hij),
    Function.update_of_ne (Ne.symm hik), Function.update_of_ne (Ne.symm hjk)]
  ring

/-- At a minimizing vector, no positive triple has a unique largest entry. -/
theorem minimizing_no_unique_largest {q : ℝ} {v : ι → ℝ}
    (hv : v ∈ momentFibre q)
    (hmin : ∀ (w : ι → ℝ), w ∈ momentFibre q → (∑ i, (v i) ^ 3) ≤ ∑ i, (w i) ^ 3)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hxy : v j < v i) (hyz : v k ≤ v j) (hz : 0 < v k) : False := by
  obtain ⟨a, b, c, ha, hb, hc, hs, hsq, hcube⟩ := improve_three_coordinates hxy hyz hz
  let w := replaceThree v i j k a b c
  have hw : w ∈ momentFibre q := by
    refine ⟨?_, ?_, ?_⟩
    · intro l
      dsimp [w, replaceThree]
      by_cases hk : l = k
      · subst l; simp [hc.le]
      by_cases hj : l = j
      · subst l; simp [hk, hb.le]
      by_cases hi : l = i
      · subst l; simp [hk, hj, ha.le]
      simp [hk, hj, hi, hv.1 l]
    · change (∑ l, (id : ℝ → ℝ) (replaceThree v i j k a b c l)) = 1
      rw [sum_replaceThree v i j k hij hik hjk a b c id]
      dsimp
      linarith [hv.2.1]
    · change (∑ l, (replaceThree v i j k a b c l) ^ 2) = q
      rw [sum_replaceThree v i j k hij hik hjk a b c (fun r => r ^ 2)]
      linarith [hv.2.2]
  have hh := hmin w hw
  dsimp [w] at hh
  rw [sum_replaceThree v i j k hij hik hjk a b c (fun r => r ^ 3)] at hh
  linarith


/-- A minimizer has equal positive coordinates, apart from at most one smaller coordinate. -/
theorem minimizing_shape {q : ℝ} {v : ι → ℝ} (hv : v ∈ momentFibre q)
    (hmin : ∀ (w : ι → ℝ), w ∈ momentFibre q → (∑ i, (v i) ^ 3) ≤ ∑ i, (w i) ^ 3) :
    ∃ k : ℕ, ∃ r b : ℝ, 0 < k ∧ 0 < r ∧ 0 ≤ b ∧ b ≤ r ∧
      (∀ p : ℕ, 0 < p → (∑ i, (v i) ^ p) = k * r ^ p + b ^ p) := by
  classical
  have hpos : ∃ i, 0 < v i := by
    by_contra h
    push Not at h
    have he : ∀ i, v i = 0 := fun i => le_antisymm (h i) (hv.1 i)
    have hvsum := hv.2.1
    simp [he] at hvsum
  obtain ⟨i₀, hi₀⟩ := hpos
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ v ⟨i₀, Finset.mem_univ _⟩
  have hmax (j : ι) : v j ≤ v i := hi j (Finset.mem_univ _)
  have hir : 0 < v i := hi₀.trans_le (hmax i₀)
  have huniq (j k : ι) (hj : 0 < v j) (hj' : v j < v i)
      (hk : 0 < v k) (hk' : v k < v i) : j = k := by
    by_contra hjk
    have hij : i ≠ j := by intro h; subst j; exact lt_irrefl _ hj'
    have hik : i ≠ k := by intro h; subst k; exact lt_irrefl _ hk'
    rcases le_total (v k) (v j) with h | h
    · exact minimizing_no_unique_largest hv hmin i j k hij hik hjk hj' h hk
    · exact minimizing_no_unique_largest hv hmin i k j hik hij (Ne.symm hjk) hk' h hj
  let S := Finset.univ.filter (fun j => v j = v i)
  have hiS : i ∈ S := by simp [S]
  have hS : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
  have hsum (p : ℕ) : (∑ j : ι, if v j = v i then (v i) ^ p else 0) =
      (S.card : ℝ) * (v i) ^ p := by
    rw [← Finset.sum_filter]
    simp [S]
  by_cases hb : ∃ j, 0 < v j ∧ v j < v i
  · obtain ⟨j, hj, hji⟩ := hb
    refine ⟨S.card, v i, v j, hS, hir, hj.le, hji.le, ?_⟩
    intro p hp
    have he (l : ι) : (v l) ^ p =
        (if v l = v i then (v i) ^ p else 0) + (if l = j then (v j) ^ p else 0) := by
      by_cases hlj : l = j
      · subst l
        simp [ne_of_lt hji]
      by_cases hl : v l = v i
      · simp [hl, hlj]
      have hz : v l = 0 := by
        by_contra hz
        have hlow : 0 < v l := lt_of_le_of_ne (hv.1 l) (Ne.symm hz)
        exact hlj (huniq l j hlow (lt_of_le_of_ne (hmax l) hl) hj hji)
      simp [hz, Ne.symm (ne_of_gt hir), hlj, ne_of_gt hp]
    rw [Finset.sum_congr rfl (fun l _ => he l)]
    rw [Finset.sum_add_distrib, hsum]
    simp
  · refine ⟨S.card, v i, 0, hS, hir, le_rfl, hir.le, ?_⟩
    intro p hp
    have he (l : ι) : (v l) ^ p = if v l = v i then (v i) ^ p else 0 := by
      by_cases hl : v l = v i
      · simp [hl]
      have hz : v l = 0 := by
        by_contra hz
        exact hb ⟨l, lt_of_le_of_ne (hv.1 l) (Ne.symm hz),
          lt_of_le_of_ne (hmax l) hl⟩
      simp [hz, Ne.symm (ne_of_gt hir), ne_of_gt hp]
    rw [Finset.sum_congr rfl (fun l _ => he l)]
    rw [hsum]
    simp [ne_of_gt hp]

/-- Finite-dimensional symmetric-polynomial minimization, with an explicit
two-level shape and no assumed extremal inequality. -/
theorem powerSum_prototype (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ k : ℕ, ∃ r b : ℝ, 0 < k ∧ 0 < r ∧ 0 ≤ b ∧ b ≤ r ∧
      k * r + b = 1 ∧ k * r ^ 2 + b ^ 2 = ∑ i, (u i) ^ 2 ∧
      k * r ^ 3 + b ^ 3 ≤ ∑ i, (u i) ^ 3 := by
  obtain ⟨v, hv, hle, hmin⟩ := exists_min_powerSum_three u hu hs
  obtain ⟨k, r, b, hk, hr, hb, hbr, hm⟩ := minimizing_shape hv hmin
  refine ⟨k, r, b, hk, hr, hb, hbr, ?_, ?_, ?_⟩
  · have h := hm 1 (by decide)
    simpa only [pow_one, hv.2.1] using h.symm
  · exact (hm 2 (by decide)).symm.trans hv.2.2
  · rwa [hm 3 (by decide)] at hle

end ProbabilityTheory.Copula.RankRegion.RhoTau
