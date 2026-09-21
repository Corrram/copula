/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.CompleteSums
import Copula.Rank.Region.RhoTau.FiniteMinimum

open scoped BigOperators unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem a_le_complete (S : SignData ι) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    S.a u ≤ completeSigns.a u := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (hu j)
  apply mul_le_mul_of_nonneg_right _ (hu i)
  rw [complete_inversion]
  by_cases h : i = j
  · subst j; simp
  · simp only [h, ite_false]
    rcases S.values i j with he | he <;> norm_num [SignData.inversion, he]

theorem two_weight_witness {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 4) :
    ∃ v : Fin 2 → ℝ, (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 ∧
      completeSigns.a v = a ∧ completeSigns.b v = 0 := by
  obtain ⟨s, hs⟩ := exists_unitInterval_eq (z := a)
    (f := fun s : I => ((s : ℝ) / 2) * (1 - (s : ℝ) / 2)) (by fun_prop)
    (by simpa using ha) (by norm_num; exact ha')
  let v : Fin 2 → ℝ := ![(s : ℝ) / 2, 1 - (s : ℝ) / 2]
  have hsum : ∑ i, v i = 1 := by simp [v, Fin.sum_univ_two]
  refine ⟨v, ?_, hsum, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact div_nonneg s.property.1 (by norm_num)
    · dsimp [v]; linarith [s.property.2]
  · rw [complete_a, hsum]
    simp only [v, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith only [hs]
  · rw [complete_b, hsum]
    simp only [v, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

omit [DecidableEq ι] in
theorem small_inversion_complete (S : SignData ι) (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (ha : S.a u ≤ 1 / 4) :
    ∃ v : Fin 2 → ℝ, (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 ∧
      completeSigns.a v = S.a u ∧ completeSigns.b v ≤ S.b u := by
  obtain ⟨v, hv, hs, he, hb⟩ := two_weight_witness (S.a_nonneg u hu) ha
  exact ⟨v, hv, hs, he, by rw [hb]; exact S.b_nonneg u hu⟩

theorem a_le_quarter_of_card_le_two {n : ℕ} (hn : n ≤ 2) (S : SignData (Fin n))
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) : S.a u ≤ 1 / 4 := by
  have h := a_le_complete S u hu
  rw [complete_a, hs] at h
  interval_cases n
  · simp at hs
  · simp only [Fin.sum_univ_one] at hs h
    nlinarith
  · simp only [Fin.sum_univ_two] at hs h
    nlinarith [sq_nonneg (u 0 - u 1)]

theorem exists_third_index {n : ℕ} (hn : 3 ≤ n) (p q : Fin n) :
    ∃ k : Fin n, k ≠ p ∧ k ≠ q := by
  classical
  by_contra h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {p, q} := by
    intro i _
    by_cases hip : i = p
    · simp [hip]
    have hiq : i = q := by by_contra hiq; exact h ⟨i, hip, hiq⟩
    simp [hiq]
  have hc := Finset.card_le_card hsub
  have htwo : ({p, q} : Finset (Fin n)).card ≤ 2 := by
    by_cases he : p = q <;> simp [he]
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

end ProbabilityTheory.Copula.RankRegion.RhoTau
