/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PermutationSums
import Copula.Rank.Region.RhoTau.PowerSums

open scoped BigOperators
open Set

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

namespace SignData

variable {ι : Type*} [Fintype ι] (S : SignData ι)

theorem continuous_a : Continuous S.a := by
  unfold a bilinear
  fun_prop

theorem continuous_b : Continuous S.b := by
  unfold b trilinear
  fun_prop

theorem a_nonneg (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) : 0 ≤ S.a u := by
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have hi : 0 ≤ S.inversion i j := by
    rcases S.values i j with h | h <;> norm_num [inversion, h]
  exact mul_nonneg (mul_nonneg hi (hu i)) (hu j)

theorem b_nonneg (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) : 0 ≤ S.b u := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (S.triple_nonneg i j k) (hu i)) (hu j)) (hu k)

def simplexFibre (x : ℝ) : Set (ι → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1 ∧ S.a u = x}

theorem isCompact_simplexFibre (x : ℝ) : IsCompact (S.simplexFibre x) := by
  have hc : IsClosed (S.simplexFibre x) := by
    have hnonneg : IsClosed {u : ι → ℝ | ∀ i, 0 ≤ u i} := by
      simpa only [Set.ofPred_forall] using
        (isClosed_iInter fun i : ι =>
          isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply i))
    exact hnonneg.inter ((isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_eq S.continuous_a continuous_const))
  apply isCompact_Icc.of_isClosed_subset hc
  intro u hu
  refine ⟨hu.1, fun i => ?_⟩
  have h := Finset.single_le_sum (s := Finset.univ) (f := u)
    (fun j _ => hu.1 j) (Finset.mem_univ i)
  simpa only [hu.2.1, Pi.one_apply] using h

end SignData

/-- A global finite minimizer exists over all permutations and all weights at fixed a. -/
theorem exists_finite_minimizer {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hs : ∑ i, u i = 1) :
    ∃ σ : Equiv.Perm (Fin n), ∃ v : Fin n → ℝ,
      v ∈ (permutationSigns σ).simplexFibre ((permutationSigns π).a u) ∧
      (permutationSigns σ).b v ≤ (permutationSigns π).b u ∧
      ∀ (θ : Equiv.Perm (Fin n)) (w : Fin n → ℝ),
        w ∈ (permutationSigns θ).simplexFibre ((permutationSigns π).a u) →
          (permutationSigns σ).b v ≤ (permutationSigns θ).b w := by
  classical
  let x := (permutationSigns π).a u
  let P : Set (Equiv.Perm (Fin n)) := {σ | ((permutationSigns σ).simplexFibre x).Nonempty}
  have hπ : π ∈ P := ⟨u, hu, hs, rfl⟩
  have hm (σ : P) : ∃ v ∈ (permutationSigns σ.val).simplexFibre x,
      ∀ w ∈ (permutationSigns σ.val).simplexFibre x,
        (permutationSigns σ.val).b v ≤ (permutationSigns σ.val).b w := by
    obtain ⟨v, hv, hmin⟩ := ((permutationSigns σ.val).isCompact_simplexFibre x).exists_isMinOn
      σ.property (permutationSigns σ.val).continuous_b.continuousOn
    exact ⟨v, hv, fun w hw => hmin hw⟩
  choose V hV hmin using hm
  obtain ⟨σ, _, hbest⟩ := Finset.exists_min_image Finset.univ
    (fun θ : P => (permutationSigns θ.val).b (V θ)) ⟨⟨π, hπ⟩, Finset.mem_univ _⟩
  have hglobal (θ : Equiv.Perm (Fin n)) (w : Fin n → ℝ)
      (hw : w ∈ (permutationSigns θ).simplexFibre x) :
      (permutationSigns σ.val).b (V σ) ≤ (permutationSigns θ).b w := by
    let θ' : P := ⟨θ, ⟨w, hw⟩⟩
    exact (hbest θ' (Finset.mem_univ _)).trans (hmin θ' w hw)
  exact ⟨σ.val, V σ, hV σ, hglobal π u ⟨hu, hs, rfl⟩, hglobal⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
