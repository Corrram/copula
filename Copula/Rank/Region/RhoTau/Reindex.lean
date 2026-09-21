/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.PermutationSums

open scoped BigOperators

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

namespace SignData

variable {ι : Type*}

@[ext] theorem ext_edge (S T : SignData ι) (h : ∀ i j, S.edge i j = T.edge i j) : S = T := by
  cases S
  cases T
  have he := funext fun i => funext (h i)
  cases he
  rfl

def relabel (S : SignData ι) (e : Equiv.Perm ι) : SignData ι where
  edge i j := S.edge (e i) (e j)
  symmetric i j := S.symmetric (e i) (e j)
  diagonal i := S.diagonal (e i)
  values i j := S.values (e i) (e j)

variable [Fintype ι]

theorem a_relabel (S : SignData ι) (e : Equiv.Perm ι) (u : ι → ℝ) :
    (S.relabel e).a (u ∘ e) = S.a u := by
  simp only [a, bilinear, inversion, relabel, Function.comp_apply]
  have h (i : ι) := Equiv.sum_comp e (fun j => (1 + S.edge i j) / 2 * u i * u j)
  simp_rw [h]
  rw [Equiv.sum_comp e (fun i => ∑ j, (1 + S.edge i j) / 2 * u i * u j)]

theorem b_relabel (S : SignData ι) (e : Equiv.Perm ι) (u : ι → ℝ) :
    (S.relabel e).b (u ∘ e) = S.b u := by
  simp only [b, trilinear, triple, relabel, Function.comp_apply]
  have h (i j : ι) := Equiv.sum_comp e
    (fun k => (1 + S.edge i j * S.edge i k * S.edge j k) / 2 * u i * u j * u k)
  simp_rw [h]
  have h' (i : ι) := Equiv.sum_comp e
    (fun j => ∑ k, (1 + S.edge i j * S.edge i k * S.edge j k) / 2 * u i * u j * u k)
  simp_rw [h']
  rw [Equiv.sum_comp e (fun i => ∑ j, ∑ k,
    (1 + S.edge i j * S.edge i k * S.edge j k) / 2 * u i * u j * u k)]

end SignData

theorem inverse_signs {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (permutationSigns π.symm).relabel π = permutationSigns π := by
  apply SignData.ext_edge
  intro i j
  simp only [SignData.relabel, permutationSigns, IsInversion, Equiv.symm_apply_apply]
  have h : (π i < π j ∧ j < i ∨ π j < π i ∧ i < j) ↔
      (i < j ∧ π j < π i ∨ j < i ∧ π i < π j) := by tauto
  exact if_congr h (by rfl) (by rfl)

theorem inverse_coefficients {n : ℕ} (π : Equiv.Perm (Fin n)) (u : Fin n → ℝ) :
    (permutationSigns π.symm).a (u ∘ π.symm) = (permutationSigns π).a u ∧
      (permutationSigns π.symm).b (u ∘ π.symm) = (permutationSigns π).b u := by
  have hfun : (u ∘ π.symm) ∘ π = u := by funext i; simp
  have ha := (permutationSigns π.symm).a_relabel π (u ∘ π.symm)
  have hb := (permutationSigns π.symm).b_relabel π (u ∘ π.symm)
  rw [inverse_signs, hfun] at ha hb
  exact ⟨ha.symm, hb.symm⟩

end ProbabilityTheory.Copula.RankRegion.RhoTau
