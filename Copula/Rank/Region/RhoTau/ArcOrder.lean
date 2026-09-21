/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Rank.Region.RhoTau.Boundary
import Mathlib.Topology.Order.MonotoneContinuity

open scoped unitInterval

namespace ProbabilityTheory.Copula.RankRegion.RhoTau

structure JoinedIncreasingArcs (f : ℕ → I → ℝ) : Prop where
  strictMono : ∀ n, StrictMono (f n)
  join : ∀ n, f n 0 = f (n + 1) 1

namespace JoinedIncreasingArcs

variable {f : ℕ → I → ℝ} (h : JoinedIncreasingArcs f)

include h

theorem junction_strictAnti : StrictAnti (fun n => f n 1) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [← h.join n]
  exact h.strictMono n (by norm_num : (0 : I) < 1)

theorem ordered {n m : ℕ} (hnm : n < m) (s t : I) : f m t ≤ f n s := by
  calc
    f m t ≤ f m 1 := (h.strictMono m).monotone t.property.2
    _ ≤ f (n + 1) 1 := h.junction_strictAnti.antitone hnm
    _ = f n 0 := (h.join n).symm
    _ ≤ f n s := (h.strictMono n).monotone s.property.1

theorem eq_of_ordered {n m : ℕ} (hnm : n < m) {s t : I} (he : f n s = f m t) :
    s = 0 ∧ t = 1 ∧ m = n + 1 := by
  have hs : f n s = f n 0 := le_antisymm
    (he ▸ h.ordered hnm 0 t) ((h.strictMono n).monotone s.property.1)
  have ht : f m t = f m 1 := le_antisymm ((h.strictMono m).monotone t.property.2)
    (he ▸ h.ordered hnm s 1)
  have hs' := (h.strictMono n).injective hs
  have ht' := (h.strictMono m).injective ht
  refine ⟨hs', ht', h.junction_strictAnti.injective ?_⟩
  rw [← h.join, ← hs, ← ht, he]

end JoinedIncreasingArcs

theorem joined_arcs_order {f g : ℕ → I → ℝ} (hf : JoinedIncreasingArcs f)
    (hg : JoinedIncreasingArcs g) {n m : ℕ} {s t : I} (h : f n s ≤ f m t) :
    g n s ≤ g m t := by
  rcases lt_trichotomy n m with hnm | rfl | hmn
  · obtain ⟨rfl, rfl, rfl⟩ := hf.eq_of_ordered hnm (le_antisymm h (hf.ordered hnm s t))
    exact (hg.join n).le
  · exact (hg.strictMono n).monotone ((hf.strictMono n).le_iff_le.mp h)
  · exact hg.ordered hmn t s

theorem joined_arcTau : JoinedIncreasingArcs (fun n s => arcTau n s) where
  strictMono := strictMono_arcTau
  join n := by
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one]
    rw [(arc_zero n).1, (arc_one (n + 1)).1]
    push_cast
    ring

theorem joined_arcRho : JoinedIncreasingArcs (fun n s => arcRho n s) where
  strictMono := strictMono_arcRho
  join n := by
    simp only [Set.Icc.coe_zero, Set.Icc.coe_one]
    rw [(arc_zero n).2, (arc_one (n + 1)).2]
    push_cast
    ring

theorem arcTau_gt_neg_one (n : ℕ) (s : I) : -1 < arcTau n s := by
  have h : -1 < arcTau n (0 : I) := by
    simp only [Set.Icc.coe_zero]
    rw [(arc_zero n).1]
    have : 0 < 2 / ((n : ℝ) + 2) := by positivity
    linarith
  exact h.trans_le ((strictMono_arcTau n).monotone s.property.1)

theorem arcRho_gt_neg_one (n : ℕ) (s : I) : -1 < arcRho n s := by
  have h : -1 < arcRho n (0 : I) := by
    simp only [Set.Icc.coe_zero]
    rw [(arc_zero n).2]
    have : 0 < 2 / ((n : ℝ) + 2) ^ 2 := by positivity
    linarith
  exact h.trans_le ((strictMono_arcRho n).monotone s.property.1)

theorem LowerParameter.order_iff (a b : LowerParameter) : a.tau ≤ b.tau ↔ a.rho ≤ b.rho := by
  cases a with
  | endpoint => exact iff_of_true b.tau_mem.1 b.rho_mem.1
  | arc n s =>
    cases b with
    | endpoint =>
      exact iff_of_false (not_le_of_gt (arcTau_gt_neg_one n s))
        (not_le_of_gt (arcRho_gt_neg_one n s))
    | arc m t => exact ⟨joined_arcs_order joined_arcTau joined_arcRho,
        joined_arcs_order joined_arcRho joined_arcTau⟩

theorem LowerParameter.tau_eq_iff (a b : LowerParameter) : a.tau = b.tau ↔ a.rho = b.rho := by
  simp only [le_antisymm_iff, a.order_iff b, b.order_iff a]

end ProbabilityTheory.Copula.RankRegion.RhoTau
