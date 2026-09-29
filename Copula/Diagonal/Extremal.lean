/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Diagonal.Bertino

/-!
# Extremal copulas with a prescribed diagonal section

Let `δ` be a diagonal function (`IsDiagonalFunction`) and write `δ̂ t = t - δ t` (`diagGap`).
This file collects the order-theoretic facts about the set of copulas with diagonal section `δ`
(Nelsen, *An Introduction to Copulas*, 2nd ed., §3.2.6; Fredricks and Nelsen, *Copulas
constructed from diagonal sections*, 1997; Fredricks and Nelsen, *The Bertino family of copulas*,
2002). Upper bounds for arbitrary (non-exchangeable) copulas and quasi-copulas with diagonal `δ`
are in `Copula.Diagonal.UpperBound`.

* `cdf_add_cdf_swap_le`: `C(u,v) + C(v,u) ≤ δ(u) + δ(v)` for every copula.
* `isExchangeable_diagonalCopula`, `cdf_le_diagonalCopula`: the Fredricks–Nelsen copula
  `K_δ(u,v) = min(u, v, (δ u + δ v)/2)` is exchangeable and is the pointwise largest
  exchangeable copula with diagonal `δ`.
* `bertinoCopula_lt_diagonalCopula`, `bertinoCopula_eq_diagonalCopula_iff`: if `δ ≠ id`, the
  Bertino copula and the Fredricks–Nelsen copula differ; hence
  `diagonal_determines_copula_iff`: **a diagonal determines its copula uniquely if and only if it
  is the identity**, i.e. the copula is `M`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {δ : I → ℝ}

/-! ### The Fredricks–Nelsen copula is the largest exchangeable one -/

/-- The increment over the diagonal square `[u ∧ v, u ∨ v]²`: for every bivariate copula,
`C(u,v) + C(v,u) ≤ δ_C(u) + δ_C(v)`. -/
theorem cdf_add_cdf_swap_le (C : Copula 2) (u v : I) :
    C.cdf ![u, v] + C.cdf ![v, u] ≤ C.diagonal u + C.diagonal v := by
  have key : ∀ s t : I, s ≤ t → C.cdf ![s, t] + C.cdf ![t, s] ≤ C.diagonal s + C.diagonal t := by
    intro s t hst
    have hle : (![s, s] : Fin 2 → I) ≤ ![t, t] := by
      intro i; fin_cases i <;> exact hst
    have h := C.rectangleIncrement_cdf_nonneg ![s, s] ![t, t] hle
    rw [rectangleIncrement_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    unfold diagonal
    linarith
  rcases le_total u v with huv | hvu
  · exact key u v huv
  · have := key v u hvu
    linarith

/-- The Fredricks–Nelsen kernel is symmetric. -/
theorem diagKernel_comm (u v : I) : diagKernel δ u v = diagKernel δ v u := by
  unfold diagKernel; rw [min_comm (u : ℝ), add_comm (δ u)]

@[simp] theorem cdf_diagonalCopula_two (hδ : IsDiagonalFunction δ) (u v : I) :
    (diagonalCopula δ hδ).cdf ![u, v] = diagKernel δ u v :=
  cdf_diagonalCopula δ hδ _

/-- The Fredricks–Nelsen copula `K_δ` is exchangeable. -/
theorem isExchangeable_diagonalCopula (hδ : IsDiagonalFunction δ) :
    (diagonalCopula δ hδ).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp [diagKernel_comm u v]

/-- **`K_δ` is the largest exchangeable copula with diagonal `δ`** (Fredricks–Nelsen 1997):
every exchangeable copula with diagonal section `δ` lies below
`K_δ(u,v) = min(u, v, (δ u + δ v)/2)`. -/
theorem cdf_le_diagonalCopula (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hC : C.IsExchangeable) (hd : ∀ t, C.diagonal t = δ t) (u v : I) :
    C.cdf ![u, v] ≤ (diagonalCopula δ hδ).cdf ![u, v] := by
  rw [cdf_diagonalCopula_two]
  have hs := C.cdf_add_cdf_swap_le u v
  rw [(C.isExchangeable_iff.mp hC) v u, hd, hd] at hs
  unfold diagKernel
  refine le_min (le_min (C.cdf_le_coord _ 0) (C.cdf_le_coord _ 1)) ?_
  linarith

/-- `K_δ` dominates every exchangeable copula with diagonal `δ` in the lower orthant order. -/
theorem lowerOrthantLE_diagonalCopula (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hC : C.IsExchangeable) (hd : ∀ t, C.diagonal t = δ t) :
    C.LowerOrthantLE (diagonalCopula δ hδ) := by
  intro u
  have hu : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
  rw [hu]
  exact cdf_le_diagonalCopula hδ hC hd _ _

/-- Every exchangeable copula with diagonal `δ` lies between the Bertino copula `B_δ` and the
Fredricks–Nelsen copula `K_δ`; both bounds are exchangeable copulas with diagonal `δ`. -/
theorem bertino_le_cdf_le_diagonalCopula (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hC : C.IsExchangeable) (hd : ∀ t, C.diagonal t = δ t) (u v : I) :
    (bertinoCopula δ hδ).cdf ![u, v] ≤ C.cdf ![u, v] ∧
      C.cdf ![u, v] ≤ (diagonalCopula δ hδ).cdf ![u, v] :=
  ⟨bertinoCopula_cdf_le hδ hd u v, cdf_le_diagonalCopula hδ hC hd u v⟩

/-! ### Uniqueness: only the identity diagonal determines its copula -/

/-- If `δ` is not the identity, the Bertino copula lies strictly below the Fredricks–Nelsen copula
at some point. -/
theorem bertinoCopula_lt_diagonalCopula (hδ : IsDiagonalFunction δ) (hne : ∃ t, δ t ≠ t) :
    ∃ u v : I, (bertinoCopula δ hδ).cdf ![u, v] < (diagonalCopula δ hδ).cdf ![u, v] := by
  obtain ⟨ts, -, hts⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    hδ.continuous_diagGap.continuousOn
  have hmax : ∀ x, diagGap δ x ≤ diagGap δ ts := fun x => hts (mem_univ x)
  set c := diagGap δ ts with hc
  have hcpos : 0 < c := by
    obtain ⟨t0, ht0⟩ := hne
    have h1 : 0 < diagGap δ t0 := by
      unfold diagGap
      exact sub_pos.mpr (lt_of_le_of_ne (hδ.le_self t0) ht0)
    exact h1.trans_le (hmax t0)
  have hc1 : c ≤ ts := hδ.diagGap_le ts
  have hc2 : c ≤ 1 - ts := hδ.diagGap_le_one_sub ts
  let u : I := ⟨(ts : ℝ) - c / 2, by linarith, by linarith [ts.property.2]⟩
  let v : I := ⟨(ts : ℝ) + c / 2, by linarith [ts.property.1], by linarith⟩
  have hu : (u : ℝ) = ts - c / 2 := rfl
  have hv : (v : ℝ) = ts + c / 2 := rfl
  have huv : u ≤ v := by
    change (u : ℝ) ≤ v
    rw [hu, hv]; linarith
  have hu_ts : u ≤ ts := by
    change (u : ℝ) ≤ ts
    rw [hu]; linarith
  have hts_v : ts ≤ v := by
    change (ts : ℝ) ≤ v
    rw [hv]; linarith
  refine ⟨u, v, ?_⟩
  rw [cdf_bertinoCopula_two, cdf_diagonalCopula_two, bertinoKernel_of_le huv]
  -- Two lower bounds on the minimum of the gap over `[u, v]`.
  have hm1 : c / 2 ≤ bertinoGap δ u v := by
    apply le_bertinoGap
    intro w hw
    rw [uIcc_of_le huv] at hw
    rcases le_total w ts with hwt | htw
    · have := hδ.diagGap_sub_le hwt
      have hw1 : (u : ℝ) ≤ w := hw.1
      linarith
    · have := hδ.diagGap_sub_ge htw
      have hw2 : (w : ℝ) ≤ v := hw.2
      linarith
  have hm2 : (diagGap δ u + diagGap δ v) / 2 - c / 4 ≤ bertinoGap δ u v := by
    apply le_bertinoGap
    intro w hw
    rw [uIcc_of_le huv] at hw
    have hgu := hmax u
    have hgv := hmax v
    rcases le_total w ts with hwt | htw
    · have h1 := hδ.diagGap_sub_le hwt
      have h2 := hδ.diagGap_sub_ge hw.1
      have hw1 : (u : ℝ) ≤ w := hw.1
      linarith
    · have h1 := hδ.diagGap_sub_ge htw
      have h2 := hδ.diagGap_sub_le hw.2
      have hw2 : (w : ℝ) ≤ v := hw.2
      linarith
  unfold diagKernel
  rw [min_eq_left (show (u : ℝ) ≤ v from huv)]
  apply lt_min
  · linarith
  · unfold diagGap at hm2
    linarith

/-- The Bertino copula and the Fredricks–Nelsen copula of `δ` coincide if and only if `δ` is the
identity (in which case both are `M`). -/
theorem bertinoCopula_eq_diagonalCopula_iff (hδ : IsDiagonalFunction δ) :
    bertinoCopula δ hδ = diagonalCopula δ hδ ↔ ∀ t, δ t = t := by
  constructor
  · intro h
    by_contra hne
    have hne' : ∃ t, δ t ≠ t := by
      by_contra h'
      exact hne fun t => by_contra fun ht => h' ⟨t, ht⟩
    obtain ⟨u, v, huv⟩ := bertinoCopula_lt_diagonalCopula hδ hne'
    rw [h] at huv
    exact lt_irrefl _ huv
  · intro h
    have hB : bertinoCopula δ hδ = comonotonic 2 := by
      rw [← diagonal_eq_id_iff]
      intro t
      rw [diagonal_bertinoCopula, h]
    have hK : diagonalCopula δ hδ = comonotonic 2 := by
      rw [← diagonal_eq_id_iff]
      intro t
      rw [diagonal_diagonalCopula, h]
    rw [hB, hK]

/-- **A diagonal section determines its copula if and only if it is the identity**: for a diagonal
function `δ`, all copulas with diagonal `δ` coincide exactly when `δ(t) = t` for all `t` (and then
the copula is `M`). In particular the diagonal of `W` does not determine `W`. -/
theorem diagonal_determines_copula_iff (hδ : IsDiagonalFunction δ) :
    (∀ C D : Copula 2, (∀ t, C.diagonal t = δ t) → (∀ t, D.diagonal t = δ t) → C = D) ↔
      ∀ t, δ t = t := by
  constructor
  · intro h
    exact (bertinoCopula_eq_diagonalCopula_iff hδ).mp
      (h _ _ (diagonal_bertinoCopula hδ) (diagonal_diagonalCopula δ hδ))
  · intro h C D hC hD
    have hC' : C = comonotonic 2 := (diagonal_eq_id_iff C).mp fun t => (hC t).trans (h t)
    have hD' : D = comonotonic 2 := (diagonal_eq_id_iff D).mp fun t => (hD t).trans (h t)
    rw [hC', hD']

end ProbabilityTheory.Copula
