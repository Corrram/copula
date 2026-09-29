/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Diagonal.Extremal
import Copula.QuasiCopula.Bivariate

/-!
# Upper bounds for copulas and quasi-copulas with a prescribed diagonal

Let `δ` be a diagonal function and `δ̂ t = t - δ t` its gap (`diagGap`). Every copula, and more
generally every bivariate quasi-copula `Q`, with diagonal section `δ` satisfies
`Q(u,v) ≤ δ(t) + (u - t)⁺ + (v - t)⁺` for all `t`, by monotonicity and the Lipschitz property.
Taking the infimum gives the bound

`A_δ(u,v) = min(u, v, max(u,v) - max_{t ∈ [u ∧ v, u ∨ v]} (t - δ t))`

of Nelsen, Quesada-Molina, Rodríguez-Lallena and Úbeda-Flores (*Best-possible bounds on sets of
bivariate distribution functions*, J. Multivariate Anal. 2004); see also Nelsen, *An Introduction
to Copulas*, 2nd ed., §3.2.6 and §6.2.

* `diagonalUpperBound δ`: defined as `min(u, v, inf_t (δ t + (u - t)⁺ + (v - t)⁺))`;
  `diagonalUpperBound_eq` proves the `max`-formula above.
* `quasiCopula_le_diagonalUpperBound`, `cdf_le_diagonalUpperBound`: `Q ≤ A_δ` and `C ≤ A_δ`.
* `isQuasiCopula_diagonalUpperBound`, `diagonalUpperBound_self`: `A_δ` is itself a quasi-copula
  with diagonal `δ`; hence (`diagonalUpperBound_isGreatest`) it is the **largest quasi-copula with
  diagonal `δ`**, the best-possible upper bound on the set of quasi-copulas with diagonal `δ`.
* `bertino_le_cdf_le_upper`: `B_δ ≤ C ≤ A_δ` for copulas with diagonal `δ`.
* For *copulas* the bound `A_δ` need not be best possible:
  `cdf_le_diagonal_add_diagonal_sub_bertino` gives the additional bound
  `C(u,v) ≤ δ(u) + δ(v) - B_δ(u,v)`, and `dipDiagonal` is an explicit diagonal
  (`δ(t) = t - min(t, 1 - t, 1/10 + |t - 1/2|)`) for which every copula `C` with that diagonal
  satisfies `C(3/10, 7/10) ≤ 1/5 < 3/10 = A_δ(3/10, 7/10)` (`dipDiagonal_gap`). The sup of the
  copulas with diagonal `δ` is therefore in general strictly smaller than `A_δ` (compare
  Úbeda-Flores, *On the best-possible upper bound on sets of copulas with given diagonal
  sections*, Soft Computing 2008).
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {δ : I → ℝ}

/-! ### Bivariate quasi-copulas: monotonicity and Lipschitz bounds in one variable -/

namespace IsQuasiCopula

variable {Q : (Fin 2 → I) → ℝ}

theorem mono_two (hQ : IsQuasiCopula Q) {u u' v v' : I} (hu : u ≤ u') (hv : v ≤ v') :
    Q ![u, v] ≤ Q ![u', v'] := by
  apply hQ.monotone
  intro i
  fin_cases i
  · exact hu
  · exact hv

theorem sub_le_left (hQ : IsQuasiCopula Q) {s t : I} (hst : s ≤ t) (v : I) :
    Q ![t, v] - Q ![s, v] ≤ (t : ℝ) - s := by
  have h := hQ.lipschitz ![t, v] ![s, v]
  have hst' : (s : ℝ) ≤ t := hst
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, abs_zero, add_zero, abs_of_nonneg (sub_nonneg.mpr hst')] at h
  exact (le_abs_self _).trans h

theorem sub_le_right (hQ : IsQuasiCopula Q) {s t : I} (hst : s ≤ t) (u : I) :
    Q ![u, t] - Q ![u, s] ≤ (t : ℝ) - s := by
  have h := hQ.lipschitz ![u, t] ![u, s]
  have hst' : (s : ℝ) ≤ t := hst
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, abs_zero, zero_add, abs_of_nonneg (sub_nonneg.mpr hst')] at h
  exact (le_abs_self _).trans h

end IsQuasiCopula

/-! ### The upper bound `A_δ` of Nelsen, Quesada-Molina, Rodríguez-Lallena and Úbeda-Flores -/

/-- The function `δ t + (u - t)⁺ + (v - t)⁺`, an upper bound for `C(u,v)` obtained from the
diagonal value at `t` and the Lipschitz property. -/
def diagUpperAux (δ : I → ℝ) (t u v : I) : ℝ :=
  δ t + max ((u : ℝ) - t) 0 + max ((v : ℝ) - t) 0

/-- The infimum over `t` of `δ t + (u - t)⁺ + (v - t)⁺`. -/
noncomputable def diagUpperInf (δ : I → ℝ) (u v : I) : ℝ := ⨅ t : I, diagUpperAux δ t u v

/-- The upper bound `A_δ(u,v) = min(u, v, inf_t (δ t + (u - t)⁺ + (v - t)⁺))` for copulas with
diagonal `δ`; see `diagonalUpperBound_eq` for the form
`min(u, v, max(u,v) - max_{t ∈ [u ∧ v, u ∨ v]} (t - δ t))`. -/
noncomputable def diagonalUpperBound (δ : I → ℝ) (u v : I) : ℝ :=
  min (min (u : ℝ) v) (diagUpperInf δ u v)

theorem diagUpperAux_comm (t u v : I) : diagUpperAux δ t u v = diagUpperAux δ t v u := by
  unfold diagUpperAux; ring

theorem diagUpperInf_comm (u v : I) : diagUpperInf δ u v = diagUpperInf δ v u := by
  unfold diagUpperInf; simp_rw [diagUpperAux_comm _ u v]

theorem diagonalUpperBound_comm (u v : I) :
    diagonalUpperBound δ u v = diagonalUpperBound δ v u := by
  unfold diagonalUpperBound; rw [min_comm (u : ℝ), diagUpperInf_comm]

namespace IsDiagonalFunction

theorem diagUpperAux_nonneg (hδ : IsDiagonalFunction δ) (t u v : I) :
    0 ≤ diagUpperAux δ t u v := by
  unfold diagUpperAux
  have := hδ.nonneg t
  have := le_max_right ((u : ℝ) - t) 0
  have := le_max_right ((v : ℝ) - t) 0
  linarith

theorem bddBelow_diagUpperAux (hδ : IsDiagonalFunction δ) (u v : I) :
    BddBelow (range fun t => diagUpperAux δ t u v) :=
  ⟨0, by rintro _ ⟨t, rfl⟩; exact hδ.diagUpperAux_nonneg t u v⟩

theorem diagUpperInf_le (hδ : IsDiagonalFunction δ) (t u v : I) :
    diagUpperInf δ u v ≤ diagUpperAux δ t u v :=
  ciInf_le (hδ.bddBelow_diagUpperAux u v) t

theorem diagUpperInf_nonneg (hδ : IsDiagonalFunction δ) (u v : I) : 0 ≤ diagUpperInf δ u v :=
  le_ciInf fun t => hδ.diagUpperAux_nonneg t u v

theorem le_diagUpperInf_one (hδ : IsDiagonalFunction δ) (v : I) :
    (v : ℝ) ≤ diagUpperInf δ 1 v := by
  apply le_ciInf
  intro t
  unfold diagUpperAux
  have h1 := hδ.two_mul_sub_one_le t
  have h2 := le_max_left (((1 : I) : ℝ) - t) 0
  have h3 := le_max_left ((v : ℝ) - t) 0
  simp only [Set.Icc.coe_one] at h2 ⊢
  linarith

private theorem diagUpperInf_mono_left (hδ : IsDiagonalFunction δ) {u u' : I} (h : u ≤ u')
    (v : I) : diagUpperInf δ u v ≤ diagUpperInf δ u' v := by
  apply ciInf_mono (hδ.bddBelow_diagUpperAux u v)
  intro t
  unfold diagUpperAux
  have : max ((u : ℝ) - t) 0 ≤ max ((u' : ℝ) - t) 0 :=
    max_le_max (by linarith [show (u : ℝ) ≤ u' from h]) le_rfl
  linarith

private theorem diagUpperInf_lip_left (hδ : IsDiagonalFunction δ) {u u' : I} (h : u ≤ u')
    (v : I) : diagUpperInf δ u' v - diagUpperInf δ u v ≤ (u' : ℝ) - u := by
  have : diagUpperInf δ u' v - ((u' : ℝ) - u) ≤ diagUpperInf δ u v := by
    apply le_ciInf
    intro t
    have h1 := hδ.diagUpperInf_le t u' v
    have h2 : max ((u' : ℝ) - t) 0 ≤ max ((u : ℝ) - t) 0 + ((u' : ℝ) - u) := by
      have hu : (u : ℝ) ≤ u' := h
      rcases le_total ((u' : ℝ) - t) 0 with h3 | h3
      · rw [max_eq_right h3]
        linarith [le_max_right ((u : ℝ) - t) 0]
      · rw [max_eq_left h3]
        linarith [le_max_left ((u : ℝ) - t) 0]
    unfold diagUpperAux at h1 ⊢
    linarith
  linarith

/-- Every bivariate quasi-copula satisfies `Q(u,v) ≤ Q(t,t) + (u - t)⁺ + (v - t)⁺` for all `t`. -/
theorem _root_.ProbabilityTheory.Copula.IsQuasiCopula.le_diagUpperAux
    {Q : (Fin 2 → I) → ℝ} (hQ : IsQuasiCopula Q) (t u v : I) :
    Q ![u, v] ≤ diagUpperAux (fun s => Q ![s, s]) t u v := by
  unfold diagUpperAux
  rcases le_total u t with hut | htu
  · have hu : max ((u : ℝ) - t) 0 = 0 := max_eq_right (by linarith [show (u : ℝ) ≤ t from hut])
    rcases le_total v t with hvt | htv
    · have hv : max ((v : ℝ) - t) 0 = 0 :=
        max_eq_right (by linarith [show (v : ℝ) ≤ t from hvt])
      rw [hu, hv]
      linarith [hQ.mono_two hut hvt]
    · have hv : max ((v : ℝ) - t) 0 = v - t :=
        max_eq_left (by linarith [show (t : ℝ) ≤ v from htv])
      rw [hu, hv]
      linarith [hQ.mono_two hut (le_refl v), hQ.sub_le_right htv t]
  · have hu : max ((u : ℝ) - t) 0 = u - t := max_eq_left (by linarith [show (t : ℝ) ≤ u from htu])
    rcases le_total v t with hvt | htv
    · have hv : max ((v : ℝ) - t) 0 = 0 :=
        max_eq_right (by linarith [show (v : ℝ) ≤ t from hvt])
      rw [hu, hv]
      linarith [hQ.mono_two (le_refl u) hvt, hQ.sub_le_left htu t]
    · have hv : max ((v : ℝ) - t) 0 = v - t :=
        max_eq_left (by linarith [show (t : ℝ) ≤ v from htv])
      rw [hu, hv]
      linarith [hQ.sub_le_left htu v, hQ.sub_le_right htv t]

/-- The `max`-formula of Nelsen, Quesada-Molina, Rodríguez-Lallena and Úbeda-Flores (2004):
`inf_t (δ t + (u - t)⁺ + (v - t)⁺) = max(u,v) - max_{t ∈ [u ∧ v, u ∨ v]} (t - δ t)`. -/
theorem diagUpperInf_eq (hδ : IsDiagonalFunction δ) (u v : I) :
    diagUpperInf δ u v = max (u : ℝ) v - sSup (diagGap δ '' uIcc u v) := by
  have hbdd : ∀ s : Set I, BddAbove (diagGap δ '' s) := fun s =>
    ⟨1, by rintro _ ⟨t, -, rfl⟩; linarith [hδ.diagGap_le t, t.property.2]⟩
  have main : ∀ u v : I, u ≤ v →
      diagUpperInf δ u v = (v : ℝ) - sSup (diagGap δ '' uIcc u v) := by
    intro u v huv
    have huv' : (u : ℝ) ≤ v := huv
    have hin : ∀ t ∈ uIcc u v, diagUpperAux δ t u v = (v : ℝ) - diagGap δ t := by
      intro t ht
      rw [uIcc_of_le huv] at ht
      have ht1 : (u : ℝ) ≤ t := ht.1
      have ht2 : (t : ℝ) ≤ v := ht.2
      unfold diagUpperAux diagGap
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    apply le_antisymm
    · have : sSup (diagGap δ '' uIcc u v) ≤ (v : ℝ) - diagUpperInf δ u v := by
        apply csSup_le (nonempty_uIcc.image _)
        rintro _ ⟨t, ht, rfl⟩
        have := hδ.diagUpperInf_le t u v
        rw [hin t ht] at this
        linarith
      linarith
    · apply le_ciInf
      intro t
      have hS : ∀ s ∈ uIcc u v, diagGap δ s ≤ sSup (diagGap δ '' uIcc u v) :=
        fun s hs => le_csSup (hbdd _) ⟨s, hs, rfl⟩
      rcases lt_or_ge t u with htu | hut
      · -- `t < u`: compare with `t = u`.
        have h1 := hS u left_mem_uIcc
        have h2 := hδ.lipschitz t u htu.le
        have htu' : (t : ℝ) < u := htu
        unfold diagUpperAux
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        have e : diagGap δ u = (u : ℝ) - δ u := rfl
        linarith
      rcases le_or_gt t v with htv | hvt
      · rw [hin t (by rw [uIcc_of_le huv]; exact ⟨hut, htv⟩)]
        linarith [hS t (by rw [uIcc_of_le huv]; exact ⟨hut, htv⟩)]
      · -- `v < t`: compare with `t = v`.
        have h1 := hS v right_mem_uIcc
        have h2 := hδ.monotone hvt.le
        have hvt' : (v : ℝ) < t := hvt
        unfold diagUpperAux
        rw [max_eq_right (by linarith), max_eq_right (by linarith)]
        have e : diagGap δ v = (v : ℝ) - δ v := rfl
        linarith
  rcases le_total u v with huv | hvu
  · rw [main u v huv, max_eq_right (show (u : ℝ) ≤ v from huv)]
  · rw [diagUpperInf_comm, main v u hvu, max_eq_left (show (v : ℝ) ≤ u from hvu), uIcc_comm]

end IsDiagonalFunction

/-- The upper bound in the form of Nelsen, Quesada-Molina, Rodríguez-Lallena and Úbeda-Flores
(2004): `A_δ(u,v) = min(u, v, max(u,v) - max_{t ∈ [u ∧ v, u ∨ v]} (t - δ t))`. -/
theorem diagonalUpperBound_eq (hδ : IsDiagonalFunction δ) (u v : I) :
    diagonalUpperBound δ u v =
      min (min (u : ℝ) v) (max (u : ℝ) v - sSup (diagGap δ '' uIcc u v)) := by
  rw [diagonalUpperBound, hδ.diagUpperInf_eq]

/-- **Upper bound for quasi-copulas with a prescribed diagonal** (Nelsen, Quesada-Molina,
Rodríguez-Lallena and Úbeda-Flores 2004): every bivariate quasi-copula with diagonal `δ` satisfies
`Q ≤ A_δ`. -/
theorem quasiCopula_le_diagonalUpperBound {Q : (Fin 2 → I) → ℝ} (hQ : IsQuasiCopula Q)
    (hd : ∀ t, Q ![t, t] = δ t) (u v : I) : Q ![u, v] ≤ diagonalUpperBound δ u v := by
  have hδ' : (fun s => Q ![s, s]) = δ := funext hd
  subst hδ'
  refine le_min (le_min (hQ.le_coord _ 0) (hQ.le_coord _ 1)) (le_ciInf fun t => ?_)
  exact hQ.le_diagUpperAux t u v

/-- **Upper bound for copulas with a prescribed diagonal**: every copula with diagonal `δ`
satisfies `C ≤ A_δ`. -/
theorem cdf_le_diagonalUpperBound {C : Copula 2} (hd : ∀ t, C.diagonal t = δ t) (u v : I) :
    C.cdf ![u, v] ≤ diagonalUpperBound δ u v :=
  quasiCopula_le_diagonalUpperBound (isQuasiCopula_cdf C) hd u v

/-- **Bounds for copulas with a prescribed diagonal**: `B_δ ≤ C ≤ A_δ` for every copula `C` with
diagonal section `δ`. The lower bound is itself a copula with diagonal `δ`. -/
theorem bertino_le_cdf_le_upper (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hd : ∀ t, C.diagonal t = δ t) (u v : I) :
    (bertinoCopula δ hδ).cdf ![u, v] ≤ C.cdf ![u, v] ∧ C.cdf ![u, v] ≤ diagonalUpperBound δ u v :=
  ⟨bertinoCopula_cdf_le hδ hd u v, cdf_le_diagonalUpperBound hd u v⟩

/-- The upper bound `A_δ` has diagonal `δ`. -/
theorem diagonalUpperBound_self (hδ : IsDiagonalFunction δ) (t : I) :
    diagonalUpperBound δ t t = δ t := by
  apply le_antisymm
  · refine (min_le_right _ _).trans ((hδ.diagUpperInf_le t t t).trans_eq ?_)
    simp [diagUpperAux]
  · have h := cdf_le_diagonalUpperBound (C := diagonalCopula δ hδ)
      (diagonal_diagonalCopula δ hδ) t t
    have h' := diagonal_diagonalCopula δ hδ t
    unfold diagonal at h'
    linarith

/-- `A_δ` is a (bivariate) quasi-copula. -/
theorem isQuasiCopula_diagonalUpperBound (hδ : IsDiagonalFunction δ) :
    IsQuasiCopula (fun u : Fin 2 → I => diagonalUpperBound δ (u 0) (u 1)) := by
  have hmin : ∀ a b a' b' d : ℝ, a' ≤ a + d → b' ≤ b + d → min a' b' ≤ min a b + d := by
    intro a b a' b' d ha hb
    rw [← min_add_add_right]
    exact min_le_min ha hb
  have hm : ∀ u u' v : I, u ≤ u' → diagonalUpperBound δ u v ≤ diagonalUpperBound δ u' v := by
    intro u u' v h
    unfold diagonalUpperBound
    exact min_le_min (min_le_min h le_rfl) (hδ.diagUpperInf_mono_left h v)
  have hl : ∀ u u' v : I, u ≤ u' →
      diagonalUpperBound δ u' v - diagonalUpperBound δ u v ≤ (u' : ℝ) - u := by
    intro u u' v h
    unfold diagonalUpperBound
    have h1 := hδ.diagUpperInf_lip_left h v
    have h2 : min (u' : ℝ) v ≤ min (u : ℝ) v + ((u' : ℝ) - u) :=
      hmin _ _ _ _ _ (by linarith) (by linarith [show (u : ℝ) ≤ u' from h])
    have := hmin _ _ _ _ ((u' : ℝ) - u) h2 (show diagUpperInf δ u' v ≤ diagUpperInf δ u v + ((u' : ℝ) - u) by linarith)
    linarith
  apply IsQuasiCopula.ofBivariate (diagonalUpperBound δ)
  · intro v
    unfold diagonalUpperBound
    rw [Set.Icc.coe_zero, min_eq_left v.property.1, min_eq_left (hδ.diagUpperInf_nonneg 0 v)]
  · intro u
    unfold diagonalUpperBound
    rw [Set.Icc.coe_zero, min_eq_right u.property.1, min_eq_left (hδ.diagUpperInf_nonneg u 0)]
  · intro v
    unfold diagonalUpperBound
    rw [Set.Icc.coe_one, min_eq_right v.property.2, min_eq_left (hδ.le_diagUpperInf_one v)]
  · intro u
    rw [diagonalUpperBound_comm]
    unfold diagonalUpperBound
    rw [Set.Icc.coe_one, min_eq_right u.property.2, min_eq_left (hδ.le_diagUpperInf_one u)]
  · exact hm
  · intro u v v' h
    rw [diagonalUpperBound_comm u v, diagonalUpperBound_comm u v']
    exact hm v v' u h
  · exact hl
  · intro u v v' h
    rw [diagonalUpperBound_comm u v, diagonalUpperBound_comm u v']
    exact hl v v' u h

/-- **`A_δ` is the largest quasi-copula with diagonal `δ`**: it is a quasi-copula, its diagonal is
`δ`, and it dominates every quasi-copula with diagonal `δ`. -/
theorem diagonalUpperBound_isGreatest (hδ : IsDiagonalFunction δ) :
    IsQuasiCopula (fun u : Fin 2 → I => diagonalUpperBound δ (u 0) (u 1)) ∧
      (∀ t, diagonalUpperBound δ t t = δ t) ∧
      ∀ Q : (Fin 2 → I) → ℝ, IsQuasiCopula Q → (∀ t, Q ![t, t] = δ t) →
        ∀ u v : I, Q ![u, v] ≤ diagonalUpperBound δ u v :=
  ⟨isQuasiCopula_diagonalUpperBound hδ, diagonalUpperBound_self hδ,
    fun _ hQ hd => quasiCopula_le_diagonalUpperBound hQ hd⟩

/-! ### A sharper bound for copulas, and a diagonal for which `A_δ` is not attained -/

/-- For copulas the exchange inequality and the Bertino lower bound give
`C(u,v) ≤ δ(u) + δ(v) - B_δ(u,v)`. -/
theorem cdf_le_diagonal_add_diagonal_sub_bertino (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hd : ∀ t, C.diagonal t = δ t) (u v : I) :
    C.cdf ![u, v] ≤ δ u + δ v - bertinoKernel δ u v := by
  have h1 := C.cdf_add_cdf_swap_le u v
  have h2 := bertinoCopula_cdf_le hδ hd v u
  rw [cdf_bertinoCopula_two, bertinoKernel_comm] at h2
  rw [hd, hd] at h1
  linarith

private theorem min3_le_add (a b c a' b' c' d : ℝ) (ha : a' ≤ a + d) (hb : b' ≤ b + d)
    (hc : c' ≤ c + d) : min (min a' b') c' ≤ min (min a b) c + d := by
  rw [← min_add_add_right, ← min_add_add_right]
  exact min_le_min (min_le_min ha hb) hc

/-- The gap `min(t, 1 - t, 1/10 + |t - 1/2|)` of `dipDiagonal`: two tents joined by a dip. -/
noncomputable def dipGap (t : I) : ℝ := min (min (t : ℝ) (1 - t)) (1 / 10 + |(t : ℝ) - 1 / 2|)

/-- The diagonal `δ(t) = t - min(t, 1 - t, 1/10 + |t - 1/2|)`, i.e. `δ = 0` on `[0, 3/10]`,
`δ(t) = 2t - 3/5` on `[3/10, 1/2]`, `δ = 2/5` on `[1/2, 7/10]` and `δ(t) = 2t - 1` on
`[7/10, 1]`. -/
noncomputable def dipDiagonal (t : I) : ℝ := (t : ℝ) - dipGap t

private theorem dipGap_le_add {s t : I} (d : ℝ) (h1 : (t : ℝ) ≤ s + d) (h2 : (s : ℝ) ≤ t + d)
    (hd : |(t : ℝ) - s| ≤ d) : dipGap t ≤ dipGap s + d := by
  unfold dipGap
  apply min3_le_add
  · exact h1
  · linarith
  · have := abs_sub_abs_le_abs_sub ((t : ℝ) - 1 / 2) ((s : ℝ) - 1 / 2)
    rw [show ((t : ℝ) - 1 / 2) - ((s : ℝ) - 1 / 2) = t - s by ring] at this
    linarith

theorem isDiagonalFunction_dipDiagonal : IsDiagonalFunction dipDiagonal where
  one := by
    unfold dipDiagonal dipGap
    norm_num
  nonneg t := by
    unfold dipDiagonal dipGap
    have := min_le_left (min (t : ℝ) (1 - t)) (1 / 10 + |(t : ℝ) - 1 / 2|)
    have := min_le_left (t : ℝ) (1 - t)
    linarith
  le_self t := by
    unfold dipDiagonal dipGap
    have h : 0 ≤ min (min (t : ℝ) (1 - t)) (1 / 10 + |(t : ℝ) - 1 / 2|) :=
      le_min (le_min t.property.1 (by linarith [t.property.2]))
        (by positivity)
    linarith
  monotone s t hst := by
    have hst' : (s : ℝ) ≤ t := hst
    have := dipGap_le_add (s := s) (t := t) ((t : ℝ) - s) (by linarith) (by linarith)
      (by rw [abs_of_nonneg (by linarith)])
    unfold dipDiagonal
    linarith
  lipschitz s t hst := by
    have hst' : (s : ℝ) ≤ t := hst
    have := dipGap_le_add (s := t) (t := s) ((t : ℝ) - s) (by linarith) (by linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
    unfold dipDiagonal
    linarith

/-- The point `3/10`. -/
noncomputable def threeTenths : I := ⟨3 / 10, by norm_num, by norm_num⟩

/-- The point `7/10`. -/
noncomputable def sevenTenths : I := ⟨7 / 10, by norm_num, by norm_num⟩

private theorem dipGap_half : dipGap unitHalf = 1 / 10 := by
  simp only [dipGap, unitHalf, sub_self, abs_zero]
  norm_num

private theorem dipDiagonal_threeTenths : dipDiagonal threeTenths = 0 := by
  have h : |(3 / 10 : ℝ) - 1 / 2| = 1 / 5 := by
    rw [abs_of_neg (by norm_num)]; norm_num
  simp only [dipDiagonal, dipGap, threeTenths, h]
  norm_num

private theorem dipDiagonal_sevenTenths : dipDiagonal sevenTenths = 2 / 5 := by
  have h : |(7 / 10 : ℝ) - 1 / 2| = 1 / 5 := by
    rw [abs_of_pos (by norm_num)]; norm_num
  simp only [dipDiagonal, dipGap, sevenTenths, h]
  norm_num

/-- `A_δ(3/10, 7/10) = 3/10` for `δ = dipDiagonal`. -/
theorem diagonalUpperBound_dipDiagonal :
    diagonalUpperBound dipDiagonal threeTenths sevenTenths = 3 / 10 := by
  have hu : ((threeTenths : I) : ℝ) = 3 / 10 := rfl
  have hv : ((sevenTenths : I) : ℝ) = 7 / 10 := rfl
  unfold diagonalUpperBound
  rw [hu, hv, min_eq_left (by norm_num : (3 / 10 : ℝ) ≤ 7 / 10)]
  apply min_eq_left
  apply le_ciInf
  intro t
  unfold diagUpperAux dipDiagonal dipGap
  rw [hu, hv]
  set G := min (min (t : ℝ) (1 - t)) (1 / 10 + |(t : ℝ) - 1 / 2|) with hG
  have g1 : G ≤ min (t : ℝ) (1 - t) := min_le_left _ _
  have g2 : G ≤ 1 / 10 + |(t : ℝ) - 1 / 2| := min_le_right _ _
  have g3 := min_le_left (t : ℝ) (1 - t)
  have m1 := le_max_left ((3 / 10 : ℝ) - t) 0
  have m2 := le_max_right ((3 / 10 : ℝ) - t) 0
  have m3 := le_max_left ((7 / 10 : ℝ) - t) 0
  have m4 := le_max_right ((7 / 10 : ℝ) - t) 0
  rcases le_total (t : ℝ) (1 / 2) with ht | ht
  · have ha : |(t : ℝ) - 1 / 2| = 1 / 2 - t := by rw [abs_of_nonpos (by linarith)]; ring
    linarith
  · have ha : |(t : ℝ) - 1 / 2| = t - 1 / 2 := abs_of_nonneg (by linarith)
    linarith

/-- **`A_δ` is not best possible for copulas.** For `δ = dipDiagonal`, every copula with diagonal
`δ` satisfies `C(3/10, 7/10) ≤ 1/5`, whereas `A_δ(3/10, 7/10) = 3/10`. -/
theorem dipDiagonal_gap {C : Copula 2} (hd : ∀ t, C.diagonal t = dipDiagonal t) :
    C.cdf ![threeTenths, sevenTenths] ≤ 1 / 5 ∧
      C.cdf ![threeTenths, sevenTenths] + 1 / 10 ≤
        diagonalUpperBound dipDiagonal threeTenths sevenTenths := by
  have h := cdf_le_diagonal_add_diagonal_sub_bertino isDiagonalFunction_dipDiagonal hd
    threeTenths sevenTenths
  have hmem : unitHalf ∈ uIcc threeTenths sevenTenths := by
    rw [uIcc_of_le (show threeTenths ≤ sevenTenths from
      show ((threeTenths : I) : ℝ) ≤ sevenTenths by norm_num [threeTenths, sevenTenths])]
    constructor
    · show ((threeTenths : I) : ℝ) ≤ unitHalf
      norm_num [threeTenths, unitHalf]
    · show ((unitHalf : I) : ℝ) ≤ sevenTenths
      norm_num [sevenTenths, unitHalf]
  have hgap := isDiagonalFunction_dipDiagonal.bertinoGap_le hmem
  have hg : diagGap dipDiagonal unitHalf = 1 / 10 := by
    simp only [diagGap, dipDiagonal, dipGap_half]; ring
  rw [hg] at hgap
  have hk : bertinoKernel dipDiagonal threeTenths sevenTenths =
      3 / 10 - bertinoGap dipDiagonal threeTenths sevenTenths := by
    unfold bertinoKernel
    rw [show ((threeTenths : I) : ℝ) = 3 / 10 from rfl,
      show ((sevenTenths : I) : ℝ) = 7 / 10 from rfl]
    norm_num
  rw [hk, dipDiagonal_threeTenths, dipDiagonal_sevenTenths] at h
  rw [diagonalUpperBound_dipDiagonal]
  constructor <;> linarith

end ProbabilityTheory.Copula
