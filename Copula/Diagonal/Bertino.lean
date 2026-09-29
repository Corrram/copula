/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Diagonal.Construction
import Copula.Rectangle
import Copula.Order.Orthant
import Copula.Symmetry

/-!
# Bertino copulas: the smallest copula with a prescribed diagonal

For a diagonal function `δ` (see `IsDiagonalFunction`) write `δ̂ t = t - δ t` for the
*diagonal gap* (`diagGap`). The **Bertino copula** of `δ` is

`B_δ(u, v) = min u v - min_{t ∈ [u ∧ v, u ∨ v]} (t - δ t)`

(Bertino 1977; Fredricks and Nelsen, *The Bertino family of copulas*, 2002; see also Nelsen,
*An Introduction to Copulas*, 2nd ed., §3.2.6). The minimum is written as an infimum over the
closed interval `Set.uIcc u v` (`bertinoGap`).

Main results:

* `symmetric_twoIncreasing`: a symmetric function on `[0,1]²` is `2`-increasing as soon as its
  rectangle increments are nonnegative on rectangles lying weakly above the diagonal and on squares
  centred on the diagonal (a general reduction lemma).
* `bertinoCopula δ hδ`: the Bertino copula is a copula, with `cdf_bertinoCopula`,
  `diagonal_bertinoCopula` (its diagonal is `δ`) and `isExchangeable_bertinoCopula`.
* `bertinoCopula_cdf_le`, `lowerOrthantLE_bertinoCopula`: every copula `C` with diagonal `δ`
  satisfies `B_δ ≤ C` pointwise (Fredricks–Nelsen 2002). Since `B_δ` itself has
  diagonal `δ`, it is the pointwise smallest copula with this diagonal, so the lower bound is best
  possible.
* `bertinoCopula_diagonal_comonotonic`, `bertinoCopula_diagonal_countermonotonic`: the Bertino
  copulas of the diagonals of `M` and `W` are `M` and `W`.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-! ### A reduction lemma for symmetric `2`-increasing functions -/

/-- The four-term rectangle increment of a bivariate function on `[a,b] × [c,e]`. -/
def rectIncr (F : I → I → ℝ) (a b c e : I) : ℝ := F b e - F a e - F b c + F a c

private theorem rectIncr_symm {F : I → I → ℝ} (hF : ∀ u v, F u v = F v u) (a b c e : I) :
    rectIncr F a b c e = rectIncr F c e a b := by
  unfold rectIncr
  rw [hF b e, hF a e, hF b c, hF a c]
  ring

private theorem rectIncr_self_left (F : I → I → ℝ) (a c e : I) : rectIncr F a a c e = 0 := by
  unfold rectIncr; ring

/-- **Reduction lemma for symmetric functions.** A symmetric function `F` on `[0,1]²` is
`2`-increasing provided its increments are nonnegative on rectangles `[a,b] × [c,e]` with
`b ≤ c` (weakly above the diagonal) and on diagonal squares `[s,t] × [s,t]`. -/
theorem symmetric_twoIncreasing (F : I → I → ℝ) (hF : ∀ u v, F u v = F v u)
    (hup : ∀ a b c e : I, a ≤ b → b ≤ c → c ≤ e → 0 ≤ F b e - F a e - F b c + F a c)
    (hsq : ∀ s t : I, s ≤ t → 0 ≤ F t t - F s t - F t s + F s s) :
    ∀ a b c e : I, a ≤ b → c ≤ e → 0 ≤ F b e - F a e - F b c + F a c := by
  have hup' : ∀ a b c e : I, a ≤ b → b ≤ c → c ≤ e → 0 ≤ rectIncr F a b c e := hup
  intro a b c e hab hce
  change 0 ≤ rectIncr F a b c e
  rcases le_or_gt b c with hbc | hcb
  · exact hup' a b c e hab hbc hce
  rcases le_or_gt e a with hea | hae
  · rw [rectIncr_symm hF]
    exact hup' c e a b hce hea hab
  set p := max a c with hp
  set q := min b e with hq
  have hpq : p ≤ q := max_le (le_min hab hae.le) (le_min hcb.le hce)
  have hsplit : rectIncr F a b c e = rectIncr F a p c e + rectIncr F p q c p +
      rectIncr F p q p q + rectIncr F p q q e + rectIncr F q b c e := by
    unfold rectIncr; ring
  have h1 : 0 ≤ rectIncr F a p c e := by
    rcases le_total a c with hac | hca
    · rw [hp, max_eq_right hac]
      exact hup' a c c e hac le_rfl hce
    · rw [hp, max_eq_left hca, rectIncr_self_left]
  have h2 : 0 ≤ rectIncr F p q c p := by
    rw [rectIncr_symm hF]
    exact hup' c p p q (le_max_right a c) le_rfl hpq
  have h3 : 0 ≤ rectIncr F p q p q := by
    have := hsq p q hpq
    unfold rectIncr
    linarith
  have h4 : 0 ≤ rectIncr F p q q e := hup' p q q e hpq le_rfl (min_le_right b e)
  have h5 : 0 ≤ rectIncr F q b c e := by
    rcases le_total b e with hbe | heb
    · rw [hq, min_eq_left hbe, rectIncr_self_left]
    · rw [hq, min_eq_right heb, rectIncr_symm hF]
      exact hup' c e e b hce le_rfl heb
  rw [hsplit]
  linarith

/-! ### The diagonal gap and its minimum over an interval -/

/-- The diagonal gap `t - δ t`. -/
def diagGap (δ : I → ℝ) (t : I) : ℝ := (t : ℝ) - δ t

/-- The minimum of the diagonal gap over the closed interval between `u` and `v`. -/
noncomputable def bertinoGap (δ : I → ℝ) (u v : I) : ℝ := sInf (diagGap δ '' uIcc u v)

variable {δ : I → ℝ}

namespace IsDiagonalFunction

theorem zero (hδ : IsDiagonalFunction δ) : δ 0 = 0 :=
  le_antisymm (by simpa using hδ.le_self 0) (hδ.nonneg 0)

theorem diagGap_nonneg (hδ : IsDiagonalFunction δ) (t : I) : 0 ≤ diagGap δ t := by
  unfold diagGap; linarith [hδ.le_self t]

theorem diagGap_zero (hδ : IsDiagonalFunction δ) : diagGap δ 0 = 0 := by
  simp [diagGap, hδ.zero]

theorem diagGap_one (hδ : IsDiagonalFunction δ) : diagGap δ 1 = 0 := by
  simp [diagGap, hδ.one]

/-- The lower bound `2t - 1 ≤ δ t`. -/
theorem two_mul_sub_one_le (hδ : IsDiagonalFunction δ) (t : I) : 2 * (t : ℝ) - 1 ≤ δ t := by
  have h := hδ.lipschitz t 1 unitInterval.le_one'
  rw [hδ.one, Set.Icc.coe_one] at h
  linarith

theorem diagGap_le_one_sub (hδ : IsDiagonalFunction δ) (t : I) : diagGap δ t ≤ 1 - t := by
  unfold diagGap; linarith [hδ.two_mul_sub_one_le t]

theorem diagGap_le (hδ : IsDiagonalFunction δ) (t : I) : diagGap δ t ≤ t := by
  unfold diagGap; linarith [hδ.nonneg t]

/-- The diagonal gap does not increase faster than the identity. -/
theorem diagGap_sub_le (hδ : IsDiagonalFunction δ) {s t : I} (hst : s ≤ t) :
    diagGap δ t - diagGap δ s ≤ (t : ℝ) - s := by
  unfold diagGap; linarith [hδ.monotone hst]

/-- The diagonal gap does not decrease faster than the identity. -/
theorem diagGap_sub_ge (hδ : IsDiagonalFunction δ) {s t : I} (hst : s ≤ t) :
    diagGap δ s - diagGap δ t ≤ (t : ℝ) - s := by
  unfold diagGap; linarith [hδ.lipschitz s t hst]

theorem continuous (hδ : IsDiagonalFunction δ) : Continuous δ := by
  have hL : LipschitzWith 2 δ := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
    rcases le_total s t with hst | hts
    · have h1 := hδ.lipschitz s t hst
      have h2 := hδ.monotone hst
      have hst' : (s : ℝ) ≤ t := hst
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm,
        abs_of_nonneg (by linarith)]
      linarith
    · have h1 := hδ.lipschitz t s hts
      have h2 := hδ.monotone hts
      have hts' : (t : ℝ) ≤ s := hts
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  exact hL.continuous

theorem continuous_diagGap (hδ : IsDiagonalFunction δ) : Continuous (diagGap δ) :=
  continuous_subtype_val.sub hδ.continuous

theorem bddBelow_diagGap_image (hδ : IsDiagonalFunction δ) (s : Set I) :
    BddBelow (diagGap δ '' s) :=
  ⟨0, by rintro _ ⟨t, -, rfl⟩; exact hδ.diagGap_nonneg t⟩

theorem bertinoGap_le (hδ : IsDiagonalFunction δ) {u v t : I} (ht : t ∈ uIcc u v) :
    bertinoGap δ u v ≤ diagGap δ t :=
  csInf_le (hδ.bddBelow_diagGap_image _) ⟨t, ht, rfl⟩

theorem bertinoGap_nonneg (hδ : IsDiagonalFunction δ) (u v : I) : 0 ≤ bertinoGap δ u v :=
  le_csInf (nonempty_uIcc.image _) (by rintro _ ⟨t, -, rfl⟩; exact hδ.diagGap_nonneg t)

theorem bertinoGap_eq_zero (hδ : IsDiagonalFunction δ) {u v t : I} (ht : t ∈ uIcc u v)
    (h0 : diagGap δ t = 0) : bertinoGap δ u v = 0 :=
  le_antisymm (h0 ▸ hδ.bertinoGap_le ht) (hδ.bertinoGap_nonneg u v)

theorem bertinoGap_anti (hδ : IsDiagonalFunction δ) {u v u' v' : I}
    (h : uIcc u v ⊆ uIcc u' v') : bertinoGap δ u' v' ≤ bertinoGap δ u v :=
  csInf_le_csInf (hδ.bddBelow_diagGap_image _) (nonempty_uIcc.image _) (image_mono h)

end IsDiagonalFunction

theorem le_bertinoGap {u v : I} {L : ℝ} (h : ∀ t ∈ uIcc u v, L ≤ diagGap δ t) :
    L ≤ bertinoGap δ u v :=
  le_csInf (nonempty_uIcc.image _) (by rintro _ ⟨t, ht, rfl⟩; exact h t ht)

theorem bertinoGap_comm (u v : I) : bertinoGap δ u v = bertinoGap δ v u := by
  unfold bertinoGap; rw [uIcc_comm]

@[simp] theorem bertinoGap_self (t : I) : bertinoGap δ t t = diagGap δ t := by
  simp [bertinoGap]

/-! ### The Bertino kernel -/

/-- The Bertino kernel `min u v - min_{t ∈ [u ∧ v, u ∨ v]} (t - δ t)`. -/
noncomputable def bertinoKernel (δ : I → ℝ) (u v : I) : ℝ :=
  min (u : ℝ) v - bertinoGap δ u v

theorem bertinoKernel_comm (u v : I) : bertinoKernel δ u v = bertinoKernel δ v u := by
  unfold bertinoKernel; rw [min_comm, bertinoGap_comm]

@[simp] theorem bertinoKernel_self (t : I) : bertinoKernel δ t t = δ t := by
  simp [bertinoKernel, diagGap]

theorem bertinoKernel_of_le {u v : I} (h : u ≤ v) :
    bertinoKernel δ u v = (u : ℝ) - bertinoGap δ u v := by
  unfold bertinoKernel; rw [min_eq_left (show (u : ℝ) ≤ v from h)]

namespace IsDiagonalFunction

private theorem bertino_up (hδ : IsDiagonalFunction δ) (a b c e : I) (hab : a ≤ b)
    (hbc : b ≤ c) (hce : c ≤ e) :
    0 ≤ bertinoKernel δ b e - bertinoKernel δ a e - bertinoKernel δ b c +
      bertinoKernel δ a c := by
  rw [bertinoKernel_of_le (hbc.trans hce), bertinoKernel_of_le ((hab.trans hbc).trans hce),
    bertinoKernel_of_le hbc, bertinoKernel_of_le (hab.trans hbc)]
  have hX : bertinoGap δ a c ≤ bertinoGap δ b c :=
    hδ.bertinoGap_anti (uIcc_subset_uIcc (mem_uIcc_of_le hab hbc) right_mem_uIcc)
  have hY : bertinoGap δ b e ≤ bertinoGap δ b c :=
    hδ.bertinoGap_anti (uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hbc hce))
  have hZ : min (bertinoGap δ a c) (bertinoGap δ b e) ≤ bertinoGap δ a e := by
    apply le_bertinoGap
    intro t ht
    rw [uIcc_of_le ((hab.trans hbc).trans hce)] at ht
    rcases le_total t c with htc | hct
    · exact (min_le_left _ _).trans (hδ.bertinoGap_le (mem_uIcc_of_le ht.1 htc))
    · exact (min_le_right _ _).trans (hδ.bertinoGap_le (mem_uIcc_of_le (hbc.trans hct) ht.2))
  rcases le_total (bertinoGap δ a c) (bertinoGap δ b e) with h | h
  · rw [min_eq_left h] at hZ; linarith
  · rw [min_eq_right h] at hZ; linarith

private theorem bertino_square (hδ : IsDiagonalFunction δ) (s t : I) (hst : s ≤ t) :
    0 ≤ bertinoKernel δ t t - bertinoKernel δ s t - bertinoKernel δ t s +
      bertinoKernel δ s s := by
  rw [bertinoKernel_comm t s, bertinoKernel_self, bertinoKernel_self, bertinoKernel_of_le hst]
  have h : (s : ℝ) - (δ s + δ t) / 2 ≤ bertinoGap δ s t := by
    apply le_bertinoGap
    intro w hw
    rw [uIcc_of_le hst] at hw
    have h1 := hδ.monotone hw.2
    have h2 := hδ.lipschitz s w hw.1
    unfold diagGap
    linarith
  linarith

/-- The Bertino kernel of a diagonal function satisfies the classical copula conditions. -/
theorem isClassical_bertino (hδ : IsDiagonalFunction δ) :
    IsClassical (fun u : Fin 2 → I => bertinoKernel δ (u 0) (u 1)) := by
  apply IsClassical.ofBivariate (bertinoKernel δ)
  · intro v
    rw [bertinoKernel_of_le (unitInterval.nonneg' (t := v)), hδ.bertinoGap_eq_zero left_mem_uIcc hδ.diagGap_zero]
    simp
  · intro u
    rw [bertinoKernel_comm, bertinoKernel_of_le (unitInterval.nonneg' (t := u)),
      hδ.bertinoGap_eq_zero left_mem_uIcc hδ.diagGap_zero]
    simp
  · intro v
    rw [bertinoKernel_comm, bertinoKernel_of_le (unitInterval.le_one' (t := v)),
      hδ.bertinoGap_eq_zero right_mem_uIcc hδ.diagGap_one]
    simp
  · intro u
    rw [bertinoKernel_of_le (unitInterval.le_one' (t := u)), hδ.bertinoGap_eq_zero right_mem_uIcc hδ.diagGap_one]
    simp
  · exact symmetric_twoIncreasing _ bertinoKernel_comm hδ.bertino_up hδ.bertino_square

end IsDiagonalFunction

/-- The **Bertino copula** `B_δ(u,v) = min u v - min_{t ∈ [u ∧ v, u ∨ v]} (t - δ t)` of a
diagonal function `δ` (Fredricks–Nelsen 2002). -/
noncomputable def bertinoCopula (δ : I → ℝ) (hδ : IsDiagonalFunction δ) : Copula 2 :=
  ofClassical _ hδ.isClassical_bertino

/-- The CDF of the Bertino copula. -/
theorem cdf_bertinoCopula (hδ : IsDiagonalFunction δ) (u : Fin 2 → I) :
    (bertinoCopula δ hδ).cdf u = bertinoKernel δ (u 0) (u 1) :=
  congrFun (cdf_ofClassical _ hδ.isClassical_bertino) u

@[simp] theorem cdf_bertinoCopula_two (hδ : IsDiagonalFunction δ) (u v : I) :
    (bertinoCopula δ hδ).cdf ![u, v] = bertinoKernel δ u v :=
  cdf_bertinoCopula hδ _

/-- The Bertino copula of `δ` has diagonal section `δ`. -/
@[simp] theorem diagonal_bertinoCopula (hδ : IsDiagonalFunction δ) (t : I) :
    (bertinoCopula δ hδ).diagonal t = δ t := by
  simp [diagonal]

/-- Bertino copulas are exchangeable. -/
theorem isExchangeable_bertinoCopula (hδ : IsDiagonalFunction δ) :
    (bertinoCopula δ hδ).IsExchangeable := by
  rw [isExchangeable_iff]
  intro u v
  simp [bertinoKernel_comm u v]

/-- A bivariate copula CDF increases by at most `t - s` when its first argument moves from `s`
to `t`. -/
theorem cdf_sub_le_left (C : Copula 2) {s t : I} (hst : s ≤ t) (v : I) :
    C.cdf ![t, v] - C.cdf ![s, v] ≤ (t : ℝ) - s := by
  have h := C.abs_cdf_sub_le_sum_abs ![t, v] ![s, v]
  have hst' : (s : ℝ) ≤ t := hst
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, abs_zero, add_zero, abs_of_nonneg (sub_nonneg.mpr hst')] at h
  exact (le_abs_self _).trans h

/-- A bivariate copula CDF increases by at most `t - s` when its second argument moves from `s`
to `t`. -/
theorem cdf_sub_le_right (C : Copula 2) {s t : I} (hst : s ≤ t) (u : I) :
    C.cdf ![u, t] - C.cdf ![u, s] ≤ (t : ℝ) - s := by
  have h := C.abs_cdf_sub_le_sum_abs ![u, t] ![u, s]
  have hst' : (s : ℝ) ≤ t := hst
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, abs_zero, zero_add, abs_of_nonneg (sub_nonneg.mpr hst')] at h
  exact (le_abs_self _).trans h

theorem cdf_mono_two (C : Copula 2) {u u' v v' : I} (hu : u ≤ u') (hv : v ≤ v') :
    C.cdf ![u, v] ≤ C.cdf ![u', v'] := by
  apply C.monotone_cdf
  intro i
  fin_cases i
  · exact hu
  · exact hv

/-- **The Bertino copula is the smallest copula with diagonal `δ`** (Fredricks–Nelsen 2002):
every copula `C` with diagonal section `δ` satisfies `B_δ ≤ C` pointwise. -/
theorem bertinoCopula_cdf_le (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hC : ∀ t, C.diagonal t = δ t) (u v : I) :
    (bertinoCopula δ hδ).cdf ![u, v] ≤ C.cdf ![u, v] := by
  rw [cdf_bertinoCopula_two]
  rcases le_total u v with huv | hvu
  · rw [bertinoKernel_of_le huv]
    have h : (u : ℝ) - C.cdf ![u, v] ≤ bertinoGap δ u v := by
      apply le_bertinoGap
      intro t ht
      rw [uIcc_of_le huv] at ht
      have h1 := C.cdf_mono_two (le_refl t) ht.2
      have h2 := C.cdf_sub_le_left ht.1 v
      have h3 := hC t
      unfold diagonal at h3
      unfold diagGap
      linarith
    linarith
  · rw [bertinoKernel_comm, bertinoKernel_of_le hvu]
    have h : (v : ℝ) - C.cdf ![u, v] ≤ bertinoGap δ v u := by
      apply le_bertinoGap
      intro t ht
      rw [uIcc_of_le hvu] at ht
      have h1 := C.cdf_mono_two ht.2 (le_refl t)
      have h2 := C.cdf_sub_le_right ht.1 u
      have h3 := hC t
      unfold diagonal at h3
      unfold diagGap
      linarith
    linarith

/-- The Bertino copula of `δ` lies below every copula with diagonal `δ` in the lower orthant
order. -/
theorem lowerOrthantLE_bertinoCopula (hδ : IsDiagonalFunction δ) {C : Copula 2}
    (hC : ∀ t, C.diagonal t = δ t) : (bertinoCopula δ hδ).LowerOrthantLE C := by
  intro u
  have hu : u = ![u 0, u 1] := by ext i; fin_cases i <;> rfl
  rw [hu]
  exact bertinoCopula_cdf_le hδ hC (u 0) (u 1)

/-- The Bertino copula of the diagonal of a copula lies below that copula. -/
theorem lowerOrthantLE_bertinoCopula_diagonal (C : Copula 2) :
    (bertinoCopula C.diagonal (isDiagonalFunction_diagonal C)).LowerOrthantLE C :=
  lowerOrthantLE_bertinoCopula _ fun _ => rfl

/-- The Bertino copula of the diagonal of `M` is `M`. -/
theorem bertinoCopula_diagonal_comonotonic :
    bertinoCopula (comonotonic 2).diagonal (isDiagonalFunction_diagonal _) = comonotonic 2 := by
  rw [← diagonal_eq_id_iff]
  intro t
  simp

/-- The Bertino copula of the diagonal of `W` is `W`: the countermonotonic copula is the
smallest copula with its diagonal. -/
theorem bertinoCopula_diagonal_countermonotonic :
    bertinoCopula countermonotonic.diagonal (isDiagonalFunction_diagonal _) =
      countermonotonic := by
  apply ext_cdf
  intro u
  exact le_antisymm (lowerOrthantLE_bertinoCopula_diagonal _ u)
    (cdf_countermonotonic_le _ u)

end ProbabilityTheory.Copula
