/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.QuasiCopula.Basic

/-!
# Bivariate quasi-copulas

Nelsen, *An Introduction to Copulas*, second edition, §6.2.

* `IsQuasiCopula.ofBivariate` checks the quasi-copula conditions for a two-variable formula from
  the four boundary identities, monotonicity and the one-sided Lipschitz bounds in each variable.
* **Characterization of Genest, Quesada Molina, Rodríguez Lallena and Sempi (1999)**
  (Nelsen, §6.2): a function on `[0,1]²` with the
  copula boundary conditions is a quasi-copula if and only if every rectangle with at least one
  side on the boundary of the unit square has a nonnegative increment
  (`isQuasiCopula_iff_rectangleIncrement_nonneg_of_boundary`). A copula needs this for every
  rectangle.
* A **proper quasi-copula** (`quasiCopulaExample`): the function
  `Q(u,v) = max (W(u,v), min (u, v, max(u,v) - 1/3))`, which spreads mass `1/3` uniformly on each
  of the segments from `(0,1/3)` to `(1/3,2/3)`, `(1/3,0)` to `(2/3,1/3)`, `(1/3,2/3)` to
  `(2/3,1)` and `(2/3,1/3)` to `(1,2/3)`, and mass `-1/3` on the diagonal segment from `(1/3,1/3)`
  to `(2/3,2/3)`; cf. the proper quasi-copulas in Nelsen, §6.2. The rectangle `[1/3,2/3]²` has
  increment `-1/3`, so it is not a copula (`not_isClassical_quasiCopulaExample`).
-/

open Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

theorem eq_vecCons_two (u : Fin 2 → I) : u = ![u 0, u 1] := by
  funext i
  fin_cases i <;> rfl

theorem update_one_zero (t : I) : Function.update (fun _ : Fin 2 => (1 : I)) 0 t = ![t, 1] := by
  funext i
  fin_cases i <;> simp

theorem update_one_one (t : I) : Function.update (fun _ : Fin 2 => (1 : I)) 1 t = ![1, t] := by
  funext i
  fin_cases i <;> simp

/-- Check the quasi-copula conditions for a bivariate formula: the four boundary identities,
monotonicity in each variable, and the Lipschitz bound in each variable. -/
theorem IsQuasiCopula.ofBivariate (F : I → I → ℝ)
    (hz₁ : ∀ v, F 0 v = 0) (hz₂ : ∀ u, F u 0 = 0)
    (ho₁ : ∀ v, F 1 v = v) (ho₂ : ∀ u, F u 1 = u)
    (hm₁ : ∀ u u' v, u ≤ u' → F u v ≤ F u' v) (hm₂ : ∀ u v v', v ≤ v' → F u v ≤ F u v')
    (hl₁ : ∀ u u' v, u ≤ u' → F u' v - F u v ≤ (u' : ℝ) - u)
    (hl₂ : ∀ u v v', v ≤ v' → F u v' - F u v ≤ (v' : ℝ) - v) :
    IsQuasiCopula (fun u : Fin 2 → I => F (u 0) (u 1)) where
  normalized := ho₁ 1
  grounded u i hi := by
    fin_cases i
    · change u 0 = 0 at hi
      simp only [hi, hz₁]
    · change u 1 = 0 at hi
      simp only [hi, hz₂]
  marginal i t := by
    fin_cases i <;> simp [ho₁, ho₂]
  monotone u v huv := (hm₁ _ _ _ (huv 0)).trans (hm₂ _ _ _ (huv 1))
  lipschitz u v := by
    have habs₁ : ∀ a b c : I, |F a c - F b c| ≤ |(a : ℝ) - b| := by
      intro a b c
      rcases le_total a b with hab | hab
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm₁ _ _ _ hab)),
          abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))]
        exact hl₁ _ _ _ hab
      · rw [abs_of_nonneg (sub_nonneg.mpr (hm₁ _ _ _ hab)),
          abs_of_nonneg (sub_nonneg.mpr (show (b : ℝ) ≤ a from hab))]
        exact hl₁ _ _ _ hab
    have habs₂ : ∀ a b c : I, |F c a - F c b| ≤ |(a : ℝ) - b| := by
      intro a b c
      rcases le_total a b with hab | hab
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm₂ _ _ _ hab)),
          abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))]
        exact hl₂ _ _ _ hab
      · rw [abs_of_nonneg (sub_nonneg.mpr (hm₂ _ _ _ hab)),
          abs_of_nonneg (sub_nonneg.mpr (show (b : ℝ) ≤ a from hab))]
        exact hl₂ _ _ _ hab
    rw [Fin.sum_univ_two]
    calc
      |F (u 0) (u 1) - F (v 0) (v 1)|
          = |(F (u 0) (u 1) - F (v 0) (u 1)) + (F (v 0) (u 1) - F (v 0) (v 1))| := by ring_nf
      _ ≤ |F (u 0) (u 1) - F (v 0) (u 1)| + |F (v 0) (u 1) - F (v 0) (v 1)| := abs_add_le _ _
      _ ≤ _ := add_le_add (habs₁ _ _ _) (habs₂ _ _ _)

/-- **Characterization of bivariate quasi-copulas** (Genest, Quesada Molina, Rodríguez Lallena
and Sempi, 1999). A function on `[0,1]²` is a quasi-copula if and only if it satisfies the
copula boundary conditions and every rectangle with a side on the boundary of the unit square has
a nonnegative increment. -/
theorem isQuasiCopula_iff_rectangleIncrement_nonneg_of_boundary {Q : (Fin 2 → I) → ℝ} :
    IsQuasiCopula Q ↔
      (∀ (u : Fin 2 → I) (i : Fin 2), u i = 0 → Q u = 0) ∧
        (∀ (i : Fin 2) (t : I), Q (Function.update (fun _ => 1) i t) = (t : ℝ)) ∧
          ∀ a b : Fin 2 → I, a ≤ b → (∃ i, a i = 0 ∨ b i = 1) →
            0 ≤ rectangleIncrement Q a b := by
  constructor
  · intro hQ
    refine ⟨hQ.grounded, hQ.marginal, ?_⟩
    have hz₁ (t : I) : Q ![0, t] = 0 := hQ.grounded _ 0 rfl
    have hz₂ (s : I) : Q ![s, 0] = 0 := hQ.grounded _ 1 rfl
    have ho₁ (t : I) : Q ![1, t] = t := by rw [← update_one_one, hQ.marginal]
    have ho₂ (s : I) : Q ![s, 1] = s := by rw [← update_one_zero, hQ.marginal]
    have hm₁ (s s' t : I) (h : s ≤ s') : Q ![s, t] ≤ Q ![s', t] :=
      hQ.monotone (by intro i; fin_cases i <;> simp [h])
    have hm₂ (s t t' : I) (h : t ≤ t') : Q ![s, t] ≤ Q ![s, t'] :=
      hQ.monotone (by intro i; fin_cases i <;> simp [h])
    have hl₁ (s s' t : I) (h : s ≤ s') : Q ![s', t] - Q ![s, t] ≤ (s' : ℝ) - s := by
      have := (le_abs_self _).trans (hQ.lipschitz ![s', t] ![s, t])
      simpa [Fin.sum_univ_two, abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ s' from h))]
        using this
    have hl₂ (s t t' : I) (h : t ≤ t') : Q ![s, t'] - Q ![s, t] ≤ (t' : ℝ) - t := by
      have := (le_abs_self _).trans (hQ.lipschitz ![s, t'] ![s, t])
      simpa [Fin.sum_univ_two, abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ t' from h))]
        using this
    intro a b hab ⟨i, hi⟩
    obtain ⟨a0, a1, rfl⟩ : ∃ x y, a = ![x, y] := ⟨a 0, a 1, eq_vecCons_two a⟩
    obtain ⟨b0, b1, rfl⟩ : ∃ x y, b = ![x, y] := ⟨b 0, b 1, eq_vecCons_two b⟩
    have h0 : a0 ≤ b0 := hab 0
    have h1 : a1 ≤ b1 := hab 1
    rw [rectangleIncrement_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hi ⊢
    fin_cases i
    · rcases hi with hi | hi
      · simp only [Fin.zero_eta, Matrix.cons_val_zero] at hi
        subst hi
        have := hm₂ b0 a1 b1 h1
        rw [hz₁, hz₁]
        linarith
      · simp only [Fin.zero_eta, Matrix.cons_val_zero] at hi
        subst hi
        have := hl₂ a0 a1 b1 h1
        rw [ho₁, ho₁]
        linarith
    · rcases hi with hi | hi
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hi
        subst hi
        have := hm₁ a0 b0 b1 h0
        rw [hz₂, hz₂]
        linarith
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hi
        subst hi
        have := hl₁ a0 b0 a1 h0
        rw [ho₂, ho₂]
        linarith
  · rintro ⟨hg, hm, hr⟩
    have hz₁ (t : I) : Q ![0, t] = 0 := hg _ 0 rfl
    have hz₂ (s : I) : Q ![s, 0] = 0 := hg _ 1 rfl
    have ho₁ (t : I) : Q ![1, t] = t := by rw [← update_one_one, hm]
    have ho₂ (s : I) : Q ![s, 1] = s := by rw [← update_one_zero, hm]
    have hQ : Q = fun u => Q ![u 0, u 1] := funext fun u => congrArg Q (eq_vecCons_two u)
    rw [hQ]
    have hle (s s' t t' : I) (h : s ≤ s') (h' : t ≤ t') : ![s, t] ≤ ![s', t'] := by
      intro i; fin_cases i <;> simpa
    apply IsQuasiCopula.ofBivariate (fun s t => Q ![s, t]) hz₁ hz₂ ho₁ ho₂
    · intro s s' t h
      have := hr ![s, 0] ![s', t] (hle _ _ _ _ h unitInterval.nonneg') ⟨1, Or.inl rfl⟩
      rw [rectangleIncrement_two] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        hz₂] at this
      linarith
    · intro s t t' h
      have := hr ![0, t] ![s, t'] (hle _ _ _ _ unitInterval.nonneg' h) ⟨0, Or.inl rfl⟩
      rw [rectangleIncrement_two] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        hz₁] at this
      linarith
    · intro s s' t h
      have := hr ![s, t] ![s', 1] (hle _ _ _ _ h unitInterval.le_one') ⟨1, Or.inr rfl⟩
      rw [rectangleIncrement_two] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        ho₂] at this
      linarith
    · intro s t t' h
      have := hr ![s, t] ![1, t'] (hle _ _ _ _ unitInterval.le_one' h) ⟨0, Or.inr rfl⟩
      rw [rectangleIncrement_two] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        ho₁] at this
      linarith

/-! ### A proper quasi-copula -/

/-- The real formula `max (W(s,t), min (s, t, max(s,t) - 1/3))` behind `quasiCopulaExample`. -/
noncomputable def quasiCopulaExampleFormula (s t : ℝ) : ℝ :=
  max (max 0 (s + t - 1)) (min (min s t) (max s t - 1 / 3))

theorem quasiCopulaExampleFormula_comm (s t : ℝ) :
    quasiCopulaExampleFormula s t = quasiCopulaExampleFormula t s := by
  simp only [quasiCopulaExampleFormula, add_comm s t, min_comm s t, max_comm s t]

theorem quasiCopulaExampleFormula_zero_left {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    quasiCopulaExampleFormula 0 t = 0 := by
  simp only [quasiCopulaExampleFormula, max_def, min_def]
  split_ifs <;> linarith

theorem quasiCopulaExampleFormula_one_left {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    quasiCopulaExampleFormula 1 t = t := by
  simp only [quasiCopulaExampleFormula, max_def, min_def]
  split_ifs <;> linarith

theorem abs_quasiCopulaExampleFormula_sub_left (s s' t : ℝ) :
    |quasiCopulaExampleFormula s' t - quasiCopulaExampleFormula s t| ≤ |s' - s| := by
  have h1 : |max 0 (s' + t - 1) - max 0 (s + t - 1)| ≤ |s' - s| := by
    have h := abs_max_sub_max_le_max (0 : ℝ) (s' + t - 1) 0 (s + t - 1)
    rw [sub_self, abs_zero, show s' + t - 1 - (s + t - 1) = s' - s by ring] at h
    exact h.trans (max_le (abs_nonneg _) le_rfl)
  have h2 : |min s' t - min s t| ≤ |s' - s| := by
    have h := abs_min_sub_min_le_max s' t s t
    rw [sub_self, abs_zero] at h
    exact h.trans (max_le le_rfl (abs_nonneg _))
  have h3 : |(max s' t - 1 / 3) - (max s t - 1 / 3)| ≤ |s' - s| := by
    rw [show max s' t - 1 / 3 - (max s t - 1 / 3) = max s' t - max s t by ring]
    exact abs_max_sub_max_le_abs s' s t
  have h4 : |min (min s' t) (max s' t - 1 / 3) - min (min s t) (max s t - 1 / 3)| ≤ |s' - s| :=
    (abs_min_sub_min_le_max _ _ _ _).trans (max_le h2 h3)
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h1 h4)

/-- A proper bivariate quasi-copula: `max (W(u,v), min (u, v, max(u,v) - 1/3))`. -/
noncomputable def quasiCopulaExample (u : Fin 2 → I) : ℝ :=
  quasiCopulaExampleFormula (u 0) (u 1)

/-- `quasiCopulaExample` is a quasi-copula. -/
theorem isQuasiCopula_quasiCopulaExample : IsQuasiCopula quasiCopulaExample := by
  have hl₁ (s s' t : I) (h : s ≤ s') : quasiCopulaExampleFormula s' t -
      quasiCopulaExampleFormula s t ≤ (s' : ℝ) - s := by
    have := (le_abs_self _).trans (abs_quasiCopulaExampleFormula_sub_left s s' t)
    rwa [abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ s' from h))] at this
  apply IsQuasiCopula.ofBivariate (fun s t : I => quasiCopulaExampleFormula s t)
  · intro v
    exact quasiCopulaExampleFormula_zero_left v.2.1 v.2.2
  · intro u
    rw [quasiCopulaExampleFormula_comm]
    exact quasiCopulaExampleFormula_zero_left u.2.1 u.2.2
  · intro v
    exact quasiCopulaExampleFormula_one_left v.2.1 v.2.2
  · intro u
    rw [quasiCopulaExampleFormula_comm]
    exact quasiCopulaExampleFormula_one_left u.2.1 u.2.2
  · intro u u' v h
    have h' : (u : ℝ) ≤ u' := h
    simp only [quasiCopulaExampleFormula]
    gcongr
  · intro u v v' h
    have h' : (v : ℝ) ≤ v' := h
    simp only [quasiCopulaExampleFormula]
    gcongr
  · exact hl₁
  · intro u v v' h
    have := hl₁ v v' u h
    rwa [quasiCopulaExampleFormula_comm v', quasiCopulaExampleFormula_comm v] at this

/-- The point `1/3` of the unit interval. -/
private noncomputable def third : I := ⟨1 / 3, by norm_num, by norm_num⟩

/-- The point `2/3` of the unit interval. -/
private noncomputable def twoThirds : I := ⟨2 / 3, by norm_num, by norm_num⟩

/-- The central square `[1/3, 2/3]²` has increment `-1/3` under `quasiCopulaExample`. -/
theorem rectangleIncrement_quasiCopulaExample :
    rectangleIncrement quasiCopulaExample ![⟨1 / 3, by norm_num, by norm_num⟩,
      ⟨1 / 3, by norm_num, by norm_num⟩] ![⟨2 / 3, by norm_num, by norm_num⟩,
      ⟨2 / 3, by norm_num, by norm_num⟩] = -1 / 3 := by
  rw [rectangleIncrement_two]
  simp only [quasiCopulaExample, quasiCopulaExampleFormula, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num [max_def, min_def]

/-- **`quasiCopulaExample` is a proper quasi-copula**: it violates the rectangle inequality. -/
theorem not_isClassical_quasiCopulaExample : ¬ IsClassical quasiCopulaExample := by
  intro h
  have := h.increasing ![third, third] ![twoThirds, twoThirds] (by
    intro i
    fin_cases i <;> (change (1 / 3 : ℝ) ≤ 2 / 3; norm_num))
  rw [show ![third, third] = ![⟨1 / 3, by norm_num, by norm_num⟩,
      ⟨1 / 3, by norm_num, by norm_num⟩] from rfl,
    show ![twoThirds, twoThirds] = ![⟨2 / 3, by norm_num, by norm_num⟩,
      ⟨2 / 3, by norm_num, by norm_num⟩] from rfl,
    rectangleIncrement_quasiCopulaExample] at this
  norm_num at this

/-- No copula has `quasiCopulaExample` as its CDF. -/
theorem cdf_ne_quasiCopulaExample (C : Copula 2) : C.cdf ≠ quasiCopulaExample := by
  intro h
  exact not_isClassical_quasiCopulaExample (h ▸ C.isClassical_cdf)

end ProbabilityTheory.Copula
