/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Classical
import Copula.CDF.Bounds
import Copula.Countermonotonic

/-!
# Quasi-copulas

Nelsen, *An Introduction to Copulas*, second edition, §6.2. Nelsen defines quasi-copulas through
tracks; following Genest, Quesada Molina, Rodríguez Lallena and Sempi (1999), who proved the
equivalence, and Durante–Sempi, *Principles of Copula Theory*, §7.2, we use the functional
characterization as the definition.

A `d`-quasi-copula is a function `Q : [0,1]^d → ℝ` that is grounded, has uniform
one-dimensional margins, is nondecreasing in each argument, and satisfies the Lipschitz
condition `|Q u - Q v| ≤ ∑ i, |u i - v i|` (`IsQuasiCopula`). As for `IsClassical`, the value
at the top corner is required explicitly so that dimension zero is covered.

* Every copula CDF, and more generally every function satisfying the classical copula
  conditions, is a quasi-copula (`isQuasiCopula_cdf`, `IsClassical.isQuasiCopula`); a
  quasi-copula is a copula exactly when all of its rectangle increments are nonnegative
  (`isClassical_iff_isQuasiCopula`).
* Quasi-copulas satisfy the Fréchet–Hoeffding bounds (`IsQuasiCopula.frechet_lower_le`,
  `IsQuasiCopula.le_frechet_upper`, and for `d = 2` the forms `W ≤ Q ≤ M`).
* Pointwise suprema and infima of nonempty families of quasi-copulas, in particular of copulas,
  are quasi-copulas (`IsQuasiCopula.iSup`, `IsQuasiCopula.iInf`), and quasi-copulas are closed
  under convex combinations (`IsQuasiCopula.convexCombination`).

The bivariate characterization by rectangles touching the boundary and a proper quasi-copula
are in `Copula.QuasiCopula.Bivariate`.
-/

open Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- A `d`-dimensional quasi-copula: grounded, uniform margins, nondecreasing in each argument, and
`1`-Lipschitz for the sum of coordinate distances. -/
structure IsQuasiCopula (Q : (Fin d → I) → ℝ) : Prop where
  /-- The top corner has value one, including in dimension zero. -/
  normalized : Q (fun _ => 1) = 1
  /-- A zero coordinate makes the function vanish. -/
  grounded : ∀ (u : Fin d → I) (i : Fin d), u i = 0 → Q u = 0
  /-- The one-coordinate boundary faces are uniform. -/
  marginal : ∀ (i : Fin d) (t : I), Q (Function.update (fun _ => 1) i t) = (t : ℝ)
  /-- Monotonicity in the pointwise order. -/
  monotone : Monotone Q
  /-- The Lipschitz condition for the sum of coordinate distances. -/
  lipschitz : ∀ u v, |Q u - Q v| ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)|

/-- Functions satisfying the classical copula conditions are quasi-copulas. -/
theorem IsClassical.isQuasiCopula {F : (Fin d → I) → ℝ} (hF : IsClassical F) :
    IsQuasiCopula F :=
  ⟨hF.normalized, hF.grounded, hF.marginal, hF.monotone, hF.abs_sub_le_sum_abs⟩

/-- **Every copula is a quasi-copula.** -/
theorem isQuasiCopula_cdf (C : Copula d) : IsQuasiCopula C.cdf :=
  C.isClassical_cdf.isQuasiCopula

/-- A quasi-copula is (the CDF of) a copula exactly when all rectangle increments are
nonnegative. -/
theorem isClassical_iff_isQuasiCopula {F : (Fin d → I) → ℝ} :
    IsClassical F ↔ IsQuasiCopula F ∧ ∀ a b, a ≤ b → 0 ≤ rectangleIncrement F a b :=
  ⟨fun hF => ⟨hF.isQuasiCopula, hF.increasing⟩,
    fun ⟨hQ, h⟩ => ⟨hQ.normalized, hQ.grounded, hQ.marginal, h⟩⟩

/-- A quasi-copula with a negative rectangle increment is not the CDF of any copula. -/
theorem cdf_ne_of_rectangleIncrement_neg {F : (Fin d → I) → ℝ} {a b : Fin d → I} (hab : a ≤ b)
    (h : rectangleIncrement F a b < 0) (C : Copula d) : C.cdf ≠ F := by
  rintro rfl
  exact (not_le.mpr h) (C.rectangleIncrement_cdf_nonneg a b hab)

namespace IsQuasiCopula

variable {Q : (Fin d → I) → ℝ}

theorem le_coord (hQ : IsQuasiCopula Q) (u : Fin d → I) (i : Fin d) : Q u ≤ (u i : ℝ) := by
  have h := hQ.monotone (show u ≤ Function.update (fun _ => 1) i (u i) by
    intro j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj, unitInterval.le_one'])
  rwa [hQ.marginal] at h

theorem le_one (hQ : IsQuasiCopula Q) (u : Fin d → I) : Q u ≤ 1 := by
  rw [← hQ.normalized]
  exact hQ.monotone fun _ => unitInterval.le_one'

theorem nonneg (hQ : IsQuasiCopula Q) (u : Fin d → I) : 0 ≤ Q u := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i⟩⟩
  · rw [Subsingleton.elim u (fun _ => 1), hQ.normalized]
    exact zero_le_one
  · rw [← hQ.grounded (Function.update u i 0) i (by simp)]
    apply hQ.monotone
    intro j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]

/-- The untruncated lower Fréchet–Hoeffding bound for quasi-copulas. -/
theorem sum_sub_dim_add_one_le (hQ : IsQuasiCopula Q) (u : Fin d → I) :
    (∑ i, (u i : ℝ)) - d + 1 ≤ Q u := by
  have h := hQ.lipschitz (fun _ => 1) u
  have hs : ∑ i, |((1 : I) : ℝ) - (u i : ℝ)| = (d : ℝ) - ∑ i, (u i : ℝ) := by
    calc
      ∑ i, |((1 : I) : ℝ) - (u i : ℝ)| = ∑ i, (1 - (u i : ℝ)) :=
        Finset.sum_congr rfl fun i _ => by
          rw [Set.Icc.coe_one, abs_of_nonneg (sub_nonneg.mpr (u i).property.2)]
      _ = _ := by simp [Finset.sum_sub_distrib]
  rw [hQ.normalized, hs] at h
  linarith [le_abs_self (1 - Q u)]

/-- **Fréchet–Hoeffding lower bound for quasi-copulas.** -/
theorem frechet_lower_le (hQ : IsQuasiCopula Q) (u : Fin d → I) :
    max 0 ((∑ i, (u i : ℝ)) - d + 1) ≤ Q u :=
  max_le (hQ.nonneg u) (hQ.sum_sub_dim_add_one_le u)

/-- **Fréchet–Hoeffding upper bound for quasi-copulas.** -/
theorem le_frechet_upper (hQ : IsQuasiCopula Q) (u : Fin d → I) :
    Q u ≤ ((⨅ i, u i : I) : ℝ) := by
  have h : (⟨Q u, hQ.nonneg u, hQ.le_one u⟩ : I) ≤ ⨅ i, u i :=
    le_iInf fun i => hQ.le_coord u i
  exact h

/-- The upper bound `Q ≤ M`, with `M` the comonotonic copula. -/
theorem le_cdf_comonotonic (hQ : IsQuasiCopula Q) (u : Fin d → I) :
    Q u ≤ (comonotonic d).cdf u := by
  rw [cdf_comonotonic]
  exact hQ.le_frechet_upper u

/-- The bivariate lower bound `W ≤ Q`, with `W` the countermonotonic copula. -/
theorem cdf_countermonotonic_le {Q : (Fin 2 → I) → ℝ} (hQ : IsQuasiCopula Q) (u : Fin 2 → I) :
    countermonotonic.cdf u ≤ Q u := by
  have h := hQ.frechet_lower_le u
  rw [Fin.sum_univ_two] at h
  rw [cdf_countermonotonic]
  convert h using 2
  push_cast
  ring

theorem bddAbove_range {ι : Type*} {Q : ι → (Fin d → I) → ℝ} (hQ : ∀ k, IsQuasiCopula (Q k))
    (u : Fin d → I) : BddAbove (range fun k => Q k u) :=
  ⟨1, by rintro _ ⟨k, rfl⟩; exact (hQ k).le_one u⟩

theorem bddBelow_range {ι : Type*} {Q : ι → (Fin d → I) → ℝ} (hQ : ∀ k, IsQuasiCopula (Q k))
    (u : Fin d → I) : BddBelow (range fun k => Q k u) :=
  ⟨0, by rintro _ ⟨k, rfl⟩; exact (hQ k).nonneg u⟩

/-- **The pointwise supremum of a nonempty family of quasi-copulas is a quasi-copula.** -/
protected theorem iSup {ι : Type*} [Nonempty ι] {Q : ι → (Fin d → I) → ℝ}
    (hQ : ∀ k, IsQuasiCopula (Q k)) : IsQuasiCopula (fun u => ⨆ k, Q k u) where
  normalized := by
    simp only [fun k => (hQ k).normalized, ciSup_const]
  grounded u i hi := by
    simp only [fun k => (hQ k).grounded u i hi, ciSup_const]
  marginal i t := by
    simp only [fun k => (hQ k).marginal i t, ciSup_const]
  monotone u v huv := ciSup_mono (bddAbove_range hQ v) fun k => (hQ k).monotone huv
  lipschitz u v := by
    have key : ∀ x y : Fin d → I,
        (⨆ k, Q k x) - (⨆ k, Q k y) ≤ ∑ i, |(x i : ℝ) - (y i : ℝ)| := by
      intro x y
      rw [sub_le_iff_le_add]
      apply ciSup_le
      intro k
      have h := (le_abs_self _).trans ((hQ k).lipschitz x y)
      have hk := le_ciSup (bddAbove_range hQ y) k
      linarith
    refine abs_le.mpr ⟨?_, key u v⟩
    have h := key v u
    simp only [abs_sub_comm (v _ : ℝ)] at h
    linarith

/-- **The pointwise infimum of a nonempty family of quasi-copulas is a quasi-copula.** -/
protected theorem iInf {ι : Type*} [Nonempty ι] {Q : ι → (Fin d → I) → ℝ}
    (hQ : ∀ k, IsQuasiCopula (Q k)) : IsQuasiCopula (fun u => ⨅ k, Q k u) where
  normalized := by
    simp only [fun k => (hQ k).normalized, ciInf_const]
  grounded u i hi := by
    simp only [fun k => (hQ k).grounded u i hi, ciInf_const]
  marginal i t := by
    simp only [fun k => (hQ k).marginal i t, ciInf_const]
  monotone u v huv := ciInf_mono (bddBelow_range hQ u) fun k => (hQ k).monotone huv
  lipschitz u v := by
    have key : ∀ x y : Fin d → I,
        (⨅ k, Q k y) - (⨅ k, Q k x) ≤ ∑ i, |(x i : ℝ) - (y i : ℝ)| := by
      intro x y
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
      apply le_ciInf
      intro k
      have h := (abs_le.mp ((hQ k).lipschitz x y)).1
      have hk := ciInf_le (bddBelow_range hQ y) k
      linarith
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h := key u v
      linarith
    · have h := key v u
      simp only [abs_sub_comm (v _ : ℝ)] at h
      linarith

/-- Quasi-copulas are closed under convex combinations. -/
theorem convexCombination {Q R : (Fin d → I) → ℝ} (hQ : IsQuasiCopula Q) (hR : IsQuasiCopula R)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsQuasiCopula (fun u => t * Q u + (1 - t) * R u) where
  normalized := by simp only [hQ.normalized, hR.normalized]; ring
  grounded u i hi := by simp only [hQ.grounded u i hi, hR.grounded u i hi]; ring
  marginal i s := by simp only [hQ.marginal i s, hR.marginal i s]; ring
  monotone u v huv := by
    have h1 := mul_le_mul_of_nonneg_left (hQ.monotone huv) ht0
    have h2 := mul_le_mul_of_nonneg_left (hR.monotone huv) (sub_nonneg.mpr ht1)
    exact add_le_add h1 h2
  lipschitz u v := by
    have hQl := hQ.lipschitz u v
    have hRl := hR.lipschitz u v
    calc
      |t * Q u + (1 - t) * R u - (t * Q v + (1 - t) * R v)|
          = |t * (Q u - Q v) + (1 - t) * (R u - R v)| := by ring_nf
      _ ≤ |t * (Q u - Q v)| + |(1 - t) * (R u - R v)| := abs_add_le _ _
      _ = t * |Q u - Q v| + (1 - t) * |R u - R v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
      _ ≤ t * ∑ i, |(u i : ℝ) - (v i : ℝ)| + (1 - t) * ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
        gcongr
      _ = ∑ i, |(u i : ℝ) - (v i : ℝ)| := by ring

end IsQuasiCopula

/-- The pointwise supremum of a nonempty family of copula CDFs is a quasi-copula. -/
theorem isQuasiCopula_iSup_cdf {ι : Type*} [Nonempty ι] (C : ι → Copula d) :
    IsQuasiCopula (fun u => ⨆ k, (C k).cdf u) :=
  IsQuasiCopula.iSup fun k => isQuasiCopula_cdf (C k)

/-- The pointwise infimum of a nonempty family of copula CDFs is a quasi-copula. -/
theorem isQuasiCopula_iInf_cdf {ι : Type*} [Nonempty ι] (C : ι → Copula d) :
    IsQuasiCopula (fun u => ⨅ k, (C k).cdf u) :=
  IsQuasiCopula.iInf fun k => isQuasiCopula_cdf (C k)

end ProbabilityTheory.Copula
