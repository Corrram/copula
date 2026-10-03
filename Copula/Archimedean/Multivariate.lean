/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.MultivariateMonotone
import Copula.Archimedean.Clayton
import Copula.Multivariate.Margins

/-!
# Multivariate Archimedean copulas

**McNeil–Nešlehová (2009), Theorem 2.2 ("if" part); Nelsen (2006), Theorem 4.6.2 and
Kimberling (1974).** Let `ψ` be a continuous, nonincreasing inverse generator on `[0, ∞)` with
`ψ(0) = 1`, generalized inverse `φ`, and let `ψ` be `d`-monotone on `(0, ∞)`. Then
`C(u) = ψ(φ(u₁) + ⋯ + φ(u_d))` (and `C(u) = 0` when some `uᵢ = 0`) is a `d`-copula.

The rectangle increment of `C` over a box with positive lower corner `a` and upper corner `b`
is the alternating corner sum of `ψ` at `x = ∑ φ(bᵢ)` with increments `hᵢ = φ(aᵢ) - φ(bᵢ) ≥ 0`
(`rectangleIncrement_cdf_eq_cornerSum`), which is nonnegative by `d`-monotonicity
(`IsMultiplyMonotone.cornerSum_nonneg_of_nonneg`); boxes touching the lower faces are handled
by an approximation from the inside (`rectangleIncrement_cdf_nonneg`). Completely monotone `ψ`
(Kimberling) are `d`-monotone for every `d`.

Main declarations:
* `MultivariateGenerator d`: a bivariate generator whose inverse generator is continuous on
  `[0, ∞)` and `d`-monotone; `MultivariateGenerator.copula` is the `d`-copula and
  `hasArchimedeanGenerator_copula` records its Archimedean form;
* for `d = 2` it agrees with the bivariate construction (`copula_two`), and all its margins have
  the same generator (`hasArchimedeanGenerator_reindex`);
* the positive-parameter Clayton family in every dimension is an instance, and the copula
  coincides with the gamma-frailty construction `clayton d θ hθ` (`claytonMultivariate_copula`).
-/

open Set Finset
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-- A generator of `d`-dimensional Archimedean copulas: a bivariate generator whose inverse
generator `ψ` is continuous on `[0, ∞)` and `d`-monotone on `(0, ∞)`. -/
structure MultivariateGenerator (d : ℕ) extends BivariateGenerator where
  /-- Continuity of the inverse generator on `[0, ∞)`. -/
  continuousOn : ContinuousOn toFun (Ici 0)
  /-- `d`-monotonicity of the inverse generator (McNeil–Nešlehová 2009, Definition 2.3). -/
  multiplyMonotone : IsMultiplyMonotone d toFun

namespace MultivariateGenerator

variable {d : ℕ} (g : MultivariateGenerator d)

/-- The `d`-dimensional Archimedean formula, with grounded boundary values. -/
noncomputable def cdf (u : Fin d → I) : ℝ := by
  classical
  exact if ∃ i, u i = 0 then 0 else g.toFun (∑ i, g.invFun (u i))

theorem cdf_of_exists_zero {u : Fin d → I} (h : ∃ i, u i = 0) : g.cdf u = 0 := by
  simp only [cdf, h, ↓reduceIte]

theorem cdf_of_forall_ne_zero {u : Fin d → I} (h : ∀ i, u i ≠ 0) :
    g.cdf u = g.toFun (∑ i, g.invFun (u i)) := by
  have : ¬ ∃ i, u i = 0 := fun ⟨i, hi⟩ => h i hi
  simp only [cdf, this, ↓reduceIte]

theorem toFun_zero : g.toFun 0 = 1 := by
  have h := g.right_inv 1 one_ne_zero
  rwa [g.inv_one, Set.Icc.coe_one] at h

private theorem sum_invFun_nonneg {u : Fin d → I} (h : ∀ i, u i ≠ 0) :
    0 ≤ ∑ i, g.invFun (u i) :=
  Finset.sum_nonneg fun i _ => g.inv_nonneg _ (h i)

theorem cdf_nonneg (u : Fin d → I) : 0 ≤ g.cdf u := by
  by_cases h : ∃ i, u i = 0
  · rw [g.cdf_of_exists_zero h]
  · push Not at h
    rw [g.cdf_of_forall_ne_zero h]
    exact g.nonneg _ (g.sum_invFun_nonneg h)

theorem cdf_le_coord (u : Fin d → I) (i : Fin d) : g.cdf u ≤ u i := by
  by_cases h : ∃ j, u j = 0
  · rw [g.cdf_of_exists_zero h]
    exact (u i).property.1
  · push Not at h
    rw [g.cdf_of_forall_ne_zero h]
    have hle : g.invFun (u i) ≤ ∑ j, g.invFun (u j) :=
      Finset.single_le_sum (fun j _ => g.inv_nonneg _ (h j)) (Finset.mem_univ i)
    calc
      g.toFun (∑ j, g.invFun (u j)) ≤ g.toFun (g.invFun (u i)) :=
        g.antitone (g.inv_nonneg _ (h i)) (g.sum_invFun_nonneg h) hle
      _ = u i := g.right_inv _ (h i)

/-- **Rectangle increments are corner sums of the inverse generator** for boxes whose lower
corner has positive coordinates. -/
theorem rectangleIncrement_cdf_eq_cornerSum {a b : Fin d → I} (ha : ∀ i, a i ≠ 0)
    (hab : a ≤ b) :
    rectangleIncrement g.cdf a b = cornerSum g.toFun (∑ i, g.invFun (b i))
      (fun i => g.invFun (a i) - g.invFun (b i)) Finset.univ := by
  have hb : ∀ i, b i ≠ 0 := fun i hbi =>
    ha i (le_antisymm ((hab i).trans_eq hbi) unitInterval.nonneg')
  rw [rectangleIncrement, partialIncrement, cornerSum]
  apply Finset.sum_congr rfl
  intro t _
  have hc : ∀ i, corner a b t i ≠ 0 := by
    intro i
    by_cases hi : i ∈ t
    · simpa [corner, hi] using ha i
    · simpa [corner, hi] using hb i
  rw [g.cdf_of_forall_ne_zero hc]
  congr 2
  have he : ∀ i, g.invFun (corner a b t i) =
      g.invFun (b i) + (if i ∈ t then g.invFun (a i) - g.invFun (b i) else 0) := by
    intro i
    by_cases hi : i ∈ t <;> simp [corner, hi]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]

/-- Rectangle increments of the Archimedean formula with positive lower corner are nonnegative. -/
private theorem rectangleIncrement_nonneg_of_pos {a b : Fin d → I} (ha : ∀ i, a i ≠ 0)
    (hab : a ≤ b) : 0 ≤ rectangleIncrement g.cdf a b := by
  classical
  have hb : ∀ i, b i ≠ 0 := fun i hbi =>
    ha i (le_antisymm ((hab i).trans_eq hbi) unitInterval.nonneg')
  rw [g.rectangleIncrement_cdf_eq_cornerSum ha hab]
  apply g.multiplyMonotone.cornerSum_nonneg_of_nonneg g.continuousOn
  · simp
  · exact Finset.sum_nonneg fun i _ => g.inv_nonneg _ (hb i)
  · intro i _
    exact sub_nonneg.mpr (g.inv_antitone _ _ (ha i) (hab i))

/-- **The Archimedean formula is `d`-increasing.** -/
theorem rectangleIncrement_cdf_nonneg (a b : Fin d → I) (hab : a ≤ b) :
    0 ≤ rectangleIncrement g.cdf a b := by
  classical
  by_cases hb0 : ∃ i, b i = 0
  · -- every corner has a zero coordinate
    obtain ⟨i, hi⟩ := hb0
    have hai : a i = 0 := le_antisymm ((hab i).trans_eq hi) unitInterval.nonneg'
    rw [rectangleIncrement, partialIncrement]
    apply le_of_eq
    symm
    apply Finset.sum_eq_zero
    intro t _
    rw [g.cdf_of_exists_zero ⟨i, by by_cases hit : i ∈ t <;> simp [corner, hit, hai, hi]⟩,
      mul_zero]
  push Not at hb0
  -- approximate the lower corner from the inside
  by_contra hneg
  push Not at hneg
  set D := rectangleIncrement g.cdf a b with hD
  set N : ℝ := ((Finset.univ : Finset (Fin d)).powerset.card : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact_mod_cast Finset.card_pos.mpr ⟨∅, Finset.empty_mem_powerset _⟩
  have hbpos : ∀ i, 0 < (b i : ℝ) := fun i =>
    lt_of_le_of_ne (b i).property.1 (fun h => hb0 i (Subtype.ext h.symm))
  -- a positive threshold below all `b i`
  obtain ⟨m, hm0, hm1, hmb⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ i, m ≤ (b i : ℝ) := by
    rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i₀⟩⟩
    · exact ⟨1, one_pos, le_rfl, fun i => (IsEmpty.false i).elim⟩
    · have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
      exact ⟨Finset.univ.inf' hne (fun i => (b i : ℝ)),
        (Finset.lt_inf'_iff hne).mpr fun i _ => hbpos i,
        (Finset.inf'_le _ (Finset.mem_univ i₀)).trans (b i₀).property.2, fun i =>
        Finset.inf'_le _ (Finset.mem_univ i)⟩
  set ε : ℝ := min m (-D / (2 * N)) with hε
  have hεpos : 0 < ε := lt_min hm0 (div_pos (by linarith) (by linarith))
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans hm1
  set e : I := ⟨ε, hεpos.le, hε1⟩
  set a' : Fin d → I := fun i => if a i = 0 then e else a i with ha'
  have ha'0 : ∀ i, a' i ≠ 0 := by
    intro i
    by_cases hi : a i = 0
    · simp only [ha', hi, ↓reduceIte]
      exact fun h => hεpos.ne' (congrArg Subtype.val h)
    · simp [ha', hi]
  have ha'b : a' ≤ b := by
    intro i
    by_cases hi : a i = 0
    · simp only [ha', hi, ↓reduceIte]
      exact (min_le_left _ _).trans (hmb i)
    · simpa [ha', hi] using hab i
  have hpos := g.rectangleIncrement_nonneg_of_pos ha'0 ha'b
  have hterm : ∀ t : Finset (Fin d),
      |g.cdf (corner a' b t) - g.cdf (corner a b t)| ≤ ε := by
    intro t
    by_cases hz : ∃ i ∈ t, a i = 0
    · obtain ⟨i, hit, hai⟩ := hz
      rw [g.cdf_of_exists_zero (u := corner a b t) ⟨i, by simp [corner, hit, hai]⟩, sub_zero,
        abs_of_nonneg (g.cdf_nonneg _)]
      calc
        g.cdf (corner a' b t) ≤ corner a' b t i := g.cdf_le_coord _ i
        _ = ε := by simp [corner, hit, ha', hai, e]
    · push Not at hz
      have hc : corner a' b t = corner a b t := by
        funext i
        by_cases hit : i ∈ t
        · simp [corner, hit, ha', hz i hit]
        · simp [corner, hit]
      rw [hc, sub_self, abs_zero]
      exact hεpos.le
  have hdiff : rectangleIncrement g.cdf a' b - D ≤ N * ε := by
    rw [hD, rectangleIncrement, rectangleIncrement, partialIncrement, partialIncrement,
      ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ t ∈ (Finset.univ : Finset (Fin d)).powerset, ε := by
        apply Finset.sum_le_sum
        intro t _
        rw [← mul_sub]
        calc
          (-1 : ℝ) ^ t.card * (g.cdf (corner a' b t) - g.cdf (corner a b t))
              ≤ |(-1 : ℝ) ^ t.card * (g.cdf (corner a' b t) - g.cdf (corner a b t))| :=
            le_abs_self _
          _ = |g.cdf (corner a' b t) - g.cdf (corner a b t)| := by
            rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
          _ ≤ ε := hterm t
      _ = N * ε := by rw [Finset.sum_const, nsmul_eq_mul]
  have hεD : N * ε ≤ -D / 2 := by
    have : ε ≤ -D / (2 * N) := min_le_right _ _
    calc
      N * ε ≤ N * (-D / (2 * N)) := mul_le_mul_of_nonneg_left this hNpos.le
      _ = -D / 2 := by field_simp
  linarith

theorem isClassical_cdf : IsClassical g.cdf where
  normalized := by
    rw [g.cdf_of_forall_ne_zero (fun _ => one_ne_zero)]
    simp [g.inv_one, g.toFun_zero]
  grounded u i hi := g.cdf_of_exists_zero ⟨i, hi⟩
  marginal i t := by
    by_cases ht : t = 0
    · rw [g.cdf_of_exists_zero ⟨i, by simp [ht]⟩, ht, Set.Icc.coe_zero]
    · have hne : ∀ j, Function.update (fun _ => (1 : I)) i t j ≠ 0 := by
        intro j
        by_cases hj : j = i
        · subst j; simpa using ht
        · simp [Function.update_of_ne hj]
      rw [g.cdf_of_forall_ne_zero hne]
      have hs : ∑ j, g.invFun (Function.update (fun _ => (1 : I)) i t j) = g.invFun t := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
        rw [Finset.sum_eq_zero (fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), g.inv_one]), add_zero]
      rw [hs, g.right_inv t ht]
  increasing a b hab := g.rectangleIncrement_cdf_nonneg a b hab

/-- **The `d`-dimensional Archimedean copula** generated by a `d`-monotone inverse generator. -/
noncomputable def copula : Copula d :=
  ofClassical g.cdf g.isClassical_cdf

@[simp]
theorem cdf_copula (u : Fin d → I) : g.copula.cdf u = g.cdf u :=
  congrFun (cdf_ofClassical _ _) u

theorem hasArchimedeanGenerator_copula :
    HasArchimedeanGenerator g.copula g.toBivariateGenerator := by
  intro u hu
  rw [cdf_copula, g.cdf_of_forall_ne_zero hu]

theorem isArchimedean_copula : IsArchimedean g.copula :=
  ⟨_, g.hasArchimedeanGenerator_copula⟩

/-- In dimension two the construction is the bivariate Archimedean copula. -/
theorem copula_two (g : MultivariateGenerator 2) :
    g.copula = g.toBivariateGenerator.copula := by
  apply ext_cdf
  intro u
  rw [cdf_copula, BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
  split_ifs with h
  · rcases h with h | h
    · exact g.cdf_of_exists_zero ⟨0, h⟩
    · exact g.cdf_of_exists_zero ⟨1, h⟩
  · push Not at h
    rw [g.cdf_of_forall_ne_zero (fun i => by fin_cases i; exacts [h.1, h.2]), Fin.sum_univ_two]

/-- **Margins of Archimedean copulas are Archimedean with the same generator.** -/
theorem hasArchimedeanGenerator_reindex {e : ℕ} {ρ : Fin e → Fin d}
    (hρ : Function.Injective ρ) :
    HasArchimedeanGenerator (g.copula.reindex ρ) g.toBivariateGenerator := by
  intro v hv
  classical
  rw [cdf_reindex, cdf_copula]
  have hm : ∀ i, marginPoint ρ v i ≠ 0 := by
    intro i
    by_cases hi : i ∈ Set.range ρ
    · obtain ⟨j, rfl⟩ := hi
      rw [marginPoint_apply_of_injective hρ]
      exact hv j
    · rw [marginPoint_apply_of_notMem_range ρ v hi]
      exact one_ne_zero
  rw [g.cdf_of_forall_ne_zero hm]
  congr 1
  symm
  apply Fintype.sum_of_injective ρ hρ
  · intro i hi
    rw [marginPoint_apply_of_notMem_range ρ v hi, g.inv_one]
  · intro j
    rw [marginPoint_apply_of_injective hρ]

end MultivariateGenerator

/-! ### Clayton copulas in every dimension -/

/-- Clayton's generator `(1 + t)^{-1/θ}` (`θ > 0`) is `d`-monotone for every `d`. -/
noncomputable def claytonMultivariateGenerator (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    MultivariateGenerator d where
  toBivariateGenerator := claytonGenerator θ hθ
  continuousOn := by
    intro t ht
    have h1 : (0 : ℝ) < 1 + t := by linarith [show (0 : ℝ) ≤ t from ht]
    exact ((continuous_const.add continuous_id).continuousAt.rpow_const
      (Or.inl h1.ne')).continuousWithinAt
  multiplyMonotone := by
    refine (isMultiplyMonotone_one_add_rpow_neg d (c := 1) (α := θ⁻¹) zero_le_one
      (inv_pos.mpr hθ)).congr fun t _ => ?_
    simp [claytonGenerator]

/-- **The analytic `d`-dimensional Clayton copula equals the gamma-frailty construction.** -/
theorem claytonMultivariate_copula (d : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    (claytonMultivariateGenerator d θ hθ).copula = clayton d θ hθ := by
  apply ext_cdf
  intro u
  by_cases h : ∃ i, u i = 0
  · obtain ⟨i, hi⟩ := h
    rw [MultivariateGenerator.cdf_copula,
      MultivariateGenerator.cdf_of_exists_zero _ ⟨i, hi⟩,
      cdf_eq_zero_of_coord_eq_zero _ u i hi]
  · push Not at h
    rw [MultivariateGenerator.cdf_copula, MultivariateGenerator.cdf_of_forall_ne_zero _ h,
      hasArchimedeanGenerator_clayton d θ hθ u h]
    rfl

end ProbabilityTheory.Copula
