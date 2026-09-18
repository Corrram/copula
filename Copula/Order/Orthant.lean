/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Order.Survival
import Copula.CDF.Extensionality

/-! # Lower orthant, upper orthant, and concordance orders

These predicates use the copula convention: smaller lower orthant probabilities
mean a smaller copula. No global `LE` instance selects one of the different orders.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Pointwise comparison of distribution functions. -/
def LowerOrthantLE (C D : Copula d) : Prop := ∀ u, C.cdf u ≤ D.cdf u

/-- Pointwise comparison of upper orthant probabilities. -/
def UpperOrthantLE (C D : Copula d) : Prop := ∀ u, C.survival u ≤ D.survival u

/-- Concordance compares both lower and upper orthants. -/
def ConcordanceLE (C D : Copula d) : Prop := C.LowerOrthantLE D ∧ C.UpperOrthantLE D

@[refl] theorem LowerOrthantLE.refl (C : Copula d) : C.LowerOrthantLE C := fun _ => le_rfl

@[trans] theorem LowerOrthantLE.trans {C D E : Copula d}
    (h : C.LowerOrthantLE D) (k : D.LowerOrthantLE E) : C.LowerOrthantLE E :=
  fun u => (h u).trans (k u)

theorem LowerOrthantLE.antisymm {C D : Copula d}
    (h : C.LowerOrthantLE D) (k : D.LowerOrthantLE C) : C = D :=
  ext_cdf (fun u => le_antisymm (h u) (k u))

@[refl] theorem UpperOrthantLE.refl (C : Copula d) : C.UpperOrthantLE C := fun _ => le_rfl

@[trans] theorem UpperOrthantLE.trans {C D E : Copula d}
    (h : C.UpperOrthantLE D) (k : D.UpperOrthantLE E) : C.UpperOrthantLE E :=
  fun u => (h u).trans (k u)

theorem upperOrthantLE_iff_reflect (C D : Copula d) :
    C.UpperOrthantLE D ↔ (C.reflect Finset.univ).LowerOrthantLE (D.reflect Finset.univ) := by
  constructor
  · intro h u
    simpa only [survival_eq_cdf_reflect, reflectPoint_reflectPoint] using
      h (reflectPoint Finset.univ u)
  · intro h u
    simpa only [survival_eq_cdf_reflect] using h (reflectPoint Finset.univ u)

theorem UpperOrthantLE.antisymm {C D : Copula d}
    (h : C.UpperOrthantLE D) (k : D.UpperOrthantLE C) : C = D :=
  reflect_injective Finset.univ (((upperOrthantLE_iff_reflect C D).1 h).antisymm
    ((upperOrthantLE_iff_reflect D C).1 k))

@[refl] theorem ConcordanceLE.refl (C : Copula d) : C.ConcordanceLE C :=
  ⟨LowerOrthantLE.refl C, UpperOrthantLE.refl C⟩

@[trans] theorem ConcordanceLE.trans {C D E : Copula d}
    (h : C.ConcordanceLE D) (k : D.ConcordanceLE E) : C.ConcordanceLE E :=
  ⟨h.1.trans k.1, h.2.trans k.2⟩

theorem ConcordanceLE.antisymm {C D : Copula d}
    (h : C.ConcordanceLE D) (k : D.ConcordanceLE C) : C = D := h.1.antisymm k.1

theorem concordanceLE_reflect_iff (C D : Copula d) :
    (C.reflect Finset.univ).ConcordanceLE (D.reflect Finset.univ) ↔ C.ConcordanceLE D := by
  simp only [ConcordanceLE, upperOrthantLE_iff_reflect, reflect_reflect]
  exact and_comm

/-- In dimension two the two orthant comparisons coincide. -/
theorem upperOrthantLE_iff_lowerOrthantLE (C D : Copula 2) :
    C.UpperOrthantLE D ↔ C.LowerOrthantLE D := by
  simp only [UpperOrthantLE, LowerOrthantLE, survival_two, add_le_add_iff_left]

theorem concordanceLE_iff_lowerOrthantLE (C D : Copula 2) :
    C.ConcordanceLE D ↔ C.LowerOrthantLE D := by
  simp [ConcordanceLE, upperOrthantLE_iff_lowerOrthantLE]

theorem LowerOrthantLE.mix {C D E F : Copula d} (h : C.LowerOrthantLE D)
    (k : E.LowerOrthantLE F) (a : I) : (C.mix E a).LowerOrthantLE (D.mix F a) := by
  intro u
  simp only [cdf_mix]
  exact add_le_add (mul_le_mul_of_nonneg_left (h u) a.property.1)
    (mul_le_mul_of_nonneg_left (k u) (sub_nonneg.mpr a.property.2))

/-- Increasing the weight of the larger copula increases the mixture. -/
theorem LowerOrthantLE.mix_weight {C D : Copula d} (h : C.LowerOrthantLE D)
    {a b : I} (hab : a ≤ b) : (D.mix C a).LowerOrthantLE (D.mix C b) := by
  intro u
  simp only [cdf_mix]
  have hp := mul_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))
    (sub_nonneg.mpr (h u))
  nlinarith

end ProbabilityTheory.Copula
