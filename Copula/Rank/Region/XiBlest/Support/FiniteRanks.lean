import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

namespace ProbabilityTheory.Copula.RankRegion.XiBlest.Support

/-- Sort distinct observations into a rank permutation. -/
noncomputable def finiteRanks {n : ℕ} {α : Type*} [LinearOrder α] (x : Fin n → α)
    (hx : Function.Injective x) : Equiv.Perm (Fin n) := by
  classical
  let e := Equiv.ofInjective x hx
  letI : Fintype (Set.range x) := Fintype.ofEquiv (Fin n) e
  have hcard : Fintype.card (Set.range x)=n := by rw [← Fintype.card_congr e,Fintype.card_fin]
  exact e.trans (Fintype.orderIsoFinOfCardEq (Set.range x) hcard).symm.toEquiv

theorem finiteRanks_le_iff {n : ℕ} {α : Type*} [LinearOrder α] (x : Fin n → α)
    (hx : Function.Injective x) (i j : Fin n) :
    finiteRanks x hx i ≤ finiteRanks x hx j ↔ x i ≤ x j := by
  classical
  unfold finiteRanks
  exact (OrderIso.le_iff_le _)

theorem rankPermutation_unique {n : ℕ} (r s : Equiv.Perm (Fin n))
    (h : ∀ i j, r i ≤ r j ↔ s i ≤ s j) : r=s := by
  let e : Fin n ≃o Fin n := {
    toEquiv := r.symm.trans s
    map_rel_iff' := by
      intro i j
      change s (r.symm i) ≤ s (r.symm j) ↔ i≤j
      simpa only [Equiv.apply_symm_apply] using (h (r.symm i) (r.symm j)).symm }
  have he : e=OrderIso.refl (Fin n) := Subsingleton.elim _ _
  apply Equiv.ext
  intro i
  have hh := congrArg (fun e : Fin n ≃o Fin n => e (r i)) he
  change s (r.symm (r i))=r i at hh
  simpa only [Equiv.symm_apply_apply] using hh.symm

theorem finiteRanks_comp_mono {n : ℕ} {α β : Type*} [LinearOrder α] [LinearOrder β]
    (x : Fin n → α) (f : α → β) (hf : Monotone f) (hx : Function.Injective x)
    (hfx : Function.Injective (fun i => f (x i))) : finiteRanks x hx=finiteRanks (fun i => f (x i)) hfx := by
  apply rankPermutation_unique
  intro i j
  rw [finiteRanks_le_iff,finiteRanks_le_iff]
  constructor
  · exact fun h => hf h
  · intro h
    by_contra hh
    have h' := hf (le_of_not_ge hh)
    have he := hfx (le_antisymm h h')
    subst j
    exact hh le_rfl

end ProbabilityTheory.Copula.RankRegion.XiBlest.Support
