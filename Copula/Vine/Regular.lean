/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Vine.Gluing
import Copula.Vine.Structure

/-! # Regular-vine copula construction

Each path attachment preserves the entire previous copula. At every new edge
the supplied family couples the two conditional coordinate laws over their
shared marginal. Measurability is explicit; the family can depend on all of the
conditioning coordinates. Singular conditional laws are allowed.
-/

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula.Vine

variable {d : ℕ}

/-- A pair-copula family for each oriented pair and conditioning set.
Only the entries belonging to the chosen vine are used. Each family is evaluated
on the conditioning vector padded by zero outside its conditioning set. -/
abbrev PairFamilies (d : ℕ) :=
  Fin d → Fin d → Finset (Fin d) → Family (Fin d → I) 2

/-- A realization records the marginal law at every ancestral cluster and proves
that each cluster projects to its two immediate parents. -/
inductive Realization : (t : Tree d) → Marginal t.vars → Type
  | empty : Realization .empty Marginal.empty
  | leaf (i : Fin d) : Realization (.leaf i) (Marginal.singleton i)
  | join {a b : Fin d} {s : Finset (Fin d)} {l r : Tree d}
      {L : Marginal l.vars} {R : Marginal r.vars}
      (left : Realization l L) (right : Realization r R)
      (M : Marginal (insert a (insert b s)))
      (left_map : M.toMeasure.map (project l.vars) = L.toMeasure)
      (right_map : M.toMeasure.map (project r.vars) = R.toMeasure) :
      Realization (.join a b s l r) M

/-- The result of adding one variable: its law, its ancestral marginals, and
the proof that the previous law is preserved. -/
structure Extension {t : Tree d} (M : Marginal t.vars) (a : Fin d) (path : List Bool) where
  law : Marginal (t.graft a path).vars
  realization : Realization (t.graft a path) law
  marginal : law.toMeasure.map (project t.vars) = M.toMeasure

private def Extension.ofEq {t u : Tree d} {M : Marginal t.vars} {a : Fin d}
    {path : List Bool} (ht : t.graft a path = u) (N : Marginal u.vars)
    (hn : Realization u N) (hm : N.toMeasure.map (project t.vars) = M.toMeasure) :
    Extension M a path := by
  subst u
  exact ⟨N, hn, hm⟩

/-- Build a path attachment, using a conditional copula at each newly introduced edge. -/
noncomputable def Realization.graft {t : Tree d} {M : Marginal t.vars}
    (model : Realization t M) (ht : t.Valid) (a : Fin d) (ha : a ∉ t.vars)
    (path : List Bool) (families : PairFamilies d) : Extension M a path := by
  induction model generalizing a path with
  | empty =>
    exact ⟨Marginal.singleton a, .leaf a, (Marginal.singleton a).map_empty⟩
  | leaf i =>
    have hia : i ≠ a := by simpa [Tree.vars, eq_comm] using ha
    let h : Overlap (Marginal.singleton i) (Marginal.singleton a) Marginal.empty i a :=
      ⟨rfl, rfl, by simp, by simp, hia,
        (Marginal.singleton i).map_empty, (Marginal.singleton a).map_empty⟩
    let N := glue (Marginal.singleton i) (Marginal.singleton a) Marginal.empty
      i a (families i a ∅) h
    exact ⟨N, .join (.leaf i) (.leaf a) N
      (map_glue_project_left _ _ _ _ _ _ h) (map_glue_project_right _ _ _ _ _ _ h),
      map_glue_project_left _ _ _ _ _ _ h⟩
  | @join i j s l r L R ml mr C hCL hCR ihl ihr =>
    obtain ⟨hl, hr, hls, hrs, hi, hj, hij, _⟩ := Tree.valid_join_iff.mp ht
    have hal : a ∉ l.vars := by
      simp only [Tree.vars, Finset.mem_insert, not_or] at ha
      simp [hls, ha.1, ha.2.2]
    have har : a ∉ r.vars := by
      simp only [Tree.vars, Finset.mem_insert, not_or] at ha
      simp [hrs, ha.2.1, ha.2.2]
    cases hp : path.headD false
    · let E := ihl hl a hal path.tail
      have hleft : (Tree.join i j s l r).vars = insert j l.vars := by
        change insert i (insert j s) = insert j l.vars
        rw [hls, Finset.insert_comm]
      have hjl : j ∉ l.vars := by simp [hls, hij.symm, hj]
      have hja : j ≠ a := by
        simp only [Tree.vars, Finset.mem_insert, not_or] at ha
        exact Ne.symm ha.2.1
      let h : Overlap C E.law L j a :=
        ⟨hleft, Tree.vars_graft hl a path.tail, hjl, hal, hja, hCL, E.marginal⟩
      let N := glue C E.law L j a (families j a l.vars) h
      have hm : Realization (Tree.join i j s l r) C := .join ml mr C hCL hCR
      exact Extension.ofEq (u := .join j a l.vars (.join i j s l r) (l.graft a path.tail))
        (by simp only [Tree.graft, hp, Bool.false_eq_true, ite_false])
        N (.join hm E.realization N
        (map_glue_project_left _ _ _ _ _ _ h) (map_glue_project_right _ _ _ _ _ _ h))
        (map_glue_project_left _ _ _ _ _ _ h)
    · let E := ihr hr a har path.tail
      have hleft : (Tree.join i j s l r).vars = insert i r.vars := by
        change insert i (insert j s) = insert i r.vars
        rw [hrs]
      have hir : i ∉ r.vars := by simp [hrs, hij, hi]
      have hia : i ≠ a := by
        simp only [Tree.vars, Finset.mem_insert, not_or] at ha
        exact Ne.symm ha.1
      let h : Overlap C E.law R i a :=
        ⟨hleft, Tree.vars_graft hr a path.tail, hir, har, hia, hCR, E.marginal⟩
      let N := glue C E.law R i a (families i a r.vars) h
      have hm : Realization (Tree.join i j s l r) C := .join ml mr C hCL hCR
      exact Extension.ofEq (u := .join i a r.vars (.join i j s l r) (r.graft a path.tail))
        (by simp only [Tree.graft, hp, ite_true])
        N (.join hm E.realization N
        (map_glue_project_left _ _ _ _ _ _ h) (map_glue_project_right _ _ _ _ _ _ h))
        (map_glue_project_left _ _ _ _ _ _ h)

/-- A law together with its ancestral marginal identities. -/
structure Model (t : Tree d) where
  law : Marginal t.vars
  realization : Realization t law

/-- Construct the probability laws for an ordered list of distinct variables. -/
noncomputable def modelOfList (paths : Fin d → List Bool) (families : PairFamilies d) :
    (xs : List (Fin d)) → xs.Nodup → Model (Tree.ofList paths xs)
  | [], _ => ⟨Marginal.empty, .empty⟩
  | a :: xs, h => by
    let M := modelOfList paths families xs h.of_cons
    have ht := (Tree.valid_ofList paths xs h.of_cons).1
    have ha : a ∉ (Tree.ofList paths xs).vars := by
      rw [(Tree.valid_ofList paths xs h.of_cons).2]
      simpa using (List.nodup_cons.mp h).1
    let E := M.realization.graft ht a ha (paths a) families
    exact ⟨E.law, E.realization⟩

/-- Adding a variable preserves the complete joint law of all previously added variables. -/
theorem modelOfList_cons_marginal (paths : Fin d → List Bool) (families : PairFamilies d)
    (a : Fin d) (xs : List (Fin d)) (h : (a :: xs).Nodup) :
    (modelOfList paths families (a :: xs) h).law.toMeasure.map
        (project (Tree.ofList paths xs).vars) =
      (modelOfList paths families xs h.of_cons).law.toMeasure := by
  exact ((modelOfList paths families xs h.of_cons).realization.graft
    (Tree.valid_ofList paths xs h.of_cons).1 a
    (by simpa [(Tree.valid_ofList paths xs h.of_cons).2] using (List.nodup_cons.mp h).1)
    (paths a) families).marginal

end ProbabilityTheory.Copula.Vine

namespace ProbabilityTheory.Copula

namespace RVineStructure

variable {d : ℕ}

/-- The compatible probability law at every ancestral node of this vine. -/
noncomputable def model (S : RVineStructure d) (families : Vine.PairFamilies d) :
    Vine.Model S.toTree :=
  Vine.modelOfList S.paths families S.eliminationOrder S.nodup

/-- Construct a regular-vine copula from measurable, possibly conditioning-dependent
pair-copula families. Uniform marginals follow from conditional gluing. -/
noncomputable def toCopula (S : RVineStructure d) (families : Vine.PairFamilies d) : Copula d :=
  ((S.model families).law.cast S.vars_toTree).toCopula

/-- The full copula law is the law at the top of the vine. -/
theorem toMeasure_toCopula (S : RVineStructure d) (families : Vine.PairFamilies d) :
    (S.toCopula families).toMeasure = (S.model families).law.toMeasure :=
  Vine.Marginal.toMeasure_cast _ _

/-- A simplified regular vine, with a fixed copula at each edge. -/
noncomputable def simplified (S : RVineStructure d)
    (pairs : Fin d → Fin d → Finset (Fin d) → Copula 2) : Copula d :=
  S.toCopula (fun a b s => Family.const (pairs a b s))

end RVineStructure

/-- A possibly non-simplified C-vine with a prescribed variable order. -/
noncomputable def cVine {d : ℕ} (order : Equiv.Perm (Fin d))
    (families : Vine.PairFamilies d) : Copula d := (RVineStructure.cVine order).toCopula families

/-- A possibly non-simplified D-vine with a prescribed variable order. -/
noncomputable def dVine {d : ℕ} (order : Equiv.Perm (Fin d))
    (families : Vine.PairFamilies d) : Copula d := (RVineStructure.dVine order).toCopula families

end ProbabilityTheory.Copula
