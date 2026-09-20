/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Tauto

/-! # Regular-vine structures by nested path attachment

A new variable is attached along a path through the existing vine's nested
coordinate clusters. Each new higher-tree edge shares an immediate parent
with its two endpoints: the proximity condition is built into the construction.
Always taking the left child gives a C-vine; always taking the right child gives
a D-vine. Mixed paths give other regular vines.
-/

namespace ProbabilityTheory.Copula.Vine

/-- A labelled ancestral representation of the top edge of a regular vine.
Repeated subtrees represent the same lower-tree cluster. -/
inductive Tree (d : ℕ) where
  | empty
  | leaf (i : Fin d)
  | join (a b : Fin d) (conditioning : Finset (Fin d)) (left right : Tree d)
  deriving DecidableEq

namespace Tree

variable {d : ℕ}

/-- Coordinates of a cluster. -/
def vars : Tree d → Finset (Fin d)
  | .empty => ∅
  | .leaf i => {i}
  | .join a b s _ _ => insert a (insert b s)

/-- An immediate parent in the preceding tree. -/
def Child (q : Tree d) : Tree d → Prop
  | .join _ _ _ l r => q = l ∨ q = r
  | _ => False

/-- The usual shared-parent proximity condition, with the first tree as base case. -/
def Proximity (l r : Tree d) (s : Finset (Fin d)) : Prop :=
  (∃ a b, l = .leaf a ∧ r = .leaf b ∧ s = ∅) ∨
    ∃ q, Child q l ∧ Child q r ∧ q.vars = s

/-- Well-formed recursive regular-vine clusters. -/
inductive Valid : Tree d → Prop
  | empty : Valid .empty
  | leaf (i : Fin d) : Valid (.leaf i)
  | join {a b : Fin d} {s : Finset (Fin d)} {l r : Tree d}
      (left : Valid l) (right : Valid r)
      (left_vars : l.vars = insert a s) (right_vars : r.vars = insert b s)
      (left_notMem : a ∉ s) (right_notMem : b ∉ s) (distinct : a ≠ b)
      (proximity : Proximity l r s) : Valid (.join a b s l r)

theorem valid_join_iff {a b : Fin d} {s : Finset (Fin d)} {l r : Tree d} :
    Valid (.join a b s l r) ↔ Valid l ∧ Valid r ∧
      l.vars = insert a s ∧ r.vars = insert b s ∧ a ∉ s ∧ b ∉ s ∧
      a ≠ b ∧ Proximity l r s := by
  constructor
  · intro h
    cases h with
    | join hl hr hls hrs ha hb hab hp => exact ⟨hl, hr, hls, hrs, ha, hb, hab, hp⟩
  · rintro ⟨hl, hr, hls, hrs, ha, hb, hab, hp⟩
    exact .join hl hr hls hrs ha hb hab hp

/-- Attach a fresh variable along a path (`false` = left, `true` = right).
Missing choices default to left; choices after reaching a leaf are unused. -/
def graft : Tree d → Fin d → List Bool → Tree d
  | .empty, a, _ => .leaf a
  | .leaf i, a, _ => .join i a ∅ (.leaf i) (.leaf a)
  | .join i j s l r, a, path =>
    if path.headD false then
      .join i a r.vars (.join i j s l r) (graft r a path.tail)
    else
      .join j a l.vars (.join i j s l r) (graft l a path.tail)

theorem vars_graft {t : Tree d} (ht : Valid t) (a : Fin d) (path : List Bool) :
    (t.graft a path).vars = insert a t.vars := by
  cases ht with
  | empty => rfl
  | leaf i =>
    change ({i, a} : Finset (Fin d)) = {a, i}
    ext k
    simp [or_comm]
  | @join i j s l r hl hr hls hrs hi hj hij hp =>
    cases h : path.headD false
    · simp only [graft, h, Bool.false_eq_true, ite_false]
      change insert j (insert a l.vars) = insert a (insert i (insert j s))
      rw [hls]
      ext k
      simp only [Finset.mem_insert]
      tauto
    · simp only [graft, h, ite_true]
      change insert i (insert a r.vars) = insert a (insert i (insert j s))
      rw [hrs]
      ext k
      simp only [Finset.mem_insert]
      tauto

theorem child_graft {t : Tree d} (ht : t ≠ .empty) (a : Fin d) (path : List Bool) :
    Child t (t.graft a path) := by
  cases t with
  | empty => exact False.elim (ht rfl)
  | leaf i => exact Or.inl rfl
  | join i j s l r =>
    simp only [graft]
    split <;> exact Or.inl rfl

private theorem ne_empty_of_vars_insert {t : Tree d} {i : Fin d} {s : Finset (Fin d)}
    (h : t.vars = insert i s) : t ≠ .empty := by
  intro ht
  have hm : i ∈ t.vars := by rw [h]; exact Finset.mem_insert_self _ _
  simp [ht, vars] at hm

/-- Path attachment preserves regularity and the proximity condition. -/
theorem Valid.graft {t : Tree d} (ht : Valid t) (a : Fin d) (ha : a ∉ t.vars)
    (path : List Bool) : Valid (t.graft a path) := by
  induction ht generalizing path with
  | empty => exact .leaf a
  | leaf i =>
    apply Valid.join (.leaf i) (.leaf a) rfl rfl (by simp) (by simp)
    · simpa [vars, eq_comm] using ha
    · exact Or.inl ⟨i, a, rfl, rfl, rfl⟩
  | @join i j s l r hl hr hls hrs hi hj hij hp ihl ihr =>
    have hal : a ∉ l.vars := by
      simp only [vars, Finset.mem_insert, not_or] at ha
      simp [hls, ha.1, ha.2.2]
    have har : a ∉ r.vars := by
      simp only [vars, Finset.mem_insert, not_or] at ha
      simp [hrs, ha.2.1, ha.2.2]
    have htop := Valid.join hl hr hls hrs hi hj hij hp
    cases h : path.headD false
    · simp only [Tree.graft, h, Bool.false_eq_true, ite_false]
      refine Valid.join htop (ihl hal path.tail) ?_ (vars_graft hl a path.tail) ?_ hal ?_ ?_
      · change insert i (insert j s) = insert j l.vars
        rw [hls, Finset.insert_comm]
      · simp [hls, hij.symm, hj]
      · simp only [vars, Finset.mem_insert, not_or] at ha
        exact Ne.symm ha.2.1
      · exact Or.inr ⟨l, Or.inl rfl, child_graft (ne_empty_of_vars_insert hls) a path.tail, rfl⟩
    · simp only [Tree.graft, h, ite_true]
      refine Valid.join htop (ihr har path.tail) ?_ (vars_graft hr a path.tail) ?_ har ?_ ?_
      · change insert i (insert j s) = insert i r.vars
        rw [hrs]
      · simp [hrs, hij, hi]
      · simp only [vars, Finset.mem_insert, not_or] at ha
        exact Ne.symm ha.1
      · exact Or.inr ⟨r, Or.inr rfl, child_graft (ne_empty_of_vars_insert hrs) a path.tail, rfl⟩

/-- Build a vine by adding a list of distinct variables from right to left. -/
def ofList (paths : Fin d → List Bool) : List (Fin d) → Tree d
  | [] => .empty
  | a :: xs => (ofList paths xs).graft a (paths a)

theorem valid_ofList (paths : Fin d → List Bool) (xs : List (Fin d)) :
    xs.Nodup → Valid (ofList paths xs) ∧ (ofList paths xs).vars = xs.toFinset := by
  induction xs with
  | nil => exact fun _ => ⟨.empty, rfl⟩
  | cons a xs ih =>
    intro h
    obtain ⟨ht, hv⟩ := ih h.of_cons
    refine ⟨ht.graft a ?_ (paths a), ?_⟩
    · simpa [hv] using (List.nodup_cons.mp h).1
    · simpa [ofList, hv] using vars_graft ht a (paths a)

/-- All labelled pair-copula edges; duplicate ancestral references are removed. -/
def edges : Tree d → Finset (Fin d × Fin d × Finset (Fin d))
  | .empty => ∅
  | .leaf _ => ∅
  | .join a b s l r => insert (a, b, s) (l.edges ∪ r.edges)

end Tree

end ProbabilityTheory.Copula.Vine

namespace ProbabilityTheory.Copula

/-- A regular-vine structure in path-attachment form. The list is an elimination
order: construction adds its variables from right to left. -/
structure RVineStructure (d : ℕ) where
  /-- Each coordinate occurs exactly once. -/
  eliminationOrder : List (Fin d)
  nodup : eliminationOrder.Nodup
  complete : eliminationOrder.toFinset = Finset.univ
  /-- Left/right choices for attaching a variable to the earlier clusters. -/
  paths : Fin d → List Bool

namespace RVineStructure

variable {d : ℕ}

/-- Specify the order in which variables are added, together with their attachment paths. -/
def ofOrder (order : Equiv.Perm (Fin d)) (paths : Fin d → List Bool) : RVineStructure d where
  eliminationOrder := (List.ofFn order).reverse
  nodup := List.nodup_reverse.mpr (List.nodup_ofFn.mpr order.injective)
  complete := by
    ext i
    simp only [List.toFinset_reverse, List.mem_toFinset, List.mem_ofFn, Finset.mem_univ, iff_true]
    exact order.surjective i
  paths := paths

/-- The C-vine with the given root order. -/
def cVine (order : Equiv.Perm (Fin d)) : RVineStructure d := ofOrder order (fun _ => [])

/-- The D-vine with the given chain order. -/
def dVine (order : Equiv.Perm (Fin d)) : RVineStructure d :=
  ofOrder order (fun _ => List.replicate d true)

/-- The labelled ancestral tree, including all conditioned and conditioning sets. -/
def toTree (S : RVineStructure d) : Vine.Tree d :=
  Vine.Tree.ofList S.paths S.eliminationOrder

/-- Every structure produced by the API satisfies the recursive proximity condition. -/
theorem valid (S : RVineStructure d) : S.toTree.Valid :=
  (Vine.Tree.valid_ofList S.paths S.eliminationOrder S.nodup).1

@[simp] theorem vars_toTree (S : RVineStructure d) : S.toTree.vars = Finset.univ :=
  (Vine.Tree.valid_ofList S.paths S.eliminationOrder S.nodup).2.trans S.complete

/-- The distinct pair-copula edges `(a, b, conditioningSet)`. -/
def edges (S : RVineStructure d) : Finset (Fin d × Fin d × Finset (Fin d)) := S.toTree.edges

/-- First-tree edges, with empty conditioning sets. -/
def firstTree (S : RVineStructure d) : Finset (Fin d × Fin d) :=
  (S.edges.filter (fun e => e.2.2 = ∅)).image (fun e => (e.1, e.2.1))

end RVineStructure

end ProbabilityTheory.Copula
