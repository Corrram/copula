/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Mathlib.Tactic.NormNum

/-! # Conditionals on a disjunction

Small rewriting lemmas for `if p ∨ q then x else y`, stated for an arbitrary decidability
instance so that `rw` unifies with whatever instance the surrounding definition uses. -/

namespace ProbabilityTheory.Copula

theorem ite_or_of_not {α : Sort*} {p q : Prop} {inst : Decidable (p ∨ q)}
    (hp : ¬p) (hq : ¬q) (x y : α) : (@ite α (p ∨ q) inst x y) = y := by
  simp [hp, hq]

theorem ite_or_of_left {α : Sort*} {p q : Prop} {inst : Decidable (p ∨ q)}
    (hp : p) (x y : α) : (@ite α (p ∨ q) inst x y) = x := by
  simp [hp]

theorem ite_or_of_right {α : Sort*} {p q : Prop} {inst : Decidable (p ∨ q)}
    (hq : q) (x y : α) : (@ite α (p ∨ q) inst x y) = x := by
  simp [hq]

end ProbabilityTheory.Copula
