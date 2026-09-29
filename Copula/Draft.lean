/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.Ite
import Copula.Topology.Uniform
import Copula.Topology.Closed
import Copula.Diagonal.Construction
import Copula.Archimedean.TheoryConvex
import Copula.Archimedean.Theory
import Copula.Archimedean.Diagonal
import Copula.Families.NelsenTable.N9
import Copula.Families.NelsenTable.N10
import Copula.Families.NelsenTable.N13
import Copula.Families.NelsenTable.N19
import Copula.Families.NelsenTable.N20
import Copula.Measures.Deviation
import Copula.Measures.SchweizerWolff
import Copula.Measures.Hoeffding
import Copula.RandomVariable.Ext
import Copula.RandomVariable.Independence
import Copula.RandomVariable.Invariance
import Copula.RandomVariable.Monotone
import Copula.RandomVariable.Symmetry

/-!
# Draft modules (not yet compiled)

This aggregator collects modules written without access to a Lean toolchain.
It is deliberately *not* imported by `Copula.lean`, so `lake build` is
unaffected. Build it with `lake build Copula.Draft`; once every module here
compiles, move its imports into `Copula.lean` and delete this file.
-/
