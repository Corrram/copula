/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Families.Plackett.Basic
import Copula.Families.Plackett.Order
import Copula.Families.Plackett.Spearman
import Copula.Families.Plackett.Tail
import Copula.Families.Plackett.Kendall
import Copula.Families.Plackett.KendallOrder
import Copula.Families.Plackett.KendallArctan

/-! # The Plackett family

Aggregator: construction, cross-product ratio, symmetry and Blomqvist's beta (`Basic`),
concordance ordering and Fréchet–Hoeffding limits (`Order`), Spearman's rho (`Spearman`),
tail independence `λ_L = λ_U = 0` (`Tail`), Kendall's tau as a double integral of the partial
derivatives and of a rational function (`Kendall`) and as a one-dimensional arctangent integral
(`KendallArctan`), full support and strict monotonicity, sign and limits of tau and rho
(`KendallOrder`).
-/
