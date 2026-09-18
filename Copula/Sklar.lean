/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Sklar.Continuous
import Copula.Sklar.General

/-! # Sklar's theorem

`exists_sklarCopula` gives existence for arbitrary real marginals.
`existsUnique_sklarCopula_of_continuous` gives full uniqueness for continuous marginals.
`IsSklarCopula.cdf_eq_on_ranges` gives uniqueness on marginal CDF ranges without continuity.
-/
