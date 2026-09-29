/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantFrank
import Copula.Archimedean.QuadrantJoe
import Copula.Archimedean.QuadrantTails
import Copula.Archimedean.QuadrantNelsenB
import Copula.Archimedean.QuadrantNelsenC
import Copula.Archimedean.QuadrantN16
import Copula.Archimedean.QuadrantN17
import Copula.Dependence.ClaytonClassification
import Copula.Dependence.Clayton
import Copula.Dependence.AMH

/-! # PQD/NQD classification of the one-parameter Archimedean families

One theorem per family of Nelsen, *An Introduction to Copulas*, Table 4.1 (numbers `#1`–`#22`),
and for Gumbel's, Frank's, Joe's and the Ali–Mikhail–Haq family, stating positive and negative
quadrant dependence on the full parameter range. Independence (`Π`) is both PQD and NQD; every
other family below is at most one of the two. Notation: `PQD` is `Copula.IsPQD`, `NQD` is
`Copula.IsNQD`.

| # | family | range | PQD | NQD |
| --- | --- | --- | --- | --- |
| 1 | Clayton | `θ > 0` | yes | no |
| 1 | Clayton | `-1 ≤ θ < 0` | no | yes |
| 2 | | `θ ≥ 1` | no | iff `θ = 1` (`W`) |
| 3 / AMH | | `-1 ≤ θ ≤ 1` | iff `θ ≥ 0` | iff `θ ≤ 0` |
| 4 / Gumbel | | `θ ≥ 1` | yes | iff `θ = 1` (`Π`) |
| 5 / Frank | | `θ > 0` | yes | no |
| 5 / Frank | | `θ < 0` | no | yes |
| 6 / Joe | | `θ ≥ 1` | yes | iff `θ = 1` (`Π`) |
| 7 | | `0 ≤ θ ≤ 1` | iff `θ = 1` | yes |
| 8 | | `θ ≥ 1` | no | iff `θ ≤ 2` |
| 9, 10, 11 | | whole range | no | yes |
| 12, 14 | | `θ ≥ 1` | yes | no |
| 13 | | `θ > 0` | iff `θ ≥ 1` | iff `θ ≤ 1` |
| 15 | | `θ ≥ 1` | no | iff `θ = 1` (`W`) |
| 16 | | `θ ≥ 0` | iff `θ ≥ 1` | iff `θ = 0` (`W`) |
| 17 | | `θ ≠ 0` | iff `θ ≥ -1` | iff `θ ≤ -1` |
| 18 | | `θ ≥ 2` | no | no |
| 19, 20 | | `θ > 0` | yes | no |
| 21 | | `θ ≥ 1` | no | iff `θ = 1` (`W`) |
| 22 | | `0 < θ ≤ 1` | no | yes |

Families 2, 8, 15, 16 (`0 < θ < 1`), 18, 21 (`θ > 1`) are neither PQD nor NQD on the indicated
ranges: 2, 15, 21 (`θ > 1`), 18 have positive upper tail dependence, 16 lower tail dependence, 8
(`θ > 2`) exceeds `Π` at `u = v = θ / (2 (θ - 1))`.
-/

open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- #1 Clayton, `θ > 0`: PQD and not NQD. -/
theorem clayton_quadrant_pos (θ : ℝ) (hθ : 0 < θ) :
    (clayton 2 θ hθ).IsPQD ∧ ¬ (clayton 2 θ hθ).IsNQD :=
  ⟨isPQD_clayton_positive θ hθ, not_isNQD_clayton_positive θ hθ⟩

/-- #1 Clayton, `-1 ≤ θ < 0`: NQD and not PQD. -/
theorem clayton_quadrant_neg (θ : ℝ) (hθ : -1 ≤ θ) (hn : θ < 0) :
    (claytonNegative θ hθ hn).IsNQD ∧ ¬ (claytonNegative θ hθ hn).IsPQD :=
  ⟨isNQD_clayton_negative θ hθ hn, not_isPQD_clayton_negative θ hθ hn⟩

/-- #2: never PQD; NQD iff `θ = 1`. -/
theorem nelsen2_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (nelsen2 θ hθ).IsPQD ∧ ((nelsen2 θ hθ).IsNQD ↔ θ = 1) :=
  ⟨not_isPQD_nelsen2 θ hθ, isNQD_nelsen2_iff θ hθ⟩

/-- #3 (Ali–Mikhail–Haq): PQD iff `θ ≥ 0`, NQD iff `θ ≤ 0`. -/
theorem amh_quadrant (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    ((amh θ hmin hmax).IsPQD ↔ 0 ≤ θ) ∧ ((amh θ hmin hmax).IsNQD ↔ θ ≤ 0) :=
  ⟨isPQD_amh_iff θ hmin hmax, isNQD_amh_iff θ hmin hmax⟩

/-- #4 (Gumbel): always PQD; NQD iff `θ = 1`. -/
theorem gumbel_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    (gumbel θ hθ).IsPQD ∧ ((gumbel θ hθ).IsNQD ↔ θ = 1) :=
  ⟨isPQD_gumbel θ hθ, isNQD_gumbel_iff θ hθ⟩

/-- #5 (Frank), `θ > 0`: PQD and not NQD. -/
theorem frank_quadrant_pos (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).IsPQD ∧ ¬ (frank θ hθ).IsNQD :=
  ⟨isPQD_frank θ hθ, not_isNQD_frank θ hθ⟩

/-- #5 (Frank), `θ < 0`: NQD and not PQD. -/
theorem frank_quadrant_neg (θ : ℝ) (hθ : θ < 0) :
    (frankNegative θ hθ).IsNQD ∧ ¬ (frankNegative θ hθ).IsPQD :=
  ⟨isNQD_frankNegative θ hθ, not_isPQD_frankNegative θ hθ⟩

/-- #6 (Joe): always PQD; NQD iff `θ = 1`. -/
theorem joe_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    (joe θ hθ).IsPQD ∧ ((joe θ hθ).IsNQD ↔ θ = 1) :=
  ⟨isPQD_joe θ hθ, isNQD_joe_iff θ hθ⟩

/-- #7: always NQD; PQD iff `θ = 1`. -/
theorem nelsen7_quadrant (θ : I) : ((nelsen7 θ).IsPQD ↔ θ = 1) ∧ (nelsen7 θ).IsNQD :=
  ⟨isPQD_nelsen7_iff θ, isNQD_nelsen7 θ⟩

/-- #8: never PQD; NQD iff `θ ≤ 2`. -/
theorem nelsen8_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (nelsen8 θ hθ).IsPQD ∧ ((nelsen8 θ hθ).IsNQD ↔ θ ≤ 2) :=
  ⟨not_isPQD_nelsen8 θ hθ, isNQD_nelsen8_iff θ hθ⟩

/-- #9: NQD and not PQD. -/
theorem nelsen9_quadrant (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen9 θ hθ h1).IsNQD ∧ ¬ (nelsen9 θ hθ h1).IsPQD :=
  ⟨isNQD_nelsen9 θ hθ h1, not_isPQD_nelsen9 θ hθ h1⟩

/-- #10: NQD and not PQD. -/
theorem nelsen10_quadrant (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen10 θ hθ h1).IsNQD ∧ ¬ (nelsen10 θ hθ h1).IsPQD :=
  ⟨isNQD_nelsen10 θ hθ h1, not_isPQD_nelsen10 θ hθ h1⟩

/-- #11: NQD and not PQD. -/
theorem nelsen11_quadrant (θ : ℝ) (hθ : 0 < θ) (h2 : θ ≤ 1 / 2) :
    (nelsen11 θ hθ h2).IsNQD ∧ ¬ (nelsen11 θ hθ h2).IsPQD :=
  ⟨isNQD_nelsen11 θ hθ h2, not_isPQD_nelsen11 θ hθ h2⟩

/-- #12: PQD and not NQD. -/
theorem nelsen12_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen12 θ hθ).IsPQD ∧ ¬ (nelsen12 θ hθ).IsNQD :=
  ⟨isPQD_nelsen12 θ hθ, not_isNQD_nelsen12 θ hθ⟩

/-- #13: PQD iff `θ ≥ 1`, NQD iff `θ ≤ 1`. -/
theorem nelsen13_quadrant (θ : ℝ) (hθ : 0 < θ) :
    ((nelsen13 θ hθ).IsPQD ↔ 1 ≤ θ) ∧ ((nelsen13 θ hθ).IsNQD ↔ θ ≤ 1) :=
  ⟨isPQD_nelsen13_iff θ hθ, isNQD_nelsen13_iff θ hθ⟩

/-- #14: PQD and not NQD. -/
theorem nelsen14_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen14 θ hθ).IsPQD ∧ ¬ (nelsen14 θ hθ).IsNQD :=
  ⟨isPQD_nelsen14 θ hθ, not_isNQD_nelsen14 θ hθ⟩

/-- #15 (Genest–Ghoudi): never PQD; NQD iff `θ = 1`. -/
theorem nelsen15_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (genestGhoudi θ hθ).IsPQD ∧ ((genestGhoudi θ hθ).IsNQD ↔ θ = 1) :=
  ⟨not_isPQD_genestGhoudi θ hθ, isNQD_genestGhoudi_iff θ hθ⟩

/-- #16: PQD iff `θ ≥ 1`, NQD iff `θ = 0`. -/
theorem nelsen16_quadrant (θ : ℝ) (hθ : 0 ≤ θ) :
    ((nelsen16 θ hθ).IsPQD ↔ 1 ≤ θ) ∧ ((nelsen16 θ hθ).IsNQD ↔ θ = 0) :=
  ⟨isPQD_nelsen16_iff θ hθ, isNQD_nelsen16_iff θ hθ⟩

/-- #17: PQD iff `θ ≥ -1`, NQD iff `θ ≤ -1`. -/
theorem nelsen17_quadrant (θ : ℝ) (hθ : θ ≠ 0) :
    ((nelsen17 θ hθ).IsPQD ↔ -1 ≤ θ) ∧ ((nelsen17 θ hθ).IsNQD ↔ θ ≤ -1) :=
  ⟨isPQD_nelsen17_iff θ hθ, isNQD_nelsen17_iff θ hθ⟩

/-- #18: neither PQD nor NQD. -/
theorem nelsen18_quadrant (θ : ℝ) (hθ : 2 ≤ θ) :
    ¬ (nelsen18 θ hθ).IsPQD ∧ ¬ (nelsen18 θ hθ).IsNQD :=
  ⟨not_isPQD_nelsen18 θ hθ, not_isNQD_nelsen18 θ hθ⟩

/-- #19: PQD and not NQD. -/
theorem nelsen19_quadrant (θ : ℝ) (hθ : 0 < θ) :
    (nelsen19 θ hθ).IsPQD ∧ ¬ (nelsen19 θ hθ).IsNQD :=
  ⟨isPQD_nelsen19 θ hθ, not_isNQD_nelsen19 θ hθ⟩

/-- #20: PQD and not NQD. -/
theorem nelsen20_quadrant (θ : ℝ) (hθ : 0 < θ) :
    (nelsen20 θ hθ).IsPQD ∧ ¬ (nelsen20 θ hθ).IsNQD :=
  ⟨isPQD_nelsen20 θ hθ, not_isNQD_nelsen20 θ hθ⟩

/-- #21: never PQD; NQD iff `θ = 1`. -/
theorem nelsen21_quadrant (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (nelsen21 θ hθ).IsPQD ∧ ((nelsen21 θ hθ).IsNQD ↔ θ = 1) :=
  ⟨not_isPQD_nelsen21 θ hθ, isNQD_nelsen21_iff θ hθ⟩

/-- #22: NQD and not PQD. -/
theorem nelsen22_quadrant (θ : ℝ) (hθ : 0 < θ) (h1 : θ ≤ 1) :
    (nelsen22 θ hθ h1).IsNQD ∧ ¬ (nelsen22 θ hθ h1).IsPQD :=
  ⟨isNQD_nelsen22 θ hθ h1, not_isPQD_nelsen22 θ hθ h1⟩

end ProbabilityTheory.Copula
