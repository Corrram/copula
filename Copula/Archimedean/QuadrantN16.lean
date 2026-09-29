/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Archimedean.QuadrantTails
import Copula.Families.NelsenTable.N16

/-! # Quadrant dependence of Nelsen's family 16

The generator is `φ(u) = (θ/u + 1)(1 - u)`, and for `u, v ∈ (0, 1]`
`φ(uv) - φ(u) - φ(v) = (1 - u)(1 - v)(θ - uv) / (uv)`.
Hence for `θ ≥ 1` the copula is PQD, whereas for `θ < 1` the diagonal point `u = v = (1 + θ)/2`
violates PQD. The copula is never NQD for `θ > 0` (`λ_L = 1/2`), and `θ = 0` is `W`.
So the classification is: PQD iff `θ ≥ 1`, NQD iff `θ = 0`; for `0 < θ < 1` it is neither.
-/

open Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

private theorem n16_invFunReal (θ : ℝ) (hθ : 0 ≤ θ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (nelsen16Generator θ hθ).invFunReal x = (θ / x + 1) * (1 - x) :=
  (nelsen16Generator θ hθ).invFunReal_of_pos hx0 hx1

private theorem n16_diff (θ : ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (θ / (u * v) + 1) * (1 - u * v) - ((θ / u + 1) * (1 - u) + (θ / v + 1) * (1 - v)) =
      (1 - u) * (1 - v) * (θ - u * v) / (u * v) := by
  field_simp
  ring

/-- Nelsen's family 16 is PQD for `θ ≥ 1`. -/
theorem isPQD_nelsen16 (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen16 θ (by linarith)).IsPQD := by
  refine BivariateGenerator.isPQD_of_phi _ fun u v hu0 hu1 hv0 hv1 => ?_
  have huv0 : 0 < u * v := mul_pos hu0 hv0
  have huv1 : u * v ≤ 1 := by nlinarith
  rw [n16_invFunReal θ (by linarith) hu0 hu1, n16_invFunReal θ (by linarith) hv0 hv1,
    n16_invFunReal θ (by linarith) huv0 huv1]
  have := n16_diff θ hu0 hv0
  have hnn : 0 ≤ (1 - u) * (1 - v) * (θ - u * v) / (u * v) := by
    apply div_nonneg _ huv0.le
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

/-- Nelsen's family 16 is not PQD for `0 ≤ θ < 1`. -/
theorem not_isPQD_nelsen16 (θ : ℝ) (hθ : 0 ≤ θ) (h1 : θ < 1) : ¬ (nelsen16 θ hθ).IsPQD := by
  have ht0 : 0 < (1 + θ) / 2 := by linarith
  have ht1 : (1 + θ) / 2 ≤ 1 := by linarith
  refine BivariateGenerator.not_isPQD_of_phi _ ht0 ht1 ht0 ht1 ?_
  set t := (1 + θ) / 2 with ht
  have htt : 0 < t * t := mul_pos ht0 ht0
  have htt1 : t * t ≤ 1 := by nlinarith
  rw [n16_invFunReal θ hθ ht0 ht1, n16_invFunReal θ hθ htt htt1]
  have h := n16_diff θ ht0 ht0
  have hneg : (1 - t) * (1 - t) * (θ - t * t) / (t * t) < 0 := by
    apply div_neg_of_neg_of_pos _ htt
    have h1t : 0 < 1 - t := by rw [ht]; linarith
    have : θ - t * t < 0 := by rw [ht]; nlinarith
    exact mul_neg_of_pos_of_neg (mul_pos h1t h1t) this
  linarith

/-- Nelsen's family 16 is PQD iff `θ ≥ 1`. -/
theorem isPQD_nelsen16_iff (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen16 θ hθ).IsPQD ↔ 1 ≤ θ := by
  constructor
  · intro h
    by_contra hc
    exact not_isPQD_nelsen16 θ hθ (not_le.mp hc) h
  · exact fun h => isPQD_nelsen16 θ h

/-- Nelsen's family 16 is NQD iff `θ = 0` (the lower Fréchet bound `W`). -/
theorem isNQD_nelsen16_iff (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen16 θ hθ).IsNQD ↔ θ = 0 := by
  constructor
  · intro h
    by_contra hc
    exact not_isNQD_nelsen16 θ (lt_of_le_of_ne hθ (Ne.symm hc)) h
  · rintro rfl
    rw [nelsen16_zero]
    exact isNQD_countermonotonic

end ProbabilityTheory.Copula
