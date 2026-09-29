/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.CDF.Continuity
import Copula.Classical.Regularity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Uniform convergence of copula distribution functions

Every copula CDF is `d`-Lipschitz for the maximum metric on the cube
(`Copula.lipschitzWith_cdf`). Hence any family of copula CDFs is uniformly
equicontinuous, and by the Arzelà–Ascoli theorem of mathlib, pointwise
convergence of copula CDFs along a filter is automatically uniform on the
compact cube. The starting point is Nelsen, *An Introduction to Copulas*, 2nd ed.,
Theorem 2.2.4 (the Lipschitz condition, §2.2).
-/

open Filter
open scoped unitInterval Topology BigOperators

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The Lipschitz estimate of a function satisfying the classical copula conditions,
stated with the real constant `d`. -/
theorem IsClassical.abs_sub_le_dim_mul_dist {F : (Fin d → I) → ℝ} (hF : IsClassical F)
    (u v : Fin d → I) : |F u - F v| ≤ (d : ℝ) * dist u v := by
  calc
    |F u - F v| ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := hF.abs_sub_le_sum_abs u v
    _ ≤ ∑ _ : Fin d, dist u v := Finset.sum_le_sum fun i _ => by
      simpa [Subtype.dist_eq, Real.dist_eq] using dist_le_pi_dist u v i
    _ = (d : ℝ) * dist u v := by simp

/-- The Lipschitz estimate of a copula CDF, stated with the real constant `d`. -/
theorem abs_cdf_sub_le_dim_mul_dist (C : Copula d) (u v : Fin d → I) :
    |C.cdf u - C.cdf v| ≤ (d : ℝ) * dist u v :=
  C.isClassical_cdf.abs_sub_le_dim_mul_dist u v

/-- Any family of functions satisfying the classical copula conditions is uniformly
equicontinuous on the cube. -/
theorem uniformEquicontinuous_of_isClassical {ι : Type*} {G : ι → (Fin d → I) → ℝ}
    (hG : ∀ n, IsClassical (G n)) : UniformEquicontinuous G := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  refine ⟨ε / ((d : ℝ) + 1), div_pos hε (by positivity), fun x y hxy n => ?_⟩
  have h := (hG n).abs_sub_le_dim_mul_dist x y
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (d : ℝ) * dist x y ≤ d * (ε / ((d : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left hxy.le hd
  have h2 : (d : ℝ) * (ε / ((d : ℝ) + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  linarith

/-- Any family of copula CDFs is uniformly equicontinuous on the cube
(consequence of Nelsen, Theorem 2.2.4). -/
theorem uniformEquicontinuous_cdf {ι : Type*} (C : ι → Copula d) :
    UniformEquicontinuous (fun n => (C n).cdf) :=
  uniformEquicontinuous_of_isClassical fun n => (C n).isClassical_cdf

/-- Any family of copula CDFs is equicontinuous on the cube. -/
theorem equicontinuous_cdf {ι : Type*} (C : ι → Copula d) :
    Equicontinuous (fun n => (C n).cdf) :=
  (uniformEquicontinuous_cdf C).equicontinuous

/-- Pointwise convergence of copula CDFs along a filter implies uniform convergence on the cube
(Nelsen, §2.2, via Theorem 2.2.4). -/
theorem tendstoUniformly_cdf_of_tendsto {ι : Type*} {l : Filter ι} (C : ι → Copula d)
    (D : Copula d) (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u))) :
    TendstoUniformly (fun n => (C n).cdf) D.cdf l := by
  have hpi : Tendsto (fun n => (C n).cdf) l (𝓝 D.cdf) := tendsto_pi_nhds.mpr h
  have h1 := ((equicontinuous_cdf C).tendsto_uniformFun_iff_pi l D.cdf).mpr hpi
  exact UniformFun.tendsto_iff_tendstoUniformly.mp h1

/-- Pointwise and uniform convergence of copula CDFs along a filter coincide. -/
theorem tendstoUniformly_cdf_iff {ι : Type*} {l : Filter ι} (C : ι → Copula d)
    (D : Copula d) :
    TendstoUniformly (fun n => (C n).cdf) D.cdf l ↔
      ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (D.cdf u)) :=
  ⟨fun h u => h.tendsto_at u, tendstoUniformly_cdf_of_tendsto C D⟩

/-- Sequence version: pointwise convergence of copula CDFs is uniform. -/
theorem tendstoUniformly_cdf_atTop {C : ℕ → Copula d} {D : Copula d}
    (h : ∀ u, Tendsto (fun n => (C n).cdf u) atTop (𝓝 (D.cdf u))) :
    TendstoUniformly (fun n => (C n).cdf) D.cdf atTop :=
  tendstoUniformly_cdf_of_tendsto C D h

end ProbabilityTheory.Copula
