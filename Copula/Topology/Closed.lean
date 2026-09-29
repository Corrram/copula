/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
import Copula.Topology.Uniform
import Copula.Classical.Characterization
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

/-!
# Closedness and compactness of the set of copulas

A pointwise limit of functions satisfying the classical copula conditions again
satisfies them, since every condition is a closed condition for pointwise
convergence. By the classical characterization (`Copula.ofClassical`) such a
limit is the CDF of a copula, and by `Copula.Topology.Uniform` the convergence is
uniform. Combining this with the Arzelà–Ascoli theorem, the set of copula CDFs is
a compact subset of the bounded continuous functions on the cube, so every
sequence of copulas has a uniformly convergent subsequence
(Nelsen, *An Introduction to Copulas*, 2nd ed., §2.2 and the discussion of
convergence of copulas following Theorem 2.2.4).
-/

open Filter Set
open scoped unitInterval Topology BoundedContinuousFunction

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- A pointwise limit of functions satisfying the classical copula conditions
satisfies them. -/
theorem IsClassical.of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {G : ι → (Fin d → I) → ℝ} {F : (Fin d → I) → ℝ} (hG : ∀ n, IsClassical (G n))
    (h : ∀ u, Tendsto (fun n => G n u) l (𝓝 (F u))) : IsClassical F where
  normalized :=
    tendsto_nhds_unique (h _)
      (Tendsto.congr (fun n => ((hG n).normalized).symm) tendsto_const_nhds)
  grounded u i hi :=
    tendsto_nhds_unique (h u)
      (Tendsto.congr (fun n => ((hG n).grounded u i hi).symm) tendsto_const_nhds)
  marginal i t :=
    tendsto_nhds_unique (h _)
      (Tendsto.congr (fun n => ((hG n).marginal i t).symm) tendsto_const_nhds)
  increasing a b hab := by
    have ht : Tendsto (fun n => rectangleIncrement (G n) a b) l
        (𝓝 (rectangleIncrement F a b)) := by
      unfold rectangleIncrement partialIncrement
      exact tendsto_finsetSum _ (fun t _ => (h (corner a b t)).const_mul _)
    exact ge_of_tendsto' ht (fun n => (hG n).increasing a b hab)

/-- A pointwise limit of copula CDFs satisfies the classical copula conditions. -/
theorem isClassical_of_tendsto_cdf {ι : Type*} {l : Filter ι} [NeBot l] (C : ι → Copula d)
    {F : (Fin d → I) → ℝ} (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (F u))) :
    IsClassical F :=
  IsClassical.of_tendsto (fun n => (C n).isClassical_cdf) h

/-- A pointwise limit of copula CDFs is the CDF of a copula, and the convergence is uniform. -/
theorem exists_copula_tendstoUniformly_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    (C : ι → Copula d) {F : (Fin d → I) → ℝ}
    (h : ∀ u, Tendsto (fun n => (C n).cdf u) l (𝓝 (F u))) :
    ∃ D : Copula d, D.cdf = F ∧ TendstoUniformly (fun n => (C n).cdf) D.cdf l := by
  have hF : IsClassical F := isClassical_of_tendsto_cdf C h
  refine ⟨ofClassical F hF, cdf_ofClassical F hF, ?_⟩
  apply tendstoUniformly_cdf_of_tendsto
  intro u
  rw [cdf_ofClassical F hF]
  exact h u

/-- The bounded continuous function on the cube given by a copula CDF. -/
noncomputable def cdfBCF (C : Copula d) : (Fin d → I) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨C.cdf, C.continuous_cdf⟩

@[simp]
theorem coe_cdfBCF (C : Copula d) : ⇑(cdfBCF C) = C.cdf := rfl

/-- The set of bounded continuous functions on the cube satisfying the classical copula
conditions. -/
def classicalSet (d : ℕ) : Set ((Fin d → I) →ᵇ ℝ) :=
  {f | IsClassical ⇑f}

/-- The set of functions satisfying the classical conditions is closed for uniform
convergence. -/
theorem isClosed_classicalSet : IsClosed (classicalSet d) := by
  apply IsSeqClosed.isClosed
  intro x p hx hp
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hp
  have hx' : ∀ n, IsClassical ⇑(x n) := fun n => hx n
  show IsClassical ⇑p
  exact IsClassical.of_tendsto (G := fun n => ⇑(x n)) (l := atTop) hx'
    (fun u => hu.tendsto_at u)

/-- Functions satisfying the classical conditions take values in `[0, 1]`. -/
theorem IsClassical.mem_Icc {F : (Fin d → I) → ℝ} (hF : IsClassical F) (u : Fin d → I) :
    F u ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · rw [← hF.rectangleIncrement_zero_lower u]
    exact hF.increasing _ _ (fun i => unitInterval.nonneg')
  · have h := hF.monotone
      (show u ≤ fun _ => (1 : I) from fun i => unitInterval.le_one' (t := u i))
    rw [hF.normalized] at h
    exact h

/-- Arzelà–Ascoli: the set of copula CDFs in `C(I^d, ℝ)` is compact for the uniform metric. -/
theorem isCompact_classicalSet : IsCompact (classicalSet d) := by
  refine BoundedContinuousFunction.arzela_ascoli₂ (Icc (0 : ℝ) 1) isCompact_Icc _
    isClosed_classicalSet (fun f x hf => (show IsClassical ⇑f from hf).mem_Icc x) ?_
  exact (uniformEquicontinuous_of_isClassical
    (G := fun f : classicalSet d => ⇑(f : (Fin d → I) →ᵇ ℝ)) (fun f => f.2)).equicontinuous

/-- Every sequence of copulas has a subsequence whose CDFs converge uniformly on the cube to
the CDF of a copula (compactness of the set of copulas, Nelsen §2.2). -/
theorem exists_subseq_tendstoUniformly_cdf (C : ℕ → Copula d) :
    ∃ (D : Copula d) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoUniformly (fun n => (C (φ n)).cdf) D.cdf atTop := by
  have hx : ∀ n, cdfBCF (C n) ∈ classicalSet d := fun n => (C n).isClassical_cdf
  obtain ⟨f, hf, φ, hφ, hlim⟩ := isCompact_classicalSet.tendsto_subseq hx
  refine ⟨ofClassical ⇑f hf, φ, hφ, ?_⟩
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  have h : (ofClassical (⇑f) hf).cdf = ⇑f := cdf_ofClassical _ _
  rw [h]
  exact hu

end ProbabilityTheory.Copula
