/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Smooth moving-frame matrices of the original bundle action

Public module ID: M0507.

The original smooth action columns reconstruct its actual continuous linear
matrix in a fixed input and output frame. Joint smoothness holds on exactly
their moving overlap. This provides the common matrix family used by parameter
coordinate amplitudes, smoothing kernels, and lower-order symbol cocycles.
No smoothness of group inversion or additional Lie-group structure is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.EquivariantStructure

open Bundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)

-- The base-action instance is required to state hσ, but its columns contain the needed smoothness.
set_option linter.unusedSectionVars false in
include hσ in
/-- The actual action matrices in two original frames vary smoothly on their moving overlap. -/
theorem contMDiffOn_frameMap
    (e f : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      (fun p : G × M ↦ (f.continuousLinearMapAt ℂ (p.1 • p.2)).comp
        ((σ.linearMap p.1 p.2).toContinuousLinearMap.comp (e.symmL ℂ p.2)))
      {p : G × M | p.2 ∈ e.baseSet ∧ p.1 • p.2 ∈ f.baseSet} := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let F := EuclideanSpace ℂ (Fin r)
  let L (p : G × M) : F →L[ℂ] F :=
    (f.continuousLinearMapAt ℂ (p.1 • p.2)).comp
      ((σ.linearMap p.1 p.2).toContinuousLinearMap.comp (e.symmL ℂ p.2))
  let U : Set (G × M) := {p | p.2 ∈ e.baseSet ∧ p.1 • p.2 ∈ f.baseSet}
  -- The given smoothness hypothesis controls each column in these same frames.
  have hcol (j : Fin r) : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, F) ∞ (fun p ↦ L p (EuclideanSpace.single j 1)) U := by
    apply (hσ e f j).congr
    intro p hp
    exact f.continuousLinearMapAt_apply_of_mem ℂ hp.2 _
  -- Reassemble the finite columns; the resulting matrix is the original action on every vector.
  have hsum : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, F →L[ℂ] F) ∞
      (fun p ↦ ∑ j : Fin r, ContinuousLinearMap.smulRightL ℂ F F
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j)
        (L p (EuclideanSpace.single j 1))) U := by
    apply contMDiffOn_finsetSum
    intro j _
    exact ((ContinuousLinearMap.smulRightL ℂ F F
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j)).restrictScalars ℝ).contMDiff
        |>.comp_contMDiffOn (hcol j)
  apply hsum.congr
  intro p _
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, ContinuousLinearMap.smulRightL_apply_apply]
  change L p v = ∑ j : Fin r, v j • L p (EuclideanSpace.single j 1)
  have hv := congrArg (L p) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
  simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr] using hv.symm

end AtiyahSinger.ComplexBundle.EquivariantStructure
