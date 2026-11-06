/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol

/-!
# The specified amplitude of a localized conjugate

Public module ID: M0535.

This is the actual coordinate-change amplitude of an original two-sided
piece, for one fixed near-diagonal cutoff in its original coordinates.
The input and output matrices use the original moving-fiber actions and
the specified target frames. The same family is used for parameter estimates
and the exact localized operator identity; no symbol representative is chosen.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

/-- The original fixed-cutoff amplitude transported into the specified moving frames. -/
def PseudodifferentialPiece.equivariantLocalizedAmplitude {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (γ₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ)
    (g : G) : AmplitudeFunction n r q := by
  letI := L.input.frame_mem_atlas
  letI := L.output.frame_mem_atlas
  letI := A.frame_mem_atlas
  letI := B.frame_mem_atlas
  letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  letI (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  letI (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let d := Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g
  let t := L.chart.symm.trans (d.toHomeomorph.toOpenPartialHomeomorph.trans c)
  let oldBase (z : EuclideanSpace ℝ (Fin n)) : M := g⁻¹ • c.symm z
  let p₀ := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  let γ (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : ℝ :=
    A.cutoff z.1 * A.cutoff z.2 * γ₀ (t.symm z.1, t.symm z.2)
  let Cin := cutoffMatrix A.cutoff (fun z ↦
    (L.input.frame.continuousLinearMapAt ℂ (oldBase z)).comp
      ((σ.linearMap g⁻¹ (c.symm z)).toContinuousLinearMap.comp
        (A.frame.symmL ℂ (c.symm z))))
  -- The output frame is evaluated at the actual target fiber of τ(g).
  let Cout := cutoffMatrix A.cutoff (fun z ↦
    (B.frame.continuousLinearMapAt ℂ (g • oldBase z)).comp
      ((τ.linearMap g (oldBase z)).toContinuousLinearMap.comp
        (L.output.frame.symmL ℂ (oldBase z))))
  exact fun x y ξ ↦ (Cout x).comp
    ((coordinateAmplitude t γ p₀ x y ξ).comp (Cin y))

end AtiyahSinger
