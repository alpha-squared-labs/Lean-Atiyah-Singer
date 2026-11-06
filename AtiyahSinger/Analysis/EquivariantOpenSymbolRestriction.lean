/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Geometry.SmoothEquivariantPullback
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantCotangentClopen

/-!
# Covariance of the actual symbol on an invariant open submanifold

Public module ID: M0546.

The restricted symbol uses the original covectors and fiber maps. Its native
pulled actions satisfy covariance by the actual cotangent inclusion square
and the two original bundle-action lift squares. The open set need not be
compact or closed, and the symbol need not be realized by an operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native open restriction preserves the original off-zero equivariance equation. -/
theorem equivariantGlobalSymbolLinearMap_eq_restrictOpen
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure G E.Fiber)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure G F.Fiber)
    (U : Opens M) [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (s : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g s x ξ = s x ξ) :
    let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
    let σU := σ.modelPullback i hU
    let τU := τ.modelPullback i hU
    ∀ (g : G) (x : U) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σU τU g (fun y η ↦ s y.val η) x ξ = s x.val ξ := by
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let σU := σ.modelPullback i hU
  let τU := τ.modelPullback i hU
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) ((i : U → M) *ᵖ E.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) ((i : U → M) *ᵖ F.Fiber)
  apply (equivariantGlobalSymbolLinearMap_eq_iff IG σU τU (fun y η ↦ s y.val η)).mpr
  intro g x ξ hξ v
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let η := (cotangentDiffeomorphMap (Diffeomorph.smul (M := U) IG I ∞ g) ⟨x, ξ⟩).snd
  -- The actual open inclusion identifies the transported native covector.
  have hcot := cotangentOpenInclusion_smul IG U hU g ⟨x, ξ⟩
  have hη : η =
      (cotangentDiffeomorphMap (Diffeomorph.smul (M := M) IG I ∞ g) ⟨x.val, ξ⟩).snd :=
    eq_of_heq (TotalSpace.ext_iff.mp hcot).2
  have hsource := σ.modelPullback_lift i hU g x v
  have htarget := τ.modelPullback_lift i hU g x (s x.val ξ v)
  have hsymbol := (equivariantGlobalSymbolLinearMap_eq_iff IG σ τ s).mp hs g x.val ξ hξ v
  let S : TotalSpace Unit E.Fiber → TotalSpace Unit F.Fiber :=
    fun z ↦ ⟨z.proj, s z.proj η z.snd⟩
  have hsquare :
      (⟨i (g • x), s (i (g • x)) η (σU.linearMap g x v)⟩ : TotalSpace Unit F.Fiber) =
        ⟨i (g • x), τU.linearMap g x (s (i x) ξ v)⟩ := by
    calc
      _ = ⟨g • i x, s (g • i x) η (σ.linearMap g (i x) v)⟩ := congrArg S hsource
      _ = ⟨g • i x, τ.linearMap g (i x) (s (i x) ξ v)⟩ := by
        rw [hη]
        exact congrArg (TotalSpace.mk (g • i x)) hsymbol
      _ = _ := htarget.symm
  exact TotalSpace.mk_injective (i (g • x)) hsquare

end AtiyahSinger
