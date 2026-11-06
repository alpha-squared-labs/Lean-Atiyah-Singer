/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.TensorAtlasSymbol
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# The coefficient action on the original cotangent symbol class

Public module ID: M0314.

Tensoring the given elliptic symbol with the identity of the actual coefficient
bundle gives the compact-support K action of that bundle. The comparison uses
the original zero-section control and the literal pullback/tensor isomorphisms.
The supplied smoothness certificates apply to the actual symbols; no linearity
in the covector, global rank or nonzero coefficient rank is required.

Source: SG III.13.6 and the support-triple tensor action. This is the topological
coefficient comparison needed for the associated-sphere index construction;
a particular PDO's principal class is identified by a separate comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor isFiniteRank_pullback
  t2Space_cotangent locallyCompactSpace_cotangent

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M]
  {E F W : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  [TopologicalSpace (TotalSpace Unit W)]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 30 in
/-- The actual coefficient symbol realizes the action of the original coefficient bundle. -/
theorem atlasSymbolKClass_tensor
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (C : SmoothComplexBundleAtlas (n := n) W)
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hi : IsEllipticAtlasSymbol a)
    (ht : IsSmoothOffZeroAtlasSymbol (tensorSmoothAtlas A C) (tensorSmoothAtlas B C)
      (tensorAtlasSymbol (W := W) a))
    (hj : IsEllipticAtlasSymbol (tensorAtlasSymbol (W := W) a)) :
    letI := C.isFiniteRank
    atlasSymbolKClass (tensorSmoothAtlas A C) (tensorSmoothAtlas B C)
        (tensorAtlasSymbol (W := W) a) ht hj =
      complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := M))
        (ComplexBundle.kZeroClass W) (atlasSymbolKClass A B a hs hi) := by
  classical
  let := A.isFiniteRank
  let := B.isFiniteRank
  let := C.isFiniteRank
  let p : C(CotangentTotalSpace (n := n) (M := M), M) := cotangentProjection
  let u := atlasEllipticSymbolTriple A B a hs hi
  let v := atlasEllipticSymbolTriple (tensorSmoothAtlas A C) (tensorSmoothAtlas B C)
    (tensorAtlasSymbol (W := W) a) ht hj
  -- The specified pullback/tensor comparisons retain each original tensor vector.
  let e : Iso ((p : _ → M) *ᵖ (fun x ↦ E x ⊗[ℂ] W x))
      (fun y ↦ ((p : _ → M) *ᵖ E) y ⊗[ℂ] ((p : _ → M) *ᵖ W) y) :=
    pullbackTensorIso (E := E) (F := W) p
  let f : Iso ((p : _ → M) *ᵖ (fun x ↦ F x ⊗[ℂ] W x))
      (fun y ↦ ((p : _ → M) *ᵖ F) y ⊗[ℂ] ((p : _ → M) *ᵖ W) y) :=
    pullbackTensorIso (E := F) (F := W) p
  -- Both triples have the same zero control, and their exterior maps agree on pure tensors.
  have htriple : v.congr e f = u.tensorRight ((p : _ → M) *ᵖ W) := by
    change CompactSupportTriple.mk cotangentZeroSet _ _ =
      CompactSupportTriple.mk cotangentZeroSet _ _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext'
    intro x w
    rfl
  -- Invariance under those actual bundle isomorphisms identifies the support action.
  change v.compactSupportClass =
    complexKZeroCompactSupportAction p (ComplexBundle.kZeroClass W) u.compactSupportClass
  calc
    _ = (v.congr e f).compactSupportClass := (v.compactSupportClass_congr e f).symm
    _ = (u.tensorRight ((p : _ → M) *ᵖ W)).compactSupportClass :=
      congrArg CompactSupportTriple.compactSupportClass htriple
    _ = _ := u.compactSupportClass_tensorRight_pullback W p

end AtiyahSinger
