/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# Tensoring the original cotangent symbol with a bundle identity

Public module ID: M1031.

The original fiber map is tensored with the identity of the supplied
locally finite-rank twisting bundle. The tensor charts and tensor topology
are exactly those fixed by SmoothTensorAtlas. This construction preserves
cotangent linearity and off-zero invertibility without an equality of ranks
or positive-rank assumption. On a smoothly compatible base atlas, the same
symbol also preserves smoothness.

Sources: SG II.5 Proposition 5.10 and III.13.10. These properties concern
the same displayed symbol, not an arbitrarily isomorphic replacement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F W : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
  [TopologicalSpace (TotalSpace Unit W)]

attribute [local instance] ComplexBundle.tensorTopology

/-- The actual original symbol tensored on the right with the identity of the twisting fiber. -/
def tensorAtlasSymbol (c : AtlasSymbolFunction (n := n) E F) :
    AtlasSymbolFunction (n := n) (fun x ↦ E x ⊗[ℂ] W x) (fun x ↦ F x ⊗[ℂ] W x) :=
  fun x ξ ↦ TensorProduct.map (c x ξ) (LinearMap.id : Module.End ℂ (W x))

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use tensorAtlasSymbol_properties_of_isManifold for this same map.
The historical outline below does not justify the original weak chart assumptions.
This block defines no Lean constant.

/-- Smoothness, cotangent linearity and ellipticity are retained by the same tensor symbol. -/
theorem tensorAtlasSymbol_properties
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F)
    (C : SmoothComplexBundleAtlas (n := n) W)
    (c : AtlasSymbolFunction (n := n) E F)
    (hc : ∀ x : M, IsLinearMap ℝ (c x))
    (hs : IsSmoothOffZeroAtlasSymbol A B c) :
    (∀ x : M, IsLinearMap ℝ (tensorAtlasSymbol (W := W) c x)) ∧
      IsSmoothOffZeroAtlasSymbol (tensorSmoothAtlas A C) (tensorSmoothAtlas B C)
        (tensorAtlasSymbol c) ∧
      (IsEllipticAtlasSymbol c → IsEllipticAtlasSymbol (tensorAtlasSymbol (W := W) c)) 
  /- Stage 1: tensoring a linear map with a fixed identity is linear
  in that map. The actual pure-vector formula proves the two real-linear
  identities on a spanning set of original tensor vectors.
  Stage 2: in the specified tensor charts, every matrix entry is an
  entry of c times an identity entry. Thus the off-zero coordinate maps
  are smooth on the exact original overlaps, even when ranks vary.
  Stage 3: tensor the actual inverse of c(x,ξ) with that same identity.
  The two tensor composition identities yield a two-sided inverse on
  the original fibers. This includes the zero twisting fiber and imposes
  no equal-rank premise or choice of a different tensor topology. -/
-/

end AtiyahSinger
