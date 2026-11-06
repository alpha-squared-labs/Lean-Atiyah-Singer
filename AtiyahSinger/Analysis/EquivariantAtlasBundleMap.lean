/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# The section action of a smooth equivariant atlas bundle map

Public module ID: M0465.

An equivariant map of the original bundles intertwines their actual smooth
section representations. This retains the specified atlases, actions and
fiber maps, including the equality transports in the moving-base action.
The result supplies both maps of the smooth retract used in quantization.

Source: the bundle and section equivariance definitions in SG III.9.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
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
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  (σ : EquivariantStructure G E) (τ : EquivariantStructure G F)
  (hσ : σ.IsSmoothAtlas IG A) (hτ : τ.IsSmoothAtlas IG B)

/-- The original smooth equivariant bundle map intertwines the original section actions. -/
theorem ComplexBundle.Hom.atlasSmoothSectionMap_intertwines
    (c : Hom E F) (hc : IsSmoothAtlasBundleMap A B c.linearMap)
    (he : c.IsEquivariant σ τ) (g : G) :
    (atlasSmoothSectionMap A B c.linearMap hc).comp
        (σ.atlasSmoothSectionRepresentation IG A hσ g) =
      (τ.atlasSmoothSectionRepresentation IG B hτ g).comp
        (atlasSmoothSectionMap A B c.linearMap hc) := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x
  -- Fiberwise maps commute with equality transport along the same base identity.
  let transportE : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  let transportF : ∀ {x y : M}, x = y → F x →ₗ[ℂ] F y := fun {x y} h ↦ by
    subst y
    exact LinearMap.id
  have htransport {x y : M} (h : x = y) (v : E x) :
      c.linearMap y (transportE h v) = transportF h (c.linearMap x v) := by
    subst y
    rfl
  change c.linearMap x (transportE (smul_inv_smul g x)
    (σ.linearMap g (g⁻¹ • x) (s.val (g⁻¹ • x)))) =
      transportF (smul_inv_smul g x)
        (τ.linearMap g (g⁻¹ • x) (c.linearMap (g⁻¹ • x) (s.val (g⁻¹ • x))))
  -- The equivariant square is evaluated on the original vector over the inverse-moved point.
  rw [htransport, he g (g⁻¹ • x) (s.val (g⁻¹ • x))]

end AtiyahSinger
