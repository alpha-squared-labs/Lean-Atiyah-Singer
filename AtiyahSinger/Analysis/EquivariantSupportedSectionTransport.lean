/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Geometry.OpenSections
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Equivariance of supported section transport

Public module ID: M0585.

A section map prescribed by an equivariant fiber map on the image of a specified
base map and by zero off its prescribed support intertwines the actual smooth
actions. The conclusion uses the original section map. It neither chooses new
actions nor assumes that the two entire spaces of sections are equivalent. This
is the geometric action comparison for both source and target maps in analytic
excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N]
  (E : SmoothFiniteComplexBundle (n := n) M)
  (F : SmoothFiniteComplexBundle (n := m) N)
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (hσ : σ.IsSmooth (n := n) (r := E.rank) IG)
  (hτ : τ.IsSmooth (n := m) (r := F.rank) IG)

set_option maxHeartbeats 1000000 in
-- Keep the moving fibers in the original total-space action square.
/-- A prescribed equivariant fiber transport, extended by zero, intertwines section actions. -/
theorem supportedSmoothSectionTransport_intertwines
    (f : M → N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (K : Set M) (L : Set N) (hL : IsClosed L)
    (hLi : ∀ (g : G) (y : N), g • y ∈ L ↔ y ∈ L)
    (hLf : L ⊆ Set.range f)
    (a : ∀ x : M, E.Fiber x →ₗ[ℂ] F.Fiber (f x))
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (g : G) (x : M) (v : E.Fiber x),
        (⟨f (g • x), a (g • x) (σ.linearMap g x v)⟩ : TotalSpace Unit F.Fiber) =
          ⟨g • f x, τ.linearMap g (f x) (a x v)⟩)
    (T : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K →ₗ[ℂ]
      supportedSmoothSections (n := m) (r := F.rank) F.Fiber L)
    (hT : ∀ (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) (x : M),
      (T u).val.val (f x) = a x (u.val.val x))
    (g : G) (u : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K)
    (hu : σ.smoothSectionRepresentation IG hσ g u.val ∈
      supportedSmoothSections (n := n) (r := E.rank) E.Fiber K) :
    (T ⟨σ.smoothSectionRepresentation IG hσ g u.val, hu⟩).val =
      τ.smoothSectionRepresentation IG hτ g (T u).val := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let gu : supportedSmoothSections (n := n) (r := E.rank) E.Fiber K :=
    ⟨σ.smoothSectionRepresentation IG hσ g u.val, hu⟩
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ L
  · -- Compare on the original image after moving both base points by the same element.
    obtain ⟨x, hx⟩ := hLf ((hLi g⁻¹ y).mpr hy)
    have hxy : g • f x = y := (congrArg (fun z ↦ g • z) hx).trans (smul_inv_smul g y)
    have hfxy : f (g • x) = y := (hf g x).trans hxy
    apply TotalSpace.mk_injective (F := Unit) y
    calc
      (⟨y, (T gu).val.val y⟩ : TotalSpace Unit F.Fiber) =
          ⟨f (g • x), (T gu).val.val (f (g • x))⟩ :=
        congrArg (fun z ↦ (⟨z, (T gu).val.val z⟩ : TotalSpace Unit F.Fiber)) hfxy.symm
      _ = ⟨f (g • x), a (g • x) (σ.sectionLinearMap g u.val.val (g • x))⟩ := by
        rw [hT gu]
        rfl
      _ = ⟨f (g • x), a (g • x) (σ.linearMap g x (u.val.val x))⟩ := by
        rw [σ.sectionLinearMap_smul]
      _ = ⟨g • f x, τ.linearMap g (f x) (a x (u.val.val x))⟩ := ha g x _
      _ = ⟨g • f x, τ.sectionLinearMap g (T u).val.val (g • f x)⟩ := by
        rw [τ.sectionLinearMap_smul, hT]
      _ = ⟨y, τ.sectionLinearMap g (T u).val.val y⟩ :=
        congrArg (fun z ↦ (⟨z, τ.sectionLinearMap g (T u).val.val z⟩ :
          TotalSpace Unit F.Fiber)) hxy
  · -- Off the invariant target control both sections are the original zero extension.
    have hs : closure {z : N | (T u).val.val z ≠ 0} ⊆ L := by
      apply closure_minimal ?_ hL
      intro z hz
      by_contra hzL
      exact hz ((T u).property z hzL)
    have hacted : closure {z : N | τ.sectionLinearMap g (T u).val.val z ≠ 0} ⊆ L := by
      rw [τ.closure_support_sectionLinearMap]
      rintro _ ⟨z, hz, rfl⟩
      exact (hLi g z).mpr (hs hz)
    have hzero : τ.sectionLinearMap g (T u).val.val y = 0 := by
      by_contra hne
      exact hy (hacted (subset_closure hne))
    exact ((T gu).property y hy).trans hzero.symm

end AtiyahSinger
