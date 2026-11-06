/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.EquivariantAtlasSmoothing
public import AtiyahSinger.Geometry.EquivariantFixedRankModel
public import AtiyahSinger.Geometry.NativeAtlasBundleMap
public import AtiyahSinger.Geometry.SmoothAtlasSum

/-!
# Equivariant smooth sums of the original native bundles

Public module ID: M1196.

The original product-fiber bundle, with its existing sum topology, admits a
native smooth model compatible with both original smooth inclusions. Its
action is the same componentwise action through one specified comparison.
This is the usual smooth direct sum of SG III.1, presented in the project's
fixed Euclidean models for later stabilization of actual symbols.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [CompactSpace M] [T2Space M]
  {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- The original two smooth equivariant bundles have a compatible native smooth direct sum. -/
theorem exists_equivariant_native_smooth_sum
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      EquivariantStructure G F)
    (hσ : σ.IsSmooth (n := n) (r := r) IG)
    (hτ : τ.IsSmooth (n := n) (r := q) IG) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := sumTopology (E := E) (F := F)
    ∃ S : SmoothFiniteComplexBundle (n := n) M, S.rank = r + q ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
      ∃ ρ : EquivariantStructure G S.Fiber, ρ.IsSmooth (n := n) (r := S.rank) IG ∧
        ∃ e : Iso (E ×ᵇ F) S.Fiber, e.IsEquivariant (σ.sum τ) ρ ∧
          IsSmoothBundleMap (n := n) (r := r) (q := S.rank)
            (fun x ↦ (e.linearEquiv x).toLinearMap.comp (LinearMap.inl ℂ (E x) (F x))) ∧
          IsSmoothBundleMap (n := n) (r := q) (q := S.rank)
            (fun x ↦ (e.linearEquiv x).toLinearMap.comp (LinearMap.inr ℂ (E x) (F x))) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := sumTopology (E := E) (F := F)
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  -- The product atlas uses the actual two given native smooth structures.
  have hsum := A.isSmoothAtlas_sum B IG σ τ
    (σ.isSmoothAtlas_native IG hσ) (τ.isSmoothAtlas_native IG hτ)
  have hrank (x : M) : Module.finrank ℂ ((E ×ᵇ F) x) = r + q := by
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    change Module.finrank ℂ (E x × F x) = r + q
    rw [Module.finrank_prod, VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin r)) E x,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin q)) F x]
    simp
  -- Verify the second original inclusion in these same concatenated coordinates.
  have hinr : IsSmoothAtlasBundleMap B (A.sum B)
      (fun x ↦ LinearMap.inr ℂ (E x) (F x)) := by
    refine ⟨contMDiff_id, ?_⟩
    rintro i ⟨j, k⟩ a
    let c : ((Fin (A.rank j) → ℂ) × (Fin (B.rank k) → ℂ)) ≃L[ℂ]
        (Fin (A.rank j + B.rank k) → ℂ) :=
      ((LinearEquiv.sumArrowLequivProdArrow (Fin (A.rank j)) (Fin (B.rank k)) ℂ ℂ).symm.trans
        (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (A.rank j + B.rank k) ↦ ℂ)
          finSumFinEquiv)).toContinuousLinearEquiv
    have hs := c.toContinuousLinearMap.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
      ((contMDiffOn_const (c := (0 : Fin (A.rank j) → ℂ))).prodMk_space
        ((B.contMDiffOn_coordChange i k a).mono
          (fun (x : M) (hx : x ∈ (B.chart i).baseSet ∩
              ((A.chart j).baseSet ∩ (B.chart k).baseSet)) ↦ ⟨hx.1, hx.2.2⟩)))
    apply hs.congr
    intro x hx
    rw [dite_eq_left hx.1]
    change c ((A.chart j ⟨x, 0⟩).2,
      (B.chart k ⟨x, (B.frameLinearEquiv i x hx.1).symm (Pi.single a 1)⟩).2) =
        c (0, (B.chart k ((B.chart i).toPartialEquiv.symm (x, Pi.single a 1))).2)
    have hpoint := TotalSpace.mk_cast (F := Unit) (E := F)
      ((B.chart i).proj_symm_apply' (x := Pi.single a 1) hx.1)
      ((B.chart i).toPartialEquiv.symm (x, Pi.single a 1)).2
    have hzero : (A.chart j ⟨x, (0 : E x)⟩).2 = 0 :=
      (A.frameLinearEquiv j x hx.2.1).map_zero
    exact congrArg c (Prod.ext hzero
      (congrArg (fun z : TotalSpace Unit F ↦ (B.chart k z).2) hpoint))
  -- One comparison carries the sum action and both smooth inclusion maps together.
  obtain ⟨S, hrS, ρ, hρ, e, he, hforward, _⟩ :=
    (A.sum B).exists_equivariant_smooth_model_of_rank_with_atlasMaps
      IG (σ.sum τ) (r + q) hrank hsum
  let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  refine ⟨S, hrS, ρ, hρ, e, he, ?_, ?_⟩
  · exact (isSmoothAtlasBundleMap_native_iff _).mp
      (hforward.comp (A.isSmoothAtlasBundleMap_inl B))
  · exact (isSmoothAtlasBundleMap_native_iff _).mp (hforward.comp hinr)

end AtiyahSinger
