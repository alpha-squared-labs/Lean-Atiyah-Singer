/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.NativeAtlasBundleMap
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Native smooth maps act continuously on the original total spaces

Public module ID: M1374.

Native smooth maps compose in the same three specified atlases. Their
finite smooth matrix columns give joint continuity of the actual bundle
map in the specified native topologies. Fiberwise invertibility then yields an
actual bundle isomorphism with the prescribed action, using local finite rank.
No compactness, global trivialization or arbitrary fiber topology is introduced.
This is the standard local-matrix criterion needed to compare the raw symbol
triples in analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Smooth native matrix columns give continuity on the original total spaces. -/
theorem IsSmoothBundleMap.continuous_total
    {a : ∀ x, E x →ₗ[ℂ] F x}
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, a z.proj z.snd⟩ : TotalSpace Unit F)) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).continuousAt, ?_⟩
  let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E z.proj
  let t := trivializationAt (EuclideanSpace ℂ (Fin q)) F z.proj
  have hyd : z.proj ∈ d.baseSet := mem_baseSet_trivializationAt _ _ _
  have hyt : z.proj ∈ t.baseSet := mem_baseSet_trivializationAt _ _ _
  -- The same finite columns assemble a continuous coordinate operator on this overlap.
  let L (y : M) : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
    ∑ j : Fin r, ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)
        ((t ⟨y, a y (d.symmL ℂ y (EuclideanSpace.single j 1))⟩).2)
  have hL : ContinuousOn L (d.baseSet ∩ t.baseSet) := by
    apply continuousOn_finsetSum
    intro j _
    exact (ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) j)).continuous
        |>.comp_continuousOn (ha d t j).continuousOn
  have hLc := (hL.continuousAt
    ((d.open_baseSet.inter t.open_baseSet).mem_nhds ⟨hyd, hyt⟩)).comp
      (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E).continuousAt
  have hdc := ((d.continuousAt (d.mem_source.mpr hyd)).comp
    (continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).continuousAt).snd
  -- Coordinate evaluation equals the actual original bundle map on a neighborhood.
  apply (hLc.clm_apply hdc).congr_of_eventuallyEq
  filter_upwards [((d.open_baseSet.inter t.open_baseSet).preimage
    (continuous_model_proj (EuclideanSpace ℂ (Fin r)) E)).mem_nhds ⟨hyd, hyt⟩]
    with w hw
  let B := (t.linearMapAt ℂ w.proj).comp
    ((a w.proj).comp (d.symmL ℂ w.proj).toLinearMap)
  have hmap := congrArg B ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr
    (d ⟨w.proj, w.snd⟩).2)
  simpa [L, B, d, t, unitTotalEquiv, map_sum, map_smul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, t.coe_linearMapAt_of_mem hw.2,
    d.symmL_apply hw.1, d.symm_apply_apply_mk hw.1] using hmap.symm

/-- A smooth family of fiber equivalences gives the actual continuous bundle isomorphism. -/
theorem IsSmoothBundleMap.exists_iso
    (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ b : Iso E F, ∀ (x : M) (v : E x), b.linearEquiv x v = e x v := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let b : Hom E F := ⟨fun x ↦ (e x).toLinearMap, he.continuous_total⟩
  -- Local finite rank gives continuous inversion of this very forward map.
  exact ⟨b.toIso (fun x ↦ (e x).bijective), fun _ _ ↦ rfl⟩

variable {s : ℕ} {H : M → Type*}
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) H]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := s) H]

/-- Native smooth bundle maps compose on the original fibers and specified atlases. -/
theorem IsSmoothBundleMap.comp
    {a : ∀ x, E x →ₗ[ℂ] F x} {b : ∀ x, F x →ₗ[ℂ] H x}
    (hb : IsSmoothBundleMap (n := n) (r := q) (q := s) b)
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    IsSmoothBundleMap (n := n) (r := r) (q := s) (fun x ↦ (b x).comp (a x)) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin s)) H
  -- The native criteria use these same three original atlases, so the middle one cancels.
  exact (isSmoothAtlasBundleMap_native_iff _).mp
    (((isSmoothAtlasBundleMap_native_iff _).mpr hb).comp
      ((isSmoothAtlasBundleMap_native_iff _).mpr ha))

end AtiyahSinger
