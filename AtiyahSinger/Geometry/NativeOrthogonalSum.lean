/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativeAtlasCovariantSobolev
public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.NativeAtlasBundleMap
public import AtiyahSinger.Geometry.SmoothOrthogonalSum

/-!
# Orthogonal sums of the specified native bundles

Public module ID: M1306.

Over a compact Hausdorff smooth base, this native specialization keeps the
chosen sum comparison, its smooth inverse,
the original Hermitian pairings, and both actual smooth inclusions together.
The graded PDO and its adjoint can therefore use one sum model, while the same
comparison transports the original tensor-sum symbol bundles.

The second inclusion is checked in the original concatenated sum chart. It
requires no different native model and no change of either summand's metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothFiniteComplexBundle

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] sumTopology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M] [T2Space M]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- Retain the same native sum and original metric through both smooth inclusion maps.
/-- Two specified native metric bundles admit one smooth orthogonal sum with both inclusions. -/
theorem exists_orthogonal_sum
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
    let B := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
    ∃ N : SmoothFiniteComplexBundle (n := n) M, N.rank = E.rank + F.rank ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
      ∃ e : Iso (E.Fiber ×ᵇ F.Fiber) N.Fiber,
        IsSmoothAtlasBundleMap (A.sum B)
          (nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber)
          e.toHom.linearMap ∧
        IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n) (r := N.rank) N.Fiber)
          (A.sum B) e.symm.toHom.linearMap ∧
        IsSmoothBundleMap (n := n) (r := E.rank) (q := N.rank)
          (fun x ↦ (e.linearEquiv x).toLinearMap.comp
            (LinearMap.inl ℂ (E.Fiber x) (F.Fiber x))) ∧
        IsSmoothBundleMap (n := n) (r := F.rank) (q := N.rank)
          (fun x ↦ (e.linearEquiv x).toLinearMap.comp
            (LinearMap.inr ℂ (E.Fiber x) (F.Fiber x))) ∧
        ∃ l : SmoothHermitianMetric (n := n) (r := N.rank) N.Fiber,
          ∀ x (u v : E.Fiber x × F.Fiber x),
            l.pairing x (e.linearEquiv x u) (e.linearEquiv x v) =
              h.pairing x u.1 v.1 + k.pairing x u.2 v.2 := by
  classical
  let : MeasurableSpace M := borel M
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  intro A B
  have hr (x : M) : Module.finrank ℂ (E.Fiber x) = E.rank := by
    rw [VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin E.rank)) E.Fiber x]
    simp
  have hs (x : M) : Module.finrank ℂ (F.Fiber x) = F.rank := by
    rw [VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x]
    simp
  obtain ⟨N, hN, e, he, hei, l, hl⟩ := A.exists_native_orthogonal_sum B E.rank F.rank hr hs
    h.toContinuousHermitianMetric k.toContinuousHermitianMetric
    h.isSmoothHermitianMetric_nativeAtlas k.isSmoothHermitianMetric_nativeAtlas
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  have hinr : IsSmoothAtlasBundleMap B (A.sum B)
      (fun x ↦ LinearMap.inr ℂ (E.Fiber x) (F.Fiber x)) := by
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
    have hpoint := TotalSpace.mk_cast (F := Unit) (E := F.Fiber)
      ((B.chart i).proj_symm_apply' (x := Pi.single a 1) hx.1)
      ((B.chart i).toPartialEquiv.symm (x, Pi.single a 1)).2
    have hzero : (A.chart j ⟨x, (0 : E.Fiber x)⟩).2 = 0 :=
      (A.frameLinearEquiv j x hx.2.1).map_zero
    exact congrArg c (Prod.ext hzero
      (congrArg (fun z : TotalSpace Unit F.Fiber ↦ (B.chart k z).2) hpoint))
  refine ⟨N, hN, e, he, hei, ?_, ?_, l, hl⟩
  · exact (isSmoothAtlasBundleMap_native_iff _).mp
      (he.comp (A.isSmoothAtlasBundleMap_inl B))
  · exact (isSmoothAtlasBundleMap_native_iff _).mp (he.comp hinr)

end AtiyahSinger.SmoothFiniteComplexBundle
