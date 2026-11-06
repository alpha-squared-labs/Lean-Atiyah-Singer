/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.NativeSmoothAtlas
public import AtiyahSinger.Geometry.SmoothBundleMaps

/-!
# Compatibility of the native and atlas smooth bundle-map criteria

Public module ID: M1303.

The same original bundle map has the same smoothness criterion in the native
charts and in their finite-coordinate atlas. This comparison uses the canonical
coordinate equivalence and retains each original designated chart and fiber.
It is the standard local-matrix definition of a smooth bundle map in SG III.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
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

/-- The native atlas tests smoothness of the same original fiberwise linear map. -/
theorem isSmoothAtlasBundleMap_native_iff (a : ∀ x : M, E x →ₗ[ℂ] F x) :
    (letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
     letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
     IsSmoothAtlasBundleMap
       (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
       (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) a) ↔
      IsSmoothBundleMap (n := n) (r := r) (q := q) a :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let c := EuclideanSpace.equiv (Fin q) ℂ
  -- Both inverse frames select exactly the same original vector on the same base set.
  have hframe (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) (k : Fin r) :
      letI : MemTrivializationAtlas i.val := i.property
      (A.frameLinearEquiv i x hx).symm (Pi.single k 1) =
        i.val.symmL ℂ x (EuclideanSpace.single k 1) := by
    let : MemTrivializationAtlas i.val := i.property
    apply (A.frameLinearEquiv i x hx).injective
    rw [LinearEquiv.apply_symm_apply]
    change Pi.single k 1 = (EuclideanSpace.equiv (Fin r) ℂ)
      ((i.val ⟨x, i.val.symmL ℂ x (EuclideanSpace.single k 1)⟩).2)
    rw [← i.val.continuousLinearMapAt_apply_of_mem ℂ hx,
      i.val.continuousLinearMapAt_symmL hx]
    rfl
  constructor
  · intro ha e he f hf k
    let i : A.Index := ⟨e, he⟩
    let j : B.Index := ⟨f, hf⟩
    have h := (c.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn (ha.2 i j k)
    apply h.congr
    intro x hx
    have hxi : x ∈ (A.chart i).baseSet := hx.1
    change (f ⟨x, a x (e.symmL ℂ x (EuclideanSpace.single k 1))⟩).2 =
      c.symm (if hx : x ∈ (A.chart i).baseSet then
        (B.chart j ⟨x, a x ((A.frameLinearEquiv i x hx).symm (Pi.single k 1))⟩).2 else 0)
    rw [dite_eq_left hxi, hframe i x hxi k]
    rfl
  · intro ha
    refine ⟨contMDiff_id, ?_⟩
    intro i j k
    let : MemTrivializationAtlas i.val := i.property
    let : MemTrivializationAtlas j.val := j.property
    have h := c.toContinuousLinearMap.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
      (ha i.val j.val k)
    apply h.congr
    intro x hx
    have hxi : x ∈ (A.chart i).baseSet := hx.1
    rw [dite_eq_left hxi, hframe i x hxi k]
    rfl

end AtiyahSinger
