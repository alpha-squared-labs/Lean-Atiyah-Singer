/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass

/-!
# Native and atlas smoothness of the same punctured symbol

Public module ID: M0803.

Every native atlas frame is an original designated bundle frame. Their exact
coordinate formula identifies off-zero smoothness in both directions, without
assuming homogeneity or ellipticity. This comparison is used when transporting
a prescribed atlas symbol into a compatible native bundle model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {F : M → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- The original native and converted atlas coordinate tests define the same smoothness. -/
theorem isSmoothOffZeroAtlasSymbol_native_iff
    (a : GlobalSymbolFunction (n := n) E F) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    IsSmoothOffZeroAtlasSymbol
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) (nativeAtlasSymbolFunction a) ↔
      IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  -- Both finite-coordinate conversions cancel on the same original fiber vectors.
  have hcoord (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      atlasGlobalSymbolInChart A B (nativeAtlasSymbolFunction a) c
          ⟨e, inferInstance⟩ ⟨f, inferInstance⟩ = globalSymbolInChart E F a c e f := by
    funext z η
    apply ContinuousLinearMap.ext
    intro v
    change EuclideanSpace ℂ (Fin r) at v
    have heBase : (A.chart ⟨e, inferInstance⟩).baseSet = e.baseSet := rfl
    have hfBase : (B.chart ⟨f, inferInstance⟩).baseSet = f.baseSet := rfl
    by_cases he : c.symm z ∈ e.baseSet
    · by_cases hf : c.symm z ∈ f.baseSet
      · have heFrame : A.frameLinearEquiv ⟨e, inferInstance⟩ (c.symm z) he =
            (e.continuousLinearEquivAt ℂ (c.symm z) he).toLinearEquiv.trans
              (EuclideanSpace.equiv (Fin r) ℂ).toLinearEquiv := by
          apply LinearEquiv.ext
          intro w
          rfl
        have hfFrame : B.frameLinearEquiv ⟨f, inferInstance⟩ (c.symm z) hf =
            (f.continuousLinearEquivAt ℂ (c.symm z) hf).toLinearEquiv.trans
              (EuclideanSpace.equiv (Fin q) ℂ).toLinearEquiv := by
          apply LinearEquiv.ext
          intro w
          rfl
        simp only [atlasGlobalSymbolInChart, heBase, hfBase, he, hf, and_self, dite_true]
        change (EuclideanSpace.equiv (Fin q) ℂ).symm
          ((B.frameLinearEquiv ⟨f, inferInstance⟩ (c.symm z) hf)
            (a (c.symm z) (covectorFromChart c (c.symm z) η)
              ((A.frameLinearEquiv ⟨e, inferInstance⟩ (c.symm z) he).symm
                ((EuclideanSpace.equiv (Fin r) ℂ) v)))) = _
        rw [heFrame, hfFrame]
        change (EuclideanSpace.equiv (Fin q) ℂ).symm
          ((EuclideanSpace.equiv (Fin q) ℂ)
            ((f.continuousLinearEquivAt ℂ (c.symm z) hf)
              (a (c.symm z) (covectorFromChart c (c.symm z) η)
                ((e.continuousLinearEquivAt ℂ (c.symm z) he).symm
                  ((EuclideanSpace.equiv (Fin r) ℂ).symm
                    ((EuclideanSpace.equiv (Fin r) ℂ) v)))))) =
          f.continuousLinearMapAt ℂ (c.symm z)
            (a (c.symm z) (covectorFromChart c (c.symm z) η)
              (e.symmL ℂ (c.symm z) v))
        rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
        change (f ⟨c.symm z, a (c.symm z) (covectorFromChart c (c.symm z) η)
          (e.symm (c.symm z) v)⟩).2 = _
        rw [e.symmL_apply he]
        exact (Trivialization.continuousLinearMapAt_apply_of_mem ℂ f hf _).symm
      · simp only [atlasGlobalSymbolInChart, heBase, hfBase, hf, and_false, dite_false]
        change (0 : EuclideanSpace ℂ (Fin q)) = f.continuousLinearMapAt ℂ (c.symm z)
          (a (c.symm z) (covectorFromChart c (c.symm z) η) (e.symmL ℂ (c.symm z) v))
        simp [Trivialization.continuousLinearMapAt, Trivialization.coe_linearMapAt, hf]
    · simp only [atlasGlobalSymbolInChart, heBase, hfBase, he, false_and, dite_false]
      change (0 : EuclideanSpace ℂ (Fin q)) = f.continuousLinearMapAt ℂ (c.symm z)
        (a (c.symm z) (covectorFromChart c (c.symm z) η) (e.symmL ℂ (c.symm z) v))
      rw [e.symmL_apply_of_notMem he, map_zero, map_zero]
  constructor
  · intro ha c hc e f he hf
    have h := ha c hc ⟨e, he⟩ ⟨f, hf⟩
    change ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A B (nativeAtlasSymbolFunction a)
        c ⟨e, he⟩ ⟨f, hf⟩)) _ at h
    rw [hcoord] at h
    exact h
  · intro ha c hc i j
    rcases i with ⟨e, he⟩
    rcases j with ⟨f, hf⟩
    let := he
    let := hf
    change ContDiffOn ℝ ∞
      (Function.uncurry (atlasGlobalSymbolInChart A B (nativeAtlasSymbolFunction a)
        c ⟨e, he⟩ ⟨f, hf⟩)) _
    rw [hcoord]
    exact ha c hc e f

end AtiyahSinger
