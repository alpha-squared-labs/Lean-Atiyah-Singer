/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Analysis.JointGraphAdjunction
public import AtiyahSinger.Analysis.NativeAtlasDifferentialOperator
public import AtiyahSinger.Geometry.AtlasNativeMetric
public import AtiyahSinger.Geometry.AtlasSectionEquiv

/-!
# Joint L² realization of two operators on the original atlas sections

Public module ID: M0256.

The supplied native models, bundle isomorphisms and metric pairings identify
three original atlas section spaces with dense subspaces of their specified
native metric L² spaces. Two actual integral adjunctions then give the closed
simultaneous graph of the two original operators. The result retains both images
and the same smooth core; it does not replace a simultaneous closure by an
intersection of two separately chosen domains. This is the joint-domain step
used for horizontal and vertical actions in the product-index argument, SG III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {E E₀ E₁ : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace Unit E₀)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁)]

set_option maxSynthPendingDepth 40 in
/-- The integral adjunctions give a joint closed graph in the specified native L² spaces. -/
theorem exists_closed_jointL2Realization
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) E₀)
    (C : SmoothComplexBundleAtlas (n := n) E₁)
    (h : ContinuousHermitianMetric E)
    (h₀ : ContinuousHermitianMetric E₀) (h₁ : ContinuousHermitianMetric E₁)
    (N N₀ N₁ : SmoothFiniteComplexBundle (n := n) M)
    (k : SmoothHermitianMetric (n := n) (r := N.rank) N.Fiber)
    (k₀ : SmoothHermitianMetric (n := n) (r := N₀.rank) N₀.Fiber)
    (k₁ : SmoothHermitianMetric (n := n) (r := N₁.rank) N₁.Fiber)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
    ∀ (e : Iso E N.Fiber) (e₀ : Iso E₀ N₀.Fiber) (e₁ : Iso E₁ N₁.Fiber)
      (he : IsSmoothAtlasBundleMap A (nativeSmoothComplexBundleAtlas N.Fiber)
        e.toHom.linearMap)
      (hei : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) A
        e.symm.toHom.linearMap)
      (he₀ : IsSmoothAtlasBundleMap B (nativeSmoothComplexBundleAtlas N₀.Fiber)
        e₀.toHom.linearMap)
      (he₀i : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₀.Fiber) B
        e₀.symm.toHom.linearMap)
      (he₁ : IsSmoothAtlasBundleMap C (nativeSmoothComplexBundleAtlas N₁.Fiber)
        e₁.toHom.linearMap)
      (he₁i : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N₁.Fiber) C
        e₁.symm.toHom.linearMap),
      (∀ (x : M) (v w : E x), k.pairing x (e.linearEquiv x v) (e.linearEquiv x w) =
        (h.toCore x).inner v w) →
      (∀ (x : M) (v w : E₀ x), k₀.pairing x (e₀.linearEquiv x v) (e₀.linearEquiv x w) =
        (h₀.toCore x).inner v w) →
      (∀ (x : M) (v w : E₁ x), k₁.pairing x (e₁.linearEquiv x v) (e₁.linearEquiv x w) =
        (h₁.toCore x).inner v w) →
      ∀ (p : A.smoothSections →ₗ[ℂ] B.smoothSections)
        (q : A.smoothSections →ₗ[ℂ] C.smoothSections)
        (pa : B.smoothSections →ₗ[ℂ] A.smoothSections)
        (qa : C.smoothSections →ₗ[ℂ] A.smoothSections),
      (∀ u v, (∫ x, (h₀.toCore x).inner ((p u).val x) (v.val x) ∂μ) =
        ∫ x, (h.toCore x).inner (u.val x) ((pa v).val x) ∂μ) →
      (∀ u v, (∫ x, (h₁.toCore x).inner ((q u).val x) (v.val x) ∂μ) =
        ∫ x, (h.toCore x).inner (u.val x) ((qa v).val x) ∂μ) →
      let S := (atlasSmoothSectionEquiv A (nativeSmoothComplexBundleAtlas N.Fiber)
        e he hei).trans (nativeSmoothSectionLinearEquiv N.Fiber)
      let S₀ := (atlasSmoothSectionEquiv B (nativeSmoothComplexBundleAtlas N₀.Fiber)
        e₀ he₀ he₀i).trans (nativeSmoothSectionLinearEquiv N₀.Fiber)
      let S₁ := (atlasSmoothSectionEquiv C (nativeSmoothComplexBundleAtlas N₁.Fiber)
        e₁ he₁ he₁i).trans (nativeSmoothSectionLinearEquiv N₁.Fiber)
      let i := (k.smoothToL2 μ).comp S.toLinearMap
      let j₀ := (k₀.smoothToL2 μ).comp S₀.toLinearMap
      let j₁ := (k₁.smoothToL2 μ).comp S₁.toLinearMap
      ∃ D : k.L2SectionSpace μ →ₗ.[ℂ] (k₀.L2SectionSpace μ × k₁.L2SectionSpace μ),
        D.graph = (i.prod ((j₀.comp p).prod (j₁.comp q))).range.topologicalClosure ∧
          D.IsClosed ∧ Dense (D.domain : Set (k.L2SectionSpace μ)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀.rank)) N₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁.rank)) N₁.Fiber
  intro e e₀ e₁ he hei he₀ he₀i he₁ he₁i hk hk₀ hk₁ p q pa qa hp hq
  let S := (atlasSmoothSectionEquiv A (nativeSmoothComplexBundleAtlas N.Fiber)
    e he hei).trans (nativeSmoothSectionLinearEquiv N.Fiber)
  let S₀ := (atlasSmoothSectionEquiv B (nativeSmoothComplexBundleAtlas N₀.Fiber)
    e₀ he₀ he₀i).trans (nativeSmoothSectionLinearEquiv N₀.Fiber)
  let S₁ := (atlasSmoothSectionEquiv C (nativeSmoothComplexBundleAtlas N₁.Fiber)
    e₁ he₁ he₁i).trans (nativeSmoothSectionLinearEquiv N₁.Fiber)
  let i := (k.smoothToL2 μ).comp S.toLinearMap
  let j₀ := (k₀.smoothToL2 μ).comp S₀.toLinearMap
  let j₁ := (k₁.smoothToL2 μ).comp S₁.toLinearMap
  -- Each supplied section isomorphism is onto the same native smooth core, hence has dense image.
  have hi : DenseRange i := by
    apply (k.denseRange_smoothToL2 μ).mono
    rintro _ ⟨u, rfl⟩
    exact ⟨S.symm u, congrArg (k.smoothToL2 μ) (S.apply_symm_apply u)⟩
  have hj₀ : DenseRange j₀ := by
    apply (k₀.denseRange_smoothToL2 μ).mono
    rintro _ ⟨u, rfl⟩
    exact ⟨S₀.symm u, congrArg (k₀.smoothToL2 μ) (S₀.apply_symm_apply u)⟩
  have hj₁ : DenseRange j₁ := by
    apply (k₁.denseRange_smoothToL2 μ).mono
    rintro _ ⟨u, rfl⟩
    exact ⟨S₁.symm u, congrArg (k₁.smoothToL2 μ) (S₁.apply_symm_apply u)⟩
  -- The completion pairing pulls back to exactly the original metric integral, in each slot.
  have hinner (u v : A.smoothSections) : inner ℂ (i u) (i v) =
      ∫ x, (h.toCore x).inner (u.val x) (v.val x) ∂μ := by
    change inner ℂ (k.smoothToL2 μ (S u)) (k.smoothToL2 μ (S v)) = _
    rw [k.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ hk x (u.val x) (v.val x)
  have hinner₀ (u v : B.smoothSections) : inner ℂ (j₀ u) (j₀ v) =
      ∫ x, (h₀.toCore x).inner (u.val x) (v.val x) ∂μ := by
    change inner ℂ (k₀.smoothToL2 μ (S₀ u)) (k₀.smoothToL2 μ (S₀ v)) = _
    rw [k₀.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ hk₀ x (u.val x) (v.val x)
  have hinner₁ (u v : C.smoothSections) : inner ℂ (j₁ u) (j₁ v) =
      ∫ x, (h₁.toCore x).inner (u.val x) (v.val x) ∂μ := by
    change inner ℂ (k₁.smoothToL2 μ (S₁ u)) (k₁.smoothToL2 μ (S₁ v)) = _
    rw [k₁.inner_smoothToL2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ hk₁ x (u.val x) (v.val x)
  -- Both adjunctions now hold in these same Hilbert spaces, with both outputs retained together.
  apply exists_closed_jointGraph_of_adjoint_pairings
    i (j₀.comp p) (j₁.comp q) j₀ j₁ (i.comp pa) (i.comp qa) hi hj₀ hj₁
  · intro u v
    change inner ℂ (j₀ (p u)) (j₀ v) = inner ℂ (i u) (i (pa v))
    rw [hinner₀, hinner]
    exact hp u v
  · intro u v
    change inner ℂ (j₁ (q u)) (j₁ v) = inner ℂ (i u) (i (qa v))
    rw [hinner₁, hinner]
    exact hq u v

end AtiyahSinger.SmoothComplexBundleAtlas
