/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothBundleMapOperator

/-!
# The actual smooth and L² maps of a specified bundle direct sum

Public module ID: M0964.

Smoothness of the two inclusions of a specified fiberwise decomposition gives
smoothness of its original inverse projections. The finite coordinate matrix
is inverted on each common frame neighborhood, without choosing a new smooth
structure on the product bundle or imposing a global rank equality. The same
maps then give the bounded decomposition of the original metric completions.

Source: the smooth local-matrix inverse argument and finite direct-sum
construction used in SG III.5 and III.9; explicit comparison with the existing
metric completions is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r₁ r₂ r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E₁ E₂ E : M → Type*}
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [∀ x, NormedAddCommGroup (E₂ x)] [∀ x, NormedSpace ℂ (E₂ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₂)) E₂)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₂)) E₂]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₂)) E₂]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

set_option maxHeartbeats 800000 in
-- Normalize the original smooth columns and invert the same bundle decomposition.
set_option backward.isDefEq.respectTransparency false in
/-- Smooth inclusions of a specified decomposition give its original smooth inverse projections. -/
theorem isSmoothBundleMap_sumInverse
    (e : ∀ x, (E₁ x × E₂ x) ≃ₗ[ℂ] E x)
    (h₁ : IsSmoothBundleMap (n := n) (r := r₁) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))))
    (h₂ : IsSmoothBundleMap (n := n) (r := r₂) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x)))) :
    IsSmoothBundleMap (n := n) (r := r) (q := r₁)
      (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap) ∧
    IsSmoothBundleMap (n := n) (r := r) (q := r₂)
      (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap) := by
  classical
  let V₁ := EuclideanSpace ℂ (Fin r₁)
  let V₂ := EuclideanSpace ℂ (Fin r₂)
  let V := EuclideanSpace ℂ (Fin r)
  -- Assemble both smooth column families in arbitrary original common frames.
  have hinverse (d₁ : Trivialization V₁ (π V₁ E₁)) [MemTrivializationAtlas d₁]
      (d₂ : Trivialization V₂ (π V₂ E₂)) [MemTrivializationAtlas d₂]
      (f : Trivialization V (π V E)) [MemTrivializationAtlas f]
      (x : M) (hx : x ∈ (d₁.baseSet ∩ d₂.baseSet) ∩ f.baseSet) :
      ∃ L : M → (V₁ × V₂) →L[ℂ] V,
        ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V₁ × V₂) ∞
          (fun y ↦ (L y).inverse) x ∧
        ∀ y ∈ (d₁.baseSet ∩ d₂.baseSet) ∩ f.baseSet, ∀ v : V,
          (L y).inverse v =
            ((d₁ ⟨y, ((e y).symm (f.symmL ℂ y v)).1⟩).2,
              (d₂ ⟨y, ((e y).symm (f.symmL ℂ y v)).2⟩).2) := by
    let L₁ : M → V₁ →L[ℂ] V := fun y ↦
      ((f.linearMapAt ℂ y).comp ((e y).toLinearMap.comp
        ((LinearMap.inl ℂ (E₁ y) (E₂ y)).comp (d₁.symmL ℂ y).toLinearMap))).toContinuousLinearMap
    let L₂ : M → V₂ →L[ℂ] V := fun y ↦
      ((f.linearMapAt ℂ y).comp ((e y).toLinearMap.comp
        ((LinearMap.inr ℂ (E₁ y) (E₂ y)).comp (d₂.symmL ℂ y).toLinearMap))).toContinuousLinearMap
    have hL₁ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V₁ →L[ℂ] V) ∞
        L₁ (d₁.baseSet ∩ f.baseSet) := by
      have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V₁ →L[ℂ] V) ∞
          (fun y ↦ ∑ j : Fin r₁, ContinuousLinearMap.smulRightL ℂ V₁ V
            (PiLp.proj 2 (fun _ : Fin r₁ ↦ ℂ) j)
            ((f ⟨y, e y (d₁.symmL ℂ y (EuclideanSpace.single j 1), 0)⟩).2))
          (d₁.baseSet ∩ f.baseSet) := by
        apply contMDiffOn_finsetSum
        intro j _
        exact ((ContinuousLinearMap.smulRightL ℂ V₁ V
          (PiLp.proj 2 (fun _ : Fin r₁ ↦ ℂ) j)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
            (h₁ d₁ f j)
      apply hsum.congr
      intro y hy
      apply ContinuousLinearMap.ext
      intro v
      have hexpand := congrArg (L₁ y) ((EuclideanSpace.basisFun (Fin r₁) ℂ).sum_repr v)
      simpa [L₁, V₁, V, PiLp.proj, PiLp.projₗ, WithLp.coe_linearEquiv,
        map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hy.2] using hexpand.symm
    have hL₂ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V₂ →L[ℂ] V) ∞
        L₂ (d₂.baseSet ∩ f.baseSet) := by
      have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V₂ →L[ℂ] V) ∞
          (fun y ↦ ∑ j : Fin r₂, ContinuousLinearMap.smulRightL ℂ V₂ V
            (PiLp.proj 2 (fun _ : Fin r₂ ↦ ℂ) j)
            ((f ⟨y, e y (0, d₂.symmL ℂ y (EuclideanSpace.single j 1))⟩).2))
          (d₂.baseSet ∩ f.baseSet) := by
        apply contMDiffOn_finsetSum
        intro j _
        exact ((ContinuousLinearMap.smulRightL ℂ V₂ V
          (PiLp.proj 2 (fun _ : Fin r₂ ↦ ℂ) j)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
            (h₂ d₂ f j)
      apply hsum.congr
      intro y hy
      apply ContinuousLinearMap.ext
      intro v
      have hexpand := congrArg (L₂ y) ((EuclideanSpace.basisFun (Fin r₂) ℂ).sum_repr v)
      simpa [L₂, V₂, V, PiLp.proj, PiLp.projₗ, WithLp.coe_linearEquiv,
        map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, f.coe_linearMapAt_of_mem hy.2] using hexpand.symm
    let L : M → (V₁ × V₂) →L[ℂ] V := fun y ↦ (L₁ y).coprod (L₂ y)
    have hL : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, (V₁ × V₂) →L[ℂ] V) ∞ L ((d₁.baseSet ∩ d₂.baseSet) ∩ f.baseSet) := by
      let A₁ : (V₁ →L[ℂ] V) →L[ℝ] ((V₁ × V₂) →L[ℂ] V) :=
        ((ContinuousLinearMap.compL ℂ (V₁ × V₂) V₁ V).flip
          (ContinuousLinearMap.fst ℂ V₁ V₂)).restrictScalars ℝ
      let A₂ : (V₂ →L[ℂ] V) →L[ℝ] ((V₁ × V₂) →L[ℂ] V) :=
        ((ContinuousLinearMap.compL ℂ (V₁ × V₂) V₂ V).flip
          (ContinuousLinearMap.snd ℂ V₁ V₂)).restrictScalars ℝ
      exact (A₁.contMDiff.comp_contMDiffOn (hL₁.mono (fun _ hy ↦ ⟨hy.1.1, hy.2⟩))).add
        (A₂.contMDiff.comp_contMDiffOn (hL₂.mono (fun _ hy ↦ ⟨hy.1.2, hy.2⟩)))
    let C (y : M) (hy : y ∈ (d₁.baseSet ∩ d₂.baseSet) ∩ f.baseSet) :
        (V₁ × V₂) ≃L[ℂ] V :=
      ((((d₁.linearEquivAt ℂ y hy.1.1).prodCongr (d₂.linearEquivAt ℂ y hy.1.2)).symm.trans
        (e y)).trans (f.linearEquivAt ℂ y hy.2)).toContinuousLinearEquiv
    have hC (y : M) (hy : y ∈ (d₁.baseSet ∩ d₂.baseSet) ∩ f.baseSet) :
        (C y hy).toContinuousLinearMap = L y := by
      apply ContinuousLinearMap.ext
      intro v
      have hsum := map_add ((f.linearMapAt ℂ y).comp (e y).toLinearMap)
        (d₁.symm y v.1, 0) (0, d₂.symm y v.2)
      simpa [C, L, L₁, L₂, f.coe_linearMapAt_of_mem hy.2,
        d₁.symmL_apply hy.1.1, d₂.symmL_apply hy.1.2,
        Bundle.Trivialization.linearEquivAt_symm_apply,
        Bundle.Trivialization.linearEquivAt_apply] using hsum
    have hinversion := (contDiffAt_map_inverse (n := ∞) (C x hx)).restrict_scalars ℝ
    rw [hC x hx] at hinversion
    refine ⟨L, hinversion.comp_contMDiffAt (hL.contMDiffAt
      (((d₁.open_baseSet.inter d₂.open_baseSet).inter f.open_baseSet).mem_nhds hx)), ?_⟩
    intro y hy v
    rw [← hC y hy, ContinuousLinearMap.inverse_equiv]
    simp [C, f.symmL_apply hy.2, Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply]
  -- Project the same smooth inverse coordinate map to its two original row blocks.
  constructor
  · intro f _ d₁ _ j x hx
    let d₂ := trivializationAt V₂ E₂ x
    have hx₂ : x ∈ d₂.baseSet := mem_baseSet_trivializationAt _ _ _
    obtain ⟨L, hL, hvalue⟩ := hinverse d₁ d₂ f x ⟨⟨hx.2, hx₂⟩, hx.1⟩
    have hcolumn := ((ContinuousLinearMap.apply ℂ (V₁ × V₂)
      (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contDiff.comp_contMDiffAt hL
    have hfirst := ((ContinuousLinearMap.fst ℂ V₁ V₂).restrictScalars ℝ).contDiff.comp_contMDiffAt
      hcolumn
    apply (hfirst.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((d₁.open_baseSet.inter d₂.open_baseSet).inter f.open_baseSet).mem_nhds
      ⟨⟨hx.2, hx₂⟩, hx.1⟩] with y hy
    exact (congrArg Prod.fst (hvalue y hy (EuclideanSpace.single j 1))).symm
  · intro f _ d₂ _ j x hx
    let d₁ := trivializationAt V₁ E₁ x
    have hx₁ : x ∈ d₁.baseSet := mem_baseSet_trivializationAt _ _ _
    obtain ⟨L, hL, hvalue⟩ := hinverse d₁ d₂ f x ⟨⟨hx₁, hx.2⟩, hx.1⟩
    have hcolumn := ((ContinuousLinearMap.apply ℂ (V₁ × V₂)
      (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ).contDiff.comp_contMDiffAt hL
    have hsecond := ((ContinuousLinearMap.snd ℂ V₁ V₂).restrictScalars ℝ).contDiff.comp_contMDiffAt
      hcolumn
    apply (hsecond.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [((d₁.open_baseSet.inter d₂.open_baseSet).inter f.open_baseSet).mem_nhds
      ⟨⟨hx₁, hx.2⟩, hx.1⟩] with y hy
    exact (congrArg Prod.snd (hvalue y hy (EuclideanSpace.single j 1))).symm

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₂) E₂]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- The specified smooth decomposition identifies the actual metric L² spaces with their
native Banach product, with the original inverse projections on smooth sections. -/
theorem exists_l2Equiv_of_smoothBundleSum
    (e : ∀ x, (E₁ x × E₂ x) ≃ₗ[ℂ] E x)
    (h₁ : IsSmoothBundleMap (n := n) (r := r₁) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))))
    (h₂ : IsSmoothBundleMap (n := n) (r := r₂) (q := r)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))))
    (k₁ : SmoothHermitianMetric (n := n) (r := r₁) E₁)
    (k₂ : SmoothHermitianMetric (n := n) (r := r₂) E₂)
    (k : SmoothHermitianMetric (n := n) (r := r) E) :
    let p₁ := smoothSectionMap
      (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
      (isSmoothBundleMap_sumInverse e h₁ h₂).1
    let p₂ := smoothSectionMap
      (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
      (isSmoothBundleMap_sumInverse e h₁ h₂).2
    ∃ U : k.L2SectionSpace μ ≃L[ℂ] (k₁.L2SectionSpace μ × k₂.L2SectionSpace μ),
      ∀ u, U (k.smoothToL2 μ u) =
        (k₁.smoothToL2 μ (p₁ u), k₂.smoothToL2 μ (p₂ u)) := by
  classical
  let I₁ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E₁ x) (E₂ x))) h₁
  let I₂ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E₁ x) (E₂ x))) h₂
  let D₁ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (LinearMap.fst ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).1
  let D₂ := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (LinearMap.snd ℂ (E₁ x) (E₂ x)).comp (e x).symm.toLinearMap)
    (isSmoothBundleMap_sumInverse e h₁ h₂).2
  let A := (I₁.metricL2Extension k₁ k).coprod (I₂.metricL2Extension k₂ k)
  let B := (D₁.metricL2Extension k k₁).prod (D₂.metricL2Extension k k₂)
  have hB (u : smoothSections (n := n) (r := r) E) :
      B (k.smoothToL2 μ u) =
        (k₁.smoothToL2 μ (D₁.toLinearMap u), k₂.smoothToL2 μ (D₂.toLinearMap u)) := by
    exact Prod.ext (D₁.metricL2Extension_smooth k k₁ u)
      (D₂.metricL2Extension_smooth k k₂ u)
  have hA (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := n) (r := r₂) E₂) :
      A (k₁.smoothToL2 μ u, k₂.smoothToL2 μ v) =
        k.smoothToL2 μ (I₁.toLinearMap u + I₂.toLinearMap v) := by
    change I₁.metricL2Extension k₁ k (k₁.smoothToL2 μ u) +
      I₂.metricL2Extension k₂ k (k₂.smoothToL2 μ v) = _
    rw [I₁.metricL2Extension_smooth, I₂.metricL2Extension_smooth, map_add]
  -- The two inverse identities first hold on the exact same smooth section maps.
  have hsum (u : smoothSections (n := n) (r := r) E) :
      I₁.toLinearMap (D₁.toLinearMap u) + I₂.toLinearMap (D₂.toLinearMap u) = u := by
    apply Subtype.ext
    funext x
    change e x (((e x).symm (u.val x)).1, 0) +
      e x (0, ((e x).symm (u.val x)).2) = u.val x
    rw [← map_add]
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using
      (e x).apply_symm_apply (u.val x)
  have hproj (u : smoothSections (n := n) (r := r₁) E₁)
      (v : smoothSections (n := n) (r := r₂) E₂) :
      (D₁.toLinearMap (I₁.toLinearMap u + I₂.toLinearMap v),
        D₂.toLinearMap (I₁.toLinearMap u + I₂.toLinearMap v)) = (u, v) := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      change ((e x).symm (e x (u.val x, 0) + e x (0, v.val x))).1 = u.val x
      rw [← map_add, (e x).symm_apply_apply]
      simp only [Prod.mk_add_mk, add_zero]
    · apply Subtype.ext
      funext x
      change ((e x).symm (e x (u.val x, 0) + e x (0, v.val x))).2 = v.val x
      rw [← map_add, (e x).symm_apply_apply]
      simp only [Prod.mk_add_mk, zero_add]
  have hAB : A.comp B = ContinuousLinearMap.id ℂ (k.L2SectionSpace μ) := by
    apply DFunLike.coe_injective
    apply (k.denseRange_smoothToL2 μ).equalizer (A.comp B).continuous
      (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)).continuous
    funext u
    change A (B (k.smoothToL2 μ u)) = k.smoothToL2 μ u
    rw [hB, hA, hsum]
  have hBA : B.comp A = ContinuousLinearMap.id ℂ
      (k₁.L2SectionSpace μ × k₂.L2SectionSpace μ) := by
    apply DFunLike.coe_injective
    apply ((k₁.denseRange_smoothToL2 μ).prodMap
      (k₂.denseRange_smoothToL2 μ)).equalizer (B.comp A).continuous
        (ContinuousLinearMap.id ℂ (k₁.L2SectionSpace μ × k₂.L2SectionSpace μ)).continuous
    funext z
    change B (A (k₁.smoothToL2 μ z.1, k₂.smoothToL2 μ z.2)) =
      (k₁.smoothToL2 μ z.1, k₂.smoothToL2 μ z.2)
    rw [hA, hB]
    exact Prod.ext (congrArg (k₁.smoothToL2 μ) (congrArg Prod.fst (hproj z.1 z.2)))
      (congrArg (k₂.smoothToL2 μ) (congrArg Prod.snd (hproj z.1 z.2)))
  let U : k.L2SectionSpace μ ≃L[ℂ] (k₁.L2SectionSpace μ × k₂.L2SectionSpace μ) :=
    { B.toLinearMap with
      invFun := A
      left_inv := fun x ↦ DFunLike.congr_fun hAB x
      right_inv := fun y ↦ DFunLike.congr_fun hBA y
      continuous_toFun := B.continuous
      continuous_invFun := A.continuous }
  exact ⟨U, hB⟩

end AtiyahSinger
