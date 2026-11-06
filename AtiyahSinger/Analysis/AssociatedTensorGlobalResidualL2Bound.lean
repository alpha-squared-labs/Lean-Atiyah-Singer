/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalRemainderBound
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.NativePresentationChartCutoff

/-!
# Global L² bounds for the actual zero-order vertical residuals

Public module ID: M0149.

The actual residuals of the original sphere decomposition act in the same
normalized principal charts and retain the original base partition support.
Compact base plateaus are constructed internally. The supplied zero-order
sphere realizations belong to the literal residuals; no smoothing hypothesis
is imposed. The specified native metrics bound those same upstairs residuals
and their finite sum. This applies to the order-zero difference between the
original sphere PDO and its fixed full-symbol quantization in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
  [T2Space B]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

include k k' in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3600000 in
-- Normalize the original zero-order residuals and their finite base return maps.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual supported zero-order residuals and their finite sum have global native L² bounds. -/
theorem exists_associatedSphereTensorVerticalResidual_global_l2_bound
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ j, tsupport (J.cutoff j) ⊆ (S.trivialization (b j)).baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    ∀ (Q : AtlasPseudodifferentialOperator A A' 1)
      (Npiece : Fin J.size → ℕ)
      (Ppiece : ∀ j : Fin J.size, Fin (Npiece j) → AtlasPseudodifferentialPiece A A' 1)
      (R₀ : ∀ _j : Fin J.size, L.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
        L'.toAtlasBundlePresentation.SobolevSpace 0),
      (∀ j u, R₀ j (L.toAtlasBundlePresentation.smoothToSobolev 0 u) =
        L'.toAtlasBundlePresentation.smoothToSobolev 0
          ((Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap) u)) →
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
      letI := associatedSphereChartedSpace S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI := isManifold_linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      letI (x : B) : FiniteDimensional ℂ (E x) :=
        VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
      let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
      let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
      ∀ W : Fin J.size → AT.smoothSections →ₗ[ℂ] AT'.smoothSections,
        (∀ j (w : AT.smoothSections) z,
          πS z ∉ tsupport (J.cutoff j) → (W j w).val z = 0) →
        (∀ j (w : AT.smoothSections) x, x ∈ (J.chart j).source →
          x ∈ (S.trivialization (b j)).baseSet → x ∈ (J.frame j).baseSet → ∀ y : Y,
            let q := (S.trivialization (b j)).toOpenPartialHomeomorph.symm (x, 1)
            (W j w).val (associatedBundleMk G P Y q y) =
              (J.cutoff j x : ℂ) • associatedSphereTensorFiberEquiv S E σ' q y
                ((tensorSectionOperator (E (projection q)) A.smoothSections A'.smoothSections
                  (Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap)
                  (associatedSphereTensorFiberRestriction (a := a) S E A σ hA q w)).val y)) →
        ∀ (_G₀ : AtlasBundlePresentation AT) (_G₀' : AtlasBundlePresentation AT')
          (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
          (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
          (N N' : SmoothFiniteComplexBundle (n := n + r) Z)
          (kGlobal : SmoothHermitianMetric (n := n + r) (r := N.rank) N.Fiber)
          (kGlobal' : SmoothHermitianMetric (n := n + r) (r := N'.rank) N'.Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
          letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
          ∀ (e : Iso T N.Fiber)
            (he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas N.Fiber)
              e.toHom.linearMap)
            (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N.Fiber) AT
              e.symm.toHom.linearMap)
            (e' : Iso T' N'.Fiber)
            (he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
              e'.toHom.linearMap)
            (hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas N'.Fiber) AT'
              e'.symm.toHom.linearMap),
            (∀ (z : Z) (v w : T z),
              kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
                (l.toCore z).inner v w) →
            (∀ (z : Z) (v w : T' z),
              kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
                (l'.toCore z).inner v w) →
            let sectionEquiv :=
              (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
                (nativeSmoothSectionLinearEquiv N.Fiber)
            let sectionEquiv' :=
              (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
                e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
            let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
            let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
            ∃ C : Fin J.size → ℝ, (∀ j, 0 ≤ C j) ∧
              (∀ j (w : AT.smoothSections), ‖inclusion' (W j w)‖ ≤ C j * ‖inclusion w‖) ∧
              ∀ w : AT.smoothSections,
                ‖inclusion' (∑ j, W j w)‖ ≤ (∑ j, C j) * ‖inclusion w‖ := by
  classical
  -- The original finite compactly supported partition already makes the base compact.
  let : CompactSpace B := by
    refine ⟨?_⟩
    have hcompact : IsCompact (⋃ j : Fin J.size, tsupport (J.cutoff j)) :=
      isCompact_iUnion J.compact_support
    apply hcompact.of_isClosed_subset isClosed_univ
    intro x _
    by_contra hx
    have hzero (j : Fin J.size) : J.cutoff j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Set.mem_iUnion.mpr ⟨j, h⟩))
    have hsum := J.sum_cutoff x
    simp [hzero] at hsum
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let := isManifold_linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
  dsimp only
  intro Q Npiece Ppiece R₀ hR₀ W hWzero hreturn G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η hη
  let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N'.rank)) N'.Fiber
  intro e he hi e' he' hi' hpair hpair'
  let sectionEquiv :=
    (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas N.Fiber) e he hi).trans
      (nativeSmoothSectionLinearEquiv N.Fiber)
  let sectionEquiv' :=
    (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas N'.Fiber)
      e' he' hi').trans (nativeSmoothSectionLinearEquiv N'.Fiber)
  let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
  let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
  -- Enlarge the compact support inside the same chart, frame, and principal trivialization.
  have hbound (j : Fin J.size) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : AT.smoothSections,
      ‖inclusion' (W j w)‖ ≤ C * ‖inclusion w‖ := by
    let c := J.chart j
    let K := c '' tsupport (J.cutoff j)
    have hK : IsCompact K := (J.compact_support j).image_of_continuousOn
      (c.continuousOn.mono (fun x hx ↦ (J.support_subset j hx).1))
    let U := c.target ∩ c.symm ⁻¹'
      ((J.frame j).baseSet ∩ (S.trivialization (b j)).baseSet)
    have hU : IsOpen U := c.isOpen_inter_preimage_symm
      ((J.frame j).open_baseSet.inter (S.trivialization (b j)).open_baseSet)
    have hKU : K ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hxc := (J.support_subset j hx).1
      refine ⟨c.map_source hxc, ?_⟩
      change c.symm (c x) ∈ (J.frame j).baseSet ∩ (S.trivialization (b j)).baseSet
      rw [c.left_inv hxc]
      exact ⟨(J.support_subset j hx).2, hJ j hx⟩
    obtain ⟨γ, hγ, hcγ, hsγ, hγone⟩ := exists_compact_cutoff_one_near K U hK hU hKU
    let input : BundleChartCutoff (r := a) E c := {
      J.chartCutoff E j with
      cutoff := γ
      smooth_cutoff := hγ
      compact_support := hcγ
      support_subset := fun x hx ↦ ⟨(hsγ hx).1, (hsγ hx).2.1⟩ }
    have hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization (b j)).baseSet := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hsγ hx).2.2
    have hbase : IsCompact (c.symm '' tsupport input.cutoff) :=
      input.compact_support.image_of_continuousOn
        (c.continuousOn_symm.mono (fun x hx ↦ (input.support_subset hx).1))
    obtain ⟨U₁, hU₁, hKU₁, hU₁base, hU₁compact⟩ :=
      exists_open_between_and_isCompact_closure hbase
        (S.trivialization (b j)).open_baseSet hinput
    obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓡 n) (n := ⊤) hbase.isClosed (hKU₁.trans hU₁.subset_interior_closure)
    have hχsupport : tsupport χ ⊆ (S.trivialization (b j)).baseSet := by
      apply Set.Subset.trans ?_ hU₁base
      apply closure_minimal ?_ hU₁compact.isClosed
      intro x hx
      by_contra hn
      exact hx (hχzero x hn)
    have hχone' (x : B) (hx : x ∈ c.symm '' tsupport input.cutoff) : χ x = 1 :=
      hχone.self_of_nhdsSet x hx
    have hW (w : AT.smoothSections) (z : Z) (hz : (W j w).val z ≠ 0) :
        πS z ∈ c.symm '' {x | input.cutoff x = 1} := by
      have hs : πS z ∈ tsupport (J.cutoff j) := by
        by_contra hn
        exact hz (hWzero j w z hn)
      refine ⟨c (πS z), ?_, c.left_inv (J.support_subset j hs).1⟩
      exact interior_subset (hγone ⟨πS z, hs, rfl⟩)
    -- Use the supplied zero-order realization of this literal sphere residual.
    obtain ⟨Cθ, hθ⟩ := (J.compact_support j).exists_bound_of_continuous
      (J.smooth_cutoff j).continuous
    have hθ' (x : B) : ‖J.cutoff j x‖ ≤ max Cθ 0 := (hθ x).trans (le_max_left _ _)
    exact exists_associatedSphereTensorFiberOperator_global_l2_bound (a := a)
      S E F F' σ σ' hσ hσ' k k' ν L L' (b j) input (J.chart_mem_atlas j) hinput
      χ χ.contMDiff hχsupport hχone' (J.cutoff j) (max Cθ 0) (le_max_right _ _) hθ'
      (Q.toLinearMap - ∑ i, (Ppiece j i).toLinearMap) (R₀ j) (hR₀ j) (W j) hW (hreturn j)
      G₀ G₀' l hl l' hl' N N' kGlobal kGlobal' η e he hi e' he' hi' hpair hpair'
  choose C hC hCbound using hbound
  refine ⟨C, hC, hCbound, ?_⟩
  intro w
  -- Finite summation preserves the specified inclusion and every original residual witness.
  have hfinite (m : ℕ) (f : Fin m → kGlobal'.L2SectionSpace η)
      (c : Fin m → ℝ) (t : ℝ) (hf : ∀ j, ‖f j‖ ≤ c j * t) :
      ‖∑ j, f j‖ ≤ (∑ j, c j) * t := by
    have hsum := (norm_sum_le Finset.univ f).trans (Finset.sum_le_sum (fun j _ ↦ hf j))
    exact hsum.trans_eq (Finset.sum_mul Finset.univ c t).symm
  exact (congrArg norm (map_sum inclusion' (fun j ↦ W j w) Finset.univ)).trans_le
    (hfinite J.size (fun j ↦ inclusion' (W j w)) C ‖inclusion w‖ (fun j ↦ hCbound j w))

end AtiyahSinger
