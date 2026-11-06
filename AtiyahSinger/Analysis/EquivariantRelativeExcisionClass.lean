/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantRelativeSymbolKClass
public import AtiyahSinger.Geometry.DiffeomorphBundlePullback
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Geometry.OpenEmbeddingBundleIso
public import AtiyahSinger.Geometry.SmoothEquivariantPullback
public import AtiyahSinger.Topology.EquivariantControlledOpenClass
public import AtiyahSinger.Topology.EquivariantPullbackTransport

/-!
# The original common-open class of transported relative symbols

Public module ID: M0562.

The actual smooth fiber comparisons are lifted through the two native cotangent
maps. Their moving-fiber squares retain the given actions, and the full boundary
square identifies the target class with extension of the same source restriction.
The specified zero-section controls are used, including exterior zero covectors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space M] [T2Space N]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Both pullback reassociations preserve the original fiber vectors and their actions.
/-- The relative boundary square preserves the full class through the same common open set. -/
theorem CompactSupportTriple.kZeroClass_eq_openPushforward_restrict_of_transport
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (E' F' : SmoothFiniteComplexBundle (n := n) N)
    (U : Opens M) (V : Opens N)
    [MulAction G U] [ContinuousSMul G U]
    [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
    (α : ∀ x : U, E.Fiber x.val ≃ₗ[ℂ] E'.Fiber (e x).val)
    (β : ∀ x : U, F.Fiber x.val ≃ₗ[ℂ] F'.Fiber (e x).val)
    (hα : IsSmoothBundleMap (M := U) (n := n) (r := E.rank) (q := E'.rank)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber))
      (F := ((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ E'.Fiber))
      (fun x ↦ (α x).toLinearMap))
    (hβ : IsSmoothBundleMap (M := U) (n := n) (r := F.rank) (q := F'.rank)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber))
      (F := ((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ F'.Fiber))
      (fun x ↦ (β x).toLinearMap))
    (K : Set M) (hKU : K ⊆ U)
    (s : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (t : GlobalSymbolFunction (n := n) E'.Fiber F'.Fiber)
    (hst : ∀ (x : U) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val),
      t (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (α x v) = β x (s x.val ξ v)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let pM := cotangentProjection (n := n) (M := M)
    let pN := cotangentProjection (n := n) (M := N)
    let f : C(CotangentTotalSpace (n := n) (M := U),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
    let g : C(CotangentTotalSpace (n := n) (M := U),
        CotangentTotalSpace (n := n) (M := N)) :=
      ⟨fun z ↦ cotangentOpenInclusion V (cotangentDiffeomorph e z),
        (isOpenEmbedding_cotangentOpenInclusion V).continuous.comp
          (cotangentDiffeomorph e).continuous⟩
    ∀ (hfg : ∀ (a : G) (z : CotangentTotalSpace (n := n) (M := U)),
        f (a • z) = a • f z)
      (hgg : ∀ (a : G) (z : CotangentTotalSpace (n := n) (M := U)),
        g (a • z) = a • g z)
      (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber)
      (τE : EquivariantStructure G E'.Fiber) (τF : EquivariantStructure G F'.Fiber)
      (_hαg : ∀ (a : G) (x : U) (v : E.Fiber x.val),
        (⟨(e (a • x)).val, α (a • x)
          (cast (congrArg E.Fiber (hU a x).symm) (σE.linearMap a x.val v))⟩ :
            TotalSpace Unit E'.Fiber) =
          ⟨a • (e x).val, τE.linearMap a (e x).val (α x v)⟩)
      (_hβg : ∀ (a : G) (x : U) (v : F.Fiber x.val),
        (⟨(e (a • x)).val, β (a • x)
          (cast (congrArg F.Fiber (hU a x).symm) (σF.linearMap a x.val v))⟩ :
            TotalSpace Unit F'.Fiber) =
          ⟨a • (e x).val, τF.linearMap a (e x).val (β x v)⟩)
      (a : CompactSupportTriple ((pM : _ → M) *ᵖ E.Fiber) ((pM : _ → M) *ᵖ F.Fiber))
      (b : CompactSupportTriple ((pN : _ → N) *ᵖ E'.Fiber) ((pN : _ → N) *ᵖ F'.Fiber))
      (ha : a.IsEquivariant (σE.pullback pM (fun _ _ ↦ rfl))
        (σF.pullback pM (fun _ _ ↦ rfl)))
      (hb : b.IsEquivariant (τE.pullback pN (fun _ _ ↦ rfl))
        (τF.pullback pN (fun _ _ ↦ rfl)))
      (_hac : a.control = cotangentZeroSection '' K)
      (_hbc : b.control = cotangentZeroSection ''
        ((fun x : U ↦ (e x).val) '' ((Subtype.val : U → M) ⁻¹' K)))
      (_has : ∀ (z : (a.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
        (v : E.Fiber z.val.proj), a.boundary.linearEquiv z v = s z.val.proj z.val.snd v)
      (_hbt : ∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := N))))
        (v : E'.Fiber z.val.proj), b.boundary.linearEquiv z v = t z.val.proj z.val.snd v),
      ∃ hrange : a.control ⊆ Set.range f,
        (EquivariantSupportBundleTriple.ofBoundary
          ((FiniteBundle.ofFamily E'.Fiber).pullback pN)
          ((FiniteBundle.ofFamily F'.Fiber).pullback pN) b
          (τE.pullback pN (fun _ _ ↦ rfl)) (τF.pullback pN (fun _ _ ↦ rfl)) hb).kZeroClass =
        equivariantSupportTripleKZeroOpenPushforward g
          ((isOpenEmbedding_cotangentOpenInclusion V).comp
            (cotangentDiffeomorph e).isOpenEmbedding) hgg
          (((EquivariantSupportBundleTriple.ofBoundary
            ((FiniteBundle.ofFamily E.Fiber).pullback pM)
            ((FiniteBundle.ofFamily F.Fiber).pullback pM) a
            (σE.pullback pM (fun _ _ ↦ rfl)) (σF.pullback pM (fun _ _ ↦ rfl)) ha).openRestrict
            f (isOpenEmbedding_cotangentOpenInclusion U) hfg hrange).kZeroClass) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E'.rank)) E'.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  dsimp only
  intro hfg hgg σE σF τE τF hαg hβg a b ha hb hac hbc has hbt
  let X := CotangentTotalSpace (n := n) (M := U)
  let Y := CotangentTotalSpace (n := n) (M := M)
  let Z := CotangentTotalSpace (n := n) (M := N)
  let pU : C(X, U) := cotangentProjection
  let pM : C(Y, M) := cotangentProjection
  let pN : C(Z, N) := cotangentProjection
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let j : C(U, N) := (ContinuousMap.subtypeVal (V : Set N)).comp ⟨e, e.continuous⟩
  let f : C(X, Y) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let g : C(X, Z) :=
    ⟨fun z ↦ cotangentOpenInclusion V (cotangentDiffeomorph e z),
      (isOpenEmbedding_cotangentOpenInclusion V).continuous.comp
        (cotangentDiffeomorph e).continuous⟩
  -- Native smooth maps become the same continuous maps in the iterated pullback topology.
  have liftIso (D : SmoothFiniteComplexBundle (n := n) M)
      (D' : SmoothFiniteComplexBundle (n := n) N)
      (δ : ∀ x : U, D.Fiber x.val ≃ₗ[ℂ] D'.Fiber (e x).val)
      (hδ : IsSmoothBundleMap (M := U) (n := n) (r := D.rank) (q := D'.rank)
        (E := (i : U → M) *ᵖ D.Fiber)
        (F := ((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
          ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ D'.Fiber))
        (fun x ↦ (δ x).toLinearMap)) :
      letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
      ∃ A : Iso ((f : X → Y) *ᵖ ((pM : Y → M) *ᵖ D.Fiber))
          ((g : X → Z) *ᵖ ((pN : Z → N) *ᵖ D'.Fiber)),
        ∀ (z : X) (v : D.Fiber z.proj.val), A.linearEquiv z v = δ z.proj v := by
    let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
    let DU := D.pullback i contMDiff_subtype_val
    have h := IsSmoothBundleMap.exists_iso_openEmbedding DU D' V ⟨e, e.continuous⟩ δ hδ
    let tP : TopologicalSpace (TotalSpace Unit ((i : U → M) *ᵖ D.Fiber)) :=
      @Pullback.TotalSpace.topologicalSpace M Unit D.Fiber U i _
        (modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber)
    have htop : modelTopology (EuclideanSpace ℂ (Fin D.rank)) ((i : U → M) *ᵖ D.Fiber) =
        tP := by
      simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
        induced_inf, induced_compose, tP, modelTopology]
      rfl
    change letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) ((i : U → M) *ᵖ D.Fiber);
      ∃ B : Iso ((i : U → M) *ᵖ D.Fiber) ((j : U → N) *ᵖ D'.Fiber),
        ∀ x v, B.linearEquiv x v = δ x v at h
    rw [htop] at h
    obtain ⟨B, hB⟩ := h
    let R := (pullbackCompIso (E := D.Fiber) pM f).trans
      (pullbackCompIso (E := D.Fiber) i pU).symm
    let S := (pullbackCompIso (E := D'.Fiber) j pU).trans
      (pullbackCompIso (E := D'.Fiber) pN g).symm
    refine ⟨R.trans ((B.pullback pU).trans S), ?_⟩
    intro z v
    have hR : R.linearEquiv z v = v := by
      apply ((pullbackCompIso (E := D.Fiber) i pU).linearEquiv z).injective
      change (pullbackCompIso (E := D.Fiber) i pU).linearEquiv z
        (((pullbackCompIso (E := D.Fiber) i pU).linearEquiv z).symm
          ((pullbackCompIso (E := D.Fiber) pM f).linearEquiv z v)) = _
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    have hS (w : D'.Fiber (e z.proj).val) : S.linearEquiv z w = w := by
      apply ((pullbackCompIso (E := D'.Fiber) pN g).linearEquiv z).injective
      change (pullbackCompIso (E := D'.Fiber) pN g).linearEquiv z
        (((pullbackCompIso (E := D'.Fiber) pN g).linearEquiv z).symm
          ((pullbackCompIso (E := D'.Fiber) j pU).linearEquiv z w)) = _
      rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
    change S.linearEquiv z (B.linearEquiv z.proj (R.linearEquiv z v)) = _
    rw [hR, hS, hB]
  obtain ⟨A, hA⟩ := liftIso E E' α hα
  obtain ⟨B, hB⟩ := liftIso F F' β hβ
  have intertwines (D : SmoothFiniteComplexBundle (n := n) M)
      (D' : SmoothFiniteComplexBundle (n := n) N)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        EquivariantStructure G D.Fiber)
      (τ : letI := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
        EquivariantStructure G D'.Fiber)
      (δ : ∀ x : U, D.Fiber x.val ≃ₗ[ℂ] D'.Fiber (e x).val)
      (hδg : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
        ∀ (a : G) (x : U) (v : D.Fiber x.val),
          (⟨(e (a • x)).val, δ (a • x)
            (cast (congrArg D.Fiber (hU a x).symm) (σ.linearMap a x.val v))⟩ :
              TotalSpace Unit D'.Fiber) =
            ⟨a • (e x).val, τ.linearMap a (e x).val (δ x v)⟩) :
      letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
      ∀ (C : Iso ((f : X → Y) *ᵖ ((pM : Y → M) *ᵖ D.Fiber))
          ((g : X → Z) *ᵖ ((pN : Z → N) *ᵖ D'.Fiber)))
        (hC : ∀ (z : X) (v : D.Fiber z.proj.val), C.linearEquiv z v = δ z.proj v),
        C.IsEquivariant ((σ.pullback pM (fun _ _ ↦ rfl)).pullback f hfg)
          ((τ.pullback pN (fun _ _ ↦ rfl)).pullback g hgg) := by
    let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
    intro C hC a z v
    let σC := (σ.pullback pM (fun _ _ ↦ rfl)).pullback f hfg
    let τC := (τ.pullback pN (fun _ _ ↦ rfl)).pullback g hgg
    have hv := (congrArg (Pullback.lift pM)
      (EquivariantStructure.pullback_lift_action (σ.pullback pM (fun _ _ ↦ rfl)) f hfg a z v)).trans
        (EquivariantStructure.pullback_lift_action σ pM (fun _ _ ↦ rfl) a (f z) v)
    have hcast : σC.linearMap a z v =
        cast (congrArg D.Fiber (hU a z.proj).symm) (σ.linearMap a z.proj.val v) := by
      have hh {y w : M} (hyw : y = w) (u : D.Fiber w) :
          (⟨y, cast (congrArg D.Fiber hyw.symm) u⟩ : TotalSpace Unit D.Fiber) =
            ⟨w, u⟩ := by
        subst w
        rfl
      exact TotalSpace.mk_injective ((a • z.proj : U).val)
        (hv.trans (hh (hU a z.proj) _).symm)
    have hw := (congrArg (Pullback.lift pN)
      (EquivariantStructure.pullback_lift_action
        (τ.pullback pN (fun _ _ ↦ rfl)) g hgg a z (δ z.proj v))).trans
        (EquivariantStructure.pullback_lift_action τ pN (fun _ _ ↦ rfl) a (g z) (δ z.proj v))
    change C.linearEquiv (a • z) (σC.linearMap a z v) =
      τC.linearMap a z (C.linearEquiv z v)
    rw [hC, hC, hcast]
    exact TotalSpace.mk_injective ((e (a • z.proj)).val)
      ((hδg a z.proj v).trans hw.symm)
  have hAg := intertwines E E' σE τE α hαg A hA
  have hBg := intertwines F F' σF τF β hβg B hB
  have hrange : a.control ⊆ Set.range f := by
    rw [hac]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨cotangentZeroSection (⟨x, hKU hx⟩ : U), rfl⟩
  let aM := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily E.Fiber).pullback pM)
    ((FiniteBundle.ofFamily F.Fiber).pullback pM) a
    (σE.pullback pM (fun _ _ ↦ rfl)) (σF.pullback pM (fun _ _ ↦ rfl)) ha
  let aU := aM.openRestrict f (isOpenEmbedding_cotangentOpenInclusion U) hfg hrange
  let bN := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily E'.Fiber).pullback pN)
    ((FiniteBundle.ofFamily F'.Fiber).pullback pN) b
    (τE.pullback pN (fun _ _ ↦ rfl)) (τF.pullback pN (fun _ _ ↦ rfl)) hb
  have hcontrol : bN.1.datum.control ⊆ g '' aU.1.datum.control := by
    change b.control ⊆ g '' (f ⁻¹' a.control)
    rw [hac, hbc]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨cotangentZeroSection x, ⟨x.val, hx, rfl⟩, ?_⟩
    change (⟨(e x).val, (0 : CotangentFiber (n := n) x).comp _⟩ : Z) =
      ⟨(e x).val, 0⟩
    rw [ContinuousLinearMap.zero_comp]
  refine ⟨hrange, ?_⟩
  apply aU.kZeroClass_eq_openPushforward_of_boundary bN g
    ((isOpenEmbedding_cotangentOpenInclusion V).comp
      (cotangentDiffeomorph e).isOpenEmbedding) hgg hcontrol A B hAg hBg
  intro z hz hgz v
  change B.linearEquiv z ((a.boundary.pullback f).linearEquiv ⟨z, hz⟩ v) =
    b.boundary.linearEquiv ⟨g z, hgz⟩ (A.linearEquiv z v)
  rw [hA, hB]
  rw [RelativeTriple.pullback_apply, has, hbt]
  exact (hst z.proj z.snd v).symm

end AtiyahSinger
