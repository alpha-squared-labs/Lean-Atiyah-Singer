/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity
public import AtiyahSinger.Analysis.EllipticSymbolTriple
public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Geometry.EquivariantBoundarySmoothing
public import AtiyahSinger.Geometry.SmoothEquivariantPullback
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Geometry.SmoothBundleMapPullback
public import AtiyahSinger.Topology.RealBundleSupport

/-!
# Smooth exterior zero-fiber data on the original cotangent bundles

Public module ID: M0497.

Smooth an equivariant boundary while keeping its original compact control.
Evaluation at exterior zero covectors then gives a smooth base isomorphism.
The same controlled cylinder retains the source support class when restricted
through a common open image. This module is the native-cotangent implementation
bridge from equivariant boundary smoothing to relative analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT hSC hE hF hG hGC hGT hAction hσE hσF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in
-- The same boundary and zero-fiber evaluation pass through three native pullback models.
/-- Smooth a cotangent boundary with its exact control and smooth exterior zero-fiber values. -/
theorem CompactSupportTriple.exists_equivariant_smooth_exterior_cotangent_boundary
    (K : Set M) (hK : IsCompact K)
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F))
    (hControl : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.control = cotangentZeroSection '' K)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
      letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
        ContMDiffSMul.continuousSMul (I := IG)
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      a.IsEquivariant (σE.pullback cotangentProjection (fun _ _ ↦ rfl))
        (σF.pullback cotangentProjection (fun _ _ ↦ rfl))) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃ b : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F),
      b.control = a.control ∧
      b.IsEquivariant (σE.pullback cotangentProjection (fun _ _ ↦ rfl))
        (σF.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
      (∃ H : CompactSupportTriple.EquivariantHomotopy
        (σE.pullback cotangentProjection (fun _ _ ↦ rfl))
        (σF.pullback cotangentProjection (fun _ _ ↦ rfl)) a b,
        H.control = a.control) ∧
      let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
      ∃ τ : RelativeTriple E F Kᶜ,
        IsSmoothBundleMap (n := n) (r := r) (q := q) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E))
          (F := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F))
          (fun x ↦ (τ.linearEquiv x).toLinearMap) ∧
        ∀ (x : W) (hz : cotangentZeroSection x.val ∈ b.controlᶜ),
          τ.linearEquiv x = b.boundary.linearEquiv ⟨cotangentZeroSection x.val, hz⟩ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let CT := CotangentTotalSpace (n := n) (M := M)
  let V₀ := EuclideanSpace ℝ (Fin n)
  let W₀ := V₀ × CotangentModel n
  let I₀ := 𝓘(ℝ, V₀).prod 𝓘(ℝ, CotangentModel n)
  let : RealBundle.IsFiniteRank (CotangentModel n)
      (CotangentFiber (n := n) (M := M)) :=
    RealBundle.isFiniteRank_of_vectorBundle _ _
  let : SecondCountableTopology CT :=
    RealBundle.secondCountableTopology_totalSpace
      (CotangentModel n) (CotangentFiber (M := M))
  have hCT : IsManifold I₀ ∞ CT := inferInstance
  let : ChartedSpace W₀ CT := inferInstanceAs (ChartedSpace
    (ModelProd V₀ (CotangentModel n)) CT)
  let : IsManifold 𝓘(ℝ, W₀) ∞ CT := by
    rw [modelWithCornersSelf_prod]
    exact hCT
  let R : CotangentModel n ≃L[ℝ] V₀ :=
    (InnerProductSpace.toDual ℝ V₀).symm.toContinuousLinearEquiv
  let e : W₀ ≃L[ℝ] EuclideanSpace ℝ (Fin (n + n)) :=
    ((ContinuousLinearEquiv.refl ℝ V₀).prodCongr R).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := n)).symm
  let := linearModelChartedSpace e CT
  let := isManifold_linearModelChartedSpace e CT
  let d := linearModelDiffeomorph e CT
  have hπ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n)))
      𝓘(ℝ, V₀) ∞ (cotangentProjection (n := n) (M := M)) := by
    have hp : ContMDiff I₀ 𝓘(ℝ, V₀) ∞
        (cotangentProjection (n := n) (M := M)) :=
      contMDiff_proj (CotangentFiber (n := n) (M := M))
    have hi : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) I₀ ∞
        (id : CT → CT) := by
      dsimp only [I₀]
      rw [← modelWithCornersSelf_prod]
      exact d.contMDiff_invFun
    exact hp.comp hi
  have hforward : ContMDiff I₀ 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞
      (id : CT → CT) := by
    dsimp only [I₀]
    rw [← modelWithCornersSelf_prod]
    exact d.contMDiff_toFun
  have hreverse : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) I₀ ∞
      (id : CT → CT) := by
    dsimp only [I₀]
    rw [← modelWithCornersSelf_prod]
    exact d.contMDiff_invFun
  let : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞ G CT := by
    constructor
    have hact : ContMDiff (IG.prod I₀) I₀ ∞ (fun z : G × CT ↦ z.1 • z.2) :=
      contMDiff_smul
    exact hforward.comp (hact.comp
      (contMDiff_fst.prodMk (hreverse.comp contMDiff_snd)))
  -- Pull back the original frames and actions through the same smooth projection.
  -- The explicit topology equalities allow boundary smoothing on those exact bundles.
  let p : C(CT, M) := cotangentProjection (n := n) (M := M)
  let E' := (p : CT → M) *ᵖ E
  let F' := (p : CT → M) *ᵖ F
  let : IsSmoothComplexBundle (n := n + n) (r := r) E' :=
    isSmoothComplexBundle_pullback E p hπ
  let : IsSmoothComplexBundle (n := n + n) (r := q) F' :=
    isSmoothComplexBundle_pullback F p hπ
  let tE' : TopologicalSpace (TotalSpace Unit E') :=
    @Pullback.TotalSpace.topologicalSpace M Unit E CT (p : CT → M) _
      (modelTopology (EuclideanSpace ℂ (Fin r)) E)
  let tF' : TopologicalSpace (TotalSpace Unit F') :=
    @Pullback.TotalSpace.topologicalSpace M Unit F CT (p : CT → M) _
      (modelTopology (EuclideanSpace ℂ (Fin q)) F)
  have hEtop : modelTopology (EuclideanSpace ℂ (Fin r)) E' = tE' := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tE', modelTopology]
    rfl
  have hFtop : modelTopology (EuclideanSpace ℂ (Fin q)) F' = tF' := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tF', modelTopology]
    rfl
  let PE (L : ∀ (g : G) (z : CT), E' z →ₗ[ℂ] E' (g • z)) : Prop :=
    ∀ (e₀ f₀ : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E'))
      [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀], ∀ j : Fin r,
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun z : G × CT ↦
          (f₀ ⟨z.1 • z.2, L z.1 z.2
            (e₀.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2)
        {z : G × CT | z.2 ∈ e₀.baseSet ∧ z.1 • z.2 ∈ f₀.baseSet}
  let PF (L : ∀ (g : G) (z : CT), F' z →ₗ[ℂ] F' (g • z)) : Prop :=
    ∀ (e₀ f₀ : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F'))
      [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀], ∀ j : Fin q,
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
        (fun z : G × CT ↦
          (f₀ ⟨z.1 • z.2, L z.1 z.2
            (e₀.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2)
        {z : G × CT | z.2 ∈ e₀.baseSet ∧ z.1 • z.2 ∈ f₀.baseSet}
  let ρE := σE.pullback p (fun _ _ ↦ rfl)
  let ρF := σF.pullback p (fun _ _ ↦ rfl)
  have hρE : PE ρE.linearMap := by
    rintro _ _ ⟨e₀, he, rfl⟩ ⟨f₀, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : G × CT ↦ (z.1, p z.2)) :=
      contMDiff_fst.prodMk (hπ.comp contMDiff_snd)
    apply ((hσE e₀ f₀ j).comp hi.contMDiffOn (fun z hz ↦ hz)).congr
    intro z hz
    have heq : (e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1) =
        e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1) := by
      rw [(e₀.pullback p).symmL_apply (R := ℂ) hz.1,
        e₀.symmL_apply (R := ℂ) hz.1, (e₀.pullback p).symm_apply hz.1]
      rfl
    change (f₀ ⟨z.1 • p z.2, σE.linearMap z.1 (p z.2)
      ((e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2 =
        (f₀ ⟨z.1 • p z.2, σE.linearMap z.1 (p z.2)
          (e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  have hρF : PF ρF.linearMap := by
    rintro _ _ ⟨e₀, he, rfl⟩ ⟨f₀, hf, rfl⟩ j
    let := he
    let := hf
    have hi : ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))))
        (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun z : G × CT ↦ (z.1, p z.2)) :=
      contMDiff_fst.prodMk (hπ.comp contMDiff_snd)
    apply ((hσF e₀ f₀ j).comp hi.contMDiffOn (fun z hz ↦ hz)).congr
    intro z hz
    have heq : (e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1) =
        e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1) := by
      rw [(e₀.pullback p).symmL_apply (R := ℂ) hz.1,
        e₀.symmL_apply (R := ℂ) hz.1, (e₀.pullback p).symm_apply hz.1]
      rfl
    change (f₀ ⟨z.1 • p z.2, σF.linearMap z.1 (p z.2)
      ((e₀.pullback p).symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2 =
        (f₀ ⟨z.1 • p z.2, σF.linearMap z.1 (p z.2)
          (e₀.symmL ℂ (p z.2) (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  let Φ (tE : TopologicalSpace (TotalSpace Unit E'))
      (tF : TopologicalSpace (TotalSpace Unit F')) : Prop :=
    letI := tE
    letI := tF
    ∀ (τE : EquivariantStructure G E') (τF : EquivariantStructure G F'),
      PE τE.linearMap → PF τF.linearMap →
      ∀ (c : CompactSupportTriple E' F'), c.IsEquivariant τE τF →
      let W : TopologicalSpace.Opens CT :=
        ⟨c.controlᶜ, c.isCompact_control.isClosed.isOpen_compl⟩
      ∃ β : RelativeTriple E' F' c.controlᶜ,
        IsSmoothBundleMap (n := n + n) (r := r) (q := q) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set CT) : W → CT) *ᵖ E'))
          (F := ((ContinuousMap.subtypeVal (W : Set CT) : W → CT) *ᵖ F'))
          (fun z ↦ (β.linearEquiv z).toLinearMap) ∧
        let b : CompactSupportTriple E' F' :=
          { control := c.control
            isCompact_control := c.isCompact_control
            boundary := β }
        b.IsEquivariant τE τF ∧
          ∃ H : CompactSupportTriple.EquivariantHomotopy τE τF c b,
            H.control = c.control
  have hsmooth : Φ tE' tF' := by
    let hE' : IsSmoothComplexBundle (n := n + n) (r := r) E' := inferInstance
    let hF' : IsSmoothComplexBundle (n := n + n) (r := q) F' := inferInstance
    rw [← hEtop, ← hFtop]
    intro τE τF hτE hτF c hc
    let := hE'
    let := hF'
    exact c.exists_equivariant_smooth_boundary_homotopy (n := n + n) (r := r) (q := q)
      (E := E') (F := F') (hE := hE') (hF := hF') IG τE τF hτE hτF hc
  obtain ⟨β, hβsmooth, hβeq, Hβ, hHβ⟩ := hsmooth ρE ρF hρE hρF a ha
  let b : CompactSupportTriple E' F' := ⟨a.control, a.isCompact_control, β⟩
  let WK : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  let WC : Opens CT := ⟨a.controlᶜ, a.isCompact_control.isClosed.isOpen_compl⟩
  let iK : C(WK, M) := ContinuousMap.subtypeVal (WK : Set M)
  let iC : C(WC, CT) := ContinuousMap.subtypeVal (WC : Set CT)
  have hproj (z : CT) (hz : z ∈ a.control) : z.proj ∈ K := by
    rw [hControl] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hx
  let zK : C(WK, WC) :=
    ⟨fun x ↦ ⟨cotangentZeroSection x.val, fun hz ↦ x.property (hproj _ hz)⟩,
      (continuous_cotangentZeroSection.comp continuous_subtype_val).subtype_mk _⟩
  let τ : RelativeTriple E F Kᶜ := {
    linearEquiv x := β.linearEquiv (zK x)
    continuous_total := by
      have hin : Continuous (fun w : TotalSpace Unit ((iK : WK → M) *ᵖ E) ↦
          (⟨zK w.proj, w.snd⟩ : TotalSpace Unit ((iC : WC → CT) *ᵖ E'))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E' iC).continuous_iff]
        refine (zK.continuous.comp (Pullback.continuous_proj Unit E iK)).prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
        exact ((iC.continuous.comp zK.continuous).comp
          (Pullback.continuous_proj Unit E iK)).prodMk (Pullback.continuous_lift Unit E iK)
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F iK).continuous_iff]
      exact (Pullback.continuous_proj Unit E iK).prodMk
        ((Pullback.continuous_lift Unit F p).comp
          ((Pullback.continuous_lift Unit F' iC).comp (β.continuous_total.comp hin)))
    continuous_symm := by
      have hin : Continuous (fun w : TotalSpace Unit ((iK : WK → M) *ᵖ F) ↦
          (⟨zK w.proj, w.snd⟩ : TotalSpace Unit ((iC : WC → CT) *ᵖ F'))) := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F' iC).continuous_iff]
        refine (zK.continuous.comp (Pullback.continuous_proj Unit F iK)).prodMk ?_
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
        exact ((iC.continuous.comp zK.continuous).comp
          (Pullback.continuous_proj Unit F iK)).prodMk (Pullback.continuous_lift Unit F iK)
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E iK).continuous_iff]
      exact (Pullback.continuous_proj Unit F iK).prodMk
        ((Pullback.continuous_lift Unit E p).comp
          ((Pullback.continuous_lift Unit E' iC).comp (β.continuous_symm.comp hin))) }
  refine ⟨b, rfl, hβeq, ⟨Hβ, hHβ⟩, τ, ?_, fun _ _ ↦ rfl⟩
  -- Pull the smooth boundary back through the actual exterior zero section.
  have hzK : ContMDiff 𝓘(ℝ, V₀) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + n))) ∞ zK := by
    apply (ContMDiff.subtypeVal_comp_iff WC zK).mp
    exact hforward.comp ((contMDiff_zeroSection ℝ
      (CotangentFiber (n := n) (M := M))).comp contMDiff_subtype_val)
  rintro _ ⟨e₀, he, rfl⟩ _ ⟨f₀, hf, rfl⟩ j
  let := he
  let := hf
  let e' := (e₀.pullback p).pullback iC
  let f' := (f₀.pullback p).pullback iC
  let : MemTrivializationAtlas (e₀.pullback p) := ⟨e₀, inferInstance, rfl⟩
  let : MemTrivializationAtlas (f₀.pullback p) := ⟨f₀, inferInstance, rfl⟩
  let : MemTrivializationAtlas e' := ⟨e₀.pullback p, inferInstance, rfl⟩
  let : MemTrivializationAtlas f' := ⟨f₀.pullback p, inferInstance, rfl⟩
  apply ((hβsmooth e' f' j).comp hzK.contMDiffOn (fun x hx ↦ hx)).congr
  intro x hx
  have hxe : x.val ∈ e₀.baseSet := hx.1
  have he₀ : (e₀.pullback iK).symmL ℂ x (EuclideanSpace.single j 1) =
      e₀.symmL ℂ x.val (EuclideanSpace.single j 1) := by
    rw [(e₀.pullback iK).symmL_apply (R := ℂ) (b := x) hxe,
      e₀.symmL_apply (R := ℂ) (b := x.val) hxe,
      (e₀.pullback iK).symm_apply (b := x) hxe]
    rfl
  have he' : e'.symmL ℂ (zK x) (EuclideanSpace.single j 1) =
      e₀.symmL ℂ x.val (EuclideanSpace.single j 1) := by
    rw [e'.symmL_apply (R := ℂ) (b := zK x) hxe,
      e₀.symmL_apply (R := ℂ) (b := x.val) hxe,
      ((e₀.pullback p).pullback iC).symm_apply (b := zK x) hxe]
    change (e₀.pullback p).symm (iC (zK x)) (EuclideanSpace.single j 1) = _
    rw [(e₀.pullback p).symm_apply (b := iC (zK x)) hxe]
    rfl
  change (f₀ ⟨x.val, β.linearEquiv (zK x)
    ((e₀.pullback iK).symmL ℂ x (EuclideanSpace.single j 1))⟩).2 =
      (f₀ ⟨x.val, β.linearEquiv (zK x)
        (e'.symmL ℂ (zK x) (EuclideanSpace.single j 1))⟩).2
  rw [he₀, he']

end AtiyahSinger.ComplexBundle
