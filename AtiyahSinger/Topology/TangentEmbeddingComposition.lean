/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding
public import AtiyahSinger.Geometry.TangentNestedTubeDerivative
public import AtiyahSinger.Geometry.TangentNestedTubeReference
public import AtiyahSinger.Geometry.TangentNestedTubeReferenceDerivative
public import AtiyahSinger.Geometry.TangentNormalCompositionHomotopy
public import AtiyahSinger.Topology.ComplexifiedNormalComposition
public import AtiyahSinger.Topology.OpenEmbeddingHomotopyOperations
public import AtiyahSinger.Topology.TangentEmbeddingPushforward
public import AtiyahSinger.Topology.TangentNestedTube
public import AtiyahSinger.Topology.TangentNestedTubeIsotopy
public import AtiyahSinger.Topology.TangentTubularRealTransport
public import AtiyahSinger.Topology.ThomDirectSum
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# Composition and identity for the actual tangent embedding pushforward

Public module ID: M2230.

The proper smooth embedding pushforward is the already defined supported Thom
operator followed by its actual tubular open extension. Its composite agrees
with the pushforward for the original smooth composite, and its identity case
is the identity on the original compact-support group.

The normal comparison needed in the proof is constructed from the original
short exact sequence of normal bundles. Its smooth real splitting is first
complexified; an arbitrary real isomorphism of doubled normals is not accepted
as a complex Thom identification. The ordered factors are the normal of f,
then the pullback of the normal of g. Throughout, the quotient/vertical
complex structure is the SG convention (u,v) ↦ (-v,u).

Sources: SG III.12, printed p.241, for the tangent embedding construction;
KA IV.5.19 and IV.5.21--5.22(a) for Thom transitivity, tubular construction and
the composition law. KA uses a
conjugate convention for its normal complex structure; its structural argument
is expanded here for the project's fixed SG convention. The supported Thom
direct-sum, naturality and open-extension results are used for actual maps on
noncompact total spaces. The composite normal comparison is joined to the actual
nested tubular map through a normalized reference and a whole-cylinder open
isotopy. The identity law uses the positive zero-rank Thom normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]


set_option linter.unusedSectionVars false in
/-- Successive finite-dimensional smooth embeddings give the actual smooth composite embedding. -/
theorem isSmoothEmbedding_comp
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) :
    IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (g.comp f) := by
  /- Stage 1: the existing embedding certificates make both original
  differentials injective. The chain rule identifies the differential of
  the actual g.comp f with their composite, hence it is injective as well.
  Stage 2: the finite-dimensional smooth immersion normal-form theorem
  supplies local inclusion charts for this composite. This establishes the
  local-normal-form IsImmersion predicate; smooth injectivity alone is not
  substituted for it. No properness or global separation is needed here.
  Stage 3: compose the given topological embeddings. This gives the induced
  topology on the composite image and completes IsSmoothEmbedding. -/
  have hderiv (x : M) :
      Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) x) := by
    change Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) ((g : N → P) ∘ (f : M → N)) x)
    rw [mfderiv_comp x (g.contMDiff.mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x)]
    exact (hg.isImmersion.mfderiv_injective (by simp) (f x)).comp
      (hf.isImmersion.mfderiv_injective (by simp) x)
  -- Use the full-real finite-dimensional normal form, then the actual induced topologies.
  exact ⟨isImmersion_of_injective_mfderiv (g.comp f) hderiv,
    hg.isEmbedding.comp hf.isEmbedding⟩

variable [T2Space M] [T2Space N] [T2Space P]
  [SecondCountableTopology M] [SecondCountableTopology N] [SecondCountableTopology P]

section Composition

open ComplexBundle
open scoped unitInterval

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2200000 in
-- Normalize the original complexified normal splitting and nested pushforward maps.
/-- The actual tangent embedding pushforward preserves proper smooth composition. -/
theorem tangentEmbeddingPushforward_comp
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
    (hpf : IsProperMap f) (hpg : IsProperMap g) :
    tangentEmbeddingPushforward (g.comp f) (isSmoothEmbedding_comp f g hf hg)
        (hpg.comp hpf) =
      (tangentEmbeddingPushforward g hg hpg).comp
        (tangentEmbeddingPushforward f hf hpf) := by
  /- Complexify the original real normal splitting with its positive factor order.
  The three-shear path compares the resulting real tubular map to the reference
  normalized by the actual nested derivative. The same transported nested tube
  is openly isotopic to this reference. Only the genuine complex isomorphism
  transports the Thom operator; the real homotopies act on open extensions.
  Finally use the nested operator identity and the three original choice laws. -/
  classical
  let hgf := isSmoothEmbedding_comp f g hf hg
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let TP := TangentBundle 𝓘(ℝ, G) P
  let TfMap := smoothTangentMap f
  let TgMap := smoothTangentMap g
  let TgfMap := smoothTangentMap (g.comp f)
  let νf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νg := NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g
  let νgf := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f)
  let νTf := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) TfMap
  let νTg := NormalBundle 𝓘(ℝ, F × F) 𝓘(ℝ, G × G) TgMap
  let νTgf := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) TgfMap
  let VTf := NormalModel (E × E) (F × F)
  let VTg := NormalModel (F × F) (G × G)
  let VTgf := NormalModel (E × E) (G × G)
  let Vg := NormalModel F G
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace F N
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : T2Space TP := (tangentBundle_topology G P).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let : LocallyCompactSpace TP := ChartedSpace.locallyCompactSpace (G × G) TP
  let : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
  let : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
  let : SecondCountableTopology TP := (tangentBundle_topology G P).2.1
  let : ParacompactSpace TM := (tangentBundle_topology E M).2.2
  let : ParacompactSpace TN := (tangentBundle_topology F N).2.2
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle g hg.isImmersion
  let := normalBundleVectorBundle g hg.isImmersion
  let := normalBundleContMDiffVectorBundle g hg.isImmersion
  let := normalBundleFiberBundle (g.comp f) hgf.isImmersion
  let := normalBundleVectorBundle (g.comp f) hgf.isImmersion
  let := normalBundleContMDiffVectorBundle (g.comp f) hgf.isImmersion
  let := normalBundleFiberBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle TfMap (isImmersion_smoothTangentMap f hf)
  let := normalBundleFiberBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleContMDiffVectorBundle TgMap (isImmersion_smoothTangentMap g hg)
  let := normalBundleFiberBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleVectorBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  let := normalBundleContMDiffVectorBundle TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  -- Choose one set of the original normalized splittings and proper tangent tubes.
  let Sf := tangentNormalSplitting f hf
  let Sg := tangentNormalSplitting g hg
  let Sgf := tangentNormalSplitting (g.comp f) hgf
  let Tf := (nonempty_tubularNeighborhood TfMap (isImmersion_smoothTangentMap f hf)
    (isSmoothEmbedding_tangentMap hf).isEmbedding (isProperMap_tangentMap hf hpf)).some
  let Tg := (nonempty_tubularNeighborhood TgMap (isImmersion_smoothTangentMap g hg)
    (isSmoothEmbedding_tangentMap hg).isEmbedding (isProperMap_tangentMap hg hpg)).some
  let Tgf := (nonempty_tubularNeighborhood TgfMap
    (isImmersion_smoothTangentMap (g.comp f) hgf)
    (isSmoothEmbedding_tangentMap hgf).isEmbedding
    (isProperMap_tangentMap hgf (hpg.comp hpf))).some
  let S := (nonempty_normalEmbeddingCompositionSplitting f g hf.isImmersion
    hg.isImmersion hgf.isImmersion).some
  have hTcomp : TgMap.comp TfMap = TgfMap := by
    apply DFunLike.ext
    intro z
    change (⟨g (f z.proj), mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f z.proj)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj z.snd)⟩ : TP) =
      ⟨g (f z.proj), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj z.snd⟩
    have hd := mfderiv_comp z.proj (g.contMDiff.mdifferentiable (by simp) _)
      (f.contMDiff.mdifferentiable (by simp) _)
    rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, G) (g.comp f) z.proj =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) g (f z.proj)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) from hd]
    rfl
  have hTC : IsImmersion 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) ∞ (TgMap.comp TfMap) := by
    rw [hTcomp]
    exact isImmersion_smoothTangentMap (g.comp f) hgf
  let νTC := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) (TgMap.comp TfMap)
  let := normalBundleFiberBundle (TgMap.comp TfMap) hTC
  let := normalBundleVectorBundle (TgMap.comp TfMap) hTC
  let := normalBundleContMDiffVectorBundle (TgMap.comp TfMap) hTC
  obtain ⟨ST, hST⟩ := exists_tangentNestedTube_normalDerivative f g hf hg Tf Tg Sg hTC
  obtain ⟨c, A, H, hc, hH, hA₀, hA₁⟩ :=
    exists_tangentNormalComposition_homotopy f g hf hg hgf hTC S ST Sf Sg Sgf
  -- Canonical quotient representatives identify this c with its smooth comparison.
  obtain ⟨c', hc', hcs', _⟩ :=
    exists_tangentNormalComposition_comparison f g hf hg hgf hTC S ST
  have hcc : c = c' := by
    funext z
    apply ContinuousLinearEquiv.ext
    funext v
    obtain ⟨w, rfl⟩ := (LinearMap.range
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, G × G) (TgMap.comp TfMap) z).toLinearMap).mkQ_surjective v
    exact (hc z w).trans (hc' z w).symm
  have hcs : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTgf))
      (𝓘(ℝ, E × E).prod 𝓘(ℝ, VTgf)) ∞
      (fun z : TotalSpace VTgf νTC ↦ (⟨z.proj, c z.proj z.snd⟩ : TotalSpace VTgf νTgf)) := by
    rw [hcc]
    exact hcs'.1
  let Bf := ComplexifiedNormalPullback f
  let BgC := ComplexifiedNormalPullback g
  let Bgf := ComplexifiedNormalPullback (g.comp f)
  let j : C(TM, TN) := ⟨TfMap, TfMap.contMDiff.continuous⟩
  let Bsum := Bf ×ᵇ ((j : TM → TN) *ᵖ BgC)
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let := isFiniteRank_complexifiedNormalPullback g hg.isImmersion
  let := isFiniteRank_complexifiedNormalPullback (g.comp f) hgf.isImmersion
  let := isFiniteRank_pullback (E := BgC) j
  let hCf := (nonempty_continuousHermitianMetric Bf).some
  let hCg := (nonempty_continuousHermitianMetric BgC).some
  let hCgf := (nonempty_continuousHermitianMetric Bgf).some
  let Bg := (π F (TangentSpace 𝓘(ℝ, F)) : TN → N) *ᵖ νg
  let Dg := Bg ×ᵇ Bg
  let Wg := Vg × Vg
  let Rsum := νTf ×ᵇ ((j : TM → TN) *ᵖ Dg)
  let Xsum := TotalSpace (VTf × Wg) Rsum
  let := complexificationTopology Vg Bg
  obtain ⟨e, R, hR, hRc, hRic, hezero, hRzero⟩ :=
    exists_tangentTubular_real_transport f hf Tf Vg Bg Sf
      (isFiniteRank_complexifiedNormalPullback g hg.isImmersion)
  obtain ⟨NN, hNN, hNNformula, hNNzero, hNNpush⟩ :=
    exists_tangentNestedTube f g hf hg Tf Tg Sf Sg hCf hCg e R hR
  obtain ⟨ec, hec⟩ := exists_complexifiedNormalPullback_composition_iso
    f g hf.isImmersion hg.isImmersion hgf.isImmersion S
  let Xcf := TotalSpace Unit Bgf
  let Xcs := TotalSpace Unit Bsum
  let N₀ := TotalSpace VTgf νTgf
  let N₁ := TotalSpace (VTf × VTg) (νTf ×ᵇ ((j : TM → TN) *ᵖ νTg))
  let Cgf := complexifiedNormalTotalHomeomorph (g.comp f) hgf Sgf
  let Hsum := tangentNormalSumHomeomorph f g hf Sf
  -- Scalar extension has the original positive real/imaginary ordering on every tensor.
  have hecReIm (z : TM) (w : Bgf z) :
      (complexificationReIm (νf z.proj) (ec.linearEquiv z w).1,
        complexificationReIm (νg (f z.proj)) (ec.linearEquiv z w).2) =
      (((S.equiv z.proj (complexificationReIm (νgf z.proj) w).1).1,
          (S.equiv z.proj (complexificationReIm (νgf z.proj) w).2).1),
        ((S.equiv z.proj (complexificationReIm (νgf z.proj) w).1).2,
          (S.equiv z.proj (complexificationReIm (νgf z.proj) w).2).2)) := by
    induction w using TensorProduct.inductionOn with
    | tmul a v =>
      rw [hec]
      simp only [(complexificationReIm_properties _).1, map_smul,
        Prod.smul_fst, Prod.smul_snd]
    | add u v hu hv =>
      simp only [map_add, Prod.fst_add, Prod.snd_add] at *
      simpa only [Prod.add_def] using congrArg₂ (· + ·) hu hv
  let J : Xsum → N₁ := fun z ↦
    ⟨z.proj, (z.snd.1, (Sg.equiv (TfMap z.proj)).symm z.snd.2)⟩
  have hAendpoint (w : Xcf) : (H (1, Cgf w)).2 = J (Hsum (ec.totalHomeomorph w)) := by
    rw [hH]
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      change A 1 w.proj ((Sgf.equiv w.proj).symm
        (complexificationReIm (νgf w.proj.proj) w.snd)) =
        ((Sf.equiv w.proj).symm (complexificationReIm (νf w.proj.proj)
            (ec.linearEquiv w.proj w.snd).1),
          (Sg.equiv (TfMap w.proj)).symm (complexificationReIm (νg (f w.proj.proj))
            (ec.linearEquiv w.proj w.snd).2))
      rw [hA₁, (Sgf.equiv w.proj).apply_symm_apply]
      exact congrArg (fun p : (νf w.proj.proj × νf w.proj.proj) ×
          (νg (f w.proj.proj) × νg (f w.proj.proj)) ↦
        ((Sf.equiv w.proj).symm p.1, (Sg.equiv (TfMap w.proj)).symm p.2))
        (hecReIm w.proj w.snd).symm
  -- Restrict the given normal cylinder at zero without choosing a different comparison.
  have hHtime (p : ℝ × N₀) : (H p).1 = p.1 := congrArg Prod.fst (hH p.1 p.2)
  have hHitime (p : ℝ × N₁) : (H.symm p).1 = p.1 :=
    (hHtime (H.symm p)).symm.trans (congrArg Prod.fst (H.apply_symm_apply p))
  let H₀ : N₀ ≃ₜ N₁ :=
    { toFun z := (H (0, z)).2
      invFun z := (H.symm (0, z)).2
      left_inv z := by
        have hp : (0, (H (0, z)).2) = H (0, z) := Prod.ext (hHtime (0, z)).symm rfl
        change (H.symm (0, (H (0, z)).2)).2 = z
        rw [hp]
        exact congrArg Prod.snd (H.symm_apply_apply (0, z))
      right_inv z := by
        have hp : (0, (H.symm (0, z)).2) = H.symm (0, z) :=
          Prod.ext (hHitime (0, z)).symm rfl
        change (H (0, (H.symm (0, z)).2)).2 = z
        rw [hp]
        exact congrArg Prod.snd (H.apply_symm_apply (0, z))
      continuous_toFun := H.continuous.snd.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := H.symm.continuous.snd.comp (continuous_const.prodMk continuous_id) }
  have hH₀ (z : N₀) : H₀ z = ⟨z.proj, ST.equiv z.proj ((c z.proj).symm z.snd)⟩ := by
    change (H (0, z)).2 = _
    rw [hH, hA₀]
  -- This reference uses the same actual nested derivative, splitting and canonical c.
  let L (z : TM) : Rsum z ≃L[ℝ] νTgf z :=
    (((ContinuousLinearEquiv.refl ℝ (νTf z)).prodCongr
      (Sg.equiv (TfMap z)).symm).trans (ST.equiv z).symm).trans (c z)
  obtain ⟨Q, hQ⟩ := exists_tangentNestedTube_referenceDiffeomorph
    f g hf hg hgf hTC ST Sg c hcs
  have hQL (z : Xsum) : Q z = ⟨z.proj, L z.proj z.snd⟩ := hQ z
  have hvertical := fun z : TM ↦ tangentNestedTube_reference_normalDerivative
    f g hf hg Tf Tg Sg hTC ST c z (hST z) (hc z) (L z) (fun _ ↦ rfl)
  have hH₀Q (z : Xsum) : H₀ (Q z) = J z := by
    rw [hQ, hH₀]
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      change ST.equiv z.proj ((c z.proj).symm (c z.proj
        ((ST.equiv z.proj).symm (z.snd.1, (Sg.equiv (TfMap z.proj)).symm z.snd.2)))) = _
      rw [(c z.proj).symm_apply_apply, (ST.equiv z.proj).apply_symm_apply]
  let τN : C(N₀, TP) := Tgf.totalMap TgfMap (isImmersion_smoothTangentMap (g.comp f) hgf)
  have hτN : IsOpenEmbedding τN :=
    Tgf.target.isOpen.isOpenEmbedding_subtypeVal.comp
      Tgf.diffeomorph.toHomeomorph.isOpenEmbedding
  let ecMap : C(Xcf, Xcs) := ⟨ec.totalHomeomorph, ec.totalHomeomorph.continuous⟩
  let D : C(Xcf, Xsum) := (⟨Hsum, Hsum.continuous⟩ : C(Xcs, Xsum)).comp ecMap
  have hD : IsOpenEmbedding D := Hsum.isOpenEmbedding.comp ec.totalHomeomorph.isOpenEmbedding
  let τref : C(Xsum, TP) := τN.comp ⟨Q, Q.contMDiff.continuous⟩
  have hτref : IsOpenEmbedding τref := hτN.comp Q.toHomeomorph.isOpenEmbedding
  let G₀ : C(Xcf, TP) := tangentEmbeddingTubularMap (g.comp f) hgf Sgf Tgf
  let G₁ : C(Xcf, TP) := τref.comp D
  have hG₀ : IsOpenEmbedding G₀ :=
    isOpenEmbedding_tangentEmbeddingTubularMap (g.comp f) hgf Sgf Tgf
  have hG₁ : IsOpenEmbedding G₁ := hτref.comp hD
  let Φ : ℝ × Xcf → ℝ × TP := fun p ↦
    (p.1, τN (H₀.symm (H (p.1, Cgf p.2)).2))
  have hΦ : IsOpenEmbedding Φ := by
    have h := (IsOpenEmbedding.id.prodMap hτN).comp
      (((Homeomorph.refl ℝ).prodCongr H₀.symm).isOpenEmbedding.comp
        (H.isOpenEmbedding.comp ((Homeomorph.refl ℝ).prodCongr Cgf).isOpenEmbedding))
    convert h using 1
    funext p
    apply Prod.ext
    · exact (hHtime (p.1, Cgf p.2)).symm
    · rfl
  have hΦ₀ (w : Xcf) : (Φ (0, w)).2 = G₀ w := by
    change τN (H₀.symm (H₀ (Cgf w))) = G₀ w
    rw [H₀.symm_apply_apply]
    rfl
  have hΦ₁ (w : Xcf) : (Φ (1, w)).2 = G₁ w := by
    change τN (H₀.symm (H (1, Cgf w)).2) = τN (Q (Hsum (ec.totalHomeomorph w)))
    rw [hAendpoint, ← hH₀Q, H₀.symm_apply_apply]
  -- This whole-cylinder homotopy compares the complex Thom tube to the same real reference.
  let K₀ : ContinuousMap.Homotopy G₀ G₁ :=
    { toFun p := (Φ ((p.1 : ℝ), p.2)).2
      continuous_toFun := hΦ.continuous.snd.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      map_zero_left := hΦ₀
      map_one_left := hΦ₁ }
  have hK₀ : IsOpenEmbedding (fun p : I × Xcf ↦ (p.1, K₀ p)) :=
    isOpenEmbedding_parameter_comp_of_isOpenEmbedding (fun p ↦ (Φ p).2) hΦ
      (fun t : I ↦ (t : ℝ)) continuous_subtype_val
  have hpush₀ := compactSupportKZeroOpenPushforward_eq_of_isotopy hG₀ hG₁ K₀ hK₀
  let G₂ : C(Xcf, TP) := NN.comp D
  have hG₂ : IsOpenEmbedding G₂ := hNN.comp hD
  -- The same normalized reference is joined to the actual transported nested tube.
  obtain ⟨K, hK, _⟩ := exists_tangentNestedTube_openIsotopy
    f g hf hg hgf Tf Tg Tgf Sg L Q hQL hvertical R hRc hRic hRzero
    NN hNN hNNformula hNNzero
  let K₁ : ContinuousMap.Homotopy G₁ G₂ := K.compContinuousMap D
  have hK₁ : IsOpenEmbedding (fun p : I × Xcf ↦ (p.1, K₁ p)) :=
    hK.comp (IsOpenEmbedding.id.prodMap hD)
  have hpush₁ := compactSupportKZeroOpenPushforward_eq_of_isotopy hG₁ hG₂ K₁ hK₁
  -- Only the actual scalar-extension isomorphism is used to carry the complex Thom class.
  have hthom := hCgf.supportedThomHom_iso (hCf.sum (hCg.pullback j)) ec
  have hproduct : (compactSupportKZeroOpenPushforward G₂ hG₂).comp hCgf.supportedThomHom =
      (tangentEmbeddingPushforwardWith g hg Sg Tg hCg).comp
        (tangentEmbeddingPushforwardWith f hf Sf Tf hCf) := by
    let JNN : C(Xcs, TP) := NN.comp ⟨Hsum, Hsum.continuous⟩
    let hJNN : IsOpenEmbedding JNN := hNN.comp Hsum.isOpenEmbedding
    have hcomp : compactSupportKZeroOpenPushforward G₂ hG₂ =
        (compactSupportKZeroOpenPushforward JNN hJNN).comp
          (compactSupportKZeroHomeomorph ec.totalHomeomorph) := by
      have h := compactSupportKZeroOpenPushforward_comp ec.totalHomeomorph
        ec.totalHomeomorph.isOpenEmbedding JNN hJNN
      rw [compactSupportKZeroOpenPushforward_homeomorph] at h
      exact h
    rw [hcomp, AddMonoidHom.comp_assoc, hthom]
    exact hNNpush
  -- The three selected witnesses are related to the originals by the proved choice law.
  have hfchoice : tangentEmbeddingPushforward f hf hpf =
      tangentEmbeddingPushforwardWith f hf Sf Tf hCf := by
    unfold tangentEmbeddingPushforward
    exact tangentEmbeddingPushforwardWith_eq f hf _ _ _ _ _ _
  have hgchoice : tangentEmbeddingPushforward g hg hpg =
      tangentEmbeddingPushforwardWith g hg Sg Tg hCg := by
    unfold tangentEmbeddingPushforward
    exact tangentEmbeddingPushforwardWith_eq g hg _ _ _ _ _ _
  have hgfchoice : tangentEmbeddingPushforward (g.comp f) hgf (hpg.comp hpf) =
      tangentEmbeddingPushforwardWith (g.comp f) hgf Sgf Tgf hCgf := by
    unfold tangentEmbeddingPushforward
    exact tangentEmbeddingPushforwardWith_eq (g.comp f) hgf _ _ _ _ _ _
  rw [hfchoice, hgchoice, hgfchoice]
  change (compactSupportKZeroOpenPushforward G₀ hG₀).comp hCgf.supportedThomHom = _
  rw [hpush₀, hpush₁]
  exact hproduct

end Composition

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity embedding has the positively normalized identity compact-support pushforward. -/
theorem tangentEmbeddingPushforward_id :
    letI : T2Space (TangentBundle 𝓘(ℝ, E) M) := (tangentBundle_topology E M).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M) :=
      ChartedSpace.locallyCompactSpace (E × E) (TangentBundle 𝓘(ℝ, E) M)
    tangentEmbeddingPushforward (ContMDiffMap.id (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
        IsSmoothEmbedding.id isProperMap_id =
      AddMonoidHom.id (CompactSupportKZero (TangentBundle 𝓘(ℝ, E) M)) := by
  /- The differential of the original identity has full range, so its normal
  quotient and its actual complexification are zero fibers. For any selected
  splitting and tube, the tubular map is therefore the inverse of the actual
  zero-section homeomorphism: its zero-section formula determines every point.
  The zero-rank Thom formula and inverse homeomorphism transport cancel on the
  original compact-support group. This applies directly to the choices in the
  existing definition; no change of those choices is needed. -/
  classical
  let I := 𝓘(ℝ, E)
  let TM := TangentBundle I M
  let f₀ := ContMDiffMap.id (I := I) (M := M) (n := ∞)
  let : T2Space TM := (tangentBundle_topology E M).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  -- Full differential range makes each original real normal quotient the zero space.
  have hnormal (x : M) : Subsingleton (NormalBundle I I f₀ x) := by
    change Subsingleton (TangentSpace I x ⧸
      LinearMap.range (mfderiv I I (id : M → M) x).toLinearMap)
    rw [mfderiv_id]
    change Subsingleton (TangentSpace I x ⧸ LinearMap.range (LinearMap.id))
    rw [LinearMap.range_id]
    infer_instance
  let (x : M) : Subsingleton (NormalBundle I I f₀ x) := hnormal x
  let : ∀ z : TM, Subsingleton (ComplexifiedNormalPullback f₀ z) := fun z ↦ by
    let := hnormal z.proj
    change Subsingleton (ℂ ⊗[ℝ] NormalBundle I I f₀ z.proj)
    infer_instance
  let : ComplexBundle.IsFiniteRank (ComplexifiedNormalPullback f₀) :=
    isFiniteRank_complexifiedNormalPullback f₀ IsSmoothEmbedding.id.isImmersion
  have htangent (z : TM) : smoothTangentMap f₀ z = z := by
    change (⟨z.proj, mfderiv I I (id : M → M) z.proj z.snd⟩ : TM) = z
    rw [mfderiv_id]
    rfl
  -- Every actual tube on these zero fibers is the same inverse zero-section map.
  have hWith (S : TangentNormalSplitting f₀ IsSmoothEmbedding.id)
      (T : TubularNeighborhood (smoothTangentMap f₀)
        (isImmersion_smoothTangentMap f₀ IsSmoothEmbedding.id))
      (h : ComplexBundle.ContinuousHermitianMetric (ComplexifiedNormalPullback f₀)) :
      tangentEmbeddingPushforwardWith f₀ IsSmoothEmbedding.id S T h =
        AddMonoidHom.id (CompactSupportKZero TM) := by
    let X := TotalSpace Unit (ComplexifiedNormalPullback f₀)
    let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) (smoothTangentMap f₀)
    let VT := NormalModel (E × E) (E × E)
    let (z : TM) : Subsingleton (νT z) :=
      ⟨fun v w ↦ (S.equiv z).injective (Subsingleton.elim _ _)⟩
    let τ := tangentEmbeddingTubularMap f₀ IsSmoothEmbedding.id S T
    let he := isOpenEmbedding_tangentEmbeddingTubularMap f₀ IsSmoothEmbedding.id S T
    let : T2Space X := he.isEmbedding.t2Space
    let : LocallyCompactSpace X := he.locallyCompactSpace
    let e := ComplexBundle.zeroSectionHomeomorph (E := ComplexifiedNormalPullback f₀)
    have hzero (z : TM) : τ ⟨z, 0⟩ = z := by
      have hC : complexifiedNormalTotalHomeomorph f₀ IsSmoothEmbedding.id S ⟨z, 0⟩ =
          (⟨z, 0⟩ : TotalSpace VT νT) := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (Subsingleton.elim _ _)
      change T.totalMap (smoothTangentMap f₀)
        (isImmersion_smoothTangentMap f₀ IsSmoothEmbedding.id)
        (complexifiedNormalTotalHomeomorph f₀ IsSmoothEmbedding.id S ⟨z, 0⟩) = z
      rw [hC]
      exact (T.map_zero z).trans (htangent z)
    have hτ : (τ : X → TM) = e.symm := by
      funext z
      have hz : z = (⟨z.proj, 0⟩ : X) :=
        TotalSpace.ext rfl (heq_of_eq (Subsingleton.elim _ _))
      exact (congrArg τ hz).trans (hzero z.proj)
    -- The positive zero-rank Thom unit is transport by e, so the same inverse transport cancels.
    change (compactSupportKZeroOpenPushforward τ he).comp h.supportedThomHom = _
    have hpush : compactSupportKZeroOpenPushforward τ he =
        compactSupportKZeroHomeomorph e.symm := by
      simpa only [hτ] using compactSupportKZeroOpenPushforward_homeomorph e.symm
    rw [ComplexBundle.ContinuousHermitianMetric.supportedThomHom_zeroRank, hpush]
    exact compactSupportKZeroHomeomorph_symm e
  unfold tangentEmbeddingPushforward
  exact hWith _ _ _

end AtiyahSinger
