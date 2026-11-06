/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.NestedThomOpenExtension
public import AtiyahSinger.Topology.TangentNormalSumHomeomorph
public import AtiyahSinger.Topology.TangentTubularRealTransport

/-!
# The actual nested tangent tube and its supported operator

Public module ID: M2238.

A specified complex transport on the first native tangent normal determines an
actual nested open embedding on the ordered real normal sum. The formula uses
the two original tubes, the specified second splitting, and precisely the
real/imaginary conjugate of that transport. On the original complex sum, the
same map realizes the composite of the two supported Thom-to-tube operators.

The proof reindexes the supplied transport by the original first
complexification homeomorphism. All pullback comparisons preserve fiber
vectors. Thus the native formula and the supported operator refer
to the same nested map; no smoothness of the transport is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology sumTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  isFiniteRank_sum isFiniteRank_pullback t2Space_totalSpace locallyCompactSpace_totalSpace

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]
  [T2Space M] [T2Space N] [T2Space P]
  [SecondCountableTopology M] [SecondCountableTopology N] [SecondCountableTopology P]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (g : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, G) N P ∞)
  (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  (hg : IsSmoothEmbedding 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g)
  (Tf : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
  (Tg : TubularNeighborhood (smoothTangentMap g) (isImmersion_smoothTangentMap g hg))
  (Sf : TangentNormalSplitting f hf) (Sg : TangentNormalSplitting g hg)

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "TP" => TangentBundle 𝓘(ℝ, G) P
local notation "νTf" => NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
local notation "VTf" => NormalModel (E × E) (F × F)
local notation "Vg" => NormalModel F G
local notation "Bg" => (π F (TangentSpace 𝓘(ℝ, F)) : TN → N) *ᵖ
  (NormalBundle 𝓘(ℝ, F) 𝓘(ℝ, G) g)
local notation "Dg" => Bg ×ᵇ Bg
local notation "Wg" => Vg × Vg
local notation "Tfc" => (smoothTangentMap f : TM → TN)
local notation "X" => TotalSpace VTf νTf
local notation "Rsum" => νTf ×ᵇ (Tfc *ᵖ Dg)

set_option maxSynthPendingDepth 50 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
-- Normalize the original nested tubes and their time-preserving complex transport.
/-- The same two tubes and complex transport give the actual nested open map and operator. -/
theorem exists_tangentNestedTube
    (hCf : ContinuousHermitianMetric (ComplexifiedNormalPullback f))
    (hCg : ContinuousHermitianMetric (ComplexifiedNormalPullback g)) :
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI : T2Space TM := (tangentBundle_topology E M).1
    letI : T2Space TN := (tangentBundle_topology F N).1
    letI : T2Space TP := (tangentBundle_topology G P).1
    letI : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
    letI : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
    letI : LocallyCompactSpace TP := ChartedSpace.locallyCompactSpace (G × G) TP
    letI := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
    letI := isFiniteRank_complexifiedNormalPullback g hg.isImmersion
    let j : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
    letI := isFiniteRank_pullback (E := ComplexifiedNormalPullback g) j
    let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
      (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
    let b := Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    ∀ e : Iso ((a : X → TN) *ᵖ (ComplexifiedNormalPullback g))
      ((b : X → TN) *ᵖ (ComplexifiedNormalPullback g)),
      ∀ R : ∀ x : X, Dg (a x) ≃ₗ[ℝ] Dg (b x),
        (∀ x w, R x w = complexificationReIm (Bg (b x))
          (e.linearEquiv x ((complexificationReIm (Bg (a x))).symm w))) →
        ∃ N : C(TotalSpace (VTf × Wg) Rsum, TP), ∃ hN : IsOpenEmbedding N,
          (∀ z, N z = Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
            ⟨b ⟨z.proj, z.snd.1⟩, (Sg.equiv (b ⟨z.proj, z.snd.1⟩)).symm
              (R ⟨z.proj, z.snd.1⟩ z.snd.2)⟩) ∧
          (∀ z : TM, N ⟨z, 0⟩ = smoothTangentMap g (smoothTangentMap f z)) ∧
          (let H := tangentNormalSumHomeomorph f g hf Sf
           let j : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
           (compactSupportKZeroOpenPushforward (N.comp ⟨H, H.continuous⟩)
               (hN.comp H.isOpenEmbedding)).comp (hCf.sum (hCg.pullback j)).supportedThomHom =
             (tangentEmbeddingPushforwardWith g hg Sg Tg hCg).comp
               (tangentEmbeddingPushforwardWith f hf Sf Tf hCf)) := by
  classical
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : T2Space TP := (tangentBundle_topology G P).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let : LocallyCompactSpace TP := ChartedSpace.locallyCompactSpace (G × G) TP
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let := isFiniteRank_complexifiedNormalPullback g hg.isImmersion
  let j : C(TM, TN) := ⟨smoothTangentMap f, (smoothTangentMap f).contMDiff.continuous⟩
  let := isFiniteRank_pullback (E := ComplexifiedNormalPullback g) j
  let a : C(X, TN) := ⟨fun z ↦ smoothTangentMap f z.proj,
    (smoothTangentMap f).contMDiff.continuous.comp (FiberBundle.continuous_proj VTf νTf)⟩
  let b := Tf.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  dsimp only
  intro e R hR
  let Cf := ComplexifiedNormalPullback f
  let Cg := ComplexifiedNormalPullback g
  let XC := TotalSpace Unit Cf
  let q : C(XC, TM) := ⟨π Unit Cf, continuous_proj⟩
  let Hf := complexifiedNormalTotalHomeomorph f hf Sf
  let K : C(XC, X) := ⟨Hf, Hf.continuous⟩
  let τf := tangentEmbeddingTubularMap f hf Sf Tf
  let τg := tangentEmbeddingTubularMap g hg Sg Tg
  let hτf := isOpenEmbedding_tangentEmbeddingTubularMap f hf Sf Tf
  let hτg := isOpenEmbedding_tangentEmbeddingTubularMap g hg Sg Tg
  -- Reindex the original transport; each canonical comparison is the identity on vectors.
  let ca := pullbackCompIso (E := Cg) a K
  let cb := pullbackCompIso (E := Cg) b K
  let c := pullbackCompIso (E := Cg) j q
  let ec : Iso ((π Unit Cf) *ᵖ ((j : TM → TN) *ᵖ Cg))
      ((τf : XC → TN) *ᵖ Cg) :=
    c.trans (ca.symm.trans ((Iso.pullback K e).trans cb))
  have hc (x : XC) : c.linearEquiv x = LinearEquiv.refl ℂ (Cg (j (q x))) := by
    apply LinearEquiv.ext
    exact pullbackCompIso_apply j q x
  have hca (x : XC) : ca.linearEquiv x = LinearEquiv.refl ℂ (Cg (a (K x))) := by
    apply LinearEquiv.ext
    exact pullbackCompIso_apply a K x
  have hcb (x : XC) : cb.linearEquiv x = LinearEquiv.refl ℂ (Cg (b (K x))) := by
    apply LinearEquiv.ext
    exact pullbackCompIso_apply b K x
  have hec (x : XC) (v : Cg (j (q x))) :
      ec.linearEquiv x v = e.linearEquiv (K x) v := by
    change cb.linearEquiv x (e.linearEquiv (K x)
      ((ca.linearEquiv x).symm (c.linearEquiv x v))) = _
    simp only [hc, hca, hcb]
    rfl
  -- Use this same comparison in the supported nested Thom construction.
  obtain ⟨NC, hNC, hformula, hoperator⟩ :=
    hCf.exists_nestedThom_openEmbedding hCg j τf hτf τg hτg ec
  let H := tangentNormalSumHomeomorph f g hf Sf
  let NR : C(TotalSpace (VTf × Wg) Rsum, TP) := NC.comp ⟨H.symm, H.symm.continuous⟩
  have hNR : IsOpenEmbedding NR := hNC.comp H.symm.isOpenEmbedding
  have hnative (z : TotalSpace (VTf × Wg) Rsum) :
      NR z = Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
        ⟨b ⟨z.proj, z.snd.1⟩, (Sg.equiv (b ⟨z.proj, z.snd.1⟩)).symm
          (R ⟨z.proj, z.snd.1⟩ z.snd.2)⟩ := by
    rw [show NR z = NC (H.symm z) from rfl, hformula, hec]
    have hK : K ⟨(H.symm z).proj, (H.symm z).snd.1⟩ =
        (⟨z.proj, z.snd.1⟩ : X) := by
      change Hf (Hf.symm ⟨z.proj, z.snd.1⟩) = _
      exact Hf.apply_symm_apply _
    let L : TotalSpace Unit ((a : X → TN) *ᵖ Cg) → TP := fun p ↦
      Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
        ⟨b p.proj, (Sg.equiv (b p.proj)).symm
          (complexificationReIm (Bg (b p.proj)) (e.linearEquiv p.proj p.snd))⟩
    have hin : (⟨K ⟨(H.symm z).proj, (H.symm z).snd.1⟩, (H.symm z).snd.2⟩ :
        TotalSpace Unit ((a : X → TN) *ᵖ Cg)) =
      ⟨⟨z.proj, z.snd.1⟩,
        (complexificationReIm (Bg (smoothTangentMap f z.proj))).symm z.snd.2⟩ :=
      TotalSpace.ext hK HEq.rfl
    change L ⟨K ⟨(H.symm z).proj, (H.symm z).snd.1⟩, (H.symm z).snd.2⟩ = _
    calc
      _ = L ⟨⟨z.proj, z.snd.1⟩,
          (complexificationReIm (Bg (smoothTangentMap f z.proj))).symm z.snd.2⟩ :=
        congrArg L hin
      _ = _ := congrArg
        (fun v : Dg (b ⟨z.proj, z.snd.1⟩) ↦
          Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
            ⟨b ⟨z.proj, z.snd.1⟩, (Sg.equiv (b ⟨z.proj, z.snd.1⟩)).symm v⟩)
        (hR ⟨z.proj, z.snd.1⟩ z.snd.2).symm
  refine ⟨NR, hNR, hnative, ?_, ?_⟩
  · -- Linearity and the original zero sections retain the actual composite embedding.
    intro z
    calc
      NR ⟨z, 0⟩ = Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
          ⟨b ⟨z, 0⟩, (Sg.equiv (b ⟨z, 0⟩)).symm (R ⟨z, 0⟩ 0)⟩ := hnative ⟨z, 0⟩
      _ = Tg.totalMap (smoothTangentMap g) (isImmersion_smoothTangentMap g hg)
          ⟨b ⟨z, 0⟩, 0⟩ := by
        apply congrArg (fun v ↦ Tg.totalMap (smoothTangentMap g)
          (isImmersion_smoothTangentMap g hg) ⟨b ⟨z, 0⟩, v⟩)
        exact (congrArg (Sg.equiv (b ⟨z, 0⟩)).symm ((R ⟨z, 0⟩).map_zero)).trans
          (Sg.equiv (b ⟨z, 0⟩)).symm.map_zero
      _ = smoothTangentMap g (b ⟨z, 0⟩) := Tg.map_zero _
      _ = smoothTangentMap g (smoothTangentMap f z) :=
        congrArg (smoothTangentMap g) (Tf.map_zero z)
  · have heq : NR.comp ⟨H, H.continuous⟩ = NC := by
      apply ContinuousMap.ext
      intro z
      exact congrArg NC (H.symm_apply_apply z)
    change (compactSupportKZeroOpenPushforward (NR.comp ⟨H, H.continuous⟩)
      (hNR.comp H.isOpenEmbedding)).comp (hCf.sum (hCg.pullback j)).supportedThomHom = _
    simp only [heq]
    exact hoperator

end AtiyahSinger
