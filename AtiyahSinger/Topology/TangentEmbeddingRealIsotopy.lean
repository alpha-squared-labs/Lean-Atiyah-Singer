/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ParameterizedTangentEmbedding
public import AtiyahSinger.Geometry.ParameterizedTubularNeighborhood
public import AtiyahSinger.Topology.ComplexBundleCylinderTransport
public import AtiyahSinger.Topology.OpenEmbeddingHomotopyOperations
public import AtiyahSinger.Topology.ParameterizedTangentTubularMap
public import AtiyahSinger.Topology.ThomNaturality

/-!
# Tangent pushforwards along an all-real embedding family

Public module ID: M2236.

A smooth family of compact-source embeddings has a proper vertical tangent
cylinder. A parameter-preserving normalized tube and the original quotient-normal
comparisons give one actual open cylinder on a fixed complex total space.
The endpoint comparisons use the same splittings, tubes and scalar extensions.
Supported Thom naturality and open-extension isotopy invariance then compare
the original tangent pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff TensorProduct unitInterval

attribute [local instance] productFullChartedSpace product_full_isManifold
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology complexifiedNormalPullbackTopology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [CompactSpace M] [T2Space M] [T2Space N]
  [SecondCountableTopology M] [SecondCountableTopology N]

local notation "TM" => TangentBundle 𝓘(ℝ, E) M
local notation "TN" => TangentBundle 𝓘(ℝ, F) N
local notation "P" => ℝ × TM

set_option maxHeartbeats 2000000 in
-- Normalize the time-preserving tube, scalar extensions and endpoint pushforwards.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An all-real smooth family of compact-source embeddings preserves the tangent pushforward. -/
theorem tangentEmbeddingPushforward_eq_of_real_isotopy
    (f : ℝ → ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M ↦ f p.1 p.2))
    (hemb : ∀ t : ℝ, IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (f t)) :
    tangentEmbeddingPushforward (f 0) (hemb 0) (f 0).contMDiff.continuous.isProperMap =
      tangentEmbeddingPushforward (f 1) (hemb 1) (f 1).contMDiff.continuous.isProperMap := by
  classical
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
  let : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : ParacompactSpace M := inferInstance
  let : ParacompactSpace TM := inferInstance
  let : ParacompactSpace (ℝ × M) := inferInstance
  let : ParacompactSpace P := inferInstance
  -- Retain time in both the original embedding family and its actual tangent cylinder.
  let β : ContMDiffMap 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) (ℝ × M) (ℝ × N) ∞ :=
    ⟨fun p ↦ (p.1, f p.1 p.2), by
      simpa only [modelWithCornersSelf_prod] using! contMDiff_fst.prodMk hsmooth⟩
  have hβp : IsProperMap β := isProperMap_of_comp_of_t2 β.contMDiff.continuous
    continuous_fst isProperMap_fst_of_compactSpace
  have hβ : IsSmoothEmbedding 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) ∞ β := by
    simpa only [modelWithCornersSelf_prod] using!
      isSmoothEmbedding_parameterMap (fun t ↦ f t) hsmooth hemb hβp
  let H : ContMDiffMap 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) P (ℝ × TN) ∞ :=
    ⟨fun p ↦ (p.1, smoothTangentMap (f p.1) p.2), by
      simpa only [modelWithCornersSelf_prod] using!
        contMDiff_fst.prodMk (contMDiff_parameterTangentMap (fun t ↦ f t) hsmooth)⟩
  have hH : IsSmoothEmbedding 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) ∞ H :=
    by simpa only [modelWithCornersSelf_prod] using!
      isSmoothEmbedding_parameterTangentMap (fun t ↦ f t) hsmooth hemb
  have hHp : IsProperMap H := isProperMap_parameterTangentMap (fun t ↦ f t) hsmooth hemb
  have hfactor (p : P) : zeroVelocityInclusion F N (H p) =
      smoothTangentMap β (zeroVelocityInclusion E M p) := by
    have h : (⟨(p.1, f p.1 p.2.proj), (0,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2.proj p.2.snd)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × N)) =
        tangentMap (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
          (fun q : ℝ × M ↦ (q.1, f q.1 q.2)) ⟨(p.1, p.2.proj), (0, p.2.snd)⟩ := by
      simp only [tangentMap]
      rw [mfderiv_prodMk mdifferentiableAt_fst (hsmooth.mdifferentiable (by simp) _)]
      rw [mfderiv_fst]
      change (⟨(p.1, f p.1 p.2.proj), (0,
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f p.1) p.2.proj p.2.snd)⟩ :
          TangentBundle (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × N)) =
        ⟨(p.1, f p.1 p.2.proj), (0, mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F)
          (fun q : ℝ × M ↦ f q.1 q.2) (p.1, p.2.proj) (0, p.2.snd))⟩
      rw [mfderiv_prod_eq_add_apply (hsmooth.mdifferentiable (by simp) _), map_zero, zero_add]
    simpa only [modelWithCornersSelf_prod] using! h
  -- Choose one cylinder splitting, one zero-velocity comparison and one time-preserving tube.
  let Sβ := tangentNormalSplitting β hβ
  obtain ⟨eZ, heZ, heZs, _⟩ := exists_zeroVelocity_normalEquiv β hβ H hH.isImmersion
    (fun _ ↦ rfl) hfactor
  obtain ⟨T, hTtime⟩ := exists_parameterTubularNeighborhood H hH.isImmersion
    hH.isEmbedding hHp (fun _ ↦ rfl)
  let νβ := NormalBundle 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × F) β
  let Vβ := NormalModel (ℝ × E) (ℝ × F)
  let νH := NormalBundle 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (F × F)) H
  let VH := NormalModel (ℝ × (E × E)) (ℝ × (F × F))
  let V := (parameterTangentProjection E M : P → ℝ × M) *ᵖ νβ
  let (p : P) : AddCommGroup (V p) := by
    change AddCommGroup (νβ (p.1, p.2.proj)); infer_instance
  let (p : P) : Module ℝ (V p) := by
    change Module ℝ (νβ (p.1, p.2.proj)); infer_instance
  let := ComplexBundle.complexificationTopology Vβ V
  let B := fun p : P ↦ ℂ ⊗[ℝ] V p
  obtain ⟨hB, C, hC⟩ := exists_parameterizedComplexNormal_homeomorph
    β hβ H hH.isImmersion eZ heZs Sβ
  let : ComplexBundle.IsFiniteRank B := hB
  let s (t : ℝ) : C(TM, P) := ⟨fun z ↦ (t, z), continuous_const.prodMk continuous_id⟩
  let D (t : ℝ) : TM → Type _ := (s t : TM → P) *ᵖ B
  let (t : ℝ) (z : TM) : AddCommGroup (D t z) := by
    change AddCommGroup (B (t, z)); infer_instance
  let (t : ℝ) (z : TM) : Module ℂ (D t z) := by
    change Module ℂ (B (t, z)); infer_instance
  let (t : ℝ) : TopologicalSpace (TotalSpace Unit (D t)) :=
    Pullback.TotalSpace.topologicalSpace Unit B (s t)
  let (t : ℝ) : ComplexBundle.IsFiniteRank (D t) :=
    ComplexBundle.isFiniteRank_pullback (E := B) (s t)
  obtain ⟨e, q, hq, _⟩ := ComplexBundle.exists_cylinderTransport B
  -- The inverse of the actual cylinder transport restricts to the same fiberwise inverse.
  let Q (t : ℝ) : ComplexBundle.Iso (D 0) (D t) := {
    linearEquiv z := e t z
    continuous_total := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit B (s t)).continuous_iff]
      refine (Pullback.continuous_proj Unit B (s 0)).prodMk ?_
      exact (q.continuous.comp
        ((continuous_const (y := t)).prodMk continuous_id)).congr
          (fun z ↦ hq t z.proj z.snd)
    continuous_symm := by
      have hi (z : TotalSpace Unit (D t)) :
          q.symm ⟨(t, z.proj), z.snd⟩ = (t, ⟨z.proj, (e t z.proj).symm z.snd⟩) := by
        apply q.injective
        rw [q.apply_symm_apply, hq, LinearEquiv.apply_symm_apply]
      exact (continuous_snd.comp (q.symm.continuous.comp
        (Pullback.continuous_lift Unit B (s t)))).congr
          (fun z ↦ congrArg Prod.snd (hi z)) }
  -- All endpoint data are restrictions of those same cylinder witnesses.
  have hend (t : ℝ) := exists_parameterSlice_tangentTubularMap (f t) β H (hemb t) hβ
    hH.isImmersion t (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    eZ heZ heZs Sβ T hTtime C hC
  choose S TT U hU using hend
  let A (t : ℝ) : ComplexBundle.Iso (D 0) (ComplexifiedNormalPullback (f t)) :=
    (Q t).trans (U t).symm
  let X := TotalSpace Unit (D 0)
  let := normalBundleFiberBundle H hH.isImmersion
  let cC : C(TotalSpace Unit B, TotalSpace VH νH) := ⟨C, C.continuous⟩
  let cQ : C(ℝ × X, TotalSpace Unit B) := ⟨q, q.continuous⟩
  let Φ : C(ℝ × X, ℝ × TN) := (T.totalMap H hH.isImmersion).comp
    (cC.comp cQ)
  have hΦ : IsOpenEmbedding Φ :=
    (T.target.isOpen.isOpenEmbedding_subtypeVal.comp
      T.diffeomorph.toHomeomorph.isOpenEmbedding).comp (C.isOpenEmbedding.comp q.isOpenEmbedding)
  have htime (p : ℝ × X) : (Φ p).1 = p.1 := by
    change (T.totalMap H hH.isImmersion (C (q p))).1 = p.1
    have hc := (congrArg (fun z : TotalSpace Unit B ↦ C z)
      (hq p.1 p.2.proj p.2.snd)).trans (hC (p.1, p.2.proj) (e p.1 p.2.proj p.2.snd))
    exact (hTtime (C (q p))).trans
      (congrArg (fun z : TotalSpace VH νH ↦ z.proj.1) hc)
  let F₀ : ℝ × X → TN := fun p ↦ (Φ p).2
  have hF₀ : IsOpenEmbedding (fun p : ℝ × X ↦ (p.1, F₀ p)) := by
    have heq : (fun p : ℝ × X ↦ (p.1, F₀ p)) = Φ :=
      funext (fun p ↦ Prod.ext (htime p).symm rfl)
    rw [heq]
    exact hΦ
  let G (t : ℝ) : C(X, TN) := (tangentEmbeddingTubularMap (f t) (hemb t) (S t) (TT t)).comp
    ⟨(A t).totalHomeomorph, (A t).totalHomeomorph.continuous⟩
  have hG (t : ℝ) : IsOpenEmbedding (G t) :=
    (isOpenEmbedding_tangentEmbeddingTubularMap (f t) (hemb t) (S t) (TT t)).comp
      (A t).totalHomeomorph.isOpenEmbedding
  have hGt (t : ℝ) (w : X) : G t w = F₀ (t, w) := by
    change tangentEmbeddingTubularMap (f t) (hemb t) (S t) (TT t)
      ((A t).totalHomeomorph w) = _
    rw [hU]
    change (T.totalMap H hH.isImmersion (C ⟨(t, w.proj),
      (U t).linearEquiv w.proj (((U t).linearEquiv w.proj).symm (e t w.proj w.snd))⟩)).2 = _
    rw [LinearEquiv.apply_symm_apply]
    change _ = (T.totalMap H hH.isImmersion (C (q (t, w)))).2
    exact congrArg (fun z : TotalSpace Unit B ↦ (T.totalMap H hH.isImmersion (C z)).2)
      (hq t w.proj w.snd).symm
  let : T2Space X := (hG 0).isEmbedding.t2Space
  let : LocallyCompactSpace X := (hG 0).locallyCompactSpace
  let K : ContinuousMap.Homotopy (G 0) (G 1) := {
    toFun p := F₀ ((p.1 : ℝ), p.2)
    continuous_toFun := Φ.continuous.snd.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    map_zero_left w := (hGt 0 w).symm
    map_one_left w := (hGt 1 w).symm }
  have hK : IsOpenEmbedding (fun p : I × X ↦ (p.1, K p)) :=
    isOpenEmbedding_parameter_comp_of_isOpenEmbedding F₀ hF₀
      (fun t : I ↦ (t : ℝ)) continuous_subtype_val
  have hpush := compactSupportKZeroOpenPushforward_eq_of_isotopy (hG 0) (hG 1) K hK
  -- Transport Thom operators by the actual complex isomorphisms, then use the open cylinder.
  let h₀ := (ComplexBundle.nonempty_continuousHermitianMetric (D 0)).some
  have hidentify (t : ℝ) : tangentEmbeddingPushforward (f t) (hemb t)
      (f t).contMDiff.continuous.isProperMap =
      (compactSupportKZeroOpenPushforward (G t) (hG t)).comp h₀.supportedThomHom := by
    let := isFiniteRank_complexifiedNormalPullback (f t) (hemb t).isImmersion
    let ht := (ComplexBundle.nonempty_continuousHermitianMetric
      (ComplexifiedNormalPullback (f t))).some
    have hchoice : tangentEmbeddingPushforward (f t) (hemb t)
        (f t).contMDiff.continuous.isProperMap =
        tangentEmbeddingPushforwardWith (f t) (hemb t) (S t) (TT t) ht := by
      unfold tangentEmbeddingPushforward
      exact tangentEmbeddingPushforwardWith_eq (f t) (hemb t) _ _ _ _ _ _
    rw [hchoice]
    let τ := tangentEmbeddingTubularMap (f t) (hemb t) (S t) (TT t)
    let hτ := isOpenEmbedding_tangentEmbeddingTubularMap (f t) (hemb t) (S t) (TT t)
    let := hτ.isEmbedding.t2Space
    let := hτ.locallyCompactSpace
    change (compactSupportKZeroOpenPushforward τ hτ).comp ht.supportedThomHom = _
    rw [← h₀.supportedThomHom_iso ht (A t), ← AddMonoidHom.comp_assoc,
      ← compactSupportKZeroOpenPushforward_homeomorph,
      ← compactSupportKZeroOpenPushforward_comp]
    rfl
  rw [hidentify 0, hidentify 1, hpush]

end AtiyahSinger
