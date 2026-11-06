/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding
public import AtiyahSinger.Topology.TangentEmbeddingOpenGeometry
public import AtiyahSinger.Topology.TangentEmbeddingPushforward
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# Open locality of the actual tangent embedding pushforward

Public module ID: M2233.

For a commuting square of proper smooth embeddings with open smooth horizontal
maps, the actual tangent pushforwards commute with covariant open extension.
An open smooth map is expressed as an injective local diffeomorphism; its tangent
map is the original derivative map, with openness proved rather than assumed.

The vertical maps are the geometric pushforwards already constructed from the
fixed complexified normal bundle, normalized splitting and actual tube. The
horizontal maps are the existing open extensions on the actual tangent bundles.
No desired K-theory square or compatible tubular neighborhoods are hypotheses.
The square need not be Cartesian: the given source may select open and closed
components of the full inverse-image submanifold.

Sources: SG III.12 (12.7) and KA IV.5.21--5.22 for the geometric construction and
its Thom-naturality method; SG C.1 and C.13 and KA IV.1.3, IV.1.10--1.11 for
supported Thom naturality under open extension. The exact geometric locality
square is a standard project supplement, not the statement of SG III.13.4,
which concerns analytic-index excision. The two whole normal tubes are
transported to the common, possibly nonproper embedding into TN, then compared
by normalized tube-choice independence. No Cartesian hypothesis or restriction
of the large ambient tube into the prescribed open target is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

section OpenTangent

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

set_option backward.isDefEq.respectTransparency false in
/-- The actual tangent map of an open smooth embedding is an open embedding. -/
theorem isOpenEmbedding_smoothTangentMap
    (u : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hu : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ u)
    (hinj : Function.Injective u) : IsOpenEmbedding (smoothTangentMap u) := by
  let T := tangentMap 𝓘(ℝ, E) 𝓘(ℝ, F) u
  have hcont : Continuous T := (smoothTangentMap u).contMDiff.continuous
  -- The original base injection and invertible differential give tangent-map injectivity.
  have hinjT : Function.Injective T := by
    rintro ⟨x, v⟩ ⟨y, w⟩ heq
    have hbase : u x = u y := congrArg TotalSpace.proj heq
    have hxy : x = y := hinj hbase
    subst y
    have hv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) u x v =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) u x w := congrArg (fun z ↦ z.snd) heq
    have hvw : v = w := by
      apply (hu.mfderivToContinuousLinearEquiv (by simp) x).injective
      simpa only [← ContinuousLinearEquiv.coe_coe,
        IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe] using hv
    exact congrArg (TotalSpace.mk x) hvw
  -- At each vector, differentiate the same local inverse of the original map.
  have hopen : IsOpenMap T := by
    apply IsOpenMap.of_nhds_le
    intro z
    let h := hu z.proj
    let g := h.localInverse
    let S := tangentMap 𝓘(ℝ, F) 𝓘(ℝ, E) g
    -- The left inverse fixes this actual vector, so continuity has the required target.
    have hleft : S (T z) = z := by
      dsimp only [S, T, g]
      rw [← tangentMap_comp_at z (h.mdifferentiableAt_localInverse (by simp))
        (u.contMDiff.mdifferentiable (by simp) z.proj)]
      apply TotalSpace.ext (h.localInverse_left_inv h.localInverse_mem_target)
      have hd := h.localInverse_eventuallyEq_left.mfderiv_eq
        (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
      apply heq_of_eq
      have heval := congrArg (fun L ↦ L z.snd) hd
      rw [mfderiv_id] at heval
      exact heval
    have hS : Filter.Tendsto S (𝓝 (T z)) (𝓝 z) := by
      have hc := (h.contMDiffAt_localInverse.contMDiffAt_tangentMap
        (X := T z) (m := ∞) (by simp)).continuousAt
      have ht : Filter.Tendsto S (𝓝 (T z)) (𝓝 (S (T z))) := hc.tendsto
      rwa [hleft] at ht
    -- On the target chart, the right inverse identity differentiates on a neighborhood.
    have hright : T ∘ S =ᶠ[𝓝 (T z)] id := by
      filter_upwards [(g.open_source.preimage (FiberBundle.continuous_proj F
        (TangentSpace 𝓘(ℝ, F) (M := N)))).mem_nhds
          h.localInverse_mem_source] with w hw
      have hg := h.contMDiffOn_localInverse.contMDiffAt (g.open_source.mem_nhds hw)
      dsimp only [Function.comp_apply, T, S]
      rw [← tangentMap_comp_at w
        (u.contMDiff.mdifferentiable (by simp) (g w.proj))
        (hg.mdifferentiableAt (by simp))]
      apply TotalSpace.ext (h.localInverse_right_inv hw)
      have hevent : (u : M → N) ∘ g =ᶠ[𝓝 w.proj] id :=
        Filter.eventuallyEq_of_mem (g.open_source.mem_nhds hw) h.localInverse_eqOn_right
      have hd := hevent.mfderiv_eq (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F))
      apply heq_of_eq
      have heval := congrArg (fun L ↦ L w.snd) hd
      rw [mfderiv_id] at heval
      exact heval
    -- This continuous local right inverse sends neighborhoods to neighborhoods.
    calc
      𝓝 (T z) = Filter.map T (Filter.map S (𝓝 (T z))) := by
        rw [Filter.map_map, Filter.map_congr hright, Filter.map_id]
      _ ≤ Filter.map T (𝓝 z) := Filter.map_mono hS
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinjT hopen

end OpenTangent

section OpenSquare

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace M'] [ChartedSpace E M']
  [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace N'] [ChartedSpace F N']
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) ∞ M']
  [IsManifold 𝓘(ℝ, F) ∞ N] [IsManifold 𝓘(ℝ, F) ∞ N']
  [T2Space M] [T2Space M'] [T2Space N] [T2Space N']
  [SecondCountableTopology M] [SecondCountableTopology M']
  [SecondCountableTopology N] [SecondCountableTopology N']

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  ComplexBundle.isFiniteRank_pullback ComplexBundle.t2Space_totalSpace
  ComplexBundle.locallyCompactSpace_totalSpace

set_option maxHeartbeats 1800000 in
-- Normalize the same quotient-normal splittings and tubes in the open tangent square.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual geometric tangent pushforward commutes with open extension in a smooth square. -/
theorem tangentEmbeddingPushforward_open_naturality
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (hp : IsProperMap f)
    (f' : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M' N' ∞)
    (hf' : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f') (hp' : IsProperMap f')
    (u : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, E) M' M ∞)
    (hu : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ u)
    (hinju : Function.Injective u)
    (v : ContMDiffMap 𝓘(ℝ, F) 𝓘(ℝ, F) N' N ∞)
    (hv : IsLocalDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ v)
    (hinjv : Function.Injective v) (hcomm : ∀ x : M', f (u x) = v (f' x)) :
    letI : T2Space (TangentBundle 𝓘(ℝ, E) M) := (tangentBundle_topology E M).1
    letI : T2Space (TangentBundle 𝓘(ℝ, E) M') := (tangentBundle_topology E M').1
    letI : T2Space (TangentBundle 𝓘(ℝ, F) N) := (tangentBundle_topology F N).1
    letI : T2Space (TangentBundle 𝓘(ℝ, F) N') := (tangentBundle_topology F N').1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M) :=
      ChartedSpace.locallyCompactSpace (E × E) (TangentBundle 𝓘(ℝ, E) M)
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M') :=
      ChartedSpace.locallyCompactSpace (E × E) (TangentBundle 𝓘(ℝ, E) M')
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, F) N) :=
      ChartedSpace.locallyCompactSpace (F × F) (TangentBundle 𝓘(ℝ, F) N)
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, F) N') :=
      ChartedSpace.locallyCompactSpace (F × F) (TangentBundle 𝓘(ℝ, F) N')
    (compactSupportKZeroOpenPushforward (smoothTangentMap v)
      (isOpenEmbedding_smoothTangentMap v hv hinjv)).comp
        (tangentEmbeddingPushforward f' hf' hp') =
      (tangentEmbeddingPushforward f hf hp).comp
        (compactSupportKZeroOpenPushforward (smoothTangentMap u)
          (isOpenEmbedding_smoothTangentMap u hu hinju)) := by
  classical
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TM' := TangentBundle 𝓘(ℝ, E) M'
  let TN := TangentBundle 𝓘(ℝ, F) N
  let TN' := TangentBundle 𝓘(ℝ, F) N'
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TM' := (tangentBundle_topology E M').1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : T2Space TN' := (tangentBundle_topology F N').1
  let : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
  let : SecondCountableTopology TM' := (tangentBundle_topology E M').2.1
  let : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
  let : SecondCountableTopology TN' := (tangentBundle_topology F N').2.1
  let : ParacompactSpace TM := (tangentBundle_topology E M).2.2
  let : ParacompactSpace TM' := (tangentBundle_topology E M').2.2
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TM' := ChartedSpace.locallyCompactSpace (E × E) TM'
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let : LocallyCompactSpace TN' := ChartedSpace.locallyCompactSpace (F × F) TN'
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : LocallyCompactSpace M' := ChartedSpace.locallyCompactSpace E M'
  let Tu : C(TM', TM) := ⟨smoothTangentMap u, (smoothTangentMap u).contMDiff.continuous⟩
  let Tv : C(TN', TN) := ⟨smoothTangentMap v, (smoothTangentMap v).contMDiff.continuous⟩
  have huT : IsOpenEmbedding Tu := isOpenEmbedding_smoothTangentMap u hu hinju
  have hvT : IsOpenEmbedding Tv := isOpenEmbedding_smoothTangentMap v hv hinjv
  -- Both tubes will be normalized for this same possibly nonproper embedding into N.
  let k := f.comp u
  have hk : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ k := by
    have hder (x : M') : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) k x) := by
      change Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ((f : M → N) ∘ u) x)
      rw [mfderiv_comp x (f.contMDiff.mdifferentiable (by simp) (u x))
        (u.contMDiff.mdifferentiable (by simp) x)]
      exact (hf.isImmersion.mfderiv_injective (by simp) (u x)).comp
        (hu.isInvertible_mfderiv (by simp) x).injective
    exact ⟨isImmersion_of_injective_mfderiv k hder,
      hf.isEmbedding.comp (IsOpenEmbedding.of_continuous_injective_isOpenMap
        u.contMDiff.continuous hinju hu.isOpenMap).isEmbedding⟩
  let Sf := tangentNormalSplitting f hf
  let Tf := (nonempty_tubularNeighborhood (smoothTangentMap f)
    (isImmersion_smoothTangentMap f hf) (isSmoothEmbedding_tangentMap hf).isEmbedding
    (isProperMap_tangentMap hf hp)).some
  let Tf' := (nonempty_tubularNeighborhood (smoothTangentMap f')
    (isImmersion_smoothTangentMap f' hf') (isSmoothEmbedding_tangentMap hf').isEmbedding
    (isProperMap_tangentMap hf' hp')).some
  -- Source restriction and ambient transport use their actual normal derivative comparisons.
  obtain ⟨Sk, Tk₀, U, hsourceMap⟩ := exists_tangentEmbeddingTubularMap_openSource
    k f u hk hf hu hinju (fun _ ↦ rfl) Sf Tf
  obtain ⟨Sf', Tk₁, V, hambientMap⟩ := exists_tangentEmbeddingTubularMap_openAmbient
    f' k v hf' hk hv hinjv (fun x ↦ (hcomm x).symm) Sk Tf'
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  let := isFiniteRank_complexifiedNormalPullback f' hf'.isImmersion
  let := isFiniteRank_complexifiedNormalPullback k hk.isImmersion
  let h := (ComplexBundle.nonempty_continuousHermitianMetric
    (ComplexifiedNormalPullback f)).some
  let h' := (ComplexBundle.nonempty_continuousHermitianMetric
    (ComplexifiedNormalPullback f')).some
  let hK := (ComplexBundle.nonempty_continuousHermitianMetric
    (ComplexifiedNormalPullback k)).some
  let D := (Tu : TM' → TM) *ᵖ (ComplexifiedNormalPullback f)
  let (z : TM') : AddCommGroup (D z) := by
    change AddCommGroup (ComplexifiedNormalPullback f (Tu z)); infer_instance
  let (z : TM') : Module ℂ (D z) := by
    change Module ℂ (ComplexifiedNormalPullback f (Tu z)); infer_instance
  change ComplexBundle.Iso (ComplexifiedNormalPullback k) D at U
  let q := ComplexBundle.pullbackTotalMap (ComplexifiedNormalPullback f) Tu
  have hq : IsOpenEmbedding q :=
    (ComplexBundle.pullbackTotalMap_properties (ComplexifiedNormalPullback f) Tu).2 huT
  let τf := tangentEmbeddingTubularMap f hf Sf Tf
  let τf' := tangentEmbeddingTubularMap f' hf' Sf' Tf'
  let τ₀ := tangentEmbeddingTubularMap k hk Sk Tk₀
  let τ₁ := tangentEmbeddingTubularMap k hk Sk Tk₁
  have hfτ : IsOpenEmbedding τf := isOpenEmbedding_tangentEmbeddingTubularMap f hf Sf Tf
  have hf'τ : IsOpenEmbedding τf' := isOpenEmbedding_tangentEmbeddingTubularMap f' hf' Sf' Tf'
  have hτ₀ : IsOpenEmbedding τ₀ := isOpenEmbedding_tangentEmbeddingTubularMap k hk Sk Tk₀
  have hτ₁ : IsOpenEmbedding τ₁ := isOpenEmbedding_tangentEmbeddingTubularMap k hk Sk Tk₁
  -- The complex bundle isomorphism and the original open Thom law give the source square.
  have hsource : tangentEmbeddingPushforwardWith k hk Sk Tk₀ hK =
      (tangentEmbeddingPushforwardWith f hf Sf Tf h).comp
        (compactSupportKZeroOpenPushforward Tu huT) := by
    have hi := hK.supportedThomHom_iso (h.pullback Tu) U
    have ho := h.supportedThomHom_openPushforward Tu huT
    have hm : (τ₀ : TotalSpace Unit (ComplexifiedNormalPullback k) → TN) =
        (τf : TotalSpace Unit (ComplexifiedNormalPullback f) → TN) ∘ q ∘ U.totalHomeomorph :=
      funext hsourceMap
    change (compactSupportKZeroOpenPushforward τ₀ hτ₀).comp hK.supportedThomHom =
      ((compactSupportKZeroOpenPushforward τf hfτ).comp h.supportedThomHom).comp
        (compactSupportKZeroOpenPushforward Tu huT)
    simp only [hm]
    rw [compactSupportKZeroOpenPushforward_comp (q ∘ U.totalHomeomorph)
      (hq.comp U.totalHomeomorph.isOpenEmbedding) τf hfτ,
      compactSupportKZeroOpenPushforward_comp U.totalHomeomorph
        U.totalHomeomorph.isOpenEmbedding q hq,
      compactSupportKZeroOpenPushforward_homeomorph]
    simp only [AddMonoidHom.comp_assoc]
    rw [hi, ho]
  -- Thom naturality for the specified complex-bundle isomorphism gives the ambient square.
  have hambient : (compactSupportKZeroOpenPushforward Tv hvT).comp
      (tangentEmbeddingPushforwardWith f' hf' Sf' Tf' h') =
        tangentEmbeddingPushforwardWith k hk Sk Tk₁ hK := by
    have hi := h'.supportedThomHom_iso hK V
    have hm : (Tv : TN' → TN) ∘ τf' =
        (τ₁ : TotalSpace Unit (ComplexifiedNormalPullback k) → TN) ∘ V.totalHomeomorph :=
      funext hambientMap
    change (compactSupportKZeroOpenPushforward Tv hvT).comp
      ((compactSupportKZeroOpenPushforward τf' hf'τ).comp h'.supportedThomHom) =
        (compactSupportKZeroOpenPushforward τ₁ hτ₁).comp hK.supportedThomHom
    rw [← AddMonoidHom.comp_assoc,
      ← compactSupportKZeroOpenPushforward_comp τf' hf'τ Tv hvT]
    simp only [hm]
    rw [compactSupportKZeroOpenPushforward_comp V.totalHomeomorph
      V.totalHomeomorph.isOpenEmbedding τ₁ hτ₁, AddMonoidHom.comp_assoc,
      compactSupportKZeroOpenPushforward_homeomorph, hi]
  -- Whole-tube choice independence applies to k without properness or a Cartesian square.
  have htubes := tangentEmbeddingPushforwardWith_eq k hk Sk Sk Tk₁ Tk₀ hK hK
  have hfwith : tangentEmbeddingPushforward f hf hp =
      tangentEmbeddingPushforwardWith f hf Sf Tf h := by
    unfold tangentEmbeddingPushforward
    exact tangentEmbeddingPushforwardWith_eq f hf _ _ _ _ _ _
  have hf'with : tangentEmbeddingPushforward f' hf' hp' =
      tangentEmbeddingPushforwardWith f' hf' Sf' Tf' h' := by
    unfold tangentEmbeddingPushforward
    exact tangentEmbeddingPushforwardWith_eq f' hf' _ _ _ _ _ _
  rw [hfwith, hf'with]
  exact hambient.trans (htubes.trans hsource)

end OpenSquare

end AtiyahSinger
