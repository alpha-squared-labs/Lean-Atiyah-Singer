/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticExcision
public import AtiyahSinger.Analysis.AssociatedSphereIndex
public import AtiyahSinger.Analysis.FixedPointAnalyticIndex
public import AtiyahSinger.Analysis.FrameSphereEmbeddingIndex
public import AtiyahSinger.Analysis.LinearModelTangentIndex
public import AtiyahSinger.Analysis.TangentEmbeddingIndexLocality
public import AtiyahSinger.Analysis.TangentAnalyticIndex
public import AtiyahSinger.Geometry.EmbeddingFrameSphereNeighborhood
public import AtiyahSinger.Geometry.FrameSphereAdaptedHorizontalLift
public import AtiyahSinger.Geometry.FrameSphereStereographic
public import AtiyahSinger.Geometry.HorizontalLiftMetric
public import AtiyahSinger.Geometry.LinearModelMusical
public import AtiyahSinger.Topology.CotangentEmbeddingPushforward
public import AtiyahSinger.Topology.TangentFullModelDiffeomorphPushforward

/-!
# Analytic index and the original compact embedding pushforward

Public module ID: M0456.

P08 is SG III.13 Property 2, printed p.247, proved at the end of the index
argument on p.254. For a smooth embedding between compact manifolds without
boundary, the original tangent Thom-to-tube pushforward preserves the analytic
index. Its already defined musical conjugate gives the same statement on
the actual cotangent K groups, for arbitrary supplied smooth metrics and
independent positive smooth densities.

The full component analytic index is used on every original K class. The
source need not be connected or nonempty, the normal rank may be zero, and
symbol representatives need not have a common global rank. Properness is
retained as the witness already required by the original pushforward API;
for these compact sources it also follows from continuity and a Hausdorff
target. No extra dimension inequality is imposed on an empty source.

The proof follows the source: the actual normal neighborhood, its associated
sphere compactification, the original twisted-product formula, and the full
orthogonal fixed-point index. Equalities of the actual Thom and twisted-product
classes retain their coordinate normalization and positive proper homotopy.
The actual full-model musical square and common-open analytic excision give
the result for the supplied independent densities. The index-preservation
conclusion is not used to define the pushforward.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold MeasureTheory Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  normalBundleTopology orthogonalFrameTopology continuousSMul_orthogonalSphere
  complexifiedNormalPullbackTopology

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 m) ∞ N] [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]

set_option maxSynthPendingDepth 60 in
set_option maxHeartbeats 12000000 in
-- The original normal sphere, its two manifold models and four actual bundle maps coexist here.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- SG Property 2: the actual cotangent embedding pushforward preserves every class's index. -/
theorem analyticIndexOfComponents_cotangentEmbeddingPushforward
    (f : ContMDiffMap (𝓡 n) (𝓡 m) M N ∞)
    (hf : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ f) (hp : IsProperMap f)
    (gM : SmoothTangentMetric (n := n) (M := M))
    (gN : SmoothTangentMetric (n := m) (M := N))
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν]
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    analyticIndexOfComponents ν (cotangentEmbeddingPushforward f hf hp gM gN u) =
      analyticIndexOfComponents μ u := by
  classical
  let En := EuclideanSpace ℝ (Fin n)
  let Em := EuclideanSpace ℝ (Fin m)
  let TM := TangentBundle (𝓡 n) M
  let TN := TangentBundle (𝓡 m) N
  let : T2Space TM := (tangentBundle_topology En M).1
  let : T2Space TN := (tangentBundle_topology Em N).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (En × En) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (Em × Em) TN
  -- The empty source has zero reduced K group; no codimension inequality is used there.
  rcases isEmpty_or_nonempty M with hM | hM
  · let := hM
    let X := CotangentTotalSpace (n := n) (M := M)
    have hzero : u = 0 := by
      apply Subtype.ext
      have hsplit : (algebraMap ℂ C(OnePoint X, ℂ)).comp
          (ContinuousMap.evalAlgHom ℂ ℂ (OnePoint.infty : OnePoint X)).toRingHom =
          RingHom.id C(OnePoint X, ℂ) := by
        ext a z
        change a OnePoint.infty = a z
        induction z using OnePoint.rec with
        | infty => rfl
        | coe z => exact isEmptyElim z.proj
      have hu := u.property
      change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ
        (OnePoint.infty : OnePoint X)).toRingHom u.val = 0 at hu
      have h := congrArg (kZeroMap (algebraMap ℂ C(OnePoint X, ℂ))) hu
      rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp, hsplit, kZeroMap_id] at h
      simpa using h
    rw [hzero, map_zero, map_zero, map_zero]
  · let := hM
    let v := (tangentCotangentKZeroEquiv gM).symm u
    let r := Module.finrank ℝ Em - Module.finrank ℝ En
    let R := EuclideanSpace ℝ (Fin r)
    let V := NormalBundle (𝓡 n) (𝓡 m) f
    let := normalBundleFiberBundle f hf.isImmersion
    let := normalBundleVectorBundle f hf.isImmersion
    let := normalBundleContMDiffVectorBundle f hf.isImmersion
    let : ∀ x, TopologicalSpace (V x) := fun _ ↦ inferInstance
    let : ∀ x, AddCommGroup (V x) := fun _ ↦ inferInstance
    let : ∀ x, Module ℝ (V x) := fun _ ↦ inferInstance
    let : ∀ x, IsTopologicalAddGroup (V x) := fun _ ↦ inferInstance
    let : ∀ x, ContinuousConstSMul ℝ (V x) := fun _ ↦ inferInstance
    -- The metric is placed on the actual quotient normal bundle and its original atlas.
    let gV := smoothRiemannianMetric (EB := En) (NormalModel En Em) V
    let : RiemannianBundle V := ⟨gV.toRiemannianMetric⟩
    let : ∀ x, NormedAddCommGroup (V x) :=
      instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    let : ∀ x, InnerProductSpace ℝ (V x) := instInnerProductSpaceReal
    let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (NormalModel En Em) V :=
      ⟨gV.inner, gV.contMDiff, fun _ _ _ ↦ rfl⟩
    let := continuousSMul_orthogonalFrame r V (𝓡 n)
    let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
    let GO := Matrix.orthogonalGroup (Fin r) ℝ
    let P := OrthogonalFrameBundle r V
    let Z := AssociatedBundle GO P (OrthogonalSphere r)
    let := S.toIsPrincipalBundle
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let : T2Space Z := associatedBundle_t2Space S.toIsPrincipalBundle
    have hcontrol : associatedControl GO P (OrthogonalSphere r) Set.univ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro z
      induction z using Quotient.inductionOn with
      | h z => exact ⟨z, ⟨Set.mem_univ z.1, Set.mem_univ z.2⟩, rfl⟩
    let : CompactSpace Z := ⟨by
      rw [← hcontrol]
      exact isCompact_associatedControl S.toIsPrincipalBundle Set.univ isCompact_univ
        (fun _ _ ↦ Iff.rfl)⟩
    let : SecondCountableTopology Z :=
      ChartedSpace.secondCountable_of_sigmaCompact (En × R) Z
    let : MeasurableSpace Z := borel Z
    let : BorelSpace Z := ⟨rfl⟩
    let J := 𝓘(ℝ, En × R)
    let a := frameSphereStereographic (EB := En) r V
    let j₀ : ContMDiffMap (𝓡 n) J M Z ∞ :=
      ⟨fun x ↦ a.symm ⟨x, 0⟩,
        (frameSphereStereographic_spec (EB := En) r V).2.2.2.2.2.comp
          (contMDiff_zeroSection ℝ V)⟩
    let hj₀ := isSmoothEmbedding_frameSphere_zeroSection (EB := En) r V
    have hpj₀ : IsProperMap j₀ := j₀.contMDiff.continuous.isProperMap
    let TZ := TangentBundle J Z
    let : T2Space TZ := (tangentBundle_topology (En × R) Z).1
    let : LocallyCompactSpace TZ :=
      ChartedSpace.locallyCompactSpace ((En × R) × (En × R)) TZ
    -- Adapt the lift along this actual section and construct a metric compatible with gM.
    obtain ⟨H, hH⟩ := exists_frameSphere_adaptedHorizontalLift (EB := En) r V
      (associatedSphereHorizontalLift S)
    let h₀ := smoothRiemannianMetric (EB := En × R) (En × R) (TangentSpace J : Z → Type _)
    obtain ⟨h, _, hcompat⟩ := H.exists_compatibleMetric (smoothAssociatedSphereProjection S) gM h₀
    obtain ⟨K, T, hSphere⟩ :=
      exists_frameSphere_tangentPushforward_index r V μ H gM h hcompat hH
    let : ParacompactSpace TM := (tangentBundle_topology En M).2.2
    let := isFiniteRank_complexifiedNormalPullback j₀ hj₀.isImmersion
    let hN := (ComplexBundle.nonempty_continuousHermitianMetric
      (ComplexifiedNormalPullback j₀)).some
    have hWith : tangentEmbeddingPushforward j₀ hj₀ hpj₀ =
        tangentEmbeddingPushforwardWith j₀ hj₀ K T hN := by
      unfold tangentEmbeddingPushforward
      exact tangentEmbeddingPushforwardWith_eq j₀ hj₀ _ _ _ _ _ _
    let dNative := (exists_tangentMusical_diffeomorph h).choose
    let := dNative.toHomeomorph.t2Space
    let := dNative.toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
    have hSphereValue : associatedSphereAnalyticIndex S
        (compactSupportKZeroHomeomorph dNative.toHomeomorph
          (tangentEmbeddingPushforward j₀ hj₀ hpj₀ v)) = tangentAnalyticIndex μ v := by
      have hchoice := DFunLike.congr_fun hWith v
      exact (congrArg (fun w : CompactSupportKZero TZ ↦ associatedSphereAnalyticIndex S
        (compactSupportKZeroHomeomorph dNative.toHomeomorph w)) hchoice).trans (hSphere hN v)
    -- The original normal tube supplies a common open model, with its explicit ambient recharting.
    obtain ⟨l, hl⟩ := exists_normal_frameSphere_neighborhood f hf hp
    let := linearModelChartedSpace l Z
    let := isManifold_linearModelChartedSpace l Z
    obtain ⟨j, hj, hpj, hjv, U, s, hs, hps, hsf, d, hd⟩ := hl
    let W : TopologicalSpace.Opens Z := ⟨a.source, a.open_source⟩
    let dModel := linearModelDiffeomorph l Z
    let TZm := TangentBundle (𝓡 m) Z
    let : T2Space TZm := (tangentBundle_topology Em Z).1
    let : LocallyCompactSpace TZm := ChartedSpace.locallyCompactSpace (Em × Em) TZm
    obtain ⟨ρ, hρ⟩ := exists_smoothPositiveMeasure (n := m) (M := Z)
    let := hρ
    obtain ⟨t, ht, hindexModel⟩ := exists_linearModelTangentIndex_comparison l Z h ρ hρ
    have heModel : IsSmoothEmbedding J (𝓡 m) ∞ dModel :=
      isSmoothEmbedding_of_leftInverse dModel.toContMDiffMap dModel.symm.toContMDiffMap
        dModel.symm_apply_apply
    have hpModel : IsProperMap dModel := dModel.toHomeomorph.isProperMap
    have htMap (z : TZ) : t z = tangentMap J (𝓡 m) dModel z := by
      rw [ht]
      change (⟨z.proj, l z.snd⟩ : TZm) =
        ⟨z.proj, mfderiv J (𝓡 m) (id : Z → Z) z.proj z.snd⟩
      rw [(contMDiff_mfderiv_linearModelId l Z).2.1]
      rfl
    have hjEq : j = dModel.toContMDiffMap.comp j₀ := by
      apply ContMDiffMap.ext
      intro x
      exact hjv x
    have hpush := tangentEmbeddingPushforward_comp j₀ dModel.toContMDiffMap hj₀ heModel
      hpj₀ hpModel
    have hpushJ : tangentEmbeddingPushforward j hj hpj =
        (tangentEmbeddingPushforward dModel.toContMDiffMap heModel hpModel).comp
          (tangentEmbeddingPushforward j₀ hj₀ hpj₀) := by
      subst j
      exact hpush
    have hdiffeo := tangentEmbeddingPushforward_eq_of_diffeomorph
      dModel heModel hpModel t htMap
    have hpushValue : tangentEmbeddingPushforward j hj hpj v =
        compactSupportKZeroHomeomorph t (tangentEmbeddingPushforward j₀ hj₀ hpj₀ v) :=
      (DFunLike.congr_fun hpushJ v).trans
        (DFunLike.congr_fun hdiffeo (tangentEmbeddingPushforward j₀ hj₀ hpj₀ v))
    -- The model index comparison uses this same tangent map and the supplied positive density.
    have hmodel : tangentAnalyticIndex ρ (tangentEmbeddingPushforward j hj hpj v) =
        associatedSphereAnalyticIndex S
          (compactSupportKZeroHomeomorph dNative.toHomeomorph
            (tangentEmbeddingPushforward j₀ hj₀ hpj₀ v)) := by
      have hrechart := DFunLike.congr_fun
        (analyticIndexLinearModel_independent_equiv l Z
          (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm)
        (compactSupportKZeroHomeomorph dNative.toHomeomorph
          (tangentEmbeddingPushforward j₀ hj₀ hpj₀ v))
      exact (congrArg (tangentAnalyticIndex ρ) hpushValue).trans
        ((hindexModel (tangentEmbeddingPushforward j₀ hj₀ hpj₀ v)).symm.trans hrechart)
    -- Analytic excision compares the original f and the same sphere section through that tube.
    have hlocal : tangentAnalyticIndex ν (tangentEmbeddingPushforward f hf hp v) =
        tangentAnalyticIndex ρ (tangentEmbeddingPushforward j hj hpj v) :=
      tangentAnalyticIndex_embedding_eq_of_commonOpen
        (n := n) (m := m) (M := M) (O := U) (N := N) (P := Z)
        f hf hp j hj hpj s hs hps U W (Diffeomorph.refl (𝓡 m) U ∞) d hsf hd ν ρ v
    have hindex : tangentAnalyticIndex ν (tangentEmbeddingPushforward f hf hp v) =
        tangentAnalyticIndex μ v := hlocal.trans (hmodel.trans hSphereValue)
    rw [tangentAnalyticIndex_eq ν gN, tangentAnalyticIndex_eq μ gM] at hindex
    simpa only [v, cotangentEmbeddingPushforward, AddMonoidHom.comp_apply,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
      AddEquiv.apply_symm_apply] using hindex

/-- The same compact embedding compatibility on SG's original tangent K groups. -/
theorem tangentAnalyticIndex_tangentEmbeddingPushforward
    (f : ContMDiffMap (𝓡 n) (𝓡 m) M N ∞)
    (hf : IsSmoothEmbedding (𝓡 n) (𝓡 m) ∞ f) (hp : IsProperMap f)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν] :
    letI : T2Space (TangentBundle (𝓡 n) M) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
    letI : T2Space (TangentBundle (𝓡 m) N) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) N).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 n) M) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (TangentBundle (𝓡 n) M)
    letI : LocallyCompactSpace (TangentBundle (𝓡 m) N) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (TangentBundle (𝓡 m) N)
    ∀ u : CompactSupportKZero (TangentBundle (𝓡 n) M),
      tangentAnalyticIndex ν (tangentEmbeddingPushforward f hf hp u) =
        tangentAnalyticIndex μ u := by
  /- Stage 1: choose existing smooth tangent metrics on the original M and
  N. The supplied-metric formula tangentAnalyticIndex_eq expresses both
  displayed maps using exactly their musical K equivalences and the
  original component indices.
  Stage 2: apply the preceding cotangent compatibility to the forward
  musical image of this same u. In cotangentEmbeddingPushforward the
  source inverse musical map cancels that exact forward equivalence;
  the remaining target musical map is the one in Stage 1. Thus the
  middle homomorphism is the original tangentEmbeddingPushforward of f,
  not a new map defined by requiring index preservation.
  Stage 3: metric independence removes the auxiliary choices. The given
  density on each separate manifold remains unchanged. The same argument
  includes zero normal rank, disconnected and empty compact manifolds. -/
  classical
  intro u
  let gM : SmoothTangentMetric (n := n) (M := M) :=
    Classical.choice SmoothTangentMetric.nonempty
  let gN : SmoothTangentMetric (n := m) (M := N) :=
    Classical.choice SmoothTangentMetric.nonempty
  -- Use the same forward musical image as the input to the cotangent formula.
  have hindex := analyticIndexOfComponents_cotangentEmbeddingPushforward f hf hp gM gN
    μ ν ((tangentCotangentKZeroEquiv gM) u)
  rw [tangentAnalyticIndex_eq ν gN, tangentAnalyticIndex_eq μ gM]
  simpa only [cotangentEmbeddingPushforward, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
    AddEquiv.symm_apply_apply] using hindex

end AtiyahSinger
