/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereTangentNormalBundle
public import AtiyahSinger.Geometry.TubularNeighborhood

/-!
# A normalized tube for the original frame-sphere tangent embedding

Public module ID: M1253.

For a horizontal lift adapted to the south section, the actual horizontal-
plus-vertical parametrization is transported through its own ordered normal
derivative. The result is a tubular neighborhood of the
original tangent embedding, normalized on the prescribed quotient normal.
The same original normal isomorphism is used on both ordered factors.

The whole doubled bundle maps to the tangent vectors over the original south
chart, including rank zero. No cotangent metric comparison is asserted here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere
  normalBundleTopology verticalTangentTopology tangentBundleFullChartedSpace
  tangentBundle_full_isManifold

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 55 in
set_option maxHeartbeats 4000000 in
-- Normalize the same whole chart by its actual radial derivative, in the original normal atlas.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- With a south-adapted horizontal lift, the tangent parametrization becomes a tube
through its ordered normal derivative. -/
theorem exists_frameSphere_tangentTubularNeighborhood
    (H : letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
      let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let I := 𝓘(ℝ, EB)
    let J := 𝓘(ℝ, EB × R)
    let H' : SmoothHorizontalLift (smoothAssociatedSphereProjection S) := H
    let a := frameSphereStereographic (EB := EB) r V
    let j : ContMDiffMap I J B Z ∞ :=
      ⟨fun x ↦ a.symm ⟨x, 0⟩,
        (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2.comp
          (contMDiff_zeroSection ℝ V)⟩
    let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V
    let F := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose
    let e := (exists_frameSphere_normalEquiv (EB := EB) r V).choose
    ∀ (_hH : ∀ x : B, H'.lift (j x) = mfderiv I J j x),
      ∃ K : TangentNormalSplitting j hj,
        ∃ T : TubularNeighborhood (smoothTangentMap j) (isImmersion_smoothTangentMap j hj),
          ∀ (z : TangentBundle I B) (u w : V z.proj),
            (T.diffeomorph ⟨z, (K.equiv z).symm (e z.proj u, e z.proj w)⟩ :
              TangentBundle J Z) = F ⟨z, u, w⟩ := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let IT := 𝓘(ℝ, EB × EB)
  let JT := 𝓘(ℝ, (EB × R) × (EB × R))
  let a := frameSphereStereographic (EB := EB) r V
  let j : ContMDiffMap I J B Z ∞ :=
    ⟨fun x ↦ a.symm ⟨x, 0⟩,
      (frameSphereStereographic_spec (EB := EB) r V).2.2.2.2.2.comp
        (contMDiff_zeroSection ℝ V)⟩
  let hj := isSmoothEmbedding_frameSphere_zeroSection (EB := EB) r V
  let F := (exists_frameSphere_tangentParametrization (EB := EB) r V H).choose
  let e := (exists_frameSphere_normalEquiv (EB := EB) r V).choose
  have he := (exists_frameSphere_normalEquiv (EB := EB) r V).choose_spec
  dsimp only
  intro hH
  have hdata := exists_frameSphere_tangentNormalSplitting (EB := EB) r V H hH
  let K : TangentNormalSplitting j hj := hdata.2.choose
  have hK := hdata.2.choose_spec
  have hzero := hdata.1
  let prT : ContMDiffMap IT I (TangentBundle I B) B ∞ :=
    ⟨Bundle.TotalSpace.proj, (smoothTangentBundleProjection EB B).contMDiff⟩
  let Vt := (prT : TangentBundle I B → B) *ᵖ V
  let W := Vt ×ᵇ Vt
  let : FiberBundle (R × R) W := by
    change FiberBundle (R × R) (Vt ×ᵇ Vt)
    infer_instance
  let : VectorBundle ℝ (R × R) W := by
    change VectorBundle ℝ (R × R) (Vt ×ᵇ Vt)
    infer_instance
  let : ContMDiffVectorBundle ∞ (R × R) W IT := by
    change ContMDiffVectorBundle ∞ (R × R) (Vt ×ᵇ Vt) IT
    infer_instance
  let C := IT.prod 𝓘(ℝ, R × R)
  let fT := smoothTangentMap j
  let hfT := isImmersion_smoothTangentMap j hj
  let := normalBundleFiberBundle j hj.isImmersion
  let := normalBundleVectorBundle j hj.isImmersion
  let := normalBundleContMDiffVectorBundle j hj.isImmersion
  let := normalBundleFiberBundle fT hfT
  let := normalBundleVectorBundle fT hfT
  let := normalBundleContMDiffVectorBundle fT hfT
  let ν := NormalBundle I J j
  let νT := NormalBundle IT JT fT
  let N := NormalModel EB (EB × R)
  let NT := NormalModel (EB × EB) ((EB × R) × (EB × R))
  let νP := (prT : TangentBundle I B → B) *ᵖ ν
  -- Apply the same original normal isomorphism to both pulled factors.
  have hforward : ContMDiff C (IT.prod 𝓘(ℝ, N × N)) ∞
      (fun z : TotalSpace (R × R) W ↦
        (⟨z.proj, e z.proj.proj z.snd.1, e z.proj.proj z.snd.2⟩ :
          TotalSpace (N × N) (νP ×ᵇ νP))) := by
    intro z
    have ht : ContMDiffAt C IT ∞ (fun w : TotalSpace (R × R) W ↦ w.proj) z :=
      Bundle.contMDiffAt_proj W
    have hb := prT.contMDiff.contMDiffAt.comp z ht
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt C C ∞ id z)).2
    have hfirst : ContMDiffAt C (I.prod 𝓘(ℝ, R)) ∞
        (fun w : TotalSpace (R × R) W ↦
          (⟨w.proj.proj, w.snd.1⟩ : TotalSpace R V)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (ContinuousLinearMap.fst ℝ R R).contDiff.contMDiff.contMDiffAt.comp z hc⟩
    have hsecond : ContMDiffAt C (I.prod 𝓘(ℝ, R)) ∞
        (fun w : TotalSpace (R × R) W ↦
          (⟨w.proj.proj, w.snd.2⟩ : TotalSpace R V)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (ContinuousLinearMap.snd ℝ R R).contDiff.contMDiff.contMDiffAt.comp z hc⟩
    have hu := he.2.1.contMDiffAt.comp z hfirst
    have hw := he.2.1.contMDiffAt.comp z hsecond
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨ht, (Bundle.contMDiffAt_totalSpace.mp hu).2.prodMk_space
      (Bundle.contMDiffAt_totalSpace.mp hw).2⟩
  have hinverse : ContMDiff (IT.prod 𝓘(ℝ, N × N)) C ∞
      (fun z : TotalSpace (N × N) (νP ×ᵇ νP) ↦
        (⟨z.proj, (e z.proj.proj).symm z.snd.1,
          (e z.proj.proj).symm z.snd.2⟩ : TotalSpace (R × R) W)) := by
    intro z
    have ht : ContMDiffAt (IT.prod 𝓘(ℝ, N × N)) IT ∞
        (fun w : TotalSpace (N × N) (νP ×ᵇ νP) ↦ w.proj) z :=
      Bundle.contMDiffAt_proj (νP ×ᵇ νP)
    have hb := prT.contMDiff.contMDiffAt.comp z ht
    have hc := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (IT.prod 𝓘(ℝ, N × N))
        (IT.prod 𝓘(ℝ, N × N)) ∞ id z)).2
    have hfirst : ContMDiffAt (IT.prod 𝓘(ℝ, N × N)) (I.prod 𝓘(ℝ, N)) ∞
        (fun w : TotalSpace (N × N) (νP ×ᵇ νP) ↦
          (⟨w.proj.proj, w.snd.1⟩ : TotalSpace N ν)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (ContinuousLinearMap.fst ℝ N N).contDiff.contMDiff.contMDiffAt.comp z hc⟩
    have hsecond : ContMDiffAt (IT.prod 𝓘(ℝ, N × N)) (I.prod 𝓘(ℝ, N)) ∞
        (fun w : TotalSpace (N × N) (νP ×ᵇ νP) ↦
          (⟨w.proj.proj, w.snd.2⟩ : TotalSpace N ν)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, (ContinuousLinearMap.snd ℝ N N).contDiff.contMDiff.contMDiffAt.comp z hc⟩
    have hu := he.2.2.contMDiffAt.comp z hfirst
    have hw := he.2.2.contMDiffAt.comp z hsecond
    apply Bundle.contMDiffAt_totalSpace.mpr
    exact ⟨ht, (Bundle.contMDiffAt_totalSpace.mp hu).2.prodMk_space
      (Bundle.contMDiffAt_totalSpace.mp hw).2⟩
  let dV : TotalSpace (R × R) W ≃ₘ⟮C, IT.prod 𝓘(ℝ, N × N)⟯
      TotalSpace (N × N) (νP ×ᵇ νP) :=
    { toFun := fun z ↦ ⟨z.proj, e z.proj.proj z.snd.1, e z.proj.proj z.snd.2⟩
      invFun := fun z ↦ ⟨z.proj, (e z.proj.proj).symm z.snd.1,
        (e z.proj.proj).symm z.snd.2⟩
      left_inv := by
        rintro ⟨z, u, w⟩
        change (⟨z, (e z.proj).symm (e z.proj u), (e z.proj).symm (e z.proj w)⟩ :
          TotalSpace (R × R) W) = ⟨z, u, w⟩
        rw [(e z.proj).symm_apply_apply, (e z.proj).symm_apply_apply]
      right_inv := by
        rintro ⟨z, u, w⟩
        change (⟨z, e z.proj ((e z.proj).symm u), e z.proj ((e z.proj).symm w)⟩ :
          TotalSpace (N × N) (νP ×ᵇ νP)) = ⟨z, u, w⟩
        rw [(e z.proj).apply_symm_apply, (e z.proj).apply_symm_apply]
      contMDiff_toFun := hforward
      contMDiff_invFun := hinverse }
  let dK : TotalSpace (N × N) (νP ×ᵇ νP) ≃ₘ⟮IT.prod 𝓘(ℝ, N × N),
      IT.prod 𝓘(ℝ, NT)⟯ TotalSpace NT νT :=
    { toFun := fun z ↦ ⟨z.proj, (K.equiv z.proj).symm z.snd⟩
      invFun := fun z ↦ ⟨z.proj, K.equiv z.proj z.snd⟩
      left_inv := by
        intro z
        change (⟨z.proj, K.equiv z.proj ((K.equiv z.proj).symm z.snd)⟩ :
          TotalSpace (N × N) (νP ×ᵇ νP)) = z
        rw [(K.equiv z.proj).apply_symm_apply]
      right_inv := by
        intro z
        change (⟨z.proj, (K.equiv z.proj).symm (K.equiv z.proj z.snd)⟩ :
          TotalSpace NT νT) = z
        rw [(K.equiv z.proj).symm_apply_apply]
      contMDiff_toFun := K.contMDiff_invFun
      contMDiff_invFun := K.contMDiff_toFun }
  let U : TopologicalSpace.Opens (TangentBundle J Z) :=
    ⟨Bundle.TotalSpace.proj ⁻¹' a.source,
      a.open_source.preimage (FiberBundle.continuous_proj (EB × R) (TangentSpace J))⟩
  let F' : TotalSpace (R × R) W ≃ₘ⟮C, JT⟯ U :=
    { toEquiv := F.toEquiv
      contMDiff_toFun := by
        change ContMDiff (IT.prod 𝓘(ℝ, R × R)) JT ∞ _
        rw (occs := .pos [1]) [show IT = I.tangent from modelWithCornersSelf_prod]
        rw (occs := .pos [1]) [show JT = J.tangent from modelWithCornersSelf_prod]
        exact F.contMDiff_toFun
      contMDiff_invFun := by
        change ContMDiff JT (IT.prod 𝓘(ℝ, R × R)) ∞ _
        rw (occs := .pos [1]) [show JT = J.tangent from modelWithCornersSelf_prod]
        rw (occs := .pos [1]) [show IT = I.tangent from modelWithCornersSelf_prod]
        exact F.contMDiff_invFun }
  let D : TotalSpace NT νT ≃ₘ⟮IT.prod 𝓘(ℝ, NT), JT⟯ U := (dV.trans dK).symm.trans F'
  have hD (z : TangentBundle I B) (v : νT z) :
      (D ⟨z, v⟩ : TangentBundle J Z) =
        F ⟨z, (e z.proj).symm (K.equiv z v).1, (e z.proj).symm (K.equiv z v).2⟩ := rfl
  -- The radial identity already proved for this K is exactly the tube normalization.
  let T : TubularNeighborhood fT hfT :=
    { target := U
      diffeomorph := D
      map_zero := by
        intro z
        rw [hD, (K.equiv z).map_zero]
        change (F ⟨z, (e z.proj).symm 0, (e z.proj).symm 0⟩ : TangentBundle J Z) = fT z
        rw [(e z.proj).symm.map_zero]
        exact hzero z
      normal_deriv := by
        intro z
        dsimp only
        intro v
        let b := trivializationAt NT νT z
        let c := b.continuousLinearEquivAt ℝ z (mem_baseSet_trivializationAt NT νT z)
        let ep := (e z.proj).prodCongr (e z.proj)
        let Avert : NT →L[ℝ] (V z.proj × V z.proj) :=
          ep.symm.toContinuousLinearMap.comp
            ((K.equiv z).toContinuousLinearMap.comp c.symm.toContinuousLinearMap)
        let f : NT → TangentBundle J Z := fun u ↦ D ⟨z, c.symm u⟩
        have hf : ContMDiff 𝓘(ℝ, NT) JT ∞ f := by
          apply (contMDiff_subtype_val.comp D.contMDiff_toFun).comp
          intro u
          apply Bundle.contMDiffAt_totalSpace.mpr
          refine ⟨contMDiffAt_const, ?_⟩
          apply contMDiffAt_id.congr_of_eventuallyEq
          apply Filter.Eventually.of_forall
          intro u
          change (b ⟨z, c.symm u⟩).2 = u
          exact c.apply_symm_apply u
        let l : ℝ →L[ℝ] NT := (ContinuousLinearMap.id ℝ ℝ).smulRight v
        have hfun : (fun t : ℝ ↦
            (F ⟨z, t • (Avert v).1, t • (Avert v).2⟩ : TangentBundle J Z)) = f ∘ l := by
          funext t
          change _ = (D ⟨z, c.symm (t • v)⟩ : TangentBundle J Z)
          rw [hD]
          change _ = (F ⟨z, (Avert (t • v)).1, (Avert (t • v)).2⟩ : TangentBundle J Z)
          rw [map_smul]
          rfl
        have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, NT)) (I'' := JT) 0
          (hf.mdifferentiable (by simp) (l 0))
          (l.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
        rw [show l 0 = 0 from map_zero l, l.hasFDerivAt.hasMFDerivAt.mfderiv] at hchain
        have hd := DFunLike.congr_fun hchain
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
        change _ = mfderiv 𝓘(ℝ, NT) JT f 0 (l (1 : ℝ)) at hd
        have hder : mfderiv 𝓘(ℝ, ℝ) JT
            (fun t : ℝ ↦ (F ⟨z, t • (Avert v).1, t • (Avert v).2⟩ : TangentBundle J Z)) 0
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) =
            mfderiv 𝓘(ℝ, NT) JT f 0 ((NormedSpace.fromTangentSpace (0 : NT)).symm v) := by
          have hh := congrArg (fun k : ℝ → TangentBundle J Z ↦
            (mfderiv 𝓘(ℝ, ℝ) JT k 0
              ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) :
                (EB × R) × (EB × R))) hfun
          exact hh.trans (hd.trans (congrArg (mfderiv 𝓘(ℝ, NT) JT f 0) (one_smul ℝ v)))
        have hn := hK z (Avert v).1 (Avert v).2
        have heA : (e z.proj (Avert v).1, e z.proj (Avert v).2) =
            K.equiv z (c.symm v) := ep.apply_symm_apply (K.equiv z (c.symm v))
        change (LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ
          (mfderiv 𝓘(ℝ, NT) JT f 0 ((NormedSpace.fromTangentSpace (0 : NT)).symm v)) = c.symm v
        calc
          _ = (LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ
              (mfderiv 𝓘(ℝ, ℝ) JT (fun t : ℝ ↦
                (F ⟨z, t • (Avert v).1, t • (Avert v).2⟩ : TangentBundle J Z)) 0
                ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)) :=
            (congrArg (LinearMap.range (mfderiv IT JT fT z).toLinearMap).mkQ hder).symm
          _ = (K.equiv z).symm (e z.proj (Avert v).1, e z.proj (Avert v).2) := hn.symm
          _ = (K.equiv z).symm (K.equiv z (c.symm v)) := congrArg (K.equiv z).symm heA
          _ = c.symm v := (K.equiv z).symm_apply_apply (c.symm v) }
  refine ⟨K, T, ?_⟩
  intro z u w
  change (D ⟨z, (K.equiv z).symm (e z.proj u, e z.proj w)⟩ : TangentBundle J Z) =
    (F ⟨z, u, w⟩ : TangentBundle J Z)
  have hk := (K.equiv z).apply_symm_apply (e z.proj u, e z.proj w)
  have hu : (e z.proj).symm
      (K.equiv z ((K.equiv z).symm (e z.proj u, e z.proj w))).1 = u :=
    (congrArg (fun v : ν z.proj × ν z.proj ↦ (e z.proj).symm v.1) hk).trans
      ((e z.proj).symm_apply_apply u)
  have hw : (e z.proj).symm
      (K.equiv z ((K.equiv z).symm (e z.proj u, e z.proj w))).2 = w :=
    (congrArg (fun v : ν z.proj × ν z.proj ↦ (e z.proj).symm v.2) hk).trans
      ((e z.proj).symm_apply_apply w)
  have hp : ((e z.proj).symm
        (K.equiv z ((K.equiv z).symm (e z.proj u, e z.proj w))).1,
      (e z.proj).symm
        (K.equiv z ((K.equiv z).symm (e z.proj u, e z.proj w))).2) = (u, w) :=
    Prod.ext hu hw
  have hfinal := congrArg (fun v : V z.proj × V z.proj ↦
    (F ⟨z, v.1, v.2⟩ : TangentBundle J Z)) hp
  exact (hD z ((K.equiv z).symm (e z.proj u, e z.proj w))).trans hfinal

end AtiyahSinger

