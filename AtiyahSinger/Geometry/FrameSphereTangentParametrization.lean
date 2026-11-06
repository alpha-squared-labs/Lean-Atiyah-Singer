/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FrameSphereTangentCoordinates

/-!
# The actual tangent parametrization of the whole frame-sphere chart

Public module ID: M1252.

The original base tangent vector and two original vector fibers parametrize
all tangent vectors over the original south stereographic open subset.
The formula is the specified horizontal lift plus the actual affine vertical
derivative. Source reordering and every inverse use the same native charts.

This supplies an actual open diffeomorphism. Adaptation at the south section
and the prescribed ordered tangent-normal derivative enter the tubular comparison;
no arbitrary real normal isomorphism is substituted for them here.
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
  verticalTangentTopology

local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 50 in
set_option maxHeartbeats 2400000 in
-- The source reorders the original three fibers; the target keeps each ambient tangent vector.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole south chart gives actual tangent coordinates over the doubled original bundle. -/
theorem exists_frameSphere_tangentParametrization
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
    let prT : ContMDiffMap I.tangent I (TangentBundle I B) B ∞ :=
      ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj (TangentSpace I)⟩
    let Vt := (prT : TangentBundle I B → B) *ᵖ V
    let U : TopologicalSpace.Opens (TangentBundle J Z) :=
      ⟨Bundle.TotalSpace.proj ⁻¹' a.source,
        a.open_source.preimage (FiberBundle.continuous_proj (EB × R) (TangentSpace J))⟩
    ∃ F : TotalSpace (R × R) (Vt ×ᵇ Vt) ≃ₘ⟮I.tangent.prod 𝓘(ℝ, R × R), J.tangent⟯ U,
      ∀ (z : TangentBundle I B) (u w : V z.proj),
        let horizontal : EB × R := H'.lift (a.symm ⟨z.proj, u⟩) z.snd
        let vertical : EB × R :=
          mfderiv 𝓘(ℝ, ℝ) J (fun t : ℝ ↦ a.symm ⟨z.proj, u + t • w⟩) 0
            ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
        (F ⟨z, u, w⟩ : TangentBundle J Z) =
          ⟨a.symm ⟨z.proj, u⟩, horizontal + vertical⟩ := by
  classical
  let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
  let S := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, EB)
  let J := 𝓘(ℝ, EB × R)
  let A := I.prod 𝓘(ℝ, R)
  let a := frameSphereStereographic (EB := EB) r V
  have ha := frameSphereStereographic_spec (EB := EB) r V
  let prT : ContMDiffMap I.tangent I (TangentBundle I B) B ∞ :=
    ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj (TangentSpace I)⟩
  let Vt := (prT : TangentBundle I B → B) *ᵖ V
  let Q := Vt ×ᵇ Vt
  let C := I.tangent.prod 𝓘(ℝ, R × R)
  let pr : ContMDiffMap A I (TotalSpace R V) B ∞ :=
    ⟨Bundle.TotalSpace.proj, Bundle.contMDiff_proj V⟩
  let aInv : ContMDiffMap A J (TotalSpace R V) Z ∞ := ⟨a.symm, ha.2.2.2.2.2⟩
  let Wb := (pr : TotalSpace R V → B) *ᵖ (TangentSpace I)
  let Wr := (pr : TotalSpace R V → B) *ᵖ V
  let W := Wb ×ᵇ Wr
  let T := (aInv : TotalSpace R V → Z) *ᵖ (TangentSpace J)
  -- Reorder (x, tangent; u, w) into (x, u; tangent, w), using the original three fibers.
  let swap : TotalSpace (R × R) Q → TotalSpace (EB × R) W :=
    fun z ↦ ⟨⟨z.proj.proj, z.snd.1⟩, z.proj.snd, z.snd.2⟩
  let unswap : TotalSpace (EB × R) W → TotalSpace (R × R) Q :=
    fun z ↦ ⟨⟨z.proj.proj, z.snd.1⟩, z.proj.snd, z.snd.2⟩
  have hswap : ContMDiff C (A.prod 𝓘(ℝ, EB × R)) ∞ swap := by
    intro z
    have ht : ContMDiffAt C I.tangent ∞
        (fun w : TotalSpace (R × R) Q ↦ w.proj) z := Bundle.contMDiffAt_proj Q
    have hb := prT.contMDiff.contMDiffAt.comp z ht
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt C C ∞ id z)).2
    have hu := (ContinuousLinearMap.fst ℝ R R).contDiff.contMDiff.contMDiffAt.comp z hcoords
    have hw := (ContinuousLinearMap.snd ℝ R R).contDiff.contMDiff.contMDiffAt.comp z hcoords
    have hbase : ContMDiffAt C A ∞
        (fun w : TotalSpace (R × R) Q ↦ (⟨w.proj.proj, w.snd.1⟩ : TotalSpace R V)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, hu⟩
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hbase, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp ht).2.prodMk_space hw
  have hunswap : ContMDiff (A.prod 𝓘(ℝ, EB × R)) C ∞ unswap := by
    intro z
    have ht : ContMDiffAt (A.prod 𝓘(ℝ, EB × R)) A ∞
        (fun w : TotalSpace (EB × R) W ↦ w.proj) z := Bundle.contMDiffAt_proj W
    have hb := pr.contMDiff.contMDiffAt.comp z ht
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (A.prod 𝓘(ℝ, EB × R))
        (A.prod 𝓘(ℝ, EB × R)) ∞ id z)).2
    have hξ := (ContinuousLinearMap.fst ℝ EB R).contDiff.contMDiff.contMDiffAt.comp z hcoords
    have hw := (ContinuousLinearMap.snd ℝ EB R).contDiff.contMDiff.contMDiffAt.comp z hcoords
    have hbase : ContMDiffAt (A.prod 𝓘(ℝ, EB × R)) I.tangent ∞
        (fun w : TotalSpace (EB × R) W ↦ (⟨w.proj.proj, w.snd.1⟩ : TangentBundle I B)) z := by
      apply Bundle.contMDiffAt_totalSpace.mpr
      exact ⟨hb, hξ⟩
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hbase, ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp ht).2.prodMk_space hw
  let reorder : TotalSpace (R × R) Q ≃ₘ⟮C, A.prod 𝓘(ℝ, EB × R)⟯
      TotalSpace (EB × R) W :=
    { toFun := swap
      invFun := unswap
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := hswap
      contMDiff_invFun := hunswap }
  -- Assemble the original horizontal lift and the actual vertical derivative.
  obtain ⟨e, he, hef, hei⟩ := exists_frameSphere_tangentCoordinateEquiv (EB := EB) r V H
  let E : TotalSpace (EB × R) W ≃ₘ⟮A.prod 𝓘(ℝ, EB × R), A.prod 𝓘(ℝ, EB × R)⟯
      TotalSpace (EB × R) T :=
    { toFun := fun z ↦ ⟨z.proj, e z.proj z.snd⟩
      invFun := fun z ↦ ⟨z.proj, (e z.proj).symm z.snd⟩
      left_inv := by
        intro z
        change (⟨z.proj, (e z.proj).symm (e z.proj z.snd)⟩ : TotalSpace (EB × R) W) = z
        rw [(e z.proj).symm_apply_apply]
      right_inv := by
        intro z
        change (⟨z.proj, e z.proj ((e z.proj).symm z.snd)⟩ : TotalSpace (EB × R) T) = z
        rw [(e z.proj).apply_symm_apply]
      contMDiff_toFun := hef
      contMDiff_invFun := hei }
  let U : TopologicalSpace.Opens (TangentBundle J Z) :=
    ⟨Bundle.TotalSpace.proj ⁻¹' a.source,
      a.open_source.preimage (FiberBundle.continuous_proj (EB × R) (TangentSpace J))⟩
  have hm (v : TotalSpace R V) : v ∈ a.target := ha.2.1.symm ▸ Set.mem_univ v
  let forward : TotalSpace (EB × R) T → U :=
    fun z ↦ ⟨⟨a.symm z.proj, z.snd⟩, a.map_target (hm z.proj)⟩
  let inverse : U → TotalSpace (EB × R) T :=
    fun z ↦ ⟨a z.val.proj, z.val.snd⟩
  -- Replacing only the base by its original open coordinates leaves tangent vectors unchanged.
  have hf : ContMDiff (A.prod 𝓘(ℝ, EB × R)) J.tangent ∞ forward := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    intro z
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨aInv.contMDiff.contMDiffAt.comp z (Bundle.contMDiffAt_proj T), ?_⟩
    exact (Bundle.contMDiffAt_totalSpace.mp
      (contMDiffAt_id : ContMDiffAt (A.prod 𝓘(ℝ, EB × R))
        (A.prod 𝓘(ℝ, EB × R)) ∞ id z)).2
  have hi : ContMDiff J.tangent (A.prod 𝓘(ℝ, EB × R)) ∞ inverse := by
    intro z
    have ht : ContMDiffAt J.tangent J.tangent ∞
        (fun w : U ↦ w.val) z := contMDiff_subtype_val z
    have hb : ContMDiffAt J.tangent J ∞
        (fun w : U ↦ w.val.proj) z := (Bundle.contMDiffAt_proj (TangentSpace J)).comp z ht
    have haAt := (ha.2.2.2.2.1 z.val.proj z.property).contMDiffAt
      (a.open_source.mem_nhds z.property)
    have hbase : ContMDiffAt J.tangent A ∞ (fun w : U ↦ a w.val.proj) z :=
      haAt.comp z hb
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨hbase, ?_⟩
    have hcoords := (Bundle.contMDiffAt_totalSpace.mp ht).2
    change ContMDiffAt J.tangent 𝓘(ℝ, EB × R) ∞
      (fun w : U ↦
        ((trivializationAt (EB × R) (TangentSpace J) (a.symm (a z.val.proj)))
          ⟨a.symm (a w.val.proj), w.val.snd⟩).2) z
    rw [a.left_inv z.property]
    apply hcoords.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro w
    exact congrArg (fun y : TangentBundle J Z ↦
      ((trivializationAt (EB × R) (TangentSpace J) z.val.proj) y).2)
        (Bundle.TotalSpace.ext (a.left_inv w.property) (by rfl))
  let openBase : TotalSpace (EB × R) T ≃ₘ⟮A.prod 𝓘(ℝ, EB × R), J.tangent⟯ U :=
    { toFun := forward
      invFun := inverse
      left_inv := fun z ↦ Bundle.TotalSpace.ext (a.right_inv (hm z.proj)) (by rfl)
      right_inv := fun z ↦ Subtype.ext (Bundle.TotalSpace.ext (a.left_inv z.property) (by rfl))
      contMDiff_toFun := hf
      contMDiff_invFun := hi }
  refine ⟨reorder.trans (E.trans openBase), ?_⟩
  intro z u w
  change (⟨a.symm ⟨z.proj, u⟩, e ⟨z.proj, u⟩ (z.snd, w)⟩ : TangentBundle J Z) = _
  exact Bundle.TotalSpace.ext rfl (heq_of_eq (he ⟨z.proj, u⟩ z.snd w))

end AtiyahSinger

