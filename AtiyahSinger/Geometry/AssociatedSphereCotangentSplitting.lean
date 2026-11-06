/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereVerticalCotangent
public import AtiyahSinger.Geometry.SubmersionCotangentSplitting
public import AtiyahSinger.Topology.PrincipalBundlePullback

/-!
# The cotangent realization of the pulled associated sphere bundle

Public module ID: M1072.

Pull the original orthogonal principal bundle back to the actual cotangent
bundle of its base. Its associated sphere-cotangent quotient identifies with
the actual cotangent total space upstairs after choosing a smooth horizontal
lift. The representative formula retains the original base covector, the
canonical vertical covector and the exact inverse cotangent splitting.

This is the geometric identification preceding SG III.13 (13.16). It requires
no compactness once the horizontal lift is supplied. The compact-support
K-theory operation and the analytic multiplicativity formula remain separate.
The total manifold uses the already chosen full product model, not a second
atlas identified with a Euclidean model by an unstated coordinate choice.
The proof uses the original quotient and native product and pullback topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => CotangentTotalSpace (n := n) (M := B)
local notation "Y" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "Q" => PrincipalBundlePullback (cotangentProjection (n := n) (M := B)) projection
local notation "C" => fun z : Z ↦ TangentSpace 𝓘(ℝ, E × R) z →L[ℝ] ℝ

set_option maxHeartbeats 1000000 in
-- Compare the original quotient with the native product and pullback total spaces.
set_option backward.isDefEq.respectTransparency false in
/-- The original pulled associated cotangent quotient realizes the actual total cotangent bundle. -/
theorem exists_associatedSphereCotangentHomeomorph
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := verticalTangentFiberBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    letI := verticalTangentVectorBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    letI := verticalTangentContMDiffVectorBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    ∃ e : AssociatedBundle G Q Y ≃ₜ TotalSpace ((E × R) →L[ℝ] ℝ) C,
      ∀ (p : Q) (z : Y), e (associatedBundleMk G Q Y p z) =
        (H.cotangentSplitHomeomorph (smoothAssociatedSphereProjection S)
          (associatedSphereProjection_isSubmersion S)).symm
            ⟨associatedBundleMk G P (OrthogonalSphere r) p.val.2 z.proj,
              p.val.1.snd, (associatedSphereCotangentRepresentative S p.val.2 z).snd⟩ := by
  /- Stage 1: the existing associated pullback homeomorphism identifies the
  original quotient with pairs (xi,a) satisfying base(xi)=base(a). The original
  principal pullback stores this equality; its native right action leaves xi
  fixed. No properness of the cotangent projection is used or asserted.
  Stage 2: apply the canonical associated vertical cotangent homeomorphism
  to a. Its exact representative formula preserves the point [p,s] in Z.
  Hence the same fiber product is the native direct sum over Z of the pulled
  base cotangent bundle and the selected vertical cotangent bundle. In local
  principal and native bundle charts this comparison and its inverse are
  continuous; the stored base equality transports the first covector to the
  exact fiber required by the same associated projection.
  Stage 3: compose with the inverse of the generic cotangent splitting for
  the supplied H. Its formula uses the same original projection differential,
  same vertical kernel atlas and same order of the two covector factors.
  The resulting homeomorphism has precisely the displayed formula on every
  representative, so it cannot be replaced by an unrelated homeomorphism.
  The canonical vertical comparison uses no horizontal choice; this final
  comparison depends on H. No extra separation, paracompactness, compactness
  or metric assumption is needed when H is given. -/
  classical
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let V := VerticalTangentModel (E × R) E
  let W := VerticalCotangentFiber («E» := E × R) (F := E) (q : Z → B)
  let A := ((q : Z → B) *ᵖ (fun b : B ↦ TangentSpace (𝓡 n) b →L[ℝ] ℝ))
  let T := TotalSpace ((E →L[ℝ] ℝ) × (V →L[ℝ] ℝ)) (A ×ᵇ W)
  let Fp := AssociatedBundlePullback («G» := G) (F := Y) (projection := projection)
    (cotangentProjection (n := n) (M := B))
  let eV := associatedSphereVerticalCotangentHomeomorph S
  have heV (p : P) (η : Y) : eV (associatedBundleMk G P Y p η) =
      associatedSphereCotangentRepresentative S p η :=
    (exists_associatedSphereVerticalCotangentHomeomorph S).choose_spec p η
  -- Stage 1: the canonical vertical comparison preserves the original quotient projection.
  have hbase (u : AssociatedBundle G P Y) :
      q (eV u).proj = associatedBundleProjection (F := Y) S.toIsPrincipalBundle u := by
    induction u using Quotient.inductionOn with
    | h z =>
      change q (eV (associatedBundleMk G P Y z.1 z.2)).proj = projection z.1
      rw [heV]
      rfl
  let forward (u : Fp) : T := ⟨(eV u.val.2).proj, u.val.1.snd, (eV u.val.2).snd⟩
  have hbaseFp (u : Fp) : q (eV u.val.2).proj = u.val.1.proj :=
    (hbase u.val.2).trans u.property.symm
  have hcovector (u : Fp) :
      (⟨q (eV u.val.2).proj, u.val.1.snd⟩ : X) = u.val.1 := by
    exact congrArg (fun b : B ↦ (⟨b, u.val.1.snd⟩ : X)) (hbaseFp u)
  let inverse (u : T) : Fp :=
    ⟨(⟨q u.proj, u.snd.1⟩, eV.symm ⟨u.proj, u.snd.2⟩), by
      change q u.proj = associatedBundleProjection (F := Y) S.toIsPrincipalBundle _
      rw [← hbase, eV.apply_symm_apply]⟩
  have hleft (u : Fp) : inverse (forward u) = u := by
    apply Subtype.ext
    apply Prod.ext
    · exact hcovector u
    · exact eV.symm_apply_apply u.val.2
  have hright (u : T) : forward (inverse u) = u := by
    dsimp [forward, inverse]
    rw [eV.apply_symm_apply]
  -- Stage 2: use the native induced product and pullback topologies in both directions.
  have hc : Continuous forward := by
    rw [(FiberBundle.Prod.isInducing_diag (E →L[ℝ] ℝ) A (V →L[ℝ] ℝ) W).continuous_iff]
    apply Continuous.prodMk
    · rw [(inducing_pullbackTotalSpaceEmbedding (E →L[ℝ] ℝ)
        (fun b : B ↦ TangentSpace (𝓡 n) b →L[ℝ] ℝ) (q : Z → B)).continuous_iff]
      have hz : Continuous (fun u : Fp ↦ (eV u.val.2).proj) :=
        (FiberBundle.continuous_proj (V →L[ℝ] ℝ) W).comp
        (eV.continuous.comp continuous_subtype_val.snd)
      apply (hz.prodMk continuous_subtype_val.fst).congr
      intro u
      exact Prod.ext rfl (hcovector u).symm
    · exact eV.continuous.comp continuous_subtype_val.snd
  have hi : Continuous inverse := by
    have hd := (FiberBundle.Prod.isInducing_diag
      (E →L[ℝ] ℝ) A (V →L[ℝ] ℝ) W).continuous
    exact (((Pullback.continuous_lift (E →L[ℝ] ℝ)
      (fun b : B ↦ TangentSpace (𝓡 n) b →L[ℝ] ℝ) (q : Z → B)).comp hd.fst).prodMk
      (eV.symm.continuous.comp hd.snd)).subtype_mk _
  let comparison : Fp ≃ₜ T :=
    { toFun := forward
      invFun := inverse
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hc
      continuous_invFun := hi }
  -- Stage 3: compose with precisely the supplied lift's inverse cotangent splitting.
  let eP := associatedBundlePullbackHomeomorph («G» := G) (F := Y) (projection := projection)
    (cotangentProjection (n := n) (M := B))
  refine ⟨(eP.trans comparison).trans (H.cotangentSplitHomeomorph q hq).symm, ?_⟩
  intro p η
  apply congrArg (H.cotangentSplitHomeomorph q hq).symm
  change (⟨(eV (associatedBundleMk G P Y p.val.2 η)).proj, p.val.1.snd,
    (eV (associatedBundleMk G P Y p.val.2 η)).snd⟩ : T) = _
  rw [heV]
  rfl

/-- Select the cotangent realization with its exact original representative formula. -/
def associatedSphereCotangentHomeomorph
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    AssociatedBundle G Q Y ≃ₜ TotalSpace ((E × R) →L[ℝ] ℝ) C :=
  (exists_associatedSphereCotangentHomeomorph S H).choose

end AtiyahSinger
