/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereCotangentSplitting
public import AtiyahSinger.Geometry.AssociatedSphereTrivialAction
public import AtiyahSinger.Geometry.CotangentProduct

/-!
# The original zero-sphere cotangent product

Public module ID: M1517.

The quotient product maps on the associated sphere and on its split cotangent
space determine the same inverse-differential cotangent homeomorphism. The
zero-dimensional vertical tangent makes the supplied horizontal lift the
inverse of the actual projection derivative. No new lift or cotangent model
is chosen, and both original poles remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology

variable {n : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin 0) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin 0) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas 0 (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin 0) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin 0)
local notation "Iprod" => 𝓘(ℝ, E × V)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere 0)
local notation "X" => CotangentTotalSpace (n := n) (M := B)
local notation "Y" => CotangentTotalSpace (n := 0) (M := OrthogonalSphere 0)
local notation "Q" => PrincipalBundlePullback (cotangentProjection (n := n) (M := B)) projection

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Retain the original lift and both actual quotient representative maps in the derivative square.
/-- The zero-sphere quotient product agrees with the actual inverse differential on covectors. -/
theorem associatedSphereCotangentProduct_inverseDifferential_of_zero :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI : ChartedSpace (E × V) (B × OrthogonalSphere 0) :=
      prodChartedSpace E B V (OrthogonalSphere 0)
    letI : IsManifold Iprod ∞ (B × OrthogonalSphere 0) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓡 n) (I' := 𝓡 0) B (OrthogonalSphere 0)
    ∀ (H : SmoothHorizontalLift (smoothAssociatedSphereProjection S))
      (d : Z ≃ₘ⟮Iprod, Iprod⟯ (B × OrthogonalSphere 0))
      (_hd : ∀ (p : P) (y : OrthogonalSphere 0),
        d (associatedBundleMk G P (OrthogonalSphere 0) p y) = (projection p, y))
      (e : AssociatedBundle G Q Y ≃ₜ X × Y)
      (_he : ∀ (p : Q) (y : Y), e (associatedBundleMk G Q Y p y) = (p.val.1, y)),
      let c := ((associatedSphereCotangentHomeomorph S H).symm.trans e).trans
        (cotangentProductModelHomeomorph (n := n) (m := 0) B (OrthogonalSphere 0)).symm
      ∀ z, c z = ⟨d z.proj, z.snd.comp (mfderiv Iprod Iprod d.symm (d z.proj))⟩ := by
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let : ChartedSpace (E × V) (B × OrthogonalSphere 0) :=
    prodChartedSpace E B V (OrthogonalSphere 0)
  let : IsManifold Iprod ∞ (B × OrthogonalSphere 0) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓡 0) B (OrthogonalSphere 0)
  intro H d hd e he
  dsimp only
  let D := smoothAssociatedSphereProjection S
  let hD := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle D hD
  let := verticalTangentVectorBundle D hD
  let := verticalTangentContMDiffVectorBundle D hD
  let split := H.cotangentSplitHomeomorph D hD
  let a := associatedSphereCotangentHomeomorph S H
  let prod := cotangentProductModelHomeomorph (n := n) (m := 0) B (OrthogonalSphere 0)
  -- Surjectivity of the projection derivative and equality of dimensions force its injectivity.
  have hinj (x : Z) : Function.Injective (mfderiv Iprod (𝓡 n) D x) := by
    have hdim : Module.finrank ℝ (TangentSpace Iprod x) =
        Module.finrank ℝ (TangentSpace (𝓡 n) (D x)) := by
      change Module.finrank ℝ (E × V) = Module.finrank ℝ E
      simp
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (H.right_inv x).surjective
  have hleft (x : Z) (v : TangentSpace Iprod x) :
      H.lift x (mfderiv Iprod (𝓡 n) D x v) = v :=
    hinj x (H.right_inv x (mfderiv Iprod (𝓡 n) D x v))
  have hbase (x : Z) : D x = (d x).1 := by
    induction x using Quotient.inductionOn with
    | h w => exact (congrArg Prod.fst (hd w.1 w.2)).symm
  have hcomp : (D : Z → B) ∘ d.symm = Prod.fst := by
    funext y
    exact (hbase (d.symm y)).trans (congrArg Prod.fst (d.apply_symm_apply y))
  have hderiv (x : Z) : (mfderiv Iprod (𝓡 n) D x).comp
      (mfderiv Iprod Iprod d.symm (d x)) = ContinuousLinearMap.fst ℝ E V := by
    have h := (mfderiv_comp (d x)
      (D.contMDiff.mdifferentiable (by simp) (d.symm (d x)))
      (d.symm.mdifferentiable (by simp) (d x))).symm
    have hfst (y : B × OrthogonalSphere 0) :
        mfderiv Iprod (𝓡 n) (Prod.fst : B × OrthogonalSphere 0 → B) y =
        ContinuousLinearMap.fst ℝ E V := by
      rw [modelWithCornersSelf_prod]
      exact mfderiv_fst
    have hchange : mfderiv Iprod (𝓡 n) ((D : Z → B) ∘ d.symm) (d x) =
        mfderiv Iprod (𝓡 n) (Prod.fst : B × OrthogonalSphere 0 → B) (d x) := by
      congr 1
    have heq := h.trans (hchange.trans (hfst (d x)))
    have hd : mfderiv Iprod (𝓡 n) D (d.symm (d x)) = mfderiv Iprod (𝓡 n) D x := by
      congr 1
      exact d.symm_apply_apply x
    exact hd ▸ heq
  -- Check the covector formula on every original principal representative.
  intro z
  obtain ⟨w, rfl⟩ := a.surjective z
  induction w using Quotient.inductionOn with
  | h w =>
    let p := w.1
    let η := w.2
    let z := a (associatedBundleMk G Q Y p η)
    let z₀ := associatedBundleMk G P (OrthogonalSphere 0) p.val.2 η.proj
    have hsplit : H.cotangentSplitMap D z =
        ⟨z₀, p.val.1.snd, (associatedSphereCotangentRepresentative S p.val.2 η).snd⟩ := by
      have ha := (exists_associatedSphereCotangentHomeomorph S H).choose_spec p η
      exact ((SmoothHorizontalLift.exists_cotangentSplitHomeomorph D hD H).choose_spec.1 z).symm
        |>.trans ((congrArg split ha).trans (split.apply_symm_apply _))
    have hz : z.proj = z₀ := congrArg TotalSpace.proj hsplit
    have hcov : z.snd.comp (H.lift z.proj) = p.val.1.snd :=
      congrArg (fun t ↦ (t.snd.1 : E →L[ℝ] ℝ)) hsplit
    have hpoint : d z.proj = (p.val.1.proj, η.proj) :=
      (congrArg d hz).trans ((hd p.val.2 η.proj).trans (Prod.ext p.property.symm rfl))
    have hmap : z.snd.comp (mfderiv Iprod Iprod d.symm (d z.proj)) =
        p.val.1.snd.coprod η.snd := by
      apply ContinuousLinearMap.ext
      intro v
      let v' := mfderiv Iprod Iprod d.symm (d z.proj) v
      have hη : η.snd v.2 = 0 := by
        rw [Subsingleton.elim v.2 0, map_zero]
      calc
        z.snd v' = (z.snd.comp (H.lift z.proj)) (mfderiv Iprod (𝓡 n) D z.proj v') :=
          (congrArg z.snd (hleft z.proj v')).symm
        _ = p.val.1.snd (mfderiv Iprod (𝓡 n) D z.proj v') :=
          DFunLike.congr_fun hcov _
        _ = p.val.1.snd v.1 := congrArg p.val.1.snd (DFunLike.congr_fun (hderiv z.proj) v)
        _ = p.val.1.snd v.1 + η.snd v.2 := by rw [hη, add_zero]
    have hvalue : prod.symm (e (a.symm z)) =
        (⟨(p.val.1.proj, η.proj), p.val.1.snd.coprod η.snd⟩ :
          TotalSpace ((E × V) →L[ℝ] ℝ)
            (fun x : B × OrthogonalSphere 0 ↦ TangentSpace Iprod x →L[ℝ] ℝ)) := by
      change prod.symm (e (a.symm (a (associatedBundleMk G Q Y p η)))) = _
      rw [a.symm_apply_apply, he]
      rfl
    have hpair : ((p.val.1.proj, η.proj), p.val.1.snd.coprod η.snd) =
        (d z.proj, z.snd.comp (mfderiv Iprod Iprod d.symm (d z.proj))) :=
      Prod.ext hpoint.symm hmap.symm
    exact hvalue.trans (congrArg (fun t : (B × OrthogonalSphere 0) × ((E × V) →L[ℝ] ℝ) ↦
      (⟨t.1, t.2⟩ : TotalSpace ((E × V) →L[ℝ] ℝ)
        (fun x : B × OrthogonalSphere 0 ↦ TangentSpace Iprod x →L[ℝ] ℝ))) hpair)

end AtiyahSinger
