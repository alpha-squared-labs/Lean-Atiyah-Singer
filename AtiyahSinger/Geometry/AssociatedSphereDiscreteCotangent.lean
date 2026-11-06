/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereCotangentSplitting
public import AtiyahSinger.Geometry.AssociatedSphereDiscreteProduct
public import AtiyahSinger.Geometry.CotangentProduct

/-!
# The actual cotangent product over a zero-dimensional base

Public module ID: M1074.

The original sphere gauge and its cotangent action determine the same
inverse-differential transport on the original total cotangent bundle.
Every tangent vector is vertical because the base tangent space is zero.
The fiber-inclusion derivative therefore determines the entire comparison,
including the inverse sphere differential in the native cotangent action.
The supplied horizontal lift and both quotient maps are retained throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology

variable {r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) B] [IsManifold (𝓡 0) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 0) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "E" => EuclideanSpace ℝ (Fin 0)
local notation "V" => EuclideanSpace ℝ (Fin r)
local notation "Iprod" => 𝓘(ℝ, E × V)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => CotangentTotalSpace (n := 0) (M := B)
local notation "Y" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "Q" => PrincipalBundlePullback (cotangentProjection (n := 0) (M := B)) projection

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- The actual vertical kernel and its dependent covector evaluation are kept in one comparison.
/-- Over a zero-dimensional base the original gauge product is the inverse differential lift. -/
theorem associatedSphereCotangentProduct_inverseDifferential_of_base_dim_zero :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI : ChartedSpace (E × V) (B × OrthogonalSphere r) :=
      prodChartedSpace E B V (OrthogonalSphere r)
    letI : IsManifold Iprod ∞ (B × OrthogonalSphere r) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓡 0) (I' := 𝓡 r) B (OrthogonalSphere r)
    ∀ (H : SmoothHorizontalLift (smoothAssociatedSphereProjection S)) (θ : C(P, G))
      (d : Z ≃ₘ⟮Iprod, Iprod⟯ (B × OrthogonalSphere r))
      (_hd : ∀ (p : P) (y : OrthogonalSphere r),
        d (associatedBundleMk G P (OrthogonalSphere r) p y) = (projection p, θ p • y))
      (e : AssociatedBundle G Q Y ≃ₜ X × Y)
      (_he : ∀ (p : Q) (y : Y),
        e (associatedBundleMk G Q Y p y) = (p.val.1, θ p.val.2 • y)),
      let c := ((associatedSphereCotangentHomeomorph S H).symm.trans e).trans
        (cotangentProductModelHomeomorph (n := 0) (m := r) B (OrthogonalSphere r)).symm
      ∀ z, c z = ⟨d z.proj, z.snd.comp (mfderiv Iprod Iprod d.symm (d z.proj))⟩ := by
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let : ChartedSpace (E × V) (B × OrthogonalSphere r) :=
    prodChartedSpace E B V (OrthogonalSphere r)
  let : IsManifold Iprod ∞ (B × OrthogonalSphere r) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 0) (I' := 𝓡 r) B (OrthogonalSphere r)
  intro H θ d hd e he
  dsimp only
  let D := smoothAssociatedSphereProjection S
  let hD := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle D hD
  let := verticalTangentVectorBundle D hD
  let := verticalTangentContMDiffVectorBundle D hD
  let split := H.cotangentSplitHomeomorph D hD
  let a := associatedSphereCotangentHomeomorph S H
  let prod := cotangentProductModelHomeomorph (n := 0) (m := r) B (OrthogonalSphere r)
  -- Zero base tangent makes every original tangent vector a member of the actual vertical kernel.
  let vertical (x : Z) (v : E × V) : VerticalTangentFiber Iprod (𝓡 0) (D : Z → B) x :=
    ⟨v, by
      change (mfderiv Iprod (𝓡 0) D x v : E) = 0
      exact @Subsingleton.elim E inferInstance _ _⟩
  intro z
  obtain ⟨w, rfl⟩ := a.surjective z
  induction w using Quotient.inductionOn with
  | h w =>
    let p := w.1
    let η := w.2
    let z := a (associatedBundleMk G Q Y p η)
    let z₀ := associatedBundleMk G P (OrthogonalSphere r) p.val.2 η.proj
    let i := associatedBundleMk G P (OrthogonalSphere r) p.val.2
    let g := orthogonalSphereDiffeomorph r (θ p.val.2)
    let di := mfderiv (𝓡 r) Iprod i η.proj
    let dg := (g.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (show η.proj ∈ g.toHomeomorph.toOpenPartialHomeomorph.source from Set.mem_univ _)
    let dd := (d.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (show z₀ ∈ d.toHomeomorph.toOpenPartialHomeomorph.source from Set.mem_univ _)
    let fi := associatedSphereFiberTangentEquiv S p.val.2 η.proj
    have hfi (v : V) : (fi v).val = di v :=
      (exists_associatedSphereFiberTangentEquiv S p.val.2 η.proj).choose_spec v
    have hsplit : H.cotangentSplitMap D z =
        ⟨z₀, p.val.1.snd, (associatedSphereCotangentRepresentative S p.val.2 η).snd⟩ := by
      have ha := (exists_associatedSphereCotangentHomeomorph S H).choose_spec p η
      exact ((SmoothHorizontalLift.exists_cotangentSplitHomeomorph D hD H).choose_spec.1 z).symm
        |>.trans ((congrArg split ha).trans (split.apply_symm_apply _))
    have hz : z.proj = z₀ := congrArg TotalSpace.proj hsplit
    -- The splitting records the original covector on every actual fiber-inclusion derivative.
    have hcov (v : V) : z.snd (di v) = η.snd v := by
      have h := congrArg (fun t ↦ t.snd.2 (vertical t.proj (di v))) hsplit
      change z.snd (di v) = η.snd (fi.symm (vertical z₀ (di v))) at h
      have hv : vertical z₀ (di v) = fi v := by
        apply Subtype.ext
        exact (hfi v).symm
      rw [hv, fi.symm_apply_apply] at h
      exact h
    -- Differentiate the same representative formula; its first component is constant.
    have hcoord (v : V) : dd (di v) = (0, dg v) := by
      have hcomp : (d : Z → B × OrthogonalSphere r) ∘ i =
          fun y ↦ (projection p.val.2, g y) := funext (hd p.val.2)
      have h := mfderiv_comp η.proj (d.mdifferentiable (by simp) (i η.proj))
        ((smoothAssociatedSphereFiberInclusion S p.val.2).contMDiff.mdifferentiable
          (by simp) η.proj)
      rw [hcomp] at h
      have hp : mfderiv (𝓡 r) Iprod (fun y ↦ (projection p.val.2, g y)) η.proj =
          (0 : V →L[ℝ] E).prod (mfderiv (𝓡 r) (𝓡 r) g η.proj) := by
        rw [modelWithCornersSelf_prod]
        rw [mfderiv_prodMk mdifferentiableAt_const (g.mdifferentiable (by simp) η.proj),
          mfderiv_const]
      rw [hp] at h
      exact (congrArg (fun L ↦ L v) h).symm
    have hinverse (v : E × V) :
        mfderiv Iprod Iprod d.symm (d z.proj) v = di (dg.symm v.2) := by
      rw [hz]
      change dd.symm v = di (dg.symm v.2)
      apply dd.injective
      rw [dd.apply_symm_apply, hcoord, dg.apply_symm_apply]
      exact Prod.ext (Subsingleton.elim _ _) rfl
    have hpoint : d z.proj = (p.val.1.proj, (θ p.val.2 • η).proj) :=
      (congrArg d hz).trans ((hd p.val.2 η.proj).trans (Prod.ext p.property.symm rfl))
    have hmap : z.snd.comp (mfderiv Iprod Iprod d.symm (d z.proj)) =
        p.val.1.snd.coprod (θ p.val.2 • η).snd := by
      apply ContinuousLinearMap.ext
      intro v
      have hzero : p.val.1.snd v.1 = 0 := by
        rw [Subsingleton.elim v.1 0, map_zero]
      change z.snd (mfderiv Iprod Iprod d.symm (d z.proj) v) =
        p.val.1.snd v.1 + η.snd (dg.symm v.2)
      rw [hinverse, hcov, hzero, zero_add]
    have hvalue : prod.symm (e (a.symm z)) =
        (⟨(p.val.1.proj, (θ p.val.2 • η).proj),
          p.val.1.snd.coprod (θ p.val.2 • η).snd⟩ :
          TotalSpace ((E × V) →L[ℝ] ℝ)
            (fun x : B × OrthogonalSphere r ↦ TangentSpace Iprod x →L[ℝ] ℝ)) := by
      change prod.symm (e (a.symm (a (associatedBundleMk G Q Y p η)))) = _
      rw [a.symm_apply_apply, he]
      rfl
    have hpair :
        ((p.val.1.proj, (θ p.val.2 • η).proj), p.val.1.snd.coprod (θ p.val.2 • η).snd) =
          (d z.proj, z.snd.comp (mfderiv Iprod Iprod d.symm (d z.proj))) :=
      Prod.ext hpoint.symm hmap.symm
    exact hvalue.trans (congrArg (fun t : (B × OrthogonalSphere r) × ((E × V) →L[ℝ] ℝ) ↦
      (⟨t.1, t.2⟩ : TotalSpace ((E × V) →L[ℝ] ℝ)
        (fun x : B × OrthogonalSphere r ↦ TangentSpace Iprod x →L[ℝ] ℝ))) hpair)

end AtiyahSinger
