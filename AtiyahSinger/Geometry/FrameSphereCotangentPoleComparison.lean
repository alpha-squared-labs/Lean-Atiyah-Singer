/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereCotangentSplitting
public import AtiyahSinger.Geometry.FrameSphereTangentParametrization
public import AtiyahSinger.Geometry.FrameSphereVerticalDerivative
public import AtiyahSinger.Geometry.FrameSphereVerticalMetric
public import AtiyahSinger.Geometry.SphereCotangentPoleCoordinates
public import AtiyahSinger.Geometry.TangentMusicalDiffeomorph

/-!
# The actual frame-sphere cotangent pole and normalized tangent coordinates

Public module ID: M1243.

For the supplied compatible metric and horizontal lift, the actual associated
inverse-dual cotangent pole equals the musical image of the original tangent
parametrization. The real coordinate is multiplied by two, while the vertical
coordinate is one half times the actual positive inverse-Riesz comparison.
Both corrections use the same original frame and depend on its actual point.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Manifold Topology
open scoped ContDiff

variable {n : ℕ} (r : ℕ)
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold (𝓡 n) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V (𝓡 n)]
  [IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] orthogonalFrameTopology continuousSMul_orthogonalSphere
  verticalTangentTopology

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)

set_option maxSynthPendingDepth 50 in
set_option maxHeartbeats 3500000 in
-- Retain the native vertical kernel, actual normalized chart and both original metrics.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The associated cotangent pole is the musical tangent chart with the exact reciprocal
scale and the same positive inverse-Riesz vertical correction. -/
theorem frameSphere_cotangentPole_eq_musical_tangentParametrization
    (H : letI := continuousSMul_orthogonalFrame r V (𝓡 n)
      let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ E (TangentSpace (𝓡 n) : B → Type _))
    (h : letI := continuousSMul_orthogonalFrame r V (𝓡 n)
      let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      ContMDiffRiemannianMetric 𝓘(ℝ, E × R) ∞ (E × R)
        (TangentSpace 𝓘(ℝ, E × R) : Z → Type _)) :
    letI := continuousSMul_orthogonalFrame r V (𝓡 n)
    let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let J := 𝓘(ℝ, E × R)
    let q := smoothAssociatedSphereProjection S
    let H' : SmoothHorizontalLift q := H
    let h' : ContMDiffRiemannianMetric J ∞ (E × R) (TangentSpace J : Z → Type _) := h
    let C := (exists_frameSphere_verticalRieszComparison r V h').choose
    let F := (exists_frameSphere_tangentParametrization r V H').choose
    let d := (exists_tangentMusical_diffeomorph h').choose
    let eCot := associatedSphereCotangentHomeomorph S H'
    let Q := PrincipalBundlePullback (cotangentProjection (n := n) (M := B))
      (orthogonalFrameProjection r V)
    (∀ (x : Z) (v : TangentSpace (𝓡 n) (q x)),
      h'.inner x (H'.lift x v) = (g.inner (q x) v).comp (mfderiv J (𝓡 n) q x)) →
    ∀ (p : P) (ξ : TangentSpace (𝓡 n) p.1) (z : EuclideanSpace ℂ (Fin r)),
      let u : V p.1 := p.2 (WithLp.toLp 2 (fun i ↦ (z i).re))
      let w : V p.1 := p.2 (WithLp.toLp 2 (fun i ↦ (z i).im))
      let x : TotalSpace R V := ⟨p.1, (2 : ℝ) • u⟩
      let pQ : Q := ⟨(⟨p.1, g.inner p.1 ξ⟩, p), rfl⟩
      eCot (associatedBundleMk G Q
          (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) pQ
          (orthogonalSphereCotangentChart r false z)) =
        d (F ⟨⟨p.1, ξ⟩, (2 : ℝ) • u, (1 / 2 : ℝ) • C x w⟩) := by
  classical
  let := continuousSMul_orthogonalFrame r V (𝓡 n)
  let S := smoothOrthogonalFrameAtlas r V (𝓡 n)
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓡 n
  let J := 𝓘(ℝ, E × R)
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let K := VerticalTangentFiber J I q
  let C := (exists_frameSphere_verticalRieszComparison r V h).choose
  let L := (exists_frameSphere_verticalDerivativeEquiv (EB := E) r V).choose
  let F := (exists_frameSphere_tangentParametrization r V H).choose
  let d := (exists_tangentMusical_diffeomorph h).choose
  let eCot := associatedSphereCotangentHomeomorph S H
  let eSplit := H.cotangentSplitHomeomorph q hq
  let Q := PrincipalBundlePullback (cotangentProjection (n := n) (M := B))
    (orthogonalFrameProjection r V)
  dsimp only
  intro hcompat p ξ z
  let u : R := WithLp.toLp 2 (fun i ↦ (z i).re)
  let w : R := WithLp.toLp 2 (fun i ↦ (z i).im)
  let x : TotalSpace R V := ⟨p.1, (2 : ℝ) • p.2 u⟩
  let a := frameSphereStereographic (EB := E) r V
  let b := orthogonalSphereNormalizedChart r false
  let y := b.symm u
  let i : OrthogonalSphere r → Z := associatedBundleMk G P (OrthogonalSphere r) p
  have hpoint : a.symm x = i y := frameSphereStereographic_symm_two_smul (EB := E) r V p u
  have hb := orthogonalSphereNormalizedChart_smooth r false
  have hbt : u ∈ b.target := by
    rw [(orthogonalSphereNormalizedChart_properties r false).2.1]
    trivial
  have hbd : b.MDifferentiable (𝓡 r) (𝓡 r) :=
    ⟨hb.1.mdifferentiableOn (by simp), (hb.2.mdifferentiable (by simp)).mdifferentiableOn⟩
  let db : R ≃L[ℝ] TangentSpace (𝓡 r) y := hbd.symm.mfderiv hbt
  let eV := associatedSphereFiberTangentEquiv S p y
  -- The affine derivative has precisely the half inverse-frame factor.
  have hL (v : V p.1) : (L x v).val =
      (eV (db ((1 / 2 : ℝ) • p.2.symm v))).val := by
    let v₀ : R := (1 / 2 : ℝ) • p.2.symm v
    let l (t : ℝ) : R := u + t • v₀
    let dl : ℝ →L[ℝ] R := (ContinuousLinearMap.id ℝ ℝ).smulRight v₀
    have hl₀ : l 0 = u := by simp [l]
    have hl : HasFDerivAt l dl 0 := dl.hasFDerivAt.const_add u
    have hfun : (fun t : ℝ ↦ a.symm ⟨p.1, (2 : ℝ) • p.2 u + t • v⟩) =
        i ∘ b.symm ∘ l := by
      funext t
      have hc := frameSphereStereographic_symm_two_smul (EB := E) r V p (l t)
      have hvec : (2 : ℝ) • p.2 (l t) = (2 : ℝ) • p.2 u + t • v := by
        change (2 : ℝ) • p.2 (u + t • ((1 / 2 : ℝ) • p.2.symm v)) = _
        rw [map_add, map_smul, map_smul, p.2.apply_symm_apply, smul_add,
          smul_smul, smul_smul]
        congr 1
        have hc : (2 : ℝ) * t * (1 / 2) = t := by ring
        rw [hc]
      rw [hvec] at hc
      exact hc
    have hi := (smoothAssociatedSphereFiberInclusion S p).contMDiff
    have hc := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 r) (I'' := J) 0
      ((hi.comp hb.2).mdifferentiable (by simp) (l 0)) hl.hasMFDerivAt.mdifferentiableAt
    rw [hl₀, hl.hasMFDerivAt.mfderiv] at hc
    have hc₂ := mfderiv_comp (I := 𝓡 r) (I' := 𝓡 r) (I'' := J) u
      (hi.mdifferentiable (by simp) _) (hb.2.mdifferentiable (by simp) _)
    rw [hc₂] at hc
    have hd := DFunLike.congr_fun hc
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1)
    have hf := congrArg (fun k : ℝ → Z ↦
      (mfderiv 𝓘(ℝ, ℝ) J k 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : E × R))
        hfun
    have hunit : dl ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (0 : ℝ)).symm 1) = v₀ := by
      change (1 : ℝ) • v₀ = v₀
      exact one_smul ℝ v₀
    have he := (exists_associatedSphereFiberTangentEquiv S p y).choose_spec (db v₀)
    calc
      (L x v).val = _ :=
        (exists_frameSphere_verticalDerivativeEquiv (EB := E) r V).choose_spec.1 x v
      _ = (mfderiv 𝓘(ℝ, ℝ) J ((i ∘ b.symm) ∘ l) 0
          ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) : E × R) := hf
      _ = (mfderiv (𝓡 r) J i y : R →L[ℝ] E × R)
          (db (dl ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1))) := hd
      _ = (eV (db v₀)).val := by
        rw [hunit]
        exact he.symm
  -- The inverse-dual pole covector evaluates on that same derivative, not an arbitrary frame map.
  let ν : K (i y) →L[ℝ] ℝ :=
    ((innerSL ℝ w).comp (mfderiv (𝓡 r) (𝓡 r) b y)).comp eV.symm.toContinuousLinearMap
  let ν₀ : K (a.symm x) →L[ℝ] ℝ :=
    (innerSL ℝ ((1 / 2 : ℝ) • p.2 w)).comp (L x).symm.toContinuousLinearMap
  have hν : HEq ν₀ ν := by
    have hcast (s t : Z) (hst : s = t) (f : K s →L[ℝ] ℝ) (g' : K t →L[ℝ] ℝ)
        (hh : ∀ v : K s, f v = g' ⟨v.val, hst ▸ v.property⟩) : HEq f g' := by
      subst t
      apply heq_of_eq
      ext v
      exact hh v
    apply hcast _ _ hpoint
    intro v
    obtain ⟨v₀, rfl⟩ := (L x).surjective v
    have hv : (⟨(L x v₀).val, hpoint ▸ (L x v₀).property⟩ : K (i y)) =
        eV (db ((1 / 2 : ℝ) • p.2.symm v₀)) := Subtype.ext (hL v₀)
    change inner ℝ ((1 / 2 : ℝ) • p.2 w) ((L x).symm (L x v₀)) = ν _
    rw [(L x).symm_apply_apply, hv]
    change _ = inner ℝ w
      (mfderiv (𝓡 r) (𝓡 r) b y (eV.symm (eV (db ((1 / 2 : ℝ) • p.2.symm v₀)))))
    rw [eV.symm_apply_apply]
    have hdb : mfderiv (𝓡 r) (𝓡 r) b y (db ((1 / 2 : ℝ) • p.2.symm v₀)) =
        (1 / 2 : ℝ) • p.2.symm v₀ := by
      exact DFunLike.congr_fun (hbd.comp_symm_deriv hbt) _
    rw [hdb, real_inner_smul_left, real_inner_smul_right]
    congr 1
    have hiso := p.2.inner_map_map w (p.2.symm v₀)
    rw [p.2.apply_symm_apply] at hiso
    exact hiso
  -- Compatibility recovers the same base covector and cancels the mixed metric terms.
  let v₁ : V p.1 := (1 / 2 : ℝ) • C x (p.2 w)
  let horizontal : E × R := H.lift (a.symm x) ξ
  let vertical : E × R := (L x v₁).val
  let tangent : TangentBundle J Z :=
    ⟨a.symm x, horizontal + vertical⟩
  have hF : (F ⟨⟨p.1, ξ⟩, (2 : ℝ) • p.2 u, v₁⟩ : TangentBundle J Z) = tangent := by
    let radial : E × R := mfderiv 𝓘(ℝ, ℝ) J
      (fun t : ℝ ↦ a.symm ⟨p.1, (2 : ℝ) • p.2 u + t • v₁⟩) 0
        ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
    have ht : (F ⟨⟨p.1, ξ⟩, (2 : ℝ) • p.2 u, v₁⟩ : TangentBundle J Z) =
        ⟨a.symm x, horizontal + radial⟩ :=
      (exists_frameSphere_tangentParametrization r V H).choose_spec
        (⟨p.1, ξ⟩ : TangentBundle I B) ((2 : ℝ) • p.2 u) v₁
    have hd := (exists_frameSphere_verticalDerivativeEquiv (EB := E) r V).choose_spec.1 x v₁
    exact ht.trans (congrArg (fun v : E × R ↦
      (⟨a.symm x, horizontal + v⟩ : TangentBundle J Z)) hd.symm)
  have hqpoint : q (a.symm x) = p.1 := by
    rw [hpoint]
    rfl
  have hsplit : eSplit (d tangent) =
      ⟨a.symm x, g.inner p.1 ξ, ν₀⟩ := by
    have hd : d tangent = ⟨tangent.proj, h.inner tangent.proj tangent.snd⟩ :=
      (exists_tangentMusical_diffeomorph h).choose_spec tangent
    have he : eSplit ⟨tangent.proj, h.inner tangent.proj tangent.snd⟩ =
        H.cotangentSplitMap q ⟨tangent.proj, h.inner tangent.proj tangent.snd⟩ :=
      (SmoothHorizontalLift.exists_cotangentSplitHomeomorph q hq H).choose_spec.1 _
    apply (congrArg eSplit hd).trans
    apply he.trans
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext
      · change (h.inner (a.symm x) (horizontal + vertical)).comp
          (H.lift (a.symm x)) = g.inner p.1 ξ
        ext η
        change h.inner (a.symm x) (horizontal + vertical)
          (H.lift (a.symm x) η) = g.inner p.1 ξ η
        rw [map_add, add_apply]
        have hh : h.inner (a.symm x) horizontal (H.lift (a.symm x) η) =
            g.inner (q (a.symm x)) ξ
              (mfderiv J I q (a.symm x) (H.lift (a.symm x) η)) :=
          DFunLike.congr_fun (hcompat (a.symm x) ξ) (H.lift (a.symm x) η)
        have hh₀ : h.inner (a.symm x) (H.lift (a.symm x) η) (L x v₁).val =
            g.inner (q (a.symm x)) η (mfderiv J I q (a.symm x) (L x v₁).val) :=
          DFunLike.congr_fun (hcompat (a.symm x) η) (L x v₁).val
        have hright := H.right_inv (a.symm x) η
        have hker : mfderiv J I q (a.symm x) (L x v₁).val = 0 := (L x v₁).property
        rw [hright, hqpoint] at hh
        rw [hker, map_zero] at hh₀
        have hv : h.inner (a.symm x) vertical (H.lift (a.symm x) η) = 0 :=
          (h.symm (a.symm x) vertical (H.lift (a.symm x) η)).trans hh₀
        exact (congrArg₂ (fun a b : ℝ ↦ a + b) hh hv).trans (add_zero _)
      · ext η
        obtain ⟨η₀, rfl⟩ := (L x).surjective η
        change h.inner (a.symm x) (horizontal + vertical)
          (L x η₀).val = inner ℝ ((1 / 2 : ℝ) • p.2 w) ((L x).symm (L x η₀))
        rw [map_add, add_apply, (L x).symm_apply_apply]
        have hh : h.inner (a.symm x) horizontal (L x η₀).val =
            g.inner (q (a.symm x)) ξ (mfderiv J I q (a.symm x) (L x η₀).val) :=
          DFunLike.congr_fun (hcompat (a.symm x) ξ) (L x η₀).val
        have hker : mfderiv J I q (a.symm x) (L x η₀).val = 0 := (L x η₀).property
        rw [hker, map_zero] at hh
        rw [hh, zero_add]
        have hC := (exists_frameSphere_verticalRieszComparison r V h).choose_spec.1 x (p.2 w) η₀
        change h.inner (a.symm x) (L x ((1 / 2 : ℝ) • C x (p.2 w))).val
          (L x η₀).val = _
        rw [(L x).map_smul]
        change h.inner (a.symm x) ((1 / 2 : ℝ) • (L x (C x (p.2 w))).val)
          (L x η₀).val = _
        rw [map_smul, smul_apply, hC, real_inner_smul_left]
        simp only [smul_eq_mul]
  let pQ : Q := ⟨(⟨p.1, g.inner p.1 ξ⟩, p), rfl⟩
  have hcot : eCot (associatedBundleMk G Q _ pQ
        (orthogonalSphereCotangentChart r false z)) = eSplit.symm
      ⟨associatedBundleMk G P (OrthogonalSphere r) p
          (orthogonalSphereCotangentChart r false z).proj,
        g.inner p.1 ξ,
        (associatedSphereCotangentRepresentative S p
          (orthogonalSphereCotangentChart r false z)).snd⟩ :=
    (exists_associatedSphereCotangentHomeomorph S H).choose_spec pQ
      (orthogonalSphereCotangentChart r false z)
  apply eSplit.injective
  change eSplit (eCot (associatedBundleMk G Q _ pQ
    (orthogonalSphereCotangentChart r false z))) =
      eSplit (d (F ⟨⟨p.1, ξ⟩, (2 : ℝ) • p.2 u, v₁⟩))
  have hleft := (congrArg eSplit hcot).trans (eSplit.apply_symm_apply _)
  have hright := (congrArg (fun v : TangentBundle J Z ↦ eSplit (d v)) hF).trans hsplit
  apply hleft.trans
  apply Eq.trans _ hright.symm
  rw [orthogonalSphereCotangentChart_apply]
  symm
  apply TotalSpace.ext
  · exact hpoint
  · have hprod {α β γ : Type} (a : α) {v : β} {w : γ} (hvw : HEq v w) :
        HEq (a, v) (a, w) := by
      cases hvw
      rfl
    exact hprod (g.inner p.1 ξ) hν

end AtiyahSinger
