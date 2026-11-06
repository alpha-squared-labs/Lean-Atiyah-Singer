/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.OrthogonalSphereCotangent
public import AtiyahSinger.Geometry.VerticalCotangentBundle

/-!
# The associated sphere cotangent fiber and the actual vertical dual

Public module ID: M1082.

The derivative of the original fiber inclusion y ↦ [p,y] identifies the
sphere tangent space with the actual kernel of the associated projection.
Dualizing that specified map gives the canonical associated cotangent
comparison. It uses the original quotient topology and the same selected
smooth sphere atlas and vertical kernel atlas throughout.

SG III.13, pp.251--252, uses the associated sphere cotangent bundle in the
cotangent splitting. The derivative and quotient descent arguments below
make that canonical identification explicit. No metric identifies vertical
vectors with covectors. No smooth structure on the associated cotangent
quotient is asserted merely by constructing its topological comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Function Set Topology
open scoped Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {P B : Type*} [TopologicalSpace P] [TopologicalSpace B] [ChartedSpace E B]
  [IsManifold 𝓘(ℝ, E) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B}
  (S : SmoothOrthogonalPrincipalAtlas r 𝓘(ℝ, E) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "R" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "V" => VerticalTangentModel (E × R) E
local notation "q" => smoothAssociatedSphereProjection S
local notation "W" => VerticalCotangentFiber (E := E × R) (F := E) (q : Z → B)

set_option backward.isDefEq.respectTransparency false in
/-- The actual fiber-inclusion derivative is a linear equivalence onto the vertical kernel. -/
theorem exists_associatedSphereFiberTangentEquiv (p : P) (y : OrthogonalSphere r) :
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    ∃ e : TangentSpace (𝓡 r) y ≃L[ℝ]
        VerticalTangentFiber 𝓘(ℝ, E × R) 𝓘(ℝ, E) (q : Z → B)
          (associatedBundleMk G P (OrthogonalSphere r) p y),
      ∀ w, (e w).val = mfderiv (𝓡 r) 𝓘(ℝ, E × R)
        (associatedBundleMk G P (OrthogonalSphere r) p) y w := by
  classical
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let I := 𝓘(ℝ, E × R)
  let J := 𝓘(ℝ, E).prod (𝓡 r)
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  let b := projection p
  let t := associatedSphereTrivialization S b
  let g : G := (S.trivialization b p).2
  let a := orthogonalSphereDiffeomorph r g
  let i : OrthogonalSphere r → Z := associatedBundleMk G P (OrthogonalSphere r) p
  have hb : b ∈ (S.trivialization b).baseSet := S.mem_baseSet b
  have hbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hz : z ∈ t.source := t.mem_source.mpr (by
    change projection p ∈ t.baseSet
    rw [hbase]
    exact hb)
  have ht : t.toOpenPartialHomeomorph.MDifferentiable I J := by
    have h := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    exact ⟨h.1.mdifferentiableOn (by simp), h.2.mdifferentiableOn (by simp)⟩
  let L := ht.mfderiv hz
  let da := (a.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (show y ∈ a.toHomeomorph.toOpenPartialHomeomorph.source from Set.mem_univ y)
  let di := mfderiv (𝓡 r) I i y
  have hi : MDifferentiable (𝓡 r) I i :=
    (smoothAssociatedSphereFiberInclusion S p).contMDiff.mdifferentiable (by simp)
  have hcoord (s : OrthogonalSphere r) : t (i s) = (b, a s) :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p s hb
  -- The derivative of the actual fiber inclusion is the second-factor inclusion in this chart.
  have hdi (w : TangentSpace (𝓡 r) y) : L (di w) = (0, da w) := by
    have hc := mfderiv_comp y (ht.mdifferentiableAt hz) (hi y)
    have heq : (t.toOpenPartialHomeomorph ∘ i) = fun s ↦ (b, a s) := funext hcoord
    rw [heq, mfderiv_prodMk mdifferentiableAt_const (a.mdifferentiable (by simp) y),
      mfderiv_const] at hc
    exact (congrArg (fun A ↦ A w) hc).symm
  -- The first component of the same derivative is precisely the original projection derivative.
  have hproj (v : TangentSpace I z) : (L v).1 = mfderiv I 𝓘(ℝ, E) q z v := by
    have heq : (fun z' ↦ (t z').1) =ᶠ[𝓝 z] (q : Z → B) := by
      filter_upwards [t.open_source.mem_nhds hz] with z' hz'
      exact t.coe_fst hz'
    have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, E))
    have hc := mfderiv_comp z (mdifferentiableAt_fst (I := 𝓘(ℝ, E))
      (I' := 𝓡 r)) (ht.mdifferentiableAt hz)
    rw [mfderiv_fst] at hc
    change mfderiv I 𝓘(ℝ, E) (Prod.fst ∘ t.toOpenPartialHomeomorph) z = _ at hd
    rw [hc] at hd
    exact congrArg (fun A ↦ A v) hd
  let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B) z
  let d : TangentSpace (𝓡 r) y →L[ℝ] K :=
    di.codRestrict (LinearMap.ker (mfderiv I 𝓘(ℝ, E) q z).toLinearMap) (by
      intro w
      change mfderiv I 𝓘(ℝ, E) q z (di w) = 0
      rw [← hproj, hdi])
  have hbij : Bijective d := by
    constructor
    · intro v w hvw
      apply da.injective
      have h := congrArg (fun v : K ↦ L v.val) hvw
      change L (di v) = L (di w) at h
      rw [hdi, hdi] at h
      exact congrArg Prod.snd h
    · intro v
      refine ⟨da.symm (L v.val).2, ?_⟩
      apply Subtype.ext
      apply L.injective
      change L (di (da.symm (L v.val).2)) = L v.val
      rw [hdi, da.apply_symm_apply]
      apply Prod.ext
      · exact ((hproj v.val).trans v.property).symm
      · rfl
  -- This equivalence retains the exact original inclusion derivative, not a rank comparison.
  let e := (LinearEquiv.ofBijective d.toLinearMap hbij).toContinuousLinearEquiv
  exact ⟨e, fun w ↦ rfl⟩


/-- The specified fiber derivative, selected with its actual inclusion formula. -/
def associatedSphereFiberTangentEquiv (p : P) (y : OrthogonalSphere r) :
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    TangentSpace (𝓡 r) y ≃L[ℝ]
      VerticalTangentFiber 𝓘(ℝ, E × R) 𝓘(ℝ, E) (q : Z → B)
        (associatedBundleMk G P (OrthogonalSphere r) p y) :=
  (exists_associatedSphereFiberTangentEquiv S p y).choose

/-- Transport the original sphere covector by the inverse of the actual fiber derivative. -/
def associatedSphereCotangentRepresentative (p : P)
    (z : CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    TotalSpace (V →L[ℝ] ℝ) W :=
  letI := associatedSphereChartedSpace S
  letI := associatedSphereIsManifold S
  ⟨associatedBundleMk G P (OrthogonalSphere r) p z.proj,
    z.snd.comp (associatedSphereFiberTangentEquiv S p z.proj).symm.toContinuousLinearMap⟩

set_option maxHeartbeats 4000000 in
-- Descend the exact dual formula and prove continuity in both original bundle topologies.
set_option backward.isDefEq.respectTransparency false in
/-- The associated cotangent quotient is canonically the actual vertical cotangent total space. -/
theorem exists_associatedSphereVerticalCotangentHomeomorph :
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := verticalTangentFiberBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    letI := verticalTangentVectorBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    ∃ e : AssociatedBundle G P (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) ≃ₜ
        TotalSpace (V →L[ℝ] ℝ) W,
      ∀ p z, e (associatedBundleMk G P _ p z) =
        associatedSphereCotangentRepresentative S p z := by
  classical
  -- Stage 1: the original inverse differential cotangent action cancels the
  -- change of principal representative, before descending through the quotient.
  have representative_smul (p : P) (g : G)
      (η : CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      associatedSphereCotangentRepresentative S (MulOpposite.op g • p) η =
        associatedSphereCotangentRepresentative S p (g • η) := by
    classical
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let I := 𝓘(ℝ, E × R)
    let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B)
    have covector_ext {z z' : Z} (h : z = z')
        (α : K z →L[ℝ] ℝ) (β : K z' →L[ℝ] ℝ)
        (heq : ∀ v hv hv', α ⟨v, hv⟩ = β ⟨v, hv'⟩) :
        (⟨z, α⟩ : TotalSpace (V →L[ℝ] ℝ) W) = ⟨z', β⟩ := by
      subst z'
      congr 1
      ext v
      exact heq v.val v.property v.property
    let y := η.proj
    let a := orthogonalSphereDiffeomorph r g
    let i₁ := associatedBundleMk G P (OrthogonalSphere r) (MulOpposite.op g • p)
    let i₂ := associatedBundleMk G P (OrthogonalSphere r) p
    let e₁ := associatedSphereFiberTangentEquiv S (MulOpposite.op g • p) y
    let e₂ := associatedSphereFiberTangentEquiv S p (g • y)
    have he₁ (w : R) : (e₁ w).val = mfderiv (𝓡 r) I i₁ y w :=
      (exists_associatedSphereFiberTangentEquiv S (MulOpposite.op g • p) y).choose_spec w
    have he₂ (w : R) : (e₂ w).val = mfderiv (𝓡 r) I i₂ (g • y) w :=
      (exists_associatedSphereFiberTangentEquiv S p (g • y)).choose_spec w
    have hd : mfderiv (𝓡 r) I i₁ y =
        (mfderiv (𝓡 r) I i₂ (g • y)).comp (mfderiv (𝓡 r) (𝓡 r) a y) := by
      have heq : i₁ = i₂ ∘ a := funext (fun z ↦ associatedBundleMk_smul p g z)
      rw [heq]
      exact mfderiv_comp y
        ((smoothAssociatedSphereFiberInclusion S p).contMDiff.mdifferentiable (by simp) _)
        (a.mdifferentiable (by simp) y)
    apply covector_ext (associatedBundleMk_smul p g y)
    intro v hv hv'
    change η.snd (e₁.symm ⟨v, hv⟩) =
      η.snd (mfderiv (𝓡 r) (𝓡 r) a.symm (a y) (e₂.symm ⟨v, hv'⟩))
    congr 1
    let da := (a.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (show y ∈ a.toHomeomorph.toOpenPartialHomeomorph.source from Set.mem_univ y)
    have he : da (e₁.symm ⟨v, hv⟩) = e₂.symm ⟨v, hv'⟩ := by
      apply e₂.injective
      apply Subtype.ext
      rw [he₂]
      change mfderiv (𝓡 r) I i₂ (g • y)
        (mfderiv (𝓡 r) (𝓡 r) a y (e₁.symm ⟨v, hv⟩)) = _
      have h := congrArg (fun A ↦ A (e₁.symm ⟨v, hv⟩)) hd
      change mfderiv (𝓡 r) I i₁ y (e₁.symm ⟨v, hv⟩) = _ at h
      rw [← he₁, e₁.apply_symm_apply] at h
      exact h.symm.trans (congrArg Subtype.val (e₂.apply_symm_apply ⟨v, hv'⟩)).symm
    rw [← he]
    exact (congrArg (fun A ↦ A (e₁.symm ⟨v, hv⟩))
      ((a.toOpenPartialHomeomorph_mdifferentiable (by simp)).symm_comp_deriv
        (show y ∈ a.toHomeomorph.toOpenPartialHomeomorph.source from Set.mem_univ y))).symm
  -- Stage 2: descend that exact formula and prove bijectivity in the original fibers.
  have quotient_equiv :
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      ∃ e : AssociatedBundle G P (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) ≃
          TotalSpace (V →L[ℝ] ℝ) W,
        ∀ p η, e (associatedBundleMk G P _ p η) =
          associatedSphereCotangentRepresentative S p η := by
    classical
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
    let A := AssociatedBundle G P Y
    let T := TotalSpace (V →L[ℝ] ℝ) W
    let rep := associatedSphereCotangentRepresentative S
    let F : A → T := Quotient.lift (fun u : P × Y ↦ rep u.1 u.2) (by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      exact ((representative_smul x.1 g (g⁻¹ • x.2)).trans
        (congrArg (rep x.1) (smul_inv_smul g x.2))).symm)
    have hrep (p : P) : Injective (rep p) := by
      intro η η' h
      have hbase := congrArg TotalSpace.proj h
      change associatedBundleMk G P (OrthogonalSphere r) p η.proj =
        associatedBundleMk G P (OrthogonalSphere r) p η'.proj at hbase
      let b := projection p
      let t := associatedSphereTrivialization S b
      have hcoord (s : OrthogonalSphere r) :
          t (associatedBundleMk G P (OrthogonalSphere r) p s) =
            (projection p, (S.trivialization b p).2 • s) :=
        (exists_associatedBundleTrivialization (F := OrthogonalSphere r) S.toIsPrincipalBundle
          (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p s (S.mem_baseSet b)
      have hpair := congrArg t hbase
      rw [hcoord η.proj, hcoord η'.proj] at hpair
      have hy : η.proj = η'.proj :=
        (MulAction.injective (S.trivialization b p).2) (congrArg Prod.snd hpair)
      obtain ⟨y, ξ⟩ := η
      obtain ⟨y', ξ'⟩ := η'
      dsimp only at hy
      subst y'
      congr 1
      have hξ : ξ.comp (associatedSphereFiberTangentEquiv S p y).symm.toContinuousLinearMap =
          ξ'.comp (associatedSphereFiberTangentEquiv S p y).symm.toContinuousLinearMap :=
        (TotalSpace.mk_inj (F := V →L[ℝ] ℝ) (E := W)).mp h
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun f ↦ f (associatedSphereFiberTangentEquiv S p y v)) hξ
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] using hv
    have hF : Bijective F := by
      constructor
      · intro x y hxy
        induction x using Quotient.inductionOn with
        | h x =>
          induction y using Quotient.inductionOn with
          | h y =>
            have hbase := congrArg TotalSpace.proj hxy
            obtain ⟨g, hg⟩ := Quotient.exact hbase
            have hp : y.1 = MulOpposite.op g • x.1 := congrArg Prod.fst hg
            change rep x.1 x.2 = rep y.1 y.2 at hxy
            rw [hp] at hxy
            change associatedSphereCotangentRepresentative S x.1 x.2 =
              associatedSphereCotangentRepresentative S (MulOpposite.op g • x.1) y.2 at hxy
            rw [representative_smul] at hxy
            have hη := hrep x.1 hxy
            change associatedBundleMk G P Y x.1 x.2 = associatedBundleMk G P Y y.1 y.2
            rw [hp, associatedBundleMk_smul, hη]
      · rintro ⟨z, ξ⟩
        induction z using Quotient.inductionOn with
        | h u =>
          let e := associatedSphereFiberTangentEquiv S u.1 u.2
          refine ⟨associatedBundleMk G P Y u.1 ⟨u.2, ξ.comp e.toContinuousLinearMap⟩, ?_⟩
          change (⟨associatedBundleMk G P (OrthogonalSphere r) u.1 u.2,
            (ξ.comp e.toContinuousLinearMap).comp e.symm.toContinuousLinearMap⟩ : T) = _
          congr 1
          ext v
          exact congrArg ξ (e.apply_symm_apply v)
    exact ⟨Equiv.ofBijective F hF, fun _ _ ↦ rfl⟩
  -- Stage 3: evaluate covectors on continuous native vertical frames.
  -- The original smooth sphere chart differentiates into the ambient tangent bundle.
  have local_forward_continuous (b : B) :
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      letI := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
      letI := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
      let I := 𝓘(ℝ, E × R)
      let J := 𝓘(ℝ, E).prod (𝓡 r)
      let t := associatedSphereTrivialization S b
      let H : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) →
          TotalSpace (V →L[ℝ] ℝ) W := fun u ↦
        ⟨t.toOpenPartialHomeomorph.symm (u.1, u.2.proj),
          u.2.snd.comp ((ContinuousLinearMap.snd ℝ E R).comp
            ((mfderiv I J t (t.toOpenPartialHomeomorph.symm (u.1, u.2.proj))).comp
              (LinearMap.ker (mfderiv I 𝓘(ℝ, E) q
                (t.toOpenPartialHomeomorph.symm (u.1, u.2.proj))).toLinearMap).subtypeL))⟩
      ∀ u, u.1 ∈ t.baseSet → ContinuousAt H u := by
    have dual_continuous_criterion
        {F M P : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] [TopologicalSpace M] [TopologicalSpace P]
        {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
        [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
        [FiberBundle F W₀] [VectorBundle ℝ F W₀]
        (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
        (p : P) (hb : ContinuousAt b p)
        (heval : ∀ v : F, ContinuousAt
          (fun u ↦ a u ((trivializationAt F W₀ (b p)).symmL ℝ (b u) v)) p) :
        ContinuousAt
          (fun u ↦ (⟨b u, a u⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p := by
      rw [continuousAt_hom_bundle]
      refine ⟨hb, ?_⟩
      apply continuousAt_clm_apply.mpr
      intro v
      have hscalar (x : M) :
          (trivializationAt ℝ (fun _ : M ↦ ℝ) (b p)).continuousLinearMapAt ℝ x =
            ContinuousLinearMap.id ℝ ℝ := by
        change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x = _
        exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
      simpa only [ContinuousLinearMap.inCoordinates, hscalar, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_apply] using heval v
    have scalar_eval
        {F M P : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [TopologicalSpace M] [TopologicalSpace P]
        {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
        [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
        [FiberBundle F W₀] [VectorBundle ℝ F W₀]
        (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
        (v : ∀ p, W₀ (b p)) (p : P)
        (ha : ContinuousAt
          (fun u ↦ (⟨b u, a u⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p)
        (hv : ContinuousAt (fun u ↦ (⟨b u, v u⟩ : TotalSpace F W₀)) p) :
        ContinuousAt (fun u ↦ a u (v u)) p := by
      have h := ContinuousAt.clm_bundle_apply (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ) ha hv
      exact (FiberBundle.continuousAt_totalSpace ℝ _ |>.mp h).2
    have frame_continuous
        {F M P : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [TopologicalSpace M] [TopologicalSpace P]
        {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
        [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
        [FiberBundle F W₀] [VectorBundle ℝ F W₀]
        (b : P → M) (p : P) (hb : ContinuousAt b p) (v : F) :
        ContinuousAt (fun u ↦ (⟨b u, (trivializationAt F W₀ (b p)).symmL ℝ (b u) v⟩ :
          TotalSpace F W₀)) p := by
      let t := trivializationAt F W₀ (b p)
      have hc := (t.continuousAt_symm_prodMk_left (v := v)
        (mem_baseSet_trivializationAt _ _ _)).comp hb
      apply hc.congr_of_eventuallyEq
      filter_upwards [hb.preimage_mem_nhds
        (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with u hq
      change (⟨b u, t.symmL ℝ (b u) v⟩ : TotalSpace F W₀) = _
      rw [t.symmL_apply hq]
      exact t.mk_symm hq v
    classical
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
    let := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
    let I := 𝓘(ℝ, E × R)
    let J := 𝓘(ℝ, E).prod (𝓡 r)
    let t := associatedSphereTrivialization S b
    let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B)
    let X := B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
    let base : X → Z := fun u ↦ t.toOpenPartialHomeomorph.symm (u.1, u.2.proj)
    let a (u : X) : K (base u) →L[ℝ] ℝ :=
      u.2.snd.comp ((ContinuousLinearMap.snd ℝ E R).comp
        ((mfderiv I J t (base u)).comp
          (LinearMap.ker (mfderiv I 𝓘(ℝ, E) q (base u)).toLinearMap).subtypeL))
    change ∀ u : X, u.1 ∈ t.baseSet →
      ContinuousAt (fun u ↦ (⟨base u, a u⟩ : TotalSpace (V →L[ℝ] ℝ) W)) u
    intro u hu
    have htgt : (u.1, u.2.proj) ∈ t.target := t.mem_target.mpr hu
    have hsrc : base u ∈ t.source := t.toOpenPartialHomeomorph.symm.map_source htgt
    have hcoord : ContinuousAt (fun u : X ↦ (u.1, u.2.proj)) u :=
      continuousAt_fst.prodMk
        ((FiberBundle.continuous_proj _ _).continuousAt.comp continuousAt_snd)
    have hb : ContinuousAt base u :=
      (t.toOpenPartialHomeomorph.continuousAt_symm htgt).comp
        (f := fun u : X ↦ (u.1, u.2.proj)) hcoord
    have ht := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have htAt : ContMDiffAt I J ∞ t (base u) :=
      (ht.1 (base u) hsrc).contMDiffAt (t.open_source.mem_nhds hsrc)
    apply dual_continuous_criterion base a u hb
    intro v
    let frame := trivializationAt V K (base u)
    let w (u : X) : K (base u) := frame.symmL ℝ (base u) v
    have hwK : ContinuousAt (fun u ↦ (⟨base u, w u⟩ : TotalSpace V K)) u :=
      frame_continuous base u hb v
    have hwM : ContinuousAt
        (fun u ↦ (⟨base u, (w u).val⟩ : TangentBundle I Z)) u :=
      ((continuous_induced_dom (f := verticalTangentInclusion I 𝓘(ℝ, E) V q)).continuousAt.comp hwK)
    have hdt : ContinuousAt
        (fun u ↦ tangentMap I J t (⟨base u, (w u).val⟩ : TangentBundle I Z)) u :=
      (htAt.continuousAt_tangentMap (by simp)).comp hwM
    have hds : Continuous (tangentMap J (𝓡 r)
        (Prod.snd : B × OrthogonalSphere r → OrthogonalSphere r)) :=
      (contMDiff_snd (I := 𝓘(ℝ, E)) (J := 𝓡 r) (n := ∞)).continuous_tangentMap (by simp)
    have htw : ContinuousAt
        (fun u ↦ (⟨u.2.proj, (mfderiv I J t (base u) (w u).val).2⟩ :
          TangentBundle (𝓡 r) (OrthogonalSphere r))) u := by
      apply (hds.continuousAt.comp hdt).congr_of_eventuallyEq
      filter_upwards [hcoord.preimage_mem_nhds (t.open_target.mem_nhds htgt)] with u' hu'
      have heq := t.toOpenPartialHomeomorph.right_inv hu'
      change (⟨u'.2.proj, (mfderiv I J t (base u') (w u').val).2⟩ :
        TangentBundle (𝓡 r) (OrthogonalSphere r)) = _
      have hd : mfderiv J (𝓡 r) (Prod.snd : B × OrthogonalSphere r → OrthogonalSphere r)
          (t (base u')) = ContinuousLinearMap.snd ℝ E R := mfderiv_snd
      simp only [Function.comp_apply, tangentMap, hd]
      apply TotalSpace.ext (congrArg Prod.snd heq).symm
      exact HEq.rfl
    exact scalar_eval (fun u : X ↦ u.2.proj) (fun u ↦ u.2.snd)
      (fun u ↦ (mfderiv I J t (base u) (w u).val).2) u continuousAt_snd htw
  -- Stage 4: the inverse chart differentiates the second tangent factor.
  -- Its image is vertical with the original induced topology; dual evaluation is continuous.
  have local_inverse_continuous (b : B) :
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      letI := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
      letI := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
      let I := 𝓘(ℝ, E × R)
      let J := 𝓘(ℝ, E).prod (𝓡 r)
      let t := associatedSphereTrivialization S b
      let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B)
      ∀ (k : ∀ z, R →L[ℝ] K z),
        (∀ z, z ∈ t.source → ∀ v,
          (k z v).val = mfderiv J I t.toOpenPartialHomeomorph.symm (t z) (0, v)) →
        ∀ w : TotalSpace (V →L[ℝ] ℝ) W, w.proj ∈ t.source →
          ContinuousAt
            (fun w : TotalSpace (V →L[ℝ] ℝ) W ↦ ((t w.proj).1,
              (⟨(t w.proj).2, w.snd.comp (k w.proj)⟩ :
                CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))) w := by
    have dual_continuous_criterion
        {F M P : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [FiniteDimensional ℝ F] [TopologicalSpace M] [TopologicalSpace P]
        {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
        [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
        [FiberBundle F W₀] [VectorBundle ℝ F W₀]
        (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
        (p : P) (hb : ContinuousAt b p)
        (heval : ∀ v : F, ContinuousAt
          (fun u ↦ a u ((trivializationAt F W₀ (b p)).symmL ℝ (b u) v)) p) :
        ContinuousAt
          (fun u ↦ (⟨b u, a u⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p := by
      rw [continuousAt_hom_bundle]
      refine ⟨hb, ?_⟩
      apply continuousAt_clm_apply.mpr
      intro v
      have hscalar (x : M) :
          (trivializationAt ℝ (fun _ : M ↦ ℝ) (b p)).continuousLinearMapAt ℝ x =
            ContinuousLinearMap.id ℝ ℝ := by
        change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x = _
        exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
      simpa only [ContinuousLinearMap.inCoordinates, hscalar, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_apply] using heval v
    have scalar_eval
        {F M P : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [TopologicalSpace M] [TopologicalSpace P]
        {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
        [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
        [FiberBundle F W₀] [VectorBundle ℝ F W₀]
        (b : P → M) (a : ∀ p, W₀ (b p) →L[ℝ] ℝ)
        (v : ∀ p, W₀ (b p)) (p : P)
        (ha : ContinuousAt
          (fun u ↦ (⟨b u, a u⟩ : TotalSpace (F →L[ℝ] ℝ) (fun x ↦ W₀ x →L[ℝ] ℝ))) p)
        (hv : ContinuousAt (fun u ↦ (⟨b u, v u⟩ : TotalSpace F W₀)) p) :
        ContinuousAt (fun u ↦ a u (v u)) p := by
      have h := ContinuousAt.clm_bundle_apply (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ) ha hv
      exact (FiberBundle.continuousAt_totalSpace ℝ _ |>.mp h).2
    have frame_continuous
        {F M P : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
        [TopologicalSpace M] [TopologicalSpace P]
        {W₀ : M → Type _} [∀ x, AddCommGroup (W₀ x)] [∀ x, Module ℝ (W₀ x)]
        [∀ x, TopologicalSpace (W₀ x)] [TopologicalSpace (TotalSpace F W₀)]
        [FiberBundle F W₀] [VectorBundle ℝ F W₀]
        (b : P → M) (p : P) (hb : ContinuousAt b p) (v : F) :
        ContinuousAt (fun u ↦ (⟨b u, (trivializationAt F W₀ (b p)).symmL ℝ (b u) v⟩ :
          TotalSpace F W₀)) p := by
      let t := trivializationAt F W₀ (b p)
      have hc := (t.continuousAt_symm_prodMk_left (v := v)
        (mem_baseSet_trivializationAt _ _ _)).comp hb
      apply hc.congr_of_eventuallyEq
      filter_upwards [hb.preimage_mem_nhds
        (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))] with u hq
      change (⟨b u, t.symmL ℝ (b u) v⟩ : TotalSpace F W₀) = _
      rw [t.symmL_apply hq]
      exact t.mk_symm hq v
    classical
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
    let := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
    let I := 𝓘(ℝ, E × R)
    let J := 𝓘(ℝ, E).prod (𝓡 r)
    let t := associatedSphereTrivialization S b
    let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B)
    let X := TotalSpace (V →L[ℝ] ℝ) W
    change ∀ (k : ∀ z, R →L[ℝ] K z),
      (∀ z, z ∈ t.source → ∀ v,
        (k z v).val = mfderiv J I t.toOpenPartialHomeomorph.symm (t z) (0, v)) →
      ∀ w : X, w.proj ∈ t.source → ContinuousAt
        (fun w : X ↦ ((t w.proj).1,
          (⟨(t w.proj).2, w.snd.comp (k w.proj)⟩ :
            CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))) w
    intro k hk w hw
    have hb : ContinuousAt (fun w : X ↦ w.proj) w :=
      (FiberBundle.continuous_proj _ _).continuousAt
    have ht : ContinuousAt (fun w : X ↦ t w.proj) w :=
      (t.toOpenPartialHomeomorph.continuousAt hw).comp hb
    apply ht.fst.prodMk
    apply dual_continuous_criterion (F := R) (W₀ := TangentSpace (𝓡 r)) (fun w : X ↦ (t w.proj).2)
      (fun w ↦ w.snd.comp (k w.proj)) w ht.snd
    intro v
    let sphereFrame := trivializationAt R (TangentSpace (𝓡 r)) (t w.proj).2
    let s (w : X) : R := sphereFrame.symmL ℝ (t w.proj).2 v
    have hs : ContinuousAt (fun w : X ↦
        (⟨(t w.proj).2, s w⟩ : TangentBundle (𝓡 r) (OrthogonalSphere r))) w :=
      frame_continuous (fun w : X ↦ (t w.proj).2) w ht.snd v
    have hz : ContinuousAt (fun w : X ↦
        (⟨(t w.proj).1, 0⟩ : TangentBundle 𝓘(ℝ, E) B)) w :=
      (Bundle.Trivialization.continuous_zeroSection ℝ
        (F := E) (E := TangentSpace 𝓘(ℝ, E))).continuousAt.comp ht.fst
    have hprod : ContinuousAt (fun w : X ↦
        (⟨t w.proj, (0, s w)⟩ : TangentBundle J (B × OrthogonalSphere r))) w :=
      (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, E)) (I' := 𝓡 r)
        (n := ∞)).continuous.continuousAt.comp (hz.prodMk hs)
    have hsm := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have hsinv : ContMDiffAt J I ∞ t.toOpenPartialHomeomorph.symm (t w.proj) :=
      (hsm.2 (t w.proj) (t.map_source hw)).contMDiffAt
        (t.open_target.mem_nhds (t.map_source hw))
    have hder := (hsinv.continuousAt_tangentMap (by simp)).comp hprod
    have hK : ContinuousAt (fun w : X ↦
        (⟨w.proj, k w.proj (s w)⟩ : TotalSpace V K)) w := by
      have hind : IsInducing (verticalTangentInclusion I 𝓘(ℝ, E) V q) := ⟨rfl⟩
      apply hind.continuousAt_iff.mpr
      apply hder.congr_of_eventuallyEq
      filter_upwards [hb.preimage_mem_nhds (t.open_source.mem_nhds hw)] with w' hw'
      change (⟨w'.proj, (k w'.proj (s w')).val⟩ : TangentBundle I Z) = _
      simp only [Function.comp_apply, tangentMap]
      apply TotalSpace.ext (t.toOpenPartialHomeomorph.left_inv hw').symm
      exact heq_of_eq (hk w'.proj hw' (s w'))
    exact scalar_eval (fun w : X ↦ w.proj) (fun w ↦ w.snd)
      (fun w ↦ k w.proj (s w)) w continuousAt_id hK
  -- Stage 5: compare those continuous coordinate formulas with the actual
  -- chosen fiber derivative, using the same principal chart and sphere action.
  have local_formula (b : B) :
      letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      letI := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
      letI := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
      let I := 𝓘(ℝ, E × R)
      let J := 𝓘(ℝ, E).prod (𝓡 r)
      let t := associatedSphereTrivialization S b
      let H : B × CotangentTotalSpace (n := r) (M := OrthogonalSphere r) →
          TotalSpace (V →L[ℝ] ℝ) W := fun u ↦
        ⟨t.toOpenPartialHomeomorph.symm (u.1, u.2.proj),
          u.2.snd.comp ((ContinuousLinearMap.snd ℝ E R).comp
            ((mfderiv I J t (t.toOpenPartialHomeomorph.symm (u.1, u.2.proj))).comp
              (LinearMap.ker (mfderiv I 𝓘(ℝ, E) q
                (t.toOpenPartialHomeomorph.symm (u.1, u.2.proj))).toLinearMap).subtypeL))⟩
      ∀ p η, projection p ∈ t.baseSet →
        H (projection p, (S.trivialization b p).2 • η) =
          associatedSphereCotangentRepresentative S p η := by
    classical
    let := associatedSphereChartedSpace S
    let := associatedSphereIsManifold S
    let := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
    let := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
    let I := 𝓘(ℝ, E × R)
    let J := 𝓘(ℝ, E).prod (𝓡 r)
    let t := associatedSphereTrivialization S b
    let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B)
    dsimp only
    intro p η hp
    let y := η.proj
    let g : G := (S.trivialization b p).2
    let a := orthogonalSphereDiffeomorph r g
    let i := associatedBundleMk G P (OrthogonalSphere r) p
    let z := i y
    have covector_ext {z z' : Z} (h : z = z')
        (α : K z →L[ℝ] ℝ) (β : K z' →L[ℝ] ℝ)
        (heq : ∀ v hv hv', α ⟨v, hv⟩ = β ⟨v, hv'⟩) :
        (⟨z, α⟩ : TotalSpace (V →L[ℝ] ℝ) W) = ⟨z', β⟩ := by
      subst z'
      congr 1
      ext v
      exact heq v.val v.property v.property
    have spec := (exists_associatedBundleTrivialization (F := OrthogonalSphere r)
      S.toIsPrincipalBundle (S.trivialization b) (S.equivariant b)).choose_spec
    have hp' : projection p ∈ (S.trivialization b).baseSet := spec.1 ▸ hp
    have hcoord (s : OrthogonalSphere r) : t (i s) = (projection p, a s) :=
      spec.2.1 p s hp'
    have hz : z ∈ t.source := t.mem_source.mpr hp
    have hbase : t.toOpenPartialHomeomorph.symm (projection p, g • y) = z := by
      change t.toOpenPartialHomeomorph.symm (projection p, a y) = z
      rw [← hcoord y]
      exact t.toOpenPartialHomeomorph.left_inv hz
    have ht : t.toOpenPartialHomeomorph.MDifferentiable I J := by
      have h := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
      exact ⟨h.1.mdifferentiableOn (by simp), h.2.mdifferentiableOn (by simp)⟩
    let e := associatedSphereFiberTangentEquiv S p y
    let da := (a.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (show y ∈ a.toHomeomorph.toOpenPartialHomeomorph.source from Set.mem_univ y)
    have he (v : TangentSpace (𝓡 r) y) :
        (e v).val = mfderiv (𝓡 r) I i y v :=
      (exists_associatedSphereFiberTangentEquiv S p y).choose_spec v
    have hdi (v : TangentSpace (𝓡 r) y) :
        mfderiv I J t z (e v).val = (0, da v) := by
      rw [he v]
      have hc := mfderiv_comp y (ht.mdifferentiableAt hz)
        ((smoothAssociatedSphereFiberInclusion S p).contMDiff.mdifferentiable (by simp) y)
      have heq : (t.toOpenPartialHomeomorph ∘ i) = fun s ↦ (projection p, a s) := funext hcoord
      change mfderiv (𝓡 r) J (t.toOpenPartialHomeomorph ∘ i) y = _ at hc
      rw [heq, mfderiv_prodMk mdifferentiableAt_const (a.mdifferentiable (by simp) y),
        mfderiv_const] at hc
      exact (congrArg (fun A ↦ A v) hc).symm
    apply covector_ext hbase
    intro v hv hv'
    change η.snd (mfderiv (𝓡 r) (𝓡 r) a.symm (a y)
      (mfderiv I J t (t.toOpenPartialHomeomorph.symm (projection p, g • y)) v).2) =
        η.snd (e.symm ⟨v, hv'⟩)
    rw [hbase]
    have hvd := hdi (e.symm ⟨v, hv'⟩)
    rw [e.apply_symm_apply] at hvd
    rw [hvd]
    exact congrArg η.snd (da.symm_apply_apply (e.symm ⟨v, hv'⟩))
  -- Stage 6: glue through the original quotient charts and the same exact fiber formula.
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := verticalTangentFiberBundle q (associatedSphereProjection_isSubmersion S)
  let := verticalTangentVectorBundle q (associatedSphereProjection_isSubmersion S)
  let I := 𝓘(ℝ, E × R)
  let J := 𝓘(ℝ, E).prod (𝓡 r)
  let K := VerticalTangentFiber I 𝓘(ℝ, E) (q : Z → B)
  let Y := CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
  let A := AssociatedBundle G P Y
  let T := TotalSpace (V →L[ℝ] ℝ) W
  let ts (b : B) := associatedSphereTrivialization S b
  let tc (b : B) := (exists_associatedBundleTrivialization (F := Y)
    S.toIsPrincipalBundle (S.trivialization b) (S.equivariant b)).choose
  let H (b : B) : B × Y → T := fun u ↦
    ⟨(ts b).toOpenPartialHomeomorph.symm (u.1, u.2.proj),
      u.2.snd.comp ((ContinuousLinearMap.snd ℝ E R).comp
        ((mfderiv I J (ts b) ((ts b).toOpenPartialHomeomorph.symm (u.1, u.2.proj))).comp
          (LinearMap.ker (mfderiv I 𝓘(ℝ, E) q
            ((ts b).toOpenPartialHomeomorph.symm (u.1, u.2.proj))).toLinearMap).subtypeL))⟩
  have hbase (b : B) : (tc b).baseSet = (ts b).baseSet := by
    exact (exists_associatedBundleTrivialization (F := Y) S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1.trans
        (exists_associatedBundleTrivialization (F := OrthogonalSphere r)
          S.toIsPrincipalBundle (S.trivialization b) (S.equivariant b)).choose_spec.1.symm
  have hprincipal (b : B) : (ts b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization (F := OrthogonalSphere r)
      S.toIsPrincipalBundle (S.trivialization b) (S.equivariant b)).choose_spec.1
  obtain ⟨e, he⟩ := quotient_equiv
  have heOn (b : B) (x : A) (hx : x ∈ (tc b).source) : e x = H b (tc b x) := by
    induction x using Quotient.inductionOn with
    | h u =>
      have hp : projection u.1 ∈ (tc b).baseSet := (tc b).mem_source.mp hx
      have hpc : projection u.1 ∈ (S.trivialization b).baseSet :=
        (hbase b).trans (hprincipal b) ▸ hp
      have hcoord : tc b (associatedBundleMk G P Y u.1 u.2) =
          (projection u.1, (S.trivialization b u.1).2 • u.2) :=
        (exists_associatedBundleTrivialization (F := Y) S.toIsPrincipalBundle
          (S.trivialization b) (S.equivariant b)).choose_spec.2.1 u.1 u.2 hpc
      change e (associatedBundleMk G P Y u.1 u.2) = _
      rw [he]
      change associatedSphereCotangentRepresentative S u.1 u.2 =
        H b (tc b (associatedBundleMk G P Y u.1 u.2))
      rw [hcoord]
      exact (local_formula b u.1 u.2 (hbase b ▸ hp)).symm
  have hc : Continuous e := by
    apply continuous_iff_continuousAt.mpr
    intro x
    let b := associatedBundleProjection (F := Y) S.toIsPrincipalBundle x
    have hx : x ∈ (tc b).source := (tc b).mem_source.mpr (by
      change b ∈ (tc b).baseSet
      rw [hbase, hprincipal]
      exact S.mem_baseSet b)
    have htx : (tc b x).1 ∈ (ts b).baseSet := by
      rw [(tc b).coe_fst hx, ← hbase]
      exact (tc b).mem_source.mp hx
    have hloc := (local_forward_continuous b (tc b x) htx).comp
      ((tc b).toOpenPartialHomeomorph.continuousAt hx)
    apply hloc.congr_of_eventuallyEq
    filter_upwards [(tc b).open_source.mem_nhds hx] with x' hx'
    exact heOn b x' hx'
  have hi : Continuous e.symm := by
    apply continuous_iff_continuousAt.mpr
    intro w
    let b := q w.proj
    let t := ts b
    have hw : w.proj ∈ t.source := t.mem_source.mpr (by
      change b ∈ t.baseSet
      rw [hprincipal]
      exact S.mem_baseSet b)
    have ht : t.toOpenPartialHomeomorph.MDifferentiable I J := by
      have hs := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
      exact ⟨hs.1.mdifferentiableOn (by simp), hs.2.mdifferentiableOn (by simp)⟩
    have hproj (z : Z) (hz : z ∈ t.source) (v : TangentSpace I z) :
        ((ht.mfderiv hz) v).1 = mfderiv I 𝓘(ℝ, E) q z v := by
      have heq : (fun z' ↦ (t z').1) =ᶠ[𝓝 z] (q : Z → B) := by
        filter_upwards [t.open_source.mem_nhds hz] with z' hz'
        exact t.coe_fst hz'
      have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, E))
      have hc := mfderiv_comp z (mdifferentiableAt_fst (I := 𝓘(ℝ, E))
        (I' := 𝓡 r)) (ht.mdifferentiableAt hz)
      rw [mfderiv_fst] at hc
      change mfderiv I 𝓘(ℝ, E) (Prod.fst ∘ t.toOpenPartialHomeomorph) z = _ at hd
      rw [hc] at hd
      exact congrArg (fun A ↦ A v) hd
    let k (z : Z) : R →L[ℝ] K z :=
      if hz : z ∈ t.source then
        ((ht.mfderiv hz).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ E R)).codRestrict
          (LinearMap.ker (mfderiv I 𝓘(ℝ, E) q z).toLinearMap) (by
            intro v
            change mfderiv I 𝓘(ℝ, E) q z ((ht.mfderiv hz).symm (0, v)) = 0
            rw [← hproj z hz, (ht.mfderiv hz).apply_symm_apply])
      else 0
    have hk (z : Z) (hz : z ∈ t.source) (v : R) :
        (k z v).val = mfderiv J I t.toOpenPartialHomeomorph.symm (t z) (0, v) := by
      simp only [k, dite_eq_left hz]
      rfl
    let back : T → B × Y := fun w ↦
      ((t w.proj).1, ⟨(t w.proj).2, w.snd.comp (k w.proj)⟩)
    have hback : ContinuousAt back w := local_inverse_continuous b k hk w hw
    have htarget (w : T) (hw : w.proj ∈ t.source) : back w ∈ (tc b).target := by
      apply (tc b).mem_target.mpr
      change (t w.proj).1 ∈ (tc b).baseSet
      rw [hbase]
      exact t.mem_target.mp (t.map_source hw)
    have hround (w : T) (hw : w.proj ∈ t.source) : H b (back w) = w := by
      have covector_ext {z z' : Z} (h : z = z')
          (α : K z →L[ℝ] ℝ) (β : K z' →L[ℝ] ℝ)
          (heq : ∀ v hv hv', α ⟨v, hv⟩ = β ⟨v, hv'⟩) :
          (⟨z, α⟩ : T) = ⟨z', β⟩ := by
        subst z'
        congr 1
        ext v
        exact heq v.val v.property v.property
      have hb : t.toOpenPartialHomeomorph.symm (t w.proj) = w.proj :=
        t.toOpenPartialHomeomorph.left_inv hw
      apply covector_ext hb
      intro v hv hv'
      change w.snd (k w.proj
        (mfderiv I J t (t.toOpenPartialHomeomorph.symm (t w.proj)) v).2) = w.snd ⟨v, hv'⟩
      rw [hb]
      congr 1
      apply Subtype.ext
      rw [hk w.proj hw]
      let L := ht.mfderiv hw
      change L.symm (0, (L v).2) = v
      have hvL : L v = (0, (L v).2) := by
        apply Prod.ext
        · exact (hproj w.proj hw v).trans hv'
        · rfl
      rw [← hvL, L.symm_apply_apply]
    have hinv (w : T) (hw : w.proj ∈ t.source) :
        e.symm w = (tc b).toOpenPartialHomeomorph.symm (back w) := by
      apply e.injective
      rw [e.apply_symm_apply]
      have hy := htarget w hw
      rw [heOn b _ ((tc b).toOpenPartialHomeomorph.symm.map_source hy)]
      exact (hround w hw).symm.trans
        (congrArg (H b) ((tc b).toOpenPartialHomeomorph.right_inv hy)).symm
    have hloc := ((tc b).toOpenPartialHomeomorph.continuousAt_symm (htarget w hw)).comp hback
    apply hloc.congr_of_eventuallyEq
    filter_upwards [(FiberBundle.continuous_proj (V →L[ℝ] ℝ) W).continuousAt.preimage_mem_nhds
      (t.open_source.mem_nhds hw)] with w' hw'
    exact hinv w' hw'
  exact ⟨{ toEquiv := e, continuous_toFun := hc, continuous_invFun := hi }, he⟩

/-- The canonical homeomorphism with the exact original representative formula. -/
def associatedSphereVerticalCotangentHomeomorph :
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := verticalTangentFiberBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    letI := verticalTangentVectorBundle (smoothAssociatedSphereProjection S)
      (associatedSphereProjection_isSubmersion S)
    AssociatedBundle G P (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) ≃ₜ
      TotalSpace (V →L[ℝ] ℝ) W :=
  (exists_associatedSphereVerticalCotangentHomeomorph S).choose

end AtiyahSinger
