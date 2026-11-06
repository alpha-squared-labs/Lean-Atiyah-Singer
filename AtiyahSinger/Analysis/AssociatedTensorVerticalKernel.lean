/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorFiberRestriction
public import AtiyahSinger.Geometry.AssociatedTensorSectionSmoothness
public import AtiyahSinger.Geometry.TensorSectionKernel

/-!
# The full associated vertical kernel with a fixed base coefficient

Public module ID: M0205.

Apply the supplied sphere operator to every whole-fiber restriction, leaving
the base bundle coefficient fixed. Given finite equivariant coordinates for
its full kernel, the kernel of this family operator is linearly equivalent to
smooth sections of the base bundle tensored with the associated kernel
representation. The equivalence retains the supplied coordinates and exact
base-first tensor evaluation at every associated point.

Source: the vertical-kernel step in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)]
  [∀ y, Module ℂ (F' y)] [TopologicalSpace (TotalSpace Unit F')]
  (A' : SmoothComplexBundleAtlas (n := r) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z


set_option maxSynthPendingDepth 30 in
/-- Apply the original operator on every entire sphere fiber, with the base coefficient fixed. -/
def associatedSphereTensorVerticalFamilyOperator (L : A.smoothSections →ₗ[ℂ] A'.smoothSections) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
      ∀ p : P, dualTensorSections (E (projection p)) A'.smoothSections := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  exact LinearMap.pi fun p ↦ by
    let : FiniteDimensional ℂ (E (projection p)) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E (projection p)
    exact (tensorSectionOperator (E (projection p)) A.smoothSections A'.smoothSections L).comp
      (associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p)

variable (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "K" => fun b : B ↦ E b ⊗[ℂ] C b

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full vertical kernel is linearly equivalent to the smooth tensor coefficient sections. -/
theorem exists_associatedSphereTensorVerticalKernelEquiv
    (L : A.smoothSections →ₗ[ℂ] A'.smoothSections) (e : V ≃ₗ[ℂ] L.ker)
    (he : ∀ (g : G) (y : OrthogonalSphere r) (v : V),
      (e (ρ.representation g v)).val.val (g • y) =
        σ.linearMap g y ((e v).val.val y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ ev : Hom ((q : Z → B) *ᵖ C) D,
      (∀ (p : P) (y : OrthogonalSphere r) (v : V),
        ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((e v).val.val y)) ∧
      ∃ Φ : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
          (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections ≃ₗ[ℂ]
          (associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' L).ker,
        ∀ u z, (Φ u).val.val z =
          TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (q z)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let (b : B) : FiniteDimensional ℂ (E b) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E b
  let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
    (associatedOrthogonalRepresentationAtlas S ρ)
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  let TOp := associatedSphereTensorVerticalFamilyOperator (a := a) S E A σ hσ A' L
  let s : V →ₗ[ℂ] A.smoothSections := L.ker.subtype.comp e.toLinearMap
  have hs : Function.Injective s := Subtype.val_injective.comp e.injective
  obtain ⟨ev, hev, _, _⟩ := exists_associatedSectionEvaluation S.toIsPrincipalBundle A σ ρ s he
  let f (u : ∀ b, K b) (z : Z) : T z :=
    TensorProduct.map LinearMap.id (ev.linearMap z) (u (q z))
  let ec (p : P) : E (projection p) ⊗[ℂ] V ≃ₗ[ℂ] K (projection p) :=
    TensorProduct.congr (LinearEquiv.refl ℂ (E (projection p)))
      (LinearEquiv.ofBijective
        (associatedVectorFiberMk_isLinear S.toIsPrincipalBundle ρ.representation p rfl).mk'
        (associatedVectorFiberMk_bijective S.toIsPrincipalBundle ρ.representation p rfl))
  -- Tensor evaluation uses precisely the supplied finite kernel coordinates in each whole fiber.
  have hvalue (p : P) (t : E (projection p) ⊗[ℂ] V) (y : OrthogonalSphere r) :
      TensorProduct.map LinearMap.id
          (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)) (ec p t) =
        associatedSphereTensorFiberEquiv S E σ p y
          ((tensorSectionEquiv (E (projection p)) A.smoothSections
            ((s.lTensor (E (projection p))) t)).val y) := by
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      change u ⊗ₜ[ℂ] ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        u ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y)
      rw [hev]
    | add t t' ht ht' =>
      simpa only [map_add, Submodule.coe_add, Pi.add_apply] using congrArg₂ (· + ·) ht ht'
  have hinjFiber (p : P) : Function.Injective (fun v : K (projection p) ↦
      fun y : OrthogonalSphere r ↦ TensorProduct.map LinearMap.id
        (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)) v) := by
    intro u v huv
    obtain ⟨t, rfl⟩ := (ec p).surjective u
    obtain ⟨t', rfl⟩ := (ec p).surjective v
    apply congrArg (ec p)
    apply Module.Flat.lTensor_preserves_injective_linearMap s hs
    apply (tensorSectionEquiv (E (projection p)) A.smoothSections).injective
    apply Subtype.ext
    funext y
    apply (associatedSphereTensorFiberEquiv S E σ p y).injective
    rw [← hvalue, ← hvalue]
    exact congrFun huv y
  have hinj : Function.Injective f := by
    intro u v huv
    funext b
    let p := (S.trivialization b).toPartialEquiv.symm (b, 1)
    have hp : projection p = b := (S.trivialization b).proj_symm_apply' (S.mem_baseSet b)
    have hAt (b' : B) (hp' : projection p = b') : u b' = v b' := by
      subst b'
      apply hinjFiber p
      funext y
      exact congrFun huv (associatedBundleMk G P (OrthogonalSphere r) p y)
    exact hAt b hp
  let F : AC.smoothSections →ₗ[ℂ] AT.smoothSections :=
    { toFun u := ⟨f u.val, (isSmoothSection_associatedTensorEvaluation_iff
        S E A σ hσ ρ s hs ev hev u.val).mpr u.property⟩
      map_add' u v := by
        apply Subtype.ext
        funext z
        exact map_add _ _ _
      map_smul' c u := by
        apply Subtype.ext
        funext z
        change TensorProduct.map LinearMap.id (ev.linearMap z) (c • u.val (q z)) =
          c • TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (q z))
        exact map_smul _ _ _ }
  have hmem (u : AC.smoothSections) : TOp (F u) = 0 := by
    funext p
    obtain ⟨t, ht⟩ := (ec p).surjective (u.val (projection p))
    have hR : R p (F u) = tensorSectionEquiv (E (projection p)) A.smoothSections
        ((s.lTensor (E (projection p))) t) := by
      apply Subtype.ext
      funext y
      apply (associatedSphereTensorFiberEquiv S E σ p y).injective
      rw [associatedSphereTensorFiberRestriction_apply]
      change TensorProduct.map LinearMap.id
        (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y))
          (u.val (projection p)) = _
      rw [← ht]
      exact hvalue p t y
    have hzero : L.comp s = 0 := by
      apply LinearMap.ext
      intro v
      exact (e v).property
    have htzero : (L.lTensor (E (projection p))) ((s.lTensor (E (projection p))) t) = 0 := by
      change ((L.lTensor (E (projection p))).comp (s.lTensor (E (projection p)))) t = 0
      rw [← LinearMap.lTensor_comp, hzero, LinearMap.lTensor_zero, LinearMap.zero_apply]
    change tensorSectionOperator (E (projection p)) A.smoothSections A'.smoothSections L
      (R p (F u)) = 0
    rw [hR]
    simp only [tensorSectionOperator, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, htzero, map_zero]
  have hlocal (w : AT.smoothSections) (hw : TOp w = 0) (p : P) :
      ∃ c : K (projection p), ∀ y : OrthogonalSphere r,
        TensorProduct.map LinearMap.id
            (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)) c =
          w.val (associatedBundleMk G P (OrthogonalSphere r) p y) := by
    obtain ⟨ek, hek⟩ := exists_tensorSectionKernelEquiv
      (E (projection p)) A.smoothSections A'.smoothSections L
    let wK : (tensorSectionOperator (E (projection p))
        A.smoothSections A'.smoothSections L).ker := ⟨R p w, congrFun hw p⟩
    let tk := ek.symm wK
    let et := TensorProduct.congr (LinearEquiv.refl ℂ (E (projection p))) e
    let t := et.symm tk
    have ht : (s.lTensor (E (projection p))) t =
        (L.ker.subtype.lTensor (E (projection p))) tk := by
      dsimp only [s]
      rw [LinearMap.lTensor_comp_apply]
      change (L.ker.subtype.lTensor (E (projection p))) (et (et.symm tk)) = _
      rw [et.apply_symm_apply]
    have hvalues : (tensorSectionEquiv (E (projection p)) A.smoothSections
        ((L.ker.subtype.lTensor (E (projection p))) tk)).val = (R p w).val :=
      (hek tk).symm.trans (congrArg (fun v ↦ v.val.val) (ek.apply_symm_apply wK))
    refine ⟨ec p t, ?_⟩
    intro y
    rw [hvalue, ht, hvalues]
    exact associatedSphereTensorFiberRestriction_apply (a := a) S E A σ hσ p w y
  have hglobal (w : AT.smoothSections) (hw : TOp w = 0) :
      ∃ u : AC.smoothSections, F u = w := by
    let p (b : B) := (S.trivialization b).toPartialEquiv.symm (b, 1)
    have hp (b : B) : projection (p b) = b :=
      (S.trivialization b).proj_symm_apply' (S.mem_baseSet b)
    let c (b : B) := (hlocal w hw (p b)).choose
    have hc (b : B) := (hlocal w hw (p b)).choose_spec
    let transport : ∀ {b b' : B}, b = b' → K b ≃ₗ[ℂ] K b' := fun {b b'} h ↦ by
      subst b'
      exact LinearEquiv.refl ℂ (K b)
    let u (b : B) : K b := transport (hp b) (c b)
    have heq (z : Z) : f u z = w.val z := by
      obtain ⟨⟨p', y'⟩, hrep⟩ := Quotient.exists_rep z
      have hp' : projection p' = q z := congrArg q hrep
      obtain ⟨g, hg, _⟩ := S.toIsPrincipalBundle.existsUnique_smul
        (p (q z)) p' ((hp (q z)).trans hp'.symm)
      let y := g • y'
      have hz : associatedBundleMk G P (OrthogonalSphere r) (p (q z)) y = z :=
        (associatedBundleMk_smul (p (q z)) g y').symm.trans
          ((congrArg (fun p' ↦ associatedBundleMk G P (OrthogonalSphere r) p' y') hg).trans
            hrep)
      have hformula (z' : Z)
          (hz' : associatedBundleMk G P (OrthogonalSphere r) (p (q z)) y = z')
          (hpz : projection (p (q z)) = q z') :
          TensorProduct.map LinearMap.id (ev.linearMap z') (transport hpz (c (q z))) =
            w.val z' := by
        subst z'
        exact hc (q z) y
      exact hformula z hz (hp (q z))
    have hu : AC.IsSmoothSection u := by
      apply (isSmoothSection_associatedTensorEvaluation_iff S E A σ hσ ρ s hs ev hev u).mp
      have hfu : f u = w.val := funext heq
      change AT.IsSmoothSection (f u)
      rw [hfu]
      exact w.property
    exact ⟨⟨u, hu⟩, Subtype.ext (funext heq)⟩
  let Φ : AC.smoothSections →ₗ[ℂ] TOp.ker :=
    { toFun u := ⟨F u, hmem u⟩
      map_add' u v := Subtype.ext (F.map_add u v)
      map_smul' c u := Subtype.ext (F.map_smul c u) }
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro u v huv
      apply Subtype.ext
      apply hinj
      exact congrArg (fun w : TOp.ker ↦ w.val.val) huv
    · intro w
      obtain ⟨u, hu⟩ := hglobal w.val w.property
      exact ⟨u, Subtype.ext hu⟩
  exact ⟨ev, hev, LinearEquiv.ofBijective Φ hΦ, fun _ _ ↦ rfl⟩

end AtiyahSinger
