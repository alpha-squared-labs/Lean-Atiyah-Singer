/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseExtensionValue
public import AtiyahSinger.Analysis.AssociatedTensorSupportedHorizontalLift
public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Analysis.TensorSectionFormalAdjoint
public import AtiyahSinger.Geometry.AssociatedProductMeasureLocalIntegral
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Complete horizontal adjunction in the associated tensor bundle

Public module ID: M0166.

Given native PDOs in integral adjunction with a common output support,
their supplied normalized base-family lifts satisfy integral adjunction
in the associated tensor bundle. A common base plateau reduces the tensor
pairings to the native identity. The associated product measure and local
Fubini formula integrate over the base and then the sphere. The conclusion
uses whole-sphere families and complete operators on smooth sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

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

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable {a' : ℕ} [T2Space B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable [IsFiniteMeasure μ]
  [MeasurableSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2000000 in
-- Integrate the same supported horizontal lifts while retaining the original adjunction.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same supported horizontal lifts preserve the complete original native adjunction. -/
theorem associatedSphereTensorSupportedHorizontalLift_integral_adjoint {m : ℝ}
    (Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m)
    (J : PseudodifferentialOperator (n := n) (r := a') (q := a) E' E μ m)
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (h' : SmoothHermitianMetric (n := n) (r := a') E')
    (hAdj : ∀ (u : smoothSections (n := n) (r := a) E)
      (v : smoothSections (n := n) (r := a') E'),
      (∫ x, h'.pairing x ((Q.toLinearMap u).val x) (v.val x) ∂μ) =
        ∫ x, h.pairing x (u.val x) ((J.toLinearMap v).val x) ∂μ)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (ν : Measure (OrthogonalSphere r)) [IsFiniteMeasure ν]
    (hν : ∀ g : G, Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)
    (k : ∀ y, InnerProductSpace.Core ℂ (F y))
    (b : B) (K : Set B) (hKb : K ⊆ (S.trivialization b).baseSet)
    (β : B → ℝ) (hβ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ β)
    (hβsupport : tsupport β ⊆ (S.trivialization b).baseSet)
    (hβone : ∀ x ∈ K, β x = 1)
    (hQ : ∀ (u : smoothSections (n := n) (r := a) E) (x : B),
      x ∉ K → (Q.toLinearMap u).val x = 0)
    (hJ : ∀ (u : smoothSections (n := n) (r := a') E') (x : B),
      x ∉ K → (J.toLinearMap u).val x = 0) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
      .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
        (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
    let R :=
      associatedSphereTensorCutoffBaseRestriction (a := a) S E A σ hσ b β hβ hβsupport
    let R' :=
      associatedSphereTensorCutoffBaseRestriction (a := a') S E' A σ hσ b β hβ hβsupport
    let V := fun y ↦
      tensorSectionOperator (F y) (smoothSections E) (smoothSections E') Q.toLinearMap
    let V' := fun y ↦
      tensorSectionOperator (F y) (smoothSections E') (smoothSections E) J.toLinearMap
    ∀ (H : AT.smoothSections →ₗ[ℂ] AT'.smoothSections)
      (H' : AT'.smoothSections →ₗ[ℂ] AT.smoothSections),
      (∀ w z, (H w).val z = associatedSphereTensorBaseExtension S E' σ b
        (fun y x ↦ (V y (R y w)).val x) z) →
      (∀ w z, (H' w).val z = associatedSphereTensorBaseExtension S E σ b
        (fun y x ↦ (V' y (R' y w)).val x) z) →
      ∀ (l : ContinuousHermitianMetric T) (l' : ContinuousHermitianMetric T'),
        AT.IsSmoothHermitianMetric l → AT'.IsSmoothHermitianMetric l' →
        (∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F y),
          (l.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
              (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
            h.pairing (projection p) u v * (k y).inner s t) →
        (∀ (p : P) (y : OrthogonalSphere r) (u v : E' (projection p)) (s t : F y),
          (l'.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
              (associatedSphereTensorFiberEquiv S E' σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E' σ p y (v ⊗ₜ[ℂ] t)) =
            h'.pairing (projection p) u v * (k y).inner s t) →
        ∀ (s : AT.smoothSections) (t : AT'.smoothSections),
          (∫ z, (l'.toCore z).inner ((H s).val z) (t.val z)
            ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
          ∫ z, (l.toCore z).inner (s.val z) ((H' t).val z)
            ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let := linearModelChartedSpace lm Z
  let := isManifold_linearModelChartedSpace lm Z
  let (y : OrthogonalSphere r) : FiniteDimensional ℂ (F y) :=
    .of_injective (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).toLinearMap
      (A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec).injective
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let R :=
      associatedSphereTensorCutoffBaseRestriction (a := a) S E A σ hσ b β hβ hβsupport
  let R' :=
      associatedSphereTensorCutoffBaseRestriction (a := a') S E' A σ hσ b β hβ hβsupport
  let V := fun y ↦
      tensorSectionOperator (F y) (smoothSections E) (smoothSections E') Q.toLinearMap
  let V' := fun y ↦
      tensorSectionOperator (F y) (smoothSections E') (smoothSections E) J.toLinearMap
  dsimp only
  intro H H' hH hH' l l' hl hl' hpair hpair' s t
  let e (p : P) (y : OrthogonalSphere r) :=
    (TensorProduct.comm ℂ (F y) (E (projection p))).trans
      (associatedSphereTensorFiberEquiv S E σ p y)
  let e' (p : P) (y : OrthogonalSphere r) :=
    (TensorProduct.comm ℂ (F y) (E' (projection p))).trans
      (associatedSphereTensorFiberEquiv S E' σ p y)
  -- Positive tensor cores use only the specified factor pairings; bundle norms stay unchanged.
  let c (y : OrthogonalSphere r) (x : B) :
      InnerProductSpace.Core ℂ (F y ⊗[ℂ] E x) := by
    let cf := k y
    let ce := h.toCore x
    let mf : Module ℂ (F y) := inferInstance
    let me : Module ℂ (E x) := inferInstance
    let : NormedAddCommGroup (F y) := cf.toNormedAddCommGroup
    let : Module ℂ (F y) := mf
    let : InnerProductSpace ℂ (F y) := InnerProductSpace.ofCore cf.toCore
    let : NormedAddCommGroup (E x) := ce.toNormedAddCommGroup
    let : Module ℂ (E x) := me
    let : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore ce.toCore
    let : NormedAddCommGroup (F y ⊗[ℂ] E x) := TensorProduct.instNormedAddCommGroup
    let : InnerProductSpace ℂ (F y ⊗[ℂ] E x) := TensorProduct.instInnerProductSpace
    exact InnerProductSpace.toCore (𝕜 := ℂ) (E := F y ⊗[ℂ] E x)
  let c' (y : OrthogonalSphere r) (x : B) :
      InnerProductSpace.Core ℂ (F y ⊗[ℂ] E' x) := by
    let cf := k y
    let ce := h'.toCore x
    let mf : Module ℂ (F y) := inferInstance
    let me : Module ℂ (E' x) := inferInstance
    let : NormedAddCommGroup (F y) := cf.toNormedAddCommGroup
    let : Module ℂ (F y) := mf
    let : InnerProductSpace ℂ (F y) := InnerProductSpace.ofCore cf.toCore
    let : NormedAddCommGroup (E' x) := ce.toNormedAddCommGroup
    let : Module ℂ (E' x) := me
    let : InnerProductSpace ℂ (E' x) := InnerProductSpace.ofCore ce.toCore
    let : NormedAddCommGroup (F y ⊗[ℂ] E' x) := TensorProduct.instNormedAddCommGroup
    let : InnerProductSpace ℂ (F y ⊗[ℂ] E' x) := TensorProduct.instInnerProductSpace
    exact InnerProductSpace.toCore (𝕜 := ℂ) (E := F y ⊗[ℂ] E' x)
  have hpure (y : OrthogonalSphere r) (x : B) (u v : F y) (a b : E x) :
      (c y x).inner (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) = (k y).inner u v * h.pairing x a b := rfl
  have hpure' (y : OrthogonalSphere r) (x : B) (u v : F y) (a b : E' x) :
      (c' y x).inner (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] b) = (k y).inner u v * h'.pairing x a b := rfl
  -- The same associated tensor metric agrees with each core on all actual tensors.
  have hp (p : P) (y : OrthogonalSphere r) (u v : F y ⊗[ℂ] E (projection p)) :
      (l.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
        (e p y u) (e p y v) = (c y (projection p)).inner u v := by
    let z := associatedBundleMk G P (OrthogonalSphere r) p y
    have hr (u v w : F y ⊗[ℂ] E (projection p)) :
        (c y (projection p)).inner u (v + w) =
          (c y (projection p)).inner u v + (c y (projection p)).inner u w := by
      let := c y (projection p)
      exact InnerProductSpace.Core.inner_add_right u v w
    have hrl (u v w : T z) :
        (l.toCore z).inner u (v + w) =
          (l.toCore z).inner u v + (l.toCore z).inner u w := by
      let := l.toCore z
      exact InnerProductSpace.Core.inner_add_right u v w
    induction u using TensorProduct.inductionOn with
    | tmul a b =>
      induction v using TensorProduct.inductionOn with
      | tmul a' b' =>
        change (l.toCore _).inner
          (associatedSphereTensorFiberEquiv S E σ p y (b ⊗ₜ[ℂ] a))
          (associatedSphereTensorFiberEquiv S E σ p y (b' ⊗ₜ[ℂ] a')) = _
        rw [hpair, hpure, mul_comm]
      | add v w hv hw => simp only [map_add, hr, hrl, hv, hw]
    | add u v hu hv =>
      simp only [map_add, (l.toCore z).add_left, (c y (projection p)).add_left, hu, hv]
  have hp' (p : P) (y : OrthogonalSphere r) (u v : F y ⊗[ℂ] E' (projection p)) :
      (l'.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
        (e' p y u) (e' p y v) = (c' y (projection p)).inner u v := by
    let z := associatedBundleMk G P (OrthogonalSphere r) p y
    have hr (u v w : F y ⊗[ℂ] E' (projection p)) :
        (c' y (projection p)).inner u (v + w) =
          (c' y (projection p)).inner u v + (c' y (projection p)).inner u w := by
      let := c' y (projection p)
      exact InnerProductSpace.Core.inner_add_right u v w
    have hrl (u v w : T' z) :
        (l'.toCore z).inner u (v + w) =
          (l'.toCore z).inner u v + (l'.toCore z).inner u w := by
      let := l'.toCore z
      exact InnerProductSpace.Core.inner_add_right u v w
    induction u using TensorProduct.inductionOn with
    | tmul a b =>
      induction v using TensorProduct.inductionOn with
      | tmul a' b' =>
        change (l'.toCore _).inner
          (associatedSphereTensorFiberEquiv S E' σ p y (b ⊗ₜ[ℂ] a))
          (associatedSphereTensorFiberEquiv S E' σ p y (b' ⊗ₜ[ℂ] a')) = _
        rw [hpair', hpure', mul_comm]
      | add v w hv hw => simp only [map_add, hr, hrl, hv, hw]
    | add u v hu hv =>
      simp only [map_add, (l'.toCore z).add_left, (c' y (projection p)).add_left, hu, hv]
  have hn (p : P) (hp : projection p ∈ (S.trivialization b).baseSet)
      (hg : (S.trivialization b p).2 = 1) :
      (S.trivialization b).toOpenPartialHomeomorph.symm (projection p, 1) = p := by
    have hsource := (S.trivialization b).mem_source.mpr hp
    have hpair : (projection p, 1) = S.trivialization b p :=
      Prod.ext ((S.trivialization b).proj_toFun p hsource).symm hg.symm
    rw [hpair]
    exact (S.trivialization b).toOpenPartialHomeomorph.left_inv hsource
  -- Restriction and return use this exact normalized representative and inverse tensor map.
  have hres (p : P) (y : OrthogonalSphere r)
      (hpb : projection p ∈ (S.trivialization b).baseSet)
      (hg : (S.trivialization b p).2 = 1) (w : AT.smoothSections) :
      (R y w).val (projection p) =
        (β (projection p) : ℂ) • (e p y).symm
          (w.val (associatedBundleMk G P (OrthogonalSphere r) p y)) := by
    let transport : ∀ {x z : B}, x = z → E x ≃ₗ[ℂ] E z := fun {x z} h ↦ by
      subst z
      exact LinearEquiv.refl ℂ (E x)
    have hvalue (p' : P) (heq : projection p' = projection p) (hpp : p' = p) :
        TensorProduct.map (transport heq).toLinearMap LinearMap.id
          ((associatedSphereTensorFiberEquiv S E σ p' y).symm
            (w.val (associatedBundleMk G P (OrthogonalSphere r) p' y))) =
          (associatedSphereTensorFiberEquiv S E σ p y).symm
            (w.val (associatedBundleMk G P (OrthogonalSphere r) p y)) := by
      subst p'
      simp only [transport, LinearEquiv.refl_toLinearMap, TensorProduct.map_id, LinearMap.id_apply]
    change associatedSphereTensorCutoffBaseFamily (a := a)
      S E A σ hσ b β y w (projection p) = _
    simp only [associatedSphereTensorCutoffBaseFamily, LinearMap.pi_apply, dite_eq_left hpb,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
      Submodule.subtype_apply]
    apply congrArg (fun t ↦ (β (projection p) : ℂ) •
      TensorProduct.comm ℂ (E (projection p)) (F y) t)
    exact hvalue _ _ (hn p hpb hg)
  have hres' (p : P) (y : OrthogonalSphere r)
      (hpb : projection p ∈ (S.trivialization b).baseSet)
      (hg : (S.trivialization b p).2 = 1) (w : AT'.smoothSections) :
      (R' y w).val (projection p) =
        (β (projection p) : ℂ) • (e' p y).symm
          (w.val (associatedBundleMk G P (OrthogonalSphere r) p y)) := by
    let transport : ∀ {x z : B}, x = z → E' x ≃ₗ[ℂ] E' z := fun {x z} h ↦ by
      subst z
      exact LinearEquiv.refl ℂ (E' x)
    have hvalue (p' : P) (heq : projection p' = projection p) (hpp : p' = p) :
        TensorProduct.map (transport heq).toLinearMap LinearMap.id
          ((associatedSphereTensorFiberEquiv S E' σ p' y).symm
            (w.val (associatedBundleMk G P (OrthogonalSphere r) p' y))) =
          (associatedSphereTensorFiberEquiv S E' σ p y).symm
            (w.val (associatedBundleMk G P (OrthogonalSphere r) p y)) := by
      subst p'
      simp only [transport, LinearEquiv.refl_toLinearMap, TensorProduct.map_id, LinearMap.id_apply]
    change associatedSphereTensorCutoffBaseFamily (a := a')
      S E' A σ hσ b β y w (projection p) = _
    simp only [associatedSphereTensorCutoffBaseFamily, LinearMap.pi_apply, dite_eq_left hpb,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
      Submodule.subtype_apply]
    apply congrArg (fun t ↦ (β (projection p) : ℂ) •
      TensorProduct.comm ℂ (E' (projection p)) (F y) t)
    exact hvalue _ _ (hn p hpb hg)
  have hzero (y : OrthogonalSphere r) (x : B) (hx : x ∉ K)
      (w : dualTensorSections (F y) (smoothSections E)) : (V y w).val x = 0 := by
    obtain ⟨v, rfl⟩ := (tensorSectionEquiv (F y) (smoothSections E)).surjective w
    have hmap : V y (tensorSectionEquiv (F y) (smoothSections E) v) =
        tensorSectionEquiv (F y) (smoothSections E') ((Q.toLinearMap.lTensor (F y)) v) := by
      simp [V, tensorSectionOperator]
    rw [hmap, tensorSectionEquiv_apply]
    clear hmap
    induction v using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [LinearMap.lTensor_tmul, tensorSectionEvaluation_tmul,
        hQ v x hx, TensorProduct.tmul_zero]
    | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, add_zero]
  have hzero' (y : OrthogonalSphere r) (x : B) (hx : x ∉ K)
      (w : dualTensorSections (F y) (smoothSections E')) : (V' y w).val x = 0 := by
    obtain ⟨v, rfl⟩ := (tensorSectionEquiv (F y) (smoothSections E')).surjective w
    have hmap : V' y (tensorSectionEquiv (F y) (smoothSections E') v) =
        tensorSectionEquiv (F y) (smoothSections E) ((J.toLinearMap.lTensor (F y)) v) := by
      simp [V', tensorSectionOperator]
    rw [hmap, tensorSectionEquiv_apply]
    clear hmap
    induction v using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [LinearMap.lTensor_tmul, tensorSectionEvaluation_tmul,
        hJ v x hx, TensorProduct.tmul_zero]
    | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, add_zero]
  let f : C(Z, ℂ) := ⟨fun z ↦ (l'.toCore z).inner ((H s).val z) (t.val z),
    (AT'.contMDiff_pairing l' hl' (H s) t).continuous⟩
  let f' : C(Z, ℂ) := ⟨fun z ↦ (l.toCore z).inner (s.val z) ((H' t).val z),
    (AT.contMDiff_pairing l hl s (H' t)).continuous⟩
  have hbase : (associatedSphereTrivialization S b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hfs (z : Z) (hz : πS z ∉ (S.trivialization b).baseSet) : f z = 0 := by
    have hzs : z ∉ (associatedSphereTrivialization S b).source := by
      simpa only [Bundle.Trivialization.mem_source, hbase] using hz
    change (l'.toCore z).inner ((H s).val z) (t.val z) = 0
    rw [hH]
    simp only [associatedSphereTensorBaseExtension, LinearMap.pi_apply, dite_eq_right hzs,
      LinearMap.zero_apply]
    let := l'.toCore z
    exact InnerProductSpace.Core.inner_zero_left _
  have hfs' (z : Z) (hz : πS z ∉ (S.trivialization b).baseSet) : f' z = 0 := by
    have hzs : z ∉ (associatedSphereTrivialization S b).source := by
      simpa only [Bundle.Trivialization.mem_source, hbase] using hz
    change (l.toCore z).inner (s.val z) ((H' t).val z) = 0
    rw [hH']
    simp only [associatedSphereTensorBaseExtension, LinearMap.pi_apply, dite_eq_right hzs,
      LinearMap.zero_apply]
    let := l.toCore z
    exact InnerProductSpace.Core.inner_zero_right _
  change (∫ z, f z ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν) =
    ∫ z, f' z ∂associatedProductMeasure S.toIsPrincipalBundle μ ν hν
  -- The actual associated measure now integrates first on the original base in this chart.
  rw [integral_associatedProductMeasure_principal_chart S.toIsPrincipalBundle μ ν hν
    (S.trivialization b) f hfs,
    integral_associatedProductMeasure_principal_chart S.toIsPrincipalBundle μ ν hν
      (S.trivialization b) f' hfs']
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  have hleft (x : B) :
      (if x ∈ (S.trivialization b).baseSet then
        f (associatedBundleMk G P (OrthogonalSphere r)
          ((S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)) y) else 0) =
        (c' y x).inner ((V y (R y s)).val x) ((R' y t).val x) := by
    by_cases hx : x ∈ (S.trivialization b).baseSet
    · let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
      have hpx : projection p = x := (S.trivialization b).proj_symm_apply' hx
      have hg : (S.trivialization b p).2 = 1 :=
        congrArg Prod.snd ((S.trivialization b).apply_symm_apply' hx)
      have hpb : projection p ∈ (S.trivialization b).baseSet := hpx.symm ▸ hx
      rw [ite_eq_left hx]
      change f (associatedBundleMk G P (OrthogonalSphere r) p y) = _
      rw [← hpx]
      change (l'.toCore _).inner ((H s).val _) (t.val _) = _
      rw [hH, associatedSphereTensorBaseExtension_apply_mk S E' σ b p y hpb hg]
      change (l'.toCore _).inner (e' p y _) (t.val _) = _
      by_cases hxp : projection p ∈ K
      · rw [hres' p y hpb hg t, hβone _ hxp, Complex.ofReal_one, one_smul]
        have hh := hp' p y ((V y (R y s)).val (projection p))
          ((e' p y).symm (t.val (associatedBundleMk G P (OrthogonalSphere r) p y)))
        simpa only [LinearEquiv.apply_symm_apply] using hh
      · rw [hzero y _ hxp, map_zero]
        let := l'.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)
        let := c' y (projection p)
        rw [InnerProductSpace.Core.inner_zero_left, InnerProductSpace.Core.inner_zero_left]
    · rw [ite_eq_right hx, hzero y x (fun hk ↦ hx (hKb hk))]
      let := c' y x
      exact (InnerProductSpace.Core.inner_zero_left _).symm
  have hright' (x : B) :
      (if x ∈ (S.trivialization b).baseSet then
        f' (associatedBundleMk G P (OrthogonalSphere r)
          ((S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)) y) else 0) =
        (c y x).inner ((R y s).val x) ((V' y (R' y t)).val x) := by
    by_cases hx : x ∈ (S.trivialization b).baseSet
    · let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
      have hpx : projection p = x := (S.trivialization b).proj_symm_apply' hx
      have hg : (S.trivialization b p).2 = 1 :=
        congrArg Prod.snd ((S.trivialization b).apply_symm_apply' hx)
      have hpb : projection p ∈ (S.trivialization b).baseSet := hpx.symm ▸ hx
      rw [ite_eq_left hx]
      change f' (associatedBundleMk G P (OrthogonalSphere r) p y) = _
      rw [← hpx]
      change (l.toCore _).inner (s.val _) ((H' t).val _) = _
      rw [hH', associatedSphereTensorBaseExtension_apply_mk S E σ b p y hpb hg]
      change (l.toCore _).inner (s.val _) (e p y _) = _
      by_cases hxp : projection p ∈ K
      · rw [hres p y hpb hg s, hβone _ hxp, Complex.ofReal_one, one_smul]
        have hh := hp p y
          ((e p y).symm (s.val (associatedBundleMk G P (OrthogonalSphere r) p y)))
          ((V' y (R' y t)).val (projection p))
        simpa only [LinearEquiv.apply_symm_apply] using hh
      · rw [hzero' y _ hxp, map_zero]
        let := l.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)
        let := c y (projection p)
        rw [InnerProductSpace.Core.inner_zero_right, InnerProductSpace.Core.inner_zero_right]
    · rw [ite_eq_right hx, hzero' y x (fun hk ↦ hx (hKb hk))]
      let := c y x
      exact (InnerProductSpace.Core.inner_zero_right _).symm
  -- Finite tensor adjunction uses the original base metrics, density and complete Q/J maps.
  calc
    _ = ∫ x, (c' y x).inner ((V y (R y s)).val x) ((R' y t).val x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ x, (c y x).inner ((R y s).val x) ((V' y (R' y t)).val x) ∂μ :=
      tensorSectionOperator_integral_adjoint (F y) (smoothSections E) (smoothSections E')
        Q.toLinearMap J.toLinearMap μ (k y) h.toCore h'.toCore (c y) (c' y)
        (hpure y) (hpure' y) (h.integrable_pairing μ) (h'.integrable_pairing μ)
        hAdj (R y s) (R' y t)
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ (hright' x).symm))

end AtiyahSinger
