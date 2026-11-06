/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedVectorDescent
public import AtiyahSinger.Topology.HalfSpinorCharacterBasic
public import AtiyahSinger.Topology.PrincipalBundlePullback

/-!
# Pullback of the original associated half-spinor bundles

Public module ID: M1878.

The original even and odd spin representations commute with arbitrary
continuous principal pullback. The unique bundle comparison is characterized
on every original representative by [((x,p),v)] ↦ [p,v]. It retains the native
pullback topology and the original quotient-fiber operations on both sides.
One fixed finite coordinate presentation is used in both descents; the
representative formula removes that presentation from the resulting map.

The same comparison gives the degreewise Chern character of the half-spinor
difference for any specified continuous Hermitian metrics. The principal
bundle is exactly the one used by TopologicalSpinStructure.pullback; no new
spin frame or principal lift is selected. All m, including zero, are allowed.
No compactness, separation or properness condition is imposed.

Source: SG II.3, associated spinor bundles, and the standard naturality of
associated bundles. The explicit quotient and native-topology comparison is
a project supplement connecting the original models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

universe u v w

section BundleComparison

variable (m : ℕ) {B : Type u} {P : Type v} {X : Type w}
  [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace X]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection]

set_option maxHeartbeats 800000 in
-- The two descents retain the original quotient instances on three related bundle models.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Half-spinor pullback is the unique isomorphism retaining every original representative. -/
theorem existsUnique_halfSpinorBundle_pullback_iso (f : C(X, B)) (i : ZMod 2) :
    let hQ := isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
      (projection := projection) f
    ∃! e : ComplexBundle.Iso (HalfSpinorBundle m hQ i)
        ((f : X → B) *ᵖ (HalfSpinorBundle m hP i)),
      ∀ (x : X) (q : PrincipalBundlePullback f projection)
        (hx : principalBundlePullbackProjection f projection q = x)
        (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i),
        e.linearEquiv x
            (associatedVectorFiberMk hQ (complexSpinParityContRepresentation m i) q hx s) =
          associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) q.val.2
            (q.property.symm.trans (congrArg f hx)) s := by
  classical
  let G := spinGroup (realSpinorQuadraticForm m)
  let Q := PrincipalBundlePullback f projection
  let hQ := isPrincipalBundle_pullback (G := G) (projection := projection) f
  let V := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let ρ : ContRepresentation ℂ G V := complexSpinParityContRepresentation m i
  let A := HalfSpinorBundle m hQ i
  let E := HalfSpinorBundle m hP i
  let := associatedRepresentationAction ρ
  let := isFiniteRank_associatedVector hP ρ (continuous_complexSpinParityRepresentation m i)
  let := isFiniteRank_associatedVector hQ ρ (continuous_complexSpinParityRepresentation m i)
  let := ComplexBundle.isFiniteRank_pullback (E := E) f
  -- Fix one coordinate presentation of the original parity space for both descents.
  let n := Module.finrank ℂ V
  let c : V ≃L[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv
  let σ := FiniteContinuousRepresentation.ofEquiv ρ
    (continuous_complexSpinParityRepresentation m i) c
  have hcoord (g : G) (s : Fin n → ℂ) :
      c.symm (σ.representation g s) = ρ g (c.symm s) := by
    change c.symm (c (ρ g (c.symm s))) = _
    exact c.symm_apply_apply _
  let cQ (x : X) (q : Q) (hx : principalBundlePullbackProjection f projection q = x) :
      (Fin n → ℂ) ≃ₗ[ℂ] A x :=
    c.symm.toLinearEquiv.trans (associatedVectorFiberMkLinearEquiv hQ ρ q hx)
  have hcQ : Continuous (fun z : Q × (Fin n → ℂ) ↦
      (⟨z.1.val.1, cQ z.1.val.1 z.1 rfl z.2⟩ : TotalSpace Unit A)) :=
    ((associatedVectorTotalHomeomorph hQ ρ).symm.continuous.comp continuous_quot_mk).comp
      (continuous_fst.prodMk (c.symm.continuous.comp continuous_snd))
  have hcovQ (x : X) (q : Q) (hx : principalBundlePullbackProjection f projection q = x)
      (g : G) (s : Fin n → ℂ) :
      cQ x (MulOpposite.op g • q) ((hQ.projection_smul g q).trans hx) s =
        cQ x q hx (σ.representation g s) := by
    change associatedVectorFiberMk hQ ρ (MulOpposite.op g • q) _ (c.symm s) =
      associatedVectorFiberMk hQ ρ q hx (c.symm (σ.representation g s))
    rw [hcoord]
    apply Subtype.ext
    exact associatedBundleMk_smul q g (c.symm s)
  obtain ⟨a, ha⟩ := exists_associatedVector_iso_of_covariant_equiv hQ σ A cQ hcQ hcovQ
  -- The second descent retains x and maps its same principal representative to [p,v].
  let cP (x : X) (q : Q) (hx : principalBundlePullbackProjection f projection q = x) :
      (Fin n → ℂ) ≃ₗ[ℂ] E (f x) :=
    c.symm.toLinearEquiv.trans (associatedVectorFiberMkLinearEquiv hP ρ q.val.2
      (q.property.symm.trans (congrArg f hx)))
  let H := associatedVectorTotalHomeomorph hP ρ
  have hcP : Continuous (fun z : Q × (Fin n → ℂ) ↦
      (⟨z.1.val.1, cP z.1.val.1 z.1 rfl z.2⟩ :
        TotalSpace Unit ((f : X → B) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    apply continuous_fst.subtype_val.fst.prodMk
    have h : Continuous (fun z : Q × (Fin n → ℂ) ↦
        H.symm (associatedBundleMk G P V z.1.val.2 (c.symm z.2))) :=
      H.symm.continuous.comp (continuous_quot_mk.comp
        (continuous_fst.subtype_val.snd.prodMk (c.symm.continuous.comp continuous_snd)))
    apply h.congr
    intro z
    apply H.injective
    exact H.apply_symm_apply _
  have hcovP (x : X) (q : Q) (hx : principalBundlePullbackProjection f projection q = x)
      (g : G) (s : Fin n → ℂ) :
      cP x (MulOpposite.op g • q) ((hQ.projection_smul g q).trans hx) s =
        cP x q hx (σ.representation g s) := by
    change associatedVectorFiberMk hP ρ (MulOpposite.op g • q.val.2) _ (c.symm s) =
      associatedVectorFiberMk hP ρ q.val.2 _ (c.symm (σ.representation g s))
    rw [hcoord]
    apply Subtype.ext
    exact associatedBundleMk_smul q.val.2 g (c.symm s)
  obtain ⟨b, hb⟩ := exists_associatedVector_iso_of_covariant_equiv hQ σ
    ((f : X → B) *ᵖ E) cP hcP hcovP
  let e : ComplexBundle.Iso A ((f : X → B) *ᵖ E) := a.symm.trans b
  -- Composing the two descents removes the auxiliary coordinates from every actual vector.
  have he (x : X) (q : Q) (hx : principalBundlePullbackProjection f projection q = x)
      (s : V) : e.linearEquiv x (associatedVectorFiberMk hQ ρ q hx s) =
        associatedVectorFiberMk hP ρ q.val.2 (q.property.symm.trans (congrArg f hx)) s := by
    have hA : a.linearEquiv x (associatedVectorFiberMk hQ σ.representation q hx (c s)) =
        associatedVectorFiberMk hQ ρ q hx s := by
      rw [ha]
      change associatedVectorFiberMk hQ ρ q hx (c.symm (c s)) = _
      rw [c.symm_apply_apply]
    change b.linearEquiv x ((a.linearEquiv x).symm _) = _
    rw [← hA, LinearEquiv.symm_apply_apply, hb]
    change associatedVectorFiberMk hP ρ q.val.2 _ (c.symm (c s)) = _
    rw [c.symm_apply_apply]
  refine ⟨e, he, ?_⟩
  intro d hd
  apply ComplexBundle.Iso.ext
  intro x
  apply LinearEquiv.ext
  intro s
  -- Every vector has a representative at an actual principal point over this same x.
  obtain ⟨q, hq⟩ := hQ.projection_properties.2.2 x
  obtain ⟨v, hv⟩ := (associatedVectorFiberMk_bijective hQ ρ q hq).2 s
  rw [← hv]
  exact (hd x q hq v).trans (he x q hq v).symm

end BundleComparison

section Character

variable (m : ℕ) {B X : Type u} {P : Type v}
  [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace X]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original half-spinor character difference is natural for the same principal pullback. -/
theorem halfSpinorCharacterComponent_pullback (f : C(X, B))
    (hPlus : ContinuousHermitianMetric (HalfSpinorBundle m hP 0))
    (hMinus : ContinuousHermitianMetric (HalfSpinorBundle m hP 1))
    (kPlus : ContinuousHermitianMetric (HalfSpinorBundle m
      (isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
        (projection := projection) f) 0))
    (kMinus : ContinuousHermitianMetric (HalfSpinorBundle m
      (isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
        (projection := projection) f) 1)) (k : ℕ) :
    halfSpinorCharacterComponent m
        (isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
          (projection := projection) f) kPlus kMinus k =
      singularCohomologyPullback ℚ f (2 * k)
        (halfSpinorCharacterComponent m hP hPlus hMinus k) := by
  let hQ := isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
    (projection := projection) f
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  let := isFiniteRank_associatedVector hQ (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hQ (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  -- The two comparisons use the same principal fiber product and the original parity actions.
  obtain ⟨ePlus, _, _⟩ := existsUnique_halfSpinorBundle_pullback_iso m (hP := hP) f 0
  obtain ⟨eMinus, _, _⟩ := existsUnique_halfSpinorBundle_pullback_iso m (hP := hP) f 1
  have hp := globalChernCharacterComponent_pullback (HalfSpinorBundle m hP 0) hPlus f
    (HalfSpinorBundle m hQ 0) kPlus ePlus k
  have hm := globalChernCharacterComponent_pullback (HalfSpinorBundle m hP 1) hMinus f
    (HalfSpinorBundle m hQ 1) kMinus eMinus k
  -- Naturality already allows independent specified metrics; preserve positive-minus-negative.
  change globalChernCharacterComponent (HalfSpinorBundle m hQ 0) kPlus k -
    globalChernCharacterComponent (HalfSpinorBundle m hQ 1) kMinus k =
      singularCohomologyPullback ℚ f (2 * k)
        (globalChernCharacterComponent (HalfSpinorBundle m hP 0) hPlus k -
          globalChernCharacterComponent (HalfSpinorBundle m hP 1) hMinus k)
  rw [hp, hm, map_sub]

end Character

end AtiyahSinger
