/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedKZero
public import AtiyahSinger.Topology.PrincipalBundlePullback

/-!
# Naturality of the associated-bundle K map

Public module ID: M1542.

The principal pullback is the original fiber-product subtype with its specified
action and projection. Its associated vector bundle is compared with pullback
of the original associated vector bundle by [((x,p),v)] -> (x,[p,v]). Both K
classes and the resulting representation-to-K maps use these same objects.

Sources: HU IV.6 Proposition 6.3, printed p.47 / PDF p.68, for the canonical
associated pullback comparison; SG III.13 (13.17), p.252 / PDF p.264, for a_P.
The K-theoretic naturality statement is their standard consequence, not an
additional numbered lemma in those passages. Compact Hausdorffness of both
bases belongs to the current Serre--Swan K model. No compactness of G is used.
The proofs retain the original principal fiber product and associated quotient.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology

variable {G P X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → Y}
  [hP : IsPrincipalBundle G projection]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- The class associated to the actual principal pullback is the pullback of the original class. -/
theorem associatedKZeroClass_pullback (f : C(X, Y))
    (ρ : FiniteContinuousRepresentation G) :
    associatedKZeroClass (isPrincipalBundle_pullback (G := G) (projection := projection) f) ρ =
      complexKZeroPullback f (associatedKZeroClass hP ρ) := by
  /- Stage 1: install the action of this very representation rho on its finite
  model, with joint continuity from rho.continuous_action. The previously
  constructed associatedBundlePullbackHomeomorph sends [((x,p),v)] to (x,[p,v]).
  Realize this same representative formula using the covariant-coordinate descent
  theorem. Test its continuity against the original quotient total homeomorphism
  and native pullback topology. It preserves the base x.
  Stage 2: fix x and one original p over f(x). The representative map into
  each side is bijective and complex-linear, with the identical vector v.
  Therefore the same comparison is a linear isomorphism on the actual fibers,
  regardless of the independent algebraic coordinates used to define them.
  This makes it an isomorphism to the native pullback of the original vector
  bundle, with its original topology. No merely pointwise family of isomorphisms
  or assumption that arbitrary quotient maps are stable under pullback is used.
  Stage 3: apply kZeroClass_eq_of_iso, followed by kZeroClass_pullback. The latter
  uses the same continuous base map f and the same original associated bundle. -/
  let := associatedRepresentationAction ρ.representation
  let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
  let hQ := isPrincipalBundle_pullback (G := G) (projection := projection) f
  let := isFiniteRank_associatedVector hQ ρ.representation ρ.continuous_action
  let E := AssociatedVectorFiber hP ρ.representation
  let := ComplexBundle.isFiniteRank_pullback (E := E) f
  let H := associatedVectorTotalHomeomorph hP ρ.representation
  -- Each pullback principal point supplies the same original representative [p,v].
  let c (x : X) (q : PrincipalBundlePullback f projection)
      (hx : principalBundlePullbackProjection f projection q = x) :
      (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] E (f x) :=
    associatedVectorFiberMkLinearEquiv hP ρ.representation q.val.2
      (q.property.symm.trans (congrArg f hx))
  have hc : Continuous (fun z : PrincipalBundlePullback f projection ×
      (Fin ρ.dimension → ℂ) ↦
      (⟨z.1.val.1, c z.1.val.1 z.1 rfl z.2⟩ : TotalSpace Unit ((f : X → Y) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    apply continuous_fst.subtype_val.fst.prodMk
    have h : Continuous (fun z : PrincipalBundlePullback f projection ×
        (Fin ρ.dimension → ℂ) ↦ H.symm
        (associatedBundleMk G P (Fin ρ.dimension → ℂ) z.1.val.2 z.2)) :=
      H.symm.continuous.comp (continuous_quot_mk.comp
        (continuous_fst.subtype_val.snd.prodMk continuous_snd))
    apply h.congr
    intro z
    apply H.injective
    exact H.apply_symm_apply _
  obtain ⟨e, he⟩ := exists_associatedVector_iso_of_covariant_equiv hQ ρ
    ((f : X → Y) *ᵖ E) c hc (by
      intro x q hx g v
      apply Subtype.ext
      exact associatedBundleMk_smul q.val.2 g v)
  -- The descent formula he is exactly [((x,p),v)] mapped to (x,[p,v]).
  exact (ComplexBundle.kZeroClass_eq_of_iso e).trans (ComplexBundle.kZeroClass_pullback f)

/-- SG's fixed associated-bundle map is natural under the same actual principal pullback. -/
theorem associatedRepresentationKZero_pullback (f : C(X, Y)) :
    (associatedRepresentationKZero
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)).toAddMonoidHom =
        (complexKZeroPullback f).comp (associatedRepresentationKZero hP).toAddMonoidHom := by
  /- Stage 1: evaluate both additive maps at each finiteRepresentationClass rho.
  The specified generator values of a_P turn the desired equality into
  associatedKZeroClass_pullback for this exact rho and f.
  Stage 2: the existing representation classes generate the original additive
  quotient. Its universal-property uniqueness therefore gives equality of the
  two additive homomorphisms on every virtual representation. Forgetting the
  ring-map fields here only matches the already existing additive K pullback;
  it does not replace either a_P or the K pullback map. -/
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro ρ
  change associatedRepresentationKZero
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
      (finiteRepresentationClass ρ) =
    complexKZeroPullback f (associatedRepresentationKZero hP (finiteRepresentationClass ρ))
  rw [associatedRepresentationKZero_finiteClass, associatedRepresentationKZero_finiteClass]
  exact associatedKZeroClass_pullback f ρ

end AtiyahSinger
