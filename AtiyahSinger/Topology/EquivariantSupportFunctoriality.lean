/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantRestriction
public import AtiyahSinger.Topology.EquivariantSupportPullback
public import AtiyahSinger.Topology.SupportTriplePullback

/-!
# Proper functoriality of the original equivariant support quotients

Public module ID: M1811.

Actual equivariant bundle pullback descends through the same isomorphism,
direct-sum and arbitrary equivariant identity relations. Stable classes use the
same pulled-back representatives. The group maps commute with forgetting the
actions and restriction along a continuous group homomorphism.

Properness ensures that inverse-image controls are compact. Neither this
presentation-level construction nor its naturality needs a compact group,
a locally compact base, or effectiveness of the stable-to-group comparison.
Sources: SG I.9, pp.59,66, ASI I section 2 and KA II.2.33, II.4.1--4.2;
the explicit original-triple descent and action transports are supplementary.
The original proper pullback, stable-quotient functoriality and the two
naturality squares are proved below using the same representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]
  [MulAction G Z] [ContinuousSMul G Z]

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual identity square, reused for the presented and stable equivariant quotients. -/
private theorem EquivariantSupportBundleTriple.isIsomorphic_pullback_id
    (a : EquivariantSupportBundleTriple G X) :
    (a.pullback (ContinuousMap.id X) (fun _ _ ↦ rfl) isProperMap_id).IsIsomorphic a := by
  -- Both canonical bundle comparisons preserve each original vector and its action.
  obtain ⟨u, hu⟩ := exists_pullback_id_iso (E := a.1.source.Fiber)
  obtain ⟨w, hw⟩ := exists_pullback_id_iso (E := a.1.target.Fiber)
  refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
    a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
    u, w, ?_, ?_, ?_⟩
  · intro g x v
    exact (hu (g • x) _).trans
      (congrArg (a.2.sourceAction.linearMap g x) (hu x v)).symm
  · intro g x v
    exact (hw (g • x) _).trans
      (congrArg (a.2.targetAction.linearMap g x) (hw x v)).symm
  · -- The old boundary is read on the unchanged invariant compact exterior.
    intro x v
    have hl := (a.1.datum.pullback (ContinuousMap.id X) isProperMap_id).enlarge_apply
      a.1.datum.control a.1.datum.isCompact_control (Set.Subset.refl _) x v
    have hp := RelativeTriple.pullback_apply a.1.datum.boundary (ContinuousMap.id X) x v
    have hr := a.1.datum.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
      (Set.Subset.refl _) x v
    exact (hw x _).trans (((hl.trans hp).trans hr.symm).trans
      (congrArg ((a.1.datum.enlarge a.1.datum.control a.1.datum.isCompact_control
        (Set.Subset.refl _)).boundary.linearEquiv x) (hu x v)).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- The same composite square supplies functoriality on both original equivariant quotients. -/
private theorem EquivariantSupportBundleTriple.isIsomorphic_pullback_comp
    (a : EquivariantSupportBundleTriple G X) (f : C(Y, X)) (k : C(Z, Y))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hkeq : ∀ (g : G) (z : Z), k (g • z) = g • k z)
    (hf : IsProperMap f) (hk : IsProperMap k) :
    ((a.pullback f heq hf).pullback k hkeq hk).IsIsomorphic
      (a.pullback (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) (hf.comp hk)) := by
  -- Combine the two exact target transports before comparing the original actions.
  have haction (J : FiniteBundle X) (ρ : EquivariantStructure G J.Fiber)
      (g : G) (z : Z) (v : J.Fiber (f (k z))) :
      ((ρ.pullback f heq).pullback k hkeq).linearMap g z v =
        (ρ.pullback (f.comp k)
          (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z)))).linearMap g z v := by
    have htransport (y₀ y₁ : Y) (hy : y₀ = y₁) (x₁ : X) (hx : f y₁ = x₁)
        (L : J.Fiber (f (k z)) →ₗ[ℂ] J.Fiber x₁) :
        (Eq.mpr (congrArg (fun y ↦ J.Fiber (f (k z)) →ₗ[ℂ] J.Fiber (f y)) hy)
          (Eq.mpr (congrArg (fun x ↦ J.Fiber (f (k z)) →ₗ[ℂ] J.Fiber x) hx) L)) v =
        (Eq.mpr (congrArg (fun x ↦ J.Fiber (f (k z)) →ₗ[ℂ] J.Fiber x)
          ((congrArg f hy).trans hx)) L) v := by
      subst y₁
      subst x₁
      rfl
    exact htransport (k (g • z)) (g • k z) (hkeq g z) (g • f (k z))
      (heq g (k z)) (ρ.linearMap g (f (k z)))
  obtain ⟨u, hu⟩ := exists_pullback_comp_iso (E := a.1.source.Fiber) f k
  obtain ⟨w, hw⟩ := exists_pullback_comp_iso (E := a.1.target.Fiber) f k
  let K := (f.comp k) ⁻¹' a.1.datum.control
  have hK : IsCompact K := (hf.comp hk).isCompact_preimage a.1.datum.isCompact_control
  have hInv (g : G) (z : Z) : g • z ∈ K ↔ z ∈ K := by
    change f (k (g • z)) ∈ a.1.datum.control ↔ f (k z) ∈ a.1.datum.control
    rw [hkeq g z, heq g (k z)]
    exact a.2.isEquivariant.invariant_control g (f (k z))
  -- The inverse-image control and vector-preserving comparisons are the specified ones.
  refine ⟨K, hK, hInv, Set.Subset.refl _, Set.Subset.refl _, u, w, ?_, ?_, ?_⟩
  · intro g z v
    exact (hu (g • z) _).trans ((haction a.1.source a.2.sourceAction g z v).trans
      (congrArg ((a.2.sourceAction.pullback (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z)))).linearMap g z)
        (hu z v)).symm)
  · intro g z v
    exact (hw (g • z) _).trans ((haction a.1.target a.2.targetAction g z v).trans
      (congrArg ((a.2.targetAction.pullback (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z)))).linearMap g z)
        (hw z v)).symm)
  · intro z v
    have hl := ((a.1.datum.pullback f hf).pullback k hk).enlarge_apply K hK
      (Set.Subset.refl _) z v
    have hp := RelativeTriple.pullback_apply (a.1.datum.boundary.pullback f) k z v
    have hq := RelativeTriple.pullback_apply a.1.datum.boundary f ⟨k z, z.property⟩ v
    have hr := (a.1.datum.pullback (f.comp k) (hf.comp hk)).enlarge_apply K hK
      (Set.Subset.refl _) z v
    have hc := RelativeTriple.pullback_apply a.1.datum.boundary (f.comp k) z v
    -- Both boundaries evaluate on the same original vector over f(k(z)).
    exact (hw z _).trans (((hl.trans (hp.trans hq)).trans (hr.trans hc).symm).trans
      (congrArg (((a.1.datum.pullback (f.comp k) (hf.comp hk)).enlarge K hK
        (Set.Subset.refl _)).boundary.linearEquiv z) (hu z v)).symm)

/-- Descend the actual proper pullback through the three existing equivariant relations. -/
def equivariantSupportTripleKZeroPullback (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G Y :=
  (equivariantSupportTripleKZero_universal_property
    (fun a ↦ (a.pullback f heq hf).kZeroClass)
    (fun a b h ↦ equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.pullback_relations f heq hf).1 a b h))
    (fun a b ↦ (equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.pullback_relations f heq hf).2.2.1 a b)).trans
        (equivariantSupportTripleKZero_generator_relations.2.1 _ _))
    (fun E ρE ↦ (equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.pullback_relations f heq hf).2.2.2 E ρE)).trans
        (equivariantSupportTripleKZero_generator_relations.2.2 _ _))).choose

/-- Each generator is sent to the class of its specified original equivariant pullback. -/
theorem equivariantSupportTripleKZeroPullback_apply (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f)
    (a : EquivariantSupportBundleTriple G X) :
    equivariantSupportTripleKZeroPullback f heq hf a.kZeroClass =
      (a.pullback f heq hf).kZeroClass := by
  /- Read the generator equation from the exact universal-property witness used
  in the definition. The original inverse-image control, pulled-back boundary
  and transported fiber actions remain fixed; no replacement triple is chosen. -/
  exact (equivariantSupportTripleKZero_universal_property
    (fun a ↦ (a.pullback f heq hf).kZeroClass)
    (fun a b h ↦ equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.pullback_relations f heq hf).1 a b h))
    (fun a b ↦ (equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.pullback_relations f heq hf).2.2.1 a b)).trans
        (equivariantSupportTripleKZero_generator_relations.2.1 _ _))
    (fun E ρE ↦ (equivariantSupportTripleKZero_generator_relations.1 _ _
      ((EquivariantSupportBundleTriple.pullback_relations f heq hf).2.2.2 E ρE)).trans
        (equivariantSupportTripleKZero_generator_relations.2.2 _ _))).choose_spec.1 a

/-- Identity pullback is the identity on the presented equivariant support group. -/
theorem equivariantSupportTripleKZeroPullback_id :
    equivariantSupportTripleKZeroPullback (ContinuousMap.id X)
      (fun _ _ ↦ rfl) isProperMap_id = AddMonoidHom.id (EquivariantSupportTripleKZero G X) := by
  /- Stage 1: on a generator, the vector-preserving identity bundle comparison
  intertwines the supplied action and commutes with the original boundary.
  The original and pulled-back controls agree, giving an equivariant square.
  Stage 2: the isomorphism relation identifies the two generator values.
  Uniqueness in the group presentation extends equality to the full group. -/
  -- The original free generators determine both additive maps on the quotient.
  have heq : (equivariantSupportTripleKZeroPullback (ContinuousMap.id X)
        (fun _ _ ↦ rfl) isProperMap_id).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) =
      (AddMonoidHom.id (EquivariantSupportTripleKZero G X)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change equivariantSupportTripleKZeroPullback (ContinuousMap.id X)
      (fun _ _ ↦ rfl) isProperMap_id a.kZeroClass = a.kZeroClass
    exact (equivariantSupportTripleKZeroPullback_apply _ _ _ a).trans
      (equivariantSupportTripleKZero_generator_relations.1 _ _ a.isIsomorphic_pullback_id)
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) z
  exact DFunLike.congr_fun heq w

/-- Proper equivariant pullback composes contravariantly on the original group presentation. -/
theorem equivariantSupportTripleKZeroPullback_comp (f : C(Y, X)) (k : C(Z, Y))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hkeq : ∀ (g : G) (z : Z), k (g • z) = g • k z)
    (hf : IsProperMap f) (hk : IsProperMap k) :
    equivariantSupportTripleKZeroPullback (f.comp k)
      (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) (hf.comp hk) =
      (equivariantSupportTripleKZeroPullback k hkeq hk).comp
        (equivariantSupportTripleKZeroPullback f heq hf) := by
  /- Stage 1: compare iterated and composite pullbacks using the canonical
  vector-preserving isomorphisms. The composed equivariance equation is exactly
  the two successive base transports; proof irrelevance makes their transports
  coherent. Both controls are the same inverse image of the original control.
  Stage 2: these comparisons intertwine the original boundary and action maps,
  giving the defining isomorphism relation on each generator. Apply uniqueness
  in the presentation. No stable-to-group injectivity is used. -/
  have hgen (a : EquivariantSupportBundleTriple G X) :
      equivariantSupportTripleKZeroPullback (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) (hf.comp hk) a.kZeroClass =
      equivariantSupportTripleKZeroPullback k hkeq hk
        (equivariantSupportTripleKZeroPullback f heq hf a.kZeroClass) := by
    rw [equivariantSupportTripleKZeroPullback_apply,
      equivariantSupportTripleKZeroPullback_apply, equivariantSupportTripleKZeroPullback_apply]
    exact (equivariantSupportTripleKZero_generator_relations.1 _ _
      (a.isIsomorphic_pullback_comp f k heq hkeq hf hk)).symm
  -- Extend the same representative calculation to the original presented group.
  have hext : (equivariantSupportTripleKZeroPullback (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) (hf.comp hk)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) =
      ((equivariantSupportTripleKZeroPullback k hkeq hk).comp
        (equivariantSupportTripleKZeroPullback f heq hf)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) := by
    apply FreeAbelianGroup.lift_ext
    exact hgen
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) z
  exact DFunLike.congr_fun hext w

/-- Forgetting the actions commutes with the specified proper pullback. -/
theorem equivariantSupportTripleKZeroForget_pullback (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    (equivariantSupportTripleKZeroForget (G := G) (X := Y)).comp
        (equivariantSupportTripleKZeroPullback f heq hf) =
      (supportTripleKZeroPullback f hf).comp
        (equivariantSupportTripleKZeroForget (G := G) (X := X)) := by
  /- On each original generator, both composites give its ordinary proper
  pullback class. The equivariant pullback was built on precisely this ordinary
  triple, including its control and boundary. Extend equality by the universal
  property; no converse to forgetting or equivariant lifting is asserted. -/
  have hext : ((equivariantSupportTripleKZeroForget (G := G) (X := Y)).comp
        (equivariantSupportTripleKZeroPullback f heq hf)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) =
      ((supportTripleKZeroPullback f hf).comp
        (equivariantSupportTripleKZeroForget (G := G) (X := X))).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change equivariantSupportTripleKZeroForget
        (equivariantSupportTripleKZeroPullback f heq hf a.kZeroClass) =
      supportTripleKZeroPullback f hf (equivariantSupportTripleKZeroForget a.kZeroClass)
    rw [equivariantSupportTripleKZeroPullback_apply,
      equivariantSupportTripleKZeroForget_apply, equivariantSupportTripleKZeroForget_apply,
      supportTripleKZeroPullback_apply]
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) z
  exact DFunLike.congr_fun hext w

/-- Proper pullback on the actual stable quotient uses the same representatives. -/
def stableEquivariantSupportTripleClassPullback (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    StableEquivariantSupportTripleClass G X → StableEquivariantSupportTripleClass G Y :=
  Quotient.map (fun a ↦ a.pullback f heq hf)
    (fun a b h ↦ (EquivariantSupportBundleTriple.pullback_relations f heq hf).2.1 a b h)

/-- Identity pullback fixes every actual equivariant stable class. -/
theorem stableEquivariantSupportTripleClassPullback_id
    (a : StableEquivariantSupportTripleClass G X) :
    stableEquivariantSupportTripleClassPullback (ContinuousMap.id X)
      (fun _ _ ↦ rfl) isProperMap_id a = a := by
  /- Choose an original triple representative. The vector-preserving identity
  pullback comparisons intertwine its specified actions and give an actual
  equivariant square on the unchanged compact exterior. Such an isomorphism
  is a stable isomorphism, hence gives equality in this same setoid quotient.
  This argument does not infer equality from the stable-to-group map. -/
  induction a using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    exact (EquivariantSupportBundleTriple.isStablyIsomorphic_properties
      (G := G) (X := X)).2.1 _ _ a.isIsomorphic_pullback_id

/-- Iterated proper pullback agrees with composite pullback in the actual stable quotient. -/
theorem stableEquivariantSupportTripleClassPullback_comp (f : C(Y, X)) (k : C(Z, Y))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hkeq : ∀ (g : G) (z : Z), k (g • z) = g • k z)
    (hf : IsProperMap f) (hk : IsProperMap k)
    (a : StableEquivariantSupportTripleClass G X) :
    stableEquivariantSupportTripleClassPullback (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) (hf.comp hk) a =
      stableEquivariantSupportTripleClassPullback k hkeq hk
        (stableEquivariantSupportTripleClassPullback f heq hf a) := by
  /- Stage 1: reduce to the original representative and use the canonical
  vector-preserving comparison between iterated and composite pullback.
  Its equivariance follows from composition of the exact base transports;
  both controls and boundary values are the same iterated inverse images.
  Stage 2: the resulting original equivariant square is a stable relation,
  so quotient soundness identifies the two representatives. No compactness
  of the group, cutoff theorem or injectivity of the comparison is needed. -/
  induction a using Quotient.inductionOn with
  | h a =>
    apply Quotient.sound
    apply (EquivariantSupportBundleTriple.isStablyIsomorphic_properties
      (G := G) (X := Z)).2.1
    exact (EquivariantSupportBundleTriple.isIsomorphic_properties
      (G := G) (X := Z)).1.symm (a.isIsomorphic_pullback_comp f k heq hkeq hf hk)

/-- Stable pullback and its comparison to the presentation retain the same generator map. -/
theorem stableEquivariantSupportTripleClassPullback_comparison (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    (∀ a : EquivariantSupportBundleTriple G X,
      stableEquivariantSupportTripleClassPullback f heq hf a.stableClass =
        (a.pullback f heq hf).stableClass) ∧
    ∀ a : StableEquivariantSupportTripleClass G X,
      stableEquivariantSupportTripleClassToKZero
          (stableEquivariantSupportTripleClassPullback f heq hf a) =
        equivariantSupportTripleKZeroPullback f heq hf
          (stableEquivariantSupportTripleClassToKZero a) := by
  /- The quotient map evaluates at the specified pullback representative.
  For the comparison square, quotient induction reduces to that same original
  triple, and the group generator equation identifies the two routes. This
  construction certificate uses only well-definedness of the quotient maps;
  it does not require the stable comparison to be bijective. -/
  constructor
  · intro a
    rfl
  · intro a
    induction a using Quotient.inductionOn with
    | h a =>
      exact (equivariantSupportTripleKZeroPullback_apply f heq hf a).symm

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restricting the group action commutes with the same proper equivariant pullback. -/
theorem equivariantSupportTripleKZeroRestrict_pullback (φ : H →ₜ* G) (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    letI : MulAction H Y := MulAction.compHom Y φ.toMonoidHom
    letI : ContinuousSMul H Y := MulAction.continuousSMul_compHom φ.continuous
    (equivariantSupportTripleKZeroRestrict (X := Y) φ).comp
        (equivariantSupportTripleKZeroPullback f heq hf) =
      (equivariantSupportTripleKZeroPullback f (fun h y ↦ heq (φ h) y) hf).comp
        (equivariantSupportTripleKZeroRestrict (X := X) φ) := by
  /- Stage 1: on each generator, both routes retain the same ordinary pullback
  triple. The action on its fiber is the original action of φ(h), transported
  along the same equation f(φ(h)*y)=φ(h)*f(y). Restriction changes neither the
  inverse-image control nor the boundary. Identity bundle maps therefore give
  an equivariant square between these precise representatives.
  Stage 2: use the isomorphism relation and both generator characterizations,
  then uniqueness in the original G presentation. The H action is explicitly
  the native compHom action on both bases; it is not a new unspecified action. -/
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  let : MulAction H Y := MulAction.compHom Y φ.toMonoidHom
  let : ContinuousSMul H Y := MulAction.continuousSMul_compHom φ.continuous
  have hext : ((equivariantSupportTripleKZeroRestrict (X := Y) φ).comp
        (equivariantSupportTripleKZeroPullback f heq hf)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) =
      ((equivariantSupportTripleKZeroPullback f (fun h y ↦ heq (φ h) y) hf).comp
        (equivariantSupportTripleKZeroRestrict (X := X) φ)).comp
        (QuotientAddGroup.mk' (equivariantSupportTripleKZeroRelations G X)) := by
    apply FreeAbelianGroup.lift_ext
    intro a
    change equivariantSupportTripleKZeroRestrict φ
        (equivariantSupportTripleKZeroPullback f heq hf a.kZeroClass) =
      equivariantSupportTripleKZeroPullback f (fun h y ↦ heq (φ h) y) hf
        (equivariantSupportTripleKZeroRestrict φ a.kZeroClass)
    rw [equivariantSupportTripleKZeroPullback_apply, equivariantSupportTripleKZeroRestrict_apply,
      equivariantSupportTripleKZeroRestrict_apply, equivariantSupportTripleKZeroPullback_apply]
    -- Action precomposition evaluates at φ(h), with exactly the same fiber transport.
    rfl
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective
    (equivariantSupportTripleKZeroRelations G X) z
  exact DFunLike.congr_fun hext w

end AtiyahSinger.ComplexBundle
