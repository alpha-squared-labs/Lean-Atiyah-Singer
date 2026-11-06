/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBottNaturality
public import AtiyahSinger.Topology.EquivariantBottProduct
public import AtiyahSinger.Topology.EquivariantOpenExtension

/-!
# Representation Bott multiplication and open extension

Public module ID: M1761.

AB01: arbitrary finite continuous complex representations use the original-base
coordinate-independent Bott classes. Direct sums use the native product carrier
and action, with no artificial Hilbert norm on that product. Multiplication by
this exact class on a general base uses the existing equivariant external product.
It commutes with the new actual covariant open extension along f and f times id.

ASI I, pp.494--496, gives the multiplicative exterior construction and equivariant
Bott framework. The open-extension square is its usual supported naturality;
the implementation expands compact windows and the original reciprocal-cutoff
external product. Neither open embedding is assumed proper. This is the trivial
representation-bundle square, not a claim about all associated families or an
equivariant pushforward for every embedding. Restriction of the forward map and the
direct-sum comparison and the original open-extension comparison are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle Topology

set_option maxSynthPendingDepth 25

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]
  {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [DistribMulAction G W] [SMulCommClass G ℂ W] [ContinuousSMul G W]

/-- The class of the actual direct-sum representation is the original equivariant external
product, independently of the two invariant coordinate choices. -/
theorem equivariantRepresentationBottClass_prod :
    letI := FiniteDimensional.proper ℂ V
    letI := FiniteDimensional.proper ℂ W
    equivariantRepresentationBottClass (G := G) (V := V × W) =
      equivariantSupportKZeroExternalProduct
        (equivariantRepresentationBottClass (G := G) (V := V))
        (equivariantRepresentationBottClass (G := G) (V := W)) := by
  /- Stage 1: choose the original two unitaryBottCoordinates and their exact
  conjugated actions. Their product, followed by the native WithLp equivalence,
  is an equivariant continuous linear map onto the Hilbert direct sum of those
  two unitary representations. The class's arbitrary-model comparison permits
  this particular model without requiring it to be the chosen model for V×W.
  Stage 2: use the actual exterior ordered-tensor map and the unitary direct-sum
  class formula from EquivariantBottProduct. It compares the original SG symbols
  with the same reciprocal-cutoff external product, including its parity order
  and upper-right sign. Stage 3: pull back along the product of the two original
  coordinate maps. Proper external-product naturality and the arbitrary-model
  formulas identify the two factors with their original-base classes. This
  keeps the entire G action, includes zero dimensions, and makes no metric
  claim about the native maximum norm on V×W. -/
  classical
  let := FiniteDimensional.proper ℂ V
  let := FiniteDimensional.proper ℂ W
  -- Use the two original invariant coordinate models, retaining their conjugated actions.
  let U := EuclideanSpace ℂ (Fin (Module.finrank ℂ V))
  let T := EuclideanSpace ℂ (Fin (Module.finrank ℂ W))
  let u : V ≃L[ℂ] U := unitaryBottCoordinates (G := G) (V := V)
  let v : W ≃L[ℂ] T := unitaryBottCoordinates (G := G) (V := W)
  let := bottCoordinateAction (G := G) u
  let := bottCoordinate_smulCommClass (G := G) u
  let := bottCoordinate_continuousSMul (G := G) u
  let := bottCoordinateAction (G := G) v
  let := bottCoordinate_smulCommClass (G := G) v
  let := bottCoordinate_continuousSMul (G := G) v
  have hU (g : G) (x y : U) : inner ℂ (g • x) (g • y) = inner ℂ x y := by
    change inner ℂ (u (g • u.symm x)) (u (g • u.symm y)) = inner ℂ x y
    have h := Classical.choose_spec (exists_unitaryBottCoordinates (G := G) (V := V))
      g (u.symm x) (u.symm y)
    change inner ℂ (u (g • u.symm x)) (u (g • u.symm y)) =
      inner ℂ (u (u.symm x)) (u (u.symm y)) at h
    simpa only [u.apply_symm_apply] using h
  have hT (g : G) (x y : T) : inner ℂ (g • x) (g • y) = inner ℂ x y := by
    change inner ℂ (v (g • v.symm x)) (v (g • v.symm y)) = inner ℂ x y
    have h := Classical.choose_spec (exists_unitaryBottCoordinates (G := G) (V := W))
      g (v.symm x) (v.symm y)
    change inner ℂ (v (g • v.symm x)) (v (g • v.symm y)) =
      inner ℂ (v (v.symm x)) (v (v.symm y)) at h
    simpa only [v.apply_symm_apply] using h
  have hu (g : G) (x : V) : u (g • x) = g • u x := by
    change u (g • x) = u (g • u.symm (u x))
    rw [u.symm_apply_apply]
  have hv (g : G) (x : W) : v (g • x) = g • v x := by
    change v (g • x) = v (g • v.symm (v x))
    rw [v.symm_apply_apply]
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ U T).symm
  have hsum (g : G) (x y : WithLp 2 (U × T)) :
      inner ℂ (g • x) (g • y) = inner ℂ x y :=
    congrArg₂ (fun a b : ℂ ↦ a + b)
      (hU g (WithLp.ofLp x).1 (WithLp.ofLp y).1)
      (hT g (WithLp.ofLp x).2 (WithLp.ofLp y).2)
  let f : C(V × W, U × T) := (⟨u, u.continuous⟩ : C(V, U)).prodMap ⟨v, v.continuous⟩
  have hf (g : G) (x : V × W) : f (g • x) = g • f x := Prod.ext (hu g x.1) (hv g x.2)
  have hmodel (g : G) (x : V × W) :
      ((u.prodCongr v).trans e) (g • x) = g • ((u.prodCongr v).trans e) x := by
    exact congrArg e (hf g x)
  -- Compare the product with this particular Hilbert model, then compose proper pullbacks.
  rw [equivariantRepresentationBottClass_eq_pullback hsum ((u.prodCongr v).trans e) hmodel]
  change equivariantSupportTripleKZeroPullback ((⟨e, e.continuous⟩ : C(_, _)).comp f)
    _ _ (equivariantExteriorBottClass hsum) = _
  rw [equivariantSupportTripleKZeroPullback_comp]
  change equivariantSupportTripleKZeroPullback f hf
    (u.toHomeomorph.isProperMap.prodMap v.toHomeomorph.isProperMap)
    (equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ (fun _ _ ↦ rfl)
      e.toHomeomorph.isProperMap (equivariantExteriorBottClass hsum)) = _
  -- The original ordered product formula and its proper naturality identify both factors.
  rw [equivariantExteriorBottClass_prod hU hT,
    equivariantSupportKZeroExternalProduct_pullback _ _ hu hv
      u.toHomeomorph.isProperMap v.toHomeomorph.isProperMap]
  rw [← equivariantRepresentationBottClass_eq_pullback hU u hu,
    ← equivariantRepresentationBottClass_eq_pullback hT v hv]

variable {X Y : Type*}
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [LocallyCompactSpace Y] [T2Space Y]

/-- The supported Bott multiplication for the specified representation on the original base. -/
def equivariantRepresentationBottSuspension :
    letI := FiniteDimensional.proper ℂ V
    EquivariantSupportTripleKZero G X →ₗ[RepresentationGrothendieckGroup G]
      EquivariantSupportTripleKZero G (X × V) := by
  letI := FiniteDimensional.proper ℂ V
  let b := equivariantRepresentationBottClass (G := G) (V := V)
  exact
    { toFun := fun a ↦ equivariantSupportKZeroExternalProduct a b
      map_add' := fun a c ↦ by
        exact congrArg (fun f ↦ f b) (map_add equivariantSupportKZeroExternalProduct a c)
      map_smul' := fun r a ↦ equivariantSupportKZeroExternalProduct_smul_left r a b }

/-- The actual representation Bott multiplication commutes with covariant open extension. -/
theorem equivariantRepresentationBottSuspension_openPushforward
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (a : EquivariantSupportTripleKZero G X) :
    letI := FiniteDimensional.proper ℂ V
    equivariantSupportTripleKZeroOpenPushforward
        (f.prodMap (ContinuousMap.id V)) (hf.prodMap IsOpenEmbedding.id)
        (fun g z ↦ Prod.ext (heq g z.1) rfl)
        (equivariantRepresentationBottSuspension (V := V) a) =
      equivariantRepresentationBottSuspension (V := V)
        (equivariantSupportTripleKZeroOpenPushforward f hf heq a) := by
  /- Stage 1: expand the defined suspension as the original external product
  with the particular representation class. Apply the actual external-product
  open-pushforward square to f and the identity of the representation space.
  On generators this uses compact windows, stable equivariant extensions and
  the same reciprocal cutoffs; it never extends an arbitrary input bundle
  across the entire open-image boundary. Stage 2: identity open extension fixes
  precisely the chosen Bott class. The two remaining expressions are exactly
  the suspensions above. Neither f nor f times id is required to be proper;
  compact images, not inverse images of arbitrary compact sets, control support. -/
  let := FiniteDimensional.proper ℂ V
  -- Apply the product square to the original representation class and the identity map.
  change equivariantSupportTripleKZeroOpenPushforward
    (f.prodMap (ContinuousMap.id V)) (hf.prodMap IsOpenEmbedding.id) _
      (equivariantSupportKZeroExternalProduct a
        (equivariantRepresentationBottClass (G := G) (V := V))) = _
  rw [equivariantSupportKZeroExternalProduct_openPushforward f hf heq
    (ContinuousMap.id V) IsOpenEmbedding.id (fun _ _ ↦ rfl)]
  have hid := (equivariantSupportTripleKZeroOpenPushforward_functoriality
    (G := G) (X := V) (Y := V) (Z := V)).1
  rw [hid]
  rfl

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [hCompact : CompactSpace H] [hHausdorff : T2Space H]

include hCompact hHausdorff in
/-- The forward Bott map for a general representation commutes with full representation
restriction, even when the two groups choose different averaged coordinates. -/
theorem equivariantRepresentationBottLinearMap_restrict (φ : H →ₜ* G)
    (r : RepresentationGrothendieckGroup G) :
    letI : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
    letI : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
    letI : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ
        (equivariantRepresentationBottLinearMap (G := G) (V := V) r) =
      equivariantRepresentationBottLinearMap (G := H) (V := V)
        (representationRestrictionRingHom φ r) := by
  /- Apply the established semilinearity of the original support restriction
  to multiplication by the actual class. The arbitrary-representation class
  restriction theorem identifies that class with H's own coordinate-independent
  class. This is the original representationRestrictionRingHom coefficient,
  not its dimension, and requires no injectivity or surjectivity of phi. -/
  let : DistribMulAction H V := DistribMulAction.compHom V φ.toMonoidHom
  let : SMulCommClass H ℂ V := ⟨fun h c v ↦ smul_comm (φ h) c v⟩
  let : ContinuousSMul H V := MulAction.continuousSMul_compHom φ.continuous
  -- Semilinearity retains the full restricted representation coefficient.
  change equivariantSupportTripleKZeroRestrict φ
      (r • equivariantRepresentationBottClass (G := G) (V := V)) =
    representationRestrictionRingHom φ r •
      equivariantRepresentationBottClass (G := H) (V := V)
  rw [equivariantSupportTripleKZeroRestrict_smul, equivariantRepresentationBottClass_restrict]

end AtiyahSinger
