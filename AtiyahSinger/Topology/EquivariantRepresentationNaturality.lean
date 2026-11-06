/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRingRestriction
public import AtiyahSinger.Topology.EquivariantRepresentationAction
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# Naturality of the actual representation action

Public module ID: M1806.

The original proper pullback is R(G)-linear. Restriction of the group action
is semilinear for the original representation restriction. Forgetting all
actions changes a representation coefficient to its integer dimension, and
only after this forgetting. Each formula retains the original support group,
its specified homomorphisms, tensor representatives and native compHom actions.

Sources: ASI I section 2 for the representation module and functorial framework;
SG III.9 for representation rings. These explicit presentation-level diagrams
are elementary supplements and need neither compact groups nor LCH bases.
The product of two supported equivariant classes and other K-model comparisons
remain separate. The three naturality statements are proved below for the same
original maps and representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor isFiniteRank_pullback
  trivialTopology isFiniteRank_trivial

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

set_option backward.isDefEq.respectTransparency.types false in
/-- The specified proper equivariant pullback is linear over the same representation ring. -/
theorem equivariantSupportTripleKZeroPullback_smul (f : C(Y, X))
    (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) (hf : IsProperMap f)
    (r : RepresentationGrothendieckGroup G) (a : EquivariantSupportTripleKZero G X) :
    equivariantSupportTripleKZeroPullback f heq hf (r • a) =
      r • equivariantSupportTripleKZeroPullback f heq hf a := by
  /- Stage 1: take an actual representation and support triple. Pulling its
  diagonal product bundle back gives the same representation bundle on Y.
  The vector-preserving tensor/pullback comparison identifies both tensor
  triples with the same inverse-image control and id tensor original boundary.
  Along heq their fiber actions have exactly the same target transport, hence
  this comparison is an actual equivariant isomorphism square.
  Stage 2: use the representation-action and proper-pullback generator formulas.
  Additivity in the two inputs extends the equality to all virtual classes.
  Only f is required proper, in order to pull back the original compact control. -/
  classical
  let μX := equivariantSupportRepresentationAction (G := G) (X := X)
  let μY := equivariantSupportRepresentationAction (G := G) (X := Y)
  let P := equivariantSupportTripleKZeroPullback f heq hf
  have hgen (ρ : FiniteContinuousRepresentation G) (b : EquivariantSupportBundleTriple G X) :
      P (μX (finiteRepresentationClass ρ) b.kZeroClass) =
        μY (finiteRepresentationClass ρ) (P b.kZeroClass) := by
    change equivariantSupportTripleKZeroPullback f heq hf
        (equivariantSupportRepresentationAction (finiteRepresentationClass ρ) b.kZeroClass) =
      equivariantSupportRepresentationAction (finiteRepresentationClass ρ)
        (equivariantSupportTripleKZeroPullback f heq hf b.kZeroClass)
    rw [equivariantSupportRepresentationAction_finiteClass,
      equivariantSupportTripleKZeroPullback_apply, equivariantSupportTripleKZeroPullback_apply,
      equivariantSupportRepresentationAction_finiteClass]
    apply equivariantSupportTripleKZero_generator_relations.1
    -- These comparisons preserve the tensor vector across the two native total topologies.
    let u (J : FiniteBundle X) :
        Iso (((FiniteBundle.trivial X ρ.dimension).tensor J).pullback f).Fiber
          ((FiniteBundle.trivial Y ρ.dimension).tensor (J.pullback f)).Fiber :=
      (pullbackTensorIso (E := (FiniteBundle.trivial X ρ.dimension).Fiber)
        (F := J.Fiber) f).trans
        ((pullbackTrivialIso f ρ.dimension).tensor (Iso.refl (J.pullback f).Fiber))
    have hu (J : FiniteBundle X) (y : Y)
        (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber (f y)) :
        (u J).linearEquiv y v = v := by
      have hlin : ((u J).linearEquiv y).toLinearMap = LinearMap.id := by
        apply TensorProduct.ext'
        intro t w
        change (pullbackTrivialIso f ρ.dimension).linearEquiv y t ⊗ₜ[ℂ] w = t ⊗ₜ[ℂ] w
        rw [pullbackTrivialIso_apply]
      exact DFunLike.congr_fun hlin v
    -- Pulling a tensor action back transports precisely the original second-factor target.
    have haction (J : FiniteBundle X) (σ : EquivariantStructure G J.Fiber)
        (g : G) (y : Y) (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber (f y)) :
        (((EquivariantStructure.ofFiniteRepresentation ρ).tensor σ).pullback f heq).linearMap
            g y v =
          ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
            (σ.pullback f heq)).linearMap g y v := by
      have htransport (x z : X) (hxz : x = z) (L : J.Fiber (f y) →ₗ[ℂ] J.Fiber z) :
          (Eq.mpr (congrArg (fun t ↦
            ((Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber (f y)) →ₗ[ℂ]
              ((Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber t)) hxz)
            (TensorProduct.map (ρ.representation g).toLinearMap L)) v =
          TensorProduct.map (ρ.representation g).toLinearMap
            (Eq.mpr (congrArg (fun t ↦ J.Fiber (f y) →ₗ[ℂ] J.Fiber t) hxz) L) v := by
        subst z
        rfl
      exact htransport (f (g • y)) (g • f y) (heq g y) (σ.linearMap g (f y))
    let L := (b.tensorRepresentation ρ).pullback f heq hf
    let R := (b.pullback f heq hf).tensorRepresentation ρ
    let K := f ⁻¹' b.1.datum.control
    have hK : IsCompact K := hf.isCompact_preimage b.1.datum.isCompact_control
    have hInv (g : G) (y : Y) : g • y ∈ K ↔ y ∈ K := by
      change f (g • y) ∈ b.1.datum.control ↔ f y ∈ b.1.datum.control
      rw [heq g y]
      exact b.2.isEquivariant.invariant_control g (f y)
    refine ⟨K, hK, hInv, Set.Subset.refl _, Set.Subset.refl _,
      u b.1.source, u b.1.target, ?_, ?_, ?_⟩
    · intro g y v
      exact (hu b.1.source (g • y) _).trans
        ((haction b.1.source b.2.sourceAction g y v).trans
          (congrArg (R.2.sourceAction.linearMap g y) (hu b.1.source y v)).symm)
    · intro g y v
      exact (hu b.1.target (g • y) _).trans
        ((haction b.1.target b.2.targetAction g y v).trans
          (congrArg (R.2.targetAction.linearMap g y) (hu b.1.target y v)).symm)
    · intro y v
      -- The same inverse-image compact exterior is used on both sides of the boundary square.
      have hboundary : (L.1.datum.boundary.linearEquiv y).toLinearMap =
          (R.1.datum.boundary.linearEquiv y).toLinearMap := by
        apply TensorProduct.ext'
        intro t w
        have hp := RelativeTriple.pullback_apply
          (b.1.datum.boundary.tensorLeft (FiniteBundle.trivial X ρ.dimension).Fiber)
          f y (t ⊗ₜ[ℂ] w)
        have hl := RelativeTriple.tensorLeft_tmul
          (FiniteBundle.trivial X ρ.dimension).Fiber b.1.datum.boundary
          ⟨f y, y.property⟩ t w
        have hr := RelativeTriple.tensorLeft_tmul
          (FiniteBundle.trivial Y ρ.dimension).Fiber (b.1.datum.boundary.pullback f) y t w
        have hq := RelativeTriple.pullback_apply b.1.datum.boundary f y w
        exact (hp.trans hl).trans
          ((congrArg (fun w : b.1.target.Fiber (f y) ↦ t ⊗ₜ[ℂ] w) hq).symm.trans hr.symm)
      have hl := L.1.datum.enlarge_apply K hK (Set.Subset.refl _) y v
      have hr := R.1.datum.enlarge_apply K hK (Set.Subset.refl _) y v
      exact (hu b.1.target y _).trans
        ((hl.trans ((DFunLike.congr_fun hboundary v).trans hr.symm)).trans
          (congrArg ((R.1.datum.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv y)
            (hu b.1.source y v)).symm)
  -- The two prescribed maps agree first on support generators and then on all coefficients.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      P.comp (μX (finiteRepresentationClass ρ)) =
        (μY (finiteRepresentationClass ρ)).comp P := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen ρ
  have h : P.comp (μX.flip a) = μY.flip (P a) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    exact DFunLike.congr_fun (hρ ρ) a
  exact DFunLike.congr_fun h r

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Group restriction is semilinear for the same representation-ring restriction homomorphism. -/
theorem equivariantSupportTripleKZeroRestrict_smul (φ : H →ₜ* G)
    (r : RepresentationGrothendieckGroup G) (a : EquivariantSupportTripleKZero G X) :
    letI : MulAction H X := MulAction.compHom X φ.toMonoidHom
    letI : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
    equivariantSupportTripleKZeroRestrict φ (r • a) =
      representationRestrictionRingHom φ r • equivariantSupportTripleKZeroRestrict φ a := by
  /- Stage 1: on original generators, both sides have the same ordinary tensor
  triple and unchanged control. Restricting the tensor action evaluates each
  factor at phi(h), exactly the tensor of the restricted actions. The finite
  representation restriction retains its original coordinates and dimension.
  Thus the identity fiber maps give the required equivariant square for the
  explicit native compHom action, not for an unspecified H action.
  Stage 2: apply both existing generator characterizations and extend by
  additivity. The coefficient map is the same representationRestriction
  packaged as a ring homomorphism, so the equation has the stated semilinearity. -/
  let : MulAction H X := MulAction.compHom X φ.toMonoidHom
  let : ContinuousSMul H X := MulAction.continuousSMul_compHom φ.continuous
  let μG := equivariantSupportRepresentationAction (G := G) (X := X)
  let μH := equivariantSupportRepresentationAction (G := H) (X := X)
  let R := equivariantSupportTripleKZeroRestrict (X := X) φ
  let c := (representationRestrictionRingHom φ).toAddMonoidHom
  have hgen (ρ : FiniteContinuousRepresentation G) (b : EquivariantSupportBundleTriple G X) :
      R (μG (finiteRepresentationClass ρ) b.kZeroClass) =
        μH (c (finiteRepresentationClass ρ)) (R b.kZeroClass) := by
    change equivariantSupportTripleKZeroRestrict φ
        (equivariantSupportRepresentationAction (finiteRepresentationClass ρ) b.kZeroClass) =
      equivariantSupportRepresentationAction
        (representationRestriction φ (finiteRepresentationClass ρ))
        (equivariantSupportTripleKZeroRestrict φ b.kZeroClass)
    rw [equivariantSupportRepresentationAction_finiteClass,
      equivariantSupportTripleKZeroRestrict_apply, representationRestriction_finiteClass,
      equivariantSupportTripleKZeroRestrict_apply,
      equivariantSupportRepresentationAction_finiteClass]
    -- Both restrictions retain the same tensor triple and evaluate both actions at φ(h).
    rfl
  -- Extend first through the original support presentation, then through representation classes.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      R.comp (μG (finiteRepresentationClass ρ)) =
        (μH (c (finiteRepresentationClass ρ))).comp R := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen ρ
  have h : R.comp (μG.flip a) = (μH.flip (R a)).comp c := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    exact DFunLike.congr_fun (hρ ρ) a
  exact DFunLike.congr_fun h r

/-- Forgetting actions changes a representation coefficient to its integer dimension. -/
theorem equivariantSupportTripleKZeroForget_smul
    (r : RepresentationGrothendieckGroup G) (a : EquivariantSupportTripleKZero G X) :
    equivariantSupportTripleKZeroForget (r • a) =
      representationDimension G r • equivariantSupportTripleKZeroForget a := by
  /- First compare the same ordinary tensor triples after forgetting their actions.
  Only a trivial representation is reduced to its dimension inside R(G). The
  original nontrivial representation is never equated to that trivial class.
  Additivity then extends the generator calculation through both presentations. -/
  let τ (n : ℕ) : FiniteContinuousRepresentation G := {
    dimension := n
    representation := ContRepresentation.trivial ℂ G (Fin n → ℂ)
    continuous_action := continuous_snd }
  have hsum (n m : ℕ) : finiteRepresentationClass (τ (n + m)) =
      finiteRepresentationClass (τ n) + finiteRepresentationClass (τ m) := by
    rw [← finiteRepresentationClass_directSum]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    apply ContinuousLinearMap.ext
    intro v
    let d : (Fin (n + m) → ℂ) ≃L[ℂ] (Fin n → ℂ) × (Fin m → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n ⊕ Fin m ↦ ℂ)
        finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin n) (Fin m) (fun _ ↦ ℂ))
    change v = d.symm (d v)
    exact (d.symm_apply_apply v).symm
  have hzero : finiteRepresentationClass (τ 0) = 0 := by
    have h := hsum 0 0
    exact (add_left_cancel (show finiteRepresentationClass (τ 0) +
      finiteRepresentationClass (τ 0) = finiteRepresentationClass (τ 0) + 0 by
        simpa only [add_zero] using h.symm))
  have hone : finiteRepresentationClass (τ 1) = (1 : RepresentationGrothendieckGroup G) := rfl
  have hall (n : ℕ) : finiteRepresentationClass (τ n) =
      n • (1 : RepresentationGrothendieckGroup G) := by
    induction n with
    | zero => simpa using hzero
    | succ n ih => rw [hsum n 1, ih, hone, add_nsmul, one_nsmul]
  let μ := equivariantSupportRepresentationAction (G := G) (X := X)
  let F := equivariantSupportTripleKZeroForget (G := G) (X := X)
  have htrivial (n : ℕ) (b : EquivariantSupportTripleKZero G X) :
      μ (finiteRepresentationClass (τ n)) b = n • b := by
    rw [hall, map_nsmul]
    change n • (equivariantSupportRepresentationAction 1 b) = n • b
    rw [equivariantSupportRepresentationAction_laws.1]
  have hgen (ρ : FiniteContinuousRepresentation G)
      (b : EquivariantSupportBundleTriple G X) :
      F (μ (finiteRepresentationClass ρ) b.kZeroClass) =
        (ρ.dimension : ℤ) • F b.kZeroClass := by
    -- Forgetting discards exactly the representation action, retaining the original control K.
    have hsame : F (μ (finiteRepresentationClass ρ) b.kZeroClass) =
        F (μ (finiteRepresentationClass (τ ρ.dimension)) b.kZeroClass) := by
      change equivariantSupportTripleKZeroForget
          (equivariantSupportRepresentationAction (finiteRepresentationClass ρ) b.kZeroClass) =
        equivariantSupportTripleKZeroForget (equivariantSupportRepresentationAction
          (finiteRepresentationClass (τ ρ.dimension)) b.kZeroClass)
      rw [equivariantSupportRepresentationAction_finiteClass,
        equivariantSupportRepresentationAction_finiteClass,
        equivariantSupportTripleKZeroForget_apply, equivariantSupportTripleKZeroForget_apply]
      rfl
    rw [hsame, htrivial, map_nsmul, natCast_zsmul]
  -- Both sides are additive in a support class, including negative and zero classes.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      F.comp (μ (finiteRepresentationClass ρ)) =
        (ρ.dimension : ℤ) • F := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen ρ
  let D : RepresentationGrothendieckGroup G →+ SupportTripleKZero X := {
    toFun r := representationDimension G r • F a
    map_zero' := by simp
    map_add' r s := by simp only [map_add, add_zsmul] }
  have h : F.comp (μ.flip a) = D := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    change F (μ (finiteRepresentationClass ρ) a) =
      representationDimension G (finiteRepresentationClass ρ) • F a
    rw [representationDimension_finiteClass]
    exact DFunLike.congr_fun (hρ ρ) a
  exact DFunLike.congr_fun h r

end AtiyahSinger.ComplexBundle
