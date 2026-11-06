/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedKZero

/-!
# The associated representation coefficient in a principal gauge

Public module ID: M1535.

A supplied continuous right-equivariant gauge gives explicit linear coordinates
on the original associated vector bundle. Only after proving this bundle
isomorphism is its K class reduced to the dimension of the representation.
This applies to the original principal bundle over a discrete base, without
asserting that the original group representation is trivial.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G P B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [CompactSpace B] [T2Space B]

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology trivialTopology isFiniteRank_trivial

/-- An actual principal gauge trivializes the associated coefficient through its vector action. -/
theorem associatedRepresentationKZero_eq_dimension_of_gauge
    (hP : IsPrincipalBundle G projection) (θ : C(P, G))
    (hθ : ∀ (p : P) (g : G), θ (MulOpposite.op g • p) = θ p * g)
    (x : RepresentationGrothendieckGroup G) :
    associatedRepresentationKZero hP x = (representationDimension G x : ComplexKZero B) := by
  classical
  -- The gauge supplies coordinates on the actual quotient bundle for every representation.
  have hbundle (ρ : FiniteContinuousRepresentation G) :
      associatedKZeroClass hP ρ =
        ComplexBundle.kZeroClass (Bundle.Trivial B (Fin ρ.dimension → ℂ)) := by
    let := associatedRepresentationAction ρ.representation
    let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
    let f (b : B) (p : P) (_hp : projection p = b) :
        (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] Bundle.Trivial B (Fin ρ.dimension → ℂ) b :=
      LinearEquiv.ofBijective (ρ.representation (θ p)).toLinearMap
        (MulAction.bijective (θ p))
    obtain ⟨a, _ha⟩ := exists_associatedVector_iso_of_covariant_equiv hP ρ
      (Bundle.Trivial B (Fin ρ.dimension → ℂ)) f (by
        apply continuous_induced_rng.mpr
        exact (hP.projection_properties.1.comp continuous_fst).prodMk
          (ρ.continuous_action.comp
            ((θ.continuous.comp continuous_fst).prodMk continuous_snd))) (by
        intro b p hp g v
        change ρ.representation (θ (MulOpposite.op g • p)) v =
          ρ.representation (θ p) (ρ.representation g v)
        rw [hθ, map_mul]
        rfl)
    exact ComplexBundle.kZeroClass_eq_of_iso a
  -- The finite trivial representation of dimension n is n copies of the tensor unit.
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
  have hnat (n : ℕ) : finiteRepresentationClass (τ n) =
      (n : RepresentationGrothendieckGroup G) := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      rw [hsum, ih, Nat.cast_add, Nat.cast_one]
      rfl
  have hgen (ρ : FiniteContinuousRepresentation G) :
      associatedRepresentationKZero hP (finiteRepresentationClass ρ) =
        (representationDimension G (finiteRepresentationClass ρ) : ComplexKZero B) := by
    have heq : associatedKZeroClass hP ρ = associatedKZeroClass hP (τ ρ.dimension) :=
      (hbundle ρ).trans (hbundle (τ ρ.dimension)).symm
    rw [associatedRepresentationKZero_finiteClass, heq,
      ← associatedRepresentationKZero_finiteClass, hnat, map_natCast,
      representationDimension_finiteClass, Int.cast_natCast]
  -- Both additive maps descend through the original presentation of virtual representations.
  have h : (associatedRepresentationKZero hP).toAddMonoidHom =
      (Int.castAddHom (ComplexKZero B)).comp (representationDimension G) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact hgen
  exact DFunLike.congr_fun h x

end AtiyahSinger
