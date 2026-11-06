/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRingRestriction
public import AtiyahSinger.Analysis.SphereHodgeIndex

/-!
# The rotation-sphere and reflection-circle de Rham indices

Public module ID: M0795.

AR01: the genuine even-to-odd round de Rham operator has SO(2)-equivariant
index two on S2 and O(1)-equivariant index one minus the determinant line on S1.
The special orthogonal group is mathlib's original matrix subgroup, with its
subspace topology and native inclusion into the orthogonal group.

Restriction keeps the same smooth operator, kernel and range quotient. Its
analytic index uses the actual precomposed finite representations on those
same carriers and agrees with representation-ring restriction.
The arbitrary-coordinate characterization
retains explicit intertwining on that same kernel and quotient-cokernel.
Thus the SO(2) index is not merely a renamed restriction of a virtual class.

Sources: Atiyah--Singer, The Index of Elliptic Operators I, Section 8,
printed p.524, verifies these two low-dimensional cases. The Hodge index
calculation is also discussed in Lawson--Michelsohn, Spin Geometry, III.9,
pp.211--212. Restriction of the actual actions is a standard supplementary
argument, not a separately numbered theorem in those sources. The sphere
top class carries det for the full O(2); it becomes trivial only after
restriction to SO(2). No cancellation in R(O(2)) is performed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option maxSynthPendingDepth 25

/-- The native special orthogonal group inherits its topological group structure from O(r). -/
instance isTopologicalGroup_specialOrthogonalGroup (r : ℕ) :
    IsTopologicalGroup (Matrix.specialOrthogonalGroup (Fin r) ℝ) := by
  let h : Matrix.specialOrthogonalGroup (Fin r) ℝ ≤ Matrix.orthogonalGroup (Fin r) ℝ :=
    fun _ hA ↦ hA.1
  exact Topology.IsInducing.isTopologicalGroup
    (G := Matrix.orthogonalGroup (Fin r) ℝ)
    (H := Matrix.specialOrthogonalGroup (Fin r) ℝ) (Submonoid.inclusion h)
    (Topology.IsEmbedding.inclusion h).isInducing

/-- The standard SO(r) to O(r) inclusion is the same underlying real matrix. -/
def specialOrthogonalGroupInclusion (r : ℕ) :
    Matrix.specialOrthogonalGroup (Fin r) ℝ →ₜ* Matrix.orthogonalGroup (Fin r) ℝ where
  toMonoidHom := Submonoid.inclusion (fun _ hA ↦ hA.1)
  continuous_toFun := continuous_subtype_val.subtype_mk (fun A ↦ A.prop.1)

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The actual sphere de Rham index with its kernel and quotient actions precomposed by φ. -/
def restrictedOrthogonalSphereDeRhamIndex (r : ℕ)
    (φ : H →ₜ* Matrix.orthogonalGroup (Fin r) ℝ) : RepresentationGrothendieckGroup H :=
  let h := exists_orthogonalSphereHodgeRepresentations r
  finiteRepresentationClass (h.choose.restrict φ) -
    finiteRepresentationClass (h.choose_spec.choose.restrict φ)

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the same restricted harmonic and quotient representation
-- coordinates.
/-- Any finite coordinates intertwining the same restricted kernel and cokernel actions
give the index. -/
theorem restrictedOrthogonalSphereDeRhamIndex_eq (r : ℕ)
    (φ : H →ₜ* Matrix.orthogonalGroup (Fin r) ℝ)
    (ρ τ : FiniteContinuousRepresentation H)
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ]
      LinearMap.ker (positiveHodgeDirac (orthogonalSphereRoundMetric r)))
    (f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ]
      PositiveHodgeCokernel (orthogonalSphereRoundMetric r))
    (he : ∀ (a : H) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation a v)).val =
        orthogonalSphereEvenFormRepresentation r (φ a) (e v).val)
    (hf : ∀ (a : H)
        (v : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)),
      f (τ.representation a
          (f.symm ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ v))) =
        (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ
          (orthogonalSphereOddFormRepresentation r (φ a) v)) :
    restrictedOrthogonalSphereDeRhamIndex r φ =
      finiteRepresentationClass ρ - finiteRepresentationClass τ := by
  /- Stage 1: retain the actual kernel and quotient coordinate equivalences
  from exists_orthogonalSphereHodgeRepresentations. Evaluate their original
  O(r)-intertwining equations at the very same matrix φ(a). This proves that
  the two precomposed finite representations used in the definition are the
  representations of H on this same kernel and this same smooth range quotient.
  Their joint continuity is the existing continuous-precomposition construction.
  Stage 2: compare e with those chosen kernel coordinates. Their composite
  intertwines the full H actions on the actual kernel. Compare f with the chosen
  quotient coordinates in the same way, using surjectivity of the original
  range quotient to check its action on every class. Finite linear equivalences
  are continuous, so the representation isomorphism relations identify the
  two pairs of classes. Subtraction gives the claimed intrinsic analytic index.
  No equality of dimensions substitutes for representation equivalence. -/
  classical
  let hex := exists_orthogonalSphereHodgeRepresentations r
  let ρ₀ := hex.choose
  let τ₀ := hex.choose_spec.choose
  obtain ⟨e₀, f₀, he₀, hf₀⟩ := hex.choose_spec.choose_spec
  -- Compare kernel coordinates on the same even forms, at the original matrix φ(a).
  have hρ : (ρ₀.restrict φ).IsEquivalent ρ := by
    refine ⟨ContRepresentation.Equiv.mk (e₀.trans e.symm).toContinuousLinearEquiv ?_⟩
    intro a
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    apply Subtype.val_injective
    change (e (e.symm (e₀ (ρ₀.representation (φ a) v)))).val =
      (e (ρ.representation a (e.symm (e₀ v)))).val
    -- The kernel coordinate equations intertwine the two actual actions.
    exact (congrArg Subtype.val (e.apply_symm_apply _)).trans
      ((he₀ (φ a) v).trans
        (((he a (e.symm (e₀ v))).trans
          (congrArg (fun w : LinearMap.ker
              (positiveHodgeDirac (orthogonalSphereRoundMetric r)) ↦
            orthogonalSphereEvenFormRepresentation r (φ a) w.val)
              (e.apply_symm_apply (e₀ v)))).symm))
  -- Both quotient actions are tested on one representative of the actual range quotient.
  have quotientCompare (τ₀ : FiniteContinuousRepresentation
        (Matrix.orthogonalGroup (Fin r) ℝ))
      (f₀ : (Fin τ₀.dimension → ℂ) ≃ₗ[ℂ]
        PositiveHodgeCokernel (orthogonalSphereRoundMetric r))
      (hf₀ : ∀ (a : Matrix.orthogonalGroup (Fin r) ℝ)
          (v : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)),
        f₀ (τ₀.representation a
            (f₀.symm ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ v))) =
          (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ
            (orthogonalSphereOddFormRepresentation r a v)) :
      (τ₀.restrict φ).IsEquivalent τ := by
    refine ⟨ContRepresentation.Equiv.mk (f₀.trans f.symm).toContinuousLinearEquiv ?_⟩
    intro a
    apply ContinuousLinearMap.ext
    intro v
    apply f.injective
    change f (f.symm (f₀ (τ₀.representation (φ a) v))) =
      f (τ.representation a (f.symm (f₀ v)))
    refine (f.apply_symm_apply _).trans ?_
    obtain ⟨w, hw⟩ := (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ_surjective
      (f₀ v)
    have h₀ := hf₀ (φ a) w
    have h₁ := hf a w
    have hsource : f₀.symm
        ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ w) = v :=
      (congrArg f₀.symm hw).trans (f₀.symm_apply_apply v)
    have hleft := (congrArg (fun z ↦ f₀ (τ₀.representation (φ a) z)) hsource).symm.trans h₀
    have hright := (congrArg (fun z ↦ f (τ.representation a (f.symm z))) hw).symm.trans h₁
    exact hleft.trans hright.symm
  have hτ := quotientCompare τ₀ f₀ hf₀
  -- The two actual intertwiners identify the finite representation classes separately.
  change finiteRepresentationClass (ρ₀.restrict φ) -
    finiteRepresentationClass (τ₀.restrict φ) = _
  exact congrArg₂ (fun a b : RepresentationGrothendieckGroup H ↦ a - b)
    (finiteRepresentationClass_eq_of_isEquivalent _ _ hρ)
    (finiteRepresentationClass_eq_of_isEquivalent _ _ hτ)

/-- Restricting the actual kernel and cokernel actions agrees with
representation-ring restriction. -/
theorem restrictedOrthogonalSphereDeRhamIndex_eq_restriction (r : ℕ)
    (φ : H →ₜ* Matrix.orthogonalGroup (Fin r) ℝ) :
    restrictedOrthogonalSphereDeRhamIndex r φ =
      representationRestrictionRingHom φ (orthogonalSphereDeRhamIndex r) := by
  /- Both analytic-index definitions use the same original finite coordinates
  on the kernel and smooth quotient-cokernel. The restricted definition changes
  only the group action, by precomposing each with φ. The established generator
  formula for representationRestriction sends each original finite class to
  exactly that precomposed representation, retaining its dimension, coordinates
  and joint continuity. The restriction ring homomorphism is the same additive
  restriction map; its preservation of subtraction gives the displayed equality.
  The preceding coordinate theorem supplies its actual analytic interpretation. -/
  -- Restriction sends each finite representation class to its precomposed class.
  have h (ρ τ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ)) :
      finiteRepresentationClass (ρ.restrict φ) - finiteRepresentationClass (τ.restrict φ) =
        representationRestriction φ
          (finiteRepresentationClass ρ - finiteRepresentationClass τ) := by
    rw [map_sub, representationRestriction_finiteClass, representationRestriction_finiteClass]
  exact h (exists_orthogonalSphereHodgeRepresentations r).choose
    (exists_orthogonalSphereHodgeRepresentations r).choose_spec.choose

/-- Rotation of S2 by the native SO(2) group has actual de Rham index two. -/
theorem specialOrthogonalTwoSphereDeRhamIndex_eq_two :
    restrictedOrthogonalSphereDeRhamIndex 2 (specialOrthogonalGroupInclusion 2) = 2 := by
  /- Stage 1: the full O(2) index on the same round S2 operator is the sum of
  its trivial degree-zero line and its determinant top-degree line, by the
  established sphere Hodge calculation. Its top action is not trivial on O(2).
  Stage 2: restrict both actual kernel and quotient representations through the
  native SO(2) inclusion, using the explicit analytic restriction comparison.
  Every included matrix has determinant one by its original subtype condition,
  so the restricted determinant representation is exactly the trivial line.
  The existing representation-ring unit and sum laws yield two units.
  No orientation-reversing element is silently included in the acting group. -/
  -- Restrict the same full orthogonal index along the original matrix inclusion.
  rw [restrictedOrthogonalSphereDeRhamIndex_eq_restriction,
    orthogonalSphereDeRhamIndex_eq_one_add_det 2 (by decide)]
  have hdet : FiniteContinuousRepresentation.IsEquivalent
      ((orthogonalDeterminantRepresentation 2).restrict (specialOrthogonalGroupInclusion 2))
      (FiniteContinuousRepresentation.trivial (G :=
        Matrix.specialOrthogonalGroup (Fin 2) ℝ)) := by
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ (Fin 1 → ℂ)) ?_⟩
    intro A
    ext v i
    have hA : A.val.det = 1 := A.property.2
    change (A.val.det : ℂ) * v i = v i
    rw [hA, Complex.ofReal_one, one_mul]
  -- The determinant line becomes the actual trivial line, whose class is the ring unit.
  have hclass : representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
      (finiteRepresentationClass (orthogonalDeterminantRepresentation 2)) = 1 := by
    change representationRestriction (specialOrthogonalGroupInclusion 2)
      (finiteRepresentationClass (orthogonalDeterminantRepresentation 2)) = _
    rw [representationRestriction_finiteClass,
      finiteRepresentationClass_eq_of_isEquivalent _ _ hdet]
    rfl
  simp only [even_two, Even.neg_pow, one_pow, one_mul, map_add, map_one, hclass]
  norm_num

/-- Reflection of S1 by O(1) has actual de Rham index one minus its determinant line. -/
theorem orthogonalCircleDeRhamIndex_eq_one_sub_det :
    orthogonalSphereDeRhamIndex 1 =
      1 - finiteRepresentationClass (orthogonalDeterminantRepresentation 1) := by
  /- For the original circle action diag(a,1), the even harmonic kernel is
  the trivial H0 line and the odd harmonic quotient-cokernel is the determinant
  H1 line. The actual Hodge and quotient maps already intertwine these actions.
  Specialize the full sphere index formula to r=1; its sign is minus one.
  Thus reflection contributes minus one on H1, and subtraction gives 1-det
  in R(O(1)). This is the source's sign representation ξ, with no replacement
  by an action carrying only the same ordinary dimension. -/
  -- The odd top-degree line contributes with its actual negative Euler sign.
  simpa only [pow_one, neg_one_mul, sub_eq_add_neg] using
    orthogonalSphereDeRhamIndex_eq_one_add_det 1 (by decide)

end AtiyahSinger
