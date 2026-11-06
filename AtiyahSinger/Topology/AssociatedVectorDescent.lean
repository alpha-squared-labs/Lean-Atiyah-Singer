/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteContinuousRepresentation
public import AtiyahSinger.Topology.AssociatedVectorCoordinates
public import AtiyahSinger.Topology.BundleIso

/-!
# Covariant coordinates on an associated vector bundle

Public module ID: M1561.

A continuous family of linear coordinates indexed by actual principal points,
with the original representation transformation law, identifies the original
associated quotient bundle with the specified finite-rank bundle. The returned
formula retains every representative, including the original fiber operations
and quotient total topology. No global continuous principal section is chosen.

This is a standard consequence of SG II.3 and HU IV.5, used for isomorphism,
direct-sum, tensor and trivial-line compatibility of the associated K class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G P B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology

/-- Continuous covariant coordinates identify the original associated vector bundle. -/
theorem exists_associatedVector_iso_of_covariant_equiv
    (hP : IsPrincipalBundle G projection) (ρ : FiniteContinuousRepresentation G) (E : B → Type*)
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [TopologicalSpace (Bundle.TotalSpace Unit E)] [ComplexBundle.IsFiniteRank E]
    (f : ∀ (b : B) (p : P), projection p = b → (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] E b)
    (hc : Continuous (fun z : P × (Fin ρ.dimension → ℂ) ↦
      (⟨projection z.1, f (projection z.1) z.1 rfl z.2⟩ : Bundle.TotalSpace Unit E)))
    (hcov : ∀ (b : B) (p : P) (hp : projection p = b) (g : G) (v),
      f b (MulOpposite.op g • p) ((hP.projection_smul g p).trans hp) v =
        f b p hp (ρ.representation g v)) :
    ∃ e : ComplexBundle.Iso (AssociatedVectorFiber hP ρ.representation) E,
      ∀ (b : B) (p : P) (hp : projection p = b) (v),
        e.linearEquiv b (associatedVectorFiberMk hP ρ.representation p hp v) = f b p hp v := by
  classical
  let := associatedRepresentationAction ρ.representation
  let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
  -- Choose algebraic coordinates only; their dependence on b need not be continuous.
  let p (b : B) : P := (hP.projection_properties.2.2 b).choose
  have hp (b : B) : projection (p b) = b := (hP.projection_properties.2.2 b).choose_spec
  let a (b : B) :=
    (associatedVectorFiberMkLinearEquiv hP ρ.representation (p b) (hp b)).symm.trans
      (f b (p b) (hp b))
  have hrep (b : B) (q : P) (hq : projection q = b) (v) :
      a b (associatedVectorFiberMk hP ρ.representation q hq v) = f b q hq v := by
    obtain ⟨g, hg, _⟩ := hP.existsUnique_smul (p b) q ((hp b).trans hq.symm)
    have hvec : associatedVectorFiberMk hP ρ.representation q hq v =
        associatedVectorFiberMkLinearEquiv hP ρ.representation (p b) (hp b)
          (ρ.representation g v) := by
      apply Subtype.ext
      change associatedBundleMk G P _ q v =
        associatedBundleMk G P _ (p b) (ρ.representation g v)
      rw [← hg]
      exact associatedBundleMk_smul (p b) g v
    rw [hvec]
    change f b (p b) (hp b)
      ((associatedVectorFiberMkLinearEquiv hP ρ.representation (p b) (hp b)).symm
        (associatedVectorFiberMkLinearEquiv hP ρ.representation (p b) (hp b)
          (ρ.representation g v))) = _
    rw [LinearEquiv.symm_apply_apply, ← hcov b (p b) (hp b) g v]
    subst q
    rfl
  -- Covariance makes these coordinates agree on every original quotient representative.
  let A : ComplexBundle.Hom (AssociatedVectorFiber hP ρ.representation) E :=
    { linearMap := fun b ↦ (a b).toLinearMap
      continuous_total := by
        let H := associatedVectorTotalHomeomorph hP ρ.representation
        have hquot : Continuous (fun z : AssociatedBundle G P (Fin ρ.dimension → ℂ) ↦
            (⟨(H.symm z).proj, a (H.symm z).proj (H.symm z).snd⟩ :
              Bundle.TotalSpace Unit E)) := by
          apply isQuotientMap_quotient_mk'.continuous_iff.mpr
          apply hc.congr
          intro z
          change (⟨projection z.1, f (projection z.1) z.1 rfl z.2⟩ :
            Bundle.TotalSpace Unit E) =
            ⟨projection z.1, a (projection z.1)
              (associatedVectorFiberMk hP ρ.representation z.1 rfl z.2)⟩
          rw [hrep]
        have hc := hquot.comp H.continuous
        have hfun : ((fun z ↦
            (⟨(H.symm z).proj, a (H.symm z).proj (H.symm z).snd⟩ :
              Bundle.TotalSpace Unit E)) ∘ H) =
            (fun z ↦ (⟨z.proj, a z.proj z.snd⟩ : Bundle.TotalSpace Unit E)) := by
          funext z
          exact congrArg (fun w : Bundle.TotalSpace Unit
              (AssociatedVectorFiber hP ρ.representation) ↦
            (⟨w.proj, a w.proj w.snd⟩ : Bundle.TotalSpace Unit E)) (H.symm_apply_apply z)
        rw [hfun] at hc
        exact hc }
  -- Finite local bundle charts give continuity of this same fiberwise inverse.
  exact ⟨A.toIso (fun b ↦ (a b).bijective), hrep⟩
end AtiyahSinger
