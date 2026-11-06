/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GeometricKZeroLift

/-!
# The geometric Grothendieck universal property of the existing K group

Public module ID: M1864.

identify the existing finite-projective model as the group completion
of actual finite-rank complex bundles under direct sum. Every isomorphism
invariant additive bundle function extends uniquely to this same K group.
The constructed lift uses original idempotent image bundles; the theorem
below applies it to every original bundle class by its actual presentation.
No second K group, fixed fiber rank, connectedness, finite CW hypothesis or
cancellation of an unstabilized bundle isomorphism is assumed.

Sources: Spin Geometry I.9, Propositions 9.3 and 9.4, p.59, give
the group-completion universal property. The finite-presentation/complement
route in I.9.7--9.9 supplies the comparison with the existing matrix model.
The finite-bundle carrier uses small fibers for collection formation;
existing small-model isomorphisms retain arbitrary-universe bundle inputs.
The proofs below retain the original image bundles and quotient generators.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
  IdempotentMatrix.isFiniteRank_fiber

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {G : Type*} [AddCommGroup G]
  (φ : FiniteBundle X → G)
  (hiso : ∀ E F : FiniteBundle X, Iso E.Fiber F.Fiber → φ E = φ F)
  (hsum : ∀ E F : FiniteBundle X, φ (E.sum F) = φ E + φ F)

/-- The specified matrix-induced lift has the prescribed value on every original bundle. -/
theorem bundleKZeroLift_bundle (E : FiniteBundle X) :
    bundleKZeroLift φ hiso hsum E.kZeroClass = φ E := by
  /- Stage 1: take the existing idempotent presentation of the actual
  bundle E.Fiber. Its total-space isomorphism identifies E with the
  image bundle of that same idempotent, preserving the original fibers
  up to this specified bundle isomorphism and allowing locally varying rank.
  Stage 2: the presentation identity computes E.kZeroClass as the matrix
  class of that idempotent. Apply bundleKZeroLift_image to this same matrix.
  Isomorphism invariance hiso identifies the resulting image-bundle value
  with φ E. Compactness and Hausdorffness are used in the original bundle
  presentation theorem, not to impose a constant fiber dimension. -/
  -- Evaluate at the same chosen matrix presenting this actual bundle.
  let p := idempotentPresentation (E := E.Fiber)
  change bundleKZeroLift φ hiso hsum (kZeroClass E.Fiber) = φ E
  rw [kZeroClass_eq_of_presentation p (presentationIso (E := E.Fiber)),
    bundleKZeroLift_image]
  exact hiso _ _ (presentationIso (E := E.Fiber)).symm

include hiso hsum in
/-- SG I.9.3: the existing K group is the group completion of geometric bundle classes.
Only isomorphism invariance and direct-sum additivity are required of the invariant. -/
theorem bundleKZero_universal_property :
    ∃! f : ComplexKZero X →+ G, ∀ E : FiniteBundle X, f E.kZeroClass = φ E := by
  /- Existence: use the actual bundleKZeroLift and its preceding value
  theorem. This lift descends the invariant of genuine image bundles
  through the already defined idempotent relations, rather than assuming
  an arbitrary extension as part of the input data.
  Uniqueness: the actual finite image bundles are among the supplied bundle
  inputs. Their classes are precisely the original quotient generators.
  Equality on these generators gives equality of the additive maps on the
  original free group and hence on its quotient.
  The zero-bundle value follows from additivity and the zero direct-sum
  isomorphism; it is not an extra hypothesis. The argument never infers an
  unstabilized bundle isomorphism merely from equality of K classes. -/
  refine ⟨bundleKZeroLift φ hiso hsum, bundleKZeroLift_bundle φ hiso hsum, ?_⟩
  intro f hf
  -- Image bundles are actual finite bundles, and their classes generate the original quotient.
  have hgen (p : IdempotentMatrix C(X, ℂ)) :
      f (AtiyahSinger.kZeroClass C(X, ℂ) p) =
        bundleKZeroLift φ hiso hsum (AtiyahSinger.kZeroClass C(X, ℂ) p) := by
    rw [bundleKZeroLift_image]
    have h := hf (FiniteBundle.ofFamily (fun x ↦ p.fiber x))
    change f (kZeroClass (fun x ↦ p.fiber x)) = _ at h
    rwa [kZeroClass_image] at h
  have hcomp : f.comp (QuotientAddGroup.mk' (kZeroRelations C(X, ℂ))) =
      (bundleKZeroLift φ hiso hsum).comp (QuotientAddGroup.mk' (kZeroRelations C(X, ℂ))) := by
    apply FreeAbelianGroup.lift_ext
    exact hgen
  apply AddMonoidHom.ext
  intro z
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (kZeroRelations C(X, ℂ)) z
  exact DFunLike.congr_fun hcomp w

end AtiyahSinger.ComplexBundle
