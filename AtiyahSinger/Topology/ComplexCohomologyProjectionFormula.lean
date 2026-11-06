/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.ComplexBundleCohomologyThom

/-!
# Projection formula for the specified complex Thom inverse

Public module ID: M1703.

The original zero-section map is multiplication by its actual oriented Thom
class. Cup associativity gives its module law. The original native total-space
homeomorphism preserves the same support action, and cancellation of the two
specified inverse maps yields the projection formula for the original complex
fiber integral. The canonical orientation is never replaced by a chosen inverse.

Source: Hatcher, Algebraic Topology, Section 3.3; SG III.12.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (r : ℕ)
  (hr : ∀ x, Module.finrank ℂ (E x) = r)

omit [T2Space X] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same complex Thom map intertwines the ordered base cup and supported action. -/
theorem complexCohomologyThomMap_cup (p q : ℕ)
    (a : singularCohomology ℚ X p) (b : singularCohomology ℚ X q) :
    (eqToIso (by rw [Nat.add_assoc]) :
        compactSupportCohomology ℚ (TotalSpace Unit E) ((p + q) + 2 * r) ≅
          compactSupportCohomology ℚ (TotalSpace Unit E) (p + (q + 2 * r))).hom
      (h.complexCohomologyThomMap r hr (p + q) (singularCohomologyCup ℚ X p q a b)) =
    compactSupportCohomologyAction ℚ (TotalSpace Unit E) p (q + 2 * r)
      (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a)
      (h.complexCohomologyThomMap r hr q b) := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let F := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E F
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let o := (h.complexCohomologyOrientation r hr).rationalization
  let e := nativeModelTotalHomeomorph E F
  let P (n : ℕ) := compactSupportCohomologyHomeomorphEquiv ℚ e n
  let U := compactSupportCohomologyThomClass ℚ (2 * r) E o
  have hzero (n : ℕ) (c : singularCohomology ℚ X n) :
      cohomologyZeroSectionPushforward ℚ (2 * r) E o n c =
      compactSupportCohomologyAction ℚ (TotalSpace F E) n (2 * r)
        (singularCohomologyPullback ℚ (bundleProjection (2 * r) E) n c) U := by
    dsimp only [U, compactSupportCohomologyThomClass]
    rw [compactSupportCohomologyAction_representative]
    rfl
  have hcast {m n : ℕ} (hmn : m = n)
      (c : compactSupportCohomology ℚ (TotalSpace Unit E) m) :
      P n ((eqToIso (by rw [hmn]) : compactSupportCohomology ℚ (TotalSpace Unit E) m ≅
        compactSupportCohomology ℚ (TotalSpace Unit E) n).hom c) =
      (eqToIso (by rw [hmn]) : compactSupportCohomology ℚ (TotalSpace F E) m ≅
        compactSupportCohomology ℚ (TotalSpace F E) n).hom (P m c) := by
    subst n
    rfl
  have hthom (n : ℕ) (c : singularCohomology ℚ X n) :
      P (n + 2 * r) (h.complexCohomologyThomMap r hr n c) =
        cohomologyZeroSectionPushforward ℚ (2 * r) E o n c :=
    (P (n + 2 * r)).apply_symm_apply _
  -- Compare on the same native total space; the actual homeomorphism preserves the action.
  apply (P (p + (q + 2 * r))).injective
  rw [hcast (Nat.add_assoc p q (2 * r)), hthom]
  change _ = compactSupportCohomologyHomeomorphPullback ℚ e (p + (q + 2 * r)) _
  rw [compactSupportCohomologyHomeomorphPullback_action]
  change _ = compactSupportCohomologyAction ℚ (TotalSpace F E) p (q + 2 * r)
    (singularCohomologyPullback ℚ ⟨e, e.continuous⟩ p
      (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a))
    (P (q + 2 * r) (h.complexCohomologyThomMap r hr q b))
  rw [hthom, hzero, hzero]
  have hproj : singularCohomologyPullback ℚ ⟨e, e.continuous⟩ p
      (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a) =
      singularCohomologyPullback ℚ (bundleProjection (2 * r) E) p a := by
    change (((singularCohomologyFunctor ℚ p).map _ ≫
      (singularCohomologyFunctor ℚ p).map _) a) = _
    rw [← Functor.map_comp]
    rfl
  rw [hproj, singularCohomologyPullback_cup]
  exact compactSupportCohomologyAction_assoc ℚ (TotalSpace F E) p q (2 * r)
    (singularCohomologyPullback ℚ (bundleProjection (2 * r) E) p a)
    (singularCohomologyPullback ℚ (bundleProjection (2 * r) E) q b) U

/-- The specified complex fiber integral satisfies the ordered projection formula. -/
theorem complexCohomologyFiberIntegral_action (p q : ℕ)
    (a : singularCohomology ℚ X p)
    (b : compactSupportCohomology ℚ (TotalSpace Unit E) (q + 2 * r)) :
    h.complexCohomologyFiberIntegral r hr (p + q)
      ((eqToIso (by rw [Nat.add_assoc]) :
          compactSupportCohomology ℚ (TotalSpace Unit E) ((p + q) + 2 * r) ≅
            compactSupportCohomology ℚ (TotalSpace Unit E) (p + (q + 2 * r))).inv
        (compactSupportCohomologyAction ℚ (TotalSpace Unit E) p (q + 2 * r)
          (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a) b)) =
      singularCohomologyCup ℚ X p q a (h.complexCohomologyFiberIntegral r hr q b) := by
  -- Express the same supported b by this very Thom inverse, then use the just-proved module law.
  rw [← h.complexCohomologyThomMap_fiberIntegral r hr q b,
    ← h.complexCohomologyThomMap_cup, Iso.hom_inv_id_apply,
    h.complexCohomologyFiberIntegral_thomMap,
    h.complexCohomologyFiberIntegral_thomMap]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
