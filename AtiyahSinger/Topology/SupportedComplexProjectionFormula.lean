/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportedComplexCohomologyThom
public import AtiyahSinger.Topology.SupportedThomAction

/-!
# Projection formula with compact support on the original complex bundle

Public module ID: M2209.

The supported Thom map and its specified inverse preserve the ordinary left
action. The coefficient class has compact support on a Hausdorff base, which
need not be compact. All maps use the same Hermitian metric, canonical complex
orientation and identity-on-vectors native total-space homeomorphism.

Sources: Hatcher, Algebraic Topology, Sections 3.2--3.3; SG III.12--13.
The native-to-Unit transport is a project implementation adapter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (r : ℕ)
  (hr : ∀ x : X, Module.finrank ℂ (E x) = r)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The specified supported complex integral returns the original base class. -/
theorem supportedComplexCohomologyThomIntegral_thomMap (p : ℕ)
    (a : compactSupportCohomology ℚ X p) :
    h.supportedComplexCohomologyThomIntegral r hr p
      (h.supportedComplexCohomologyThomMap r hr p a) = a := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let o := (h.complexCohomologyOrientation r hr).rationalization
  let P := compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)
  -- Cancel the same total-space transport, then the same native Thom equivalence.
  change compactSupportCohomologyThomIntegral ℚ (2 * r) E o p
    (P (P.symm (compactSupportCohomologyThomMap ℚ (2 * r) E o p a))) = a
  rw [P.apply_symm_apply, compactSupportCohomologyThomIntegral_thomMap]

/-- The original supported Thom map recovers every class from its specified integral. -/
theorem supportedComplexCohomologyThomMap_thomIntegral (p : ℕ)
    (a : compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r)) :
    h.supportedComplexCohomologyThomMap r hr p
      (h.supportedComplexCohomologyThomIntegral r hr p a) = a := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let o := (h.complexCohomologyOrientation r hr).rationalization
  let P := compactSupportCohomologyHomeomorphEquiv ℚ
    (nativeModelTotalHomeomorph E (EuclideanSpace ℝ (Fin (2 * r)))) (p + 2 * r)
  -- No representative is selected: both specified inverses cancel on every class.
  change P.symm (compactSupportCohomologyThomMap ℚ (2 * r) E o p
    (compactSupportCohomologyThomIntegral ℚ (2 * r) E o p (P a))) = a
  rw [compactSupportCohomologyThomMap_thomIntegral, P.symm_apply_apply]

/-- The original supported complex Thom map is linear over ordinary base cohomology. -/
theorem supportedComplexCohomologyThomMap_action (p q : ℕ)
    (a : singularCohomology ℚ X p) (b : compactSupportCohomology ℚ X q) :
    (eqToIso (by rw [Nat.add_assoc]) :
        compactSupportCohomology ℚ (TotalSpace Unit E) ((p + q) + 2 * r) ≅
          compactSupportCohomology ℚ (TotalSpace Unit E) (p + (q + 2 * r))).hom
      (h.supportedComplexCohomologyThomMap r hr (p + q)
        (compactSupportCohomologyAction ℚ X p q a b)) =
    compactSupportCohomologyAction ℚ (TotalSpace Unit E) p (q + 2 * r)
      (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a)
      (h.supportedComplexCohomologyThomMap r hr q b) := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let F := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E F
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let o := (h.complexCohomologyOrientation r hr).rationalization
  let e := nativeModelTotalHomeomorph E F
  let P (n : ℕ) := compactSupportCohomologyHomeomorphEquiv ℚ e n
  have hcast {m n : ℕ} (hmn : m = n)
      (c : compactSupportCohomology ℚ (TotalSpace Unit E) m) :
      P n ((eqToIso (by rw [hmn]) : compactSupportCohomology ℚ (TotalSpace Unit E) m ≅
        compactSupportCohomology ℚ (TotalSpace Unit E) n).hom c) =
      (eqToIso (by rw [hmn]) : compactSupportCohomology ℚ (TotalSpace F E) m ≅
        compactSupportCohomology ℚ (TotalSpace F E) n).hom (P m c) := by
    subst n
    rfl
  have hthom (n : ℕ) (c : compactSupportCohomology ℚ X n) :
      P (n + 2 * r) (h.supportedComplexCohomologyThomMap r hr n c) =
        compactSupportCohomologyThomMap ℚ (2 * r) E o n c :=
    (P (n + 2 * r)).apply_symm_apply _
  -- Work on the same native total space; its homeomorphism preserves the actual action.
  apply (P (p + (q + 2 * r))).injective
  rw [hcast (Nat.add_assoc p q (2 * r)), hthom]
  change _ = compactSupportCohomologyHomeomorphPullback ℚ e (p + (q + 2 * r)) _
  rw [compactSupportCohomologyHomeomorphPullback_action]
  change _ = compactSupportCohomologyAction ℚ (TotalSpace F E) p (q + 2 * r)
    (singularCohomologyPullback ℚ ⟨e, e.continuous⟩ p
      (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a))
    (P (q + 2 * r) (h.supportedComplexCohomologyThomMap r hr q b))
  rw [hthom]
  have hproj : singularCohomologyPullback ℚ ⟨e, e.continuous⟩ p
      (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a) =
      singularCohomologyPullback ℚ (bundleProjection (2 * r) E) p a := by
    change (((singularCohomologyFunctor ℚ p).map _ ≫
      (singularCohomologyFunctor ℚ p).map _) a) = _
    rw [← Functor.map_comp]
    rfl
  rw [hproj]
  exact compactSupportCohomologyThomMap_action ℚ (2 * r) E o p q a b

/-- The same supported complex inverse satisfies the projection formula on a noncompact base. -/
theorem supportedComplexCohomologyThomIntegral_action (p q : ℕ)
    (a : singularCohomology ℚ X p)
    (b : compactSupportCohomology ℚ (TotalSpace Unit E) (q + 2 * r)) :
    h.supportedComplexCohomologyThomIntegral r hr (p + q)
      ((eqToIso (by rw [Nat.add_assoc]) :
          compactSupportCohomology ℚ (TotalSpace Unit E) ((p + q) + 2 * r) ≅
            compactSupportCohomology ℚ (TotalSpace Unit E) (p + (q + 2 * r))).inv
        (compactSupportCohomologyAction ℚ (TotalSpace Unit E) p (q + 2 * r)
          (singularCohomologyPullback ℚ ⟨π Unit E, continuous_proj (E := E)⟩ p a) b)) =
      compactSupportCohomologyAction ℚ X p q a
        (h.supportedComplexCohomologyThomIntegral r hr q b) := by
  -- Express b through this very inverse, then use the supported module law.
  rw [← h.supportedComplexCohomologyThomMap_thomIntegral r hr q b,
    ← h.supportedComplexCohomologyThomMap_action, Iso.hom_inv_id_apply,
    h.supportedComplexCohomologyThomIntegral_thomMap,
    h.supportedComplexCohomologyThomIntegral_thomMap]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
