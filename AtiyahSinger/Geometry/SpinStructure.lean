/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinTopology
public import AtiyahSinger.Geometry.OrientedFrameBundle
public import AtiyahSinger.Topology.PrincipalBundle
public import Mathlib.Topology.Covering.Basic

/-!
# A topological spin structure on the original oriented metric bundle

Public module ID: M1458.

The data are a specified principal bundle for the original native spin group
and an equivariant two-sheeted covering of the original oriented orthogonal
frames. Equivariance uses the actual realSpinVectorRepresentation and the
fixed interleaved coordinate isometry, rather than an assumed SO action.
The frame map and the principal projection lie over the same base point.

The oriented frame topology is inherited from the original orthogonal frame
column topology. The spin group has the topology fixed in SpinTopology. The
covering condition is mathlib's IsCoveringMap and every actual fiber has
cardinality two; the cardinality condition also excludes missing fibers.

Sources: Lawson--Michelsohn, Spin Geometry, II.1, Definition 1.3, p.80;
Gilkey, Invariance Theory, section 3.3, p.165. This is the positive-even-rank
topological definition. Neither existence of spin structures nor a smooth
tangent-bundle realization is asserted.
The supplied orientation field is locally compatible whenever these data
exist: principal charts and the same continuous frame map supply local
positive frame sections, as recorded below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

variable (m : ℕ) {B P : Type*} (E : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  (o : ∀ x, Orientation ℝ (E x) (Fin (2 * m)))
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}

/-- The standard equivariant double-cover lift on the specified original principal bundle. -/
structure TopologicalSpinStructure
    [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
    (hm : 0 < m)
    (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection) where
  /-- The actual continuous lift to the original oriented orthogonal frames. -/
  frameMap : C(P, OrientedOrthogonalFrameBundle m E o)
  /-- Both original projections have exactly the same base point. -/
  frameMap_projection : ∀ p : P,
    orientedOrthogonalFrameProjection m E o (frameMap p) = projection p
  /-- The original right principal action lifts precomposition by the actual spin vector action. -/
  equivariant : ∀ (g : spinGroup (realSpinorQuadraticForm m)) (p : P)
    (v : EuclideanSpace ℝ (Fin (2 * m))),
    (⟨(frameMap (MulOpposite.op g • p)).val.1,
        (frameMap (MulOpposite.op g • p)).val.2 v⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) =
      ⟨(frameMap p).val.1,
        (frameMap p).val.2 ((realSpinorCoordinateIsometry m).symm
          (realSpinVectorRepresentation m g (realSpinorCoordinateIsometry m v)))⟩
  /-- The specified frame map is a covering for its actual source and target topologies. -/
  is_covering_map : IsCoveringMap frameMap
  /-- Every original oriented frame has exactly two preimages under the same lift. -/
  fiber_card : ∀ f : OrientedOrthogonalFrameBundle m E o,
    Nat.card {p : P // frameMap p = f} = 2

variable {m E o}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]

/-- Every base point has a local continuous positive frame from the specified spin structure. -/
theorem TopologicalSpinStructure.exists_local_frame {hm : 0 < m}
    {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
    (S : TopologicalSpinStructure m E o hm hP) (b : B) :
    ∃ U : Set B, IsOpen U ∧ b ∈ U ∧
      ∃ s : C(U, OrientedOrthogonalFrameBundle m E o),
        ∀ x : U, orientedOrthogonalFrameProjection m E o (s x) = x.val := by
  -- The identity group coordinate gives a section of the actual principal chart.
  obtain ⟨e, hb, _⟩ := hP.exists_trivialization b
  let sectionMap : C(e.baseSet, P) :=
    ⟨fun x ↦ e.toOpenPartialHomeomorph.symm (x.val, 1),
      e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun x ↦ e.mem_target.mpr x.property)⟩
  -- Compose the same principal section with the specified positive-frame lift.
  refine ⟨e.baseSet, e.open_baseSet, hb, S.frameMap.comp sectionMap, ?_⟩
  intro x
  change orientedOrthogonalFrameProjection m E o
    (S.frameMap (e.toOpenPartialHomeomorph.symm (x.val, 1))) = x.val
  rw [S.frameMap_projection]
  exact e.proj_symm_apply' x.property

end AtiyahSinger
