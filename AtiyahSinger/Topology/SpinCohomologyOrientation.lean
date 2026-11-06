/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinStructure
public import AtiyahSinger.Topology.CohomologyEuler
public import AtiyahSinger.Topology.CohomologyRationalization
public import AtiyahSinger.Topology.GeometricCohomologyOrientation

/-!
# The normalized cohomological orientation of the original spin bundle

Public module ID: M2166.

SR05 / C03. The same specified spin frame lift gives continuous local positive
frames of the original real bundle. Their native bases give the geometric
orientation condition, hence its normalized integral cohomological orientation.
The rational Euler class is the actual coefficient change of the existing
zero-section pullback of that integral Thom class. No Euler class, orientation
generator, or equality of characteristic classes is supplied as an input.

Sources: MS section 9, pp.96--98, for geometric normalization and Euler;
SG II.1 Definition 1.3 and III.12, pp.242--243, for the same spin orientation.
The frame topology retains the original bundle columns and base coordinate.
We use the positive-even-rank spin structure already defined in the project;
this does not extend that structure to rank zero or to smooth tangent bundles.
The local compatibility theorem follows from the original frame sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

universe u v

variable {m : ℕ} {B : Type u} {P : Type v} {E : B → Type u}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

/-- The original spin frame lift supplies locally compatible positive geometric orientations. -/
theorem TopologicalSpinStructure.isLocallyCompatibleBundleOrientation
    (S : TopologicalSpinStructure m E o hm hP) :
    IsLocallyCompatibleBundleOrientation (2 * m) E o := by
  /- Stage 1: use S.exists_local_frame at each original base point. Its
  section lands in the original positive orthogonal frame subtype, and its
  projection is the original point, not a separately chosen base map.
  Stage 2: transport the standard Euclidean basis by this frame isometry.
  The defining orientation equality of the subtype says precisely that
  the transported basis has orientation o. Its columns are continuous
  in the original total space: the frame topology is induced by these
  same columns, and the projection equality only transports the fiber.
  Stage 3: these bases on the same open neighborhoods witness the native
  local compatibility condition. Neither a global frame nor a trivial
  principal spin bundle is inferred from the local sections. -/
  classical
  let := orthogonalFrameTopology (2 * m) E
  intro x
  obtain ⟨U, hU, hx, s, hs⟩ := S.exists_local_frame x
  -- Retain each original frame, merely expressing its already specified base point.
  have frame (y : U) : ∃ e : EuclideanSpace ℝ (Fin (2 * m)) ≃ₗᵢ[ℝ] E y.val,
      (s y).val = ⟨y.val, e⟩ := by
    have hp : (s y).val.1 = y.val := hs y
    rcases hframe : (s y).val with ⟨z, e⟩
    rw [hframe] at hp
    dsimp only at hp
    subst z
    exact ⟨e, rfl⟩
  choose e he using frame
  let b (y : U) : Module.Basis (Fin (2 * m)) ℝ (E y.val) :=
    (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map (e y).toLinearEquiv
  refine ⟨U, hU, hx, b, ?_, ?_⟩
  · intro y
    have hpositive := (s y).property
    rw [he y] at hpositive
    exact hpositive
  · intro j
    -- The original frame topology is induced by these very columns.
    have hframes : Continuous (fun y : U ↦ (s y).val) :=
      continuous_induced_dom.comp s.continuous
    have hcoordinates : Continuous (fun y : U ↦ ((s y).val.1,
        fun i : Fin (2 * m) ↦
          (⟨(s y).val.1, (s y).val.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
            TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E))) :=
      continuous_induced_dom.comp hframes
    have hcolumn := (continuous_apply j).comp hcoordinates.snd
    apply hcolumn.congr
    intro y
    exact congrArg (fun p : OrthogonalFrameBundle (2 * m) E ↦
      (⟨p.1, p.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)) (he y)

/-- The integral cohomological orientation normalized by the same original spin frames. -/
def TopologicalSpinStructure.integralCohomologyOrientation
    (S : TopologicalSpinStructure m E o hm hP) : CohomologyOrientation ℤ (2 * m) E :=
  geometricCohomologyOrientation (2 * m) E o S.isLocallyCompatibleBundleOrientation

/-- The normalized Euler class, rationalized after the actual integral zero-section pullback. -/
def TopologicalSpinStructure.rationalEulerClass
    (S : TopologicalSpinStructure m E o hm hP) : singularCohomology ℚ B (2 * m) :=
  singularCohomologyRationalization B (2 * m)
    (cohomologyEulerClass ℤ (2 * m) E S.integralCohomologyOrientation)

end AtiyahSinger
