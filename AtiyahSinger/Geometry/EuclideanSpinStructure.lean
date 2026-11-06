/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.EuclideanSpin
public import AtiyahSinger.Geometry.SpinStructure

/-!
# Spin structures in every real Euclidean rank

Public module ID: M1222.

A spin structure lifts the original oriented orthonormal frames by the
actual Euclidean native spin group. The frame map is a covering over the
same base and intertwines the original right action with the actual
Clifford-conjugation vector action. Its fibers have two elements when
n is positive. This includes n=1 and n=2 without a universal-cover claim.

SG II.1 Definition 1.3, p.80, states the main definition for n at least
three and separately treats n=2 and n=1. The n=2 lift uses the connected
double cover of SO(2); at n=1 it is a two-fold cover of the base. At n=0
SG II.1 gives no definition: this file explicitly extends the native
unit-generated Spin(0)={1} convention by a one-sheeted lift. The original
empty-frame orientation is necessary in that branch; an arbitrary negative
ray in mathlib's Orientation at rank zero has no positive empty frame.

In positive even rank these objects agree with the existing spin structures
through the actual Clifford and interleaved coordinate equivalences of
EuclideanSpin. The original principal carrier, topology, projection, metric
bundle, orientation and every lifted frame remain unchanged. No arbitrary
new spinor representation or orientation is chosen. The full and half-spin
bundles use the specified associated quotient carriers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] euclideanSpinGroupTopology euclideanSpinGroup_isTopologicalGroup
  spinGroupTopology spinGroup_isTopologicalGroup

section Frames

variable (n : ℕ) {B : Type*} (E : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  (o : ∀ x, Orientation ℝ (E x) (Fin n))

/-- The original positive orthogonal frames in arbitrary rank, including the empty-frame test. -/
def EuclideanOrientedFrameBundle : Type _ :=
  {p : OrthogonalFrameBundle n E //
    Orientation.map (Fin n) p.2.toLinearEquiv
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation = o p.1}

variable [TopologicalSpace B]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin n)) E)]

/-- The original orthogonal-column subspace topology, also retaining the base at rank zero. -/
@[reducible]
def euclideanOrientedFrameTopology : TopologicalSpace (EuclideanOrientedFrameBundle n E o) :=
  TopologicalSpace.induced (fun f : EuclideanOrientedFrameBundle n E o ↦ f.val)
    (orthogonalFrameTopology n E)

end Frames

attribute [local instance] euclideanOrientedFrameTopology

section Structure

variable (n : ℕ) {B P : Type*} (E : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin n)) E)]
  (o : ∀ x, Orientation ℝ (E x) (Fin n))
  [MulAction (spinGroup (euclideanSpinQuadraticForm n))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (euclideanSpinQuadraticForm n))ᵐᵒᵖ P]
  {projection : P → B}

/-- The original spin frame lift, with the explicitly separate native rank-zero endpoint. -/
structure EuclideanSpinStructure
    [FiberBundle (EuclideanSpace ℝ (Fin n)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin n)) E]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n)) E]
    (hP : IsPrincipalBundle (spinGroup (euclideanSpinQuadraticForm n)) projection) where
  /-- The actual continuous map to the original positively oriented metric frames. -/
  frameMap : C(P, EuclideanOrientedFrameBundle n E o)
  /-- Its base point is the original principal projection. -/
  frameMap_projection : ∀ p : P, (frameMap p).val.1 = projection p
  /-- The same right principal action lifts the actual native Clifford vector action. -/
  equivariant : ∀ (g : spinGroup (euclideanSpinQuadraticForm n)) (p : P)
    (v : EuclideanSpace ℝ (Fin n)),
    (⟨(frameMap (MulOpposite.op g • p)).val.1,
        (frameMap (MulOpposite.op g • p)).val.2 v⟩ :
        TotalSpace (EuclideanSpace ℝ (Fin n)) E) =
      ⟨(frameMap p).val.1, (frameMap p).val.2 (euclideanSpinVectorRepresentation n g v)⟩
  /-- Covering is for the actual unchanged source and frame topologies. -/
  is_covering_map : IsCoveringMap frameMap
  /-- Positive rank has two sheets; the native trivial group at zero rank has one. -/
  fiber_card : ∀ f : EuclideanOrientedFrameBundle n E o,
    Nat.card {p : P // frameMap p = f} = if n = 0 then 1 else 2

end Structure

section Zero

variable {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 0)) E]
  [MulAction (spinGroup (euclideanSpinQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (euclideanSpinQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}

/-- The native zero-rank lift exists precisely for the orientation of the actual empty frame. -/
theorem euclideanSpinStructure_zero_iff
    (hP : IsPrincipalBundle (spinGroup (euclideanSpinQuadraticForm 0)) projection)
    (o : ∀ x, Orientation ℝ (E x) (Fin 0)) :
    Nonempty (EuclideanSpinStructure 0 E o hP) ↔
      ∀ b : B, o b = Orientation.map (Fin 0)
        (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin 0)) E b).symm.toLinearEquiv
        (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis.orientation := by
  -- The genuine empty frame is determined by the original zero-rank bundle coordinate map.
  let R₀ := EuclideanSpace ℝ (Fin 0)
  let emptyFrame (b : B) : R₀ ≃ₗᵢ[ℝ] E b := {
    (VectorBundle.continuousLinearEquivAt ℝ R₀ E b).symm.toLinearEquiv with
    norm_map' := by
      intro v
      have hv : v = 0 := Subsingleton.elim v 0
      rw [hv, map_zero, norm_zero, norm_zero] }
  have hfiber (b : B) : Subsingleton (E b) :=
    (VectorBundle.continuousLinearEquivAt ℝ R₀ E b).injective.subsingleton
  let := hfiber
  constructor
  · -- Every positive lifted frame forces the empty-frame orientation at its base point.
    rintro ⟨S⟩ b
    obtain ⟨p, hp⟩ := hP.projection_properties.2.2 b
    have hframe : (S.frameMap p).val.2.toLinearEquiv =
        (VectorBundle.continuousLinearEquivAt ℝ R₀ E (S.frameMap p).val.1).symm.toLinearEquiv :=
      Subsingleton.elim _ _
    have ho := (S.frameMap p).property
    rw [hframe] at ho
    have hb : (S.frameMap p).val.1 = b := (S.frameMap_projection p).trans hp
    rw [hb] at ho
    exact ho.symm
  · intro ho
    -- Positive empty frames form the original base with its existing topology.
    let := orthogonalFrameTopology 0 E
    let e : B ≃ₜ EuclideanOrientedFrameBundle 0 E o := {
      toFun b := ⟨⟨b, emptyFrame b⟩, (ho b).symm⟩
      invFun f := f.val.1
      left_inv b := rfl
      right_inv f := by
        rcases f with ⟨⟨b, l⟩, hf⟩
        apply Subtype.ext
        change (⟨b, emptyFrame b⟩ : OrthogonalFrameBundle 0 E) = ⟨b, l⟩
        have hl : emptyFrame b = l := by
          ext v
          exact Subsingleton.elim _ _
        exact congrArg (fun l ↦ (⟨b, l⟩ : OrthogonalFrameBundle 0 E)) hl
      continuous_toFun := by
        apply continuous_induced_rng.mpr
        apply continuous_induced_rng.mpr
        exact continuous_id.prodMk (continuous_pi (fun i : Fin 0 ↦ Fin.elim0 i))
      continuous_invFun := by
        have hsub : Continuous (fun f : EuclideanOrientedFrameBundle 0 E o ↦ f.val) :=
          continuous_induced_dom
        have hcols : Continuous (fun f : OrthogonalFrameBundle 0 E ↦
            (f.1, fun i : Fin 0 ↦
              (⟨f.1, f.2 (EuclideanSpace.basisFun (Fin 0) ℝ i)⟩ : TotalSpace R₀ E))) :=
          continuous_induced_dom
        exact (hcols.comp hsub).fst }
    -- The native group is trivial; its original principal charts give a covering projection.
    have hsubspin : Subsingleton (spinGroup (euclideanSpinQuadraticForm 0)) := by
      refine ⟨fun g h ↦ Subtype.ext ?_⟩
      have hg := euclideanSpinGroup_zero_eq_bot.le g.property
      have hh := euclideanSpinGroup_zero_eq_bot.le h.property
      exact (Submonoid.mem_bot.mp hg).trans (Submonoid.mem_bot.mp hh).symm
    let := hsubspin
    have hcover : IsCoveringMap projection := by
      choose t ht _ using hP.exists_trivialization
      exact IsCoveringMap.mk projection (fun _ ↦ spinGroup (euclideanSpinQuadraticForm 0)) t ht
    -- Compose that projection with the actual empty-frame homeomorphism.
    let F : C(P, EuclideanOrientedFrameBundle 0 E o) :=
      ⟨fun p ↦ e (projection p), e.continuous.comp hP.projection_properties.1⟩
    refine ⟨{
      frameMap := F
      frameMap_projection := fun _ ↦ rfl
      equivariant := ?_
      is_covering_map := hcover.homeomorph_comp e
      fiber_card := ?_ }⟩
    · intro g p v
      have hg : g = 1 := Subsingleton.elim _ 1
      rw [hg, MulOpposite.op_one, one_smul, map_one]
      rfl
    · -- Freeness and transitivity of the trivial action make each frame fiber a singleton.
      intro f
      simp only [ite_true]
      apply Nat.card_eq_one_iff_unique.mpr
      refine ⟨?_, ?_⟩
      · refine ⟨fun p q ↦ Subtype.ext ?_⟩
        have hpq : projection p.val = projection q.val := e.injective
          (p.property.trans q.property.symm)
        obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p.val q.val hpq
        have hgone : g = 1 := Subsingleton.elim _ 1
        simpa only [hgone, MulOpposite.op_one, one_smul] using hg
      · obtain ⟨p, hp⟩ := hP.projection_properties.2.2 (e.symm f)
        exact ⟨⟨p, by change e (projection p) = f; rw [hp, e.apply_symm_apply]⟩⟩

end Zero

section EvenComparison

variable (m : ℕ) {B P : Type*} (E : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  (o : ∀ x, Orientation ℝ (E x) (Fin (2 * m)))
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}

/-- Changing only the spin coordinate model gives a frame-preserving equivalence of lifts. -/
theorem exists_spinStructure_even_equiv (hm : 0 < m)
    (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection) :
    ∃ action : MulAction (spinGroup (euclideanSpinQuadraticForm (2 * m)))ᵐᵒᵖ P,
      letI := action
      ∃ continuousAction :
          ContinuousSMul (spinGroup (euclideanSpinQuadraticForm (2 * m)))ᵐᵒᵖ P,
        letI := continuousAction
        ∃ hQ : IsPrincipalBundle (spinGroup (euclideanSpinQuadraticForm (2 * m))) projection,
          ∃ e : TopologicalSpinStructure m E o hm hP ≃ EuclideanSpinStructure (2 * m) E o hQ,
            (∀ (g : spinGroup (euclideanSpinQuadraticForm (2 * m))) (p : P),
              MulOpposite.op g • p = MulOpposite.op (euclideanSpinEvenEquiv m g) • p) ∧
            ∀ (S : TopologicalSpinStructure m E o hm hP) (p : P),
              (e S).frameMap p = S.frameMap p := by
  -- Transport only the group coordinates; retain the original carrier and projection.
  let eG := euclideanSpinEvenEquiv m
  let action : MulAction (spinGroup (euclideanSpinQuadraticForm (2 * m)))ᵐᵒᵖ P :=
    MulAction.compHom P (MulEquiv.op eG).toMonoidHom
  refine ⟨action, ?_⟩
  let := action
  let continuousAction : ContinuousSMul
      (spinGroup (euclideanSpinQuadraticForm (2 * m)))ᵐᵒᵖ P := {
    continuous_smul := by
      change Continuous (fun p :
        (spinGroup (euclideanSpinQuadraticForm (2 * m)))ᵐᵒᵖ × P ↦
          MulOpposite.op (eG p.1.unop) • p.2)
      exact (MulOpposite.continuous_op.comp
        ((continuous_euclideanSpinEvenEquiv m).1.comp
          (MulOpposite.continuous_unop.comp continuous_fst))).smul continuous_snd }
  refine ⟨continuousAction, ?_⟩
  let := continuousAction
  -- The same native equivalence changes each principal chart on its group coordinate.
  let eH : spinGroup (euclideanSpinQuadraticForm (2 * m)) ≃ₜ
      spinGroup (realSpinorQuadraticForm m) :=
    { eG.toEquiv with
      continuous_toFun := (continuous_euclideanSpinEvenEquiv m).1
      continuous_invFun := (continuous_euclideanSpinEvenEquiv m).2 }
  have hQ : IsPrincipalBundle (spinGroup (euclideanSpinQuadraticForm (2 * m))) projection := {
    projection_smul g p := hP.projection_smul (eG g) p
    exists_trivialization b := by
      obtain ⟨t, hb, ht⟩ := hP.exists_trivialization b
      refine ⟨t.transFiberHomeomorph eH.symm, hb, ?_⟩
      intro g p hp
      change eG.symm ((t (MulOpposite.op (eG g) • p)).2) = eG.symm (t p).2 * g
      rw [ht (eG g) p hp, map_mul, eG.symm_apply_apply] }
  refine ⟨hQ, ?_⟩
  -- Keep every lifted frame and covering; translate only the vector-action identity.
  let f : TopologicalSpinStructure m E o hm hP → EuclideanSpinStructure (2 * m) E o hQ :=
    fun S ↦ {
      frameMap := S.frameMap
      frameMap_projection := S.frameMap_projection
      equivariant := by
        intro g p v
        have h := S.equivariant (eG g) p v
        rw [← euclideanSpinEvenEquiv_vectorRepresentation] at h
        change (⟨(S.frameMap (MulOpposite.op (eG g) • p)).val.1,
          (S.frameMap (MulOpposite.op (eG g) • p)).val.2 v⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) = _
        rw [LinearIsometryEquiv.symm_apply_apply] at h
        exact h
      is_covering_map := S.is_covering_map
      fiber_card := by
        intro t
        change Nat.card {p : P // S.frameMap p = t} = if 2 * m = 0 then 1 else 2
        rw [ite_eq_right (show 2 * m ≠ 0 by omega)]
        exact S.fiber_card t }
  -- The inverse coordinate conversion restores the identical real-spinor action.
  let k : EuclideanSpinStructure (2 * m) E o hQ → TopologicalSpinStructure m E o hm hP :=
    fun T ↦ {
      frameMap := T.frameMap
      frameMap_projection := T.frameMap_projection
      equivariant := by
        intro g p v
        have h := T.equivariant (eG.symm g) p v
        have hvec : euclideanSpinVectorRepresentation (2 * m) (eG.symm g) v =
            (realSpinorCoordinateIsometry m).symm
              (realSpinVectorRepresentation m g (realSpinorCoordinateIsometry m v)) := by
          apply (realSpinorCoordinateIsometry m).injective
          rw [LinearIsometryEquiv.apply_symm_apply,
            euclideanSpinEvenEquiv_vectorRepresentation, eG.apply_symm_apply]
        rw [hvec] at h
        change (⟨(T.frameMap (MulOpposite.op g • p)).val.1,
          (T.frameMap (MulOpposite.op g • p)).val.2 v⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) = _
        change (⟨(T.frameMap (MulOpposite.op (eG (eG.symm g)) • p)).val.1,
          (T.frameMap (MulOpposite.op (eG (eG.symm g)) • p)).val.2 v⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) = _ at h
        rw [eG.apply_symm_apply] at h
        exact h
      is_covering_map := T.is_covering_map
      fiber_card := by
        intro t
        have ht := T.fiber_card t
        rw [ite_eq_right (show 2 * m ≠ 0 by omega)] at ht
        exact ht }
  -- Both round trips preserve the data literally, including the specified frame map.
  let e : TopologicalSpinStructure m E o hm hP ≃ EuclideanSpinStructure (2 * m) E o hQ :=
    { toFun := f
      invFun := k
      left_inv := by intro S; cases S; rfl
      right_inv := by intro T; cases T; rfl }
  refine ⟨e, ?_, ?_⟩
  · intro g p
    rfl
  · intro S p
    rfl

end EvenComparison

end AtiyahSinger
