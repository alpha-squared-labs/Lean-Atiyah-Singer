/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianProjectiveBundle

/-!
# Pullback of the actual Hermitian projective bundle

Public module ID: M1899.

The native pullback retains the same fiber vectors and the same orthogonal
projection. Its metric is the original metric evaluated at the image base point.
The projective map and tautological comparison therefore preserve the actual
projector and range, rather than merely identifying their isomorphism classes.

Source: the pullback construction for vector and projective bundles, Hatcher,
Vector Bundles and K-Theory, Sections 1.1 and 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (r : ℕ) {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E) (f : C(Y, X))

attribute [local instance] sumTopology

local instance : ∀ y : Y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))

local instance : ∀ y : Y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))

local instance : FiberBundle (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f

local instance : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f

/-- The original metric on the native pullback, with its original fiber norms and topology. -/
def hermitianProjectivePullbackMetric :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E)
    ContinuousHermitianMetric ((f : Y → X) *ᵖ E) := by
  let V := EuclideanSpace ℂ (Fin r)
  let F := (f : Y → X) *ᵖ E
  letI := modelTopology V E
  letI := modelTopology V F
  have hlift : Continuous (fun z : TotalSpace Unit F ↦
      (⟨f z.proj, z.snd⟩ : TotalSpace Unit E)) :=
    (continuous_unitTotalEquiv_symm V E).comp
      ((Pullback.continuous_lift V E f).comp (continuous_unitTotalEquiv V F))
  refine
    { toCore := fun y ↦ h.toCore (f y)
      continuous_pairing := ?_
      isFiniteRank := isFiniteRank_model V F }
  have hpair : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦
      (⟨f z.proj, z.snd⟩ : TotalSpace Unit (E ×ᵇ E))) := by
    apply continuous_induced_rng.mpr
    exact (hlift.comp (continuous_sum_fst (E := F) (F := F))).prodMk
      (hlift.comp (continuous_sum_snd (E := F) (F := F)))
  exact h.continuous_pairing.comp hpair

attribute [local instance] hermitianProjectiveTopology hermitianProjectiveLineTopology

/-- The projective map of a native pullback keeps the original orthogonal projector. -/
def hermitianProjectivePullback :
    C(HermitianProjectiveBundle r ((f : Y → X) *ᵖ E)
      (hermitianProjectivePullbackMetric r E h f), HermitianProjectiveBundle r E h) where
  toFun p := ⟨f p.1, p.2⟩
  continuous_toFun := by
    let V := EuclideanSpace ℂ (Fin r)
    let F := (f : Y → X) *ᵖ E
    let Q := HermitianProjectiveBundle r F (hermitianProjectivePullbackMetric r E h f)
    have hc : Continuous (fun p : Q ↦
        (p.1, (⟨p.1, p.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun y ↦ F y →L[ℂ] F y)))) :=
      continuous_induced_dom
    have hlift : Continuous (fun p : Q ↦
        (⟨f p.1, p.2.val⟩ : TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x))) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
      refine ⟨f.continuous.continuousAt.comp hc.fst.continuousAt, ?_⟩
      have hcoord := (continuousAt_hom_bundle (RingHom.id ℂ) _ (x₀ := p)).mp
        hc.snd.continuousAt
      apply hcoord.2.congr_of_eventuallyEq
      let e := trivializationAt V E (f p.1)
      have hnear : ∀ᶠ q : Q in nhds p, f q.1 ∈ e.baseSet :=
        (f.continuous.comp hc.fst).continuousAt.eventually
          (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E (f p.1)))
      filter_upwards [hnear] with q hq
      apply ContinuousLinearMap.ext
      intro v
      change (e.continuousLinearMapAt ℂ (f q.1))
          (q.2.val (e.symmL ℂ (f q.1) v)) =
        ((e.pullback f).continuousLinearMapAt ℂ q.1)
          (q.2.val ((e.pullback f).symmL ℂ q.1 v))
      rw [e.continuousLinearMapAt_apply_of_mem ℂ hq,
        (e.pullback f).continuousLinearMapAt_apply_of_mem ℂ hq,
        e.symmL_apply hq, (e.pullback f).symmL_apply hq]
      congr 3
      rw [(e.pullback f).symm_apply hq]
      rfl
    exact continuous_induced_rng.mpr ((f.continuous.comp hc.fst).prodMk hlift)

/-- The native projective pullback map commutes with the original base projections. -/
theorem hermitianProjectiveProjection_comp_pullback :
    (hermitianProjectiveProjection r E h).comp (hermitianProjectivePullback r E h f) =
      f.comp (hermitianProjectiveProjection r ((f : Y → X) *ᵖ E)
        (hermitianProjectivePullbackMetric r E h f)) := rfl

end AtiyahSinger.ComplexBundle
