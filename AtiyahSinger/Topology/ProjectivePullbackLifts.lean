/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveLineSections
public import AtiyahSinger.Topology.ProjectiveTautologicalComparison

/-!
# Lifting actual families of lines to projective pullbacks

Public module ID: M2019.

A continuous family of original orthogonal projections over a composite base
map gives a map to the native pulled-back projective bundle. The construction
keeps the actual projector and is used for the two summand axes in a product
of projective line bundles.

Source: the universal property of pullback bundles, Hatcher, Vector Bundles
and K-Theory, Section 1.1. Continuity uses the same original local frame in
both native Hom bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X Y Z : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E) (f : C(Y, X)) (g : C(Z, Y))

local instance projectivePullbackLiftNormedAddCommGroup :
    ∀ y : Y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))

local instance projectivePullbackLiftNormedSpace : ∀ y : Y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))

local instance projectivePullbackLiftFiberBundle :
    FiberBundle (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f

local instance projectivePullbackLiftVectorBundle :
    VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- An original continuous family of projections lifts along the specified composite base map. -/
def hermitianProjectivePullbackLift
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ z : Z, HermitianProjectiveSpace (E (f (g z))) (h.toCore (f (g z))))
    (ha : Continuous (fun z ↦ (⟨f (g z), (a z).val⟩ :
      TotalSpace (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
        (fun x ↦ E x →L[ℂ] E x)))) :
    C(Z, HermitianProjectiveBundle r ((f : Y → X) *ᵖ E)
      (hermitianProjectivePullbackMetric r E h f)) where
  toFun z := ⟨g z, a z⟩
  continuous_toFun := by
    let V := EuclideanSpace ℂ (Fin r)
    let F := (f : Y → X) *ᵖ E
    have hlift : Continuous (fun z ↦ (⟨g z, (a z).val⟩ :
        TotalSpace (V →L[ℂ] V) (fun y ↦ F y →L[ℂ] F y))) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
      refine ⟨g.continuous.continuousAt, ?_⟩
      have hcoord := (continuousAt_hom_bundle (RingHom.id ℂ) _ (x₀ := z)).mp
        ha.continuousAt
      apply hcoord.2.congr_of_eventuallyEq
      let e := trivializationAt V E (f (g z))
      have hnear : ∀ᶠ w : Z in nhds z, f (g w) ∈ e.baseSet :=
        (f.continuous.comp g.continuous).continuousAt.eventually
          (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt V E (f (g z))))
      filter_upwards [hnear] with w hw
      apply ContinuousLinearMap.ext
      intro v
      change ((e.pullback f).continuousLinearMapAt ℂ (g w))
          ((a w).val ((e.pullback f).symmL ℂ (g w) v)) =
        (e.continuousLinearMapAt ℂ (f (g w)))
          ((a w).val (e.symmL ℂ (f (g w)) v))
      rw [e.continuousLinearMapAt_apply_of_mem ℂ hw,
        (e.pullback f).continuousLinearMapAt_apply_of_mem ℂ hw,
        e.symmL_apply hw, (e.pullback f).symmL_apply hw]
      rw [(e.pullback f).symm_apply hw]
      rfl
    exact continuous_induced_rng.mpr (g.continuous.prodMk hlift)

end AtiyahSinger.ComplexBundle
