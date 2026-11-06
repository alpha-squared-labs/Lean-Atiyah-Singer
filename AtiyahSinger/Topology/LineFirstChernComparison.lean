/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CommonFlagChern
public import AtiyahSinger.Topology.GlobalChernLocalComparison

/-!
# The original global first Chern class on a complex line

Public module ID: M1932.

The actual line itself gives its only detecting line coordinate. The projective
coefficient characterization identifies the native rank-one Chern class with
the normalized first Chern class. The original global-to-native comparison and
the exact equality of the two Unit total topologies return this identity for
the original bundle, with the fiber norms specified by its Hermitian metric.

Source: MS section 14, the normalization of Chern classes on complex lines.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (hline : ∀ x, Module.finrank ℂ (E x) = 1)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On the original line, the global first Chern class is its normalized integral first class. -/
theorem globalChernClass_one_eq_firstChernClass_of_finrank_eq_one :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    globalChernClass E h 1 = firstChernClass E hline := by
  have hglobal := globalChernClass_pullback_eq_chernClass E h (ContinuousMap.id X)
    E h 1 hline (pullbackIdIso (E := E)).symm 1
  have hid : singularCohomologyPullback ℤ (ContinuousMap.id X) 2 =
      𝟙 (singularCohomology ℤ X 2) := (singularCohomologyFunctor ℤ 2).map_id _
  rw [hid, ModuleCat.id_apply] at hglobal
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let V := EuclideanSpace ℂ (Fin 1)
  let := nativeModelTopology E V
  let := h.nativeFiberBundle 1 hline
  let := h.nativeVectorBundle 1 hline
  let hN := h.nativeModelMetric 1
  have ht := ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := E) 1
  dsimp only at ht
  -- The actual identity coordinate detects the whole original line.
  have hlocal : chernClass 1 E hN 1 = firstChernClass E hline := by
    have hfinite : letI := modelTopology V E; IsFiniteRank E := by
      rw [show modelTopology V E = _ from ht]
      infer_instance
    let nativeTotalTopology := modelTopology V E
    let : IsFiniteRank E := hfinite
    have hc := chernClass_pullback_eq_elementarySymmetric_of_lineCoordinates 1 E hN
      (ContinuousMap.id X) (fun _ : Fin 1 ↦ E)
      (fun _ ↦ (pullbackIdIso (E := E)).toHom)
      (fun _ ↦ hline)
      (by
        intro x v hv
        simpa only [Iso.toHom, LinearEquiv.coe_coe, pullbackIdIso_apply] using hv 0) 1
    rw [hid, ModuleCat.id_apply] at hc
    have hs : singularCohomologyElementarySymmetric ℤ X
        (List.ofFn (fun _ : Fin 1 ↦ firstChernClass E hline)) 1 =
        firstChernClass E hline := by
      apply singularEvenCohomologyOf_injective ℤ X 1
      rw [singularEvenCohomologyOf_elementarySymmetric]
      simp [List.ofFn_succ, Multiset.esymm, Multiset.powersetCard_one]
    have heq := hc.trans hs
    refine heq.trans ?_
    congr 1
    exact proof_irrel_heq _ _
  exact hglobal.trans hlocal

end AtiyahSinger.ComplexBundle
