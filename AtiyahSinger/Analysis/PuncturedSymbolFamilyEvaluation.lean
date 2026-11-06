/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PuncturedSymbol
public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.ModelBundleTopology

import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous symbol families and original pullback evaluation

Public module ID: M0905.

A symbol family is jointly continuous off zero exactly when evaluating it on
vectors is continuous on the original pulled source and target total spaces.
Finite source-frame dimension recovers continuity of Hom coordinates from
continuous vector evaluation. The same original vector and base topologies are
retained throughout, with arbitrary external parameters and fiber universes.
This is the vector-bundle evaluation criterion used for continuous symbol
transport in the equivariant index homotopy argument of SG III.7 and III.9.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Filter IsManifold MeasureTheory
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Joint off-zero Hom continuity is equivalent to continuity of original vector evaluation. -/
theorem isContinuousOffZeroSymbolFamily_iff_continuous_total
    {Z : Type*} [TopologicalSpace Z] (a : Z → GlobalSymbolFunction (n := n) E F) :
    IsContinuousOffZeroSymbolFamily (r := r) (q := q) a ↔
      letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      let p : C(PuncturedCotangentBundle (n := n) (M := M), M) :=
        (cotangentProjection (n := n) (M := M)).comp ⟨Subtype.val, continuous_subtype_val⟩
      Continuous (fun z : Z × TotalSpace Unit ((p : _ → M) *ᵖ E) ↦
        (⟨z.2.proj, a z.1 z.2.proj.val.proj z.2.proj.val.snd z.2.snd⟩ :
          TotalSpace Unit ((p : _ → M) *ᵖ F))) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let W := PuncturedCotangentBundle (n := n) (M := M)
  let p : C(W, M) :=
    (cotangentProjection (n := n) (M := M)).comp ⟨Subtype.val, continuous_subtype_val⟩
  constructor
  · intro ha
    -- Continuous Hom evaluation is taken in the original target bundle, then lifted back.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    refine ((Pullback.continuous_proj Unit E p).comp continuous_snd).prodMk ?_
    apply (continuous_modelTotal_iff (EuclideanSpace ℂ (Fin q)) F _).mpr
    exact (Continuous.comp ha (continuous_fst.prodMk
      ((Pullback.continuous_proj Unit E p).comp continuous_snd))).clm_bundle_apply
        ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin r)) E).comp
          ((Pullback.continuous_lift Unit E p).comp continuous_snd))
  · intro hEval
    -- Finite original source frames test continuity of every matrix on its actual overlap.
    have hb : Continuous (fun y : Z × W ↦ p y.2) := p.continuous.comp continuous_snd
    apply continuous_iff_continuousAt.mpr
    intro y₀
    apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
    refine ⟨hb.continuousAt, ?_⟩
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E (p y₀.2)
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F (p y₀.2)
    have he₀ : p y₀.2 ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    have hf₀ : p y₀.2 ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
    have hevent : ∀ᶠ y : Z × W in 𝓝 y₀, p y.2 ∈ e.baseSet :=
      hb.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he₀)
    have hfevent : ∀ᶠ y : Z × W in 𝓝 y₀, p y.2 ∈ f.baseSet :=
      hb.continuousAt.preimage_mem_nhds (f.open_baseSet.mem_nhds hf₀)
    apply continuousAt_clm_apply.mpr
    intro v
    have hsection : ContinuousAt (fun y : Z × W ↦
        (⟨p y.2, e.symm (p y.2) v⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) y₀ := by
      have hlocal := e.continuousOn_symm.comp (hb.prodMk continuous_const).continuousOn
        (fun y (hy : p y.2 ∈ e.baseSet) ↦ ⟨hy, Set.mem_univ v⟩)
      exact hlocal.continuousAt hevent
    have hpull : ContinuousAt (fun y : Z × W ↦
        (⟨y.2, e.symm (p y.2) v⟩ : TotalSpace Unit ((p : W → M) *ᵖ E))) y₀ := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuousAt_iff]
      exact continuousAt_snd.prodMk
        ((continuous_unitTotalEquiv_symm (EuclideanSpace ℂ (Fin r)) E).continuousAt.comp
          hsection)
    have hout := hEval.continuousAt.comp (continuousAt_fst.prodMk hpull)
    have hcoord := (f.continuousAt (f.mem_source.mpr hf₀)).snd.comp
      ((continuous_unitTotalEquiv (EuclideanSpace ℂ (Fin q)) F).continuousAt.comp
        ((Pullback.continuous_lift Unit F p).continuousAt.comp hout))
    apply hcoord.congr_of_eventuallyEq
    filter_upwards [hevent, hfevent] with y hey hfy
    change (f.continuousLinearMapAt ℂ (p y.2))
      (a y.1 y.2.val.proj y.2.val.snd ((e.symmL ℂ (p y.2)) v)) =
        (f ⟨p y.2, a y.1 y.2.val.proj y.2.val.snd (e.symm (p y.2) v)⟩).2
    rw [e.symmL_apply hey]
    exact f.continuousLinearMapAt_apply_of_mem ℂ hfy _

end AtiyahSinger
