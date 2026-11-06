/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.EquivariantAtlasSmoothing
public import AtiyahSinger.Geometry.EquivariantFixedRankModel
public import AtiyahSinger.Geometry.TrivialSmoothEquivariance
public import AtiyahSinger.Topology.TrivialEquivariantKTheory

/-!
# A native fixed-rank model retaining the prescribed smooth atlas

Public module ID: M1100.

First move the original finite bundle to its small continuous model and transport
the prescribed atlas through that exact isomorphism. The one-element-group case
of the existing equivariant construction then supplies native norms and frames
with smooth forward and inverse maps. Thus the comparison works for arbitrary
original fiber universes without declaring a new smooth structure compatible
by assumption. The comparison applies on constant-rank clopen components.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [CompactSpace M] [T2Space M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

set_option maxSynthPendingDepth 30 in
/-- A fixed-rank specified atlas has a small native model with both original maps smooth. -/
theorem exists_native_model_with_atlasMaps
    (A : SmoothComplexBundleAtlas (n := n) E) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E x) = r) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ e : Iso E F.Fiber,
        IsSmoothAtlasBundleMap A
          (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) e.toHom.linearMap ∧
        IsSmoothAtlasBundleMap
          (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) A
          e.symm.toHom.linearMap := by
  classical
  let := A.isFiniteRank
  let V := smallBundle E
  let e := smallBundleIso E
  let B := e.symm.smoothAtlas A
  have hrV (x : M) : Module.finrank ℂ (V.Fiber x) = r :=
    (e.linearEquiv x).finrank_eq.symm.trans (hr x)
  let := punitContMDiffSMul (n := n) (M := M)
  let : ContinuousSMul PUnit.{1} M := ⟨continuous_snd⟩
  let σ : EquivariantStructure PUnit.{1} V.Fiber := EquivariantStructure.ofSubsingleton V.Fiber
  -- The only group element is the identity, so its columns are the original transition columns.
  have hσ : σ.IsSmoothAtlas 𝓘(ℝ, PUnit.{1}) B := by
    intro i j k
    have hs := (B.contMDiffOn_coordChange i j k).comp
      (contMDiffOn_snd (I := 𝓘(ℝ, PUnit.{1}))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (M := PUnit.{1}) (N := M)
        (s := {p : PUnit.{1} × M | p.2 ∈ (B.chart i).baseSet ∧
          p.1 • p.2 ∈ (B.chart j).baseSet})) (fun _ hx ↦ hx)
    apply hs.congr
    intro p hp
    rw [dite_eq_left hp.1]
    have hid : (⟨p.1 • p.2, σ.linearMap p.1 p.2
        ((B.frameLinearEquiv i p.2 hp.1).symm (Pi.single k 1))⟩ :
        TotalSpace Unit V.Fiber) =
          ⟨p.2, (B.frameLinearEquiv i p.2 hp.1).symm (Pi.single k 1)⟩ := by
      rw [Subsingleton.elim p.1 1]
      exact σ.one_map _ _
    rw [hid]
    exact congrArg (fun z : TotalSpace Unit V.Fiber ↦ (B.chart j z).2)
      (TotalSpace.mk_cast (F := Unit) (E := V.Fiber)
        ((B.chart i).proj_symm_apply' (x := Pi.single k 1) hp.1) _)
  obtain ⟨F, hF, _, _, f, _, hf, hfi⟩ :=
    B.exists_equivariant_smooth_model_of_rank_with_atlasMaps 𝓘(ℝ, PUnit.{1}) σ r hrV hσ
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  -- Composition keeps the original small-model map and both certified smooth inverse maps.
  refine ⟨F, hF, e.trans f, ?_, ?_⟩
  · exact hf.comp (e.symm.isSmoothAtlasBundleMap_symm_smoothAtlas A)
  · exact (e.symm.isSmoothAtlasBundleMap_smoothAtlas A).comp hfi

end AtiyahSinger.SmoothComplexBundleAtlas
