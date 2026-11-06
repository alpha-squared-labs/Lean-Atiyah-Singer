/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Checking smooth bundle actions in a covering family of native frames

Public module ID: M1394.

Joint smoothness can be verified on any covering family from the given native
bundle atlas. The proof changes the source and target frames separately on
the actual moving overlap. This permits product tensor frames to certify the
smooth action on an already specified native tensor bundle, without changing
that bundle's smooth structure or its original continuous action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff BigOperators Topology

set_option maxSynthPendingDepth 30

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℂ (Fin r)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Change both original frames through the supplied covering frames on one moving neighborhood.
/-- Smooth columns in covering native frames imply smoothness in the entire original atlas. -/
theorem EquivariantStructure.IsSmooth.of_frameCover
    (σ : letI := modelTopology V E; EquivariantStructure G E)
    {ι : Type*} (t : ι → Trivialization V (π V E))
    (ht : ∀ i, MemTrivializationAtlas (t i))
    (hcover : ∀ x : M, ∃ i, x ∈ (t i).baseSet)
    (hcolumns : letI := modelTopology V E
      ∀ (i l : ι) (j : Fin r),
      ContMDiffOn (IG.prod I) 𝓘(ℝ, V) ∞
        (fun p : G × M ↦ ((t l) ⟨p.1 • p.2,
          σ.linearMap p.1 p.2 ((t i).symmL ℂ p.2 (EuclideanSpace.single j 1))⟩).2)
        {p : G × M | p.2 ∈ (t i).baseSet ∧ p.1 • p.2 ∈ (t l).baseSet}) :
    σ.IsSmooth (n := n) (r := r) IG := by
  classical
  let := modelTopology V E
  intro e f he hf j p hp
  let := he
  let := hf
  obtain ⟨i, hi⟩ := hcover p.2
  obtain ⟨l, hl⟩ := hcover (p.1 • p.2)
  let := ht i
  let := ht l
  have hact : ContMDiff (IG.prod I) I ∞ (fun z : G × M ↦ z.1 • z.2) :=
    contMDiff_smul
  -- Both native transition matrices are smooth at the specified source and target points.
  have hinput := ((IsSmoothComplexBundle.contMDiffOn_coordChange
    (n := n) (E := E) e (t i)).contMDiffAt
      ((e.open_baseSet.inter (t i).open_baseSet).mem_nhds ⟨hp.1, hi⟩)).comp p
        (show ContMDiffAt (IG.prod I) I ∞ (Prod.snd : G × M → M) p from
          contMDiffAt_snd)
  have houtput := ((IsSmoothComplexBundle.contMDiffOn_coordChange
    (n := n) (E := E) (t l) f).contMDiffAt
      (((t l).open_baseSet.inter f.open_baseSet).mem_nhds ⟨hl, hp.2⟩)).comp p
        hact.contMDiffAt
  have hmoveOpen : IsOpen {z : G × M |
      z.2 ∈ (t i).baseSet ∧ z.1 • z.2 ∈ (t l).baseSet} :=
    ((t i).open_baseSet.preimage continuous_snd).inter
      ((t l).open_baseSet.preimage continuous_smul)
  have hsum : ContMDiffAt (IG.prod I) 𝓘(ℝ, V) ∞
      (fun z : G × M ↦ ∑ a : Fin r,
        (e.coordChangeL ℂ (t i) z.2 (EuclideanSpace.single j 1)) a •
          ((t l).coordChangeL ℂ f (z.1 • z.2)
            (((t l) ⟨z.1 • z.2, σ.linearMap z.1 z.2
              ((t i).symmL ℂ z.2 (EuclideanSpace.single a 1))⟩).2))) p := by
    apply ContMDiffAt.sum
    intro a _
    have hcolumn := (hcolumns i l a).contMDiffAt (hmoveOpen.mem_nhds ⟨hi, hl⟩)
    have heval : ContDiff ℝ ∞
        (fun z : ((V →L[ℂ] V) × (V →L[ℂ] V)) × V ↦
          (z.1.1 (EuclideanSpace.single j 1)) a • z.1.2 z.2) := by
      let D := ((V →L[ℂ] V) × (V →L[ℂ] V)) × V
      have hA : ContDiff ℂ ∞ (fun z : D ↦ z.1.1 (EuclideanSpace.single j 1)) :=
        (show ContDiff ℂ ∞ (fun z : D ↦ z.1.1) from contDiff_fst.fst).clm_apply
          contDiff_const
      have hB : ContDiff ℂ ∞ (fun z : D ↦ z.1.2 z.2) :=
        (show ContDiff ℂ ∞ (fun z : D ↦ z.1.2) from contDiff_fst.snd).clm_apply
          contDiff_snd
      exact (((EuclideanSpace.proj a).contDiff.comp hA).smul hB).restrict_scalars ℝ
    exact heval.comp_contMDiffAt ((hinput.prodMk_space houtput).prodMk_space hcolumn)
  -- Finite expansion in the source covering frame identifies this smooth expression exactly.
  apply (hsum.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_baseSet.preimage continuous_snd |>.mem_nhds hp.1,
    f.open_baseSet.preimage continuous_smul |>.mem_nhds hp.2,
    (t i).open_baseSet.preimage continuous_snd |>.mem_nhds hi,
    (t l).open_baseSet.preimage continuous_smul |>.mem_nhds hl] with z hez hfz hiz hlz
  let u := e.symmL ℂ z.2 (EuclideanSpace.single j 1)
  let c := (t i).continuousLinearMapAt ℂ z.2 u
  have hexpand : ∑ a : Fin r, c a • EuclideanSpace.single a 1 = c := by
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr c
  have hu : ∑ a : Fin r, c a • (t i).symmL ℂ z.2 (EuclideanSpace.single a 1) = u := by
    have hh := congrArg ((t i).symmL ℂ z.2) hexpand
    simpa only [map_sum, map_smul] using
      hh.trans ((t i).symmL_continuousLinearMapAt hiz u)
  have hc : e.coordChangeL ℂ (t i) z.2 (EuclideanSpace.single j 1) = c := by
    change e.coordChangeL ℂ (t i) z.2 (EuclideanSpace.single j 1) =
      (t i).continuousLinearMapAt ℂ z.2 (e.symmL ℂ z.2 (EuclideanSpace.single j 1))
    rw [e.coordChangeL_apply (R := ℂ) (t i) ⟨hez, hiz⟩,
      ← (t i).continuousLinearMapAt_apply_of_mem ℂ hiz, e.symmL_apply hez]
  rw [hc]
  have htarget (v : E (z.1 • z.2)) :
      (t l).coordChangeL ℂ f (z.1 • z.2) (((t l) ⟨z.1 • z.2, v⟩).2) =
        (f ⟨z.1 • z.2, v⟩).2 := by
    rw [(t l).coordChangeL_apply (R := ℂ) f ⟨hlz, hfz⟩,
      ← (t l).continuousLinearMapAt_apply_of_mem ℂ hlz,
      ← (t l).symmL_apply (R := ℂ) hlz,
      (t l).symmL_continuousLinearMapAt (R := ℂ) hlz]
  simp_rw [htarget, ← f.continuousLinearMapAt_apply_of_mem ℂ hfz]
  have hh := congrArg (fun v : E z.2 ↦
    f.continuousLinearMapAt ℂ (z.1 • z.2) (σ.linearMap z.1 z.2 v)) hu
  simpa only [map_sum, map_smul] using hh.symm

end AtiyahSinger.ComplexBundle
