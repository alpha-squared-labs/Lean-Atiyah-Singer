/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothEquivariantPullback

/-!
# Invariant open descent for smooth bundle actions

Public module ID: M1393.

Joint smoothness of the original continuous fiber action can be checked on
an invariant open cover. The restrictions are the existing native modeled
pullbacks, with their actual local charts and moving-fiber maps. This descent
is used to glue relative equivariant bundle realizations in analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

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

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℂ (Fin r)

set_option maxHeartbeats 1600000 in
-- Work on the actual open subtype of the product, keeping its inherited manifold charts.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Joint smoothness of a continuous bundle action descends from an invariant open cover. -/
theorem EquivariantStructure.IsSmooth.of_openCover
    (σ : letI := modelTopology V E
      EquivariantStructure G E)
    {ι : Type*} (U : ι → Opens M) (hcover : ∀ x, ∃ i, x ∈ U i)
    [∀ i, MulAction G (U i)] [∀ i, ContinuousSMul G (U i)]
    [∀ i, ContMDiffSMul IG I ∞ G (U i)]
    (heq : ∀ (i : ι) (g : G) (x : U i), ((g • x : U i) : M) = g • (x : M))
    (hσ : ∀ i, (σ.modelPullback (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, M))
      (heq i)).IsSmooth (n := n) (r := r) IG) :
    σ.IsSmooth (n := n) (r := r) IG := by
  classical
  let := modelTopology V E
  intro e f he hf j p hp
  let := he
  let := hf
  obtain ⟨i, hi⟩ := hcover p.2
  let u : C(U i, M) := ContinuousMap.subtypeVal (U i : Set M)
  let := modelTopology V ((u : U i → M) *ᵖ E)
  let ρ := σ.modelPullback u (heq i)
  have hρ : ρ.IsSmooth (n := n) (r := r) IG := hσ i
  let W : Opens (G × M) := ⟨{z | z.2 ∈ U i}, (U i).isOpen.preimage continuous_snd⟩
  let lift : W → G × U i := fun z ↦ (z.val.1, ⟨z.val.2, z.property⟩)
  have hlift : ContMDiff (IG.prod I) (IG.prod I) ∞ lift := by
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply (ContMDiff.subtypeVal_comp_iff (U i) _).mp
      exact contMDiff_snd.comp contMDiff_subtype_val
  -- Restriction uses the very same two native frames and their original matrix columns.
  let : MemTrivializationAtlas (e.pullback u) := ⟨e, he, rfl⟩
  let : MemTrivializationAtlas (f.pullback u) := ⟨f, hf, rfl⟩
  have hcolumns := hρ (e.pullback u) (f.pullback u) j
  let S : Set W := {z | z.val.2 ∈ e.baseSet ∧ z.val.1 • z.val.2 ∈ f.baseSet}
  have hbase : Continuous (fun z : G × M ↦ z.1 • z.2) := continuous_smul
  have hS : IsOpen S :=
    (e.open_baseSet.preimage (continuous_snd.comp continuous_subtype_val)).inter
      (f.open_baseSet.preimage (hbase.comp continuous_subtype_val))
  have hsmooth := hcolumns.comp hlift.contMDiffOn (s := S) (by
    intro z hz
    exact ⟨hz.1, by
      change ((lift z).1 • (lift z).2 : U i).val ∈ f.baseSet
      rw [heq i]
      exact hz.2⟩)
  have hactual := hsmooth.congr (f₁ := fun z : W ↦
    (f ⟨z.val.1 • z.val.2, σ.linearMap z.val.1 z.val.2
      (e.symmL ℂ z.val.2 (EuclideanSpace.single j 1))⟩).2) ?_
  · have hp' : (⟨p, hi⟩ : W) ∈ S := hp
    exact ((contMDiffAt_subtype_iff (U := W)
      (f := fun z : G × M ↦ (f ⟨z.1 • z.2, σ.linearMap z.1 z.2
        (e.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2) (x := ⟨p, hi⟩)).mp
      (hactual.contMDiffAt (hS.mem_nhds hp'))).contMDiffWithinAt
  · intro z hz
    have hframe : (e.pullback u).symmL ℂ (lift z).2 (EuclideanSpace.single j 1) =
        e.symmL ℂ z.val.2 (EuclideanSpace.single j 1) := by
      rw [(e.pullback u).symmL_apply (R := ℂ) hz.1, e.symmL_apply (R := ℂ) hz.1,
        (e.pullback u).symm_apply hz.1]
      rfl
    change _ = (f ⟨u ((lift z).1 • (lift z).2),
      ρ.linearMap (lift z).1 (lift z).2
        ((e.pullback u).symmL ℂ (lift z).2 (EuclideanSpace.single j 1))⟩).2
    rw [hframe]
    exact (congrArg (fun w : TotalSpace Unit E ↦
      (f (⟨w.proj, w.snd⟩ : TotalSpace V E)).2)
      (σ.modelPullback_lift u (heq i) (lift z).1 (lift z).2
        (e.symmL ℂ z.val.2 (EuclideanSpace.single j 1)))).symm

end AtiyahSinger.ComplexBundle
