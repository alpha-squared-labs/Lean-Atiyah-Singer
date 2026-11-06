/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothEquivariantBundleLocal
public import AtiyahSinger.Topology.EquivariantBundleActionGluing

/-!
# Gluing smooth actions on invariant open sets

Public module ID: M1391.

Two compatible actions on the actual restrictions of one bundle glue to a
jointly smooth action. The conclusion retains their original total vectors,
so it is suitable for gluing an interior bundle action to a specified exterior
representation in relative analytic excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 35

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

set_option maxHeartbeats 1800000 in
-- Compare both native pullback topologies and their actual moving matrix columns.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible jointly smooth actions on two invariant opens glue on the same bundle. -/
theorem EquivariantStructure.exists_smooth_gluing
    (U W : Opens M) (hcover : (U : Set M) ∪ (W : Set M) = Set.univ)
    [MulAction G U] [ContinuousSMul G U] [ContMDiffSMul IG I ∞ G U]
    [MulAction G W] [ContinuousSMul G W] [ContMDiffSMul IG I ∞ G W]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • (x : M))
    (hW : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M))
    (σ : letI := modelTopology V ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      EquivariantStructure G ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E))
    (τ : letI := modelTopology V ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E)
      EquivariantStructure G ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E))
    (hσ : σ.IsSmooth (M := U) (n := n) (r := r) IG)
    (hτ : τ.IsSmooth (M := W) (n := n) (r := r) IG)
    (hagree :
      letI := modelTopology V ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      letI := modelTopology V ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E)
      ∀ (g : G) (x : M) (hx : x ∈ U) (hy : x ∈ W) (v : E x),
      (⟨((g • (⟨x, hx⟩ : U) : U) : M), σ.linearMap g ⟨x, hx⟩ v⟩ : TotalSpace Unit E) =
        ⟨((g • (⟨x, hy⟩ : W) : W) : M), τ.linearMap g ⟨x, hy⟩ v⟩) :
    letI := modelTopology V E
    letI := modelTopology V ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
    letI := modelTopology V ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E)
    ∃ ρ : EquivariantStructure G E, ρ.IsSmooth (n := n) (r := r) IG ∧
      (∀ (g : G) (x : U) (v : E x),
        (⟨g • (x : M), ρ.linearMap g x.val v⟩ : TotalSpace Unit E) =
          ⟨((g • x : U) : M), σ.linearMap g x v⟩) ∧
      ∀ (g : G) (x : W) (v : E x),
        (⟨g • (x : M), ρ.linearMap g x.val v⟩ : TotalSpace Unit E) =
          ⟨((g • x : W) : M), τ.linearMap g x v⟩ := by
  classical
  let := modelTopology V E
  let := isFiniteRank_model V E
  -- The Unit-tagged and modeled pullbacks have the same native total topology.
  have htop (S : Opens M) : modelTopology V ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E) =
      @Pullback.TotalSpace.topologicalSpace M Unit E S (Subtype.val : S → M) _
        (modelTopology V E) := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose]
    rfl
  let relabel (S : Opens M) [MulAction G S] [ContinuousSMul G S]
      (a : letI := modelTopology V ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E)
        EquivariantStructure G ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E)) :
      EquivariantStructure G ((Subtype.val : S → M) *ᵖ E) := by
    let tP : TopologicalSpace (TotalSpace Unit ((Subtype.val : S → M) *ᵖ E)) :=
      inferInstance
    let := modelTopology V ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E)
    let L := a.linearMap
    have hone := a.one_map
    have hmul := a.mul_map
    have hc := a.continuous_action
    refine { linearMap := L, one_map := hone, mul_map := hmul, continuous_action := ?_ }
    change @Continuous _ _ (@instTopologicalSpaceProd G _ _ tP) tP
      (fun p ↦ ⟨p.1 • p.2.proj, L p.1 p.2.proj p.2.snd⟩)
    rw [show tP = modelTopology V
      ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E) from (htop S).symm]
    exact hc
  obtain ⟨ρ, hρU, hρW⟩ := EquivariantStructure.exists_gluing
    (E := E) U W hcover hU hW (relabel U σ) (relabel W τ) hagree
  refine ⟨ρ, ?_, hρU, hρW⟩
  -- Transfer each smoothness certificate by equality of its actual matrix columns.
  have hlocal (S : Opens M) [MulAction G S] [ContinuousSMul G S]
      [ContMDiffSMul IG I ∞ G S]
      (hS : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M))
      (a : letI := modelTopology V ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E)
        EquivariantStructure G ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E))
      (ha : a.IsSmooth (M := S) (n := n) (r := r) IG)
      (heq :
        letI := modelTopology V ((ContinuousMap.subtypeVal (S : Set M) : S → M) *ᵖ E)
        ∀ (g : G) (x : S) (v : E x),
        (⟨g • (x : M), ρ.linearMap g x.val v⟩ : TotalSpace Unit E) =
          ⟨((g • x : S) : M), a.linearMap g x v⟩) :
      (ρ.modelPullback (ContinuousMap.subtypeVal (S : Set M)) hS).IsSmooth
        (M := S) (n := n) (r := r) IG := by
    let p : C(S, M) := ContinuousMap.subtypeVal (S : Set M)
    let := modelTopology V ((p : S → M) *ᵖ E)
    have hmaps (g : G) (x : S) (v : E x) :
        (ρ.modelPullback p hS).linearMap g x v = a.linearMap g x v := by
      exact TotalSpace.mk_injective ((g • x : S) : M)
        ((ρ.modelPullback_lift p hS g x v).trans (heq g x v))
    intro e f he hf j
    apply (ha e f j).congr
    intro z _
    change (f ⟨z.1 • z.2, (ρ.modelPullback p hS).linearMap z.1 z.2
      (e.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2 = _
    rw [hmaps]
  -- One two-member invariant cover proves joint smoothness on the original manifold.
  let S : Bool → Opens M := fun b ↦ if b then U else W
  let : ∀ b, MulAction G (S b) := fun b ↦ by cases b <;> dsimp [S] <;> infer_instance
  let : ∀ b, ContinuousSMul G (S b) := fun b ↦ by cases b <;> dsimp [S] <;> infer_instance
  let : ∀ b, ContMDiffSMul IG I ∞ G (S b) :=
    fun b ↦ by cases b <;> dsimp [S] <;> infer_instance
  have heq : ∀ (b : Bool) (g : G) (x : S b), ((g • x : S b) : M) = g • (x : M) := by
    intro b
    cases b
    · exact hW
    · exact hU
  have hcov : ∀ x : M, ∃ b, x ∈ S b := by
    intro x
    have hx : x ∈ (U : Set M) ∪ (W : Set M) := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  apply EquivariantStructure.IsSmooth.of_openCover IG ρ S hcov heq
  intro b
  cases b
  · exact hlocal W hW τ hτ hρW
  · exact hlocal U hU σ hσ hρU

end AtiyahSinger.ComplexBundle

