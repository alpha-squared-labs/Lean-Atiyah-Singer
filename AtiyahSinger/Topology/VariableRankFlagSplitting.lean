/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagSplitting
public import AtiyahSinger.Topology.VariableRankFlag

/-!
# The original tautological splitting on each actual rank stratum

Public module ID: M2271.

C01. Every line below is the range of the corresponding original flag
projection. Its topology is induced from the pullback of the original Unit
total-space topology. Their sum maps to the original fiber by actual vector
addition, with inverse given by those same flag projections. This is exactly
the existing fixed-rank splitting after the inverse phantom-model retypings.

The number of summands is the rank of the chosen original clopen piece. No
uniform finite rank is imposed on the entire base, and no artificial zero
lines are added over other components. Sources: SG III.11.1 and Hatcher VBKT
Proposition 3.3, applied to the original locally constant rank pieces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

attribute [local instance] rankFlagTopology isFiniteRank_restrict

/-- The i-th actual projection range in the original rank-r fiber. -/
abbrev RankFlagLine (r : ℕ) (i : Fin r) (p : RankFlagBundle E h r) : Type v :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  LinearMap.range (p.2.val i).toLinearMap

/-- The finite sum of the actual line ranges on this same original rank piece. -/
abbrev RankFlagSum (r : ℕ) (p : RankFlagBundle E h r) : Type v :=
  ∀ i : Fin r, RankFlagLine E h r i p

/-- The original pulled-back total topology induces the topology of each range line. -/
@[reducible]
def rankFlagLineTopology (r : ℕ) (i : Fin r) :
    TopologicalSpace (TotalSpace Unit (RankFlagLine E h r i)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (RankFlagLine E h r i) ↦
      (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
        ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ
          (Restrict E (rankStratum E r)))))
    inferInstance

attribute [local instance] rankFlagLineTopology

/-- The same-base finite product topology includes the base coordinate also in rank zero. -/
@[reducible]
def rankFlagSumTopology (r : ℕ) :
    TopologicalSpace (TotalSpace Unit (RankFlagSum E h r)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (RankFlagSum E h r) ↦
      (z.proj, fun i : Fin r ↦
        (⟨z.proj, z.snd i⟩ : TotalSpace Unit (RankFlagLine E h r i))))
    inferInstance

attribute [local instance] rankFlagSumTopology

/-- The original rank-piece range is a continuous complex line bundle. -/
theorem isFiniteRank_rankFlagLine (r : ℕ) (i : Fin r) :
    IsFiniteRank (RankFlagLine E h r i) := by
  set_option backward.isDefEq.respectTransparency.types false in
    /- The native-model retyping followed by modelTopology recovers the exact
    original Unit topology. It therefore also recovers its original pullback
    topology and the induced range topology used here. The actual projections
    and their ranges are definitionally those of the existing fixed-rank flag.
    Transport its isFiniteRank_hermitianFlagLine certificate across precisely
    this topology equality. Each fiber has dimension one by its defining flag
    condition, with no substitute line bundle or unrelated basis. -/
    let F := Restrict E (rankStratum E r)
    let hF := rankHermitianMetric E h r
    let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
    let := hF.nativeFiberBundle r (fun x ↦ x.property)
    let := hF.nativeVectorBundle r (fun x ↦ x.property)
    -- Both phantom-model retypings recover the exact original pullback and range topology.
    have ht : hermitianFlagLineTopology r F (hF.nativeModelMetric r) i =
        rankFlagLineTopology E h r i := by
      exact congrArg (fun t : TopologicalSpace (TotalSpace Unit F) ↦
        letI := t
        TopologicalSpace.induced
          (fun z : TotalSpace Unit (RankFlagLine E h r i) ↦
            (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
              ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ F)))
          inferInstance) (ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := F) r)
    have hl := isFiniteRank_hermitianFlagLine r F (hF.nativeModelMetric r) i
    rw [ht] at hl
    exact hl

set_option backward.isDefEq.respectTransparency.types false in
/-- Vector addition and the flag projections are inverse on the original total spaces.
Both maps are continuous in the specified line-sum and pullback topologies. -/
theorem rankFlagSplitting_properties (r : ℕ) :
    let F := Restrict E (rankStratum E r)
    let hF := rankHermitianMetric E h r
    letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    (∀ (p : RankFlagBundle E h r) (s : RankFlagSum E h r p) (i : Fin r),
      p.2.val i (∑ j, (s j).val) = (s i).val) ∧
    (∀ (p : RankFlagBundle E h r) (v : E p.1.val), (∑ i, p.2.val i v) = v) ∧
    Continuous (fun z : TotalSpace Unit (RankFlagSum E h r) ↦
      (⟨z.proj, ∑ i, (z.snd i).val⟩ : TotalSpace Unit
        ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ
          (Restrict E (rankStratum E r))))) ∧
    Continuous
      (fun z : TotalSpace Unit
          ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ
            (Restrict E (rankStratum E r))) ↦
        (⟨z.proj, fun i ↦ ⟨z.proj.2.val i z.snd, ⟨z.snd, rfl⟩⟩⟩ :
          TotalSpace Unit (RankFlagSum E h r))) := by
  /- Stage 1: each original projection is identity on its own range and
  kills the other ranges; their sum is the original identity. These are the
  same flag equations used by hermitianFlagSplitting_properties.
  Stage 2: the inverse retyping equality identifies the native pullback and
  induced line/sum topologies with exactly those used in this declaration.
  Transfer the existing continuity certificates for the same addition and
  projection maps. No classifying space, replacement fiber or new splitting
  witness appears. For r=0, the empty sum is the original zero fiber and the
  retained base coordinate keeps the total-space topology correct. -/
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  let := hF.nativeFiberBundle r (fun x ↦ x.property)
  let := hF.nativeVectorBundle r (fun x ↦ x.property)
  -- Transport the same vector sum and the same projection inverse through topology equality.
  have ht (i : Fin r) : hermitianFlagLineTopology r F (hF.nativeModelMetric r) i =
      rankFlagLineTopology E h r i := by
    exact congrArg (fun t : TopologicalSpace (TotalSpace Unit F) ↦
      letI := t
      TopologicalSpace.induced
        (fun z : TotalSpace Unit (RankFlagLine E h r i) ↦
          (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
            ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ F)))
        inferInstance) (ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := F) r)
  have hsum : hermitianFlagSumTopology r F (hF.nativeModelMetric r) =
      rankFlagSumTopology E h r := by
    exact congrArg (fun t : ∀ i : Fin r,
        TopologicalSpace (TotalSpace Unit (RankFlagLine E h r i)) ↦
      letI := t
      TopologicalSpace.induced
        (fun z : TotalSpace Unit (RankFlagSum E h r) ↦
          (z.proj, fun i : Fin r ↦
            (⟨z.proj, z.snd i⟩ : TotalSpace Unit (RankFlagLine E h r i))))
        inferInstance) (funext ht)
  have hpullback :
      @Pullback.TotalSpace.topologicalSpace _ Unit F _ (rankFlagProjection E h r)
        (rankFlagTopology E h r) (modelTopology (EuclideanSpace ℂ (Fin r)) F) =
      @Pullback.TotalSpace.topologicalSpace _ Unit F _ (rankFlagProjection E h r)
        (rankFlagTopology E h r) inferInstance := by
    exact congrArg (fun t : TopologicalSpace (TotalSpace Unit F) ↦
      @Pullback.TotalSpace.topologicalSpace _ Unit F _ (rankFlagProjection E h r)
        (rankFlagTopology E h r) t)
      (ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := F) r)
  have hs := hermitianFlagSplitting_properties r F (hF.nativeModelMetric r)
  refine ⟨hs.1, hs.2.1, ?_, ?_⟩
  · let f (z : TotalSpace Unit (RankFlagSum E h r)) : TotalSpace Unit
        ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ F) :=
      ⟨z.proj, ∑ i, (z.snd i).val⟩
    exact Eq.mp (congrArg₂ (fun t₁ t₂ ↦ @Continuous _ _ t₁ t₂ f) hsum hpullback) hs.2.2.1
  · let f (z : TotalSpace Unit
        ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ F)) :
        TotalSpace Unit (RankFlagSum E h r) :=
      ⟨z.proj, fun i ↦ ⟨z.proj.2.val i z.snd, ⟨z.snd, rfl⟩⟩⟩
    exact Eq.mp (congrArg₂ (fun t₁ t₂ ↦ @Continuous _ _ t₁ t₂ f) hpullback hsum) hs.2.2.2

/-- The actual rank-piece splitting adds the original vectors and inverts by projection. -/
def rankFlagSplitting (r : ℕ) :
    Iso (RankFlagSum E h r)
      ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ
        (Restrict E (rankStratum E r))) :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  { linearEquiv p :=
      { toFun := fun s ↦ ∑ i, (s i).val
        invFun := fun v i ↦ ⟨p.2.val i v, ⟨v, rfl⟩⟩
        left_inv := by
          -- The same projections recover every original line component.
          intro s
          funext i
          apply Subtype.ext
          exact (rankFlagSplitting_properties E h r).1 p s i
        right_inv := (rankFlagSplitting_properties E h r).2.1 p
        map_add' := by
          intro s t
          change (∑ i, ((s i).val + (t i).val)) =
            (∑ i, (s i).val) + (∑ i, (t i).val)
          exact Finset.sum_add_distrib
        map_smul' := by
          intro c s
          change (∑ i, c • (s i).val) = c • (∑ i, (s i).val)
          exact Finset.smul_sum.symm }
    continuous_total := (rankFlagSplitting_properties E h r).2.2.1
    continuous_symm := (rankFlagSplitting_properties E h r).2.2.2 }

end AtiyahSinger.ComplexBundle
