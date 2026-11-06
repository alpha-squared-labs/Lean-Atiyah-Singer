/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacter
public import AtiyahSinger.Topology.RankStratumCohomology
public import AtiyahSinger.Topology.VariableRankFlagSplitting

/-!
# Splitting and actual Chern roots on all original rank strata

Public module ID: M2272.

C01: the global original flag projection is injective on singular cohomology,
and original-base class equality can be checked on every actual rank flag.
The clopen rank decomposition requires neither bounded ranks nor a connected
or compact base. These are the componentwise forms of SG III.11.1 and Hatcher
VBKT Proposition 3.3; the arbitrary-base comparison uses the projective
Leray--Hirsch theorem and actual flag tower in SplittingPrinciple.

The three characteristic-class adapters below are precisely the existing
fixed-rank root, Chern class and Chern-character component, applied to the
original restricted fibers and metric. Their formulas use the same rank
projection and normalized tautological lines. `VariableRankChern` assembles
these degreewise classes over the original base using its clopen rank
decomposition, including when rank is unbounded.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

attribute [local instance] isFiniteRank_restrict rankFlagTopology rankFlagLineTopology
  variableRankFlagTopology

/-- The actual global locally varying-rank flag projection is cohomologically injective. -/
theorem variableRankFlagProjection_cohomology_injective (R : Type) [CommRing R] (k : ℕ) :
    Function.Injective
      (singularCohomologyPullback R (variableRankFlagProjection E h) k) := by
  /- Stage 1: restrict to each original clopen rank stratum. The fixed-model
  adapter preserves the original fibers, restricted metric and topology, so
  the existing complete-flag injectivity theorem applies to that exact map.
  Stage 2: a singular simplex has constant rank because its domain is
  connected. The singular chain complex of the original base is the direct
  sum over rank strata; its cochain complex and cohomology are the products
  over these same pieces. The global flag projection acts componentwise by
  the injective maps from Stage 1, hence its original pullback is injective.
  No uniform rank bound or finiteness of the clopen decomposition is needed.
  Rank zero retains the original base piece with its singleton flag fiber. -/
  intro a b hab
  apply (singularCohomologyPullback_rankStrata_bijective R E k).injective
  funext r
  have hflag : Function.Injective (singularCohomologyPullback R (rankFlagProjection E h r) k) := by
    let F := Restrict E (rankStratum E r)
    let hF := rankHermitianMetric E h r
    let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
    let := hF.nativeFiberBundle r (fun x ↦ x.property)
    let := hF.nativeVectorBundle r (fun x ↦ x.property)
    exact hermitianFlagProjection_cohomology_injective R r F (hF.nativeModelMetric r) k
  apply hflag
  -- Restrict the given equality along the actual summand inclusion of this rank flag.
  have hr := congrArg (singularCohomologyPullback R (rankFlagInclusion E h r) k) hab
  have hcomp : singularCohomologyPullback R (variableRankFlagProjection E h) k ≫
      singularCohomologyPullback R (rankFlagInclusion E h r) k =
    singularCohomologyPullback R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X)) k ≫
        singularCohomologyPullback R (rankFlagProjection E h r) k := by
    simp only [singularCohomologyPullback, ← Functor.map_comp]
    rfl
  change (singularCohomologyPullback R (variableRankFlagProjection E h) k ≫
    singularCohomologyPullback R (rankFlagInclusion E h r) k) a =
      (singularCohomologyPullback R (variableRankFlagProjection E h) k ≫
        singularCohomologyPullback R (rankFlagInclusion E h r) k) b at hr
  rw [hcomp] at hr
  exact hr

/-- Equality of original-base classes is detected on all the actual rank-piece flags. -/
theorem cohomology_eq_iff_rankFlag_pullbacks_eq (R : Type) [CommRing R] (k : ℕ)
    (a b : singularCohomology R X k) :
    a = b ↔ ∀ r : ℕ,
      singularCohomologyPullback R
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X)).comp
            (rankFlagProjection E h r)) k a =
        singularCohomologyPullback R
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X)).comp
            (rankFlagProjection E h r)) k b := by
  /- Stage 1: equality is preserved by each displayed original pullback.
  Conversely, fixed-rank flag injectivity makes the restrictions of a and b
  equal on every original clopen rank stratum. The cochain product over the
  actual clopen decomposition detects equality of original-base classes.
  Equivalently apply the preceding global injectivity theorem after the
  topological-sum decomposition of its domain. Both arguments use precisely
  the original inclusions composed with the specified rank projections. -/
  constructor
  · intro hab
    subst b
    exact fun _ ↦ rfl
  · intro hab
    apply (singularCohomologyPullback_rankStrata_bijective R E k).injective
    funext r
    have hflag : Function.Injective
        (singularCohomologyPullback R (rankFlagProjection E h r) k) := by
      let F := Restrict E (rankStratum E r)
      let hF := rankHermitianMetric E h r
      let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
      let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
      let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
      let := hF.nativeFiberBundle r (fun x ↦ x.property)
      let := hF.nativeVectorBundle r (fun x ↦ x.property)
      exact hermitianFlagProjection_cohomology_injective R r F (hF.nativeModelMetric r) k
    apply hflag
    have hr := hab r
    have hcomp : singularCohomologyPullback R
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X)).comp
          (rankFlagProjection E h r)) k =
      singularCohomologyPullback R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X)) k ≫
          singularCohomologyPullback R (rankFlagProjection E h r) k :=
      (singularCohomologyFunctor R k).map_comp
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(rankStratum E r, X))).op
        (TopCat.ofHom (rankFlagProjection E h r)).op
    rw [hcomp] at hr
    exact hr

/-- The existing normalized tautological Chern root on the original rank-r flag. -/
def rankFlagChernRoot (r : ℕ) (i : Fin r) :
    singularCohomology ℤ (RankFlagBundle E h r) 2 :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  letI := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  letI := hF.nativeFiberBundle r (fun x ↦ x.property)
  letI := hF.nativeVectorBundle r (fun x ↦ x.property)
  flagChernRoot r F (hF.nativeModelMetric r) i

/-- The inherited root is the normalized class of the original rank-piece range line.
The topology comparison identifies the same continuous line family. -/
theorem rankFlagChernRoot_eq_firstChernClass (r : ℕ) (i : Fin r) :
    let F := Restrict E (rankStratum E r)
    let hF := rankHermitianMetric E h r
    letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    letI := isFiniteRank_rankFlagLine E h r i
    rankFlagChernRoot E h r i =
      firstChernClass (RankFlagLine E h r i) (fun p ↦ p.2.property.2.1 i) := by
  set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.defeqAttrib.useBackward true in
    /- The two line families are the same projection ranges. First identify
    their original total topologies, then transport the normalized first-Chern
    construction; all remaining rank and finite-rank certificates are proofs. -/
    let F := Restrict E (rankStratum E r)
    let hF := rankHermitianMetric E h r
    let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
    let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
    let := hF.nativeFiberBundle r (fun x ↦ x.property)
    let := hF.nativeVectorBundle r (fun x ↦ x.property)
    -- Retyping the model recovers the original pullback and induced range topology.
    have ht : hermitianFlagLineTopology r F (hF.nativeModelMetric r) i =
        rankFlagLineTopology E h r i := by
      exact congrArg (fun t : TopologicalSpace (TotalSpace Unit F) ↦
        letI := t
        TopologicalSpace.induced
          (fun z : TotalSpace Unit (RankFlagLine E h r i) ↦
            (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
              ((rankFlagProjection E h r : RankFlagBundle E h r → rankStratum E r) *ᵖ F)))
          inferInstance) (ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := F) r)
    -- The same positive complex normalization defines both classes on this exact line.
    let L := RankFlagLine E h r i
    have hclass (t : TopologicalSpace (TotalSpace Unit L))
        (hL : @IsFiniteRank _ _ L _ _ t)
        (hT : t = rankFlagLineTopology E h r i) :
        @firstChernClass _ _ L _ _ t hL (fun p ↦ p.2.property.2.1 i) =
          @firstChernClass _ _ L _ _ (rankFlagLineTopology E h r i)
            (isFiniteRank_rankFlagLine E h r i) (fun p ↦ p.2.property.2.1 i) := by
      subst t
      rfl
    exact hclass _ (isFiniteRank_hermitianFlagLine r F (hF.nativeModelMetric r) i) ht

/-- The existing fixed-rank integral Chern class on the original rank-r stratum. -/
def rankStratumChernClass (r k : ℕ) :
    singularCohomology ℤ (rankStratum E r) (2 * k) :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  letI := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  letI := hF.nativeFiberBundle r (fun x ↦ x.property)
  letI := hF.nativeVectorBundle r (fun x ↦ x.property)
  chernClass r F (hF.nativeModelMetric r) k

/-- The existing rational Chern-character component on the original rank-r stratum. -/
def rankStratumChernCharacterComponent (r k : ℕ) :
    singularCohomology ℚ (rankStratum E r) (2 * k) :=
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  letI : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  letI := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  letI := hF.nativeFiberBundle r (fun x ↦ x.property)
  letI := hF.nativeVectorBundle r (fun x ↦ x.property)
  chernCharacterComponent r F (hF.nativeModelMetric r) k

/-- The actual rank-flag pullback is the elementary symmetric class of its original roots. -/
theorem rankStratumChernClass_flag_pullback (r k : ℕ) :
    singularCohomologyPullback ℤ (rankFlagProjection E h r) (2 * k)
        (rankStratumChernClass E h r k) =
      singularCohomologyElementarySymmetric ℤ (RankFlagBundle E h r)
        (List.ofFn (rankFlagChernRoot E h r)) k := by
  /- Reuse chernClass_flag_pullback on the original restricted fiber family
  with precisely the designated native model, metric and bundle instances.
  The three adapters unfold to that statement with the same flag projection.
  No independent descending class or renamed formal root is chosen. -/
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  let := hF.nativeFiberBundle r (fun x ↦ x.property)
  let := hF.nativeVectorBundle r (fun x ↦ x.property)
  exact chernClass_flag_pullback r F (hF.nativeModelMetric r) k

/-- The actual rank-flag character component is the normalized power sum of the same roots. -/
theorem rankStratumChernCharacterComponent_flag_pullback (r k : ℕ) :
    singularCohomologyPullback ℚ (rankFlagProjection E h r) (2 * k)
        (rankStratumChernCharacterComponent E h r k) =
      (Nat.factorial k : ℚ)⁻¹ •
        ∑ i : Fin r, singularCohomologyDegreeTwoPow ℚ (RankFlagBundle E h r)
          (singularCohomologyRationalization (RankFlagBundle E h r) 2
            (rankFlagChernRoot E h r i)) k := by
  /- Reuse the existing fixed-rank character pullback formula on the exact
  native presentation of the restricted original bundle and its same metric.
  Root normalization, rationalization, degree-two power and factorial all
  remain unchanged. For k=0 the formula counts r roots; r=0 gives zero in
  every component. No infinite cohomological sum is introduced. -/
  let F := Restrict E (rankStratum E r)
  let hF := rankHermitianMetric E h r
  let : ∀ x, NormedAddCommGroup (F x) := hF.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hF.fiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℂ (Fin r))
  let := hF.nativeFiberBundle r (fun x ↦ x.property)
  let := hF.nativeVectorBundle r (fun x ↦ x.property)
  exact chernCharacterComponent_flag_pullback r F (hF.nativeModelMetric r) k

end AtiyahSinger.ComplexBundle
