/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBundleSmoothing
public import AtiyahSinger.Topology.EquivariantRankStrata

/-!
# Smooth equivariant realization on the actual rank strata

Public module ID: M1199.

A continuous equivariant bundle of locally varying finite rank is treated on
its actual invariant clopen rank strata. The same group G acts on each stratum
by restricting the given base action; the inherited open-submanifold atlas
makes this action smooth. For a compact finite-dimensional Lie group on a
compact smooth base, the constant-rank realization theorem supplies a smooth
target on each stratum and an equivariant isomorphism from the original
restricted bundle with its original pullback topology and specified action.

Karoubi II.1.26 and II.1.28--1.29, printed pp.56--57, supply the rank decomposition
background. Compactness gives only finitely many occurring ranks through
`isLocallyConstant_finrank` and mathlib's finite-range theorem. This module
does not assert that a single fixed-rank bundle represents all strata, or that
an arbitrary connected component is invariant under the full group G.

The smoothing step reuses `EquivariantStructure.exists_smooth_bundle_iso`.
Its SG Appendix A / SG III.9 argument is a project supplement; the Karoubi
rank passages do not supply that smoothing theorem. The proof
retains the original action on every stratum, including empty strata
and zero rank. The smooth action adapter uses only existing mathlib results.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

/-- The original smooth action restricts to the inherited rank-stratum manifold. -/
instance EquivariantStructure.contMDiffSMul_rankStratum
    (σ : EquivariantStructure G E) (r : ℕ) :
    letI := σ.rankStratumMulAction r
    ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G
      (rankStratum E r) := by
  let _ := σ.rankStratumMulAction r
  refine ⟨?_⟩
  -- Test smoothness in the original ambient manifold through the open inclusion.
  apply (ContMDiff.subtypeVal_comp_iff (rankStratum E r)
    (fun p : G × (rankStratum E r) ↦ p.1 • p.2)).mp
  change ContMDiff (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (fun p : G × (rankStratum E r) ↦ p.1 • (p.2 : M))
  have hsub : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (Subtype.val : rankStratum E r → M) := contMDiff_subtype_val
  -- This is the given joint action composed with the original subtype inclusion.
  exact contMDiff_fst.smul (hsub.comp contMDiff_snd)

variable [hDim : FiniteDimensional ℝ VG]
  [hLie : LieGroup 𝓘(ℝ, VG) ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]

include hDim hLie hGC hGT hM hT hSC hC hAction hE

/-- Each actual rank stratum admits a smooth realization of the original restricted action. -/
theorem EquivariantStructure.exists_smooth_bundle_iso_on_rankStratum
    (σ : EquivariantStructure G E) (r : ℕ) :
    letI := σ.rankStratumMulAction r
    letI := σ.continuousSMul_rankStratum r
    letI := σ.contMDiffSMul_rankStratum (VG := VG) (n := n) r
    ∃ F : SmoothFiniteComplexBundle (n := n) (rankStratum E r), F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ τ : EquivariantStructure G F.Fiber,
        τ.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
          ∃ e : Iso (Restrict E (rankStratum E r)) F.Fiber,
            e.IsEquivariant
              (σ.pullback ⟨(Subtype.val : rankStratum E r → M), continuous_subtype_val⟩
                (fun _ _ ↦ rfl)) τ := by
  /- Stage 1: the rank stratum is the actual fiber of the locally constant
  rank function. It is closed as well as open. Since M is compact, the
  inherited subtype is compact; its Hausdorff and second-countable structures
  are inherited too. The Opens presentation gives exactly the original
  restricted charts and smooth manifold structure.
  Stage 2: install rankStratumMulAction and its inherited continuous and
  smooth action certificates. Its inclusion is equivariant by reflexivity:
  it sends g acting on x to the same g acting on the same ambient base point.
  Pull back sigma along this inclusion using EquivariantStructure.pullback.
  This is the action displayed in the conclusion; the bundle is Restrict E
  with its native induced total-space topology, not a newly chosen action.
  Stage 3: isFiniteRank_restrict supplies local finite rank. Membership in
  rankStratum E r says precisely that each of these original fibers has rank r.
  Apply exists_smooth_bundle_iso to this same restricted bundle and action.
  Retain its chosen smooth target F, its action tau, and its actual equivariant
  isomorphism e, with the displayed F.rank equality and modelTopology witness.
  The proof works for every natural r. An unoccupied stratum is empty and
  receives the empty-base rank-r realization; r=0 is not excluded. On a
  compact base only finitely many strata are occupied, by the native finite
  range theorem, without requiring that G fix every connected component. -/
  let := σ.rankStratumMulAction r
  let := σ.continuousSMul_rankStratum r
  let := σ.contMDiffSMul_rankStratum (VG := VG) (n := n) r
  -- The same locally constant rank fiber is closed in the compact original base.
  have hclosed : IsClosed (rankStratum E r : Set M) :=
    (isLocallyConstant_finrank E).isClosed_fiber r
  let : CompactSpace (rankStratum E r) := isCompact_iff_compactSpace.mp hclosed.isCompact
  let := isFiniteRank_restrict (E := E) (rankStratum E r)
  -- Pull back the specified action, and keep the rank equality supplied by membership.
  exact (σ.pullback ⟨(Subtype.val : rankStratum E r → M), continuous_subtype_val⟩
    (fun _ _ ↦ rfl)).exists_smooth_bundle_iso (VG := VG) (n := n) r (fun x ↦ x.property)

end AtiyahSinger.ComplexBundle
