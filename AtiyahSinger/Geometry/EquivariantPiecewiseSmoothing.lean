/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantSupportSmoothing
public import AtiyahSinger.Topology.EquivariantClopenKZero
public import AtiyahSinger.Topology.EquivariantCommonRankPartition

/-!
# Piecewise smooth representatives of original equivariant compact-support K classes

Public module ID: M1198.

For a compact finite-dimensional Lie group, every original equivariant
support K class on a compact smooth base can be
represented by smooth triples on a finite invariant clopen partition of that
same base. The pieces are the occupied simultaneous rank strata of one original
continuous generator. Their source and target ranks are retained independently.
The resulting original class is recovered by the inverse of the same clopen
restriction equivalence, without selecting a different K-theory carrier.

On every piece the theorem records the actual proper restriction of that
generator, the original-to-smooth equivariant bundle isomorphisms, the exact
conjugated boundary, a smooth boundary with precisely the restricted control,
and a continuous equivariant homotopy with that same control. The chosen smooth
generator is used both in this local comparison and in the global assembly.
No single globally fixed-rank bundle or invariant connected-component
decomposition is asserted. Compactness of the base remains essential for the
finite global rank partition; compact support alone on a noncompact base does
not give that conclusion.

Sources: Karoubi I.2.9 and II.1.26--1.29 give local rank and finite clopen
decomposition; SG I.9.23--9.26 and ASI I Section 2 give the support framework.
This theorem assembles the existing original-group generator representation,
common-rank partition, clopen equivalence and same-control smooth realization.
The equivariant clopen comparison and smooth realization are project
supplements; none of those passages is claimed to state this assembled
theorem. The same selected generators enter the local comparison and assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hDim hLie hGC hGT hM hT hSC hC hAction

/-- Every original equivariant support K class has coherent piecewise smooth representatives. -/
theorem equivariantSupportTripleKZero_exists_piecewise_smooth_representative
    (z : EquivariantSupportTripleKZero G M) :
    ∃ a : EquivariantSupportBundleTriple G M, a.kZeroClass = z ∧
      ∃ (k : ℕ) (U : Fin k → Opens M) (r q : Fin k → ℕ),
        (∀ i, U i = rankStratum a.1.source.Fiber (r i) ⊓
          rankStratum a.1.target.Fiber (q i)) ∧
        (∀ i, (U i : Set M).Nonempty) ∧
        ∃ (hclosed : ∀ i, IsClosed (U i : Set M))
          (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
          (hcover : (⋃ i, (U i : Set M)) = Set.univ)
          (actions : ∀ i, MulAction G (U i)),
          letI := actions
          ∃ continuousActions : ∀ i, ContinuousSMul G (U i),
            letI := continuousActions
            ∃ smoothActions : ∀ i,
              ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i),
              letI := smoothActions
              ∃ heq : ∀ (i : Fin k) (g : G) (x : U i),
                ((g • x : U i) : M) = g • (x : M),
                ∃ b : ∀ i : Fin k, EquivariantSupportBundleTriple G (U i),
                  (∀ i,
                    let ai := a.pullback
                      ⟨(Subtype.val : U i → M), continuous_subtype_val⟩
                      (heq i) (hclosed i).isProperMap_subtypeVal
                    ∃ E F : SmoothFiniteComplexBundle (n := n) (U i),
                      E.rank = r i ∧ F.rank = q i ∧
                      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
                      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
                      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
                      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
                      ∃ (σE : EquivariantStructure G E.Fiber)
                        (σF : EquivariantStructure G F.Fiber),
                        σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG) ∧
                        σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
                        ∃ (e : Iso ai.1.source.Fiber E.Fiber)
                          (f : Iso ai.1.target.Fiber F.Fiber),
                          e.IsEquivariant ai.2.sourceAction σE ∧
                          f.IsEquivariant ai.2.targetAction σF ∧
                          let c := ai.1.datum.congr e f
                          let W : Opens (U i) :=
                            ⟨ai.1.datum.controlᶜ,
                              ai.1.datum.isCompact_control.isClosed.isOpen_compl⟩
                          ∃ β : RelativeTriple E.Fiber F.Fiber ai.1.datum.controlᶜ,
                            IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) (M := W)
                              (E := ((ContinuousMap.subtypeVal (W : Set (U i)) : W → U i) *ᵖ
                                E.Fiber))
                              (F := ((ContinuousMap.subtypeVal (W : Set (U i)) : W → U i) *ᵖ
                                F.Fiber))
                              (fun x ↦ (β.linearEquiv x).toLinearMap) ∧
                            let bi : CompactSupportTriple E.Fiber F.Fiber :=
                              { control := ai.1.datum.control
                                isCompact_control := ai.1.datum.isCompact_control
                                boundary := β }
                            ∃ hbi : bi.IsEquivariant σE σF,
                              b i = EquivariantSupportBundleTriple.ofBoundary
                                (FiniteBundle.ofFamily E.Fiber) (FiniteBundle.ofFamily F.Fiber)
                                bi σE σF hbi ∧
                              (∃ H : CompactSupportTriple.EquivariantHomotopy σE σF c bi,
                                H.control = ai.1.datum.control) ∧
                              ai.kZeroClass = (b i).kZeroClass) ∧
                  z = (equivariantSupportTripleKZeroClopenEquiv U hclosed heq
                    hdisjoint hcover).symm (fun i ↦ (b i).kZeroClass) := by
  /- Stage 1: represent the original z by one actual equivariant support
  triple a, using equivariantSupportBundleTriple_kZeroClass_surjective. The
  acting group is compact, and the original finite-dimensional Hausdorff
  smooth base is locally compact. Retain a itself and a.kZeroClass=z.
  Stage 2: apply exists_common_rank_partition to the two specified actions
  on a's original source and target. Keep exactly its occupied rank pieces,
  their independent labels r and q, their original Opens carriers, their
  nonemptiness, closedness, disjointness and cover of M. No common stabilizer
  is used to try to equalize locally varying virtual ranks.
  Stage 3: on each actual U_i define g acting on x by the original g*x.val.
  The partition's invariance supplies subtype membership, and the original
  action laws give the subtype laws. The inclusion is equivariant by rfl.
  The original induced topology gives joint continuity, while the inherited
  open-submanifold charts and subtypeVal_comp_iff give joint smoothness.
  Select these same action certificates for all later local constructions.
  Stage 4: closedness makes the exact inclusion U_i to M proper, so define
  ai to be the old a.pullback along it, with precisely the displayed heq i.
  Its control is the inverse image of a's original control. Each U_i is
  compact, Hausdorff and second countable, with the original inherited smooth
  structure. Membership in the stated two rank strata supplies the two
  constant-rank hypotheses for ai; its original fibers and actions remain
  the native pullbacks of a's own fibers and actions.
  Stage 5: apply exists_smooth_representative to each of these actual ai.
  Choose its E, F, smooth actions, original equivariant e and f, the exact
  c=ai.datum.congr e f, and the smooth beta on precisely the old exterior.
  Define b_i to be exactly the returned packaged generator with control
  ai.datum.control. Keep the same homotopy H, its exact control equation and
  ai.kZeroClass=b_i.kZeroClass. Dependent choice assembles these selected
  generators into one family b, without selecting a second family for K.
  Stage 6: evaluate the forward clopen equivalence on the original z. Its
  i-th coordinate is the old proper pullback of z. Substitute a.kZeroClass=z
  and the generator pullback equation to identify it with ai.kZeroClass,
  then use the same local equality to obtain b_i.kZeroClass. Apply the inverse
  of that very equivalence to the resulting equality of functions. This
  proves the displayed global assembly equation in the original K group.
  The theorem does not identify the fibers or ranks of different pieces.
  A piece with unequal ranks is retained, even when its exterior is empty.
  If M is empty the occupied index set is empty and assembly still recovers
  the original class; rank-zero fibers and empty exteriors are also allowed.
  No homogeneous elliptic symbol or noncompact global rank reduction is
  inferred from this compact-base piecewise representative theorem. -/
  classical
  -- Start with one original generator and its actual simultaneous rank partition.
  obtain ⟨a, ha⟩ := equivariantSupportBundleTriple_kZeroClass_surjective z
  obtain ⟨k, U, r, q, hU, hne, hdisjoint, hcover, hclosed, hinv⟩ :=
    a.2.sourceAction.exists_common_rank_partition a.2.targetAction
  let actions : ∀ i, MulAction G (U i) := fun i ↦
    { smul g x := ⟨g • x.val, (hinv i g x.val).mpr x.property⟩
      one_smul x := Subtype.ext (one_smul G x.val)
      mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  let := actions
  let continuousActions : ∀ i, ContinuousSMul G (U i) := fun _ ↦
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let := continuousActions
  have smoothActions : ∀ i,
      ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (U i) := by
    intro i
    refine ⟨?_⟩
    -- Joint smoothness is tested through this exact open-submanifold inclusion.
    apply (ContMDiff.subtypeVal_comp_iff (U i) (fun p : G × U i ↦ p.1 • p.2)).mp
    change ContMDiff (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : G × U i ↦ p.1 • (p.2 : M))
    have hsub : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Subtype.val : U i → M) :=
      contMDiff_subtype_val
    exact contMDiff_fst.smul (hsub.comp contMDiff_snd)
  let := smoothActions
  have heq (i : Fin k) (g : G) (x : U i) : ((g • x : U i) : M) = g • (x : M) := rfl
  let compactPieces : ∀ i, CompactSpace (U i) := fun i ↦
    isCompact_iff_compactSpace.mp (hclosed i).isCompact
  let := compactPieces
  let ai (i : Fin k) := a.pullback
    ⟨(Subtype.val : U i → M), continuous_subtype_val⟩
    (heq i) (hclosed i).isProperMap_subtypeVal
  have hSourceRank (i : Fin k) (x : U i) :
      Module.finrank ℂ ((ai i).1.source.Fiber x) = r i := by
    have hx : (x : M) ∈ rankStratum a.1.source.Fiber (r i) ⊓
        rankStratum a.1.target.Fiber (q i) := by
      simpa only [hU i] using x.property
    exact hx.1
  have hTargetRank (i : Fin k) (x : U i) :
      Module.finrank ℂ ((ai i).1.target.Fiber x) = q i := by
    have hx : (x : M) ∈ rankStratum a.1.source.Fiber (r i) ⊓
        rankStratum a.1.target.Fiber (q i) := by
      simpa only [hU i] using x.property
    exact hx.2
  -- Choose each local smooth representative once, retaining the same isomorphisms and homotopy.
  have hrep := fun i : Fin k ↦
    (ai i).exists_smooth_representative (VG := VG) (n := n) (r i) (q i)
      (hSourceRank i) (hTargetRank i)
  choose E F hEr hFq σE σF hσE hσF e f he hf β hβ hb hH hclass using hrep
  let b (i : Fin k) : EquivariantSupportBundleTriple G (U i) :=
    letI := modelTopology (EuclideanSpace ℂ (Fin (E i).rank)) (E i).Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin (F i).rank)) (F i).Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin (E i).rank)) (E i).Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin (F i).rank)) (F i).Fiber
    EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily (E i).Fiber) (FiniteBundle.ofFamily (F i).Fiber)
      { control := (ai i).1.datum.control
        isCompact_control := (ai i).1.datum.isCompact_control
        boundary := β i } (σE i) (σF i) (hb i)
  refine ⟨a, ha, k, U, r, q, hU, hne, hclosed, hdisjoint, hcover,
    actions, continuousActions, smoothActions, heq, b, ?_, ?_⟩
  · intro i
    exact ⟨E i, F i, hEr i, hFq i, σE i, σF i, hσE i, hσF i,
      e i, f i, he i, hf i, β i, hβ i, hb i, rfl, hH i, hclass i⟩
  · -- The forward equivalence restricts the original class to these very same generators.
    let Φ := equivariantSupportTripleKZeroClopenEquiv U hclosed heq hdisjoint hcover
    apply Φ.injective
    change Φ z = Φ (Φ.symm (fun i ↦ (b i).kZeroClass))
    rw [Φ.apply_symm_apply]
    funext i
    rw [← ha]
    change equivariantSupportTripleKZeroPullback
      ⟨(Subtype.val : U i → M), continuous_subtype_val⟩
      (heq i) (hclosed i).isProperMap_subtypeVal a.kZeroClass = (b i).kZeroClass
    rw [equivariantSupportTripleKZeroPullback_apply]
    exact hclass i

end AtiyahSinger.ComplexBundle
