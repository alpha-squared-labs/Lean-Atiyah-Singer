/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Topology.EquivariantCotangentClopen

/-!
# The actual common refinement of invariant clopen submanifolds

Public module ID: M1180.

Intersect two open submanifolds by taking the original inverse image inside
the first one. Reversing their order preserves the ambient point and its native
cotangent covector. The restricted actions retain the specified actions on the
original pieces. Closedness, compactness and finite partition identities pass
to these same inverse images, giving the geometric comparison needed for
independence of the clopen decomposition in the equivariant analytic index.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 30

variable {M : Type*} [TopologicalSpace M]

/-- The part of the second open submanifold inside the first, with its native subtype. -/
def openRefinementPiece (U V : Opens M) : Opens U :=
  ⟨{x : U | x.val ∈ V}, V.isOpen.preimage continuous_subtype_val⟩

/-- Closedness of the original second piece gives closedness of its actual inverse image. -/
theorem isClosed_openRefinementPiece (U V : Opens M) (hV : IsClosed (V : Set M)) :
    IsClosed (openRefinementPiece U V : Set U) :=
  hV.preimage continuous_subtype_val

/-- A closed refinement piece of a compact original piece is compact. -/
theorem compactSpace_openRefinementPiece (U V : Opens M) [CompactSpace U]
    (hV : IsClosed (V : Set M)) : CompactSpace (openRefinementPiece U V) :=
  isCompact_iff_compactSpace.mp (isClosed_openRefinementPiece U V hV).isCompact

/-- Intersecting a partition with an original open piece gives a partition of that piece. -/
theorem openRefinementPiece_partition {ι : Type*} (U : Opens M) (V : ι → Opens M)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (V i : Set M) (V j : Set M)))
    (hcover : (⋃ i, (V i : Set M)) = Set.univ) :
    Pairwise (fun i j ↦ Disjoint (openRefinementPiece U (V i) : Set U)
      (openRefinementPiece U (V j) : Set U)) ∧
    (⋃ i, (openRefinementPiece U (V i) : Set U)) = Set.univ := by
  constructor
  · intro i j hij
    exact (hdisjoint hij).preimage Subtype.val
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x.val ∈ ⋃ i, (V i : Set M) := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩

variable {G : Type*} [Group G] [TopologicalSpace G]
  [MulAction G M]

/-- The specified outer action restricts to the same invariant common refinement. -/
@[reducible]
def openRefinementMulAction (U V : Opens M) [MulAction G U] [MulAction G V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : G) (x : V), ((g • x : V) : M) = g • x.val) :
    MulAction G (openRefinementPiece U V) where
  smul g x := ⟨g • x.val, by
    change ((g • x.val : U) : M) ∈ V
    rw [hU]
    have h := (g • (⟨x.val.val, x.property⟩ : V)).property
    simpa only [hV] using h⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- The original continuous action stays continuous on the same invariant inverse image. -/
theorem continuousSMul_openRefinement (U V : Opens M)
    [MulAction G U] [ContinuousSMul G U] [MulAction G V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : G) (x : V), ((g • x : V) : M) = g • x.val) :
    letI := openRefinementMulAction U V hU hV
    ContinuousSMul G (openRefinementPiece U V) := by
  let := openRefinementMulAction U V hU hV
  exact ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG) [ChartedSpace HG G]
  {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Smoothness is inherited from the specified original action on the outer piece. -/
theorem contMDiffSMul_openRefinement (U V : Opens M)
    [MulAction G U] [MulAction G V]
    [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G U]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : G) (x : V), ((g • x : V) : M) = g • x.val) :
    letI := openRefinementMulAction U V hU hV
    ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G (openRefinementPiece U V) := by
  let := openRefinementMulAction U V hU hV
  refine ⟨?_⟩
  apply (ContMDiff.subtypeVal_comp_iff (openRefinementPiece U V)
    (fun p : G × openRefinementPiece U V ↦ p.1 • p.2)).mp
  change ContMDiff (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (fun p : G × openRefinementPiece U V ↦ p.1 • p.2.val)
  have hsub : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (Subtype.val : openRefinementPiece U V → U) := contMDiff_subtype_val
  exact contMDiff_fst.smul (hsub.comp contMDiff_snd)

/-- Reversing the order of intersection retains the original ambient point. -/
def openRefinementDiffeomorph (U V : Opens M) :
    (openRefinementPiece U V) ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ (openRefinementPiece V U) where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun y := ⟨⟨y.val.val, y.property⟩, y.val.property⟩
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : openRefinementPiece U V ↦ x.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun x : openRefinementPiece V U ↦ x.val.val)
    exact contMDiff_subtype_val.comp contMDiff_subtype_val

omit [TopologicalSpace G] in
/-- The two specified restricted actions agree through the actual refinement diffeomorphism. -/
theorem openRefinementDiffeomorph_smul (U V : Opens M)
    [MulAction G U] [MulAction G V]
    (hU : ∀ (g : G) (x : U), ((g • x : U) : M) = g • x.val)
    (hV : ∀ (g : G) (x : V), ((g • x : V) : M) = g • x.val) :
    letI := openRefinementMulAction U V hU hV
    letI := openRefinementMulAction V U hV hU
    ∀ (g : G) (x : openRefinementPiece U V),
      openRefinementDiffeomorph (n := n) U V (g • x) =
        g • openRefinementDiffeomorph (n := n) U V x := by
  let := openRefinementMulAction U V hU hV
  let := openRefinementMulAction V U hV hU
  intro g x
  apply Subtype.ext
  apply Subtype.ext
  exact (hU g x.val).trans (hV g ⟨x.val.val, x.property⟩).symm

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original inverse-dual differential on a refinement preserves the displayed covector. -/
theorem cotangentDiffeomorph_openRefinement (U V : Opens M)
    (z : CotangentTotalSpace (n := n) (M := openRefinementPiece U V)) :
    cotangentDiffeomorph (openRefinementDiffeomorph (n := n) U V) z =
      ⟨openRefinementDiffeomorph (n := n) U V z.proj, z.snd⟩ := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let P := openRefinementPiece U V
  let Q := openRefinementPiece V U
  let e := openRefinementDiffeomorph (n := n) U V
  -- The two successive original open inclusions have identity derivatives in native charts.
  have hinc (A B : Opens M) (x : openRefinementPiece A B) :
      mfderiv I I (fun y : openRefinementPiece A B ↦ y.val.val) x =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) x
      ((contMDiff_subtype_val (U := A) (n := ∞)).mdifferentiable (by simp) x.val)
      ((contMDiff_subtype_val (U := openRefinementPiece A B) (n := ∞)).mdifferentiable
        (by simp) x)
    rw [mfderiv_openSubtypeVal, mfderiv_openSubtypeVal] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  have hderiv (y : Q) : mfderiv I I e.symm y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h := mfderiv_comp (I := I) (I' := I) (I'' := I) y
      ((contMDiff_subtype_val.comp contMDiff_subtype_val :
        ContMDiff I I ∞ (fun x : P ↦ x.val.val)).mdifferentiable (by simp) (e.symm y))
      (e.symm.mdifferentiable (by simp) y)
    change mfderiv I I (fun x : Q ↦ x.val.val) y =
      (mfderiv I I (fun x : P ↦ x.val.val) (e.symm y)).comp (mfderiv I I e.symm y) at h
    rw [hinc, hinc] at h
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h.symm
  change (⟨e z.proj, z.snd.comp (mfderiv I I e.symm (e z.proj))⟩ :
    CotangentTotalSpace (n := n) (M := Q)) = ⟨e z.proj, z.snd⟩
  rw [hderiv]
  apply TotalSpace.ext rfl
  apply heq_of_eq
  apply ContinuousLinearMap.ext
  intro v
  rfl

variable [IsTopologicalGroup G]

omit [MulAction G M]

set_option maxHeartbeats 800000 in
-- Five native cotangent actions occur simultaneously in the same restriction square.
/-- The two actual nested proper restrictions agree through their refinement diffeomorphism. -/
theorem equivariantCotangentPullback_openRefinement (U V : Opens M)
    (hU : IsClosed (U : Set M)) (hV : IsClosed (V : Set M))
    [MulAction G (CotangentTotalSpace (n := n) (M := M))]
    [ContinuousSMul G (CotangentTotalSpace (n := n) (M := M))]
    [MulAction G (CotangentTotalSpace (n := n) (M := U))]
    [ContinuousSMul G (CotangentTotalSpace (n := n) (M := U))]
    [MulAction G (CotangentTotalSpace (n := n) (M := V))]
    [ContinuousSMul G (CotangentTotalSpace (n := n) (M := V))]
    [MulAction G (CotangentTotalSpace (n := n) (M := openRefinementPiece U V))]
    [ContinuousSMul G (CotangentTotalSpace (n := n) (M := openRefinementPiece U V))]
    [MulAction G (CotangentTotalSpace (n := n) (M := openRefinementPiece V U))]
    [ContinuousSMul G (CotangentTotalSpace (n := n) (M := openRefinementPiece V U))]
    (heU : ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := U)),
      cotangentOpenInclusion U (g • z) = g • cotangentOpenInclusion U z)
    (heV : ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := V)),
      cotangentOpenInclusion V (g • z) = g • cotangentOpenInclusion V z)
    (heP : ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := openRefinementPiece U V)),
      cotangentOpenInclusion (openRefinementPiece U V) (g • z) =
        g • cotangentOpenInclusion (openRefinementPiece U V) z)
    (heQ : ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := openRefinementPiece V U)),
      cotangentOpenInclusion (openRefinementPiece V U) (g • z) =
        g • cotangentOpenInclusion (openRefinementPiece V U) z) :
    let d := cotangentDiffeomorph (openRefinementDiffeomorph (n := n) U V)
    let iU : C(CotangentTotalSpace (n := n) (M := U),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
    let iV : C(CotangentTotalSpace (n := n) (M := V),
        CotangentTotalSpace (n := n) (M := M)) :=
      ⟨cotangentOpenInclusion V, (isOpenEmbedding_cotangentOpenInclusion V).continuous⟩
    let iP : C(CotangentTotalSpace (n := n) (M := openRefinementPiece U V),
        CotangentTotalSpace (n := n) (M := U)) :=
      ⟨cotangentOpenInclusion (openRefinementPiece U V),
        (isOpenEmbedding_cotangentOpenInclusion (openRefinementPiece U V)).continuous⟩
    let iQ : C(CotangentTotalSpace (n := n) (M := openRefinementPiece V U),
        CotangentTotalSpace (n := n) (M := V)) :=
      ⟨cotangentOpenInclusion (openRefinementPiece V U),
        (isOpenEmbedding_cotangentOpenInclusion (openRefinementPiece V U)).continuous⟩
    ∃ hd : ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := openRefinementPiece U V)),
        d (g • z) = g • d z,
      (equivariantSupportTripleKZeroPullback iP heP
          (isProperMap_cotangentOpenInclusion _ (isClosed_openRefinementPiece U V hV))).comp
        (equivariantSupportTripleKZeroPullback iU heU
          (isProperMap_cotangentOpenInclusion U hU)) =
        (equivariantSupportTripleKZeroPullback ⟨d, d.continuous⟩ hd d.isProperMap).comp
          ((equivariantSupportTripleKZeroPullback iQ heQ
            (isProperMap_cotangentOpenInclusion _ (isClosed_openRefinementPiece V U hU))).comp
            (equivariantSupportTripleKZeroPullback iV heV
              (isProperMap_cotangentOpenInclusion V hV))) := by
  intro d iU iV iP iQ
  have hsquare (z : CotangentTotalSpace (n := n) (M := openRefinementPiece U V)) :
      iV (iQ (d z)) = iU (iP z) := by
    change cotangentOpenInclusion V
      (cotangentOpenInclusion (openRefinementPiece V U)
        (cotangentDiffeomorph (openRefinementDiffeomorph (n := n) U V) z)) = _
    rw [cotangentDiffeomorph_openRefinement]
    rfl
  -- The faithful double inclusion identifies the same lifted action on the common piece.
  have hd (g : G) (z : CotangentTotalSpace (n := n) (M := openRefinementPiece U V)) :
      d (g • z) = g • d z := by
    apply ((isOpenEmbedding_cotangentOpenInclusion V).comp
      (isOpenEmbedding_cotangentOpenInclusion (openRefinementPiece V U))).injective
    change iV (iQ (d (g • z))) = iV (iQ (g • d z))
    calc
      iV (iQ (d (g • z))) = iU (iP (g • z)) := hsquare _
      _ = g • iU (iP z) := (congrArg iU (heP g z)).trans (heU g (iP z))
      _ = g • iV (iQ (d z)) := congrArg (g • ·) (hsquare z).symm
      _ = iV (iQ (g • d z)) :=
        ((congrArg iV (heQ g (d z))).trans (heV g (iQ (d z)))).symm
  refine ⟨hd, ?_⟩
  have hmaps : (iV.comp iQ).comp (⟨d, d.continuous⟩ :
      C(CotangentTotalSpace (n := n) (M := openRefinementPiece U V),
        CotangentTotalSpace (n := n) (M := openRefinementPiece V U))) = iU.comp iP := by
    apply ContinuousMap.ext
    exact hsquare
  -- Properness comes from the original closed pieces, and the same maps compose contravariantly.
  rw [← equivariantSupportTripleKZeroPullback_comp,
    ← equivariantSupportTripleKZeroPullback_comp,
    ← equivariantSupportTripleKZeroPullback_comp]
  congr 1
  exact hmaps.symm

end AtiyahSinger
