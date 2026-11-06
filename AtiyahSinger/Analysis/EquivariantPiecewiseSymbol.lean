/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantCotangentSmoothing
public import AtiyahSinger.Topology.EquivariantCommonRankPartition
public import AtiyahSinger.Topology.EquivariantCotangentClopen
public import AtiyahSinger.Topology.EquivariantCotangentRepresentative
public import AtiyahSinger.Topology.EquivariantPullbackTransport

/-!
# Piecewise smooth symbols representing original equivariant cotangent K classes

Public module ID: M0552.

Every original equivariant compact-support K class on a compact smooth
manifold's cotangent space is represented by one coherent family of smooth
degree-zero elliptic symbols on a finite invariant clopen base partition.
The local carriers are the actual cotangent spaces of the open submanifolds.
Each selected generator is exactly the elliptic triple of the selected
symbol, with its original pulled actions. Its class is the proper restriction
of the input class. The inverse of that same restriction equivalence recovers
the input from precisely these generators.

The construction first takes the original continuous pullback representative,
then uses the common rank strata of its two base bundles, and finally applies
smooth homogeneous replacement on each piece. Compactness makes the occupied
rank partition finite; neither connectedness nor invariant connected
components are assumed. Independent source and target ranks are retained,
including in dimension zero. This is a representative theorem, before any
analytic-index descent on the original equivariant K group.

Sources: SG III.13 Lemma 13.3 and the discussion before (13.7), pp.245--246,
give the ordinary homogeneous representative route; SG III.9 gives averaging;
SG Appendix A Remark A.1 gives ordinary smooth bundle classification.
Karoubi I.2.9 and II.1.26--1.29 give local rank and finite decomposition.
This equivariant assembly is a project supplement, not a separately numbered
theorem in those passages. It combines radial homogeneous replacement, smooth
equivariant bundle and boundary replacement, and invariant clopen decomposition.
The proof retains the same generators throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

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

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

include hDim hLie hGC hGT hM hT hSC hC hAction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in

set_option maxHeartbeats 3000000 in
-- The original family retains both native iterated-pullback topologies and action certificates.
/-- Every original equivariant cotangent K class has coherent piecewise smooth symbols. -/
theorem exists_piecewise_equivariant_homogeneous_symbol :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ (k : ℕ) (U : Fin k → Opens M),
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
                ∃ compactPieces : ∀ i, CompactSpace (U i),
                  letI := compactPieces
                  letI : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
                    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
                  letI : ∀ i, ContMDiffSMul 𝓘(ℝ, VG)
                      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
                      (CotangentTotalSpace (n := n) (M := U i)) :=
                    fun i ↦ contMDiffSMul_smoothCotangent
                      (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
                  letI : ∀ i, ContinuousSMul G
                      (CotangentTotalSpace (n := n) (M := U i)) :=
                    fun i ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
                      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
                  ∃ b : ∀ i, EquivariantSupportBundleTriple G
                      (CotangentTotalSpace (n := n) (M := U i)),
                    (∀ i, ∃ E F : SmoothFiniteComplexBundle (n := n) (U i),
                      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
                      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
                      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
                      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
                      ∃ (σE : EquivariantStructure G E.Fiber)
                        (σF : EquivariantStructure G F.Fiber),
                        σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG) ∧
                        σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
                        ∃ s : homogeneousGlobalSymbolSpace
                            (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0,
                          ∃ hi : IsEllipticGlobalSymbol E.Fiber F.Fiber s.val,
                            (∀ (g : G) (x : U i) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                              equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g s.val x ξ =
                                s.val x ξ) ∧
                            let p := cotangentProjection (n := n) (M := U i)
                            let τE := σE.pullback p (fun _ _ ↦ rfl)
                            let τF := σF.pullback p (fun _ _ ↦ rfl)
                            let bi := ellipticSymbolTriple s.val s.property.1.continuous hi
                            ∃ hbi : bi.IsEquivariant τE τF,
                              b i = EquivariantSupportBundleTriple.ofBoundary
                                (FiniteBundle.ofFamily ((p : _ → U i) *ᵖ E.Fiber))
                                (FiniteBundle.ofFamily ((p : _ → U i) *ᵖ F.Fiber))
                                bi τE τF hbi) ∧
                    (∀ i, equivariantCotangentClopenRestrict
                      (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq z i = (b i).kZeroClass) ∧
                    z = (equivariantCotangentClopenEquiv
                      (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq hdisjoint hcover).symm
                        (fun i ↦ (b i).kZeroClass) := by
  /- Stage 1: apply exists_equivariant_homogeneous_cotangent_representative
  to the original z. Keep its original continuous base bundles E0 and F0,
  their original actions, the actual projection-pullback triple a with
  precisely zero-section control, and its equality to the original class.
  Stage 2: apply exists_common_rank_partition to the two base actions.
  The occupied simultaneous rank strata are finite because M is compact.
  They are invariant, open and closed, disjoint and cover M. Restrict the
  given action to these actual Opens carriers using their invariance.
  The subtype inclusion preserves the original action, and the inherited
  open charts give the displayed continuous and smooth action witnesses.
  Closedness also makes each base piece compact; it does not make its
  cotangent fibers compact. Retain this single partition and these actions.
  Stage 3: properly restrict the original generator along the actual
  cotangentOpenInclusion of each piece. The inclusion is equivariant by
  cotangentOpenInclusion_smul and proper because the base piece is closed.
  Its inverse image of the original zero control is exactly the native
  zero section. Canonical pullback-composition isomorphisms, preserving
  each fiber vector, compare its bundles with the native projection
  pullbacks of E0 and F0 restricted to the same base piece. Their action
  compatibility follows from the same inclusion equation heq. Transport
  the boundary with these actual maps and retain the original restricted
  K class by the equivariant isomorphism-square relation.
  Stage 4: the common rank stratum supplies the two independent constant
  ranks. Apply exists_equivariant_smooth_cotangent_replacement to the
  restricted continuous pair, its original actions and the preceding
  boundary. It returns smooth base bundles and actions, one homogeneous
  symbol s, its off-zero ellipticity and equivariance, and the equality
  with precisely its ellipticSymbolTriple in the original equivariant K
  group. Define b_i to be exactly that packaged elliptic triple, using
  those same native pulled actions. Dependent choice selects these
  witnesses together; there is no second family selected for assembly.
  Stage 5: proper-pullback functoriality and the original representative
  equality identify the i-th actual restriction of z with this same b_i
  class. The forward map of equivariantCotangentClopenEquiv is literally
  that restriction. Apply its inverse to the equality of coordinate
  families to obtain the displayed reconstruction of the original z.
  Empty M gives no occupied pieces. In dimension zero the punctured
  domains are empty and unequal source/target ranks remain permissible.
  No globally fixed-rank smooth bundle, nonproper compact-support K
  pullback, or analytic-index descent is asserted by this theorem. -/
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  -- Choose one original generator and its occupied invariant common-rank partition.
  obtain ⟨E₀, F₀, ρE, ρF, a, ha, hControl, _hhom, hclass⟩ :=
    exists_equivariant_homogeneous_cotangent_representative 𝓘(ℝ, VG) z
  obtain ⟨k, U, r, q, hU, hne, hdisjoint, hcover, hclosed, hinv⟩ :=
    ρE.exists_common_rank_partition ρF
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
  let : ∀ i, MulAction G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ smoothCotangentMulAction (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
  let : ∀ i, ContMDiffSMul 𝓘(ℝ, VG)
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞ G
      (CotangentTotalSpace (n := n) (M := U i)) :=
    fun i ↦ contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U i) 𝓘(ℝ, VG)
  let : ∀ i, ContinuousSMul G (CotangentTotalSpace (n := n) (M := U i)) :=
    fun _ ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let pM := cotangentProjection (n := n) (M := M)
  let ι (i : Fin k) : C(U i, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let p (i : Fin k) := cotangentProjection (n := n) (M := U i)
  let j (i : Fin k) : C(CotangentTotalSpace (n := n) (M := U i),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion (U i), (isOpenEmbedding_cotangentOpenInclusion (U i)).continuous⟩
  have hj (i : Fin k) (g : G) (x : CotangentTotalSpace (n := n) (M := U i)) :
      j i (g • x) = g • j i x := cotangentOpenInclusion_smul 𝓘(ℝ, VG) (U i) (heq i) g x
  have hjproper (i : Fin k) : IsProperMap (j i) :=
    isProperMap_cotangentOpenInclusion (U i) (hclosed i)
  let a₀ := EquivariantSupportBundleTriple.ofBoundary
    (E₀.pullback pM) (F₀.pullback pM) a
    (ρE.pullback pM (fun _ _ ↦ rfl)) (ρF.pullback pM (fun _ _ ↦ rfl)) ha
  let ai (i : Fin k) := a₀.pullback (j i) (hj i) (hjproper i)
  -- Both pullback routes have the same base point and preserve each actual fiber vector.
  have hcompare (i : Fin k) (J : FiniteBundle M) (ρ : EquivariantStructure G J.Fiber) :
      ∃ e : Iso (((j i : _ → _) *ᵖ ((pM : _ → _) *ᵖ J.Fiber)))
          (((p i : _ → _) *ᵖ ((ι i : _ → _) *ᵖ J.Fiber))),
        e.IsEquivariant ((ρ.pullback pM (fun _ _ ↦ rfl)).pullback (j i) (hj i))
          ((ρ.pullback (ι i) (heq i)).pullback (p i) (fun _ _ ↦ rfl)) := by
    let u := pullbackCompIso (E := J.Fiber) pM (j i)
    let v := pullbackCompIso (E := J.Fiber) (ι i) (p i)
    let e := u.trans v.symm
    have he (x : CotangentTotalSpace (n := n) (M := U i)) (w : J.Fiber (x.proj : M)) :
        e.linearEquiv x w = w := by
      change (v.linearEquiv x).symm (u.linearEquiv x w) = w
      apply (v.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (pullbackCompIso_apply pM (j i) x w).trans
        (pullbackCompIso_apply (ι i) (p i) x w).symm
    refine ⟨e, ?_⟩
    intro g x w
    change e.linearEquiv (g • x) _ =
      ((ρ.pullback (ι i) (heq i)).pullback (p i) (fun _ _ ↦ rfl)).linearMap g x
        (e.linearEquiv x w)
    rw [he, he]
    have hu := ρ.pullbackCompIso_isEquivariant pM (fun _ _ ↦ rfl) (j i) (hj i) g x w
    have hv := ρ.pullbackCompIso_isEquivariant (ι i) (heq i) (p i) (fun _ _ ↦ rfl) g x w
    have hu' := (pullbackCompIso_apply pM (j i) (g • x) _).symm.trans
      (hu.trans (congrArg
        ((ρ.pullback (pM.comp (j i))
          (fun g x ↦ (congrArg pM (hj i g x)).trans rfl)).linearMap g x)
        (pullbackCompIso_apply pM (j i) x w)))
    have hv' := (pullbackCompIso_apply (ι i) (p i) (g • x) _).symm.trans
      (hv.trans (congrArg
        ((ρ.pullback ((ι i).comp (p i))
          (fun g x ↦ (congrArg (ι i) (show p i (g • x) = g • p i x from rfl)).trans
            (heq i g (p i x)))).linearMap g x)
        (pullbackCompIso_apply (ι i) (p i) x w)))
    exact hu'.trans hv'.symm
  choose e he using fun i ↦ hcompare i E₀ ρE
  choose f hf using fun i ↦ hcompare i F₀ ρF
  let c (i : Fin k) := (ai i).1.datum.congr (e i) (f i)
  let τE (i : Fin k) := (ρE.pullback (ι i) (heq i)).pullback (p i) (fun _ _ ↦ rfl)
  let τF (i : Fin k) := (ρF.pullback (ι i) (heq i)).pullback (p i) (fun _ _ ↦ rfl)
  have hc (i : Fin k) : (c i).IsEquivariant (τE i) (τF i) := by
    refine ⟨(ai i).2.isEquivariant.invariant_control, ?_⟩
    intro g x w
    -- Conjugating this very boundary by the comparison maps retains the original square.
    have hinverse : (e i).symm.linearEquiv (g • x.val) ((τE i).linearMap g x.val w) =
        (ai i).2.sourceAction.linearMap g x.val ((e i).symm.linearEquiv x.val w) := by
      have h := he i g x.val ((e i).symm.linearEquiv x.val w)
      change (e i).linearEquiv (g • x.val) _ =
        (τE i).linearMap g x.val ((e i).linearEquiv x.val
          (((e i).linearEquiv x.val).symm w)) at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact ((e i).linearEquiv (g • x.val)).symm_apply_eq.mpr h.symm
    let gx : ((c i).controlᶜ : Set _) :=
      ⟨g • x.val, fun hx ↦ x.property
        (((ai i).2.isEquivariant.invariant_control g x.val).mp hx)⟩
    change (f i).linearEquiv (g • x.val)
      ((ai i).1.datum.boundary.linearEquiv gx
        ((e i).symm.linearEquiv (g • x.val) ((τE i).linearMap g x.val w))) = _
    rw [hinverse]
    exact (congrArg ((f i).linearEquiv (g • x.val))
      ((ai i).2.isEquivariant.boundary_intertwines g x _)).trans (hf i g x.val _)
  have hcControl (i : Fin k) : (c i).control = cotangentZeroSet := by
    change (j i) ⁻¹' a.control = _
    rw [hControl]
    rfl
  have hSourceRank (i : Fin k) (x : U i) :
      Module.finrank ℂ ((E₀.pullback (ι i)).Fiber x) = r i := by
    have hx : (x : M) ∈ rankStratum E₀.Fiber (r i) ⊓ rankStratum F₀.Fiber (q i) := by
      simpa only [hU i] using x.property
    exact hx.1
  have hTargetRank (i : Fin k) (x : U i) :
      Module.finrank ℂ ((F₀.pullback (ι i)).Fiber x) = q i := by
    have hx : (x : M) ∈ rankStratum E₀.Fiber (r i) ⊓ rankStratum F₀.Fiber (q i) := by
      simpa only [hU i] using x.property
    exact hx.2
  let ci (i : Fin k) := EquivariantSupportBundleTriple.ofBoundary
    ((E₀.pullback (ι i)).pullback (p i)) ((F₀.pullback (ι i)).pullback (p i))
    (c i) (τE i) (τF i) (hc i)
  have hiso (i : Fin k) : (ai i).IsIsomorphic (ci i) := by
    refine ⟨(ai i).1.datum.control, (ai i).1.datum.isCompact_control,
      (ai i).2.isEquivariant.invariant_control, (fun _ hx ↦ hx), (fun _ hx ↦ hx),
      e i, f i, he i, hf i, ?_⟩
    intro x w
    rw [(ai i).1.datum.enlarge_apply (ai i).1.datum.control
      (ai i).1.datum.isCompact_control (fun _ hx ↦ hx),
      (ci i).1.datum.enlarge_apply (ai i).1.datum.control
        (ai i).1.datum.isCompact_control (fun _ hx ↦ hx)]
    change (f i).linearEquiv x ((ai i).1.datum.boundary.linearEquiv x w) =
      (f i).linearEquiv x ((ai i).1.datum.boundary.linearEquiv x
        (((e i).linearEquiv x).symm ((e i).linearEquiv x w)))
    rw [LinearEquiv.symm_apply_apply]
  -- Smooth each original restricted pair, selecting the resulting elliptic triple only once.
  have hrep := fun i : Fin k ↦ (c i).exists_equivariant_smooth_cotangent_replacement
    (VG := VG) (E₀.pullback (ι i)) (F₀.pullback (ι i)) (r i) (q i)
    (hSourceRank i) (hTargetRank i) (ρE.pullback (ι i) (heq i))
    (ρF.pullback (ι i) (heq i)) (hcControl i) (hc i)
  choose E F _hEr _hFq σE σF hσE hσF _e₀ _f₀ _he₀ _hf₀ _hc₀ s hi hs hb _hH hbclass
    using hrep
  let b (i : Fin k) : EquivariantSupportBundleTriple G
      (CotangentTotalSpace (n := n) (M := U i)) :=
    letI := modelTopology (EuclideanSpace ℂ (Fin (E i).rank)) (E i).Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin (F i).rank)) (F i).Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin (E i).rank)) (E i).Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin (F i).rank)) (F i).Fiber
    EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((p i : _ → _) *ᵖ (E i).Fiber))
      (FiniteBundle.ofFamily ((p i : _ → _) *ᵖ (F i).Fiber))
      (ellipticSymbolTriple (s i).val (s i).property.1.continuous (hi i))
      ((σE i).pullback (p i) (fun _ _ ↦ rfl))
      ((σF i).pullback (p i) (fun _ _ ↦ rfl)) (hb i)
  have hrestrict (i : Fin k) : equivariantCotangentClopenRestrict
      (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq z i = (b i).kZeroClass := by
    rw [← hclass]
    change equivariantSupportTripleKZeroPullback (j i) (hj i) (hjproper i)
      a₀.kZeroClass = (b i).kZeroClass
    rw [equivariantSupportTripleKZeroPullback_apply]
    exact (equivariantSupportTripleKZero_generator_relations.1 _ _ (hiso i)).trans
      (hbclass i)
  refine ⟨k, U, hne, hclosed, hdisjoint, hcover, actions, continuousActions,
    smoothActions, heq, compactPieces, b, ?_, hrestrict, ?_⟩
  · intro i
    exact ⟨E i, F i, σE i, σF i, hσE i, hσF i, s i, hi i, hs i, hb i, rfl⟩
  · -- The inverse of this same restriction map assembles this same selected family.
    let Φ := equivariantCotangentClopenEquiv
      (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq hdisjoint hcover
    apply Φ.injective
    change Φ z = Φ (Φ.symm (fun i ↦ (b i).kZeroClass))
    rw [Φ.apply_symm_apply]
    funext i
    exact hrestrict i

end AtiyahSinger
