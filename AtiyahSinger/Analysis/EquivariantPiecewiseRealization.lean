/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.EquivariantPiecewiseSymbol
public import AtiyahSinger.Analysis.EquivariantQuantization
public import AtiyahSinger.Geometry.EquivariantSmoothDensity

/-!
# Piecewise equivariant elliptic operators representing original cotangent K classes

Public module ID: M0551.

Every original equivariant cotangent support K class over a compact smooth
base admits a finite invariant clopen family of actual order-zero equivariant
elliptic PDOs. Their displayed homogeneous principal symbols are precisely the
symbols of the original local K representatives. The same selected generator
family computes the original restrictions and reconstructs the input class.

Each actual open submanifold carries a chosen invariant positive smooth
measure for its inherited Borel structure. The measure, the regularization
presentation and the actual PDO are explicitly retained in the local output.
No invariant quantization presentation, common global fiber rank, or equality
of the source and target ranks is assumed. Empty bases and dimension zero
remain allowed. This is an existence theorem before analytic-index descent
through the original equivariant compact-support K relations.

SG III.3 Theorem 3.19 supplies quantization, III.9 supplies equivariant
averaging, and III.13 Lemma 13.3 and the paragraph before (13.7), pp.245--246,
give the ordinary representative route. The original equivariant bundle and
support framework is ASI I Section 2. This precise rankwise realization
is a project supplement assembling bundle replacement, controlled boundary
smoothing, clopen decomposition and uniform lower-order averaging. The proof
retains the same symbol, measure, presentation and operator witnesses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [MeasurableSpace G] [hGB : BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hMB : BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

include hDim hLie hGC hGT hGB hM hT hSC hC hMB hAction

set_option maxHeartbeats 1000000 in
-- Preserve the original dependent family of actions, symbols and operator witnesses.
/-- Every original cotangent K class has coherent piecewise equivariant elliptic PDOs. -/
theorem exists_piecewise_equivariant_elliptic_operator :
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
                    fun _i ↦ ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
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
                        ∃ (hσE : σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG))
                          (hσF : σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG)),
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
                                bi τE τF hbi ∧
                              ∃ μ : Measure (U i),
                                ∃ hμ : IsSmoothPositiveMeasure (n := n) μ,
                                  letI := hμ
                                  (∀ g : G, Measure.map (fun x : U i ↦ g • x) μ = μ) ∧
                                  ∃ R : QuantizationPresentation
                                      (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber,
                                    ∃ P : PseudodifferentialOperator
                                        (n := n) (r := E.rank) (q := F.rank)
                                        E.Fiber F.Fiber μ 0,
                                      P.IsEquivariant 𝓘(ℝ, VG) σE σF hσE hσF ∧
                                      P.IsElliptic ∧
                                      P.principalSymbol =
                                        globalPrincipalSymbolClass E.Fiber F.Fiber 0
                                          (R.regularizedSymbol 0
                                            s.val s.property.1 s.property.2)) ∧
                    (∀ i, equivariantCotangentClopenRestrict
                      (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq z i = (b i).kZeroClass) ∧
                    z = (equivariantCotangentClopenEquiv
                      (n := n) (G := G) 𝓘(ℝ, VG) U hclosed heq hdisjoint hcover).symm
                        (fun i ↦ (b i).kZeroClass) := by
  /- Stage 1: apply exists_piecewise_equivariant_homogeneous_symbol to
  the original z. Retain its actual occupied invariant clopen partition,
  original restricted actions, compact-piece certificates and single b_i
  family. For each piece keep the same smooth E and F, smooth actions,
  homogeneous symbol s, ellipticity and off-zero equivariance. Its b_i is
  exactly the selected ellipticSymbolTriple with the displayed pullback
  actions; both the local class equation and global reconstruction already
  use this family. Do not select another symbol to realize the same class.
  Stage 2: the actual U_i inherits the original Borel space and open
  smooth charts. On this same compact base choose an invariant positive
  smooth measure using exists_invariant_smoothPositiveMeasure. Retain its
  positive smoothness certificate and every original action pushforward
  equation. These chosen measures are part of the conclusion, not new
  restrictions on z, and no common ambient measure is silently imposed.
  Stage 3: choose one actual finite QuantizationPresentation R for the
  selected E and F. Its regularization of s has a principal quotient
  class fixed by every g: apply equivariant_regularizedSymbol_class_eq_iff
  with R on both sides and exactly the off-zero equivariance of s.
  The presentation and its cutoffs need not be group invariant.
  Stage 4: apply exists_equivariant_principalSymbol to that very class
  and the chosen measure. Its average construction returns an actual
  order-zero equivariant PDO P with precisely the displayed principal
  equality. Its class preservation uses the earlier uniform lower-order
  averaging argument; pointwise lower-order membership alone is not enough.
  The existing isElliptic_iff_homogeneous, with this same R and s, makes
  P elliptic. No assertion about an arbitrary homogeneous representative
  of a general principal quotient element is needed.
  Stage 5: retain b_i, s, its original pulled actions, the new measure,
  R and P together. The original restriction and reconstruction equations
  are unchanged because these are the same previously selected b_i.
  Dependent choice packages the local operator data without another
  selection for their K classes. Independent ranks, empty occupied index
  sets and zero-dimensional punctured domains use the same statements.
  This provides representatives only: arbitrary stable K equivalence,
  merely continuous boundary homotopies and independence of partitions
  are handled by separate representation-valued index comparisons. -/
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  -- Keep the already selected local symbols and the family of their exact elliptic triples.
  obtain ⟨k, U, hne, hclosed, hdisjoint, hcover, actions, continuousActions,
    smoothActions, heq, compactPieces, b, hlocal, hrestrict, hglobal⟩ :=
      exists_piecewise_equivariant_homogeneous_symbol (VG := VG) (n := n) z
  let := actions
  let := continuousActions
  let := smoothActions
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
  refine ⟨k, U, hne, hclosed, hdisjoint, hcover, actions, continuousActions,
    smoothActions, heq, compactPieces, b, ?_, hrestrict, hglobal⟩
  intro i
  obtain ⟨E, F, σE, σF, hσE, hσF, s, hi, hs, hbi, hbiEq⟩ := hlocal i
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  -- Choose an invariant positive density on this same inherited open submanifold.
  obtain ⟨μ, hμ, hμinv⟩ :=
    exists_invariant_smoothPositiveMeasure G 𝓘(ℝ, VG) (n := n) (M := U i)
  let := hμ
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  have hfixed (g : G) :
      equivariantPrincipalSymbolRepresentation 𝓘(ℝ, VG) σE σF hσE hσF 0 g
        (globalPrincipalSymbolClass E.Fiber F.Fiber 0
          (R.regularizedSymbol 0 s.val s.property.1 s.property.2)) =
        globalPrincipalSymbolClass E.Fiber F.Fiber 0
          (R.regularizedSymbol 0 s.val s.property.1 s.property.2) :=
    (R.equivariant_regularizedSymbol_class_eq_iff 𝓘(ℝ, VG) σE σF hσE hσF R 0 s s g).mpr
      (hs g)
  -- Quantize that very class; the same displayed homogeneous symbol proves ellipticity.
  obtain ⟨P, hPeq, hPclass⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    𝓘(ℝ, VG) σE σF hσE hσF (μ := μ) 0 _ hfixed
  exact ⟨E, F, σE, σF, hσE, hσF, s, hi, hs, hbi, hbiEq,
    μ, hμ, hμinv, R, P, hPeq, (P.isElliptic_iff_homogeneous R s hPclass).mpr hi, hPclass⟩

end AtiyahSinger
