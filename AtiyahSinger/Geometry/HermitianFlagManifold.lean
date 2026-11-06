/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.EmbeddedAtlas
public import AtiyahSinger.Geometry.HermitianFlagSpaceAtlas
public import AtiyahSinger.Geometry.SmoothHermitianFlagAtlas
public import AtiyahSinger.Geometry.SmoothHermitianFlagLocalProducts
public import AtiyahSinger.Topology.HermitianFlagBundle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.LocalAtTarget

/-!
# The smooth proper flag fibration on the original projection space

Public module ID: M1266.

C01, SG III.11, Proposition 11.1, pp.225--226. The standard flag carrier is
the existing subtype of orthogonal projection tuples. Its smooth structure
is the embedded one in the actual finite-dimensional space of endomorphism
tuples, of real dimension r(r-1). The original total flag topology is retained.

The supplied original smooth bundle atlas and the same smooth Hermitian
metric construct the smooth flag charts. Arbitrary continuous native charts
are not presumed smooth. Their sole role is the existing flag topology.
Smooth local products, and the actual projector columns in the original
smooth frames, tie the chosen total atlas to the original geometric objects.
The total model has real dimension n+r(r-1), including rank zero.

Properness is the standard topological strengthening: local products with
a compact flag fiber give a universally closed projection over any base.
The smooth statement requires a smooth base, but not a compact, connected,
nonempty, or positive-dimensional one. All constructions use the original topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable (r : ℕ)

/-- The actual standard projection flag space is a compact finite-dimensional space. -/
theorem compactSpace_hermitianFlagSpace :
    CompactSpace (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
      InnerProductSpace.toCore) := by
  /- Stage 1: place the original tuples in the finite-dimensional real normed
  space of r complex endomorphisms. Self-adjoint idempotents have norm at most
  one. Their rank-one condition can be written as trace one on the idempotent
  locus, so all defining conditions cut out a closed bounded subset there.
  Stage 2: finite-dimensional compactness gives compactness of this exact
  subtype. At rank zero the tuple space and flag subtype are singletons. -/
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let L := V →L[ℂ] V
  let : ProperSpace L := FiniteDimensional.proper ℂ L
  let tr : L →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ V).comp (ContinuousLinearMap.coeLM ℂ)
  -- On the idempotent locus, the original rank condition is the closed trace equation.
  have htrace (P : L) (hP : P.comp P = P) :
      tr P = (Module.finrank ℂ (LinearMap.range P.toLinearMap) : ℂ) := by
    have hidem : IsIdempotentElem P.toLinearMap := by
      change P.toLinearMap.comp P.toLinearMap = P.toLinearMap
      exact congrArg ContinuousLinearMap.toLinearMap hP
    exact (LinearMap.IsIdempotentElem.isProj_range P.toLinearMap hidem).trace
  have hrank (P : L) (hP : P.comp P = P) :
      Module.finrank ℂ (LinearMap.range P.toLinearMap) = 1 ↔ tr P = 1 := by
    rw [htrace P hP]
    norm_cast
  let S : Set (Fin r → L) := {P |
    (∀ i, (P i).comp (P i) = P i) ∧
    (∀ i, Module.finrank ℂ (LinearMap.range (P i).toLinearMap) = 1) ∧
    (∀ i j, i ≠ j → (P i).comp (P j) = 0) ∧
    (∑ i, P i) = ContinuousLinearMap.id ℂ V ∧
    ∀ i u v, inner ℂ (P i u) v = inner ℂ u (P i v)}
  let T : Set (Fin r → L) := {P |
    (∀ i, (P i).comp (P i) = P i) ∧
    (∀ i, tr (P i) = 1) ∧
    (∀ i j, i ≠ j → (P i).comp (P j) = 0) ∧
    (∑ i, P i) = ContinuousLinearMap.id ℂ V ∧
    ∀ i u v, inner ℂ (P i u) v = inner ℂ u (P i v)}
  have hST : S = T := by
    ext P
    constructor
    · intro hP
      exact ⟨hP.1, fun i ↦ (hrank (P i) (hP.1 i)).mp (hP.2.1 i), hP.2.2⟩
    · intro hP
      exact ⟨hP.1, fun i ↦ (hrank (P i) (hP.1 i)).mpr (hP.2.1 i), hP.2.2⟩
  -- Every remaining equation is preserved under limits in the actual operator topology.
  have hidem : IsClosed {P : Fin r → L | ∀ i, (P i).comp (P i) = P i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦
      isClosed_eq ((continuous_apply i).clm_comp (continuous_apply i)) (continuous_apply i)
  have htr : IsClosed {P : Fin r → L | ∀ i, tr (P i) = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦
      isClosed_eq (tr.continuous_of_finiteDimensional.comp (continuous_apply i)) continuous_const
  have horth : IsClosed {P : Fin r → L | ∀ i j, i ≠ j → (P i).comp (P j) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_eq ((continuous_apply i).clm_comp (continuous_apply j)) continuous_const
  have hsum : IsClosed {P : Fin r → L | (∑ i, P i) = ContinuousLinearMap.id ℂ V} :=
    isClosed_eq (continuous_finsetSum _ (fun i _ ↦ continuous_apply i)) continuous_const
  have hself : IsClosed {P : Fin r → L |
      ∀ i (u v : V), inner ℂ (P i u) v = inner ℂ u (P i v)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
      isClosed_eq (((continuous_apply i).clm_apply continuous_const).inner continuous_const)
        (continuous_const.inner ((continuous_apply i).clm_apply continuous_const))
  have hSclosed : IsClosed S := by
    rw [hST]
    dsimp only [T]
    simp only [Set.ofPred_and]
    exact hidem.inter (htr.inter (horth.inter (hsum.inter hself)))
  -- The same self-adjoint idempotents have norm at most one; no frame is changed.
  have hbound (P : Fin r → L) (hP : P ∈ S) (i : Fin r) : ‖P i‖ ≤ 1 := by
    apply IsStarProjection.norm_le
    constructor
    · change (P i).comp (P i) = P i
      exact hP.1 i
    · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (hP.2.2.2.2 i)
  have hcompact : IsCompact (Set.pi Set.univ fun _ : Fin r ↦ Metric.closedBall (0 : L) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_closedBall (0 : L) 1
  have hScompact : IsCompact S := hcompact.of_isClosed_subset hSclosed (by
    intro P hP i _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound P hP i)
  -- The original flag carrier is exactly this closed subset, including the empty tuple at r=0.
  exact isCompact_iff_compactSpace.mp hScompact

/-- The standard projector subtype has its embedded smooth flag structure. -/
theorem exists_hermitianFlagSpace_atlas :
    ∃ hC : ChartedSpace (EuclideanSpace ℝ (Fin (r * (r - 1))))
        (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore),
      letI := hC
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (r * (r - 1)))) ∞
          (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore) ∧
        Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (r * (r - 1))))
          𝓘(ℝ, Fin r → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) ∞
          (fun p : HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
            InnerProductSpace.toCore ↦ p.val) := by
  /- The actual Gram slice gives local unitary frames with positive real
  diagonal and r(r-1) real free coordinates. Normalizing the projected
  reference vectors gives the inverse on the original projection subtype.
  These charts have smooth ambient coordinates and smooth parametrizations;
  their genuine inverse identity supplies an injective inclusion derivative.
  The embedded-atlas criterion preserves that original subtype topology. -/
  exact exists_embeddedAtlas _ (exists_hermitianFlagLocalChart r)

/-- The standard atlas chosen on the existing projection subtype. -/
@[reducible]
def hermitianFlagSpaceChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (r * (r - 1))))
      (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore) :=
  (exists_hermitianFlagSpace_atlas r).choose

/-- The selected standard flag atlas is a smooth manifold atlas. -/
instance hermitianFlagSpaceIsManifold :
    letI := hermitianFlagSpaceChartedSpace r
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (r * (r - 1)))) ∞
      (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore) :=
  (exists_hermitianFlagSpace_atlas r).choose_spec.1

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianFlagTopology

/-- The original flag projection is proper, even over a noncompact arbitrary base. -/
theorem hermitianFlagProjection_isProperMap :
    IsProperMap (hermitianFlagProjection r E h) := by
  /- Stage 1: use the existing actual local flag trivializations. On each
  target neighborhood the projection is the product projection with the
  compact standard flag fiber, hence it is closed and has compact fibers.
  Stage 2: closedness is local at the target and every fiber is compact.
  The continuous closed-map/compact-fiber criterion gives IsProperMap.
  No Hausdorff, compactness, smoothness or positive-rank assumption is used. -/
  classical
  let F := HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore
  let : CompactSpace F := compactSpace_hermitianFlagSpace r
  let p : HermitianFlagBundle r E h → M := hermitianFlagProjection r E h
  choose e he using exists_hermitianFlagTrivialization r E h
  -- The actual trivializations give an open cover of the original base.
  let U : M → TopologicalSpace.Opens M := fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.of_sets (fun x ↦ (e x).open_baseSet)
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact Set.mem_iUnion.mpr ⟨x, he x⟩
  -- On each member the restricted projection is the compact-fiber product projection.
  have hclosed : IsClosedMap p := by
    apply hU.isClosedMap_iff_restrictPreimage.mpr
    intro x
    let H := (e x).preimageHomeomorph (Set.Subset.rfl : (e x).baseSet ⊆ (e x).baseSet)
    have hp : (U x).1.restrictPreimage p = Prod.fst ∘ H := by
      funext z
      simp only [H, Function.comp_apply, Trivialization.preimageHomeomorph_apply]
      rfl
    rw [hp]
    exact isClosedMap_fst_of_compactSpace.comp H.isClosedMap
  -- Each original fiber is homeomorphic to that same compact standard flag space.
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(hermitianFlagProjection r E h).continuous, hclosed, ?_⟩
  intro x
  exact isCompact_iff_compactSpace.mpr
    ((e x).preimageSingletonHomeomorph (he x)).symm.compactSpace

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (A : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    SmoothComplexBundleAtlas (n := n) E)
  (hh : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    A.IsSmoothHermitianMetric h)

include hM hh

open Classical in
/-- The original smooth frames give the actual flag bundle its smooth fibration atlas. -/
theorem exists_hermitianFlag_atlas :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := hermitianFlagSpaceChartedSpace r
    ∃ hC : ChartedSpace (EuclideanSpace ℝ (Fin (n + r * (r - 1))))
        (HermitianFlagBundle r E h),
      letI := hC
      IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1)))) ∞
          (HermitianFlagBundle r E h) ∧
        ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (hermitianFlagProjection r E h) ∧
        Manifold.IsSubmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (hermitianFlagProjection r E h) ∧
        (∀ x : M, ∃ e : Trivialization
            (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
            (hermitianFlagProjection r E h : HermitianFlagBundle r E h → M),
          x ∈ e.baseSet ∧
            ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
              (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
                𝓘(ℝ, EuclideanSpace ℝ (Fin (r * (r - 1))))) ∞ e e.source ∧
            ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
                𝓘(ℝ, EuclideanSpace ℝ (Fin (r * (r - 1)))))
              𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1)))) ∞
              e.toOpenPartialHomeomorph.symm e.target) ∧
        ∀ (i : A.Index) (j : Fin r) (k : Fin (A.rank i)),
          ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
            𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
            (fun p : HermitianFlagBundle r E h ↦
              if hp : p.1 ∈ (A.chart i).baseSet then
                A.frameLinearEquiv i p.1 hp
                  (p.2.val j ((A.frameLinearEquiv i p.1 hp).symm (Pi.single k 1)))
              else 0)
            ((hermitianFlagProjection r E h) ⁻¹' (A.chart i).baseSet) := by
  /- Stage 1: orthonormalize each original A-frame with the specified metric h.
  Smooth Gram entries and strictly positive normalization denominators give
  smooth frame and inverse matrices. Conjugating actual projections by these
  frames gives local products with the standard embedded flag fiber.
  Stage 2: these products are homeomorphisms for the existing induced flag
  topology: compare the A-frame with any original continuous native frame.
  Smooth unitary frame changes act by smooth conjugation on projector tuples.
  The standard embedded atlas therefore gives smooth total chart transitions.
  Stage 3: combine base coordinates with the r(r-1) real flag coordinates,
  identifying the finite product with the displayed real model of dimension
  n+r(r-1). The local products and their inverses are smooth in this atlas.
  The unchanged base projection is a smooth submersion in these products.
  Stage 4: conjugate projector matrices back to every original A-frame.
  Smoothness of these actual columns ties the total atlas to those frames,
  independently of whichever continuous native atlas represented the topology.
  The empty tuple at r=0 retains the base coordinate and gives the identity
  fibration; no nonempty, positive-rank or compact-base hypothesis is used. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := hermitianFlagSpaceChartedSpace r
  choose U hU s hs t htBase htForward htInv a b ha hb haApply hbApply using
    exists_smoothHermitianFlagLocalProduct r E h A hh
  let g : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (r * (r - 1)))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + r * (r - 1))) := EuclideanSpace.finAddEquivProd.symm
  obtain ⟨C, hm, hp, hsub, htSmooth, hcolumns⟩ := exists_hermitianFlagAtlas_of_localFrames
    E h A (exists_hermitianFlagSpace_atlas r).choose_spec.2 U (fun x ↦ ⟨x, hU x⟩)
    s hs t htBase htForward htInv a b ha hb haApply hbApply g
  let := C
  refine ⟨C, hm, hp, hsub, ?_, hcolumns⟩
  intro x
  refine ⟨t x, ?_, (htSmooth x).1, (htSmooth x).2⟩
  rw [htBase x]
  exact hU x

/-- The chosen smooth atlas on the original full flag bundle and original topology. -/
@[reducible]
def hermitianFlagChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + r * (r - 1))))
      (HermitianFlagBundle r E h) :=
  (exists_hermitianFlag_atlas r E h A hh).choose

/-- The selected actual total flag atlas is smooth. -/
instance hermitianFlagIsManifold :
    letI := hermitianFlagChartedSpace r E h A hh
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1)))) ∞
      (HermitianFlagBundle r E h) :=
  (exists_hermitianFlag_atlas r E h A hh).choose_spec.1

/-- The original projection bundled with smoothness for the selected total atlas. -/
def smoothHermitianFlagProjection :
    letI := hermitianFlagChartedSpace r E h A hh
    ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (HermitianFlagBundle r E h) M ∞ :=
  ⟨hermitianFlagProjection r E h,
    (exists_hermitianFlag_atlas r E h A hh).choose_spec.2.1⟩

set_option linter.defProp false in
/-- The unchanged projection is a submersion for this same chosen total atlas. -/
def hermitianFlagProjection_isSubmersion :
    letI := hermitianFlagChartedSpace r E h A hh
    Manifold.IsSubmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + r * (r - 1))))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (hermitianFlagProjection r E h) :=
  (exists_hermitianFlag_atlas r E h A hh).choose_spec.2.2.1

end AtiyahSinger.ComplexBundle
