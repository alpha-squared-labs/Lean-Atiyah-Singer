/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.HermitianProjectiveCoordinates
public import AtiyahSinger.Topology.HermitianProjectiveTrivialization
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.LocalAtTarget

/-!
# Compactness of the actual Hermitian projective and flag bundles

Public module ID: M1879.

The original orthogonal projective space is the continuous image of its unit
sphere. Its existing local trivializations make the projective projection
proper, hence the actual total space is compact over a compact base. Both the
actual projective and flag bundles are Hausdorff over a Hausdorff base, by
their embeddings into the original native endomorphism bundles. Flag-fiber
compactness and properness already occur in `HermitianFlagManifold` and are
not reproved here.

Source: the standard compactness argument for projective and flag bundles,
used here to retain compact bases in the splitting and Thom comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original finite-dimensional orthogonal projective space is compact. -/
theorem compactSpace_hermitianProjectiveSpace :
    CompactSpace (HermitianProjectiveSpace V InnerProductSpace.toCore) := by
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  let S := Metric.sphere (0 : V) 1
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V) 1)
  have hne (v : S) : v.val ≠ 0 := by
    have hv : ‖v.val‖ = 1 := by
      simpa only [S, Metric.mem_sphere, dist_zero_right] using v.property
    intro hz
    rw [hz, norm_zero] at hv
    exact zero_ne_one hv
  let g : C(S, {v : V // v ≠ 0}) :=
    ⟨fun v ↦ ⟨v.val, hne v⟩, continuous_subtype_val.subtype_mk hne⟩
  let a : C({v : V // v ≠ 0}, HermitianProjectiveSpace V InnerProductSpace.toCore) :=
    ⟨fun v ↦ HermitianProjectiveSpace.ofVector v.val v.property,
      HermitianProjectiveSpace.continuous_ofVector⟩
  let f : C(S, HermitianProjectiveSpace V InnerProductSpace.toCore) := a.comp g
  have hsurj : Function.Surjective f := by
    intro P
    -- A unit normalization of any nonzero range vector represents the same actual projector.
    let L := LinearMap.range P.val.toLinearMap
    let : Nontrivial L := Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [P.property.2.1]
      exact zero_lt_one)
    obtain ⟨v, hv⟩ := exists_ne (0 : L)
    have hvne : v.val ≠ 0 := fun hz ↦ hv (Subtype.ext hz)
    have hPv : P.val v.val = v.val := by
      obtain ⟨w, hw⟩ := v.property
      rw [← hw]
      exact DFunLike.congr_fun P.property.1 w
    let w := ‖v.val‖⁻¹ • v.val
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hvne
    have hPw : P.val w = w := by
      change P.val (‖v.val‖⁻¹ • v.val) = ‖v.val‖⁻¹ • v.val
      exact ((P.val.restrictScalars ℝ).map_smul ‖v.val‖⁻¹ v.val).trans
        (congrArg (fun z ↦ ‖v.val‖⁻¹ • z) hPv)
    let z : S := ⟨w, by simpa only [S, Metric.mem_sphere, dist_zero_right] using hw⟩
    exact ⟨z, HermitianProjectiveSpace.ofVector_eq P w (hne z) hPw⟩
  exact Function.Surjective.compactSpace f.continuous hsurj

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology hermitianFlagTopology

/-- The actual projective projection is proper over an arbitrary base. -/
theorem hermitianProjectiveProjection_isProperMap :
    IsProperMap (hermitianProjectiveProjection r E h) := by
  classical
  let F := HermitianProjectiveSpace (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore
  let : CompactSpace F := compactSpace_hermitianProjectiveSpace
  let p : HermitianProjectiveBundle r E h → X := hermitianProjectiveProjection r E h
  have hcharts (x : X) : ∃ e : Trivialization F p, x ∈ e.baseSet := by
    obtain ⟨e, he, _⟩ := exists_hermitianProjectiveTrivialization r E h x
    exact ⟨e, he⟩
  choose e he using hcharts
  -- Closedness is local at the target; every local product has the same compact fiber.
  let U : X → TopologicalSpace.Opens X := fun x ↦ ⟨(e x).baseSet, (e x).open_baseSet⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.of_sets (fun x ↦ (e x).open_baseSet)
    apply Set.eq_univ_iff_forall.mpr
    intro x
    exact Set.mem_iUnion.mpr ⟨x, he x⟩
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
  -- The same original chart identifies each fiber, including empty fibers in rank zero.
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(hermitianProjectiveProjection r E h).continuous, hclosed, ?_⟩
  intro x
  exact isCompact_iff_compactSpace.mpr
    ((e x).preimageSingletonHomeomorph (he x)).symm.compactSpace

/-- The original projective bundle over a compact base is compact. -/
theorem compactSpace_hermitianProjectiveBundle [CompactSpace X] :
    CompactSpace (HermitianProjectiveBundle r E h) := by
  constructor
  simpa only [Set.preimage_univ] using
    (hermitianProjectiveProjection_isProperMap r E h).isCompact_preimage isCompact_univ

/-- The original projective bundle over a Hausdorff base is Hausdorff. -/
theorem t2Space_hermitianProjectiveBundle [T2Space X] :
    T2Space (HermitianProjectiveBundle r E h) := by
  let V := EuclideanSpace ℂ (Fin r)
  let T := TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)
  let : T2Space T := t2Space_fiberBundleTotal (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)
  have hi : Topology.IsEmbedding (fun p : HermitianProjectiveBundle r E h ↦
      (p.1, (⟨p.1, p.2.val⟩ : T))) := by
    refine ⟨⟨rfl⟩, ?_⟩
    rintro ⟨x, P⟩ ⟨y, Q⟩ heq
    obtain ⟨hbase, hval⟩ := Prod.mk.inj heq
    dsimp at hbase
    subst y
    have hPQ : P.val = Q.val :=
      (TotalSpace.mk_inj (F := V →L[ℂ] V)
        (E := fun x ↦ E x →L[ℂ] E x) (b := x)).mp hval
    exact congrArg (Sigma.mk x) (Subtype.ext hPQ)
  exact hi.t2Space

/-- The original flag bundle over a Hausdorff base is Hausdorff. -/
theorem t2Space_hermitianFlagBundle [T2Space X] :
    T2Space (HermitianFlagBundle r E h) := by
  let V := EuclideanSpace ℂ (Fin r)
  let T := TotalSpace (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)
  let : T2Space T := t2Space_fiberBundleTotal (V →L[ℂ] V) (fun x ↦ E x →L[ℂ] E x)
  have hi : Topology.IsEmbedding (fun p : HermitianFlagBundle r E h ↦
      (p.1, fun i : Fin r ↦ (⟨p.1, p.2.val i⟩ : T))) := by
    refine ⟨⟨rfl⟩, ?_⟩
    rintro ⟨x, P⟩ ⟨y, Q⟩ heq
    obtain ⟨hbase, hval⟩ := Prod.mk.inj heq
    dsimp at hbase
    subst y
    have hPQ : P.val = Q.val := by
      funext i
      exact (TotalSpace.mk_inj (F := V →L[ℂ] V)
        (E := fun x ↦ E x →L[ℂ] E x) (b := x)).mp (congrFun hval i)
    exact congrArg (Sigma.mk x) (Subtype.ext hPQ)
  exact hi.t2Space

end AtiyahSinger.ComplexBundle
