/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.SmoothAtlasSections
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Bundle maps and two-sided cutoffs on the original atlas sections

Public module ID: M1103.

These are the usual pointwise bundle-map action and scalar multiplication
on smooth sections. They retain the original locally finite-rank bundles
without a compact base, a uniform rank or a new topology on their fibers.
Two-sided cutoff means the actual map u -> chi R(chi u), not a condition
only on the principal symbol. Its output and input support laws are stated
on the same actual section carrier.

An exterior map smooth off a compact set extends globally after enlarging
that set inside a prescribed neighborhood. The extension need not be a
global isomorphism. Its equality with the original map on the new exterior
retains every prescribed exterior identity or invertibility condition.

Sources: SG III.1 for smooth bundle maps, III.3 and III.13.4 for two-sided
localization. The local-matrix atlas adaptation and relative extension
are standard project supplements using these same actual maps and atlases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

open Classical in
/-- The original fiberwise map is smooth on the given region in the two original frame atlases. -/
def IsSmoothAtlasBundleMapOn (U : Set M) (c : ∀ x : M, E x →ₗ[ℂ] F x) : Prop :=
  ∀ (i : A.Index) (j : B.Index) (k : Fin (A.rank i)),
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
      (fun x : M ↦ if hx : x ∈ (A.chart i).baseSet then
        (B.chart j ⟨x, c x ((A.frameLinearEquiv i x hx).symm (Pi.single k 1))⟩).2
        else 0) (U ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet)

/-- A smooth original bundle map acts on the original smooth section space. -/
theorem IsSmoothAtlasBundleMap.map_section
    (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c)
    (u : A.smoothSections) : B.IsSmoothSection (fun x ↦ c x (u.val x)) := by
  /- In one common source and target frame, write the section coordinates
  as the finite linear combination of the smooth columns defining hc.
  Their coefficients are the original smooth coordinates of u. Finite
  sums and products are smooth on that overlap, and source frames cover
  each target frame domain. This keeps the actual fiber values and allows
  different ranks in separate components, including empty frame families. -/
  classical
  intro j x hx
  obtain ⟨i, hix⟩ := A.covers x
  -- On a source chart through x, the original smooth columns act on smooth coefficients.
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
      (fun y ↦ ∑ k : Fin (A.rank i), (A.chart i ⟨y, u.val y⟩).2 k •
        (if hy : y ∈ (A.chart i).baseSet then
          (B.chart j ⟨y, c y ((A.frameLinearEquiv i y hy).symm (Pi.single k 1))⟩).2
          else 0)) ((A.chart i).baseSet ∩ (B.chart j).baseSet) := by
    apply contMDiffOn_finsetSum
    intro k _
    have hcoeff := ((contMDiffOn_pi_space.mp (u.property i)) k).mono
      (Set.inter_subset_left (t := (B.chart j).baseSet))
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × (Fin (B.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
    exact hmul.contMDiff.comp_contMDiffOn (hcoeff.prodMk_space (hc.2 i j k))
  have hlocal := hsum.congr (f₁ := fun y ↦ (B.chart j ⟨y, c y (u.val y)⟩).2) ?_
  · have hpoint := hlocal.contMDiffAt
      (((A.chart i).open_baseSet.inter (B.chart j).open_baseSet).mem_nhds ⟨hix, hx⟩)
    exact hpoint.contMDiffWithinAt
  · intro y hy
    let L := (B.frameLinearEquiv j y hy.2).toLinearMap.comp
      ((c y).comp (A.frameLinearEquiv i y hy.1).symm.toLinearMap)
    have hexpand := congrArg L ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr
      ((A.frameLinearEquiv i y hy.1) (u.val y)))
    simp [L, map_sum, map_smul] at hexpand
    simpa [hy.1, SmoothComplexBundleAtlas.frameLinearEquiv] using hexpand.symm

/-- The actual pointwise action of the specified original smooth bundle map. -/
def atlasSmoothSectionMap (c : ∀ x : M, E x →ₗ[ℂ] F x)
    (hc : IsSmoothAtlasBundleMap A B c) : A.smoothSections →ₗ[ℂ] B.smoothSections where
  toFun u := ⟨fun x ↦ c x (u.val x), hc.map_section A B c u⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact (c x).map_add (u.val x) (v.val x)
  map_smul' z u := by
    apply Subtype.ext
    funext x
    exact (c x).map_smul z (u.val x)

/-- Smooth scalar multiplication preserves the original section coordinates. -/
theorem SmoothComplexBundleAtlas.isSmoothSection_fun_smul
    (χ : M → ℂ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ χ)
    (u : A.smoothSections) : A.IsSmoothSection (fun x ↦ χ x • u.val x) := by
  /- Original frame linearity identifies these coordinates with the scalar
  function χ times the original coordinates of u. Smooth multiplication
  on each finite coordinate space gives the result in every original frame.
  No global rank, compactness or section-space topology is needed. -/
  intro i
  have hmul : ContDiff ℝ ∞
      (fun p : ℂ × (Fin (A.rank i) → ℂ) ↦ p.1 • p.2) := contDiff_smul
  apply (hmul.contMDiff.comp_contMDiffOn
    (hχ.contMDiffOn.prodMk_space (u.property i))).congr
  intro x hx
  exact (A.linear i x hx).map_smul (χ x) (u.val x)

/-- Pointwise multiplication by a smooth scalar function on the original section space. -/
def atlasSectionMul (χ : M → ℂ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ χ) :
    A.smoothSections →ₗ[ℂ] A.smoothSections where
  toFun u := ⟨fun x ↦ χ x • u.val x, A.isSmoothSection_fun_smul χ hχ u⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact smul_add (χ x) (u.val x) (v.val x)
  map_smul' z u := by
    apply Subtype.ext
    funext x
    exact smul_comm (χ x) z (u.val x)

/-- The two projections of support are controlled on the actual original section operator. -/
def HasAtlasSectionOperatorSupport (K : Set M)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) : Prop :=
  (∀ u, closure {x | (P u).val x ≠ 0} ⊆ K) ∧
    ∀ u, Disjoint (closure {x | u.val x ≠ 0}) K → P u = 0

/-- The actual two-sided sandwich by the same real scalar cutoff on both original bundles. -/
def twoSidedAtlasSectionCutoff (R : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ) :
    A.smoothSections →ₗ[ℂ] B.smoothSections :=
  (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)).comp
    (R.comp (atlasSectionMul A (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ)))

/-- Two-sided cutoff gives both support controls and its original pointwise action. -/
theorem twoSidedAtlasSectionCutoff_properties
    (R : A.smoothSections →ₗ[ℂ] B.smoothSections) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ) :
    HasAtlasSectionOperatorSupport A B (tsupport χ) (twoSidedAtlasSectionCutoff A B R χ hχ) ∧
      ∀ (u : A.smoothSections) (x : M),
        (twoSidedAtlasSectionCutoff A B R χ hχ u).val x =
          (χ x : ℂ) •
            (R (atlasSectionMul A (fun y ↦ (χ y : ℂ))
              (Complex.ofRealCLM.contMDiff.comp hχ) u)).val x := by
  /- The outer multiplier makes every output vanish outside tsupport χ;
  taking closure preserves inclusion because that set is closed. If an
  input support is disjoint from tsupport χ, its inner scalar product is
  zero everywhere, so linearity gives zero output. The pointwise formula
  unfolds exactly these original two multipliers and R, with no symbol or
  kernel assumptions and no compactness restriction on the base. -/
  constructor
  · constructor
    · intro u
      apply closure_minimal ?_ (isClosed_tsupport χ)
      intro x hx
      by_contra houtside
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport houtside
      exact hx (by simp [twoSidedAtlasSectionCutoff, atlasSectionMul, hχx])
    · intro u hdisjoint
      -- Disjoint input support makes the inner multiplier the zero section.
      have hinner : atlasSectionMul A (fun y ↦ (χ y : ℂ))
          (Complex.ofRealCLM.contMDiff.comp hχ) u = 0 := by
        apply Subtype.ext
        funext x
        by_cases hχx : χ x = 0
        · simp [atlasSectionMul, hχx]
        · have hux : u.val x = 0 := by
            by_contra hux
            exact Set.disjoint_left.mp hdisjoint
              (subset_closure hux) (subset_closure hχx)
          simp [atlasSectionMul, hux]
      change (atlasSectionMul B (fun y ↦ (χ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hχ)) (R
          (atlasSectionMul A (fun y ↦ (χ y : ℂ))
            (Complex.ofRealCLM.contMDiff.comp hχ) u)) = 0
      rw [hinner, map_zero, map_zero]
  · intro u x
    rfl

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC in
/-- An original smooth exterior map extends globally after enlarging only its compact exception. -/
theorem exists_atlasZeroOrder_extension_of_exterior
    (K : Set M) (hK : IsCompact K) (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U)
    (b : ∀ x : M, E x →ₗ[ℂ] F x) (hb : IsSmoothAtlasBundleMapOn A B Kᶜ b) :
    ∃ L : Set M, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
      ∃ c : ∀ x : M, E x →ₗ[ℂ] F x,
        IsSmoothAtlasBundleMap A B c ∧ ∀ x : M, x ∉ L → c x = b x := by
  /- Stage 1: choose a compact neighborhood L of K inside U and a smooth
  real cutoff η equal to one near K and zero outside L. The existing cutoff
  construction applies on this Hausdorff second-countable smooth manifold;
  M itself need not be compact.
  Stage 2: set c=(1-η)b on the original fibers. Near K this is identically
  zero, independently of the arbitrary values of b there. On the exterior,
  local matrix smoothness of hb and the cutoff prove smoothness of c.
  Stage 3: outside L the cutoff is zero, hence c is exactly b there. Any
  specified exterior identity or bijectivity of b is retained by equality.
  No global inverse is asserted or required. Empty K, rank-zero fibers,
  disconnected bases and unbounded ranks on different components are allowed. -/
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨η, hηone, hηzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hK.isClosed hKL
  let c : ∀ x : M, E x →ₗ[ℂ] F x := fun x ↦ ((1 - η x : ℝ) : ℂ) • b x
  refine ⟨L, hL, hKL, hLU, c, ?_, ?_⟩
  · refine ⟨contMDiff_id, ?_⟩
    intro i j k x hx
    by_cases hxK : x ∈ K
    · -- Near K the cutoff is identically one, so every actual column is zero.
      have hηx : ∀ᶠ y in 𝓝 x, η y = 1 := hηone.filter_mono (nhds_le_nhdsSet hxK)
      have hzero : ∀ᶠ y in 𝓝 x,
          (if hy : y ∈ (A.chart i).baseSet then
            (B.chart j ⟨y, c y ((A.frameLinearEquiv i y hy).symm (Pi.single k 1))⟩).2
            else 0) = 0 := by
        filter_upwards [hηx, (B.chart j).open_baseSet.mem_nhds hx.2] with y hηy hBy
        by_cases hAy : y ∈ (A.chart i).baseSet
        · simp [hAy, c, hηy, (B.linear j y hBy).map_zero]
        · simp [hAy]
      exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
    · -- On the exterior the original column is smooth and is multiplied by a smooth scalar.
      have hcolumn := (hb i j k).contMDiffAt
        (((hK.isClosed.isOpen_compl.inter (A.chart i).open_baseSet).inter
          (B.chart j).open_baseSet).mem_nhds ⟨⟨hxK, hx.1⟩, hx.2⟩)
      have hscalar := Complex.ofRealCLM.contMDiff.comp
        ((contMDiff_const (c := (1 : ℝ))).sub η.contMDiff)
      have hmul : ContDiff ℝ ∞
          (fun p : ℂ × (Fin (B.rank j) → ℂ) ↦ p.1 • p.2) := contDiff_smul
      have hproduct := hmul.comp_contMDiffAt (hscalar.contMDiffAt.prodMk_space hcolumn)
      apply (hproduct.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [(B.chart j).open_baseSet.mem_nhds hx.2] with y hBy
      by_cases hAy : y ∈ (A.chart i).baseSet
      · simpa [hAy, c] using (B.linear j y hBy).map_smul
          (((1 - η y : ℝ) : ℂ)) (b y ((A.frameLinearEquiv i y hAy).symm (Pi.single k 1)))
      · simp [hAy]
  · intro x hx
    simp [c, hηzero x hx]

end AtiyahSinger
