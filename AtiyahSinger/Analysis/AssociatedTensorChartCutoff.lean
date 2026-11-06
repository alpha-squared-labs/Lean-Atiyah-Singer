/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorLocalFiberCoordinates
public import AtiyahSinger.Geometry.AssociatedSphereProductChart
public import AtiyahSinger.Geometry.AtlasChartLocalization
public import AtiyahSinger.Geometry.ChartLocalization

/-!
# Compact product cutoffs in the associated tensor atlas

Public module ID: M0139.

The cutoff is the product of the supplied base and sphere cutoffs.
Its frame index retains the base frame, principal center and sphere frame
in the base-first tensor atlas. Compactness and subordination use the same
principal trivialization and product coordinate chart. The localization
formula agrees with the normalized whole-fiber coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original base and sphere cutoffs in their actual associated tensor product chart. -/
def associatedSphereTensorChartCutoff
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (c : OpenPartialHomeomorph B X) (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y) (K : AtlasChartCutoff A d) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    AtlasChartCutoff (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ)
      (associatedSphereProductChart S b c d) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let dm := linearModelDiffeomorph e.symm Z
  let := linearModelChartedSpace e.symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp dm.symm.contMDiff
  let AC := AE.pullback q hq
  let t := associatedSphereTrivialization S b
  let cut (z : XY) : ℝ := C.cutoff (e z).1 * K.cutoff (e z).2
  -- The product cutoff stays in the exact compact product of the supplied supports.
  have hsupport : tsupport cut ⊆ e ⁻¹' (tsupport C.cutoff ×ˢ tsupport K.cutoff) := by
    apply closure_minimal ?_
      (((isClosed_tsupport C.cutoff).prod (isClosed_tsupport K.cutoff)).preimage e.continuous)
    intro z hz
    constructor
    · apply subset_tsupport
      intro h
      exact hz (by simp only [cut, h, zero_mul])
    · apply subset_tsupport
      intro h
      exact hz (by simp only [cut, h, mul_zero])
  have hcompact : HasCompactSupport cut := by
    have hprod := (C.compact_support.prod K.compact_support).image e.symm.continuous
    apply hprod.of_isClosed_subset (isClosed_tsupport cut)
    intro z hz
    exact ⟨e z, hsupport hz, e.symm_apply_apply z⟩
  refine {
    frameIndex := (⟨C.frame, C.frame_mem_atlas⟩, (b, K.frameIndex))
    cutoff := cut
    smooth_cutoff := (C.smooth_cutoff.comp (contDiff_fst.comp e.contDiff)).mul
      (K.smooth_cutoff.comp (contDiff_snd.comp e.contDiff))
    compact_support := hcompact
    support_subset := ?_ }
  intro z hz
  have hx := (hsupport hz).1
  have hy := (hsupport hz).2
  have hxt := (C.support_subset hx).1
  have hxf := (C.support_subset hx).2
  have hyt := (K.support_subset hy).1
  have hyf := (K.support_subset hy).2
  have hxb := hC ⟨(e z).1, hx, rfl⟩
  have htbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have htarg : (c.symm (e z).1, d.symm (e z).2) ∈ t.target :=
    t.mem_target.mpr (htbase.symm ▸ hxb)
  constructor
  · -- The original partial homeomorphisms are defined on this entire compact support.
    change z ∈ ((t.toOpenPartialHomeomorph.trans (c.prod d)).trans
      e.symm.toHomeomorph.toOpenPartialHomeomorph).target
    exact ⟨Set.mem_univ _, ⟨hxt, hyt⟩, htarg⟩
  · let w := t.toOpenPartialHomeomorph.symm (c.symm (e z).1, d.symm (e z).2)
    have hwsource : w ∈ t.source := t.toOpenPartialHomeomorph.map_target htarg
    have hwproj : q w = c.symm (e z).1 := t.proj_symm_apply htarg
    have hDbase : w ∈ (AD.chart (b, K.frameIndex)).baseSet := by
      have hbase : (AD.chart (b, K.frameIndex)).baseSet =
          t.source ∩ t ⁻¹' (Set.univ ×ˢ (A.chart K.frameIndex).baseSet) :=
        (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
          (S.trivialization b) (S.equivariant b) (A.chart K.frameIndex)
          (A.linear K.frameIndex)).choose_spec.1
      rw [hbase]
      refine ⟨hwsource, ?_⟩
      change t w ∈ Set.univ ×ˢ (A.chart K.frameIndex).baseSet
      have htw : t w = (c.symm (e z).1, d.symm (e z).2) :=
        t.toOpenPartialHomeomorph.right_inv htarg
      rw [htw]
      exact ⟨Set.mem_univ _, hyf⟩
    have hEbase : w ∈ (AC.chart ⟨C.frame, C.frame_mem_atlas⟩).baseSet := by
      have hwf : q w ∈ C.frame.baseSet := hwproj.symm ▸ hxf
      exact (AE.exists_pullbackChart q ⟨C.frame, C.frame_mem_atlas⟩).choose_spec.1.symm ▸ hwf
    change w ∈ (AT.chart (⟨C.frame, C.frame_mem_atlas⟩, (b, K.frameIndex))).baseSet
    have htensor := (exists_tensor_trivialization
      (AC.chart ⟨C.frame, C.frame_mem_atlas⟩) (AD.chart (b, K.frameIndex))
      (AC.linear ⟨C.frame, C.frame_mem_atlas⟩) (AD.linear (b, K.frameIndex))).choose_spec.1
    exact htensor.symm ▸ ⟨hEbase, hDbase⟩

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual upstairs cutoff coordinates equal the normalized whole-sphere coordinates. -/
theorem associatedSphereTensorChartCutoff_localizedFunction
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (c : OpenPartialHomeomorph B X) (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : d ∈ atlas Y (OrthogonalSphere r)) (K : AtlasChartCutoff A d) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
      (x : X) (y : Y) (i : Fin a) (j : Fin (A.rank K.frameIndex)),
      (associatedSphereTensorChartCutoff S E A σ hσ b c C hC d K).localizedFunction w
          (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (i, j)) =
        K.localize hd ((C.cutoff x : ℂ) •
          associatedSphereTensorLocalFiberCoordinates S E A b C.frame C.frame_mem_atlas i
            (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
            (c.symm x)) y j := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  intro w x y i j
  let L := associatedSphereTensorChartCutoff S E A σ hσ b c C hC d K
  let U := associatedSphereTensorLocalFiberCoordinates S E A b C.frame C.frame_mem_atlas i
    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w) (c.symm x)
  have hcut : L.cutoff (e.symm (x, y)) = C.cutoff x * K.cutoff y := by
    change C.cutoff (e (e.symm (x, y))).1 * K.cutoff (e (e.symm (x, y))).2 = _
    rw [e.apply_symm_apply]
  change L.localizedFunction w (e.symm (x, y)) (finProdFinEquiv (i, j)) =
    K.localizedFunction ((C.cutoff x : ℂ) • U) y j
  -- Away from either original support both actual coordinate expressions vanish.
  by_cases hx : x ∈ tsupport C.cutoff
  · by_cases hy : y ∈ tsupport K.cutoff
    · have hxt := (C.support_subset hx).1
      have hxf := (C.support_subset hx).2
      have hyt := (K.support_subset hy).1
      have hyf := (K.support_subset hy).2
      have hxb := hC ⟨x, hx, rfl⟩
      let t := associatedSphereTrivialization S b
      let z := associatedSphereProductChart S b c d
      let p := (S.trivialization b).toOpenPartialHomeomorph.symm (c.symm x, 1)
      have htbase : t.baseSet = (S.trivialization b).baseSet :=
        (exists_associatedBundleTrivialization S.toIsPrincipalBundle
          (S.trivialization b) (S.equivariant b)).choose_spec.1
      have htt : (c.symm x, d.symm y) ∈ t.target :=
        t.mem_target.mpr (htbase.symm ▸ hxb)
      have hzt : e.symm (x, y) ∈ z.target := by
        change e.symm (x, y) ∈ ((t.toOpenPartialHomeomorph.trans (c.prod d)).trans
          e.symm.toHomeomorph.toOpenPartialHomeomorph).target
        refine ⟨Set.mem_univ _, ?_⟩
        change e (e.symm (x, y)) ∈ (t.toOpenPartialHomeomorph.trans (c.prod d)).target
        rw [e.apply_symm_apply]
        exact ⟨⟨hxt, hyt⟩, htt⟩
      have hinverse : z.symm (e.symm (x, y)) =
          associatedBundleMk G P (OrthogonalSphere r) p (d.symm y) := by
        change t.toOpenPartialHomeomorph.symm
          (c.symm (e (e.symm (x, y))).1, d.symm (e (e.symm (x, y))).2) = _
        rw [e.apply_symm_apply]
        exact (exists_associatedBundleTrivialization S.toIsPrincipalBundle
          (S.trivialization b) (S.equivariant b)).choose_spec.2.2 (c.symm x) (d.symm y) hxb
      -- The same full fiber restriction recovers w in the original tensor frame.
      have hcoords := associatedSphereTensorLocalFiberCoordinates_chart (a := a)
        S E A σ hσ b C.frame C.frame_mem_atlas i
        (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
        K.frameIndex (c.symm x) hxb hxf (d.symm y) hyf j
      dsimp only at hcoords
      rw [associatedSphereTensorFiberRestriction_apply (a := a)
        S E A σ hσ p w (d.symm y)] at hcoords
      dsimp only [AtlasChartCutoff.localizedFunction]
      rw [ite_eq_left hzt, ite_eq_left hyt, hcut]
      simp only [atlasSectionInChart]
      change ((C.cutoff x * K.cutoff y : ℝ) : ℂ) *
          ((associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).chart
            (⟨C.frame, C.frame_mem_atlas⟩, (b, K.frameIndex))
            ⟨z.symm (e.symm (x, y)), w.val (z.symm (e.symm (x, y)))⟩).2
              (finProdFinEquiv (i, j)) =
        (K.cutoff y : ℂ) *
          (A.chart K.frameIndex ⟨d.symm y, (C.cutoff x : ℂ) • U.val (d.symm y)⟩).2 j
      rw [hinverse, ← hcoords]
      have hscale := congrFun ((A.linear K.frameIndex (d.symm y) hyf).map_smul
        (C.cutoff x : ℂ) (U.val (d.symm y))) j
      change (A.chart K.frameIndex ⟨d.symm y, (C.cutoff x : ℂ) • U.val (d.symm y)⟩).2 j =
        (C.cutoff x : ℂ) * (A.chart K.frameIndex ⟨d.symm y, U.val (d.symm y)⟩).2 j at hscale
      rw [hscale, Complex.ofReal_mul]
      ring
    · have hyzero := image_eq_zero_of_notMem_tsupport hy
      simp only [AtlasChartCutoff.localizedFunction, hcut, hyzero, mul_zero,
        Complex.ofReal_zero, zero_smul, ite_self, WithLp.ofLp_zero, Pi.zero_apply]
  · have hxzero := image_eq_zero_of_notMem_tsupport hx
    have hzero : ((C.cutoff x : ℂ) • U) = 0 := by rw [hxzero]; simp
    rw [hzero]
    have hKzero : K.localizedFunction 0 y = 0 := by
      change K.localize hd 0 y = 0
      rw [(K.isLinearMap_localize_extend hd).1.map_zero]
      rfl
    simp only [AtlasChartCutoff.localizedFunction, hcut, hxzero, zero_mul,
      Complex.ofReal_zero, zero_smul, ite_self, WithLp.ofLp_zero, Pi.zero_apply] at *
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin (A.rank K.frameIndex)) ↦ v j) hKzero).symm

end AtiyahSinger
