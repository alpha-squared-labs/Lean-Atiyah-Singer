/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorLocalFiberCoordinates
public import AtiyahSinger.Geometry.AtlasLocalSectionSmoothness

/-!
# Smoothness through whole-fiber coordinate contractions

Public module ID: M0143.

For a whole-fiber family representing an associated tensor section, smoothness
of that section is equivalent to joint smoothness of every local base-frame
contraction in the base and sphere charts. Forward and inverse principal
charts identify the same tensor values.
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

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original local base contractions characterize smooth associated tensor sections. -/
theorem isSmoothSection_associatedSphereTensor_iff_jointFiberCoordinates
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (s : ∀ z : Z, T z)
    (u : ∀ p : P, dualTensorSections (E (projection p)) A.smoothSections)
    (hsu : ∀ (p : P) (y : OrthogonalSphere r),
      s (associatedBundleMk G P (OrthogonalSphere r) p y) =
        associatedSphereTensorFiberEquiv S E σ p y ((u p).val y)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).IsSmoothSection s ↔
      ∀ (b : B) (e : Trivialization (EuclideanSpace ℂ (Fin a))
        (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
        (i : Fin a) (j : A.Index),
        ContMDiffOn ((𝓡 n).prod (𝓡 r)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
          (fun z : B × OrthogonalSphere r ↦ (A.chart j ⟨z.2,
            (associatedSphereTensorLocalFiberCoordinates S E A b e he i u z.1).val z.2⟩).2)
          (((S.trivialization b).baseSet ∩ e.baseSet) ×ˢ (A.chart j).baseSet) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph lm Z
  let := linearModelChartedSpace lm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  let AC := AE.pullback q hq
  constructor
  · intro hs b e he i j
    let principal := S.trivialization b
    let t := associatedSphereTrivialization S b
    let p (x : B) := principal.toOpenPartialHomeomorph.symm (x, 1)
    let f (z : B × OrthogonalSphere r) :=
      associatedBundleMk G P (OrthogonalSphere r) (p z.1) z.2
    let U := (principal.baseSet ∩ e.baseSet) ×ˢ (A.chart j).baseSet
    have htbase : t.baseSet = principal.baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.1
    -- The normalized representatives are exactly the smooth inverse principal chart.
    have hf : ContMDiffOn ((𝓡 n).prod (𝓡 r)) (𝓡 (n + r)) ∞ f U := by
      have hinv := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b |>.2
      have hmem (z : B × OrthogonalSphere r) (hz : z ∈ U) : z ∈ t.target :=
        t.mem_target.mpr (htbase.symm ▸ hz.1.1)
      apply (d.contMDiff.comp_contMDiffOn (hinv.mono hmem)).congr
      intro z hz
      exact ((exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.2.2 z.1 z.2 hz.1.1).symm
    have hbase (z : B × OrthogonalSphere r) (hz : z ∈ U) :
        f z ∈ (AT.chart (⟨e, he⟩, (b, j))).baseSet := by
      have hpx : projection (p z.1) = z.1 := principal.proj_symm_apply' hz.1.1
      have hqz : q (f z) = z.1 := hpx
      have hg : (principal (p z.1)).2 = 1 :=
        congrArg Prod.snd (principal.apply_symm_apply' hz.1.1)
      have hforward : t (f z) = z := by
        have hp : projection (p z.1) ∈ principal.baseSet := hpx.symm ▸ hz.1.1
        have h : t (f z) = (projection (p z.1), (principal (p z.1)).2 • z.2) :=
          (exists_associatedBundleTrivialization S.toIsPrincipalBundle
            principal (S.equivariant b)).choose_spec.2.1 (p z.1) z.2 hp
        simpa only [hpx, hg, one_smul] using h
      have hDb : f z ∈ (AD.chart (b, j)).baseSet := by
        have hADbase : (AD.chart (b, j)).baseSet =
            t.source ∩ t ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
          (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
            principal (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
        rw [hADbase]
        refine ⟨t.mem_source.mpr (htbase.symm ▸ (hqz.symm ▸ hz.1.1)), ?_⟩
        rw [Set.mem_preimage, hforward]
        exact ⟨Set.mem_univ _, hz.2⟩
      have hEb : f z ∈ (AC.chart ⟨e, he⟩).baseSet := by
        have hEbase : (AC.chart ⟨e, he⟩).baseSet = q ⁻¹' e.baseSet :=
          (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.1
        have hmem : f z ∈ q ⁻¹' e.baseSet := by
          change q (f z) ∈ e.baseSet
          exact hqz.symm ▸ hz.1.2
        exact hEbase.symm ▸ hmem
      exact (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
        (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.1.symm ▸ ⟨hEb, hDb⟩
    apply contMDiffOn_pi_space.mpr
    intro k
    have hc := contMDiffOn_pi_space.mp
      ((hs (⟨e, he⟩, (b, j))).comp hf hbase) (finProdFinEquiv (i, k))
    apply hc.congr
    intro z hz
    have h := associatedSphereTensorLocalFiberCoordinates_chart (a := a)
      S E A σ hσ b e he i u j z.1 hz.1.1 hz.1.2 z.2 hz.2 k
    dsimp only at h
    rw [← hsu] at h
    exact h
  · intro hu
    apply AT.isSmoothSection_of_locally s
    intro z
    let b := q z
    let principal := S.trivialization b
    let t := associatedSphereTrivialization S b
    have htbase : t.baseSet = principal.baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.1
    have hzb : q z ∈ principal.baseSet := S.mem_baseSet b
    have hz : z ∈ t.source := t.mem_source.mpr (htbase.symm ▸ hzb)
    let e := trivializationAt (EuclideanSpace ℂ (Fin a)) E (q z)
    have he : MemTrivializationAtlas e := inferInstance
    have hxe : q z ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    obtain ⟨j, hy⟩ := A.covers (t z).2
    have hDbase : z ∈ (AD.chart (b, j)).baseSet := by
      have hbase : (AD.chart (b, j)).baseSet =
          t.source ∩ t ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
        (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
          principal (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
      exact hbase.symm ▸ ⟨hz, Set.mem_univ _, hy⟩
    have hEbase : z ∈ (AC.chart ⟨e, he⟩).baseSet := by
      have hbase : (AC.chart ⟨e, he⟩).baseSet = q ⁻¹' e.baseSet :=
        (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.1
      exact hbase.symm ▸ hxe
    have hTbase : z ∈ (AT.chart (⟨e, he⟩, (b, j))).baseSet :=
      (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
        (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.1.symm ▸ ⟨hEbase, hDbase⟩
    refine ⟨(⟨e, he⟩, (b, j)), hTbase, ?_⟩
    -- The forward original chart recovers the same base point and entire sphere parameter.
    have ht : ContMDiffAt (𝓡 (n + r)) ((𝓡 n).prod (𝓡 r)) ∞ t z := by
      have hts := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b |>.1
      have h := hts.comp d.symm.contMDiff.contMDiffOn (fun z hz ↦ hz)
      exact h.contMDiffAt (t.open_source.mem_nhds hz)
    have hparam : ContMDiffAt (𝓡 (n + r)) ((𝓡 n).prod (𝓡 r)) ∞
        (fun z' : Z ↦ (q z', (t z').2)) z := hq.contMDiffAt.prodMk ht.snd
    let U := (principal.baseSet ∩ e.baseSet) ×ˢ (A.chart j).baseSet
    have hmem : (q z, (t z).2) ∈ U := ⟨⟨hzb, hxe⟩, hy⟩
    have hopen : IsOpen U := (principal.open_baseSet.inter e.open_baseSet).prod
      (A.chart j).open_baseSet
    apply contMDiffAt_pi_space.mpr
    intro ik
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ik
    have hvec := ((hu b e he i j).contMDiffAt (hopen.mem_nhds hmem)).comp z hparam
    have hscalar := contMDiffAt_pi_space.mp hvec k
    apply hscalar.congr_of_eventuallyEq
    filter_upwards [t.open_source.mem_nhds hz,
      hparam.continuousAt (hopen.mem_nhds hmem)] with z' hzs hparams
    have h := associatedSphereTensorLocalFiberCoordinates_chart (a := a)
      S E A σ hσ b e he i u j (q z') hparams.1.1 hparams.1.2 (t z').2 hparams.2 k
    dsimp only at h
    rw [← hsu] at h
    let p := principal.toOpenPartialHomeomorph.symm (q z', 1)
    have hinverse : t.toOpenPartialHomeomorph.symm (q z', (t z').2) =
        associatedBundleMk G P (OrthogonalSphere r) p (t z').2 :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.2.2 (q z') (t z').2 hparams.1.1
    have hpair : (q z', (t z').2) = t z' := Prod.ext (t.proj_toFun z' hzs).symm rfl
    have hpoint : associatedBundleMk G P (OrthogonalSphere r) p (t z').2 = z' :=
      hinverse.symm.trans ((congrArg t.toOpenPartialHomeomorph.symm hpair).trans
        (t.toOpenPartialHomeomorph.left_inv hzs))
    exact (congrArg (fun x : Z ↦ (AT.chart (⟨e, he⟩, (b, j))
      ⟨x, s x⟩).2 (finProdFinEquiv (i, k))) hpoint).symm.trans h.symm

end AtiyahSinger
