/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedOrthogonalRepresentation
public import AtiyahSinger.Geometry.AssociatedSectionEvaluation
public import AtiyahSinger.Geometry.AssociatedSmoothBundleDescent
public import AtiyahSinger.Geometry.SmoothAtlasPullback

/-!
# Smoothness of the original associated coefficient evaluation

Public module ID: M1361.

Evaluation descends smoothly in the prescribed principal charts, the original
associated representation atlas and the original associated sphere-bundle
atlas. In a target principal chart it is the joint evaluation of the same
finite family at the same sphere point, with coefficients given by the base
representation transition. This is the smooth coefficient map needed for
the vertical kernel calculation in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {E : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (E y)]
  [∀ y, Module ℂ (E y)] [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (A : SmoothComplexBundleAtlas (n := r) E)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) E)
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1400000 in
-- Compare the original pullback frame and both associated quotient charts in one proof.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same representative evaluation is smooth in the two prescribed associated atlases. -/
theorem isSmoothAtlasBundleMap_associatedSectionEvaluation
    (s : V →ₗ[ℂ] A.smoothSections)
    (a : Hom (((associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle) :
        Z → B) *ᵖ C) D)
    (ha : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y)) :
    letI := associatedSphereChartedSpace S
    let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
    let d := linearModelDiffeomorph l Z
    letI := linearModelChartedSpace l Z
    let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
      (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
    IsSmoothAtlasBundleMap ((associatedOrthogonalRepresentationAtlas S ρ).pullback q hq)
      (associatedSphereSmoothBundleAtlas S A σ hσ) a.linearMap := by
  classical
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  let AC := associatedOrthogonalRepresentationAtlas S ρ
  let AP := AC.pullback q hq
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let t := associatedSphereTrivialization S
  have hCbase (i : B) : (AC.chart i).baseSet = (S.trivialization i).baseSet :=
    (associatedOrthogonalRepresentationChart_properties S ρ i).1
  have hCcoords := fun i ↦ (associatedOrthogonalRepresentationChart_properties S ρ i).2
  have hPbase (i : B) : (AP.chart i).baseSet = q ⁻¹' (AC.chart i).baseSet :=
    (AC.exists_pullbackChart q i).choose_spec.1
  have hPcoords (i : B) (w : TotalSpace Unit ((q : Z → B) *ᵖ C)) :
      (AP.chart i w).2 = (AC.chart i ⟨q w.proj, w.snd⟩).2 :=
    (AC.exists_pullbackChart q i).choose_spec.2 w
  have hDbase (j : B × A.Index) : (AD.chart j).baseSet =
      (t j.1).source ∩ (t j.1) ⁻¹' (Set.univ ×ˢ (A.chart j.2).baseSet) :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization j.1) (S.equivariant j.1) (A.chart j.2) (A.linear j.2)).choose_spec.1
  have hDcoords := fun j : B × A.Index ↦
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization j.1) (S.equivariant j.1) (A.chart j.2)
      (A.linear j.2)).choose_spec.2.2
  have htbase (b : B) : (t b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have htinverse := fun b ↦ (exists_associatedBundleTrivialization
    (F := OrthogonalSphere r) S.toIsPrincipalBundle
    (S.trivialization b) (S.equivariant b)).choose_spec.2.2
  have ht (b : B) : ContMDiffOn (𝓡 (n + r)) ((𝓡 n).prod (𝓡 r)) ∞
      (t b) (t b).source :=
    ((exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b).1.comp
      d.symm.contMDiff.contMDiffOn (fun _ hz ↦ hz)
  obtain ⟨f, hf, hfSmooth⟩ := exists_finiteSectionEvaluation A s
  have hEval (j : A.Index) :
      ContMDiffOn ((𝓡 r).prod 𝓘(ℝ, V)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun z : OrthogonalSphere r × V ↦ (A.chart j ⟨z.1, (s z.2).val z.1⟩).2)
        ((A.chart j).baseSet ×ˢ Set.univ) := by
    apply (hfSmooth j).congr
    intro z _
    rw [hf]
  -- This formula uses any representative of z, with only equality transport of the base.
  have ha' (p : P) (y : OrthogonalSphere r) (z : Z)
      (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z)
      (hp : projection p = q z) (v : V) :
      a.linearMap z (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y hz ((s v).val y) := by
    subst z
    exact ha p y v
  refine ⟨contMDiff_id, ?_⟩
  intro i j k
  change B at i
  change B × A.Index at j
  change Fin ρ.dimension at k
  let U := (AP.chart i).baseSet ∩ (AD.chart j).baseSet
  have hregion (z : Z) (hz : z ∈ U) :
      q z ∈ (AC.chart i).baseSet ∩ (AC.chart j.1).baseSet ∧
        z ∈ (t j.1).source ∧ (t j.1 z).2 ∈ (A.chart j.2).baseSet := by
    have hD := hDbase j ▸ hz.2
    have hproj : q z ∈ (AC.chart j.1).baseSet := by
      rw [hCbase, ← htbase]
      exact (t j.1).mem_source.mp hD.1
    have hsource : q z ∈ (AC.chart i).baseSet := by
      simpa only [hPbase i, Set.mem_preimage] using hz.1
    exact ⟨⟨hsource, hproj⟩, hD.1, hD.2.2⟩
  let c (b : B) : V := (AC.chart j.1 ((AC.chart i).toPartialEquiv.symm (b, Pi.single k 1))).2
  -- Only the original base transition changes the coefficient in this target principal chart.
  have hc : ContMDiffOn (𝓡 (n + r)) 𝓘(ℝ, V) ∞ (fun z : Z ↦ c (q z)) U :=
    (AC.contMDiffOn_coordChange i j.1 k).comp hq.contMDiffOn
      (fun z hz ↦ (hregion z hz).1)
  have hy : ContMDiffOn (𝓡 (n + r)) (𝓡 r) ∞ (fun z : Z ↦ (t j.1 z).2) U :=
    contMDiff_snd.comp_contMDiffOn ((ht j.1).mono (fun z hz ↦ (hregion z hz).2.1))
  have h := (hEval j.2).comp (hy.prodMk hc)
    (fun z hz ↦ ⟨(hregion z hz).2.2, Set.mem_univ _⟩)
  apply h.congr
  intro z hz
  rw [dite_eq_left hz.1]
  let v := (AP.frameLinearEquiv i z hz.1).symm (Pi.single k 1)
  have hCsource : (⟨q z, v⟩ : TotalSpace Unit C) =
      (AC.chart i).toPartialEquiv.symm (q z, Pi.single k 1) := by
    have hv : (AC.chart i ⟨q z, v⟩).2 = Pi.single k 1 := by
      rw [← hPcoords i ⟨z, v⟩]
      exact (AP.frameLinearEquiv i z hz.1).apply_symm_apply _
    symm
    calc
      (AC.chart i).toPartialEquiv.symm (q z, Pi.single k 1) =
          (AC.chart i).toPartialEquiv.symm (q z, (AC.chart i ⟨q z, v⟩).2) := by rw [hv]
      _ = ⟨q z, v⟩ := (AC.chart i).symm_apply_mk_proj (x := ⟨q z, v⟩)
          ((AC.chart i).mem_source.mpr (hregion z hz).1.1)
  have hjS : q z ∈ (S.trivialization j.1).baseSet :=
    hCbase j.1 ▸ (hregion z hz).1.2
  let p := (S.trivialization j.1).toPartialEquiv.symm (q z, 1)
  have hp : projection p = q z := (S.trivialization j.1).proj_symm_apply' hjS
  have hzrep : associatedBundleMk G P (OrthogonalSphere r) p (t j.1 z).2 = z := by
    have hfirst : (t j.1 z).1 = q z := (t j.1).coe_fst (hregion z hz).2.1
    dsimp only [p]
    erw [← htinverse j.1 (q z) (t j.1 z).2 hjS]
    rw [← hfirst]
    exact (t j.1).left_inv (hregion z hz).2.1
  have hv : v = associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation
      p hp (c (q z)) := by
    apply (AC.frameLinearEquiv j.1 (q z) (hregion z hz).1.2).injective
    change (AC.chart j.1 ⟨q z, v⟩).2 = _
    rw [hCsource]
    change c (q z) = (AC.chart j.1 ⟨q z,
      associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp (c (q z))⟩).2
    erw [hCcoords j.1 p (q z) hp _ hjS]
    dsimp only [p]
    erw [(S.trivialization j.1).apply_symm_apply' (x := (1 : G)) hjS]
    simp
  -- The local principal section has group coordinate one, leaving the original evaluation.
  change (AD.chart j ⟨z, a.linearMap z v⟩).2 = _
  rw [hv, ha' p _ z hzrep hp]
  erw [hDcoords j p _ z hzrep _ (hp.symm ▸ hjS)]
  dsimp only [p]
  erw [(S.trivialization j.1).apply_symm_apply' (x := (1 : G)) hjS]
  rw [σ.one_map]
  rfl

end AtiyahSinger
