/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasSectionMaps
public import AtiyahSinger.Geometry.FiniteCoefficientSmoothness
public import AtiyahSinger.Geometry.SmoothAssociatedSectionEvaluation

/-!
# Smooth coefficient sections detected on the full associated fiber

For an injective finite family of sphere sections, its associated evaluation
preserves and detects smoothness of base coefficient sections. Detection uses
all original fiber evaluations as separating linear forms on the finite
coefficient space. It does not require a new basis, integration, or pointwise
injectivity of the evaluation map. This supplies the actual smooth coefficient
identification in the vertical kernel argument of SG III.13.6.
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
set_option maxHeartbeats 1600000 in
-- Compare finite coefficients and the original section in all prescribed quotient charts.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation along the entire associated fiber preserves and detects coefficient smoothness. -/
theorem isSmoothSection_associatedEvaluation_iff
    (s : V →ₗ[ℂ] A.smoothSections) (hs : Function.Injective s)
    (a : Hom (((associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle) :
        Z → B) *ᵖ C) D)
    (ha : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      a.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y))
    (u : ∀ b : B, C b) :
    letI := associatedSphereChartedSpace S
    let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
    letI := linearModelChartedSpace l Z
    let q := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    (associatedSphereSmoothBundleAtlas S A σ hσ).IsSmoothSection
        (fun z : Z ↦ a.linearMap z (u (q z))) ↔
      (associatedOrthogonalRepresentationAtlas S ρ).IsSmoothSection u := by
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
  have hPbase (i : B) : (AP.chart i).baseSet = q ⁻¹' (AC.chart i).baseSet :=
    (AC.exists_pullbackChart q i).choose_spec.1
  have hPcoords := fun i ↦ (AC.exists_pullbackChart q i).choose_spec.2
  have hDbase (j : B × A.Index) : (AD.chart j).baseSet =
      (t j.1).source ∩ (t j.1) ⁻¹' (Set.univ ×ˢ (A.chart j.2).baseSet) :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization j.1) (S.equivariant j.1) (A.chart j.2) (A.linear j.2)).choose_spec.1
  have htbase (i : B) : (t i).baseSet = (S.trivialization i).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization i) (S.equivariant i)).choose_spec.1
  constructor
  · intro hu i
    change B at i
    let c (b : B) : V := (AC.chart i ⟨b, u b⟩).2
    -- All target-frame evaluations separate the original finite section coordinates.
    let I := Σ y : OrthogonalSphere r, Σ j : {j : A.Index // y ∈ (A.chart j).baseSet},
      Fin (A.rank j.val)
    let L (z : I) : V →ₗ[ℂ] ℂ :=
      (LinearMap.proj z.2.2).comp
        ((A.frameLinearEquiv z.2.1.val z.1 z.2.1.property).toLinearMap.comp
          ((LinearMap.proj z.1).comp (A.smoothSections.subtype.comp s)))
    have hL (v : V) (hv : ∀ z : I, L z v = 0) : v = 0 := by
      apply hs
      rw [map_zero]
      apply Subtype.ext
      funext y
      obtain ⟨j, hj⟩ := A.covers y
      apply (A.frameLinearEquiv j y hj).injective
      change (A.frameLinearEquiv j y hj) ((s v).val y) =
        (A.frameLinearEquiv j y hj) (0 : E y)
      rw [map_zero]
      funext k
      exact hv ⟨y, ⟨j, hj⟩, k⟩
    apply contMDiffOn_of_separating_linearForms (𝓡 n) L hL c
    intro w
    rcases w with ⟨y, ⟨j, hj⟩, k⟩
    let z (b : B) : Z := (t i).toPartialEquiv.symm (b, y)
    have hzSmooth : ContMDiffOn (𝓡 n) (𝓡 (n + r)) ∞ z (AC.chart i).baseSet := by
      have htinv := ((exists_associatedSphere_atlas S).choose_spec.2.2.2.1 i).2
      have hpair : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 r)) ∞
          (fun b : B ↦ (b, y)) (AC.chart i).baseSet :=
        (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      exact d.contMDiff.comp_contMDiffOn (htinv.comp hpair (by
        intro b hb
        exact (t i).mem_target.mpr ((htbase i).symm ▸ (hCbase i ▸ hb))))
    have hzb (b : B) (hb : b ∈ (AC.chart i).baseSet) :
        z b ∈ (AD.chart (i, j)).baseSet := by
      have hbS : b ∈ (t i).baseSet := (htbase i).symm ▸ (hCbase i ▸ hb)
      rw [hDbase]
      refine ⟨(t i).map_target ((t i).mem_target.mpr hbS), ?_⟩
      change (t i ((t i).toPartialEquiv.symm (b, y))) ∈
        Set.univ ×ˢ (A.chart j).baseSet
      erw [(t i).apply_symm_apply' (x := y) hbS]
      exact ⟨Set.mem_univ _, hj⟩
    have hlocal := (hu (i, j)).comp hzSmooth hzb
    have heq (b : B) (hb : b ∈ (AC.chart i).baseSet) :
        (AD.chart (i, j) ⟨z b, a.linearMap (z b) (u (q (z b)))⟩).2 =
          (A.chart j ⟨y, (s (c b)).val y⟩).2 := by
      have hbS : b ∈ (S.trivialization i).baseSet := hCbase i ▸ hb
      let p := (S.trivialization i).toPartialEquiv.symm (b, 1)
      have hp : projection p = b := (S.trivialization i).proj_symm_apply' hbS
      have hzrep : z b = associatedBundleMk G P (OrthogonalSphere r) p y :=
        (exists_associatedBundleTrivialization (F := OrthogonalSphere r) S.toIsPrincipalBundle
          (S.trivialization i) (S.equivariant i)).choose_spec.2.2 b y hbS
      have hqz : q (z b) = b := by
        rw [hzrep]
        exact hp
      have huRep : u b = associatedVectorFiberMk S.toIsPrincipalBundle
          ρ.representation p hp (c b) := by
        apply (AC.frameLinearEquiv i b hb).injective
        change c b = (AC.chart i ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle
          ρ.representation p hp (c b)⟩).2
        erw [(associatedOrthogonalRepresentationChart_properties S ρ i).2 p b hp _ hbS]
        dsimp only [p]
        erw [(S.trivialization i).apply_symm_apply' (x := (1 : G)) hbS]
        simp
      have ha' : a.linearMap (z b) (u (q (z b))) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y hzrep.symm
            ((s (c b)).val y) := by
        have hu' : u (q (z b)) = associatedVectorFiberMk S.toIsPrincipalBundle
            ρ.representation p (hp.trans hqz.symm) (c b) := by
          have htransport (b' : B) (h : b' = b) :
              u b' = associatedVectorFiberMk S.toIsPrincipalBundle
                ρ.representation p (hp.trans h.symm) (c b) := by
            subst b'
            exact huRep
          exact htransport (q (z b)) hqz
        rw [hu']
        generalize hv : c b = v
        have hforall (z : Z) (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z)
            (hpz : projection p = q z) :
            a.linearMap z (associatedVectorFiberMk S.toIsPrincipalBundle
                ρ.representation p hpz v) =
              associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y hz ((s v).val y) := by
          subst z
          exact ha p y v
        exact hforall (z b) hzrep.symm (hp.trans hqz.symm)
      rw [ha']
      erw [(exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
        (S.trivialization i) (S.equivariant i) (A.chart j) (A.linear j)).choose_spec.2.2
        p y (z b) hzrep.symm _ (hp.symm ▸ hbS)]
      dsimp only [p]
      erw [(S.trivialization i).apply_symm_apply' (x := (1 : G)) hbS]
      rw [σ.one_map]
    have hcoords : ContMDiffOn (𝓡 n) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun b : B ↦ (A.chart j ⟨y, (s (c b)).val y⟩).2) (AC.chart i).baseSet :=
      hlocal.congr (fun b hb ↦ (heq b hb).symm)
    exact (contMDiffOn_pi_space.mp hcoords) k
  · intro hu
    -- Pull back the same smooth coefficient section and apply the same smooth evaluation map.
    have hup : AP.IsSmoothSection (fun z : Z ↦ u (q z)) := by
      intro i
      change B at i
      have h : ContMDiffOn (𝓡 (n + r)) 𝓘(ℝ, Fin (AC.rank i) → ℂ) ∞
          (fun z : Z ↦ (AC.chart i ⟨q z, u (q z)⟩).2) (AP.chart i).baseSet :=
        (hu i).comp hq.contMDiffOn (by
        intro z hz
        have hz' : z ∈ q ⁻¹' (AC.chart i).baseSet := hPbase i ▸ hz
        exact hz')
      apply h.congr
      intro z _
      exact hPcoords i ⟨z, u (q z)⟩
    exact (isSmoothAtlasBundleMap_associatedSectionEvaluation S A σ hσ ρ s a ha).map_section
      AP AD a.linearMap ⟨fun z ↦ u (q z), hup⟩

end AtiyahSinger

