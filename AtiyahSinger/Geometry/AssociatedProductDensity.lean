/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorL2
public import AtiyahSinger.Geometry.AssociatedProductMeasureCharts
public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Geometry.DensityDiffeomorph
public import AtiyahSinger.Geometry.LocalDensity

/-!
# Positive smooth density of the actual associated product measure

Public module ID: M1061.

In each original principal chart, the actual associated Riesz measure is the
original product measure. Its local product density transports through that
same smooth associated chart. Smooth positivity is local, so this gives a
certificate for the original quotient and its specified full manifold model.
The measure itself is unchanged; no auxiliary choice of global density or
measurable principal section replaces it.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (μ : Measure B) (ν : Measure (OrthogonalSphere r))
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  [IsSmoothPositiveMeasure (n := n) μ] [IsSmoothPositiveMeasure (n := r) ν]
  (hν : ∀ g : Matrix.orthogonalGroup (Fin r) ℝ,
    Measure.map (fun y : OrthogonalSphere r ↦ g • y) ν = ν)
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual product measure is positive smooth on the original associated sphere. -/
theorem isSmoothPositiveMeasure_associatedProductMeasure :
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    IsSmoothPositiveMeasure (n := n + r)
      (associatedProductMeasure S.toIsPrincipalBundle μ ν hν) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℝ (Fin r)
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let J := 𝓘(ℝ, X × R)
  let I := 𝓡 (n + r)
  have hJI : (𝓡 n).prod (𝓡 r) = J := modelWithCornersSelf_prod.symm
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let : ChartedSpace (X × R) (B × Y) := prodChartedSpace _ _ _ _
  let : IsManifold J ∞ (B × Y) := by
    rw [← hJI]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓡 r) (n := ∞) B Y
  let dZ := linearModelDiffeomorph l Z
  let dP := linearModelDiffeomorph l (B × Y)
  let := linearModelChartedSpace l Z
  let := isManifold_linearModelChartedSpace l Z
  let := linearModelChartedSpace l (B × Y)
  let := isManifold_linearModelChartedSpace l (B × Y)
  let η := associatedProductMeasure S.toIsPrincipalBundle μ ν hν
  let : IsSmoothPositiveMeasure (n := n + r) (μ.prod ν) :=
    isSmoothPositiveMeasure_prod μ ν
  apply isSmoothPositiveMeasure_of_locally_comap
  intro z
  let b := associatedBundleProjection (F := Y) S.toIsPrincipalBundle z
  let t := associatedSphereTrivialization S b
  let U : Opens Z := ⟨t.source, t.open_source⟩
  let V : Opens (B × Y) := ⟨t.target, t.open_target⟩
  have hbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  refine ⟨U, t.mem_source.mpr (hbase.symm ▸ S.mem_baseSet b), ?_⟩
  -- Transport both directions of the same original chart through the specified linear models.
  have ht : ContMDiffOn I I ∞ t t.source := by
    have h := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b |>.1
    have h' : ContMDiffOn J J ∞ t t.source := by
      change ContMDiffOn J ((𝓡 n).prod (𝓡 r)) ∞ t t.source at h
      rw [hJI] at h
      exact h
    exact dP.contMDiff.comp_contMDiffOn
      (h'.comp dZ.symm.contMDiff.contMDiffOn (fun _ hz ↦ hz))
  have hts : ContMDiffOn I I ∞ t.toOpenPartialHomeomorph.symm t.target := by
    have h := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b |>.2
    have h' : ContMDiffOn J J ∞ t.toOpenPartialHomeomorph.symm t.target := by
      change ContMDiffOn ((𝓡 n).prod (𝓡 r)) J ∞
        t.toOpenPartialHomeomorph.symm t.target at h
      rw [hJI] at h
      exact h
    exact dZ.contMDiff.comp_contMDiffOn
      (h'.comp dP.symm.contMDiff.contMDiffOn (fun _ hz ↦ hz))
  let d : U ≃ₘ⟮I, I⟯ V := {
    toEquiv := t.toOpenPartialHomeomorph.toHomeomorphSourceTarget.toEquiv
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff V _).mp
      intro u
      exact ((ht u.val u.property).contMDiffAt (t.open_source.mem_nhds u.property)).comp u
        (contMDiff_subtype_val (n := ∞) u)
    contMDiff_invFun := by
      apply (ContMDiff.subtypeVal_comp_iff U _).mp
      intro v
      exact ((hts v.val v.property).contMDiffAt (t.open_target.mem_nhds v.property)).comp v
        (contMDiff_subtype_val (n := ∞) v) }
  have hV : IsSmoothPositiveMeasure (n := n + r)
      ((μ.prod ν).comap (Subtype.val : V → B × Y)) :=
    isSmoothPositiveMeasure_comap_opens (μ.prod ν) V
  let := hV
  have hlocal := IsSmoothPositiveMeasure.map_diffeomorph
    ((μ.prod ν).comap (Subtype.val : V → B × Y)) d.symm
  -- The previously proved chart identity identifies this transported measure with η's comap.
  have hchart := associatedProductMeasure_comap_trivialization S.toIsPrincipalBundle μ ν hν
    (S.trivialization b) t hbase
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.2
  let j (v : V) : Z := t.toOpenPartialHomeomorph.symm v.val
  have hchartV : η.comap j = (μ.prod ν).comap (Subtype.val : V → B × Y) := hchart
  have hj : Topology.IsOpenEmbedding j :=
    U.isOpen.isOpenEmbedding_subtypeVal.comp d.symm.toHomeomorph.isOpenEmbedding
  have hrange : Set.range j = (U : Set Z) := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      exact t.toOpenPartialHomeomorph.map_target v.property
    · intro hw
      exact ⟨d ⟨w, hw⟩, t.toOpenPartialHomeomorph.left_inv hw⟩
  have heq : Measure.map d.symm ((μ.prod ν).comap (Subtype.val : V → B × Y)) =
      η.comap (Subtype.val : U → Z) := by
    have hinc : MeasurableEmbedding (Subtype.val : U → Z) :=
      U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
    apply hinc.map_injective
    have hd : Measurable (d.symm : V → U) := d.symm.continuous.measurable
    calc
      Measure.map (Subtype.val : U → Z)
          (Measure.map d.symm ((μ.prod ν).comap (Subtype.val : V → B × Y))) =
          Measure.map j ((μ.prod ν).comap (Subtype.val : V → B × Y)) :=
        Measure.map_map measurable_subtype_coe hd
      _ = η.restrict U := by
        rw [← hchartV, hj.measurableEmbedding.map_comap, hrange]
      _ = Measure.map (Subtype.val : U → Z) (η.comap (Subtype.val : U → Z)) :=
        (map_comap_subtype_coe U.isOpen.measurableSet η).symm
  rw [heq] at hlocal
  exact hlocal

end AtiyahSinger
