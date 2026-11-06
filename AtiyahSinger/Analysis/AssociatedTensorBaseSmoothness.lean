/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseRestriction

/-!
# Smooth base families in the principal atlas

Public module ID: M0138.

A supported base cutoff extends normalized principal-chart slices smoothly
across the chart boundary. Each specified sphere-frame contraction varies
smoothly jointly in the sphere chart and the base frame. The construction
retains the full sphere family in the supplied tensor atlas.
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
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original sphere-frame contractions of the base slice are jointly smooth. -/
theorem contMDiffOn_associatedSphereTensorCutoffBaseFamily
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (j : A.Index) (k : Fin (A.rank j)) (l : ∀ y, F y →ₗ[ℂ] ℂ)
    (hl : ∀ (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet),
      l y = (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      ContMDiffOn ((𝓡 r).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin a)) ∞
        (fun z : OrthogonalSphere r × B ↦ (e ⟨z.2, TensorProduct.lid ℂ (E z.2)
          (TensorProduct.map (l z.1) LinearMap.id
            (associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ z.1 w z.2))⟩).2)
        ((A.chart j).baseSet ×ˢ e.baseSet) := by
  as_aux_lemma =>
    classical
    let := he
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
    let principal := S.trivialization b
    let t := associatedSphereTrivialization S b
    let p (x : B) := principal.toOpenPartialHomeomorph.symm (x, 1)
    let f (z : OrthogonalSphere r × B) :=
      associatedBundleMk G P (OrthogonalSphere r) (p z.2) z.1
    let U := (A.chart j).baseSet ×ˢ (principal.baseSet ∩ e.baseSet)
    have hU : IsOpen U := (A.chart j).open_baseSet.prod
      (principal.open_baseSet.inter e.open_baseSet)
    have htbase : t.baseSet = principal.baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.1
    -- The normalized quotient representatives are the actual smooth inverse chart.
    have hf : ContMDiffOn ((𝓡 r).prod (𝓡 n)) (𝓡 (n + r)) ∞ f U := by
      have hinv := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b |>.2
      have hswap : ContMDiffOn ((𝓡 r).prod (𝓡 n)) ((𝓡 n).prod (𝓡 r)) ∞
          (fun z : OrthogonalSphere r × B ↦ (z.2, z.1)) U :=
        contMDiffOn_snd.prodMk contMDiffOn_fst
      have hmem (z : OrthogonalSphere r × B) (hz : z ∈ U) : (z.2, z.1) ∈ t.target :=
        t.mem_target.mpr (htbase.symm ▸ hz.2.1)
      apply (d.contMDiff.comp_contMDiffOn (hinv.comp hswap hmem)).congr
      intro z hz
      exact ((exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.2.2 z.2 z.1 hz.2.1).symm
    have hbase (z : OrthogonalSphere r × B) (hz : z ∈ U) :
        f z ∈ (AT.chart (⟨e, he⟩, (b, j))).baseSet := by
      have hpx : projection (p z.2) = z.2 := principal.proj_symm_apply' hz.2.1
      have hqz : q (f z) = z.2 := hpx
      have hg : (principal (p z.2)).2 = 1 :=
        congrArg Prod.snd (principal.apply_symm_apply' hz.2.1)
      have hforward : t (f z) = (z.2, z.1) := by
        have hp : projection (p z.2) ∈ principal.baseSet := hpx.symm ▸ hz.2.1
        have h : t (f z) = (projection (p z.2), (principal (p z.2)).2 • z.1) :=
          (exists_associatedBundleTrivialization S.toIsPrincipalBundle
            principal (S.equivariant b)).choose_spec.2.1 (p z.2) z.1 hp
        rw [hpx, hg, one_smul] at h
        exact h
      have hDb : f z ∈ (AD.chart (b, j)).baseSet := by
        have hADbase : (AD.chart (b, j)).baseSet =
            t.source ∩ t ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
          (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
            principal (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
        rw [hADbase]
        refine ⟨t.mem_source.mpr (htbase.symm ▸ (hqz.symm ▸ hz.2.1)), ?_⟩
        rw [Set.mem_preimage, hforward]
        exact ⟨Set.mem_univ _, hz.1⟩
      have hEb : f z ∈ (AC.chart ⟨e, he⟩).baseSet := by
        have hEbase : (AC.chart ⟨e, he⟩).baseSet = q ⁻¹' e.baseSet :=
          (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.1
        have hmem : f z ∈ q ⁻¹' e.baseSet := by
          change q (f z) ∈ e.baseSet
          exact hqz.symm ▸ hz.2.2
        exact hEbase.symm ▸ hmem
      exact (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
        (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.1.symm ▸ ⟨hEb, hDb⟩
    intro w
    let s (z : OrthogonalSphere r × B) : EuclideanSpace ℂ (Fin a) :=
      (e ⟨z.2, TensorProduct.lid ℂ (E z.2) (TensorProduct.map (l z.1) LinearMap.id
        (associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ z.1 w z.2))⟩).2
    have hlocal (i : Fin a) : ContMDiffOn ((𝓡 r).prod (𝓡 n)) 𝓘(ℝ, ℂ) ∞
        (fun z ↦ s z i) U := by
      have hw := contMDiffOn_pi_space.mp
        ((w.property (⟨e, he⟩, (b, j))).comp hf hbase) (finProdFinEquiv (i, k))
      have hc : ContMDiffOn ((𝓡 r).prod (𝓡 n)) 𝓘(ℝ, ℂ) ∞
          (fun z : OrthogonalSphere r × B ↦ (χ z.2 : ℂ)) U :=
        (Complex.ofRealCLM.contDiff.comp_contMDiff hχ).comp_contMDiffOn contMDiffOn_snd
      apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
        (hc.prodMk_space hw)).congr
      intro z hz
      have h := associatedSphereTensorCutoffBaseFamily_coordinate (a := a) S E A σ hσ
        b χ e he j z.2 hz.2.1 hz.2.2 z.1 hz.1 i k w
      change s z i = _
      dsimp only [s]
      rw [hl z.1 hz.1]
      exact h
    -- Outside the closed base support the unchanged family is locally zero.
    have hcoord (i : Fin a) : ContMDiffOn ((𝓡 r).prod (𝓡 n)) 𝓘(ℝ, ℂ) ∞
        (fun z ↦ s z i) ((A.chart j).baseSet ×ˢ e.baseSet) := by
      intro z hz
      by_cases hχz : z.2 ∈ tsupport χ
      · exact ((hlocal i).contMDiffAt (hU.mem_nhds
          ⟨hz.1, hχsupport hχz, hz.2⟩)).contMDiffWithinAt
      · have hzero : ∀ᶠ z' : OrthogonalSphere r × B in nhds z, s z' i = 0 := by
          filter_upwards [continuous_snd.continuousAt
            ((isClosed_tsupport χ).isOpen_compl.mem_nhds hχz),
            continuous_snd.continuousAt (e.open_baseSet.mem_nhds hz.2)] with z' hz' hze
          have hχzero : χ z'.2 = 0 := image_eq_zero_of_notMem_tsupport hz'
          have hraw : associatedSphereTensorCutoffBaseFamily (a := a)
              S E A σ hσ b χ z'.1 w z'.2 = 0 := by
            simp [associatedSphereTensorCutoffBaseFamily, hχzero]
          change (e ⟨z'.2, _⟩).2 i = 0
          rw [hraw, map_zero, map_zero]
          exact congrArg (fun v : EuclideanSpace ℂ (Fin a) ↦ v i)
            ((e.linearEquivAt ℂ z'.2 hze).map_zero)
        exact (contMDiffAt_const.congr_of_eventuallyEq hzero).contMDiffWithinAt
    -- The fixed native model equivalence assembles all scalar coordinates.
    let ec := EuclideanSpace.equiv (Fin a) ℂ
    have hmodel := (ec.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
    exact (hmodel.comp_contMDiffOn (contMDiffOn_pi_space.mpr hcoord)).congr (fun _ _ ↦ rfl)

end AtiyahSinger
