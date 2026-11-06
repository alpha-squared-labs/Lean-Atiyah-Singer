/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseExtension
public import AtiyahSinger.Geometry.AtlasLocalSectionSmoothness

/-!
# Smooth return of a supported whole-fiber family

Public module ID: M0134.

A family smooth in the sphere and native base frames returns to a smooth
section in the associated tensor atlas. A closed base support inside the
specified principal chart handles its boundary. Local frame detection
checks the entire tensor atlas while retaining the full sphere parameter.
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

open scoped Classical in
set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A supported jointly smooth family returns smoothly in the same original tensor atlas. -/
theorem isSmoothSection_associatedSphereTensorBaseExtension
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (K : Set B) (hK : IsClosed K) (hKb : K ⊆ (S.trivialization b).baseSet)
    (u : ∀ y : OrthogonalSphere r, ∀ x : B, F y ⊗[ℂ] E x)
    (hsupport : ∀ y x, x ∉ K → u y x = 0)
    (hu : ∀ (j : A.Index) (k : Fin (A.rank j))
      (e : Trivialization (EuclideanSpace ℂ (Fin a))
        (π (EuclideanSpace ℂ (Fin a)) E)), MemTrivializationAtlas e →
      ContMDiffOn ((𝓡 r).prod (𝓡 n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin a)) ∞
        (fun z : OrthogonalSphere r × B ↦ if hy : z.1 ∈ (A.chart j).baseSet then
          (e ⟨z.2, TensorProduct.lid ℂ (E z.2)
            (TensorProduct.map ((LinearMap.proj k).comp
              (A.frameLinearEquiv j z.1 hy).toLinearMap) LinearMap.id (u z.1 z.2))⟩).2
          else 0) ((A.chart j).baseSet ×ˢ e.baseSet)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).IsSmoothSection
      (associatedSphereTensorBaseExtension S E σ b u) := by
  as_aux_lemma =>
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
    let principal := S.trivialization b
    let t := associatedSphereTrivialization S b
    let f := associatedSphereTensorBaseExtension S E σ b u
    have hbase : t.baseSet = principal.baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        principal (S.equivariant b)).choose_spec.1
    have hzero (z : Z) (hzK : q z ∉ K) : f z = 0 := by
      by_cases hz : z ∈ t.source
      · have hzS : z ∈ (associatedSphereTrivialization S b).source := hz
        simp only [f, associatedSphereTensorBaseExtension, LinearMap.pi_apply,
          dite_eq_left hzS, LinearMap.comp_apply, LinearMap.proj_apply]
        rw [hsupport (t z).2 (q z) hzK]
        simp only [map_zero]
      · have hzS : z ∉ (associatedSphereTrivialization S b).source := hz
        simp only [f, associatedSphereTensorBaseExtension, LinearMap.pi_apply,
          dite_eq_right hzS, LinearMap.zero_apply]
    apply AT.isSmoothSection_of_locally f
    intro z
    by_cases hzK : q z ∈ K
    · have hz : z ∈ t.source := t.mem_source.mpr (hbase.symm ▸ hKb hzK)
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
      -- The original principal coordinates give the original sphere and base parameters.
      have ht : ContMDiffAt (𝓡 (n + r)) ((𝓡 n).prod (𝓡 r)) ∞ t z := by
        have hts := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b |>.1
        have h := hts.comp d.symm.contMDiff.contMDiffOn (fun z hz ↦ hz)
        exact h.contMDiffAt (t.open_source.mem_nhds hz)
      have hparam : ContMDiffAt (𝓡 (n + r)) ((𝓡 r).prod (𝓡 n)) ∞
          (fun z' : Z ↦ ((t z').2, q z')) z := ht.snd.prodMk hq.contMDiffAt
      have hmem : ((t z).2, q z) ∈ (A.chart j).baseSet ×ˢ e.baseSet := ⟨hy, hxe⟩
      have hopen : IsOpen ((A.chart j).baseSet ×ˢ e.baseSet) :=
        (A.chart j).open_baseSet.prod e.open_baseSet
      apply contMDiffAt_pi_space.mpr
      intro ik
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ik
      have hvec := ((hu j k e he).contMDiffAt (hopen.mem_nhds hmem)).comp z hparam
      let ec := EuclideanSpace.equiv (Fin a) ℂ
      have hmodel := (ec.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
      have hscalar := contMDiffAt_pi_space.mp (hmodel.contMDiffAt.comp z hvec) i
      apply hscalar.congr_of_eventuallyEq
      filter_upwards [t.open_source.mem_nhds hz,
        hparam.continuousAt (hopen.mem_nhds hmem)] with z' hzs hparams
      dsimp only [Function.comp_apply]
      rw [dite_eq_left hparams.1]
      exact associatedSphereTensorBaseExtension_coordinate (a := a) S E A σ hσ b e he j
        z' hzs hparams.2 hparams.1 i k u
    · obtain ⟨j, hj⟩ := AT.covers z
      refine ⟨j, hj, ?_⟩
      -- The whole family vanishes near the principal-chart boundary, by closed base support.
      apply (contMDiffAt_const (c := (0 : Fin (AT.rank j) → ℂ))).congr_of_eventuallyEq
      filter_upwards [hq.continuous.continuousAt (hK.isOpen_compl.mem_nhds hzK),
        (AT.chart j).open_baseSet.mem_nhds hj] with z' hz' hj'
      rw [hzero z' hz']
      exact (AT.linear j z' hj').map_zero

end AtiyahSinger
