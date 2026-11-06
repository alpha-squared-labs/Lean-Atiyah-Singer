/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSectionSmoothness
public import AtiyahSinger.Geometry.AssociatedSphereTensorBundle
public import AtiyahSinger.Geometry.SmoothTensorMap
public import AtiyahSinger.Geometry.SmoothTensorPullback

/-!
# Smooth tensor coefficients detected on the full associated sphere

Public module ID: M1084.

Evaluation of an injective finite family of original sphere sections,
tensored with the original base bundle, preserves and detects smoothness
in the specified tensor atlases. All sphere evaluations together separate
coefficients; no pointwise injectivity or new kernel bundle is assumed.

This is the smooth base-coefficient comparison in SG III.13.6. The proof
retains the supplied evaluation map, representation coordinates, quotient
projection and the common base-first upstairs tensor atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere

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
  (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 2000000 in
-- The comparison retains the original two tensor atlases and dependent quotient-fiber maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same full-fiber tensor evaluation preserves and detects smooth base coefficients. -/
theorem isSmoothSection_associatedTensorEvaluation_iff
    (s : V →ₗ[ℂ] A.smoothSections) (hs : Function.Injective s)
    (ev : Hom ((q : Z → B) *ᵖ C) D)
    (hev : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y))
    (u : ∀ b : B, E b ⊗[ℂ] C b) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).IsSmoothSection
        (fun z : Z ↦ TensorProduct.map LinearMap.id (ev.linearMap z) (u (q z))) ↔
      (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ)).IsSmoothSection u := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let lm := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph lm Z
  let := linearModelChartedSpace lm Z
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let AC := associatedOrthogonalRepresentationAtlas S ρ
  let TC := tensorSmoothAtlas AE AC
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  let EP := AE.pullback q hq
  let CP := AC.pullback q hq
  let t := associatedSphereTrivialization S
  have hCbase (i : B) : (AC.chart i).baseSet = (S.trivialization i).baseSet :=
    (associatedOrthogonalRepresentationChart_properties S ρ i).1
  have hTC (i : AE.Index × B) :=
    (exists_tensor_trivialization (AE.chart i.1) (AC.chart i.2)
      (AE.linear i.1) (AC.linear i.2)).choose_spec
  have htbase (i : B) : (t i).baseSet = (S.trivialization i).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization i) (S.equivariant i)).choose_spec.1
  -- The original full-fiber scalar evaluations separate the finite representation.
  let J := Σ y : OrthogonalSphere r, Σ j : {j : A.Index // y ∈ (A.chart j).baseSet},
    Fin (A.rank j.val)
  let L (z : J) : V →ₗ[ℂ] ℂ :=
    (LinearMap.proj z.2.2).comp
      ((A.frameLinearEquiv z.2.1.val z.1 z.2.1.property).toLinearMap.comp
        ((LinearMap.proj z.1).comp (A.smoothSections.subtype.comp s)))
  have hL (v : V) (hv : ∀ z : J, L z v = 0) : v = 0 := by
    apply hs
    rw [map_zero]
    apply Subtype.ext
    funext y
    obtain ⟨j, hj⟩ := A.covers y
    apply (A.frameLinearEquiv j y hj).injective
    change (A.frameLinearEquiv j y hj) ((s v).val y) =
      (A.frameLinearEquiv j y hj) (0 : F y)
    rw [map_zero]
    funext k
    exact hv ⟨y, ⟨j, hj⟩, k⟩
  constructor
  · intro hu ij
    change AE.Index × B at ij
    rcases ij with ⟨ec, i⟩
    let row (l : Fin a) : (Fin (a * ρ.dimension) → ℂ) →ₗ[ℂ] V :=
      LinearMap.pi fun k ↦ LinearMap.proj (finProdFinEquiv (l, k))
    let LT (z : Fin a × J) := (L z.2).comp (row z.1)
    have hLT (v : Fin (a * ρ.dimension) → ℂ) (hv : ∀ z, LT z v = 0) : v = 0 := by
      funext k
      obtain ⟨⟨l, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      exact congrFun (hL (row l v) (fun z ↦ hv (l, z))) j
    let c (b : B) : Fin (a * ρ.dimension) → ℂ := (TC.chart (ec, i) ⟨b, u b⟩).2
    apply contMDiffOn_of_separating_linearForms (𝓡 n) LT hLT c
    rintro ⟨l, y, ⟨j, hj⟩, k⟩
    let z (b : B) : Z := (t i).toPartialEquiv.symm (b, y)
    have hbS (b : B) (hb : b ∈ (TC.chart (ec, i)).baseSet) :
        b ∈ (S.trivialization i).baseSet := hCbase i ▸ ((hTC (ec, i)).1 ▸ hb).2
    have hqz (b : B) (hb : b ∈ (TC.chart (ec, i)).baseSet) : q (z b) = b :=
      (t i).proj_symm_apply' ((htbase i).symm ▸ hbS b hb)
    have hzSmooth : ContMDiffOn (𝓡 n) (𝓡 (n + r)) ∞ z
        (TC.chart (ec, i)).baseSet := by
      have htinv := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 i |>.2
      exact d.contMDiff.comp_contMDiffOn (htinv.comp
        (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun b hb ↦
          (t i).mem_target.mpr ((htbase i).symm ▸ hbS b hb)))
    have hzb (b : B) (hb : b ∈ (TC.chart (ec, i)).baseSet) :
        z b ∈ (AT.chart (ec, (i, j))).baseSet := by
      have hbT : b ∈ (t i).baseSet := (htbase i).symm ▸ hbS b hb
      have hDb : z b ∈ (AD.chart (i, j)).baseSet := by
        have hbase : (AD.chart (i, j)).baseSet =
            (t i).source ∩ (t i) ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
          (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
            (S.trivialization i) (S.equivariant i) (A.chart j) (A.linear j)).choose_spec.1
        rw [hbase]
        refine ⟨(t i).map_target ((t i).mem_target.mpr hbT), ?_⟩
        change (t i ((t i).toPartialEquiv.symm (b, y))) ∈
          Set.univ ×ˢ (A.chart j).baseSet
        erw [(t i).apply_symm_apply' (x := y) hbT]
        exact ⟨Set.mem_univ _, hj⟩
      have hEb : z b ∈ (EP.chart ec).baseSet := by
        have hmem : z b ∈ q ⁻¹' (AE.chart ec).baseSet := by
          change q (z b) ∈ (AE.chart ec).baseSet
          rw [hqz b hb]
          exact ((hTC (ec, i)).1 ▸ hb).1
        exact (AE.exists_pullbackChart q ec).choose_spec.1.symm ▸ hmem
      exact (exists_tensor_trivialization (EP.chart ec) (AD.chart (i, j))
        (EP.linear ec) (AD.linear (i, j))).choose_spec.1.symm ▸ ⟨hEb, hDb⟩
    have hformula (p : P) (hp : projection p ∈ (S.trivialization i).baseSet)
        (hg : (S.trivialization i p).2 = 1) (hpe : projection p ∈ (AE.chart ec).baseSet)
        (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z (projection p))
        (hzAT : z (projection p) ∈ (AT.chart (ec, (i, j))).baseSet)
        (v : E (projection p) ⊗[ℂ] C (projection p)) :
        (AT.chart (ec, (i, j)) ⟨associatedBundleMk G P (OrthogonalSphere r) p y,
          TensorProduct.map LinearMap.id
            (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)) v⟩).2
              (finProdFinEquiv (l, k)) =
          L ⟨y, ⟨j, hj⟩, k⟩ (row l (TC.chart (ec, i) ⟨projection p, v⟩).2) := by
      have hpc : projection p ∈ (AC.chart i).baseSet := (hCbase i).symm ▸ hp
      have hpTC : projection p ∈ (TC.chart (ec, i)).baseSet :=
        (hTC (ec, i)).1.symm ▸ ⟨hpe, hpc⟩
      have hpAT : associatedBundleMk G P (OrthogonalSphere r) p y ∈
          (AT.chart (ec, (i, j))).baseSet := hz.symm ▸ hzAT
      have hpAD : associatedBundleMk G P (OrthogonalSphere r) p y ∈
          (AD.chart (i, j)).baseSet :=
        ((exists_tensor_trivialization (EP.chart ec) (AD.chart (i, j))
          (EP.linear ec) (AD.linear (i, j))).choose_spec.1 ▸ hpAT).2
      induction v using TensorProduct.inductionOn with
      | tmul v w =>
        obtain ⟨w₀, rfl⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
          ρ.representation p rfl).2 w
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hev]
        have htarget := associatedSphereTensorBundleAtlas_chart_tmul (a := a)
          S E A σ hσ ec.val ec.property i j p y hp hpe hpAD v ((s w₀).val y) l k
        have hsource : row l (TC.chart (ec, i) ⟨projection p,
            v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle
              ρ.representation p rfl w₀⟩).2 = (ec.val ⟨projection p, v⟩).2 l • w₀ := by
          funext j'
          have h := (hTC (ec, i)).2.2 (projection p) ⟨hpe, hpc⟩ v
            (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl w₀) l j'
          have hc := (associatedOrthogonalRepresentationChart_properties S ρ i).2
            p (projection p) rfl w₀ hp
          rw [hg] at hc
          simp only [map_one] at hc
          change _ = (ec.val ⟨projection p, v⟩).2 l * w₀ j'
          exact h.trans (congrArg ((AE.chart ec ⟨projection p, v⟩).2 l * ·) (congrFun hc j'))
        rw [hsource, map_smul]
        have hone := congrArg (fun v : TotalSpace Unit F ↦ (A.chart j v).2 k)
          (σ.one_map y ((s w₀).val y))
        rw [hg] at htarget
        exact htarget.trans (congrArg ((ec.val ⟨projection p, v⟩).2 l * ·) hone)
      | add v w hv hw =>
        have ht := congrFun ((AT.linear (ec, (i, j)) _ hpAT).map_add
          (TensorProduct.map LinearMap.id (ev.linearMap _) v)
          (TensorProduct.map LinearMap.id (ev.linearMap _) w)) (finProdFinEquiv (l, k))
        have hc := (TC.linear (ec, i) _ hpTC).map_add v w
        simp only [map_add]
        rw [ht, hc, map_add, map_add]
        exact congrArg₂ (· + ·) hv hw
    have hlocal := contMDiffOn_pi_space.mp
      ((hu (ec, (i, j))).comp hzSmooth hzb) (finProdFinEquiv (l, k))
    apply hlocal.congr
    intro b hb
    let p := (S.trivialization i).toPartialEquiv.symm (b, 1)
    have hp : projection p = b := (S.trivialization i).proj_symm_apply' (hbS b hb)
    have hg : (S.trivialization i p).2 = 1 :=
      congrArg Prod.snd ((S.trivialization i).apply_symm_apply' (hbS b hb))
    have hz : z b = associatedBundleMk G P (OrthogonalSphere r) p y :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization i) (S.equivariant i)).choose_spec.2.2 b y (hbS b hb)
    have h := hformula p (hp.symm ▸ hbS b hb) hg
      (hp.symm ▸ ((hTC (ec, i)).1 ▸ hb).1)
      (hz.symm.trans (congrArg z hp.symm)) (hp.symm ▸ hzb b hb) (u (projection p))
    have h' : (AT.chart (ec, (i, j)) ⟨z b,
          TensorProduct.map LinearMap.id (ev.linearMap (z b)) (u (q (z b)))⟩).2
            (finProdFinEquiv (l, k)) = L ⟨y, ⟨j, hj⟩, k⟩ (row l (c b)) := by
      rw [hz]
      change _ = L ⟨y, ⟨j, hj⟩, k⟩ (row l (TC.chart (ec, i) ⟨b, u b⟩).2)
      rw [← hp]
      exact h
    exact h'.symm
  · intro hu
    -- Pull back the same tensor coefficient section, then apply id tensor the specified Hom.
    have hup := isSmoothSection_tensor_pullback AE AC q hq u hu
    have hId : IsSmoothAtlasBundleMap EP EP (fun _ ↦ LinearMap.id) := by
      refine ⟨contMDiff_id, ?_⟩
      intro i j k
      apply (EP.contMDiffOn_coordChange i j k).congr
      intro z hz
      rw [dite_eq_left hz.1]
      exact congrArg (fun v : TotalSpace Unit ((q : Z → B) *ᵖ E) ↦ (EP.chart j v).2)
        (TotalSpace.mk_cast (F := Unit) (E := (q : Z → B) *ᵖ E)
          ((EP.chart i).proj_symm_apply' (x := Pi.single k 1) hz.1) _)
    have hEv := isSmoothAtlasBundleMap_associatedSectionEvaluation S A σ hσ ρ s ev hev
    have hTensor : IsSmoothAtlasBundleMap (tensorSmoothAtlas EP CP) AT
        (fun z ↦ TensorProduct.map LinearMap.id (ev.linearMap z)) := hId.tensor hEv
    exact hTensor.map_section (tensorSmoothAtlas EP CP) AT
      (fun z ↦ TensorProduct.map LinearMap.id (ev.linearMap z)) ⟨_, hup⟩

end AtiyahSinger
