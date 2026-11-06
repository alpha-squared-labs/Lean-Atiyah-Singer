/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialHorizontalTensor
public import AtiyahSinger.Geometry.AssociatedSphereTensorBundle

/-!
# Base slices in a principal chart

Public module ID: M0136.

The principal chart fixes the normalized representative above each base point.
An upstairs tensor section is pulled back by that representative while retaining
the entire sphere fiber. A scalar function of the base multiplies the family,
which is extended by zero outside the principal chart. The sphere coefficient
factor comes first in the resulting tensor family.

The coordinate formula is the corresponding tensor-atlas value multiplied
by the same base scalar.
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
/-- The actual normalized principal-chart base slice, with a cutoff only on the base. -/
def associatedSphereTensorCutoffBaseFamily
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ y : OrthogonalSphere r,
      (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections →ₗ[ℂ]
        ∀ x : B, F y ⊗[ℂ] E x := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let e := S.trivialization b
  let p (x : B) : P := e.toOpenPartialHomeomorph.symm (x, 1)
  let transport : ∀ {x z : B}, x = z → E x ≃ₗ[ℂ] E z := fun {x z} h ↦ by
    subst z
    exact LinearEquiv.refl ℂ (E x)
  -- The original inverse principal chart changes only the dependent base index.
  let c (x : B) (hx : x ∈ e.baseSet) : E (projection (p x)) ≃ₗ[ℂ] E x :=
    transport (e.proj_symm_apply' hx)
  exact fun y ↦ LinearMap.pi fun x ↦
    if hx : x ∈ e.baseSet then
      (χ x : ℂ) • ((TensorProduct.comm ℂ (E x) (F y)).toLinearMap.comp
        ((TensorProduct.map (c x hx).toLinearMap LinearMap.id).comp
          ((associatedSphereTensorFiberEquiv S E σ (p x) y).symm.toLinearMap.comp
            ((LinearMap.proj (associatedBundleMk G P (OrthogonalSphere r) (p x) y)).comp
              AT.smoothSections.subtype))))
    else 0

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in

/-- Original tensor coordinates of the normalized base slice retain exactly the base cutoff. -/
theorem associatedSphereTensorCutoffBaseFamily_coordinate
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (j : A.Index) (x : B) (hx : x ∈ (S.trivialization b).baseSet)
    (hxe : x ∈ e.baseSet) (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet)
    (i : Fin a) (k : Fin (A.rank j)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
    let z := associatedBundleMk G P (OrthogonalSphere r) p y
    let l := (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      (e ⟨x, TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id
          (associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ y w x))⟩).2 i =
        (χ x : ℂ) *
          ((associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).chart
            (⟨e, he⟩, (b, j)) ⟨z, w.val z⟩).2 (finProdFinEquiv (i, k)) := by
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
    let l := (LinearMap.proj k).comp (A.frameLinearEquiv j y hy).toLinearMap
    let transport : ∀ {x z : B}, x = z → E x ≃ₗ[ℂ] E z := fun {x z} h ↦ by
      subst z
      exact LinearEquiv.refl ℂ (E x)
    have hcoords (p : P) (x : B) (hpx : projection p = x)
        (hp : x ∈ principal.baseSet) (hg : (principal p).2 = 1)
        (hxe : x ∈ e.baseSet) (v : E (projection p) ⊗[ℂ] F y) :
        (e ⟨x, TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id
          (TensorProduct.comm ℂ (E x) (F y)
            (TensorProduct.map (transport hpx).toLinearMap LinearMap.id v)))⟩).2 i =
          (AT.chart (⟨e, he⟩, (b, j))
            ⟨associatedBundleMk G P (OrthogonalSphere r) p y,
              associatedSphereTensorFiberEquiv S E σ p y v⟩).2
                (finProdFinEquiv (i, k)) := by
      subst x
      let z := associatedBundleMk G P (OrthogonalSphere r) p y
      have hforward : t z = (projection p, y) := by
        have h : t z = (projection p, (principal p).2 • y) :=
          (exists_associatedBundleTrivialization S.toIsPrincipalBundle
            principal (S.equivariant b)).choose_spec.2.1 p y hp
        rw [hg, one_smul] at h
        exact h
      have hDbase : z ∈ (AD.chart (b, j)).baseSet := by
        have hb : t.baseSet = principal.baseSet :=
          (exists_associatedBundleTrivialization S.toIsPrincipalBundle
            principal (S.equivariant b)).choose_spec.1
        have hbase : (AD.chart (b, j)).baseSet =
            t.source ∩ t ⁻¹' (Set.univ ×ˢ (A.chart j).baseSet) :=
          (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
            principal (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
        rw [hbase]
        refine ⟨t.mem_source.mpr (hb.symm ▸ hp), ?_⟩
        rw [Set.mem_preimage, hforward]
        exact ⟨Set.mem_univ _, hy⟩
      have hTbase : z ∈ (AT.chart (⟨e, he⟩, (b, j))).baseSet := by
        have hEbase : z ∈ (AC.chart ⟨e, he⟩).baseSet :=
          (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.1.symm ▸ hxe
        exact (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
          (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.1.symm ▸ ⟨hEbase, hDbase⟩
      induction v using TensorProduct.inductionOn with
      | tmul u v =>
        change (e ⟨projection p, l v • u⟩).2 i = _
        have hE := congrArg (fun v : EuclideanSpace ℂ (Fin a) ↦ v i)
          ((e.linearEquivAt ℂ (projection p) hxe).map_smul (l v) u)
        change (e ⟨projection p, l v • u⟩).2 i = l v * (e ⟨projection p, u⟩).2 i at hE
        rw [hE]
        have h := associatedSphereTensorBundleAtlas_chart_tmul (a := a) S E A σ hσ
          e he b j p y hp hxe hDbase u v i k
        change (AT.chart (⟨e, he⟩, (b, j))
          ⟨z, associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] v)⟩).2 _ = _ at h
        rw [h]
        have hone : (A.chart j ⟨(principal p).2 • y,
            σ.linearMap (principal p).2 y v⟩).2 k = (A.chart j ⟨y, v⟩).2 k := by
          rw [hg]
          exact congrArg (fun v : TotalSpace Unit F ↦ (A.chart j v).2 k) (σ.one_map y v)
        rw [hone]
        change (A.chart j ⟨y, v⟩).2 k * (e ⟨projection p, u⟩).2 i = _
        exact mul_comm _ _
      | add u v hu hv =>
        have hE := congrArg (fun v : EuclideanSpace ℂ (Fin a) ↦ v i)
          ((e.linearEquivAt ℂ (projection p) hxe).map_add
            (TensorProduct.lid ℂ (E (projection p)) (TensorProduct.map l LinearMap.id
              (TensorProduct.comm ℂ (E (projection p)) (F y)
                (TensorProduct.map (transport rfl).toLinearMap LinearMap.id u))))
            (TensorProduct.lid ℂ (E (projection p)) (TensorProduct.map l LinearMap.id
              (TensorProduct.comm ℂ (E (projection p)) (F y)
                (TensorProduct.map (transport rfl).toLinearMap LinearMap.id v)))))
        change (e ⟨projection p, _ + _⟩).2 i =
          (e ⟨projection p, _⟩).2 i + (e ⟨projection p, _⟩).2 i at hE
        have hT := congrFun ((AT.linear (⟨e, he⟩, (b, j)) z hTbase).map_add
          (associatedSphereTensorFiberEquiv S E σ p y u)
          (associatedSphereTensorFiberEquiv S E σ p y v)) (finProdFinEquiv (i, k))
        change (AT.chart (⟨e, he⟩, (b, j)) ⟨z, _ + _⟩).2
            (finProdFinEquiv (i, k)) =
          (AT.chart (⟨e, he⟩, (b, j)) ⟨z, _⟩).2 (finProdFinEquiv (i, k)) +
            (AT.chart (⟨e, he⟩, (b, j)) ⟨z, _⟩).2 (finProdFinEquiv (i, k)) at hT
        simp only [map_add]
        rw [hE, hT]
        exact congrArg₂ (· + ·) hu hv
    dsimp only
    intro w
    let p := principal.toOpenPartialHomeomorph.symm (x, 1)
    have hpx : projection p = x := principal.proj_symm_apply' hx
    have hg : (principal p).2 = 1 := congrArg Prod.snd (principal.apply_symm_apply' hx)
    let v := (associatedSphereTensorFiberEquiv S E σ p y).symm
      (w.val (associatedBundleMk G P (OrthogonalSphere r) p y))
    have hc := hcoords p x hpx hx hg hxe v
    rw [LinearEquiv.apply_symm_apply] at hc
    have hvalue : associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ y w x =
        (χ x : ℂ) • TensorProduct.comm ℂ (E x) (F y)
          (TensorProduct.map (transport hpx).toLinearMap LinearMap.id v) := by
      simp only [associatedSphereTensorCutoffBaseFamily, LinearMap.pi_apply, dite_eq_left hx,
        LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
        Submodule.subtype_apply]
      rfl
    rw [hvalue, map_smul, map_smul]
    have hE := congrArg (fun v : EuclideanSpace ℂ (Fin a) ↦ v i)
      ((e.linearEquivAt ℂ x hxe).map_smul (χ x : ℂ)
        (TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id
          (TensorProduct.comm ℂ (E x) (F y)
            (TensorProduct.map (transport hpx).toLinearMap LinearMap.id v)))))
    change (e ⟨x, (χ x : ℂ) • _⟩).2 i = (χ x : ℂ) * (e ⟨x, _⟩).2 i at hE
    rw [hE, hc]

end AtiyahSinger
