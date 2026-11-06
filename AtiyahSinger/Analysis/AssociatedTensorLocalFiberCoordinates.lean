/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorFiberRestriction

/-!
# Original local base coordinates of whole fiber sections

Public module ID: M0178.

Contract a whole tensor fiber section against one original base-frame
coordinate at the normalized principal representative. This gives an actual
sphere section, retaining the full sphere. Its sphere coordinates are
exactly the original associated tensor coordinates in that principal chart.
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
/-- Original base-frame coordinates of a whole sphere family in a principal chart. -/
def associatedSphereTensorLocalFiberCoordinates (b : B)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e) (i : Fin a)
    (u : ∀ p : P, dualTensorSections (E (projection p)) A.smoothSections) :
    B → A.smoothSections := by
  classical
  let := he
  let principal := S.trivialization b
  let p (x : B) := principal.toOpenPartialHomeomorph.symm (x, 1)
  exact fun x ↦ if hx : x ∈ principal.baseSet ∩ e.baseSet then
    let φ : E (projection (p x)) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
      ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
        ((e.linearEquivAt ℂ x hx.2).toLinearMap.comp
          (LinearEquiv.cast (R := ℂ) (M := E)
            (principal.proj_symm_apply' hx.1)).toLinearMap))
    ⟨fun y ↦ TensorProduct.lid ℂ (F y)
      (TensorProduct.map φ LinearMap.id ((u (p x)).val y)), (u (p x)).property φ⟩
    else 0

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Local whole-fiber contractions are exactly the original associated tensor coordinates. -/
theorem associatedSphereTensorLocalFiberCoordinates_chart
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (i : Fin a) (u : ∀ p : P, dualTensorSections (E (projection p)) A.smoothSections)
    (j : A.Index) (x : B) (hx : x ∈ (S.trivialization b).baseSet)
    (hxe : x ∈ e.baseSet) (y : OrthogonalSphere r) (hy : y ∈ (A.chart j).baseSet)
    (k : Fin (A.rank j)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
    (A.chart j ⟨y, (associatedSphereTensorLocalFiberCoordinates S E A b e he i u x).val y⟩).2 k =
      ((associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).chart
        (⟨e, he⟩, (b, j)) ⟨associatedBundleMk G P (OrthogonalSphere r) p y,
          associatedSphereTensorFiberEquiv S E σ p y ((u p).val y)⟩).2
            (finProdFinEquiv (i, k)) := by
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
  have hcoords (p : P) (x : B) (hpx : projection p = x)
      (hp : x ∈ principal.baseSet) (hg : (principal p).2 = 1)
      (hxe : x ∈ e.baseSet) (v : E (projection p) ⊗[ℂ] F y) :
      let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
        ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
          ((e.linearEquivAt ℂ x hxe).toLinearMap.comp
            (LinearEquiv.cast (R := ℂ) (M := E) hpx).toLinearMap))
      (A.chart j ⟨y, TensorProduct.lid ℂ (F y) (TensorProduct.map φ LinearMap.id v)⟩).2 k =
        (AT.chart (⟨e, he⟩, (b, j))
          ⟨associatedBundleMk G P (OrthogonalSphere r) p y,
            associatedSphereTensorFiberEquiv S E σ p y v⟩).2
              (finProdFinEquiv (i, k)) := by
    subst x
    dsimp only
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
    let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
      ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
        (e.linearEquivAt ℂ (projection p) hxe).toLinearMap)
    change (A.chart j ⟨y, TensorProduct.lid ℂ (F y)
      (TensorProduct.map φ LinearMap.id v)⟩).2 k = _
    induction v using TensorProduct.inductionOn with
    | tmul v w =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
      have hA := congrFun ((A.linear j y hy).map_smul (φ v) w) k
      change (A.chart j ⟨y, φ v • w⟩).2 k =
        φ v * (A.chart j ⟨y, w⟩).2 k at hA
      rw [hA]
      have h := associatedSphereTensorBundleAtlas_chart_tmul (a := a) S E A σ hσ
        e he b j p y hp hxe hDbase v w i k
      change (AT.chart (⟨e, he⟩, (b, j))
        ⟨z, associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] w)⟩).2 _ = _ at h
      rw [h]
      have hone : (A.chart j ⟨(principal p).2 • y,
          σ.linearMap (principal p).2 y w⟩).2 k = (A.chart j ⟨y, w⟩).2 k := by
        rw [hg]
        exact congrArg (fun v : TotalSpace Unit F ↦ (A.chart j v).2 k) (σ.one_map y w)
      rw [hone]
      rfl
    | add v w hv hw =>
      have hA := congrFun ((A.linear j y hy).map_add
        (TensorProduct.lid ℂ (F y) (TensorProduct.map φ LinearMap.id v))
        (TensorProduct.lid ℂ (F y) (TensorProduct.map φ LinearMap.id w))) k
      have hT := congrFun ((AT.linear (⟨e, he⟩, (b, j)) z hTbase).map_add
        (associatedSphereTensorFiberEquiv S E σ p y v)
        (associatedSphereTensorFiberEquiv S E σ p y w)) (finProdFinEquiv (i, k))
      simp only [map_add]
      rw [hA, hT]
      exact congrArg₂ (· + ·) hv hw
  dsimp only
  let p := principal.toOpenPartialHomeomorph.symm (x, 1)
  have hpx : projection p = x := principal.proj_symm_apply' hx
  have hg : (principal p).2 = 1 := congrArg Prod.snd (principal.apply_symm_apply' hx)
  have h := hcoords p x hpx hx hg hxe ((u p).val y)
  have hx' : x ∈ (S.trivialization b).baseSet ∩ e.baseSet := ⟨hx, hxe⟩
  simpa only [associatedSphereTensorLocalFiberCoordinates, dite_eq_left hx'] using h

end AtiyahSinger
