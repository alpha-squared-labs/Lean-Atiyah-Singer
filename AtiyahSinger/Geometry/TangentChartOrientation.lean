/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.RealOrientationCycleNaturality

/-!
# Positive derivatives of the native tangent chart transitions

Public module ID: M1470.

In grouped tangent coordinates, the differential of an actual transition has
blocks A, zero, B, A, where A is the derivative of the same base transition.
Projection and restriction to a vertical fiber identify the two diagonal
blocks without choosing a connection or explicitly expanding a Hessian.
The existing smooth tangent atlas supplies the entire derivative. Its
invertibility follows from the reverse native chart, and its determinant is
the square of the nonzero base determinant.

This is the standard tangent-orientability argument used in Lawson--Michelsohn,
Spin Geometry, III.13, with the project's original tangent atlas retained.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open Bundle Manifold
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "IB" => 𝓘(ℝ, E)
local notation "IT" => 𝓘(ℝ, E × E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native tangent chart transitions have positive determinant, even over a reversing base chart. -/
theorem exists_pos_tangentChartTransition
    (p q z : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)
    (hp : z ∈ (chartAt (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) p).source)
    (hq : z ∈ (chartAt (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) q).source) :
    ∃ L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      HasFDerivAt (fun v ↦
        chartAt (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) q
          ((chartAt (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) p).symm v))
        L.toContinuousLinearMap
        (chartAt (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) p z) ∧
      0 < LinearMap.det L.toLinearMap := by
  classical
  have hp₀ : z.proj ∈ (chartAt E p.proj).source := (TangentBundle.mem_chart_source_iff z p).mp hp
  have hq₀ : z.proj ∈ (chartAt E q.proj).source := (TangentBundle.mem_chart_source_iff z q).mp hq
  -- The reverse native base transition is the inverse of this same base derivative.
  let A : E ≃L[ℝ] E :=
    { tangentCoordChange IB p.proj q.proj z.proj with
      invFun := tangentCoordChange IB q.proj p.proj z.proj
      left_inv := by
        intro v
        change tangentCoordChange IB q.proj p.proj z.proj
          (tangentCoordChange IB p.proj q.proj z.proj v) = v
        rw [tangentCoordChange_comp (I := IB) (by
          simpa only [mfld_simps] using And.intro (And.intro hp₀ hq₀) hp₀)]
        exact tangentCoordChange_self (by simpa only [mfld_simps] using hp₀)
      right_inv := by
        intro v
        change tangentCoordChange IB p.proj q.proj z.proj
          (tangentCoordChange IB q.proj p.proj z.proj v) = v
        rw [tangentCoordChange_comp (I := IB) (by
          simpa only [mfld_simps] using And.intro (And.intro hq₀ hp₀) hq₀)]
        exact tangentCoordChange_self (by simpa only [mfld_simps] using hq₀) }
  -- Apply the identical atlas derivative construction upstairs, before inspecting its blocks.
  let L : (E × E) ≃L[ℝ] (E × E) :=
    { tangentCoordChange IT p q z with
      invFun := tangentCoordChange IT q p z
      left_inv := by
        intro v
        change tangentCoordChange IT q p z (tangentCoordChange IT p q z v) = v
        rw [tangentCoordChange_comp (I := IT) (by
          simpa only [mfld_simps] using And.intro (And.intro hp hq) hp)]
        exact tangentCoordChange_self (by simpa only [mfld_simps] using hp)
      right_inv := by
        intro v
        change tangentCoordChange IT p q z (tangentCoordChange IT q p z v) = v
        rw [tangentCoordChange_comp (I := IT) (by
          simpa only [mfld_simps] using And.intro (And.intro hq hp) hq)]
        exact tangentCoordChange_self (by simpa only [mfld_simps] using hq) }
  let a := chartAt (E × E) p z
  let F : E × E → E × E := fun v ↦ chartAt (E × E) q ((chartAt (E × E) p).symm v)
  have hA : HasFDerivAt (fun v : E ↦ chartAt E q.proj ((chartAt E p.proj).symm v))
      A.toContinuousLinearMap (chartAt E p.proj z.proj) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := IB)
      (x := p.proj) (y := q.proj) (z := z.proj)
      (by simpa only [mfld_simps] using And.intro hp₀ hq₀)
    simp only [mfld_simps, hasFDerivWithinAt_univ] at h
    exact h
  have hL : HasFDerivAt F L.toContinuousLinearMap a := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := IT) (x := p) (y := q) (z := z)
      (by simpa only [mfld_simps] using And.intro hp hq)
    simp only [mfld_simps, hasFDerivWithinAt_univ] at h
    exact h
  -- Base projection gives the upper row A, zero; the same vertical slice gives the lower A.
  have hfirst (v : E × E) : (L v).1 = A v.1 := by
    have hAa : HasFDerivAt
        (fun v : E ↦ chartAt E q.proj ((chartAt E p.proj).symm v))
        A.toContinuousLinearMap a.1 := hA
    have hproj : HasFDerivAt (fun v : E × E ↦ v.1)
        (ContinuousLinearMap.fst ℝ E E) a := hasFDerivAt_fst
    have hd := hAa.comp a hproj
    have heq := hL.fst.unique hd
    exact congrArg (fun B : (E × E) →L[ℝ] E ↦ B v) heq
  have hslice (v : E) : F (a.1, v) = (chartAt E q.proj z.proj, A v) := by
    have hbase : (chartAt E p.proj).symm a.1 = z.proj :=
      (chartAt E p.proj).left_inv hp₀
    change (chartAt E q.proj ((chartAt E p.proj).symm a.1),
      tangentCoordChange IB ((chartAt E p.proj).symm a.1) q.proj
        ((chartAt E p.proj).symm a.1)
        (tangentCoordChange IB p.proj ((chartAt E p.proj).symm a.1)
          ((chartAt E p.proj).symm a.1) v)) = _
    rw [hbase, tangentCoordChange_comp (I := IB) (by
      simpa only [mfld_simps] using And.intro (And.intro hp₀ (mem_chart_source E z.proj)) hq₀)]
    rfl
  have hvertical (v : E) : (L (0, v)).2 = A v := by
    have hd := hL.comp a.2 ((hasFDerivAt_const a.1 a.2).prodMk (hasFDerivAt_id a.2))
    have heq : HasFDerivAt (fun v : E ↦ F (a.1, v))
        ((0 : E →L[ℝ] E).prod A.toContinuousLinearMap) a.2 := by
      simp only [hslice]
      have hlin : HasFDerivAt (fun v : E ↦ A v) A.toContinuousLinearMap a.2 :=
        A.toContinuousLinearMap.hasFDerivAt
      exact (hasFDerivAt_const (chartAt E q.proj z.proj) a.2).prodMk hlin
    exact congrArg (fun B : E →L[ℝ] (E × E) ↦ (B v).2) (hd.unique heq)
  -- The unspecified lower-left block does not affect the block-triangular determinant.
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let B : E →ₗ[ℝ] E := (LinearMap.snd ℝ E E).comp
    (L.toLinearMap.comp (LinearMap.inl ℝ E E))
  have hmatrix : LinearMap.toMatrix (b.prod b) (b.prod b) L.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix b b A.toLinearMap) 0
        (LinearMap.toMatrix b b B) (LinearMap.toMatrix b b A.toLinearMap) := by
    ext i j
    cases i <;> cases j <;>
      simp only [LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, Matrix.zero_apply]
    · change b.repr (L (b _, 0)).1 _ = b.repr (A (b _)) _
      rw [hfirst]
    · change b.repr (L (0, b _)).1 _ = 0
      rw [hfirst, map_zero, map_zero, Finsupp.zero_apply]
    · rfl
    · change b.repr (L (0, b _)).2 _ = b.repr (A (b _)) _
      rw [hvertical]
  have hdet : LinearMap.det L.toLinearMap = LinearMap.det A.toLinearMap *
      LinearMap.det A.toLinearMap := by
    rw [← LinearMap.det_toMatrix (b.prod b), hmatrix, Matrix.det_fromBlocks_zero₁₂,
      LinearMap.det_toMatrix]
  refine ⟨L, hL, ?_⟩
  rw [hdet]
  exact mul_self_pos.mpr (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

end AtiyahSinger
