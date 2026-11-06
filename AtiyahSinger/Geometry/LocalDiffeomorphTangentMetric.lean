/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DiffeomorphTangentMetric
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Pullback tangent metrics along local diffeomorphisms

Public module ID: M1295.

The same derivative pullback used for a global diffeomorphism also works
for a local diffeomorphism. Its fiber inverse controls the metric ball;
only the forward derivative enters smoothness. This supplies compatible
metrics on open neighborhoods in the embedding index comparison.

This extends `SmoothTangentMetric.comapDiffeomorph` to the required open
maps while retaining the original tangent fibers and bundle topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped Manifold ContDiff

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

/-- Pull back the metric by the actual invertible differential of a local diffeomorphism. -/
def SmoothTangentMetric.comapLocalDiffeomorph
    (h : SmoothTangentMetric (n := m) (M := N))
    (e : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M N ∞)
    (he : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ e) :
    SmoothTangentMetric (n := n) (M := M) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let (x : M) : IsNormableSpace ℝ (TangentSpace I x) :=
    (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I : M → Type _) x).isNormableSpace
  let (y : N) : IsNormableSpace ℝ (TangentSpace J y) :=
    (VectorBundle.continuousLinearEquivAt ℝ F (TangentSpace J : N → Type _) y).isNormableSpace
  let L (x : M) := mfderiv I J e x
  let d (x : M) := he.mfderivToContinuousLinearEquiv (by simp) x
  let R (x : M) := (d x).symm.toContinuousLinearMap
  have hRL (x : M) : (R x).comp (L x) = ContinuousLinearMap.id ℝ _ := by
    have hD : (d x).toContinuousLinearMap = L x :=
      he.mfderivToContinuousLinearEquiv_coe (by simp) x
    rw [← hD]
    apply ContinuousLinearMap.ext
    intro v
    exact (d x).symm_apply_apply v
  let q (x : M) := (h.inner (e x)).bilinearComp (L x) (L x)
  refine { inner := q
           symm := fun x v w ↦ h.symm (e x) (L x v) (L x w)
           pos := ?_
           isVonNBounded := ?_
           contMDiff := ?_ }
  · intro x v hv
    apply h.pos (e x) (L x v)
    intro hz
    have hi := DFunLike.congr_fun (hRL x) v
    change R x (L x v) = v at hi
    rw [hz, map_zero] at hi
    exact hv hi.symm
  · intro x
    -- The original inverse differential carries the target metric ball onto the pullback ball.
    apply ((h.isVonNBounded (e x)).image (R x)).subset
    intro v hv
    refine ⟨L x v, hv, ?_⟩
    exact DFunLike.congr_fun (hRL x) v
  · intro x
    -- In the same native frames the metric matrix is pulled back by the derivative matrix.
    let a := trivializationAt E (TangentSpace I : M → Type _) x
    let b := trivializationAt F (TangentSpace J : N → Type _) (e x)
    let s := trivializationAt ℝ (Bundle.Trivial M ℝ) x
    let t := trivializationAt ℝ (Bundle.Trivial N ℝ) (e x)
    let aDual := a.continuousLinearMap (RingHom.id ℝ) s
    let bDual := b.continuousLinearMap (RingHom.id ℝ) t
    let D (y : M) : E →L[ℝ] F :=
      (b.continuousLinearMapAt ℝ (e y)).comp ((L y).comp (a.symmL ℝ y))
    let H (y : M) : F →L[ℝ] F →L[ℝ] ℝ :=
      (bDual.continuousLinearMapAt ℝ (e y)).comp
        ((h.inner (e y)).comp (b.symmL ℝ (e y)))
    have hD : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ D x :=
      (e.contMDiff.contMDiffAt (x := x)).mfderiv_const (m := ∞) (by simp)
    have hH : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ H x := by
      have hc := (contMDiffAt_hom_bundle (fun y : N ↦ TotalSpace.mk'
        (F →L[ℝ] F →L[ℝ] ℝ) y (h.inner y)) (x₀ := e x)).mp (h.contMDiff (e x)) |>.2
      exact hc.comp x e.contMDiff.contMDiffAt
    have hHD := (hD.clm_precomp (F₃ := ℝ)).clm_comp (hH.clm_comp hD)
    apply (contMDiffAt_hom_bundle (fun y : M ↦ TotalSpace.mk'
      (E →L[ℝ] E →L[ℝ] ℝ) y (q y))).mpr
    refine ⟨contMDiffAt_id, hHD.congr_of_eventuallyEq ?_⟩
    filter_upwards [a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x),
      e.contMDiff.continuous.continuousAt.preimage_mem_nhds
        (b.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ (e x)))] with y ha hb
    ext u v
    change ((aDual.continuousLinearMapAt ℝ y) (q y (a.symmL ℝ y u))) v =
      ((bDual.continuousLinearMapAt ℝ (e y))
        (h.inner (e y) (b.symmL ℝ (e y) (D y u)))) (D y v)
    rw [aDual.continuousLinearMapAt_apply_of_mem ℝ ⟨ha, by simp [s]⟩,
      bDual.continuousLinearMapAt_apply_of_mem ℝ ⟨hb, by simp [t]⟩]
    simp only [aDual, bDual, Trivialization.continuousLinearMap_apply,
      ContinuousLinearMap.comp_apply]
    have hs : s.continuousLinearMapAt ℝ y = ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ y = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    have ht : t.continuousLinearMapAt ℝ (e y) = ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization N ℝ).continuousLinearMapAt ℝ (e y) = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    rw [hs, ht]
    change q y (a.symmL ℝ y u) (a.symmL ℝ y v) =
      h.inner (e y) (b.symmL ℝ (e y) (D y u)) (b.symmL ℝ (e y) (D y v))
    simp only [q, ContinuousLinearMap.bilinearComp_apply, D, ContinuousLinearMap.comp_apply,
      b.symmL_continuousLinearMapAt (R := ℝ) hb]


end AtiyahSinger
