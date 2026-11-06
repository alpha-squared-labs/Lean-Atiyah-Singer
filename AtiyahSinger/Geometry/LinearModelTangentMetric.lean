/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DiffeomorphTangentMetric
public import AtiyahSinger.Geometry.ManifoldModelChange

/-!
# Transport of the original metric through a specified linear model change

Public module ID: M1290.

The original full-model metric pulls back along the inverse identity
diffeomorphism to the prescribed Euclidean atlas. Its exact bilinear form
uses the same inverse linear map in both tangent arguments. The construction
retains the original tangent topologies and proves smoothness in their actual
frames. This extends the Euclidean-only metric transport at the point where
the associated sphere proof returns from its product model to the index API.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
  (M : Type*) [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℝ, V) ∞ M]

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same metric in the specified Euclidean atlas has the exact inverse-linear formula. -/
theorem exists_linearModelTangentMetric
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (TangentSpace 𝓘(ℝ, V) : M → Type _)) :
    letI := linearModelChartedSpace e M
    letI := isManifold_linearModelChartedSpace e M
    ∃ g : SmoothTangentMetric (n := n) (M := M),
      ∀ (x : M) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        g.inner x v w = h.inner x (e.symm v) (e.symm w) := by
  classical
  let := linearModelChartedSpace e M
  let := isManifold_linearModelChartedSpace e M
  let f := (linearModelDiffeomorph e M).symm
  let g : SmoothTangentMetric (n := n) (M := M) := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let J := 𝓘(ℝ, V)
    let E := EuclideanSpace ℝ (Fin n)
    let F := V
    let (x : M) : IsNormableSpace ℝ (TangentSpace I x) :=
      (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I : M → Type _) x).isNormableSpace
    let (y : M) : IsNormableSpace ℝ (TangentSpace J y) :=
      (VectorBundle.continuousLinearEquivAt ℝ F (TangentSpace J : M → Type _) y).isNormableSpace
    let L (x : M) := mfderiv I J f x
    let R (x : M) := mfderiv J I f.symm (f x)
    have hRL (x : M) : (R x).comp (L x) = ContinuousLinearMap.id ℝ _ := by
      rw [← mfderiv_comp x (f.symm.contMDiff.mdifferentiable (by simp) _)
        (f.contMDiff.mdifferentiable (by simp) _)]
      rw [show (f.symm : M → M) ∘ f = id from funext f.symm_apply_apply, mfderiv_id]
    let q (x : M) := (h.inner (f x)).bilinearComp (L x) (L x)
    refine { inner := q
             symm := fun x v w ↦ h.symm (f x) (L x v) (L x w)
             pos := ?_
             isVonNBounded := ?_
             contMDiff := ?_ }
    · intro x v hv
      apply h.pos (f x) (L x v)
      intro hz
      have hi := DFunLike.congr_fun (hRL x) v
      change R x (L x v) = v at hi
      rw [hz, map_zero] at hi
      exact hv hi.symm
    · intro x
      -- The original inverse differential carries the target metric ball onto the pullback ball.
      apply ((h.isVonNBounded (f x)).image (R x)).subset
      intro v hv
      refine ⟨L x v, hv, ?_⟩
      exact DFunLike.congr_fun (hRL x) v
    · intro x
      -- In the same native frames the metric matrix is pulled back by the derivative matrix.
      let a := trivializationAt E (TangentSpace I : M → Type _) x
      let b := trivializationAt F (TangentSpace J : M → Type _) (f x)
      let s := trivializationAt ℝ (Bundle.Trivial M ℝ) x
      let t := trivializationAt ℝ (Bundle.Trivial M ℝ) (f x)
      let aDual := a.continuousLinearMap (RingHom.id ℝ) s
      let bDual := b.continuousLinearMap (RingHom.id ℝ) t
      let D (y : M) : E →L[ℝ] F :=
        (b.continuousLinearMapAt ℝ (f y)).comp ((L y).comp (a.symmL ℝ y))
      let H (y : M) : F →L[ℝ] F →L[ℝ] ℝ :=
        (bDual.continuousLinearMapAt ℝ (f y)).comp
          ((h.inner (f y)).comp (b.symmL ℝ (f y)))
      have hD : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) ∞ D x :=
        (f.contMDiffAt (x := x)).mfderiv_const (m := ∞) (by simp)
      have hH : ContMDiffAt I 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞ H x := by
        have hc := (contMDiffAt_hom_bundle (fun y : M ↦ TotalSpace.mk'
          (F →L[ℝ] F →L[ℝ] ℝ) y (h.inner y)) (x₀ := f x)).mp (h.contMDiff (f x)) |>.2
        exact hc.comp x f.contMDiffAt
      have hHD := (hD.clm_precomp (F₃ := ℝ)).clm_comp (hH.clm_comp hD)
      apply (contMDiffAt_hom_bundle (fun y : M ↦ TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) y (q y))).mpr
      refine ⟨contMDiffAt_id, hHD.congr_of_eventuallyEq ?_⟩
      filter_upwards [a.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x),
        f.continuous.continuousAt.preimage_mem_nhds
          (b.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ (f x)))] with y ha hb
      ext u v
      change ((aDual.continuousLinearMapAt ℝ y) (q y (a.symmL ℝ y u))) v =
        ((bDual.continuousLinearMapAt ℝ (f y))
          (h.inner (f y) (b.symmL ℝ (f y) (D y u)))) (D y v)
      rw [aDual.continuousLinearMapAt_apply_of_mem ℝ ⟨ha, by simp [s]⟩,
        bDual.continuousLinearMapAt_apply_of_mem ℝ (b := f y) ⟨hb, by simp [t]⟩]
      simp only [aDual, bDual, Trivialization.continuousLinearMap_apply,
        ContinuousLinearMap.comp_apply]
      have hs : s.continuousLinearMapAt ℝ y = ContinuousLinearMap.id ℝ ℝ := by
        change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ y = _
        exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
      have ht : t.continuousLinearMapAt ℝ (f y) = ContinuousLinearMap.id ℝ ℝ := by
        change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (f y) = _
        exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
      rw [hs, ht]
      change q y (a.symmL ℝ y u) (a.symmL ℝ y v) =
        h.inner (f y) (b.symmL ℝ (f y) (D y u)) (b.symmL ℝ (f y) (D y v))
      simp only [q, ContinuousLinearMap.bilinearComp_apply, D, ContinuousLinearMap.comp_apply,
        b.symmL_continuousLinearMapAt (R := ℝ) (b := f y) hb]
      rfl
  refine ⟨g, ?_⟩
  intro x v w
  change h.inner x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) f x v)
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) f x w) = _
  change h.inner x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) (id : M → M) x v)
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) (id : M → M) x w) = _
  rw [(contMDiff_mfderiv_linearModelId e M).2.2 x]
  rfl

end AtiyahSinger
