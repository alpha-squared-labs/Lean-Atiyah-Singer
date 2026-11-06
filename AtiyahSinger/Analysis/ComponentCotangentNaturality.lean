/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Topology.CotangentComponents
public import AtiyahSinger.Topology.OpenCotangentKZero

/-!
# Naturality of the actual cotangent component decomposition

Public module ID: M0377.

A diffeomorphism bijects the original connected components and restricts to
smooth diffeomorphisms of their inherited open atlases. The cotangent lifts
commute with the actual inclusions, since those inclusions have identity
derivative in the native charts. Proper pullback then gives the corresponding
square on compact-support K theory. This supplies the finite-component step
in the analytic-index naturality argument, including zero-dimensional bases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)

/-- The component bijection induced by the original point map and its original inverse. -/
def diffeomorphConnectedComponentsEquiv : ConnectedComponents M ≃ ConnectedComponents N where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (e.symm (e x)) = ConnectedComponents.mk x
    rw [e.symm_apply_apply]
  right_inv c := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (e (e.symm y)) = ConnectedComponents.mk y
    rw [e.apply_symm_apply]

/-- Restrict the specified diffeomorphism to one of its actual connected components. -/
def componentDiffeomorph (c : ConnectedComponents M) :
    manifoldComponent (n := n) c ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯
      manifoldComponent (n := m) (diffeomorphConnectedComponentsEquiv e c) where
  toFun x := ⟨e x.val, by
    change ConnectedComponents.mk (e x.val) = diffeomorphConnectedComponentsEquiv e c
    change diffeomorphConnectedComponentsEquiv e (ConnectedComponents.mk x.val) = _
    rw [x.property]⟩
  invFun y := ⟨e.symm y.val, by
    apply (diffeomorphConnectedComponentsEquiv e).injective
    change ConnectedComponents.mk (e (e.symm y.val)) = diffeomorphConnectedComponentsEquiv e c
    rw [e.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val

/-- Cotangent transport on a component commutes with its actual ambient inclusion. -/
theorem cotangentDiffeomorph_componentDiffeomorph (c : ConnectedComponents M)
    (z : CotangentTotalSpace (n := n) (M := manifoldComponent (n := n) c)) :
    cotangentOpenInclusion
        (manifoldComponent (n := m) (diffeomorphConnectedComponentsEquiv e c))
        (cotangentDiffeomorph (componentDiffeomorph e c) z) =
      cotangentDiffeomorph e (cotangentOpenInclusion (manifoldComponent (n := n) c) z) := by
  let U := manifoldComponent (n := n) c
  let V := manifoldComponent (n := m) (diffeomorphConnectedComponentsEquiv e c)
  let d := componentDiffeomorph e c
  -- The inverse restricted map and ambient inverse have the same native tangent derivative.
  have hderiv (y : V) :
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) d.symm y =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          e.symm y.val := by
    have hleft := mfderiv_comp y
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) (d.symm y))
      (d.symm.mdifferentiable (by simp) y)
    have hright := mfderiv_comp y
      (e.symm.mdifferentiable (by simp) y.val)
      ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) y)
    rw [mfderiv_openSubtypeVal] at hleft
    rw [mfderiv_openSubtypeVal] at hright
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T ↦ T v) (hleft.symm.trans hright)
  change (⟨e z.proj.val, z.snd.comp
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      d.symm (d z.proj))⟩ : CotangentTotalSpace (n := m) (M := N)) =
    ⟨e z.proj.val, z.snd.comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        e.symm (e z.proj.val))⟩
  rw [hderiv]
  rfl

variable [T2Space M] [T2Space N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The original proper component restrictions commute with cotangent diffeomorphism transport. -/
theorem cotangentKZeroComponents_diffeomorph (c : ConnectedComponents M)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    cotangentKZeroComponents (cotangentKZeroDiffeomorph e u)
        (diffeomorphConnectedComponentsEquiv e c) =
      cotangentKZeroDiffeomorph (componentDiffeomorph e c) (cotangentKZeroComponents u c) := by
  let U := manifoldComponent (n := n) c
  let V := manifoldComponent (n := m) (diffeomorphConnectedComponentsEquiv e c)
  let g := cotangentDiffeomorph e
  let h := cotangentDiffeomorph (componentDiffeomorph e c)
  let i : C(CotangentTotalSpace (n := n) (M := U),
      CotangentTotalSpace (n := n) (M := M)) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let j : C(CotangentTotalSpace (n := m) (M := V),
      CotangentTotalSpace (n := m) (M := N)) :=
    ⟨cotangentOpenInclusion V, (isOpenEmbedding_cotangentOpenInclusion V).continuous⟩
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin m)) N
  have hi : IsProperMap i := isProperMap_cotangentOpenInclusion U
    (isClosed_singleton.preimage ConnectedComponents.continuous_coe)
  have hj : IsProperMap j := isProperMap_cotangentOpenInclusion V
    (isClosed_singleton.preimage ConnectedComponents.continuous_coe)
  -- Invert the same geometric square before applying contravariant proper pullback.
  have hsquare : (⟨g.symm, g.symm.continuous⟩ : C(_, _)).comp j =
      i.comp ⟨h.symm, h.symm.continuous⟩ := by
    apply ContinuousMap.ext
    intro z
    apply g.injective
    change g (g.symm (j z)) = g (i (h.symm z))
    rw [g.apply_symm_apply]
    have hforward := cotangentDiffeomorph_componentDiffeomorph e c (h.symm z)
    change j (h (h.symm z)) = g (i (h.symm z)) at hforward
    simpa only [h.apply_symm_apply] using hforward
  have hmaps : (compactSupportKZeroPullback j hj).comp
      (compactSupportKZeroPullback ⟨g.symm, g.symm.continuous⟩ g.symm.isProperMap) =
        (compactSupportKZeroPullback ⟨h.symm, h.symm.continuous⟩ h.symm.isProperMap).comp
          (compactSupportKZeroPullback i hi) := by
    rw [← compactSupportKZeroPullback_comp, ← compactSupportKZeroPullback_comp]
    congr 1
  exact DFunLike.congr_fun hmaps u

end AtiyahSinger
