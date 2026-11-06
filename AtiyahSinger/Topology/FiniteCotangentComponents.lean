/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CotangentComponents
public import AtiyahSinger.Topology.OpenEmbeddingKZeroRestriction

/-!
# Finite component decomposition without compactness of the base

Public module ID: M1850.

The actual cotangent restrictions remain a K-group isomorphism when the
component quotient is finite. This is the noncompact variant needed for
excision from a manifold of finite CW homotopy type.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Finitely many components suffice for the original cotangent K restriction isomorphism. -/
theorem cotangentKZeroComponents_bijective_of_finite [Finite (ConnectedComponents M)] :
    Function.Bijective (cotangentKZeroComponents (n := n) (M := M)) := by
  classical
  -- Local connectedness identifies the given quotient fibers as open components.
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let X := fun c : ConnectedComponents M ↦
    CotangentTotalSpace (n := n) (M := manifoldComponent (n := n) c)
  let : LocallyCompactSpace (Σ c, X c) := locallyCompactSpace_sigma X
  -- Assemble the original inclusions, keeping each base point and covector unchanged.
  let f : (Σ c, X c) → CotangentTotalSpace (n := n) (M := M) :=
    fun z ↦ cotangentOpenInclusion (n := n) (manifoldComponent (n := n) z.1) z.2
  have hcontinuous : Continuous f := by
    apply continuous_sigma
    intro c
    exact (isOpenEmbedding_cotangentOpenInclusion (n := n)
      (manifoldComponent (n := n) c)).continuous
  have hopen : IsOpenMap f := by
    apply isOpenMap_sigma.mpr
    intro c
    exact (isOpenEmbedding_cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c)).isOpenMap
  have hbijective : Function.Bijective f := by
    constructor
    · rintro ⟨c, z⟩ ⟨d, w⟩ h
      have hbase : z.proj.val = w.proj.val := congrArg Bundle.TotalSpace.proj h
      have hc : ConnectedComponents.mk z.proj.val = c := z.proj.property
      have hd : ConnectedComponents.mk w.proj.val = d := w.proj.property
      have hcd : c = d := hc.symm.trans ((congrArg ConnectedComponents.mk hbase).trans hd)
      subst d
      have hzw : z = w :=
        (isOpenEmbedding_cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c)).injective h
      cases hzw
      rfl
    · rintro ⟨x, ξ⟩
      exact ⟨⟨ConnectedComponents.mk x, ⟨⟨x, rfl⟩, ξ⟩⟩, rfl⟩
  let e : (Σ c, X c) ≃ₜ CotangentTotalSpace (n := n) (M := M) :=
    (Equiv.ofBijective f hbijective).toHomeomorphOfContinuousOpen hcontinuous hopen
  -- Finite disjoint-union K theory applies to these noncompact cotangent spaces.
  let k := (compactSupportKZeroHomeomorphEquiv e.symm).trans
    (compactSupportKZeroSigmaEquiv X)
  have hforward : k.toAddMonoidHom = cotangentKZeroComponents (n := n) (M := M) := by
    apply AddMonoidHom.ext
    intro a
    funext c
    change ((compactSupportKZeroPullback ⟨Sigma.mk c, continuous_sigmaMk⟩
      Topology.IsClosedEmbedding.sigmaMk.isProperMap).comp
      (compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap)) a = _
    -- The composite is exactly the displayed component inclusion, not a chosen substitute.
    rw [← compactSupportKZeroPullback_comp]
    rfl
  rw [← hforward]
  exact k.bijective

/-- Reconstruct a class by extending its restrictions through the actual component inclusions. -/
theorem sum_cotangentOpenPushforward_components [Fintype (ConnectedComponents M)]
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    (∑ c : ConnectedComponents M,
      compactSupportKZeroOpenPushforward
        (cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c))
        (isOpenEmbedding_cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c))
        (cotangentKZeroComponents (n := n) u c)) = u := by
  classical
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  -- Different components have disjoint actual cotangent images, including the zero covectors.
  have hdisjoint (c d : ConnectedComponents M) (h : c ≠ d) :
      Disjoint (Set.range (cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c)))
        (Set.range (cotangentOpenInclusion (n := n) (manifoldComponent (n := n) d))) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hxy⟩
    have hbase : y.proj.val = x.proj.val := congrArg Bundle.TotalSpace.proj hxy
    exact h (x.proj.property.symm.trans
      ((congrArg ConnectedComponents.mk hbase.symm).trans y.proj.property))
  -- The finite restriction isomorphism detects equality. Only its diagonal summand survives.
  apply (cotangentKZeroComponents_bijective_of_finite (n := n) (M := M)).injective
  funext c
  change compactSupportKZeroPullback
      ⟨cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c),
        (isOpenEmbedding_cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c)).continuous⟩
      (isProperMap_cotangentOpenInclusion (n := n) (manifoldComponent (n := n) c)
        (isClosed_singleton.preimage ConnectedComponents.continuous_coe)) _ = _
  rw [map_sum, Finset.sum_eq_single c]
  · exact compactSupportKZeroPullback_openPushforward_self _ _ _ _
  · intro d _ hdc
    exact compactSupportKZeroPullback_openPushforward_of_disjoint _ _ _ _
      (hdisjoint d c hdc) _
  · simp

end AtiyahSinger
