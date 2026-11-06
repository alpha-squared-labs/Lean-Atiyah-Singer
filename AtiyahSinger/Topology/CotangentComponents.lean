/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ManifoldComponents
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Topology.DisjointUnionKZero

/-!
# Cotangent K theory restricted to the connected components

Public module ID: M1745.

D07/K02/A10: specialize finite-disjoint-union K theory to actual cotangent
inclusions of compact manifold components. The base components are compact;
their cotangent total spaces need not be compact. Each inclusion is proper
because the base component is clopen, not because the cotangent projection is
proper. The forward comparison is fixed by these inclusions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Restrict a cotangent K class to each component using the actual proper inclusion. -/
def cotangentKZeroComponents :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+
      (∀ c : ConnectedComponents M,
        CompactSupportKZero (CotangentTotalSpace (n := n) (M := manifoldComponent (n := n) c))) :=
  letI := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  AddMonoidHom.pi fun c ↦
    compactSupportKZeroPullback
      ⟨cotangentOpenInclusion (manifoldComponent (n := n) c),
        (isOpenEmbedding_cotangentOpenInclusion (manifoldComponent (n := n) c)).continuous⟩
      (isProperMap_cotangentOpenInclusion (manifoldComponent (n := n) c)
        (isClosed_singleton.preimage ConnectedComponents.continuous_coe))

/-- On a compact manifold the component restrictions form a K-group isomorphism. -/
theorem cotangentKZeroComponents_bijective [CompactSpace M] :
    Function.Bijective (cotangentKZeroComponents (n := n) (M := M)) := by
  /- Stage 1: use mathlib's local connectedness of charted spaces and its
  finiteness of the connected-component quotient of a compact locally
  connected space. Each component has the inherited open-manifold atlas.
  Stage 2: the actual cotangent inclusions assemble to a homeomorphism from
  the disjoint union of the component cotangent spaces to T*M. Its inverse
  selects the component of the original base point and keeps the covector.
  Stage 3: apply compactSupportKZeroSigmaEquiv and proper-pullback
  functoriality. This identifies its restrictions with the displayed ones
  and proves bijectivity, including the empty manifold. No connectedness
  assumption or compactness of T*M is introduced. -/
  classical
  -- Compact local connectedness gives finitely many components, without a countability axiom.
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let X := fun c : ConnectedComponents M ↦
    CotangentTotalSpace (n := n) (M := manifoldComponent (n := n) c)
  let : LocallyCompactSpace (Σ c, X c) := locallyCompactSpace_sigma X
  -- Assemble the original inclusions, keeping each base point and covector unchanged.
  let f : (Σ c, X c) → CotangentTotalSpace (n := n) (M := M) :=
    fun z ↦ cotangentOpenInclusion (manifoldComponent (n := n) z.1) z.2
  have hcontinuous : Continuous f := by
    apply continuous_sigma
    intro c
    exact (isOpenEmbedding_cotangentOpenInclusion (manifoldComponent (n := n) c)).continuous
  have hopen : IsOpenMap f := by
    apply isOpenMap_sigma.mpr
    intro c
    exact (isOpenEmbedding_cotangentOpenInclusion (manifoldComponent (n := n) c)).isOpenMap
  have hbijective : Function.Bijective f := by
    constructor
    · rintro ⟨c, z⟩ ⟨d, w⟩ h
      have hbase : z.proj.val = w.proj.val := congrArg Bundle.TotalSpace.proj h
      have hc : ConnectedComponents.mk z.proj.val = c := z.proj.property
      have hd : ConnectedComponents.mk w.proj.val = d := w.proj.property
      have hcd : c = d := hc.symm.trans ((congrArg ConnectedComponents.mk hbase).trans hd)
      subst d
      have hzw : z = w :=
        (isOpenEmbedding_cotangentOpenInclusion (manifoldComponent (n := n) c)).injective h
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

/-- The component decomposition of cotangent K theory, with the specified restrictions. -/
def cotangentKZeroComponentsEquiv [CompactSpace M] :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) ≃+
      (∀ c : ConnectedComponents M,
        CompactSupportKZero (CotangentTotalSpace (n := n) (M := manifoldComponent (n := n) c))) :=
  AddEquiv.ofBijective _ cotangentKZeroComponents_bijective

end AtiyahSinger
