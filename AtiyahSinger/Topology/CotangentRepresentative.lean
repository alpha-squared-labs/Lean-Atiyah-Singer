/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Topology.RealBundleRepresentative
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Homogeneous representatives over the cotangent bundle of a compact manifold

Public module ID: M1749.

P01: the compact-base cotangent case of SG III.13 Lemma 13.3, pp.245--246.
The bundles may have different ranks on different connected components. The
boundary map is defined off the entire zero section and is constant on positive
rays. It gives the original compact-support K class, using the existing actual
support-triple comparison. No smoothness is asserted at this topological stage.
The relative noncompact real-bundle version is established separately using
a finite CW homotopy witness; no such witness is needed for this compact case.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback
  trivialTopology

include hM hT hC in
/-- Every compact cotangent K class has a degree-zero pullback representative off zero. -/
theorem exists_homogeneous_cotangent_representative
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    ∃ E F : FiniteBundle M,
      ∃ a : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
        a.control = cotangentZeroSet ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
          ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
            (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
            a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
              a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
        a.compactSupportClass = u := by
  classical
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let G := CotangentModel n
  let V := CotangentFiber (n := n) (M := M)
  let : RealBundle.IsFiniteRank G V := RealBundle.isFiniteRank_of_vectorBundle G V
  let Z := TotalSpace G V
  let πV := RealBundle.projection G V
  let z₀ := RealBundle.zeroSection G V
  -- Compactness supplies countability and makes the exterior base condition empty.
  obtain ⟨a, ha⟩ := supportBundleTriple_compactSupportClass_surjective u
  let emptyFrame (P : FiniteBundle Z) : RelativeTriple P.Fiber
      (Bundle.Trivial Z (Fin 0 → ℂ)) ((πV : Z → M) ⁻¹' (Set.univ : Set M)ᶜ) := {
    linearEquiv x := (x.property (Set.mem_univ _)).elim
    continuous_total := continuous_iff_continuousAt.mpr fun z ↦
      (z.proj.property (Set.mem_univ _)).elim
    continuous_symm := continuous_iff_continuousAt.mpr fun z ↦
      (z.proj.property (Set.mem_univ _)).elim }
  obtain ⟨_, _, _, f, _⟩ := RealBundle.exists_relative_zero_pullback_iso (n := n)
    G V a.source Set.univ isCompact_univ 0 (emptyFrame a.source)
  obtain ⟨_, _, _, g, _⟩ := RealBundle.exists_relative_zero_pullback_iso (n := n)
    G V a.target Set.univ isCompact_univ 0 (emptyFrame a.target)
  let E := a.source.pullback z₀
  let F := a.target.pullback z₀
  let a' : CompactSupportTriple ((πV : Z → M) *ᵖ E.Fiber)
      ((πV : Z → M) *ᵖ F.Fiber) := a.datum.congr f g
  let τ : RelativeTriple E.Fiber F.Fiber (Set.univ : Set M)ᶜ := {
    linearEquiv x := (x.property (Set.mem_univ _)).elim
    continuous_total := continuous_iff_continuousAt.mpr fun z ↦
      (z.proj.property (Set.mem_univ _)).elim
    continuous_symm := continuous_iff_continuousAt.mpr fun z ↦
      (z.proj.property (Set.mem_univ _)).elim }
  -- The common radial theorem uses the original cotangent topology and the entire compact base.
  obtain ⟨b, hb, hhom, _, hclass⟩ := RealBundle.exists_radial_representative G V E F a'
    Set.univ isCompact_univ (fun _ _ ↦ Set.mem_univ _) τ
    (fun _ hz _ ↦ (hz (Set.mem_univ _)).elim)
  refine ⟨E, F, b, ?_, hhom, ?_⟩
  · rw [hb, Set.image_univ]
    exact range_cotangentZeroSection
  · exact hclass.trans ((a.datum.compactSupportClass_congr f g).trans
      ((compactSupportTriple_compactSupportClass_ofBoundary a.source a.target a.datum).trans ha))

end AtiyahSinger
