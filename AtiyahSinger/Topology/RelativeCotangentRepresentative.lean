/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleHomotopyType
public import AtiyahSinger.Topology.CotangentRepresentative

/-!
# Relative homogeneous cotangent representatives on noncompact bases

Public module ID: M2074.

The cotangent case of SG III.13 Lemma 13.3, pp.245--246, retaining exterior
frames and their common identity action as used in (13.9). The base is a
second-countable Hausdorff smooth manifold with a supplied homotopy
equivalence to a finite CW complex.
Radial extension to all nonzero fibers sharpens the control to a compact piece
of the zero section; its class is checked using a larger compact disk homotopy.
The general real-bundle construction is applied on the actual cotangent
topology. Parameter-relative versions are outside this construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hY : T2Space Y]
  (C : Set Y) [hCW : Topology.CWComplex C] [hfin : Topology.CWComplex.Finite C]
  (e : ContinuousMap.HomotopyEquiv M C)

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback trivialTopology

include hM hT hSC hY hCW hfin e

/-- SG 13.3: a relative cotangent representative retains its actual exterior frames. -/
theorem exists_relative_homogeneous_cotangent_representative
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    ∃ E F : FiniteBundle M, ∃ (K : Set M), IsCompact K ∧
      ∃ (r : ℕ) (τE : RelativeTriple E.Fiber (Bundle.Trivial M (Fin r → ℂ)) Kᶜ)
        (τF : RelativeTriple F.Fiber (Bundle.Trivial M (Fin r → ℂ)) Kᶜ),
      ∃ a : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
        a.control = cotangentZeroSection '' K ∧
        (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
          ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
            (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
            a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
              a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
        (∀ (x : M) (hx : x ∉ K) (ξ : CotangentFiber (n := n) x)
          (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ) (v : E.Fiber x),
            τF.linearEquiv ⟨x, hx⟩ (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v) =
              τE.linearEquiv ⟨x, hx⟩ v) ∧
        a.compactSupportClass = u := by
  -- The native cotangent bundle satisfies the real local-chart condition without changing topology.
  let : RealBundle.IsFiniteRank (CotangentModel n) (CotangentFiber (n := n) (M := M)) :=
    RealBundle.isFiniteRank_of_vectorBundle _ _
  -- The general construction retains the specified finite CW witness, exterior frames and K class.
  exact RealBundle.exists_relative_homogeneous_representative (n := n)
    (CotangentModel n) (CotangentFiber (n := n) (M := M)) C e u

end AtiyahSinger
