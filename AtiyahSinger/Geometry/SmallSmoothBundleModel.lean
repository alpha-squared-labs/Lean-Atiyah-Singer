/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBundleSmoothing
public import AtiyahSinger.Geometry.RelativeBundleSmoothing
public import AtiyahSinger.Geometry.TrivialSmoothEquivariance
public import AtiyahSinger.Topology.TrivialEquivariantKTheory

/-!
# A small smooth model for an original finite-dimensional bundle

Public module ID: M1360.

An arbitrary-universe smooth complex bundle on a compact Hausdorff
second-countable smooth manifold admits a small native smooth model of the
same rank and a smooth bundle isomorphism.
The continuous model is obtained from the already proved realization theorem
with the one-element group. Fine smoothing then gives an isomorphism smooth
for the original source atlas, rather than assuming that a continuous model
comparison already preserves that atlas. This is the standard smooth bundle
classification comparison in SG Appendix A.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

/-- An original bundle admits a small smooth model through an actual smooth isomorphism. -/
theorem exists_small_smooth_bundle_model
    {n r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    [IsSmoothComplexBundle (n := n) (r := r) E] :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ e : Iso E F.Fiber,
        IsSmoothBundleMap (n := n) (r := r) (q := F.rank) e.toHom.linearMap := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : ContinuousSMul PUnit.{1} M := ⟨continuous_snd⟩
  let := punitContMDiffSMul (n := n) (M := M)
  let σ := EquivariantStructure.ofSubsingleton (G := PUnit.{1}) E
  have hr (x : M) : Module.finrank ℂ (E x) = r := by
    rw [VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin r)) E x]
    simp
  -- Realize the same continuous bundle with small fibers and a compatible smooth atlas.
  obtain ⟨F, hF, _, _, e, _⟩ :=
    σ.exists_smooth_bundle_iso (VG := PUnit.{1}) (n := n) r hr
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  -- Smooth the comparison itself; the original source atlas is kept in this step.
  obtain ⟨e', he', _⟩ := e.exists_smooth_homotopy_relative
    (n := n) (r := r) (q := F.rank) ∅ isClosed_empty ⊥ (by simp) (by
      intro c hc d hd j x
      exact False.elim x.property)
  exact ⟨F, hF, e', he'⟩

end AtiyahSinger
