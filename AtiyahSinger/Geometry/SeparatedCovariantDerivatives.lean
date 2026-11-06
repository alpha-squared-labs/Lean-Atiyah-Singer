/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.IteratedCovariantDerivative

/-!
# Smooth actual covariant tensors on a Hausdorff manifold

Public module ID: M1359.

The native Hom connection preserves smoothness on a Hausdorff base because
smooth bumps extend local tangent frames before testing the given global
connection classes. Iterate that established construction on the original
bundle, without changing its tensor topology or assuming a connection family.
This supplies the regularity needed by the separated Sobolev consumers of
SG III.2 (2.1). The original statements without separation remain inactive and unproved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace I (M := M)

/-- On a Hausdorff base, the actual iterated covariant derivatives of a smooth section are smooth.
Both original connections and all native recursive Hom bundle structures are retained. -/
theorem contMDiff_iteratedCovariantDerivative_of_t2Space
    (covT : CovariantDerivative I (EuclideanSpace ℝ (Fin n)) TM)
    (covE : CovariantDerivative I (EuclideanSpace ℂ (Fin r)) E)
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
    (k : ℕ) (u : smoothSections (n := n) (r := r) E) :
    ContMDiff I ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E k)) ∞
      (fun x ↦ (⟨x, iteratedCovariantDerivative covT covE k u.val x⟩ :
        TotalSpace (CovariantTensorModel (n := n) (r := r) E k)
          (CovariantTensorFiber (n := n) (r := r) E k))) := by
  -- The same induced connections are smooth at every stage of the native Hom tower.
  have hconnection (j : ℕ) : CovariantDerivative.ContMDiffCovariantDerivative
      (covariantTensorConnection covT covE j) ∞ := by
    induction j with
    | zero => exact hcovE
    | succ j ih =>
      exact contMDiff_covariantHomConnection_of_t2Space covT
        (covariantTensorConnection covT covE j) hcovT ih
  -- Apply each connection to the preceding smooth tensor, starting from the original section.
  induction k with
  | zero =>
    change ContMDiff I ((I).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r))) ∞
      (fun x ↦ (⟨x, u.val x⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
    intro x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    exact (e.contMDiffAt_section_iff he).mpr
      ((u.property e inferInstance).contMDiffAt (e.open_baseSet.mem_nhds he))
  | succ k ih =>
    exact contMDiffOn_univ.mp ((hconnection k).contMDiff.contMDiff
      (by simpa using ih.contMDiffOn))

end AtiyahSinger
