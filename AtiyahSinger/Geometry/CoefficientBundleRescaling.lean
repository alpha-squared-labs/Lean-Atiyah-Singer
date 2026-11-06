/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleRescaling

/-!
# Continuous bundle rescaling as an actual open cylinder

Public module ID: M1127.

Once the original rescaled map and its inverse are jointly continuous, their
fiber-dilation formulas give an open cylinder with the same inverse identities.
This construction uses continuous vector bundles and open partial homeomorphisms;
smoothness is one way to establish its continuity inputs, but is not required.

The formulas and source domains are those of the original smooth rescaling
construction. The common topological constructor is also used for nested tubes
whose local coefficient transport is continuous in the original bundle frames.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {C : Type*} [TopologicalSpace C]

/-- Joint continuity of the actual rescaling in both directions gives an open cylinder. -/
def rescaleBundleOpenPartialHomeomorph (a : C → ℝ) (ha : Continuous a)
    (e : OpenPartialHomeomorph (TotalSpace F V) (TotalSpace F V))
    (hzero : ∀ x : B, e ⟨x, 0⟩ = ⟨x, 0⟩)
    (hsource : ∀ x : B, (⟨x, 0⟩ : TotalSpace F V) ∈ e.source)
    (hR : ContinuousOn (rescaleBundleMap e)
      {p : ℝ × TotalSpace F V | bundleFiberScale p.1 p.2 ∈ e.source})
    (hRi : ContinuousOn (rescaleBundleMap e.symm)
      {p : ℝ × TotalSpace F V | bundleFiberScale p.1 p.2 ∈ e.target}) :
    OpenPartialHomeomorph (C × TotalSpace F V) (C × TotalSpace F V) := by
  let γ : C × TotalSpace F V → TotalSpace F V := fun p ↦ bundleFiberScale (a p.1) p.2
  let j : C × TotalSpace F V → ℝ × TotalSpace F V := fun p ↦ (a p.1, p.2)
  have hj : Continuous j := (ha.comp continuous_fst).prodMk continuous_snd
  have hγ : Continuous γ := continuous_bundleFiberScale_of_vectorBundle.comp hj
  have heleft (w : TotalSpace F V) (hw : w ∈ e.source) : e.symm (e w) = w := by
    simpa only using! e.left_inv hw
  have heright (w : TotalSpace F V) (hw : w ∈ e.target) : e (e.symm w) = w := by
    simpa only using! e.right_inv hw
  have hzeroi (x : B) : e.symm ⟨x, 0⟩ = ⟨x, 0⟩ := by
    simpa only [hzero x] using heleft ⟨x, 0⟩ (hsource x)
  have hscale (k : TotalSpace F V → TotalSpace F V)
      (hk : ∀ x : B, k ⟨x, 0⟩ = ⟨x, 0⟩) (p : C × TotalSpace F V) :
      γ (p.1, rescaleBundleMap k (j p)) = k (γ p) := by
    by_cases ht : a p.1 = 0
    · simp only [γ, j, rescaleBundleMap, ht, ↓reduceIte, bundleFiberScale, zero_smul, hk]
    · change bundleFiberScale (a p.1) (rescaleBundleMap k (a p.1, p.2)) = k (γ p)
      rw [rescaleBundleMap, ite_eq_right ht]
      change (⟨(k (γ p)).proj, a p.1 • ((a p.1)⁻¹ • (k (γ p)).2)⟩ : TotalSpace F V) = k (γ p)
      rw [smul_inv_smul₀ ht]
  have hRc : ContinuousOn (fun p ↦ rescaleBundleMap e (j p)) (γ ⁻¹' e.source) :=
    hR.comp hj.continuousOn (fun _ hp ↦ hp)
  have hRic : ContinuousOn (fun p ↦ rescaleBundleMap e.symm (j p)) (γ ⁻¹' e.target) :=
    hRi.comp hj.continuousOn (fun _ hp ↦ hp)
  refine
    { toFun := fun p ↦ (p.1, rescaleBundleMap e (j p))
      invFun := fun p ↦ (p.1, rescaleBundleMap e.symm (j p))
      source := γ ⁻¹' e.source
      target := γ ⁻¹' e.target
      map_source' := fun p hp ↦ by
        change γ (p.1, rescaleBundleMap e (j p)) ∈ e.target
        rw [hscale e hzero p]
        exact e.map_source hp
      map_target' := fun p hp ↦ by
        change γ (p.1, rescaleBundleMap e.symm (j p)) ∈ e.source
        rw [hscale e.symm hzeroi p]
        exact e.map_target hp
      left_inv' := ?_
      right_inv' := ?_
      open_source := e.open_source.preimage hγ
      open_target := e.open_target.preimage hγ
      continuousOn_toFun := continuous_fst.continuousOn.prodMk hRc
      continuousOn_invFun := continuous_fst.continuousOn.prodMk hRic }
  · intro p hp
    apply Prod.ext
    · rfl
    · by_cases ht : a p.1 = 0
      · simp only [j, rescaleBundleMap, ht, ↓reduceIte]
      · change rescaleBundleMap e.symm (a p.1, rescaleBundleMap e (j p)) = p.2
        rw [rescaleBundleMap, ite_eq_right ht]
        change bundleFiberScale (a p.1)⁻¹ (e.symm (γ (p.1, rescaleBundleMap e (j p)))) = p.2
        rw [hscale e hzero p, heleft _ hp]
        change (⟨p.2.proj, (a p.1)⁻¹ • (a p.1 • p.2.2)⟩ : TotalSpace F V) = p.2
        rw [inv_smul_smul₀ ht]
  · intro p hp
    apply Prod.ext
    · rfl
    · by_cases ht : a p.1 = 0
      · simp only [j, rescaleBundleMap, ht, ↓reduceIte]
      · change rescaleBundleMap e (a p.1, rescaleBundleMap e.symm (j p)) = p.2
        rw [rescaleBundleMap, ite_eq_right ht]
        change bundleFiberScale (a p.1)⁻¹ (e (γ (p.1, rescaleBundleMap e.symm (j p)))) = p.2
        rw [hscale e.symm hzeroi p, heright _ hp]
        change (⟨p.2.proj, (a p.1)⁻¹ • (a p.1 • p.2.2)⟩ : TotalSpace F V) = p.2
        rw [inv_smul_smul₀ ht]


end AtiyahSinger
