/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopy
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing

import Mathlib.Topology.UrysohnsLemma

/-!
# Extend a homotopy of exterior frames to a global bundle adjustment

Public module ID: M1842.

A homotopy between two frames on an open set determines a global bundle
self-isomorphism matching the two frames on any closed region buffered inside
that open set. A continuous time cutoff makes the relative adjustment the
identity near the open boundary; ordinary open gluing then applies.

This is the relative bundle-isomorphism step in the smoothing supplement to
SG III.13 Lemma 13.3. It changes the identification with a smooth model while
retaining the original bundle and its compact-support class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Topology unitInterval

attribute [local instance] isFiniteRank_pullback

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- A homotopy of exterior frames extends to a global adjustment on a buffered closed set. -/
theorem IsoHomotopy.exists_global_frame_adjustment
    (U : Opens X) {F : U → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (a b : Iso ((Subtype.val : U → X) *ᵖ E) F) (H : IsoHomotopy a b)
    (A : Set X) (hA : IsClosed A) (hAU : A ⊆ (U : Set X)) :
    ∃ e : Iso E E, ∀ (x : X) (hx : x ∈ A) (v : E x),
      b.linearEquiv ⟨x, hAU hx⟩ (e.linearEquiv x v) = a.linearEquiv ⟨x, hAU hx⟩ v := by
  classical
  -- The time function vanishes near the boundary of U and equals one on A.
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA U.isOpen hAU
  have hdisjoint : Disjoint Vᶜ A :=
    Set.disjoint_left.mpr (fun _ hx hy ↦ hx (hAV hy))
  obtain ⟨w, hwzero, hwone, hwbounds⟩ :=
    exists_continuous_zero_one_of_isClosed hV.isClosed_compl hA hdisjoint
  let χ : C(X, unitInterval) := ⟨fun x ↦ ⟨w x, hwbounds x⟩,
    w.continuous.subtype_mk _⟩
  let t : C(U, unitInterval) := χ.comp (ContinuousMap.subtypeVal (U : Set X))
  let EU := (Subtype.val : U → X) *ᵖ E
  let : IsFiniteRank EU := isFiniteRank_pullback (ContinuousMap.subtypeVal (U : Set X))
  let p : unitInterval × U → U := Prod.snd
  -- Evaluate the actual cylinder isomorphism at the varying continuous time.
  have hin : Continuous (fun z : TotalSpace Unit EU ↦
      (⟨(t z.proj, z.proj), z.snd⟩ : TotalSpace Unit (p *ᵖ EU))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit EU p).continuous_iff]
    exact ((t.continuous.comp continuous_proj).prodMk continuous_proj).prodMk continuous_id
  have hinv : Continuous (fun z : TotalSpace Unit F ↦
      (⟨(t z.proj, z.proj), z.snd⟩ : TotalSpace Unit (p *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    exact ((t.continuous.comp continuous_proj).prodMk continuous_proj).prodMk continuous_id
  let c : Iso EU F :=
    { linearEquiv x := H.iso.linearEquiv (t x, x)
      continuous_total := (Pullback.continuous_lift Unit F p).comp
        (H.iso.continuous_total.comp hin)
      continuous_symm := (Pullback.continuous_lift Unit EU p).comp
        (H.iso.continuous_symm.comp hinv) }
  let u : RelativeTriple E E (U : Set X) := a.trans c.symm
  let W : Set X := (closure V)ᶜ
  let v : RelativeTriple E E W := Iso.refl _
  have hcover : (U : Set X) ∪ W = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ closure V
    · exact Or.inl (hVU hx)
    · exact Or.inr hx
  have hagree (x : X) (hxU : x ∈ U) (hxW : x ∈ W) :
      u.linearEquiv ⟨x, hxU⟩ = v.linearEquiv ⟨x, hxW⟩ := by
    have ht : t ⟨x, hxU⟩ = 0 :=
      Subtype.ext (hwzero (fun hx ↦ hxW (subset_closure hx)))
    have hc : c.linearEquiv ⟨x, hxU⟩ = a.linearEquiv ⟨x, hxU⟩ := by
      apply LinearEquiv.ext
      intro z
      change H.iso.linearEquiv (t ⟨x, hxU⟩, ⟨x, hxU⟩) z = _
      rw [ht]
      exact H.map_zero _ z
    apply LinearEquiv.ext
    intro z
    change (c.linearEquiv ⟨x, hxU⟩).symm (a.linearEquiv ⟨x, hxU⟩ z) = z
    rw [hc, LinearEquiv.symm_apply_apply]
  -- The trivial one-point action reuses the established actual open-gluing theorem.
  let : MulAction PUnit.{1} X :=
    { smul _ x := x
      one_smul _ := rfl
      mul_smul _ _ _ := rfl }
  let : ContinuousSMul PUnit.{1} X := ⟨continuous_snd⟩
  let ρ : EquivariantStructure PUnit.{1} E :=
    { linearMap _ _ := LinearMap.id
      one_map _ _ := rfl
      mul_map _ _ _ _ := rfl
      continuous_action := continuous_snd }
  obtain ⟨e, _, he, _⟩ := Iso.exists_equivariant_gluing ρ ρ (U : Set X) W U.isOpen
    isClosed_closure.isOpen_compl hcover (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl)
    u v hagree (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
  refine ⟨e, ?_⟩
  intro x hx z
  have ht : t ⟨x, hAU hx⟩ = 1 := Subtype.ext (hwone hx)
  have hc : c.linearEquiv ⟨x, hAU hx⟩ = b.linearEquiv ⟨x, hAU hx⟩ := by
    apply LinearEquiv.ext
    intro y
    change H.iso.linearEquiv (t ⟨x, hAU hx⟩, ⟨x, hAU hx⟩) y = _
    rw [ht]
    exact H.map_one _ y
  rw [he x (hAU hx)]
  change b.linearEquiv ⟨x, hAU hx⟩
    ((c.linearEquiv ⟨x, hAU hx⟩).symm (a.linearEquiv ⟨x, hAU hx⟩ z)) = _
  rw [hc, LinearEquiv.apply_symm_apply]

end AtiyahSinger.ComplexBundle
