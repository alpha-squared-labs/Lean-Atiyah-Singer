/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexBundle
public import AtiyahSinger.Topology.BundlePullback
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Restriction and zero extension of smooth bundle sections

Public module ID: M1325.

D01/E01/UL03: the standard section spaces with prescribed support, restriction to
an open submanifold, and zero extension when the support is closed in the ambient
manifold and contained in that open set. The latter need not be compact. The bundle
on the open set is mathlib's actual pullback along the continuous subtype inclusion.

These are the geometric maps used in SG III.13.4, pp.248--249. The boundary
smoothness argument is an explicit project supplement. Merely having support
closed in the open submanifold does not justify zero extension across its boundary.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

section Supported

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Smooth sections whose nonzero locus lies in K; for closed K this is the usual Γ_K(E). -/
def supportedSmoothSections (K : Set M) : Submodule ℂ (smoothSections (n := n) (r := r) E) where
  carrier := {s | ∀ x, x ∉ K → s.val x = 0}
  zero_mem' := by
    intro x hx
    rfl
  add_mem' := by
    intro u v hu hv x hx
    change u.val x + v.val x = 0
    rw [hu x hx, hv x hx, add_zero]
  smul_mem' := by
    intro c u hu x hx
    change c • u.val x = 0
    rw [hu x hx, smul_zero]

end Supported

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

set_option linter.unusedSectionVars false in
/-- Restriction to the inherited open manifold and pullback bundle preserves smoothness. -/
theorem isSmoothSection_restrict_opens (U : Opens M)
    (s : smoothSections (n := n) (r := r) E) :
    IsSmoothSection (n := n) (r := r) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E) (fun x ↦ s.val x.val) := by
  /- Every frame in the native pullback atlas is the pullback of an ambient
  frame. Its coordinate expression is the original one composed with the smooth
  open-submanifold inclusion. Restrict to the inverse image of the frame base.
  This uses the inherited atlas, with no arbitrary replacement of the bundle topology. -/
  intro e he
  rcases he with ⟨e, he, rfl⟩
  -- The native pulled-back chart evaluates the same original fiber coordinates.
  exact (s.property e he).comp contMDiff_subtype_val.contMDiffOn (fun x hx ↦ hx)

/-- The actual restriction map evaluates a section at the underlying ambient point. -/
def smoothSectionRestriction (U : Opens M) :
    smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := r) (M := U)
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E) where
  toFun s := ⟨fun x ↦ s.val x.val, isSmoothSection_restrict_opens E U s⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
set_option linter.unusedSectionVars false in
/-- Support closed in M and contained in U makes zero extension smooth across the boundary. -/
theorem isSmoothSection_zeroExtend_opens (U : Opens M) (K : Set M)
    (hK : IsClosed K) (hKU : K ⊆ (U : Set M))
    (s : supportedSmoothSections (n := n) (r := r) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      ((Subtype.val : U → M) ⁻¹' K)) :
    IsSmoothSection (n := n) (r := r) E
      (fun x ↦ if hx : x ∈ U then s.val.val ⟨x, hx⟩ else 0) := by
  /- Inside U use the original smooth section in pulled-back bundle frames.
  At any point outside U, closedness of K and K ⊆ U give an ambient open
  neighborhood disjoint from K. The displayed extension is identically zero
  there, including its portion inside U. Smoothness therefore holds locally
  at every point. No compactness or uniform distance from the boundary is needed. -/
  classical
  intro e he
  let := he
  intro x hx
  by_cases hxU : x ∈ U
  · -- On the open set, the pulled-back chart has the exact original coordinate formula.
    apply ContMDiffAt.contMDiffWithinAt
    rw [← contMDiffAt_subtype_iff (U := U) (x := ⟨x, hxU⟩)]
    have hchart : MemTrivializationAtlas
        (e.pullback (ContinuousMap.subtypeVal (U : Set M))) := ⟨e, he, rfl⟩
    have hs := (s.val.property _ hchart).contMDiffAt
      ((e.pullback (ContinuousMap.subtypeVal (U : Set M))).open_baseSet.mem_nhds
        (show (⟨x, hxU⟩ : U) ∈ (e.pullback (ContinuousMap.subtypeVal (U : Set M))).baseSet
          from hx))
    apply hs.congr_of_eventuallyEq
    filter_upwards [] with y
    erw [dite_eq_left y.property]
    rfl
  · -- Closed ambient support makes the zero extension locally zero at every boundary point.
    have hxK : x ∉ K := fun h ↦ hxU (hKU h)
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds hxK, e.open_baseSet.mem_nhds hx] with y hy hye
    have hzero : (if hyU : y ∈ U then s.val.val ⟨y, hyU⟩ else 0) =
        (0 : E y) := by
      by_cases hyU : y ∈ U
      · erw [dite_eq_left hyU]
        exact s.property ⟨y, hyU⟩ hy
      · erw [dite_eq_right hyU]
    erw [hzero]
    exact (e.linearEquivAt ℂ y hye).map_zero

open scoped Classical in
/-- Extend a supported section by the original fiber value on U and zero off U. -/
def smoothSectionZeroExtension (U : Opens M) (K : Set M)
    (hK : IsClosed K) (hKU : K ⊆ (U : Set M)) :
    supportedSmoothSections (n := n) (r := r) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      ((Subtype.val : U → M) ⁻¹' K) →ₗ[ℂ] smoothSections (n := n) (r := r) E where
  toFun s := ⟨fun x ↦ if hx : x ∈ U then s.val.val ⟨x, hx⟩ else 0,
    isSmoothSection_zeroExtend_opens E U K hK hKU s⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    change (if hx : x ∈ U then (u + v).val.val ⟨x, hx⟩ else (0 : E x)) =
      (if hx : x ∈ U then u.val.val ⟨x, hx⟩ else (0 : E x)) +
        (if hx : x ∈ U then v.val.val ⟨x, hx⟩ else (0 : E x))
    by_cases hx : x ∈ U
    · erw [dite_eq_left hx, dite_eq_left hx, dite_eq_left hx]
      rfl
    · erw [dite_eq_right hx, dite_eq_right hx, dite_eq_right hx]
      exact (zero_add (0 : E x)).symm
  map_smul' c u := by
    apply Subtype.ext
    funext x
    change (if hx : x ∈ U then (c • u).val.val ⟨x, hx⟩ else (0 : E x)) =
      c • (if hx : x ∈ U then u.val.val ⟨x, hx⟩ else (0 : E x))
    by_cases hx : x ∈ U
    · erw [dite_eq_left hx, dite_eq_left hx]
      rfl
    · erw [dite_eq_right hx, dite_eq_right hx]
      exact (smul_zero c : c • (0 : E x) = 0).symm

end AtiyahSinger
