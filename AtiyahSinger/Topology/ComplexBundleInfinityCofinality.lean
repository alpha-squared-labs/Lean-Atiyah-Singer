/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactSupportSliceCompactification
public import AtiyahSinger.Topology.HermitianMetricPullback

/-!
# Cofinal neighborhoods for original complex-bundle compactifications

Public module ID: M1698.

The native positive metric disks give cofinal contractible neighborhoods of
infinity. We transport the actual complements through the native-model
homeomorphism, retaining the original `Unit` total-space topology. A product
with a compact space is the actual total space of the bundle pulled back by
the second projection, with exactly the pulled-back original Hermitian form.
This supplies both comparison hypotheses used to detect supported classes in
the compact-base slice compactification.

Sources: the standard metric-disk description of bundle compact supports,
as in Atiyah, K-Theory, Section 2.7, combined with singular excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle OnePoint TopologicalSpace

universe u

/-- Homeomorphisms transport the actual cofinal contractible complements at infinity. -/
theorem cofinal_contractible_onePoint_complements_of_homeomorph
    {V Y : Type u} [TopologicalSpace V] [TopologicalSpace Y] (e : V ≃ₜ Y)
    (h : ∀ K : Compacts V, ∃ L : Compacts V, K ≤ L ∧
      ContractibleSpace ((((↑) : V → OnePoint V) '' (L : Set V))ᶜ : Set (OnePoint V))) :
    ∀ K : Compacts Y, ∃ L : Compacts Y, K ≤ L ∧
      ContractibleSpace ((((↑) : Y → OnePoint Y) '' (L : Set Y))ᶜ : Set (OnePoint Y)) := by
  intro K
  obtain ⟨L, hL, hcontract⟩ := h (K.map e.symm e.symm.continuous)
  let M := L.map e e.continuous
  refine ⟨M, ?_, ?_⟩
  · intro y hy
    exact ⟨e.symm y, hL ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩
  · let N : Set (OnePoint V) := (((↑) : V → OnePoint V) '' (L : Set V))ᶜ
    let P : Set (OnePoint Y) := (((↑) : Y → OnePoint Y) '' (M : Set Y))ᶜ
    let eInf := e.onePointCongr
    have hmem (z : OnePoint Y) : z ∈ P ↔ eInf.symm z ∈ N := by
      constructor
      · intro hz ⟨v, hv, heq⟩
        apply hz
        refine ⟨e v, ⟨v, hv, rfl⟩, ?_⟩
        have heq' := congrArg eInf heq
        exact heq'.trans (eInf.apply_symm_apply z)
      · intro hz ⟨y, ⟨v, hv, hvy⟩, heq⟩
        apply hz
        refine ⟨v, hv, ?_⟩
        subst y
        have heq' := congrArg eInf.symm heq
        exact (eInf.symm_apply_apply (v : OnePoint V)).symm.trans heq'
    let eN : P ≃ₜ N := eInf.symm.subtype hmem
    let : ContractibleSpace N := hcontract
    exact eN.contractibleSpace

namespace ComplexBundle

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

namespace ContinuousHermitianMetric

variable (h : ContinuousHermitianMetric E)

include h

/-- Original complex total-space supports admit cofinal contractible complements at infinity. -/
theorem cofinal_contractible_onePoint_complements
    (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) :
    ∀ K : Compacts (TotalSpace Unit E), ∃ L : Compacts (TotalSpace Unit E), K ≤ L ∧
      ContractibleSpace ((((↑) : TotalSpace Unit E → OnePoint (TotalSpace Unit E)) ''
        (L : Set (TotalSpace Unit E)))ᶜ : Set (OnePoint (TotalSpace Unit E))) := by
  -- The native real model uses the real part of precisely the supplied Hermitian form.
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let F := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E F
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let V := TotalSpace F E
  apply cofinal_contractible_onePoint_complements_of_homeomorph
    (nativeModelTotalHomeomorph E F)
  intro K
  have hnorm : Continuous (fun v : V ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
  let a : ℝ := max b 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdisk : IsCompact {v : V | ‖v.snd‖ ≤ a} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := F) (E := E) (K := Set.univ) isCompact_univ a
  refine ⟨⟨{v | ‖v.snd‖ ≤ a}, hdisk⟩, ?_, ?_⟩
  · intro v hv
    exact (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
  · exact contractibleSpace_bundleInfinityNeighborhood F E a ha

variable (A : Type u) [TopologicalSpace A] [CompactSpace A] [T2Space A]

/-- Compact products inherit cofinal controls from the actual second-projection pullback bundle. -/
theorem cofinal_contractible_onePoint_complements_prod
    (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) :
    ∀ K : Compacts (A × TotalSpace Unit E), ∃ L : Compacts (A × TotalSpace Unit E), K ≤ L ∧
      ContractibleSpace ((((↑) : A × TotalSpace Unit E → OnePoint (A × TotalSpace Unit E)) ''
        (L : Set (A × TotalSpace Unit E)))ᶜ : Set (OnePoint (A × TotalSpace Unit E))) := by
  let f : C(A × X, X) := ContinuousMap.snd
  let P := (f : A × X → X) *ᵖ E
  let : IsFiniteRank P := isFiniteRank_pullback f
  let e : TotalSpace Unit P ≃ₜ A × TotalSpace Unit E :=
    { toFun := fun z ↦ (z.proj.1, ⟨z.proj.2, z.snd⟩)
      invFun := fun z ↦ ⟨(z.1, z.2.proj), z.2.snd⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        (continuous_fst.comp (Pullback.continuous_proj Unit E f)).prodMk
          (Pullback.continuous_lift Unit E f)
      continuous_invFun := by
        apply (inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff.mpr
        exact (continuous_fst.prodMk
          ((continuous_proj (E := E)).comp continuous_snd)).prodMk continuous_snd }
  -- The product bundle form is the given form on the same original fiber vector.
  exact cofinal_contractible_onePoint_complements_of_homeomorph e
    ((h.pullback f).cofinal_contractible_onePoint_complements r (fun z ↦ hr z.2))

/-- The slice collapse detects the original point-relative classes of this actual bundle product. -/
theorem relativeSingularCohomologyPullback_sliceCollapse_injective
    (R : Type) [CommRing R] (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (n : ℕ) :
    Function.Injective (relativeSingularCohomologyPullback R
      (compactSupportSliceCollapse A (TotalSpace Unit E))
      (compactSupportSliceCollapse_mapsTo A (TotalSpace Unit E)) n) := by
  apply AtiyahSinger.relativeSingularCohomologyPullback_sliceCollapse_injective R A
    (TotalSpace Unit E) (h.cofinal_contractible_onePoint_complements r hr) n
  exact (compactSupportCohomologyToOnePoint_bijective_of_contractible_complements R
    (h.cofinal_contractible_onePoint_complements_prod A r hr) n).surjective

end ContinuousHermitianMetric

end ComplexBundle

end AtiyahSinger
