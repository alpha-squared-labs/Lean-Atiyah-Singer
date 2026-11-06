/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.DisjointUnionKZero
public import AtiyahSinger.Topology.EquivariantClopenKZero

/-!
# Reconstruction on a finite equivariant disjoint union

Public module ID: M1781.

This specializes the invariant clopen decomposition to the actual summand
inclusions. The given action must preserve each component and agree with
its specified action. Every term uses the original proper pullback and open
extension homomorphisms; no replacement K presentation is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Topology TopologicalSpace

attribute [local instance] locallyCompactSpace_sigma

set_option maxHeartbeats 800000 in
-- The clopen restriction and insertion maps retain their dependent subtype actions.
/-- A finite disjoint union reconstructs each original class from its actual summand classes. -/
theorem equivariantSupportTripleKZero_sigma_eq_sum_openPushforward
    {G ι : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [Fintype ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, LocallyCompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, MulAction G (X i)] [∀ i, ContinuousSMul G (X i)]
    [MulAction G (Σ i, X i)] [ContinuousSMul G (Σ i, X i)]
    (heq : ∀ (i : ι) (g : G) (x : X i),
      (⟨i, g • x⟩ : Σ i, X i) = g • (⟨i, x⟩ : Σ i, X i))
    (a : EquivariantSupportTripleKZero G (Σ i, X i)) :
    a = ∑ i : ι, equivariantSupportTripleKZeroOpenPushforward
      (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ i, X i))
      IsOpenEmbedding.sigmaMk (heq i)
      (equivariantSupportTripleKZeroPullback
        (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ i, X i))
        (heq i) IsClosedEmbedding.sigmaMk.isProperMap a) := by
  classical
  let S := Σ i, X i
  let U (i : ι) : Opens S := ⟨Set.range (Sigma.mk i), isOpen_range_sigmaMk⟩
  let (i : ι) : MulAction G (U i) :=
    { smul g x := ⟨g • x.val, by
        obtain ⟨y, hy⟩ := x.property
        exact ⟨g • y, (heq i g y).trans (congrArg (g • ·) hy)⟩⟩
      one_smul x := Subtype.ext (one_smul G x.val)
      mul_smul g h x := Subtype.ext (mul_smul g h x.val) }
  let (i : ι) : ContinuousSMul G (U i) :=
    IsInducing.subtypeVal.continuousSMul (M := G) continuous_id (fun {_ _} ↦ rfl)
  let (i : ι) : LocallyCompactSpace (U i) := (U i).isOpen.locallyCompactSpace
  have hu (i : ι) (g : G) (x : U i) :
      (Subtype.val : U i → S) (g • x) = g • x.val := rfl
  have hd : Pairwise (fun i j ↦ Disjoint (U i : Set S) (U j : Set S)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact hij (congrArg Sigma.fst hy).symm
  have hc : (⋃ i, (U i : Set S)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x.1, x.2, rfl⟩
  have h := equivariantSupportTripleKZero_eq_sum_clopen_openPushforward
    U (fun _ ↦ isClosed_range_sigmaMk) hu hd hc a
  apply h.trans
  apply Finset.sum_congr rfl
  intro i _
  -- A summand is exactly its clopen image, through the original insertion map.
  let e : X i ≃ₜ U i := IsEmbedding.sigmaMk.toHomeomorph
  let f : C(X i, U i) := ⟨e, e.continuous⟩
  let k : C(U i, S) := ⟨Subtype.val, continuous_subtype_val⟩
  have he (g : G) (x : X i) : f (g • x) = g • f x := by
    apply Subtype.ext
    exact heq i g x
  have hpull := equivariantSupportTripleKZeroPullback_comp k f (hu i) he
    isClosed_range_sigmaMk.isProperMap_subtypeVal e.isProperMap
  have hpush := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    f e.isOpenEmbedding he k (U i).isOpen.isOpenEmbedding_subtypeVal (hu i)
  have hinv (b : EquivariantSupportTripleKZero G (U i)) :
      equivariantSupportTripleKZeroOpenPushforward f e.isOpenEmbedding he
        (equivariantSupportTripleKZeroPullback f he e.isProperMap b) = b := by
    -- Surjectivity of the homeomorphism contains every representative's full control.
    obtain ⟨c, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective b
    rw [equivariantSupportTripleKZeroPullback_apply]
    exact equivariantSupportTripleKZeroOpenPushforward_class f e.isOpenEmbedding he c
      (fun x _ ↦ e.surjective x)
  change equivariantSupportTripleKZeroOpenPushforward k
    (U i).isOpen.isOpenEmbedding_subtypeVal (hu i)
    (equivariantSupportTripleKZeroPullback k (hu i)
      isClosed_range_sigmaMk.isProperMap_subtypeVal a) = _
  have hp := DFunLike.congr_fun hpull a
  have hf := DFunLike.congr_fun hpush
    (equivariantSupportTripleKZeroPullback (k.comp f)
      (fun g x ↦ (congrArg k (he g x)).trans (hu i g (f x)))
      (isClosed_range_sigmaMk.isProperMap_subtypeVal.comp e.isProperMap) a)
  simp only [AddMonoidHom.comp_apply] at hp hf
  rw [hp, hinv] at hf
  exact hf.symm.trans (congrArg
    (equivariantSupportTripleKZeroOpenPushforward (k.comp f)
      ((U i).isOpen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding)
      (fun g x ↦ (congrArg k (he g x)).trans (hu i g (f x)))) hp.symm)

end AtiyahSinger.ComplexBundle
