/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.ModelBundleTopology
public import AtiyahSinger.Topology.OpenCotangentKZero
public import AtiyahSinger.Topology.RelativeSymbolExtension

/-!
# The raw symbol class in a specified excision environment

Public module ID: M0918.

The original base bundle isomorphisms lift through the actual inverse-dual
cotangent map. A literal boundary square and the corresponding zero-section
controls then identify the ambient raw triple class with the original open
cotangent pushforward. No choice of a new representative or properness of the
open embedding is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace Topology
open scoped Manifold ContDiff

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O] [T2Space O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_model isFiniteRank_pullback

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000 in

/-- The same relative symbol and fiber comparisons give its specified open cotangent K class. -/
theorem CompactSupportTriple.compactSupportClass_eq_cotangentOpenEmbedding
    (E F : SmoothFiniteComplexBundle (n := n) O)
    (G H : SmoothFiniteComplexBundle (n := n) M) (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U)
    (K : Set O) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin H.rank)) H.Fiber
    let p := cotangentProjection (n := n) (M := O)
    let q := cotangentProjection (n := n) (M := M)
    let φ := (ContinuousMap.subtypeVal (U : Set M)).comp ⟨e, e.continuous⟩
    ∀ (eE : Iso E.Fiber ((φ : O → M) *ᵖ G.Fiber))
      (eF : Iso F.Fiber ((φ : O → M) *ᵖ H.Fiber))
      (s : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
      (t : GlobalSymbolFunction (n := n) G.Fiber H.Fiber)
      (a : CompactSupportTriple ((p : _ → O) *ᵖ E.Fiber) ((p : _ → O) *ᵖ F.Fiber))
      (b : CompactSupportTriple ((q : _ → M) *ᵖ G.Fiber) ((q : _ → M) *ᵖ H.Fiber)),
      a.control = cotangentZeroSection '' K →
      b.control = cotangentZeroSection '' (φ '' K) →
      (∀ (z : (a.controlᶜ : Set (CotangentTotalSpace (n := n) (M := O))))
        (v : E.Fiber z.val.proj),
        a.boundary.linearEquiv z v = s z.val.proj z.val.snd v) →
      (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
        (v : G.Fiber z.val.proj),
        b.boundary.linearEquiv z v = t z.val.proj z.val.snd v) →
      (∀ (x : O) (ξ : CotangentFiber (n := n) x) (v : E.Fiber x),
        t (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (eE.linearEquiv x v) =
          eF.linearEquiv x (s x ξ v)) →
      b.compactSupportClass = cotangentKZeroOpenEmbedding U e a.compactSupportClass := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin H.rank)) H.Fiber
  dsimp only
  intro eE eF s t a b ha hb hsa htb hst
  let X := CotangentTotalSpace (n := n) (M := O)
  let Y := CotangentTotalSpace (n := n) (M := M)
  let p : C(X, O) := cotangentProjection
  let q : C(Y, M) := cotangentProjection
  let φ : C(O, M) := (ContinuousMap.subtypeVal (U : Set M)).comp ⟨e, e.continuous⟩
  let d := cotangentDiffeomorph e
  let j : C(CotangentTotalSpace (n := n) (M := U), Y) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let k : C(X, Y) := j.comp ⟨d, d.continuous⟩
  have hk : IsOpenEmbedding k := (isOpenEmbedding_cotangentOpenInclusion U).comp
    d.isOpenEmbedding
  -- Lift the original two isomorphisms, keeping each original fiber vector.
  let A : Iso ((p : X → O) *ᵖ E.Fiber) ((k : X → Y) *ᵖ ((q : Y → M) *ᵖ G.Fiber)) :=
    (eE.pullback p).trans ((pullbackCompIso (E := G.Fiber) φ p).trans
      (pullbackCompIso (E := G.Fiber) q k).symm)
  let B : Iso ((p : X → O) *ᵖ F.Fiber) ((k : X → Y) *ᵖ ((q : Y → M) *ᵖ H.Fiber)) :=
    (eF.pullback p).trans ((pullbackCompIso (E := H.Fiber) φ p).trans
      (pullbackCompIso (E := H.Fiber) q k).symm)
  have hA (z : X) (v : E.Fiber z.proj) : A.linearEquiv z v = eE.linearEquiv z.proj v := by
    change ((pullbackCompIso (E := G.Fiber) q k).linearEquiv z).symm
      ((pullbackCompIso (E := G.Fiber) φ p).linearEquiv z (eE.linearEquiv z.proj v)) = _
    apply ((pullbackCompIso (E := G.Fiber) q k).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hB (z : X) (v : F.Fiber z.proj) : B.linearEquiv z v = eF.linearEquiv z.proj v := by
    change ((pullbackCompIso (E := H.Fiber) q k).linearEquiv z).symm
      ((pullbackCompIso (E := H.Fiber) φ p).linearEquiv z (eF.linearEquiv z.proj v)) = _
    apply ((pullbackCompIso (E := H.Fiber) q k).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hcontrol : b.control ⊆ k '' a.control := by
    rw [ha, hb]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨cotangentZeroSection x, ⟨x, hx, rfl⟩, ?_⟩
    change (⟨(e x).val, (0 : CotangentFiber (n := n) x).comp _⟩ : Y) =
      ⟨(e x).val, 0⟩
    rw [ContinuousLinearMap.zero_comp]
  have hclass : b.compactSupportClass = compactSupportKZeroOpenPushforward k hk
      a.compactSupportClass := by
    apply a.compactSupportClass_eq_openPushforward b k hk hcontrol A B
    intro z hz hzk v
    rw [hA, hB, hsa, htb]
    exact (hst z.proj z.snd v).symm
  -- Functoriality identifies this very total-space map with the original public K transport.
  calc
    b.compactSupportClass = compactSupportKZeroOpenPushforward k hk a.compactSupportClass :=
      hclass
    _ = cotangentKZeroOpenEmbedding U e a.compactSupportClass := by
      change compactSupportKZeroOpenPushforward (cotangentOpenInclusion U ∘ d)
        ((isOpenEmbedding_cotangentOpenInclusion U).comp d.isOpenEmbedding) _ = _
      rw [compactSupportKZeroOpenPushforward_comp,
        compactSupportKZeroOpenPushforward_homeomorph]
      · rfl
      · exact d.isOpenEmbedding

end AtiyahSinger.ComplexBundle
