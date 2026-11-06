/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.RelativeBundleSmoothing
public import AtiyahSinger.Topology.RelativeBundleHomotopy

/-!
# Smooth cylinder endpoint isomorphisms preserving the original exterior frames

Public module ID: M1355.

K01: combine relative topological bundle homotopy invariance with relative
smoothing, keeping the given endpoint identifications and the same exterior
trivialization throughout. Only the composite prescribed by the exterior
coordinates must be smooth near the fixed closed set; the supplied cylinder
bundle and its endpoint identifications are allowed to be merely continuous.
The base is a second-countable Hausdorff smooth manifold.

This is a project supplement to the exterior-preserving construction in
SG III.13 Lemma 13.3, equation (13.6), using the smoothing principle of SG
Appendix A, Remark A.1. The smoothness assumption is imposed on an open
neighborhood of the fixed region. For data originally given off a compact
set, a compact enlargement supplies this buffer; preserving the original
compact set itself requires the extra neighborhood assumption stated here.
All phantom-model changes use `modelTopology`, retaining the original base
points, vectors and total-space topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff unitInterval

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

attribute [local instance] isFiniteRank_pullback trivialTopology

include hM hT hSC hE hF

/-- Smooth the relative endpoint isomorphism without changing the prescribed exterior frames. -/
theorem exists_smooth_endpoint_iso_preserving_trivialization
    (P : FiniteBundle (M × unitInterval))
    (e0 : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      Iso E
        (((⟨fun x ↦ (x, (0 : unitInterval)), continuous_id.prodMk continuous_const⟩ :
          C(M, M × unitInterval)) : M → M × unitInterval) *ᵖ P.Fiber))
    (e1 : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Iso F
        (((⟨fun x ↦ (x, (1 : unitInterval)), continuous_id.prodMk continuous_const⟩ :
          C(M, M × unitInterval)) : M → M × unitInterval) *ᵖ P.Fiber))
    (A : Set M) (hA : IsClosed A) (U : Opens M) (hAU : A ⊆ (U : Set M)) (s : ℕ)
    (triv : RelativeTriple P.Fiber (Bundle.Trivial (M × unitInterval) (Fin s → ℂ))
      (Prod.fst ⁻¹' (U : Set M)))
    (htriv : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      IsSmoothBundleMap (n := n) (r := r) (q := q) (M := U)
        (E := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
        (F := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F)
        (fun x ↦ ((e0.linearEquiv x.val).trans
          ((triv.linearEquiv ⟨(x.val, 0), x.property⟩).trans
            ((triv.linearEquiv ⟨(x.val, 1), x.property⟩).symm.trans
              (e1.linearEquiv x.val).symm))).toLinearMap)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ e : Iso E F, IsSmoothBundleMap (n := n) (r := r) (q := q) e.toHom.linearMap ∧
      ∀ (x : M) (hx : x ∈ A) (v : E x),
        triv.linearEquiv ⟨(x, 1), hAU hx⟩ (e1.linearEquiv x (e.linearEquiv x v)) =
          triv.linearEquiv ⟨(x, 0), hAU hx⟩ (e0.linearEquiv x v) := by
  /- Stage 1: the source manifold is paracompact Hausdorff and hence normal.
  Choose an open V containing A with closure V contained in U. Apply
  exists_endpoint_pullback_iso_preserving_trivialization to P, the closed
  set closure V, and the given exterior trivialization triv. This produces
  an actual continuous endpoint isomorphism a that preserves those same
  coordinate maps throughout closure V.
  Stage 2: compose e0, a and the inverse of e1. This is an isomorphism b of
  the original bundles E and F for their modelTopology instances. On V its
  fiber map equals precisely e1 inverse, triv_1 inverse, triv_0, then e0
  in composition order from right to left. Thus htriv, restricted to V,
  proves smoothness of b on the required open neighborhood of A. The given
  e0 and e1 need not be smooth separately; only this composite is used.
  Stage 3: apply Iso.exists_smooth_homotopy_relative to b, fixing A. Its
  terminal map e is smooth and agrees with b on A. At time one the endpoint
  equation for that same homotopy identifies the same e, so substituting
  into the exterior equation from Stage 1 proves the displayed equality.
  No endpoint map preserving the frames is assumed as input, and no new
  choices of exterior coordinates or endpoint identifications are made. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- Fix the original exterior formula on a neighborhood of the requested closed set.
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA U.isOpen hAU
  obtain ⟨a, ha⟩ := exists_endpoint_pullback_iso_preserving_trivialization
    P (closure V) (U : Set M) isClosed_closure U.isOpen hVU s triv
  let b : Iso E F := e0.trans (a.trans e1.symm)
  have hb (x : M) (hx : x ∈ V) (v : E x) :
      triv.linearEquiv ⟨(x, 1), hVU (subset_closure hx)⟩
          (e1.linearEquiv x (b.linearEquiv x v)) =
        triv.linearEquiv ⟨(x, 0), hVU (subset_closure hx)⟩ (e0.linearEquiv x v) := by
    change triv.linearEquiv ⟨(x, 1), hVU (subset_closure hx)⟩ (e1.linearEquiv x
      ((e1.linearEquiv x).symm (a.linearEquiv x (e0.linearEquiv x v)))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact ha x (subset_closure hx) (e0.linearEquiv x v)
  have hformula (x : M) (hx : x ∈ V) (v : E x) :
      b.linearEquiv x v =
        (e1.linearEquiv x).symm
          ((triv.linearEquiv ⟨(x, 1), hVU (subset_closure hx)⟩).symm
            (triv.linearEquiv ⟨(x, 0), hVU (subset_closure hx)⟩
              (e0.linearEquiv x v))) := by
    apply (e1.linearEquiv x).eq_symm_apply.mpr
    apply (triv.linearEquiv ⟨(x, 1), hVU (subset_closure hx)⟩).eq_symm_apply.mpr
    exact hb x hx v
  -- Restrict the given smooth composite; neither endpoint map is assumed smooth separately.
  let V' : Opens M := ⟨V, hV⟩
  let iV : C(V', M) := ContinuousMap.subtypeVal V
  let iU : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  have hVU' : V' ≤ U := fun _ hx ↦ hVU (subset_closure hx)
  have hbsmooth : IsSmoothBundleMap (n := n) (r := r) (q := q) (M := V')
      (E := (iV : V' → M) *ᵖ E) (F := (iV : V' → M) *ᵖ F)
      (fun x ↦ (b.linearEquiv x.val).toLinearMap) := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ j
    let := he
    let := hf
    let : MemTrivializationAtlas (e.pullback iU) := ⟨e, he, rfl⟩
    let : MemTrivializationAtlas (f.pullback iU) := ⟨f, hf, rfl⟩
    have h := htriv (e.pullback iU) (f.pullback iU) j
    refine (h.comp (contMDiff_inclusion hVU').contMDiffOn (fun _ hx ↦ hx)).congr ?_
    intro x hx
    have heV : (e.pullback iV).symmL ℂ x (EuclideanSpace.single j 1) =
        e.symmL ℂ x.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback iV).symmL_apply (R := ℂ) hx.1]
      change (e.pullback iV).symm x (EuclideanSpace.single j 1) =
        e.symmL ℂ (iV x) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) (b := iV x) hx.1,
        (e.pullback iV).symm_apply hx.1]
      rfl
    have heU : (e.pullback iU).symmL ℂ (Set.inclusion hVU' x)
        (EuclideanSpace.single j 1) =
        e.symmL ℂ x.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback iU).symmL_apply (R := ℂ) hx.1]
      change (e.pullback iU).symm (Set.inclusion hVU' x) (EuclideanSpace.single j 1) =
        e.symmL ℂ (iU (Set.inclusion hVU' x)) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) (b := iU (Set.inclusion hVU' x)) hx.1,
        (e.pullback iU).symm_apply hx.1]
      rfl
    change (f ⟨x.val, b.linearEquiv x.val
      ((e.pullback iV).symmL ℂ x (EuclideanSpace.single j 1))⟩).2 = _
    rw [heV, hformula x.val x.property]
    change _ = (f ⟨x.val, (e1.linearEquiv x.val).symm
      ((triv.linearEquiv ⟨(x.val, 1), _⟩).symm
        (triv.linearEquiv ⟨(x.val, 0), _⟩
          (e0.linearEquiv x.val ((e.pullback iU).symmL ℂ
            (Set.inclusion hVU' x) (EuclideanSpace.single j 1)))))⟩).2
    rw [heU]
  -- Relative smoothing keeps the same fiber map on A throughout its isomorphism homotopy.
  obtain ⟨e, hesmooth, H, hH⟩ := b.exists_smooth_homotopy_relative A hA V' hAV hbsmooth
  refine ⟨e, hesmooth, ?_⟩
  intro x hx v
  have heq : e.linearEquiv x v = b.linearEquiv x v :=
    (H.map_one x v).symm.trans (hH 1 x hx v)
  rw [heq]
  exact hb x (hAV hx) v

end AtiyahSinger.ComplexBundle
