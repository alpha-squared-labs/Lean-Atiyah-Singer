/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FiniteComplementSmoothModel
public import AtiyahSinger.Geometry.RelativeBundleSmoothing
public import AtiyahSinger.Topology.ExteriorFrameAdjustment

/-!
# Smooth exterior identifications by a global bundle adjustment

Public module ID: M1356.

An actual continuous isomorphism on an open submanifold can be made smooth by
changing the global identification of its source bundle. On a closed region
inside that open set, the adjusted isomorphism is exactly the originally given
map. The global model comparison absorbs the adjustment, so its composition
with the smooth exterior map retains the original fiber map on that region.
This is the comparison used to retain the prescribed compact-support K class.

This is the relative smoothing supplement to SG III.13 Lemma 13.3. Its two
ingredients are fine approximation through isomorphisms and the extension of
a homotopy of exterior frames by a continuous time cutoff.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

section SmoothAdjustment

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hE hF

/-- Smooth an exterior identification by an exact global adjustment on a closed interior region. -/
theorem Iso.exists_smooth_exterior_adjustment (U : Opens M)
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Iso ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F))
    (A : Set M) (hA : IsClosed A) (hAU : A ⊆ (U : Set M)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ b : Iso ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F),
      IsSmoothBundleMap (n := n) (r := r) (q := q) (M := U)
        (fun x ↦ (b.linearEquiv x).toLinearMap) ∧
      ∃ e : Iso E E, ∀ (x : M) (hx : x ∈ A) (v : E x),
        b.linearEquiv ⟨x, hAU hx⟩ (e.linearEquiv x v) =
          a.linearEquiv ⟨x, hAU hx⟩ v := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let p : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let EU := (p : U → M) *ᵖ E
  let FU := (p : U → M) *ᵖ F
  let : IsSmoothComplexBundle (n := n) (r := r) EU :=
    isSmoothComplexBundle_pullback E p contMDiff_subtype_val
  let : IsSmoothComplexBundle (n := n) (r := q) FU :=
    isSmoothComplexBundle_pullback F p contMDiff_subtype_val
  -- Native smooth pullback and Unit pullback carry exactly the same total topology.
  let tE : TopologicalSpace (TotalSpace Unit EU) :=
    @Pullback.TotalSpace.topologicalSpace M Unit E U (p : U → M) _
      (modelTopology (EuclideanSpace ℂ (Fin r)) E)
  let tF : TopologicalSpace (TotalSpace Unit FU) :=
    @Pullback.TotalSpace.topologicalSpace M Unit F U (p : U → M) _
      (modelTopology (EuclideanSpace ℂ (Fin q)) F)
  have hEtop : modelTopology (EuclideanSpace ℂ (Fin r)) EU = tE := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tE, modelTopology]
    rfl
  have hFtop : modelTopology (EuclideanSpace ℂ (Fin q)) FU = tF := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, tF, modelTopology]
    rfl
  have hsmooth : ∃ b : Iso EU FU,
      IsSmoothBundleMap (n := n) (r := r) (q := q) b.toHom.linearMap ∧
        Nonempty (IsoHomotopy a b) := by
    -- The topology equalities change no point or vector of the given isomorphism.
    revert a
    change letI := tE; letI := tF; ∀ a : Iso EU FU, ∃ b : Iso EU FU,
      IsSmoothBundleMap (n := n) (r := r) (q := q) b.toHom.linearMap ∧
        Nonempty (IsoHomotopy a b)
    rw [← hEtop, ← hFtop]
    intro a
    let := modelTopology (EuclideanSpace ℂ (Fin r)) EU
    let := modelTopology (EuclideanSpace ℂ (Fin q)) FU
    let hEU : IsSmoothComplexBundle (n := n) (r := r) EU :=
      isSmoothComplexBundle_pullback E p contMDiff_subtype_val
    let hFU : IsSmoothComplexBundle (n := n) (r := q) FU :=
      isSmoothComplexBundle_pullback F p contMDiff_subtype_val
    obtain ⟨b, hb, H, _⟩ := a.exists_smooth_homotopy_relative
      (n := n) (r := r) (q := q) (M := U) (E := EU) (F := FU) (hE := hEU) (hF := hFU)
      (∅ : Set U) isClosed_empty ⊥ (Set.empty_subset _) (by
        intro e he f hf j x
        exact x.property.elim)
    exact ⟨b, hb, ⟨H⟩⟩
  obtain ⟨b, hb, ⟨H⟩⟩ := hsmooth
  let : IsFiniteRank FU := isFiniteRank_pullback p
  obtain ⟨e, he⟩ := H.exists_global_frame_adjustment U a b A hA hAU
  exact ⟨b, hb, e, he⟩

end SmoothAdjustment

variable {n : ℕ} {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hY : T2Space Y]

include hM hT hSC hY

/-- A fixed-rank bundle of finite CW type has a smooth model retaining an exterior identification.
The isomorphism with that model, rather than the original exterior map, absorbs the adjustment. -/
theorem FiniteBundle.exists_smooth_model_preserving_exterior
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (h : ContinuousMap.HomotopyEquiv M C) (E : FiniteBundle M) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E.Fiber x) = r)
    (T : SmoothFiniteComplexBundle (n := n) M) (U : Opens M)
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
      Iso ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber)
        ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ T.Fiber))
    (A : Set M) (hA : IsClosed A) (hAU : A ⊆ (U : Set M)) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
      ∃ e : Iso E.Fiber F.Fiber,
        ∃ b : Iso ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber)
            ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ T.Fiber),
          IsSmoothBundleMap (n := n) (r := F.rank) (q := T.rank) (M := U)
            (fun x ↦ (b.linearEquiv x).toLinearMap) ∧
          ∀ (x : M) (hx : x ∈ A) (v : E.Fiber x),
            b.linearEquiv ⟨x, hAU hx⟩ (e.linearEquiv x v) =
              a.linearEquiv ⟨x, hAU hx⟩ v := by
  -- First smooth the actual finite presentation provided by the specified homotopy model.
  obtain ⟨F, hF, ⟨e₀⟩⟩ := E.exists_smooth_model_of_homotopyEquiv_finiteCW
    (n := n) C h r hr
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  let p : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let a₀ := (e₀.symm.pullback p).trans a
  -- Smooth the transferred exterior map and absorb its homotopy into the same model comparison.
  obtain ⟨b, hb, e₁, he₁⟩ := a₀.exists_smooth_exterior_adjustment
    (n := n) (r := F.rank) (q := T.rank) U A hA hAU
  refine ⟨F, hF, e₀.trans e₁, b, hb, ?_⟩
  intro x hx v
  have he := he₁ x hx (e₀.linearEquiv x v)
  change b.linearEquiv ⟨x, hAU hx⟩ (e₁.linearEquiv x (e₀.linearEquiv x v)) = _
  rw [he]
  change a.linearEquiv ⟨x, hAU hx⟩ ((e₀.linearEquiv x).symm (e₀.linearEquiv x v)) = _
  rw [LinearEquiv.symm_apply_apply]

end AtiyahSinger.ComplexBundle
