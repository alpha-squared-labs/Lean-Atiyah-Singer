/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Analysis.SymbolLocality

/-!
# Principal classes in open transport

Public module ID: M0835.

The high-frequency comparison below concerns actual smooth full symbols in the
original global symbol spaces. Agreement locally uniformly in the base implies
that their difference has every symbol order. This compares the transported
finite representation with the prescribed homogeneous regularization; it does
not infer coordinate covariance from an equality of section actions alone.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set TopologicalSpace
open scoped Manifold ContDiff

section HighFrequency

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

/-- Full symbols agreeing at high frequency on every compact chart set differ by every order. -/
theorem isGlobalSymbol_sub_of_high_frequency {m m' : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m')
    (h : ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (_hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π _ E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π _ F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f],
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
        K ⊆ symbolChartDomain E F c e f →
        ∃ R : ℝ, ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
          globalSymbolInChart E F p.val c e f z η =
            globalSymbolInChart E F p'.val c e f z η)
    (l : ℝ) : IsGlobalSymbol (n := n) (r := r) (q := q) E F l (p.val - p'.val) := by
  intro c hc e f _ _
  let V := symbolChartDomain E F c e f
  let a := globalSymbolInChart E F p.val c e f
  let b := globalSymbolInChart E F p'.val c e f
  have hsub : globalSymbolInChart E F (p.val - p'.val) c e f = a - b := by
    ext z η v
    simp [globalSymbolInChart, a, b]
  rw [hsub]
  have hs : ContDiffOn ℝ ∞ (Function.uncurry (a - b)) (V ×ˢ univ) :=
    (p.property c hc e f).1.sub (p'.property c hc e f).1
  refine ⟨hs, ?_⟩
  intro K hKV hK i j
  -- Enlarge K before selecting a radius, so the same vanishing controls base derivatives.
  obtain ⟨K', hK', hKK', hK'V⟩ :=
    exists_compact_between hK (isOpen_symbolChartDomain E F c e f) hKV
  obtain ⟨R, hR⟩ := h c hc e f K' hK' hK'V
  have hz : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → (a - b) z η = 0 := by
    intro z hz η hη
    exact sub_eq_zero.mpr (hR z (interior_subset hz) η hη)
  -- Smoothness and bounded frequency support on this neighborhood give every real order.
  have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior (a - b) R
    (hs.mono (Set.prod_mono (interior_subset.trans hK'V) subset_rfl)) hz l
  exact hlocal.2 K hKK' hK i j

end HighFrequency

section OpenTransport

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hL : IsCompact L)
  (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (α : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (α x).toLinearMap))
  (β : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (β x).toLinearMap))

include hL hLV hKL hα hβ in
omit hT hSC hSC' in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The actual supported Hom family is transported before its order is verified.
/-- A supported full symbol transports with its order and its specified original fiber action. -/
theorem exists_supported_openGlobalSymbol {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m)
    (hpzero : ∀ x, x ∉ K → ∀ ξ, p.val x ξ = 0) :
    ∃ p' : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m,
      (∀ (x : U) η (v : E.Fiber x.val),
        p'.val (e x).val η (α x v) = β x
          (p.val x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) ∧
      (∀ y, y ∉ L → ∀ η, p'.val y η = 0) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let (x : M) : FiniteDimensional ℂ (E.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E.rank)) E.Fiber x
  let (x : M) : FiniteDimensional ℂ (F.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x
  let (x : N) : FiniteDimensional ℂ (G.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin G.rank)) G.Fiber x
  let (x : N) : FiniteDimensional ℂ (H.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin H.rank)) H.Fiber x
  let α₀ (x : U) : E.Fiber x.val ≃ₗ[ℂ] G.Fiber (e x).val :=
    { toFun := α x
      invFun := (α x).symm
      left_inv := (α x).left_inv
      right_inv := (α x).right_inv
      map_add' := (α x).map_add
      map_smul' := (α x).map_smul }
  let β₀ (x : U) : F.Fiber x.val ≃ₗ[ℂ] H.Fiber (e x).val :=
    { toFun := β x
      invFun := (β x).symm
      left_inv := (β x).left_inv
      right_inv := (β x).right_inv
      map_add' := (β x).map_add
      map_smul' := (β x).map_smul }
  let P (y : V) := CotangentFiber (n := n) y.val → (G.Fiber y.val →L[ℂ] H.Fiber y.val)
  let T (x : U) : P (e x) := fun η ↦
    (β₀ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((p.val x.val (η.comp (mfderiv I I e x))).comp
        (α₀ x).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let T' : ∀ y : V, P y := Equiv.piCongrLeft P e.toEquiv T
  let J : GlobalSymbolFunction (n := n) G.Fiber H.Fiber := fun y ↦
    if hy : y ∈ V then T' ⟨y, hy⟩ else fun _ ↦ 0
  -- Transport the whole dependent family before evaluating at a target fiber.
  have hJ (x : U) (η : CotangentFiber (n := n) (e x).val) :
      J (e x).val η = T x η := by
    simp only [J, (e x).property, ↓reduceDIte]
    exact congrFun (Equiv.piCongrLeft_apply_apply P e.toEquiv T x) η
  have hnative : ∀ (x : U) η (v : E.Fiber x.val),
      J (e x).val η (α x v) = β x (p.val x.val (η.comp (mfderiv I I e x)) v) := by
    intro x η v
    rw [hJ]
    change β₀ x (p.val x.val _ ((α₀ x).symm (α₀ x v))) = _
    rw [(α₀ x).symm_apply_apply]
    rfl
  -- Compact support inside V gives a whole zero neighborhood at every exterior point.
  have hexterior (y : N) (hy : y ∉ L) (η : CotangentFiber (n := n) y) : J y η = 0 := by
    by_cases hyV : y ∈ V
    · obtain ⟨x, hx⟩ := e.surjective ⟨y, hyV⟩
      have hxy : (e x).val = y := congrArg Subtype.val hx
      have hxK : x.val ∉ K := by
        have heq := Set.ext_iff.mp hKL x
        exact fun h ↦ hy (hxy ▸ heq.mpr h)
      subst y
      rw [hJ]
      apply ContinuousLinearMap.ext
      intro w
      change β₀ x (p.val x.val _ ((α₀ x).symm w)) = 0
      rw [hpzero x.val hxK]
      exact map_zero _
    · simp only [J, hyV, ↓reduceDIte]
  have horder : IsGlobalSymbol (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber m J := by
    intro C hC f g _ _
    let D := symbolChartDomain G.Fiber H.Fiber C f g
    have hD : IsOpen D := isOpen_symbolChartDomain G.Fiber H.Fiber C f g
    apply IsSymbol.of_locally hD
    intro z hz
    by_cases hzV : C.symm z ∈ V
    · obtain ⟨C₀, f₀, g₀, hf₀, hg₀, hC₀, Z, t, A, B,
        hZ, hzZ, hZD, hZt, htS, ht, hts, hA, hB, _, hcoord⟩ :=
        exists_local_openSymbolInChart E F G H U V e α hα β hβ C hC f g z hz hzV
      let := hf₀
      let := hg₀
      have hp₀ := (p.property C₀ hC₀ f₀ g₀).restrict htS
      have hpt := (isSymbol_cotangentSymbol t ht hts m _ hp₀).restrict hZt
      have hmatrix := isSymbol_matrixSymbol Z hZ m _ hpt A B hA hB
      refine ⟨Z, hZ, hzZ, hZD, ?_⟩
      apply hmatrix.congr_on hZ
      intro y hy
      funext η
      exact (hcoord p.val J hnative y hy η).symm
    · let Z := D ∩ C.symm ⁻¹' Lᶜ
      have hZ : IsOpen Z :=
        (C.continuousOn_symm.mono (fun _ hx ↦ hx.1.1)).isOpen_inter_preimage
          hD hL.isClosed.isOpen_compl
      have hzZ : z ∈ Z := ⟨hz, fun hx ↦ hzV (hLV hx)⟩
      refine ⟨Z, hZ, hzZ, Set.inter_subset_left, ?_⟩
      apply (isSymbol_zero Z m).congr_on hZ
      intro y hy
      funext η
      simp [globalSymbolInChart, hexterior (C.symm y) hy.2]
  exact ⟨⟨J, horder⟩, hnative, hexterior⟩

end OpenTransport

end AtiyahSinger
