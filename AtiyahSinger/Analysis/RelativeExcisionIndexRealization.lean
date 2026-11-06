/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RelativeExcisionIndexModel
public import AtiyahSinger.Analysis.RelativeExcisionSymbolKClass

import all AtiyahSinger.Analysis.OpenExtensionIndex

/-!
# Realizing one supported relative model in a compact environment

Public module ID: M0916.

Compatible smooth exterior frames identify the supplied bundle multiplier
with the identity. Relative geometry then supplies ambient bundles, metrics
and density, while the prescribed finite family is extended through the given
open parametrization. The resulting operator, full kernel supports and symbol
K class use those same witnesses. The source need not be compact.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace MeasureTheory Filter
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ O]
  [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_model isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- The extended limit accommodates the compatible exterior frames and same relative quantization
-- index.
/-- Compatible exterior frames give a finite relative quantization its ambient index model. -/
theorem nonempty_relativeExcisionIndexModel
    (E F : SmoothFiniteComplexBundle (n := n) O) (hEF : E.rank = F.rank)
    (K L : Set O) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L)
    (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (ν : Measure O) [IsSmoothPositiveMeasure (n := n) ν]
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (hc : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
      (fun x ↦ (c x).toLinearMap))
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (haext : ∀ x, x ∉ K → ∀ ξ, a.val x ξ = c x)
    (g₀ : SmoothCotangentMetric (n := n) (M := O))
    (d₀ : ℕ) (T : Fin d₀ → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (hsupport : ∀ j, (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L)
    (hprincipal : ∀ x ξ, 1 ≤ g₀.length x ξ →
      (∑ j, (T j).globalSymbol).val x ξ + c x = a.val x ξ)
    (D : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L →ₗ[ℂ]
      supportedSmoothSections (n := n) (r := F.rank) F.Fiber L)
    (hD : ∀ s, (D s).val =
      (smoothSectionMap (fun x ↦ (c x).toLinearMap) hc + ∑ j, (T j).toLinearMap) s.val)
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := O)))
    (hu : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ b : CompactSupportTriple
          ((cotangentProjection (n := n) (M := O) : _ → O) *ᵖ E.Fiber)
          ((cotangentProjection (n := n) (M := O) : _ → O) *ᵖ F.Fiber),
        b.control = cotangentZeroSection '' L ∧
        (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := O))))
          (v : E.Fiber z.val.proj), b.boundary.linearEquiv z v = a.val z.val.proj z.val.snd v) ∧
        b.compactSupportClass = u)
    (U : Opens M)
    (e : O ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ U) :
    let W : Opens O := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
    ∀ (τE : ∀ x : W, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
      (τF : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
      IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank) (M := W)
        (E := ((ContinuousMap.subtypeVal (W : Set O) : W → O) *ᵖ E.Fiber))
        (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τE x).toLinearMap) →
      IsSmoothBundleMap (n := n) (r := F.rank) (q := E.rank) (M := W)
        (E := ((ContinuousMap.subtypeVal (W : Set O) : W → O) *ᵖ F.Fiber))
        (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τF x).toLinearMap) →
      (∀ (x : W) (v : E.Fiber x.val), τF x (c x.val v) = τE x v) →
      Nonempty (RelativeExcisionIndexModel E F h k ν L D u U e) := by
  classical
  dsimp only
  intro τE τF hτE hτF hτ
  -- Extend the same source geometry, preserving the pairings and the actual pushed density.
  obtain ⟨G, H, _, _, α, β, hα, hβ, d, hd, hcd, hdext,
      g, l, μ, hμ, A₀, hLA, _, hg, hl, hμν⟩ :=
    exists_relative_excision_data_of_diffeomorph E F hEF U e K L hK hL hKL
      h k ν c hc τE τF hτE hτF hτ
  let : IsSmoothPositiveMeasure (n := n) μ := hμ
  let p : C(O, U) := ⟨e, e.continuous⟩
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let φ : C(O, M) := i.comp p
  let L' : Set M := φ '' L
  have hL' : IsCompact L' := hL.image φ.continuous
  have hL'U : L' ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact (e x).property
  have hLL : e ⁻¹' ((Subtype.val : U → M) ⁻¹' L') = L := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have heq : y = x := e.injective (Subtype.ext hxy)
      exact heq ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hdextL (y : M) (hy : y ∉ L') : Function.Bijective (d y) :=
    hdext y (fun h ↦ hy (Set.image_mono hKL h))
  -- The source-top adapter changes neither a point nor a fiber vector.
  let e₀ := diffeomorphFromTop e
  let GU := G.pullback i contMDiff_subtype_val
  let HU := H.pullback i contMDiff_subtype_val
  have hα₀ := IsSmoothBundleMap.fromTop E GU e (fun x ↦ (α x).toLinearMap) hα
  have hβ₀ := IsSmoothBundleMap.fromTop F HU e (fun x ↦ (β x).toLinearMap) hβ
  have hLL₀ : e₀ ⁻¹' ((Subtype.val : U → M) ⁻¹' L') =
      (Subtype.val : (⊤ : Opens O) → O) ⁻¹' L := by
    change (Subtype.val : (⊤ : Opens O) → O) ⁻¹'
      (e ⁻¹' ((Subtype.val : U → M) ⁻¹' L')) = _
    rw [hLL]
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := G.rank) (q := H.rank) (E := G.Fiber) (F := H.Fiber)
  obtain ⟨P, a', ha', hPe, hPclass, hPsupport, hPact, ha'action, _, b', hb'control,
      hb'boundary, hb'class⟩ :=
    exists_relative_elliptic_openExtension_of_pieces E F G H ⊤ U e₀ L L'
      hL hL' (Set.subset_univ _) hL'U hLL₀
      (fun x ↦ α x.val) hα₀ (fun x ↦ β x.val) hβ₀ μ a ha c hc
      (fun x hx ↦ haext x (fun hxK ↦ hx (hKL hxK))) d hd
      (fun x ↦ hcd x.val) hdextL g₀ d₀ T hsupport hprincipal R
  -- The correction is an actual PDO and controls the full operator and adjoint kernels.
  let B₀ : DifferentialOperator (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber 0 :=
    ⟨smoothSectionMap (fun y ↦ (d y).toLinearMap) hd,
      isDifferentialOperator_smoothSectionMap _ hd⟩
  let B : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber μ 0 :=
    ⟨B₀.toLinearMap, by simpa only [Nat.cast_zero] using
      B₀.isPseudodifferentialOperator (μ := μ)⟩
  let S := P.add (B.smul (-1))
  have hS : S.toLinearMap = P.toLinearMap - smoothSectionMap (fun y ↦ (d y).toLinearMap) hd := by
    change P.toLinearMap + (-1 : ℂ) • B₀.toLinearMap = _
    rw [neg_one_smul, ← sub_eq_add_neg]
  have hPdecomp : P.toLinearMap =
      smoothSectionMap (fun y ↦ (d y).toLinearMap) hd + S.toLinearMap := by
    rw [hS]
    abel
  obtain ⟨hPP, hPadj, hkerP, hkerPadj⟩ :=
    support_and_kernel_of_supported_perturbation P S (fun y ↦ (d y).toLinearMap) hd
      hPdecomp L' hL'.isClosed (hS.symm ▸ hPsupport) hdextL g l
  -- Restrict the neighborhood density equality to the same image of the piece support.
  have hmeasure : Measure.map e (ν.restrict L) =
      (μ.comap (Subtype.val : U → M)).restrict ((Subtype.val : U → M) ⁻¹' L') := by
    have hsub : (Subtype.val : U → M) ⁻¹' L' ⊆
        (Subtype.val : U → M) ⁻¹' (A₀ : Set M) := fun _ hx ↦ hLA hx
    have hm := congrArg (fun ρ : Measure U ↦
      ρ.restrict ((Subtype.val : U → M) ⁻¹' L')) hμν
    rw [Measure.restrict_restrict_of_subset hsub,
      Measure.restrict_restrict_of_subset hsub] at hm
    have hr := e.toHomeomorph.measurableEmbedding.restrict_map ν
      ((Subtype.val : U → M) ⁻¹' L')
    change (Measure.map e ν).restrict ((Subtype.val : U → M) ⁻¹' L') =
      Measure.map e (ν.restrict (e ⁻¹' ((Subtype.val : U → M) ⁻¹' L'))) at hr
    rw [hLL] at hr
    exact hr.symm.trans hm.symm
  obtain ⟨A, hAvalue, hApair⟩ := exists_pairingPreserving_supportedSectionOpenEmbeddingEquiv
    E G U e L L' hL'.isClosed hL'U hLL α hα h g ν μ
      (fun x hx ↦ hg x (hLA ⟨x, hx, rfl⟩)) hmeasure
  obtain ⟨B', hBvalue, hBpair⟩ := exists_pairingPreserving_supportedSectionOpenEmbeddingEquiv
    F H U e L L' hL'.isClosed hL'U hLL β hβ k l ν μ
      (fun x hx ↦ hl x (hLA ⟨x, hx, rfl⟩)) hmeasure
  have haction (s : supportedSmoothSections (n := n) (r := E.rank) E.Fiber L) :
      P.toLinearMap (A s).val = (B' (D s)).val := by
    have hdelta := hPact s.val (A s).val
      (Filter.Eventually.of_forall (fun x ↦ hAvalue s x.val))
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ U
    · let x : O := e.symm ⟨y, hy⟩
      have heq : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      have hx : (P.toLinearMap (A s).val).val (e x).val =
          (B' (D s)).val.val (e x).val := by
        have hdeltax := hdelta ⟨x, Set.mem_univ _⟩
        have hDs := congrArg (fun v ↦ v.val x) (hD s)
        rw [hBvalue]
        change _ = β x ((D s).val.val x)
        rw [hDs]
        change _ = β x (c x (s.val.val x) + ((∑ j, (T j).toLinearMap) s.val).val x)
        rw [map_add, ← hcd, ← hAvalue s x]
        change (P.toLinearMap (A s).val).val (e x).val -
          d (e x).val ((A s).val.val (e x).val) = _ at hdeltax
        exact (sub_eq_iff_eq_add.mp hdeltax).trans (add_comm _ _)
      exact heq ▸ hx
    · have hyL : y ∉ L' := fun hx ↦ hy (hL'U hx)
      exact (hPP (A s) y hyL).trans ((B' (D s)).property y hyL).symm
  -- Compare the original raw triples through exactly the smooth fiber maps just used above.
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin H.rank)) H.Fiber
  obtain ⟨eE, heE⟩ := IsSmoothBundleMap.exists_iso_openEmbedding E G U p α hα
  obtain ⟨eF, heF⟩ := IsSmoothBundleMap.exists_iso_openEmbedding F H U p β hβ
  obtain ⟨b, hbcontrol, hbboundary, hbclass⟩ := hu
  have hsymbol (x : O) (ξ : CotangentFiber (n := n) x) (v : E.Fiber x) :
      a'.val (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (eE.linearEquiv x v) =
        eF.linearEquiv x (a.val x ξ v) := by
    rw [heE, heF]
    have hderiv (y : U) :
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          e₀.symm y =
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e.symm y := by
      have hh := mfderiv_comp y
        ((contMDiff_subtype_val (U := (⊤ : Opens O)) (n := ∞)).mdifferentiable (by simp)
          (e₀.symm y)) (e₀.symm.mdifferentiable (by simp) y)
      change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        e.symm y = _ at hh
      rw [mfderiv_openSubtypeVal] at hh
      apply ContinuousLinearMap.ext
      intro w
      exact congrArg (fun A ↦ A w) hh.symm
    have hh := ha'action ⟨x, Set.mem_univ _⟩ ξ v
    have hξ : (cotangentDiffeomorphMap e₀ ⟨⟨x, Set.mem_univ _⟩, ξ⟩).snd =
        (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd := by
      change ξ.comp _ = ξ.comp _
      exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) ↦ ξ.comp A) (hderiv (e x))
    exact (congrArg (fun η ↦ a'.val (e x).val η (α x v)) hξ).symm.trans hh
  have hraw := CompactSupportTriple.compactSupportClass_eq_cotangentOpenEmbedding
    E F G H U e L eE eF a.val a'.val b b' hbcontrol hb'control hbboundary hb'boundary hsymbol
  have hclass : homogeneousSymbolKClass 0 a' ha' = cotangentKZeroOpenEmbedding U e u := by
    rw [← hb'class, hraw, hbclass]
  have hindex : analyticIndexOfComponents μ (cotangentKZeroOpenEmbedding U e u) =
      P.toLinearMap.index := by
    rw [← hclass]
    exact PseudodifferentialOperator.analyticIndexOfComponents_symbolKClassOfHomogeneous
      μ P R a' hPclass hPe
  exact ⟨{ source := G
           target := H
           measure := μ
           positive := hμ
           sourceMetric := g
           targetMetric := l
           operator := P
           elliptic := hPe
           sourceEquiv := A
           targetEquiv := B'
           source_pairing := hApair
           target_pairing := hBpair
           action := haction
           adjoint_support := hPadj
           kernel_support := hkerP
           adjoint_kernel_support := hkerPadj
           class_eq_index := hindex }⟩

end AtiyahSinger
