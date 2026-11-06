/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalComposition
public import AtiyahSinger.Analysis.OpenExtensionPrincipal
public import AtiyahSinger.Analysis.OpenKernelDensity
public import AtiyahSinger.Analysis.SupportedPseudodifferentialLocalization

/-!
# Corresponding symbols for a supported global open extension

Public module ID: M0822.

A compact-source operator is localized with one finite family and one genuine
smooth kernel. Their exact extensions recover the specified target action.
The finite family supplies corresponding source and target symbol witnesses;
only the actual smoothing remainder is discarded on taking principal classes.
The auxiliary control is allowed to grow inside the common open region, while
the support of the specified operator itself remains the original one.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open Bundle MeasureTheory TopologicalSpace Filter Set
open scoped Manifold ContDiff Topology
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
  (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
  (hKU : K ⊆ (U : Set M)) (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))
  [hC' : CompactSpace N] [MeasurableSpace N] [hB' : BorelSpace N]
  (ν : Measure N) [hν : IsSmoothPositiveMeasure (n := n) ν]

include hM hN hT hT' hSC hSC' hC' hB' hν hK hL hKU hLV hKL ha hb

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hC hB hμ

omit hL in
set_option backward.isDefEq.respectTransparency false in
/-- A supported operator and its exact open extension have corresponding full-symbol witnesses. -/
theorem exists_principalSymbols_openExtension {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ m) (hP : HasSectionOperatorSupport K P.toLinearMap)
    (Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν m) (hQs : HasSectionOperatorSupport L Q.toLinearMap)
    (hQ : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (Q.toLinearMap v).val (e x).val = b x ((P.toLinearMap u).val x.val)) :
    ∃ (p : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m)
      (p' : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m)
      (C' : Set N), IsCompact C' ∧ L ⊆ C' ∧ C' ⊆ (V : Set N) ∧
      P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m p ∧
      Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber m p' ∧
      (∀ (x : U) η (v : E.Fiber x.val), p'.val (e x).val η (a x v) =
        b x (p.val x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) ∧
      ∀ y, y ∉ C' → ∀ η, p'.val y η = 0 := by
  classical
  -- Localize the actual source representation inside U and retain its genuine kernel.
  obtain ⟨C, hC, hCU, d, T, S, hT, hS, hdecomp⟩ :=
    P.exists_supported_representation K U hK hKU hP
  let D : Set M := K ∪ C
  have hD : IsCompact D := hK.union hC
  have hDU : D ⊆ (U : Set M) := Set.union_subset hKU hCU
  let D' : Set N := Set.range (fun x : D ↦ (e ⟨x.val, hDU x.property⟩).val)
  have hD' : IsCompact D' := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp hD
    apply isCompact_range
    exact continuous_subtype_val.comp (e.continuous.comp
      (continuous_subtype_val.subtype_mk (fun x : D ↦ hDU x.property)))
  have hD'V : D' ⊆ (V : Set N) := by
    rintro y ⟨x, rfl⟩
    exact (e ⟨x.val, hDU x.property⟩).property
  have hDD' : e ⁻¹' ((Subtype.val : V → N) ⁻¹' D') =
      (Subtype.val : U → M) ⁻¹' D := by
    ext x
    change (e x).val ∈ D' ↔ x.val ∈ D
    constructor
    · rintro ⟨y, hy⟩
      have heq : e ⟨y.val, hDU y.property⟩ = e x := Subtype.ext hy
      have hyx := congrArg Subtype.val (e.injective heq)
      exact hyx ▸ y.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, rfl⟩
  -- Transport the same localized finite family and its actual integral remainder.
  obtain ⟨Q₁, hQ₁, _⟩ := existsUnique_openExtension_of_pieces
    E F G H U V e D D' hD hD' hDU hD'V hDD' a ha b hb ν d T
      (fun j ↦ (hT j).trans Set.subset_union_right)
  obtain ⟨R, hR, hRzero, hRformula⟩ :=
    S.exists_openIntegralTransport E F G H U V e a ha b hb μ ν C hC hCU hS
  -- One source realization matches every target input near both K and the localized support C.
  obtain ⟨χ, hχ, Tin, _, _, hχone, hTin⟩ :=
    exists_openSectionGermPullback E G U V e D hD hDU a ha
  have hχUone : ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' D), χ x.val = 1 := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    exact (continuous_subtype_val.tendsto x).eventually
      (eventually_nhdsSet_iff_forall.mp hχone x.val hx)
  have hmatch (v : smoothSections (n := n) (r := G.rank) G.Fiber) :
      ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' D),
        v.val (e x).val = a x ((Tin v).val x.val) := by
    filter_upwards [hχUone] with x hx
    rw [hTin, hx, Complex.ofReal_one, one_smul]
    exact ((a x).apply_symm_apply _).symm
  have hmap : Q.toLinearMap = Q₁.toLinearMap + R := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext y
    by_cases hy : y ∈ V
    · let x : U := e.symm ⟨y, hy⟩
      have hex : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
      have hsmall : ∀ᶠ z : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
          v.val (e z).val = a z ((Tin v).val z.val) :=
        (hmatch v).filter_mono (nhdsSet_mono (Set.preimage_mono Set.subset_union_left))
      have hpoint : ∀ z : U, z.val ∈ C →
          v.val (e z).val = a z ((Tin v).val z.val) :=
        fun z hz ↦ (hmatch v).self_of_nhdsSet z (Or.inr hz)
      have hmain := hQ (Tin v) v hsmall x
      have hpieces := hQ₁.2 (Tin v) v (hmatch v) x
      have hkernel := hRformula (Tin v) v hpoint x
      have hsum : (Q.toLinearMap v).val (e x).val =
          (Q₁.toLinearMap v).val (e x).val + (R v).val (e x).val := by
        rw [hmain, hpieces, hkernel, hdecomp]
        change b x (((∑ j, (T j).toLinearMap) (Tin v)).val x.val +
          S.apply μ (Tin v) x.val) = _
        exact map_add (b x) _ _
      have hsum' : (Q.toLinearMap v).val (e x).val = ((Q₁.toLinearMap + R) v).val (e x).val := hsum
      exact (congrArg
        (fun z ↦ (Q.toLinearMap v).val z = ((Q₁.toLinearMap + R) v).val z) hex).mp hsum'
    · have hzero₀ : (Q.toLinearMap v).val y = 0 := by
        by_contra hn
        exact hy (hLV (hQs.1 v (subset_closure hn)))
      have hzero₁ : (Q₁.toLinearMap v).val y = 0 := by
        by_contra hn
        exact hy (hD'V (hQ₁.1.1 v (subset_closure hn)))
      change (Q.toLinearMap v).val y = (Q₁.toLinearMap v).val y + (R v).val y
      rw [hzero₀, hzero₁, hRzero v y hy, add_zero]
  -- The original source representation computes one particular principal witness.
  let p : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m :=
    ∑ j, (T j).globalSymbol
  have hpzero (x : M) (hx : x ∉ D) (ξ) : p.val x ξ = 0 := by
    simp only [p, Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply (T j).globalSymbolFunction_eq_zero
    rintro ⟨z, hz, rfl⟩
    exact hx (Or.inr (hT j ⟨z, Or.inl hz.2, rfl⟩))
  obtain ⟨p', hp'transport, hp'zero⟩ := exists_supported_openGlobalSymbol
    E F G H U V e D D' hD' hD'V hDD' a ha b hb p hpzero
  have hsource : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m p := by
    apply P.principalSymbol_eq_of_representation d T
    refine ⟨S, ?_⟩
    rw [hdecomp]
    abel
  -- Compute the finite target class, and remove only the same actual smoothing remainder.
  have hfinite := principalSymbol_openExtension_of_pieces E F G H U V e
    D D' hD hD' hDU hD'V hDD' a ha b hb ν d T
      (fun j ↦ (hT j).trans Set.subset_union_right) Q₁ hQ₁.1 hQ₁.2
      p' hp'transport hp'zero
  have htarget : Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber m p' := by
    apply (Q.principalSymbol_eq_of_isSmoothingOperator_sub Q₁ ?_).trans hfinite
    rw [hmap]
    simpa only [add_sub_cancel_left] using hR
  have hLD' : L ⊆ D' := by
    intro y hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hLV hy⟩
    have hxy : (e x).val = y := congrArg Subtype.val hx
    have hxK : x.val ∈ K := by
      apply (Set.ext_iff.mp hKL x).mp
      change (e x).val ∈ L
      rwa [hxy]
    exact ⟨⟨x.val, Or.inl hxK⟩, hxy⟩
  exact ⟨p, p', D', hD', hLD', hD'V, hsource, htarget, hp'transport, hp'zero⟩

end AtiyahSinger
