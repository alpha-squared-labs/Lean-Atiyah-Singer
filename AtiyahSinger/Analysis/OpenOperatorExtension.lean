/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactBaseQuantization
public import AtiyahSinger.Analysis.OpenPieceExtension
public import AtiyahSinger.Analysis.PseudodifferentialSpace
public import AtiyahSinger.Analysis.SectionOperatorSupport
public import AtiyahSinger.Analysis.SupportedPseudodifferentialLocalization
public import AtiyahSinger.Geometry.OpenSectionIdentification

/-!
# Exact open extension of supported pseudodifferential actions

Public module ID: M0829.

UL03/P02: transport through a specified open-region diffeomorphism and smooth
fiber equivalences, then extend by zero. The characterization uses the germ of
an actual input near the support. Finite pieces admit a noncompact source base;
the existing global PDO carrier still requires a compact source and target.
Coordinate/frame covariance and the smooth remainder must all be transported.
Sources: SG III.3.8, 3.11, 3.15 and III.13.4, pp.248--249. These explicit extension
statements are project supplements, not separately numbered source lemmas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Filter
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

/-- A finite family supported in the common region has a unique exact ambient PDO extension. -/
theorem existsUnique_openExtension_of_pieces {m : ℝ} (d : ℕ)
    (T : Fin d → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber m)
    (hT : ∀ j, (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ K) :
    ∃! Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν m,
      HasSectionOperatorSupport L Q.toLinearMap ∧
        ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
          (v : smoothSections (n := n) (r := G.rank) G.Fiber),
          (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
            v.val (e x).val = a x (u.val x.val)) →
          ∀ x : U, (Q.toLinearMap v).val (e x).val =
            b x (((∑ j, (T j).toLinearMap) u).val x.val) := by
  /- First construct the uniquely characterized smooth section action. For each
  original summand refine its actual two cutoffs in target chart neighborhoods,
  carry its native pieces and complete smooth remainder through the same open
  identification, and sum the resulting PDO actions. Uniqueness identifies that
  sum with the first section action; no source compactness is introduced. -/
  classical
  let P := ∑ j, (T j).toLinearMap
  have hpiece (j : Fin d) : HasSectionOperatorSupport K (T j).toLinearMap :=
    (T j).hasSectionOperatorSupport E F K hK (hT j)
  have hP : HasSectionOperatorSupport K P := by
    constructor
    · intro u
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hout
      apply hx
      simp only [P, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro j _
      by_contra hne
      exact hout ((hpiece j).1 u (subset_closure hne))
    · intro u hu
      simp only [P, LinearMap.sum_apply, fun j ↦ (hpiece j).2 u hu,
        Finset.sum_const_zero]
  obtain ⟨R, hR, hUnique⟩ := existsUnique_supported_openExtension E F G H U V e
    K L hK hL hKU hLV hKL a ha b hb P hP
  have hRpdo : IsPseudodifferentialOperator G.Fiber H.Fiber ν m R := by
    by_cases hU : Nonempty U
    · have hV : Nonempty V := hU.map e
      -- A source density is chosen internally solely to write the compact error kernels.
      let : MeasurableSpace M := borel M
      let : BorelSpace M := ⟨rfl⟩
      obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
      have hparts (j : Fin d) := existsUnique_supported_openExtension E F G H U V e
        K L hK hL hKU hLV hKL a ha b hb (T j).toLinearMap (hpiece j)
      choose Rj hRj hUj using hparts
      have hRjPdo (j : Fin d) : IsPseudodifferentialOperator G.Fiber H.Fiber ν m (Rj j) :=
        isPseudodifferentialOperator_openExtension_piece E F G H U V e K L hK hKU hLV
          a ha b hb μ ν (T j) (hT j) (Rj j) (hRj j).1 (hRj j).2 hU hV
      have hsum : (∑ j, Rj j) = R := by
        apply hUnique
        constructor
        · constructor
          · intro v
            apply closure_minimal _ hL.isClosed
            intro y hy
            by_contra hout
            apply hy
            simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
            apply Finset.sum_eq_zero
            intro j _
            by_contra hne
            exact hout ((hRj j).1.1 v (subset_closure hne))
          · intro v hv
            simp only [LinearMap.sum_apply, fun j ↦ (hRj j).1.2 v hv,
              Finset.sum_const_zero]
        · intro u v huv x
          simp only [P, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
          simp_rw [fun j ↦ (hRj j).2 u v huv x]
          exact (map_sum (b x) _ _).symm
      rw [← hsum]
      exact (pseudodifferentialSpace G.Fiber H.Fiber ν m).sum_mem
        (fun j _ ↦ hRjPdo j)
    · -- If the common region is empty, target support forces the entire action to be zero.
      have hRzero : R = 0 := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        funext y
        change (R v).val y = 0
        by_contra hne
        have hy : y ∈ V := hLV (hR.1.1 v (subset_closure hne))
        exact hU ⟨e.symm ⟨y, hy⟩⟩
      rw [hRzero]
      exact isPseudodifferentialOperator_zero G.Fiber H.Fiber ν m
  refine ⟨⟨R, hRpdo⟩, hR, ?_⟩
  intro Q hQ
  cases Q with
  | mk Q hQpdo =>
    have h := hUnique Q hQ
    cases h
    rfl

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hC hB hμ

/-- A genuinely supported global PDO has a unique exact extension across the open identification. -/
theorem PseudodifferentialOperator.existsUnique_openExtension {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ m) (hP : HasSectionOperatorSupport K P.toLinearMap) :
    ∃! Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber ν m,
      HasSectionOperatorSupport L Q.toLinearMap ∧
        ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
          (v : smoothSections (n := n) (r := G.rank) G.Fiber),
          (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
            v.val (e x).val = a x (u.val x.val)) →
          ∀ x : U, (Q.toLinearMap v).val (e x).val = b x ((P.toLinearMap u).val x.val) := by
  classical
  -- Fix the supported section action before identifying its finite PDO representation.
  obtain ⟨Q₀, hQ₀, hunique⟩ := existsUnique_supported_openExtension
    E F G H U V e K L hK hL hKU hLV hKL a ha b hb P.toLinearMap hP
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
  have hmap : Q₀ = Q₁.toLinearMap + R := by
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
      have hmain := hQ₀.2 (Tin v) v hsmall x
      have hpieces := hQ₁.2 (Tin v) v (hmatch v) x
      have hkernel := hRformula (Tin v) v hpoint x
      have hsum : (Q₀ v).val (e x).val =
          (Q₁.toLinearMap v).val (e x).val + (R v).val (e x).val := by
        rw [hmain, hpieces, hkernel, hdecomp]
        change b x (((∑ j, (T j).toLinearMap) (Tin v)).val x.val +
          S.apply μ (Tin v) x.val) = _
        exact map_add (b x) _ _
      have hsum' : (Q₀ v).val (e x).val = ((Q₁.toLinearMap + R) v).val (e x).val := hsum
      exact (congrArg (fun z ↦ (Q₀ v).val z = ((Q₁.toLinearMap + R) v).val z) hex).mp hsum'
    · have hzero₀ : (Q₀ v).val y = 0 := by
        by_contra hn
        exact hy (hLV (hQ₀.1.1 v (subset_closure hn)))
      have hzero₁ : (Q₁.toLinearMap v).val y = 0 := by
        by_contra hn
        exact hy (hD'V (hQ₁.1.1 v (subset_closure hn)))
      change (Q₀ v).val y = (Q₁.toLinearMap v).val y + (R v).val y
      rw [hzero₀, hzero₁, hRzero v y hy, add_zero]
  have hPDO : IsPseudodifferentialOperator G.Fiber H.Fiber ν m Q₀ := by
    rw [hmap]
    exact Q₁.isPseudodifferentialOperator.add m _ _ (hR.isPseudodifferentialOperator m R)
  refine ⟨⟨Q₀, hPDO⟩, hQ₀, ?_⟩
  intro Q hQ
  have hQmap := hunique Q.toLinearMap hQ
  cases Q with
  | mk Q hQpdo =>
    dsimp only at hQmap
    subst Q
    rfl

end AtiyahSinger
