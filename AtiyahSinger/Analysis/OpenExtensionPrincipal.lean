/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenOperatorExtension
public import AtiyahSinger.Analysis.OpenPiecePrincipal
public import AtiyahSinger.Analysis.OpenPrincipalSymbol
public import AtiyahSinger.Analysis.PseudodifferentialSpace

/-!
# The principal class of an exact finite open extension

Public module ID: M0820.

Extend each specified native piece with the same actual action and a transported
full-symbol witness. One common realization of input germs identifies their sum
with the original exact extension. Pointwise fiber transport then identifies the
sum of symbol witnesses, and linearity computes the original principal class.
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

set_option backward.isDefEq.respectTransparency false in
/-- A finite open extension retains the principal class of its specified transported symbol. -/
theorem principalSymbol_openExtension_of_pieces {m : ℝ} (d : ℕ)
    (T : Fin d → PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber m)
    (hT : ∀ j, (T j).chart.symm ''
      (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ K)
    (Q : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber ν m)
    (hQs : HasSectionOperatorSupport L Q.toLinearMap)
    (hQ : ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
      (v : smoothSections (n := n) (r := G.rank) G.Fiber),
      (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x (u.val x.val)) →
      ∀ x : U, (Q.toLinearMap v).val (e x).val =
        b x (((∑ j, (T j).toLinearMap) u).val x.val))
    (p : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m)
    (hp : ∀ (x : U) η (v : E.Fiber x.val),
      p.val (e x).val η (a x v) = b x
        ((∑ j, (T j).globalSymbol).val x.val
          (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v))
    (hpzero : ∀ y, y ∉ L → ∀ η, p.val y η = 0) :
    Q.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber m p := by
  classical
  -- Each original summand is transported with its exact action and the same symbol witness.
  have hpieces (j : Fin d) :
      ∃ Qj : PseudodifferentialOperator (n := n) (r := G.rank) (q := H.rank)
          G.Fiber H.Fiber ν m,
        HasSectionOperatorSupport L Qj.toLinearMap ∧
        (∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber)
          (v : smoothSections (n := n) (r := G.rank) G.Fiber),
          (∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
            v.val (e x).val = a x (u.val x.val)) →
          ∀ x : U, (Qj.toLinearMap v).val (e x).val =
            b x (((T j).toLinearMap u).val x.val)) ∧
        ∃ pj : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m,
          Qj.principalSymbol = globalPrincipalSymbolClass G.Fiber H.Fiber m pj ∧
          (∀ (x : U) η (v : E.Fiber x.val),
            pj.val (e x).val η (a x v) = b x
              ((T j).globalSymbol.val x.val
                (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                  𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) ∧
          (∀ y, y ∉ L → ∀ η, pj.val y η = 0) := by
    by_cases hU : Nonempty U
    · have hV : Nonempty V := hU.map e
      let : MeasurableSpace M := borel M
      let : BorelSpace M := ⟨rfl⟩
      obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
      have hsupport := (T j).hasSectionOperatorSupport E F K hK (hT j)
      obtain ⟨R, hRs, _⟩ := existsUnique_supported_openExtension
        E F G H U V e K L hK hL hKU hLV hKL a ha b hb (T j).toLinearMap hsupport
      have hpzero (x : M) (hx : x ∉ K) (ξ) : (T j).globalSymbol.val x ξ = 0 := by
        apply (T j).globalSymbolFunction_eq_zero
        intro hin
        apply hx
        apply hT j
        rcases hin with ⟨z, hz, rfl⟩
        exact ⟨z, Or.inl hz.2, rfl⟩
      obtain ⟨pj, hpjtransport, hpjzero⟩ := exists_supported_openGlobalSymbol
        E F G H U V e K L hL hLV hKL a ha b hb (T j).globalSymbol hpzero
      obtain ⟨Qj, hmap, hclass⟩ := exists_openExtension_piece_principalSymbol
        E F G H U V e K L hK hKU hLV a ha b hb μ ν
          (T j) (hT j) R hRs.1 hRs.2 pj hpjzero hpjtransport hU hV
      refine ⟨Qj, ?_, ?_, pj, hclass, hpjtransport, hpjzero⟩
      · rw [hmap]
        exact hRs.1
      · simpa only [hmap] using hRs.2
    · let Qj := pseudodifferentialOperatorOfSpace
        (0 : pseudodifferentialSpace (n := n) (r := G.rank) (q := H.rank)
          G.Fiber H.Fiber ν m)
      refine ⟨Qj, ?_, ?_, 0, ?_, ?_, ?_⟩
      · constructor
        · intro v
          change closure {y | (0 : H.Fiber y) ≠ 0} ⊆ L
          simp
        · intro v _hv
          rfl
      · intro u v _h x
        exact (hU ⟨x⟩).elim
      · change principalSymbolLinearMap G.Fiber H.Fiber ν m 0 =
          globalPrincipalSymbolClass G.Fiber H.Fiber m 0
        rw [map_zero, map_zero]
      · intro x
        exact (hU ⟨x⟩).elim
      · intro y _hy η
        rfl
  choose Qj hQjs hQj pj hpj hpjtransport hpjzero using hpieces
  -- One source realization of each target input identifies the sum as the original Q.
  obtain ⟨χ, hχ, Tin, _, _, hχone, hTin⟩ :=
    exists_openSectionGermPullback E G U V e K hK hKU a ha
  have hmatch (v : smoothSections (n := n) (r := G.rank) G.Fiber) :
      ∀ᶠ x : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' K),
        v.val (e x).val = a x ((Tin v).val x.val) := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    have hn := (continuous_subtype_val.tendsto x).eventually
      (eventually_nhdsSet_iff_forall.mp hχone x.val hx)
    filter_upwards [hn] with y hy
    rw [hTin, hy, Complex.ofReal_one, one_smul]
    exact ((a y).apply_symm_apply _).symm
  have hmaps : Q.toSpace = ∑ j, (Qj j).toSpace := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change Q.toLinearMap = ∑ j, (Qj j).toLinearMap
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext y
    by_cases hyV : y ∈ V
    · obtain ⟨x, hx⟩ := e.surjective ⟨y, hyV⟩
      have hxy : (e x).val = y := congrArg Subtype.val hx
      subst y
      change (Q.toLinearMap v).val (e x).val =
        ((∑ j, (Qj j).toLinearMap) v).val (e x).val
      rw [hQ (Tin v) v (hmatch v) x]
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      simp_rw [fun j ↦ hQj j (Tin v) v (hmatch v) x]
      exact map_sum (b x) _ _
    · have hyL : y ∉ L := fun h ↦ hyV (hLV h)
      have hzero : (Q.toLinearMap v).val y = 0 := by
        by_contra hn
        exact hyL (hQs.1 v (subset_closure hn))
      change (Q.toLinearMap v).val y = ((∑ j, (Qj j).toLinearMap) v).val y
      rw [hzero]
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      symm
      apply Finset.sum_eq_zero
      intro j _
      by_contra hn
      exact hyL ((hQjs j).1 v (subset_closure hn))
  -- The same pointwise transport and exterior zero determine the sum of symbol witnesses.
  have hsymbols : (∑ j, pj j) = p := by
    apply Subtype.ext
    funext y η
    apply ContinuousLinearMap.ext
    intro w
    by_cases hyV : y ∈ V
    · obtain ⟨x, hx⟩ := e.surjective ⟨y, hyV⟩
      have hxy : (e x).val = y := congrArg Subtype.val hx
      subst y
      obtain ⟨v, hv⟩ := (a x).surjective w
      have hpoint (j : Fin d) := hpjtransport j x η v
      have hmain := hp x η v
      rw [hv] at hpoint hmain
      simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply]
      simp_rw [hpoint]
      rw [hmain]
      simp only [Submodule.coe_sum, Finset.sum_apply, _root_.sum_apply, map_sum]
    · have hyL : y ∉ L := fun h ↦ hyV (hLV h)
      simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply]
      simp only [fun j ↦ hpjzero j y hyL η, hpzero y hyL η, zero_apply,
        Finset.sum_const_zero]
  -- Linearity now computes the class of this actual operator, without choosing another action.
  change principalSymbolLinearMap G.Fiber H.Fiber ν m Q.toSpace = _
  rw [hmaps, map_sum]
  change (∑ j, (Qj j).principalSymbol) = _
  simp_rw [hpj]
  rw [← map_sum, hsymbols]

end AtiyahSinger
