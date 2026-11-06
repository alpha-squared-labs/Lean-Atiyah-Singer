/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianFiniteResolvent
public import AtiyahSinger.Analysis.LocalFiniteResolvent

/-!
# Exact finite resolvent identities on original smooth sections

Public module ID: M0383.

The fixed supported symbols are realized in their original frames. Their compact
support and the cutoff plateau preserve the entire germ, so differentiating the
actual extended sections introduces no unaccounted cutoff commutator. The explicit
joint remainder is retained, with its already proved order and its actual quantizer.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap Topology

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

namespace FiniteResolventPatch

variable {L : DifferentialOperator (n := n) (r := r) (q := r) E E 2}

/-- Each specified patch satisfies the exact finite resolvent identity on original fibers. -/
theorem apply_sum_term (P : FiniteResolventPatch L) (N : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (u : smoothSections (n := n) (r := r) E) (x : M) :
    (L.toLinearMap (∑ j ∈ Finset.range N, P.term j τ hτ u)).val x +
        ((1 + τ : ℝ) : ℂ) • (∑ j ∈ Finset.range N, P.term j τ hτ u).val x =
      (P.weight x : ℂ) • u.val x + (P.remainder N τ hτ u).val x := by
  classical
  let := P.cutoff.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin (n + 1))
  let split : Y ≃L[ℝ] X × EuclideanSpace ℝ (Fin 1) := EuclideanSpace.finAddEquivProd
  let D := P.chart '' P.domain
  let W := (fun z : Y ↦ (split z).1) ⁻¹' D
  let f : SymbolFunction (n + 1) r r := finiteResolventSourceSymbol P.coordinateWeight
  let v := ∑ j ∈ Finset.range N, P.term j τ hτ u
  let u₀ := P.cutoff.localize P.chart_mem_atlas u
  let A : SymbolFunction n r r :=
    jointFrequencySymbolSlice (∑ j ∈ Finset.range N, P.symbol j) τ
  have hD : IsOpen D := P.chart.isOpen_image_of_subset_source P.isOpen_domain
    (fun y hy ↦ (P.hasCoordinateExpression.1 hy).1.1)
  have hW : IsOpen W := hD.preimage (continuous_fst.comp split.continuous)
  obtain ⟨O, hO, hχO, hβO⟩ := P.cutoff_eq_one
  -- The entire joint source, hence every recursive term, has horizontal support in χ.
  have hfsupport : tsupport f ⊆ (fun z : Y ↦ (split z).1) ⁻¹'
      tsupport P.coordinateWeight := by
    apply closure_minimal ?_
      ((isClosed_tsupport P.coordinateWeight).preimage (continuous_fst.comp split.continuous))
    intro z hz
    by_contra hzero
    have hχzero : P.coordinateWeight (EuclideanSpace.finAddEquivProd z).1 = 0 :=
      image_eq_zero_of_notMem_tsupport hzero
    apply hz
    funext ζ
    simp only [f, finiteResolventSourceSymbol, hχzero, zero_mul,
      Complex.ofReal_zero, zero_smul, Pi.zero_apply]
  have hslicerow (a : SymbolFunction (n + 1) r r) (hs : tsupport a ⊆ tsupport f)
      (z : X) (hz : z ∉ tsupport P.coordinateWeight) :
      jointFrequencySymbolSlice a τ z = 0 := by
    have hzero : a (split.symm (z, 0)) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ha ↦ hz (by
        simpa only [Set.mem_preimage, split.apply_symm_apply] using hfsupport (hs ha)))
    funext ξ
    exact congrFun hzero (split.symm (ξ, WithLp.toLp 2 (fun _ : Fin 1 ↦ Real.sqrt τ)))
  -- Horizontal differentiation preserves this same support for the actual finite remainder.
  have hremSupport : tsupport (P.remainderSymbol N) ⊆ tsupport f := by
    apply closure_minimal ?_ (isClosed_tsupport f)
    intro z hz
    by_contra hout
    have hzero (j : ℕ) : P.symbol j z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hout (P.support_symbol j h))
    have hEzero (j : ℕ) (ζ : Y) :
        P.coordinate.parameterCorrectionSymbol (P.symbol j) z ζ = 0 := by
      have hnear := notMem_tsupport_iff_eventuallyEq.mp
        (show z ∉ tsupport (P.symbol j) from fun h ↦ hout (P.support_symbol j h))
      have hjet : (fun y ↦ P.symbol j y ζ) =ᶠ[nhds z] (fun _ ↦ 0) := by
        filter_upwards [hnear] with y hy
        exact congrFun hy ζ
      have hder (k : ℕ) : iteratedFDeriv ℝ k (fun y ↦ P.symbol j y ζ) z = 0 := by
        rw [(hjet.iteratedFDeriv ℝ k).eq_of_nhds]
        simpa only [Pi.zero_apply] using
          congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (n := k)) z
      simp [CoordinateDifferentialOperator.parameterCorrectionSymbol, symbolComp,
        hzero j, compositionExpansionTerm, hder]
    apply hz
    funext ζ
    simp [remainderSymbol, symbolComp, hzero, hEzero,
      show finiteResolventSourceSymbol (r := r) P.coordinateWeight z = 0 from
        image_eq_zero_of_notMem_tsupport hout]
  -- The actual zero extension and outer plateau are redundant on every supported slice.
  have hrealize (m : ℝ) (hm : m ≤ 0) (a : SymbolFunction (n + 1) r r)
      (ha : IsSymbol W m a) (hs : tsupport a ⊆ tsupport f)
      (y : M) (hy : y ∈ P.domain) :
      (P.cutoff.frame ⟨y, ((P.piece m hm a ha τ hτ).toLinearMap u).val y⟩).2 =
        quantize (jointFrequencySymbolSlice a τ) u₀ (P.chart y) := by
    have hdomain := P.hasCoordinateExpression.1 hy
    have hext : zeroExtendedSymbol D P.cutoff.cutoff (jointFrequencySymbolSlice a τ) =
        jointFrequencySymbolSlice a τ := by
      funext z ξ
      by_cases hz : z ∈ tsupport P.coordinateWeight
      · have hzD : z ∈ D := P.support_coordinateWeight hz
        simp only [zeroExtendedSymbol, ite_eq_left hzD,
          hβO z (hχO hz), Complex.ofReal_one, one_smul]
      · simp [zeroExtendedSymbol, hslicerow a hs z hz]
    have hframe := (P.piece m hm a ha τ hτ).toLinearMap_in_frame u y
      hdomain.1.1 hdomain.1.2
    change (P.cutoff.frame ⟨y, ((P.piece m hm a ha τ hτ).toLinearMap u).val y⟩).2 =
      (P.cutoff.cutoff (P.chart y) : ℂ) •
        quantize (zeroExtendedSymbol D P.cutoff.cutoff (jointFrequencySymbolSlice a τ))
          u₀ (P.chart y) at hframe
    rw [hext] at hframe
    rw [hframe]
    by_cases hyχ : P.chart y ∈ tsupport P.coordinateWeight
    · rw [hβO _ (hχO hyχ), Complex.ofReal_one, one_smul]
    · simp [quantize, hslicerow a hs _ hyχ]
  have htermframe (j : ℕ) (y : M) (hy : y ∈ P.domain) :
      (P.cutoff.frame ⟨y, (P.term j τ hτ u).val y⟩).2 =
        quantize (jointFrequencySymbolSlice (P.symbol j) τ) u₀ (P.chart y) :=
    hrealize (-2 - (j : ℝ))
      (sub_nonpos.mpr ((by norm_num : (-2 : ℝ) ≤ 0).trans (Nat.cast_nonneg j))) _
      (P.isSymbol_symbol j) (P.support_symbol j) y hy
  have hremframe (y : M) (hy : y ∈ P.domain) :
      (P.cutoff.frame ⟨y, (P.remainder N τ hτ u).val y⟩).2 =
        quantize (jointFrequencySymbolSlice (P.remainderSymbol N) τ) u₀ (P.chart y) :=
    hrealize (-(N : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg N)) _
      (P.isSymbol_remainder N) hremSupport y hy
  -- Away from the fixed compact output support, locality gives zero actual differential action.
  let K := P.chart.symm '' tsupport P.cutoff.cutoff
  have hK : IsCompact K := P.cutoff.compact_support.image_of_continuousOn
    (P.chart.continuousOn_symm.mono (fun _ hz ↦ (P.cutoff.support_subset hz).1))
  have hKU : K ⊆ P.domain := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hzy⟩ := P.support_cutoff hz
    rw [← hzy, P.chart.left_inv (P.hasCoordinateExpression.1 hy).1.1]
    exact hy
  have hvzero (y : M) (hy : y ∉ K) : v.val y = 0 := by
    dsimp only [v]
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    exact PseudodifferentialPiece.toLinearMap_eq_zero
      (P.piece (-2 - (j : ℝ))
        (sub_nonpos.mpr ((by norm_num : (-2 : ℝ) ≤ 0).trans (Nat.cast_nonneg j)))
        (P.symbol j) (P.isSymbol_symbol j) τ hτ) u y hy
  by_cases hx : x ∈ P.domain
  · -- On the original coordinate domain, the sum agrees as a full germ with its quantizer.
    have hxs := (P.hasCoordinateExpression.1 hx).1.1
    have hxe := (P.hasCoordinateExpression.1 hx).1.2
    have hxD : P.chart x ∈ D := ⟨x, hx, rfl⟩
    have hslice (j : ℕ) :
        IsSymbol D 0 (jointFrequencySymbolSlice (P.symbol j) τ) := by
      have hj := (exists_uniform_quantizeSobolev_jointFrequencySymbolSlice W hW
        (-2 - (j : ℝ)) 0
        (sub_nonpos.mpr ((by norm_num : (-2 : ℝ) ≤ 0).trans (Nat.cast_nonneg j)))
        (P.symbol j) (P.isSymbol_symbol j)
        D hD (by
          intro z hz
          change (split (split.symm (z, 0))).1 ∈ D
          rw [split.apply_symm_apply]
          exact hz)
        P.cutoff.cutoff P.cutoff.smooth_cutoff P.cutoff.compact_support
        P.support_cutoff).choose τ hτ
      exact hj.mono
        (sub_nonpos.mpr ((by norm_num : (-2 : ℝ) ≤ 0).trans (Nat.cast_nonneg j)))
    have hsumSymbol : A = ∑ j ∈ Finset.range N,
        jointFrequencySymbolSlice (P.symbol j) τ := by
      funext z ξ
      simp only [A, jointFrequencySymbolSlice, Finset.sum_apply]
    have hcoord (z : X) (hz : z ∈ D) :
        sectionInChart E P.chart P.cutoff.frame v.val z = quantize A u₀ z := by
      obtain ⟨y, hy, rfl⟩ := hz
      have hys := (P.hasCoordinateExpression.1 hy).1.1
      have hye := (P.hasCoordinateExpression.1 hy).1.2
      rw [hsumSymbol, quantize_finset_sum hD 0 (Finset.range N) _
        (fun j _ ↦ hslice j) u₀ (P.chart y) ⟨y, hy, rfl⟩]
      have hpair : (⟨P.chart.symm (P.chart y), v.val (P.chart.symm (P.chart y))⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨y, v.val y⟩ :=
        congrArg (fun z ↦ (⟨z, v.val z⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          (P.chart.left_inv hys)
      change (P.cutoff.frame
        ⟨P.chart.symm (P.chart y), v.val (P.chart.symm (P.chart y))⟩).2 = _
      rw [hpair]
      simp only [v, Submodule.coe_sum, Finset.sum_apply]
      change (P.cutoff.frame.linearEquivAt ℂ y hye)
        (∑ j ∈ Finset.range N, (P.term j τ hτ u).val y) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact htermframe j y hy
    have hnear : sectionInChart E P.chart P.cutoff.frame v.val =ᶠ[nhds (P.chart x)]
        quantize A u₀ := by
      filter_upwards [hD.mem_nhds hxD] with z hz
      exact hcoord z hz
    have hLv : (P.cutoff.frame ⟨x, (L.toLinearMap v).val x⟩).2 =
        P.coordinate.apply (quantize A u₀) (P.chart x) := by
      rw [P.hasCoordinateExpression.2 v x hx]
      simp only [CoordinateDifferentialOperator.apply]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro α _
      rw [(hnear.iteratedFDeriv ℝ k.val).eq_of_nhds]
    have hv : (P.cutoff.frame ⟨x, v.val x⟩).2 = quantize A u₀ (P.chart x) := by
      have hpair : (⟨P.chart.symm (P.chart x), v.val (P.chart.symm (P.chart x))⟩ :
          TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, v.val x⟩ :=
        congrArg (fun z ↦ (⟨z, v.val z⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
          (P.chart.left_inv hxs)
      simpa only [sectionInChart, hpair] using hnear.eq_of_nhds
    -- Fourier inversion identifies the original multiplication source without a new operator.
    let Q₀ : CoordinateDifferentialOperator n r r 0 Set.univ :=
      { coefficient := fun _ _ z ↦ (P.coordinateWeight z : ℂ) • ContinuousLinearMap.id ℂ _
        smooth_coefficient := fun _ _ ↦
          ((Complex.ofRealCLM.contDiff.comp P.smooth_coordinateWeight).smul
            contDiff_const).contDiffOn }
    have hfSlice : jointFrequencySymbolSlice f τ = Q₀.totalSymbol := by
      let ρ₀ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 1)) :=
        ⟨1, 2, by norm_num, by norm_num⟩
      have hρ₀ : ρ₀ 0 = 1 := ρ₀.eventuallyEq_one.eq_of_nhds
      have hQ₀ (z ξ : X) : Q₀.totalSymbol z ξ =
          (P.coordinateWeight z : ℂ) • ContinuousLinearMap.id ℂ _ := by
        simp [CoordinateDifferentialOperator.totalSymbol, Q₀]
      funext z ξ
      change (((P.coordinateWeight (split (split.symm (z, 0))).1 *
        ρ₀ (split (split.symm (z, 0))).2 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ _) =
          Q₀.totalSymbol z ξ
      simp only [split.apply_symm_apply, hρ₀, mul_one, hQ₀]
    have hsource : quantize (jointFrequencySymbolSlice f τ) u₀ (P.chart x) =
        (P.weight x : ℂ) • (P.cutoff.frame ⟨x, u.val x⟩).2 := by
      rw [hfSlice, Q₀.quantize_totalSymbol]
      have hq : Q₀.apply u₀ (P.chart x) =
          (P.coordinateWeight (P.chart x) : ℂ) • u₀ (P.chart x) := by
        simp [Q₀, CoordinateDifferentialOperator.apply, iteratedFDeriv_zero_apply]
      rw [hq]
      by_cases hχ : P.coordinateWeight (P.chart x) = 0
      · rw [← P.coordinateWeight_apply x hxs, hχ, Complex.ofReal_zero, zero_smul, zero_smul]
      · have hβ := hβO _ (hχO (subset_tsupport _ hχ))
        have hu₀ : u₀ (P.chart x) = (P.cutoff.frame ⟨x, u.val x⟩).2 := by
          have hpair : (⟨P.chart.symm (P.chart x), u.val (P.chart.symm (P.chart x))⟩ :
              TotalSpace (EuclideanSpace ℂ (Fin r)) E) = ⟨x, u.val x⟩ :=
            congrArg (fun z ↦ (⟨z, u.val z⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E))
              (P.chart.left_inv hxs)
          change P.cutoff.localizedFunction u (P.chart x) = _
          simp only [BundleChartCutoff.localizedFunction,
            ite_eq_left (P.chart.map_source hxs), hβ, Complex.ofReal_one, one_smul,
            sectionInChart, hpair]
        rw [hu₀, P.coordinateWeight_apply x hxs]
    apply (P.cutoff.frame.linearEquivAt ℂ x hxe).injective
    rw [map_add, map_add, map_smul, map_smul]
    change (P.cutoff.frame ⟨x, (L.toLinearMap v).val x⟩).2 +
      ((1 + τ : ℝ) : ℂ) • (P.cutoff.frame ⟨x, v.val x⟩).2 =
      (P.weight x : ℂ) • (P.cutoff.frame ⟨x, u.val x⟩).2 +
        (P.cutoff.frame ⟨x, (P.remainder N τ hτ u).val x⟩).2
    rw [hLv, hv, ← hsource, hremframe x hx]
    simpa only [A, remainderSymbol, f, Complex.coe_smul] using
      P.coordinate.apply_quantize_finite_parameter_symbol_sequence hD f P.isSymbol_source
        P.symbol P.isSymbol_symbol N τ hτ u₀ (P.chart x) hxD
  · have hxK : x ∉ K := fun h ↦ hx (hKU h)
    have hnear : ∀ᶠ y in nhds x, v.val y = (0 : smoothSections (n := n) (r := r) E).val y := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      exact hvzero y hy
    have hLv := L.apply_eq_of_eventually_eq v 0 x hnear
    have hR : (P.remainder N τ hτ u).val x = 0 :=
      PseudodifferentialPiece.toLinearMap_eq_zero
        (P.piece (-(N : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg N))
          (P.remainderSymbol N) (P.isSymbol_remainder N) τ hτ) u x hxK
    change (L.toLinearMap v).val x + ((1 + τ : ℝ) : ℂ) • v.val x = _
    rw [hLv, map_zero, hvzero x hxK, hR, P.weight_eq_zero x hx]
    simp

/-- A partition of the fixed patches gives the exact global finite resolvent identity. -/
theorem apply_sum_patches {k : ℕ} (P : Fin k → FiniteResolventPatch L)
    (hpartition : ∀ x : M, ∑ i, (P i).weight x = 1)
    (N : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (u : smoothSections (n := n) (r := r) E) :
    L.toLinearMap (∑ i, ∑ j ∈ Finset.range N, (P i).term j τ hτ u) +
        ((1 + τ : ℝ) : ℂ) • (∑ i, ∑ j ∈ Finset.range N, (P i).term j τ hτ u) =
      u + ∑ i, (P i).remainder N τ hτ u := by
  classical
  have hL : L.toLinearMap (∑ i, ∑ j ∈ Finset.range N, (P i).term j τ hτ u) =
      ∑ i, L.toLinearMap (∑ j ∈ Finset.range N, (P i).term j τ hτ u) :=
    map_sum L.toLinearMap _ _
  rw [hL]
  apply Subtype.ext
  funext x
  calc
    _ = ∑ i, ((L.toLinearMap (∑ j ∈ Finset.range N, (P i).term j τ hτ u)).val x +
        ((1 + τ : ℝ) : ℂ) • (∑ j ∈ Finset.range N, (P i).term j τ hτ u).val x) := by
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
        Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finset.smul_sum,
        Finset.sum_add_distrib]
    _ = ∑ i, (((P i).weight x : ℂ) • u.val x + ((P i).remainder N τ hτ u).val x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (P i).apply_sum_term N τ hτ u x
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum,
        hpartition x, Complex.ofReal_one, one_smul, Submodule.coe_add,
        Submodule.coe_sum, Pi.add_apply, Finset.sum_apply]

end FiniteResolventPatch

end AtiyahSinger
