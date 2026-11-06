/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactBaseQuantization
public import AtiyahSinger.Analysis.DifferentialPrincipalSymbol
public import AtiyahSinger.Analysis.GlobalHomogeneousSymbol
public import AtiyahSinger.Analysis.PseudodifferentialSpace
public import AtiyahSinger.Analysis.SectionCutoff

/-!
# Localization relative to an exterior zero-order bundle map

Public module ID: M0605.

This is the compact-ambient part of the construction used in SG III.13.4,
pp.248--249. The original homogeneous principal data agree outside K with a
zero-order differential operator B. A prescribed neighborhood supplies a real
cutoff, and the actual map B + χ(P-B)χ preserves the principal class.

The kernel theorem treats both the operator and its specified metric adjoint.
Exterior fiberwise invertibility is sufficient; B need not be unitary or globally
invertible. No ellipticity is needed just to localize kernel sections. This
module does not construct noncompact relative representatives, extensions to
different compact environments, or a distributional Schwartz-kernel model.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hE hF

variable [hC : CompactSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hC hB hμ

omit hC [MeasurableSpace M] hB hμ in
/-- An order-zero differential operator acts by its original principal fiber map. -/
private theorem zeroOrder_apply_eq_principalSymbol
    (D : DifferentialOperator (n := n) (r := r) (q := q) E F 0)
    (u : smoothSections (n := n) (r := r) E) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    (D.toLinearMap u).val x = D.principalSymbol x ξ (u.val x) := by
  classical
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ _
  have hc : x ∈ c.source := mem_chart_source _ _
  obtain ⟨U, hU, hxU, Q, hQ⟩ := D.isDifferentialOperator c (chart_mem_atlas _ x)
    e f x ⟨⟨hc, he⟩, hf⟩
  -- The same local expression computes both the operator and the degree-zero symbol.
  have hact := hQ.2 u x hxU
  have hsym := LinearMap.congr_fun
    (D.hasPrincipalSymbol c (chart_mem_atlas _ x) e f U hU Q hQ x hxU ξ) (u.val x)
  apply (f.linearEquivAt ℂ x hf).injective
  have hu : sectionInChart E c e u.val (c x) = (e ⟨x, u.val x⟩).2 := by
    unfold sectionInChart
    rw [c.left_inv hc]
  have hcoordinate : Q.apply (sectionInChart E c e u.val) (c x) =
      Q.principalSymbol (c x) (covectorInChart c x ξ) ((e ⟨x, u.val x⟩).2) := by
    simp [CoordinateDifferentialOperator.apply, CoordinateDifferentialOperator.principalSymbol, hu]
  change (f ⟨x, (D.toLinearMap u).val x⟩).2 =
    (f ⟨x, D.principalSymbol x ξ (u.val x)⟩).2
  apply hact.trans (hcoordinate.trans ?_)
  simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    f.coe_linearMapAt_of_mem hf, e.coe_linearMapAt_of_mem he] using hsym.symm

namespace PseudodifferentialOperator

set_option backward.isDefEq.respectTransparency false in
/-- Localize a zero-order representative relative to B while keeping its actual principal class. -/
theorem exists_localized_representative
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (B : DifferentialOperator (n := n) (r := r) (q := q) E F 0)
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F 0 a)
    (hprincipal : P.principalSymbol =
      globalPrincipalSymbolClass E F 0 (A.regularizedSymbol 0 a hs hh))
    (K : Set M) (hK : IsCompact K)
    (hexterior : ∀ x, x ∉ K → ∀ ξ, ξ ≠ 0 → a x ξ = B.principalSymbolFunction x ξ)
    (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ),
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ x ∈ K, χ x = 1) ∧
      ∃ Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0,
        Q.toLinearMap = B.toLinearMap +
          twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ ∧
        Q.principalSymbol = P.principalSymbol := by
  /- Quantize the compactly based homogeneous correction by one finite family.
  Choose a cutoff which is one on both actual supports of that family. Its sum is
  therefore fixed by the sandwich. The original operator differs from this reference
  by one lower order, and the same sandwich preserves that lower order. -/
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let bB : globalSymbolSpace (n := n) (r := r) (q := q) E F 0 :=
    ⟨B.principalSymbolFunction, by
      change IsGlobalSymbol E F 0 B.principalSymbolFunction
      simpa only [Nat.cast_zero] using B.isGlobalSymbol_principalSymbolFunction⟩
  let d : GlobalSymbolFunction (n := n) E F := a - B.principalSymbolFunction
  have hds : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F d := by
    intro c hc e f _ _
    have hb := (bB.property c hc e f).1.mono
      (Set.prod_mono subset_rfl
        (Set.subset_univ {ξ : EuclideanSpace ℝ (Fin n) | ξ ≠ 0}))
    convert (hs c hc e f).sub hb using 1
    ext z v
    simp [d, Function.uncurry, globalSymbolInChart, bB]
  have hBhom (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
      (t : ℝ) : B.principalSymbolFunction x (t • ξ) = B.principalSymbolFunction x ξ := by
    ext v
    change B.principalSymbol x (t • ξ) v = B.principalSymbol x ξ v
    have h := LinearMap.congr_fun (B.principalSymbol_smul x ξ t) v
    simpa only [pow_zero, one_smul] using h
  have hdh : IsHomogeneousGlobalSymbol E F 0 d := by
    intro x ξ hξ t ht
    have ha := hh x ξ hξ t ht
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul] at ha ⊢
    change a x (t • ξ) - B.principalSymbolFunction x (t • ξ) =
      a x ξ - B.principalSymbolFunction x ξ
    rw [ha, hBhom]
  let b := A.regularizedSymbol 0 d hds hdh
  have hbzero : ∀ x, x ∉ K → ∀ ξ, b.val x ξ = 0 := by
    intro x hx ξ
    by_cases hξ : ξ = 0
    · subst ξ
      exact A.regularizedSymbolFunction_zero_covector d x
    · change A.regularizedSymbolFunction d x ξ = 0
      simp [QuantizationPresentation.regularizedSymbolFunction, d, hexterior x hx ξ hξ]
  obtain ⟨N, L, hLsymbol, C, hCcompact, hCU, hLC⟩ :=
    exists_supported_quantization_pieces b K hK hbzero U hU hKU
  -- The regularized correction plus the original differential symbol has the given class.
  have hclass : globalPrincipalSymbolClass E F 0 (bB + b) =
      globalPrincipalSymbolClass E F 0 (A.regularizedSymbol 0 a hs hh) := by
    apply (globalPrincipalSymbolClass_eq_iff E F 0 _ _).mpr
    intro c hc e f _ _
    let V := symbolChartDomain E F c e f
    let pB := globalSymbolInChart E F bB.val c e f
    let pd := globalSymbolInChart E F b.val c e f
    let pa := globalSymbolInChart E F (A.regularizedSymbol 0 a hs hh).val c e f
    have hcoord : globalSymbolInChart E F
        ((bB + b).val - (A.regularizedSymbol 0 a hs hh).val) c e f = pB + pd - pa := by
      ext z η v
      simp [globalSymbolInChart, pB, pd, pa]
    rw [hcoord]
    have hd : ContDiffOn ℝ ∞ (Function.uncurry (pB + pd - pa)) (V ×ˢ univ) :=
      ((bB.property c hc e f).1.add (b.property c hc e f).1).sub
        ((A.regularizedSymbol 0 a hs hh).property c hc e f).1
    refine ⟨hd, ?_⟩
    intro J hJV hJ α β
    obtain ⟨J', hJ', hJJ', hJ'V⟩ := exists_compact_between hJ
      (isOpen_symbolChartDomain E F c e f) hJV
    obtain ⟨Ra, _, hRa⟩ := A.regularizedSymbolFunction_eq_inChart_at_high_frequency
      a c hc e f J' hJ' hJ'V
    obtain ⟨Rd, _, hRd⟩ := A.regularizedSymbolFunction_eq_inChart_at_high_frequency
      d c hc e f J' hJ' hJ'V
    have hz : ∀ z ∈ interior J', ∀ η, max Ra Rd ≤ ‖η‖ → (pB + pd - pa) z η = 0 := by
      intro z hz η hη
      change globalSymbolInChart E F B.principalSymbolFunction c e f z η +
        globalSymbolInChart E F (A.regularizedSymbolFunction d) c e f z η -
        globalSymbolInChart E F (A.regularizedSymbolFunction a) c e f z η = 0
      rw [hRa z (interior_subset hz) η ((le_max_left _ _).trans hη),
        hRd z (interior_subset hz) η ((le_max_right _ _).trans hη)]
      ext v
      simp [globalSymbolInChart, d]
    exact (isSmoothingSymbol_of_frequency_support isOpen_interior (pB + pd - pa)
      (max Ra Rd) (hd.mono (Set.prod_mono (interior_subset.trans hJ'V) subset_rfl))
      hz (0 - 1)).2 J hJJ' hJ α β
  -- Both coordinate cutoffs of this same finite family fit into one plateau inside U.
  obtain ⟨D, hD, hKCD, hDU⟩ := exists_compact_between (hK.union hCcompact) hU
    (Set.union_subset hKU hCU)
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ⊤) (hK.union hCcompact).isClosed hKCD
  have hχD : tsupport χ ⊆ D := by
    apply closure_minimal ?_ hD.isClosed
    intro x hx
    by_contra hxD
    exact hx (hχzero x hxD)
  have hone (x : M) (hx : x ∈ K ∪ C) : χ x = 1 := hχone.self_of_nhdsSet x hx
  let χE := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  let χF := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  have hinput (j : Fin N) (u : smoothSections (n := n) (r := r) E) :
      (L j).toLinearMap (χE u) = (L j).toLinearMap u := by
    apply (L j).toLinearMap_eq_of_eq_on_support
    intro x hx
    change (χ x : ℂ) • u.val x = u.val x
    rw [hone x (Or.inr (hLC j (Set.image_mono subset_union_right hx)))]
    simp
  have houtput (j : Fin N) (u : smoothSections (n := n) (r := r) E) :
      χF ((L j).toLinearMap u) = (L j).toLinearMap u := by
    apply Subtype.ext
    funext x
    change (χ x : ℂ) • ((L j).toLinearMap u).val x = ((L j).toLinearMap u).val x
    by_cases hx : x ∈ (L j).chart.symm '' tsupport (L j).output.cutoff
    · rw [hone x (Or.inr (hLC j (Set.image_mono subset_union_left hx)))]
      simp
    · rw [(L j).toLinearMap_eq_zero u x hx, smul_zero]
  let t := ∑ j, (L j).toLinearMap
  have hfixed : twoSidedSectionCutoff t χ χ.contMDiff = t := by
    apply LinearMap.ext
    intro u
    change χF ((∑ j, (L j).toLinearMap) (χE u)) = (∑ j, (L j).toLinearMap) u
    simp only [LinearMap.sum_apply, map_sum, hinput, houtput]
  -- Bundle the exact finite sum with its zero smooth-kernel remainder.
  have hz : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F) := by
    let Z : SmoothKernel (n := n) (r := r) (q := q) E F :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro e f _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E F (fun _ _ ↦ 0) e f z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨Z, ?_⟩
    ext u x
    change Z.apply μ u x = 0
    simp [SmoothKernel.apply, Z]
  let T : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨t, N, L, by change IsSmoothingOperator μ (t - t); simpa using hz⟩
  have hTclass : T.principalSymbol = globalPrincipalSymbolClass E F 0 b := by
    rw [T.principalSymbol_eq_of_representation N L
      (by change IsSmoothingOperator μ (t - t); simpa using hz), hLsymbol]
  let B₀ : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨B.toLinearMap, by simpa only [Nat.cast_zero] using
      B.isPseudodifferentialOperator (μ := μ)⟩
  have hBclass : B₀.principalSymbol = globalPrincipalSymbolClass E F 0 bB := by
    have htransport (s : ℝ) (hs : ((0 : ℕ) : ℝ) = s)
        (B' : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ s)
        (b' : globalSymbolSpace (n := n) (r := r) (q := q) E F s)
        (hop : B'.toLinearMap = B.toLinearMap) (hsym : b'.val = B.principalSymbolFunction) :
        B'.principalSymbol = globalPrincipalSymbolClass E F s b' := by
      subst s
      rw [B'.principalSymbol_eq_of_toLinearMap_eq μ (B.toPseudodifferentialOperator μ) hop,
        B.principalSymbol_toPseudodifferentialOperator μ]
      congr 1
      exact Subtype.ext hsym.symm
    exact htransport 0 (Nat.cast_zero) B₀ bB rfl rfl
  let S := B₀.add T
  have hSclass : S.principalSymbol = P.principalSymbol := by
    change (B₀.add T).principalSymbol = _
    rw [principalSymbol_add, hBclass, hTclass, ← map_add, hclass, ← hprincipal]
  let space := pseudodifferentialSpace (n := n) (r := r) (q := q) E F μ 0
  let R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨P.toLinearMap - B.toLinearMap, space.sub_mem P.isPseudodifferentialOperator
      B₀.isPseudodifferentialOperator⟩
  let Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨B.toLinearMap + twoSidedSectionCutoff R.toLinearMap χ χ.contMDiff,
      space.add_mem B₀.isPseudodifferentialOperator
        (isPseudodifferentialOperator_twoSidedSectionCutoff R χ χ.contMDiff)⟩
  refine ⟨χ, χ.contMDiff, hD.of_isClosed_subset (isClosed_tsupport _) hχD,
    hχD.trans hDU, fun x hx ↦ hone x (Or.inl hx), Q, rfl, ?_⟩
  -- Only the lower-order error changes; the supported reference correction is fixed.
  have hlow := (P.principalSymbol_eq_iff S).mp hSclass.symm
  let V : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (0 - 1) :=
    ⟨P.toLinearMap - S.toLinearMap, hlow⟩
  have hcutSub (R₁ R₂ : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) :
      twoSidedSectionCutoff (R₁ - R₂) χ χ.contMDiff =
        twoSidedSectionCutoff R₁ χ χ.contMDiff - twoSidedSectionCutoff R₂ χ χ.contMDiff := by
    ext u x
    simp [twoSidedSectionCutoff, map_sub]
  have hdiff : Q.toLinearMap - P.toLinearMap =
      twoSidedSectionCutoff V.toLinearMap χ χ.contMDiff - V.toLinearMap := by
    change B.toLinearMap + twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap)
      χ χ.contMDiff - P.toLinearMap =
        twoSidedSectionCutoff (P.toLinearMap - (B.toLinearMap + t)) χ χ.contMDiff -
          (P.toLinearMap - (B.toLinearMap + t))
    rw [show P.toLinearMap - (B.toLinearMap + t) =
      (P.toLinearMap - B.toLinearMap) - t by abel,
      hcutSub (P.toLinearMap - B.toLinearMap) t, hfixed]
    abel
  apply (Q.principalSymbol_eq_iff P).mpr
  rw [hdiff]
  exact (pseudodifferentialSpace E F μ (0 - 1)).sub_mem
    (isPseudodifferentialOperator_twoSidedSectionCutoff V χ χ.contMDiff) hlow

/-- An exterior fiber isomorphism forces both localized kernels into the cutoff support. -/
theorem ker_support_of_localization
    (P Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (B : DifferentialOperator (n := n) (r := r) (q := q) E F 0)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ)
    (hQ : Q.toLinearMap = B.toLinearMap +
      twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ)
    (hBext : ∀ x, x ∉ tsupport χ → Function.Bijective (B.principalSymbol x 0))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F) :
    (∀ u : Q.toLinearMap.ker, closure {x | u.val.val x ≠ 0} ⊆ tsupport χ) ∧
      (∀ v : (Q.metricFormalAdjoint h k).toLinearMap.ker,
        closure {x | v.val.val x ≠ 0} ⊆ tsupport χ) := by
  /- Operator kernel: outside the cutoff support the correction vanishes, so
  Q u=0 says b(x)u(x)=0. The local order-zero differential expression identifies
  b(x) with B.principalSymbol x 0, and hBext forces u(x)=0.
  Adjoint kernel: the same-density integral identities give exactly
  Q†=B†+χ(P†-B†)χ. Outside the cutoff support B† is the fiber adjoint of b(x).
  A finite-dimensional fiber isomorphism has an invertible adjoint for any
  positive definite metrics, even if it is not unitary. Thus v(x)=0 there too.
  Taking closures retains inclusion in the closed cutoff support. This proves
  support only, not finite dimension or zero-extension identifications across
  different manifolds; those require ellipticity and further geometric data. -/
  classical
  let B₀ : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨B.toLinearMap, by simpa only [Nat.cast_zero] using
      B.isPseudodifferentialOperator (μ := μ)⟩
  let R := P.add (B₀.smul (-1))
  have hR : R.toLinearMap = P.toLinearMap - B.toLinearMap := by
    change P.toLinearMap + (-1 : ℂ) • B.toLinearMap = _
    simp only [neg_one_smul, sub_eq_add_neg]
  let C : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 :=
    ⟨twoSidedSectionCutoff R.toLinearMap χ hχ,
      isPseudodifferentialOperator_twoSidedSectionCutoff R χ hχ⟩
  let Bdagger := B.metricFormalAdjoint (μ := μ) h k
  -- Add the exact adjoint identities, retaining the same density and real cutoff.
  have hCadj := R.metricFormalAdjoint_twoSidedSectionCutoff C χ hχ rfl h k
  have hrel := (C.isMetricFormalAdjoint_metricFormalAdjoint h k)
  rw [hCadj] at hrel
  have hsum := (B.isMetricFormalAdjoint_metricFormalAdjoint h k).add hrel
  have hsumQ : IsMetricFormalAdjoint h k μ Q.toLinearMap
      (Bdagger.toLinearMap +
        twoSidedSectionCutoff (R.metricFormalAdjoint h k).toLinearMap χ hχ) := by
    rw [hQ, ← hR]
    exact hsum
  have hQadj := (Q.isMetricFormalAdjoint_metricFormalAdjoint h k).unique hsumQ
  constructor
  · intro u
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro x hx
    by_contra hxχ
    have hzero : (twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ u.val).val x =
        0 := by
      by_contra hne
      exact hxχ ((twoSidedSectionCutoff_support
        (P.toLinearMap - B.toLinearMap) χ hχ).1 u.val (subset_closure hne))
    have hker := congrArg (fun s : smoothSections (n := n) (r := q) F ↦ s.val x)
      u.property
    have heq := congrArg (fun T : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F ↦ (T u.val).val x) hQ
    replace hker := heq.symm.trans hker
    change (B.toLinearMap u.val).val x +
      (twoSidedSectionCutoff (P.toLinearMap - B.toLinearMap) χ hχ u.val).val x = 0 at hker
    rw [hzero, add_zero, zeroOrder_apply_eq_principalSymbol B u.val x 0] at hker
    exact hx ((hBext x hxχ).1 (hker.trans (map_zero _).symm))
  · intro v
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro x hx
    by_contra hxχ
    have hzero :
        (twoSidedSectionCutoff (R.metricFormalAdjoint h k).toLinearMap χ hχ v.val).val x =
          0 := by
      by_contra hne
      exact hxχ ((twoSidedSectionCutoff_support
        (R.metricFormalAdjoint h k).toLinearMap χ hχ).1 v.val (subset_closure hne))
    have hker := congrArg (fun s : smoothSections (n := n) (r := r) E ↦ s.val x)
      v.property
    have heq := congrArg (fun T : smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E ↦ (T v.val).val x) hQadj
    replace hker := heq.symm.trans hker
    change (Bdagger.toLinearMap v.val).val x +
      (twoSidedSectionCutoff (R.metricFormalAdjoint h k).toLinearMap χ hχ v.val).val x = 0
      at hker
    rw [hzero, add_zero, zeroOrder_apply_eq_principalSymbol Bdagger v.val x 0] at hker
    -- Surjectivity of the exterior fiber map and positivity of the original metric
    -- force a vector in the kernel of its adjoint to vanish; unitarity is unnecessary.
    obtain ⟨w, hw⟩ := (hBext x hxχ).2 (v.val.val x)
    have hpair := B.principalSymbol_metricFormalAdjoint_pairing (μ := μ) h k x 0 w (v.val.val x)
    rw [hw] at hpair
    change k.pairing x (v.val.val x) (v.val.val x) =
      h.pairing x w (Bdagger.principalSymbol x 0 (v.val.val x)) at hpair
    rw [hker] at hpair
    have hpos : v.val.val x = 0 := by
      have hz : k.pairing x (v.val.val x) (v.val.val x) = 0 := by
        apply hpair.trans
        let : InnerProductSpace.Core ℂ (E x) := h.toCore x
        exact InnerProductSpace.Core.inner_zero_right w
      exact (k.toCore x).definite _ hz
    exact hx hpos

end PseudodifferentialOperator

end AtiyahSinger
