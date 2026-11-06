/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.GlobalSymbolComposition
public import AtiyahSinger.Analysis.LocalComposition
public import AtiyahSinger.Analysis.PseudodifferentialCutoff

import all AtiyahSinger.Analysis.GlobalPrincipalSymbol

/-!
# Composition of global pseudodifferential operators

Public module ID: M0667.

Sources: SG III.3.17(iii), together with III.3.10 and III.3.19 for the principal class.
First establish the smoothing ideal using the all-order Sobolev characterization.
The compact intermediate support puts each pair of pieces in one common chart
after nested cutoffs. Apply the local calculus, keeping the smooth-kernel remainder.
Then compose arbitrary finite global representations. The bundled product is the
actual composite of section maps. Its principal class is the fiberwise product in
the concrete global quotient. All bundles have fixed, possibly different, complex
ranks on the same closed base. No ellipticity, homogeneous-symbol, Hermitian, or
orientation assumption is imposed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set Filter
open scoped Topology SchwartzMap
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F G : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin k)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin k)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := k) G]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- A smoothing map after a PDO is again represented by a smooth kernel. -/
theorem IsSmoothingOperator.comp_isPseudodifferentialOperator {m : ℝ}
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := k) G)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hQ : IsSmoothingOperator μ Q) (hP : IsPseudodifferentialOperator E F μ m P) :
    IsSmoothingOperator μ (Q.comp P) := by
  /- Choose smooth bundle presentations. For every source order s and target order
  t, first extend P from H^s(E) to H^(s-m)(F), then Q to H^t(G). The composite
  agrees with QP on the dense smooth sections. The all-order kernel characterization
  gives a genuine smooth kernel. This argument precedes global PDO composition. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  obtain ⟨C⟩ := nonempty_smoothBundlePresentation (n := n) (r := k) G
  let p : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m := ⟨P, hP⟩
  apply (isSmoothingOperator_iff_sobolevExtensions μ (Q.comp P) A C).mpr
  intro s t
  obtain ⟨S, hS, _⟩ :=
    existsUnique_sobolevExtension_of_isSmoothingOperator μ Q hQ B C (s - m) t
  refine ⟨S.comp (p.sobolevExtension A B s), ?_⟩
  intro u
  simp only [ContinuousLinearMap.comp_apply, p.sobolevExtension_smoothToSobolev, hS]
  rfl

/-- A PDO after a smoothing map is again represented by a smooth kernel. -/
theorem IsPseudodifferentialOperator.comp_isSmoothingOperator {l : ℝ}
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := k) G)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hQ : IsPseudodifferentialOperator F G μ l Q) (hP : IsSmoothingOperator μ P) :
    IsSmoothingOperator μ (Q.comp P) := by
  /- For arbitrary s,t, extend P from H^s(E) to H^(t+l)(F), then apply the
  order-l bound for Q. Identify (t+l)-l with t and retain the specified smooth
  action. All source and target orders are allowed, so the existing kernel
  characterization produces the smooth kernel of QP without using a transpose. -/
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
  obtain ⟨C⟩ := nonempty_smoothBundlePresentation (n := n) (r := k) G
  let qOp : PseudodifferentialOperator (n := n) (r := q) (q := k) F G μ l := ⟨Q, hQ⟩
  apply (isSmoothingOperator_iff_sobolevExtensions μ (Q.comp P) A C).mpr
  intro s t
  obtain ⟨S, hS, _⟩ :=
    existsUnique_sobolevExtension_of_isSmoothingOperator μ P hP A B s (t + l)
  -- The natural inclusion only identifies the equal real target-order expressions.
  let T := (C.sobolevInclusion ((t + l) - l) t (by linarith)).comp
    ((qOp.sobolevExtension B C (t + l)).comp S)
  refine ⟨T, ?_⟩
  intro u
  simp only [T, ContinuousLinearMap.comp_apply, hS,
    qOp.sobolevExtension_smoothToSobolev, C.sobolevInclusion_smoothToSobolev]
  rfl

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Compact common-chart realization, with one exact map, support, and principal germ. -/
private theorem PseudodifferentialPiece.exists_supported_localized_symbol {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (hbase : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆
      c.source ∩ A.frame.baseSet ∩ B.frame.baseSet)
    (hone : c '' (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
      interior {z | A.cutoff z = 1})
    (hoverlap : tsupport A.cutoff ⊆ c.symm ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) :
    letI := A.frame_mem_atlas
    letI := B.frame_mem_atlas
    ∃ (p : SymbolFunction n r q)
        (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)))
        (V : Set (EuclideanSpace ℝ (Fin n))),
      IsSymbol Set.univ m p ∧ IsOpen V ∧ tsupport A.cutoff ⊆ V ∧
        V ⊆ symbolChartDomain E F c A.frame B.frame ∧
        IsSymbol V (m - 1)
          (p - globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame) ∧
        (∀ u z, T u z = quantize p u z) ∧
        (∀ u z, T u z = B.localize hc (L.toLinearMap (A.extend hc u)) z) ∧
        HasOperatorSupport (tsupport A.cutoff) T := by
  classical
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨p, hp, haction, hprincipal⟩ := L.exists_localized_symbol c hc A B
    hAB hbase hone hoverlap
  -- Compactify only in the output coordinate. The plateau is one on the full local support.
  obtain ⟨O, hO, hKO, _, hOc⟩ := exists_open_between_and_isCompact_closure
    A.compact_support isOpen_univ (Set.subset_univ _)
  -- Enlarge the plateau once so that it contains a neighborhood of the original support.
  obtain ⟨O', hO', hOO', _, hO'c⟩ := exists_open_between_and_isCompact_closure
    hOc isOpen_univ (Set.subset_univ _)
  obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO' hOc.isClosed hOO'
  have hcδ : HasCompactSupport δ := by
    change IsCompact (tsupport δ)
    rw [show tsupport δ = closure O' from congrArg closure hsδ]
    exact hO'c
  have hδone : tsupport A.cutoff ⊆ interior {z | δ z = 1} := by
    apply hKO.trans
    apply interior_maximal ?_ hO
    intro z hz
    exact (honeδ z).mp (subset_closure hz)
  let p' := zeroExtendedSymbol Set.univ δ p
  have hp' : IsSymbol Set.univ m p' := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ
    m δ hδ hcδ (Set.subset_univ _) p hp
  have hcp' : HasCompactSupport p' := hasCompactSupport_zeroExtendedSymbol Set.univ δ p hcδ
  let T := quantizeSchwartz m p' hp' hcp'
  have hT (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      T u z = B.localize hc (L.toLinearMap (A.extend hc u)) z := by
    rw [quantizeSchwartz_apply]
    have hscale : quantize p' u z = (δ z : ℂ) • quantize p u z := by
      simp only [p', zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, quantize, smul_apply]
      simp_rw [smul_comm (Complex.exp _) (δ z : ℂ)]
      rw [integral_smul, smul_comm]
    rw [hscale, haction]
    by_cases hz : z ∈ tsupport A.cutoff
    · rw [show δ z = 1 from (interior_subset (s := {z | δ z = 1})) (hδone hz),
        Complex.ofReal_one, one_smul]
    · have hzB : z ∉ tsupport B.cutoff := by rwa [← hAB]
      have hzero : B.localize hc (L.toLinearMap (A.extend hc u)) z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hzB (B.tsupport_localizedFunction_subset _ h))
      rw [hzero, smul_zero]
  let W := symbolChartDomain E F c A.frame B.frame ∩ c.symm ⁻¹'
    (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)
  let V := W ∩ interior {z | δ z = 1}
  have hW : IsOpen W :=
    (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1)).isOpen_inter_preimage
      (isOpen_symbolChartDomain E F c A.frame B.frame)
      ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hV : IsOpen V := hW.inter isOpen_interior
  have hKV : tsupport A.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩,
      hoverlap hz⟩, hδone hz⟩
  have hrem : IsSymbol V (m - 1)
      (p' - globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame) := by
    have hold := hprincipal.restrict (show V ⊆ W from Set.inter_subset_left)
    have heq (z : X) (hz : z ∈ V) : p' z = p z := by
      funext ξ
      have hδz : δ z = 1 := (interior_subset (s := {z | δ z = 1})) hz.2
      simp [p', zeroExtendedSymbol, hδz]
    refine ⟨hold.1.congr (fun z hz ↦ by
      change p' z.1 z.2 - _ = p z.1 z.2 - _
      rw [heq z.1 hz.1]), ?_⟩
    intro K hKV' hK i j
    obtain ⟨C, hC, hbound⟩ := hold.2 K hKV' hK i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j
        ((p' - globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame) y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j
        ((p - globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame) y) ξ) := by
      filter_upwards [hV.mem_nhds (hKV' hx)] with y hy
      simp only [Pi.sub_apply, heq y hy]
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ
  refine ⟨p', T, V, hp', hV, hKV, fun z hz ↦ hz.1.1, hrem,
    quantizeSchwartz_apply m p' hp' hcp', hT, ?_⟩
  constructor
  · intro u
    have heq : (T u : X → EuclideanSpace ℂ (Fin q)) =
        B.localizedFunction (L.toLinearMap (A.extend hc u)) := funext (hT u)
    rw [heq]
    simpa only [← hAB] using B.tsupport_localizedFunction_subset (L.toLinearMap (A.extend hc u))
  · intro u hu
    have hzero : A.extend hc u = 0 := by
      apply Subtype.ext
      funext x
      change A.extendedFunction u x = 0
      by_cases hx : x ∈ c.source
      · by_cases hz : c x ∈ tsupport A.cutoff
        · have hu0 : u (c x) = 0 := image_eq_zero_of_notMem_tsupport
            (fun h ↦ Set.disjoint_left.mp hu h hz)
          simp [BundleChartCutoff.extendedFunction, hx, hu0]
        · simp [BundleChartCutoff.extendedFunction, hx, image_eq_zero_of_notMem_tsupport hz]
      · simp [BundleChartCutoff.extendedFunction, hx]
    apply SchwartzMap.ext
    intro z
    rw [hT, hzero, map_zero]
    change B.localizeLinearMap hc 0 z = 0
    rw [map_zero]
    rfl

/-- Common-chart refinement composes two local pieces, retaining their actual principal class. -/
theorem PseudodifferentialPiece.exists_representation_comp {l m : ℝ}
    (Q : PseudodifferentialPiece (n := n) (r := q) (q := k) F G l)
    (P : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
    ∃ (N : ℕ) (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := k) E G (l + m)),
      IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - ∑ j, (L j).toLinearMap) ∧
        globalPrincipalSymbolClass E G (l + m) (∑ j, (L j).globalSymbol) =
          globalPrincipalSymbolClass E G (l + m)
            (globalSymbolSpaceComp Q.globalSymbol P.globalSymbol) := by
  /- The actual middle support K is compact and contained in both original charts
  and all four frame domains. Choose nested cutoffs χ and β there, with χ=1 near K
  and β=1 near supp χ. The product of χ P β and β Q χ differs from QP by two
  off-diagonal smoothing terms, using the already established ideals.
  Transport both truncated pieces to P's chart with one common plateau ρ and the
  same intermediate frame. Compose their actual supported Schwartz operators.
  The resulting single piece L retains this exact action. Local composition and
  the two coordinate-change remainders give its principal comparison; all added
  cutoffs are one on the original product support. A lower-order piece with the
  same outer cutoffs records this error, so the action and class use the same L. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let := P.input.frame_mem_atlas
  let := P.output.frame_mem_atlas
  let := Q.input.frame_mem_atlas
  let := Q.output.frame_mem_atlas
  let KP := P.chart.symm '' tsupport P.output.cutoff
  let KQ := Q.chart.symm '' tsupport Q.input.cutoff
  let K := KP ∩ KQ
  let DP := P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet
  let DQ := Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet
  let D := DP ∩ DQ
  have hKP : IsCompact KP := P.output.compact_support.image_of_continuousOn
    (P.chart.continuousOn_symm.mono (fun z hz ↦ (P.output.support_subset hz).1))
  have hKQ : IsCompact KQ := Q.input.compact_support.image_of_continuousOn
    (Q.chart.continuousOn_symm.mono (fun z hz ↦ (Q.input.support_subset hz).1))
  have hK : IsCompact K := hKP.inter hKQ
  have hD : IsOpen D :=
    ((P.chart.open_source.inter P.input.frame.open_baseSet).inter P.output.frame.open_baseSet).inter
      ((Q.chart.open_source.inter Q.input.frame.open_baseSet).inter Q.output.frame.open_baseSet)
  have hKD : K ⊆ D := by
    rintro x ⟨⟨z, hz, rfl⟩, ⟨w, hw, heq⟩⟩
    refine ⟨⟨⟨P.chart.map_target (P.output.support_subset hz).1,
      P.output_support_in_input_frame hz⟩, (P.output.support_subset hz).2⟩, ?_⟩
    rw [← heq]
    exact ⟨⟨Q.chart.map_target (Q.input.support_subset hw).1,
      (Q.input.support_subset hw).2⟩, Q.input_support_in_output_frame hw⟩
  -- The whole intermediate support is in both original charts; one chart suffices.
  have hcutoff (S U : Set M) (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
      ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ U ∧ S ⊆ interior {x | χ x = 1} := by
    obtain ⟨W, hW, hSW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hS hU hSU
    obtain ⟨χ, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (n := ⊤) hS.isClosed (hSW.trans hW.subset_interior_closure)
    have hs : tsupport χ ⊆ closure W := by
      apply closure_minimal ?_ hWc.isClosed
      intro x hx
      by_contra hn
      exact hx (hzero x hn)
    refine ⟨χ, χ.contMDiff, hWc.of_isClosed_subset (isClosed_tsupport _) hs,
      hs.trans hWU, ?_⟩
    exact subset_interior_iff_mem_nhdsSet.mpr hone
  obtain ⟨χ, hχ, hcχ, hsχ, honeχ⟩ := hcutoff K D hK hD hKD
  obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff (tsupport χ) D hcχ hD hsχ
  have hχK (x : M) (hx : x ∈ K) : χ x = 1 :=
    (interior_subset (s := {x | χ x = 1})) (honeχ hx)
  have hβχ (x : M) (hx : x ∈ tsupport χ) : β x = 1 :=
    (interior_subset (s := {x | β x = 1})) (honeβ hx)
  have hχβ : tsupport χ ⊆ tsupport β := by
    intro x hx
    apply subset_tsupport
    change β x ≠ 0
    rw [hβχ x hx]
    exact one_ne_zero
  let P₁ := P.cutoff χ β hχ hβ
  let Q₁ := Q.cutoff β χ hβ hχ
  -- A compact product cutoff has no support beyond the original manifold cutoff.
  have hsupport (d : OpenPartialHomeomorph M X) (a : X → ℝ)
      (ha : tsupport a ⊆ d.target) (f : M → ℝ) (hcf : HasCompactSupport f)
      (hsf : tsupport f ⊆ d.source) :
      d.symm '' tsupport (fun z ↦ a z * f (d.symm z)) ⊆ tsupport f := by
    have hcompact : IsCompact (d '' tsupport f) := hcf.image_of_continuousOn
      (d.continuousOn.mono hsf)
    have hsub : tsupport (fun z ↦ a z * f (d.symm z)) ⊆ d '' tsupport f := by
      apply closure_minimal ?_ hcompact.isClosed
      intro z hz
      have hne : a z ≠ 0 ∧ f (d.symm z) ≠ 0 := mul_ne_zero_iff.mp hz
      exact ⟨d.symm z, subset_tsupport _ hne.2, d.right_inv (ha (subset_tsupport _ hne.1))⟩
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hsub hz
    rwa [d.left_inv (hsf hy)]
  have hP₁ : P₁.chart.symm ''
      (tsupport P₁.output.cutoff ∪ tsupport P₁.input.cutoff) ⊆ tsupport β := by
    rw [Set.image_union]
    apply Set.union_subset
    · exact (hsupport P.chart P.output.cutoff (fun z hz ↦ (P.output.support_subset hz).1)
        χ hcχ (fun x hx ↦ (hsχ hx).1.1.1)).trans hχβ
    · exact hsupport P.chart P.input.cutoff (fun z hz ↦ (P.input.support_subset hz).1)
        β hcβ (fun x hx ↦ (hsβ hx).1.1.1)
  have hQ₁ : Q₁.chart.symm ''
      (tsupport Q₁.output.cutoff ∪ tsupport Q₁.input.cutoff) ⊆ tsupport β := by
    rw [Set.image_union]
    apply Set.union_subset
    · exact hsupport Q.chart Q.output.cutoff (fun z hz ↦ (Q.output.support_subset hz).1)
        β hcβ (fun x hx ↦ (hsβ hx).2.1.1)
    · exact (hsupport Q.chart Q.input.cutoff (fun z hz ↦ (Q.input.support_subset hz).1)
        χ hcχ (fun x hx ↦ (hsχ hx).2.1.1)).trans hχβ
  let c := P.chart
  let U := c.target ∩ c.symm ⁻¹' D
  have hU : IsOpen U := c.isOpen_inter_preimage_symm hD
  have hbaseβ : tsupport β ⊆ c.source := fun x hx ↦ (hsβ hx).1.1.1
  have himage : IsCompact (c '' tsupport β) := hcβ.image_of_continuousOn
    (c.continuousOn.mono hbaseβ)
  have himageU : c '' tsupport β ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨c.map_source (hbaseβ hx), by rw [Set.mem_preimage, c.left_inv (hbaseβ hx)]; exact hsβ hx⟩
  obtain ⟨O, hO, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure himage hU himageU
  obtain ⟨O', hO', hOO', hO'U, hO'c⟩ := exists_open_between_and_isCompact_closure hOc hU hOU
  obtain ⟨ρ, hρ, _, hsρ', honeρ'⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO' hOc.isClosed hOO'
  have htsρ : tsupport ρ = closure O' := congrArg closure hsρ'
  have hcρ : HasCompactSupport ρ := by simpa only [HasCompactSupport, htsρ] using hO'c
  have hsρ : tsupport ρ ⊆ U := by rwa [htsρ]
  have honeρ : c '' tsupport β ⊆ interior {z | ρ z = 1} := by
    apply hKO.trans
    apply interior_maximal ?_ hO
    intro z hz
    exact (honeρ' z).mp (subset_closure hz)
  let A : BundleChartCutoff (r := r) E c :=
    { frame := P.input.frame
      frame_mem_atlas := P.input.frame_mem_atlas
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.1.1.2⟩ }
  let B : BundleChartCutoff (r := q) F c :=
    { frame := P.output.frame
      frame_mem_atlas := P.output.frame_mem_atlas
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.1.2⟩ }
  let C : BundleChartCutoff (r := k) G c :=
    { frame := Q.output.frame
      frame_mem_atlas := Q.output.frame_mem_atlas
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.2.2⟩ }
  obtain ⟨p, Tp, Vp, hp, hVp, hKVp, hVpD, hplower, hTp, hTpaction, hTpK⟩ :=
    P₁.exists_supported_localized_symbol c P.chart_mem_atlas A B rfl
      (fun x hx ↦ ⟨⟨(hsβ (hP₁ hx)).1.1.1, (hsβ (hP₁ hx)).1.1.2⟩,
        (hsβ (hP₁ hx)).1.2⟩)
      ((Set.image_mono hP₁).trans honeρ)
      (fun z hz ↦ (hsρ hz).2.1)
  obtain ⟨qSym, Tq, Vq, hq, hVq, hKVq, hVqD, hqlower, hTq, hTqaction, hTqK⟩ :=
    Q₁.exists_supported_localized_symbol c P.chart_mem_atlas B C rfl
      (fun x hx ↦ ⟨⟨(hsβ (hQ₁ hx)).1.1.1, (hsβ (hQ₁ hx)).1.2⟩,
        (hsβ (hQ₁ hx)).2.2⟩)
      ((Set.image_mono hQ₁).trans honeρ)
      (fun z hz ↦ (hsρ hz).2.2)
  -- The same compact support and intermediate frame enter the exact local composition.
  obtain ⟨Oδ, hOδ, hKδ, _, hcOδ⟩ := exists_open_between_and_isCompact_closure
    hcρ isOpen_univ (Set.subset_univ _)
  obtain ⟨Oδ', hOδ', hOOδ, _, hcOδ'⟩ := exists_open_between_and_isCompact_closure
    hcOδ isOpen_univ (Set.subset_univ _)
  obtain ⟨δ, hδ, _, hsδ, honeδ'⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hOδ' hcOδ.isClosed hOOδ
  have hcδ : HasCompactSupport δ := by
    change IsCompact (tsupport δ)
    rw [show tsupport δ = closure Oδ' from congrArg closure hsδ]
    exact hcOδ'
  have honeδ : tsupport ρ ⊆ interior {z | δ z = 1} := by
    apply hKδ.trans
    apply interior_maximal ?_ hOδ
    intro z hz
    exact (honeδ' z).mp (subset_closure hz)
  have hcp : HasCompactSupport p := hcρ.of_isClosed_subset (isClosed_tsupport p)
    (tsupport_symbol_subset_of_hasOperatorSupport m p hp Tp hTp
      (tsupport ρ) (isClosed_tsupport ρ) hTpK)
  have hcq : HasCompactSupport qSym := hcρ.of_isClosed_subset (isClosed_tsupport qSym)
    (tsupport_symbol_subset_of_hasOperatorSupport l qSym hq Tq hTq
      (tsupport ρ) (isClosed_tsupport ρ) hTqK)
  let s := compositionSymbol δ qSym p
  have hs : IsSymbol Set.univ (l + m) s :=
    isSymbol_compositionSymbol l m qSym p hq hp hcq hcp δ hδ hcδ
  let L : PseudodifferentialPiece (n := n) (r := r) (q := k) E G (l + m) :=
    { chart := c
      chart_mem_atlas := P.chart_mem_atlas
      input := A
      output := C
      input_support_in_output_frame := fun z hz ↦ (hsρ hz).2.2.2
      output_support_in_input_frame := fun z hz ↦ (hsρ hz).2.1.1.2
      operator := Tq.comp Tp
      symbol := s
      isSymbol := hs
      operator_apply := fun u z ↦
        (quantize_compositionSymbol l m qSym p hq hp Tq Tp hTq hTp
          (tsupport ρ) hcρ hTqK hTpK δ hδ hcδ honeδ u z).symm }
  have hρβ (x : M) (hx : x ∈ tsupport β) : ρ (c x) = 1 :=
    (interior_subset (s := {z | ρ z = 1})) (honeρ ⟨x, hx, rfl⟩)
  -- The input round trip is only used on the actual input support of P₁.
  have hinput (u : smoothSections (n := n) (r := r) E) :
      P₁.toLinearMap (A.extend P.chart_mem_atlas (A.localize P.chart_mem_atlas u)) =
        P₁.toLinearMap u := by
    apply P₁.toLinearMap_eq_of_eq_on_support
    intro x hx
    have hxβ := hP₁ ((Set.image_mono Set.subset_union_right) hx)
    have hxc : x ∈ c.source := (hsβ hxβ).1.1.1
    have hxf : x ∈ A.frame.baseSet := (hsβ hxβ).1.1.2
    change A.extendedFunction (A.localize P.chart_mem_atlas u) x = u.val x
    simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
    change (ρ (c x) : ℂ) • A.frame.symmL ℂ x (A.localizedFunction u (c x)) = _
    rw [hρβ x hxβ, Complex.ofReal_one, one_smul]
    simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
      sectionInChart]
    rw [c.left_inv hxc]
    rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
    change A.frame.symmL ℂ x ((ρ (c x) : ℂ) •
      A.frame.continuousLinearMapAt ℂ x (u.val x)) = _
    rw [hρβ x hxβ, Complex.ofReal_one, one_smul,
      A.frame.symmL_continuousLinearMapAt hxf]
  have hmiddle (u : smoothSections (n := n) (r := r) E) :
      B.extend P.chart_mem_atlas (B.localize P.chart_mem_atlas (P₁.toLinearMap u)) =
        P₁.toLinearMap u := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ P₁.chart.symm '' tsupport P₁.output.cutoff
    · have hxβ := hP₁ ((Set.image_mono Set.subset_union_left) hx)
      have hxc : x ∈ c.source := (hsβ hxβ).1.1.1
      have hxf : x ∈ B.frame.baseSet := (hsβ hxβ).1.2
      change B.extendedFunction (B.localize P.chart_mem_atlas (P₁.toLinearMap u)) x = _
      simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
      change (ρ (c x) : ℂ) • B.frame.symmL ℂ x
        (B.localizedFunction (P₁.toLinearMap u) (c x)) = _
      rw [hρβ x hxβ, Complex.ofReal_one, one_smul]
      simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
        sectionInChart]
      rw [c.left_inv hxc]
      rw [← B.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
      change B.frame.symmL ℂ x ((ρ (c x) : ℂ) •
        B.frame.continuousLinearMapAt ℂ x ((P₁.toLinearMap u).val x)) = _
      rw [hρβ x hxβ, Complex.ofReal_one, one_smul,
        B.frame.symmL_continuousLinearMapAt hxf]
    · have hz := P₁.toLinearMap_eq_zero u x hx
      change B.extendedFunction (B.localize P.chart_mem_atlas (P₁.toLinearMap u)) x = _
      by_cases hxc : x ∈ c.source
      · simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
        change (B.cutoff (c x) : ℂ) • B.frame.symmL ℂ x
          (B.localizedFunction (P₁.toLinearMap u) (c x)) = _
        simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
          sectionInChart]
        rw [c.left_inv hxc, hz]
        by_cases hxf : x ∈ B.frame.baseSet
        · rw [show (B.frame ⟨x, (0 : F x)⟩).2 = 0 from
            (B.frame.linear ℂ hxf).map_zero]
          simp
        · rw [B.frame.symmL_apply_of_notMem (R := ℂ) hxf]
          simp
      · simp [BundleChartCutoff.extendedFunction, hxc, hz]
  have houtput (v : smoothSections (n := n) (r := q) F) :
      C.extend P.chart_mem_atlas (C.localize P.chart_mem_atlas (Q₁.toLinearMap v)) =
        Q₁.toLinearMap v := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Q₁.chart.symm '' tsupport Q₁.output.cutoff
    · have hxβ := hQ₁ ((Set.image_mono Set.subset_union_left) hx)
      have hxc : x ∈ c.source := (hsβ hxβ).1.1.1
      have hxf : x ∈ C.frame.baseSet := (hsβ hxβ).2.2
      change C.extendedFunction (C.localize P.chart_mem_atlas (Q₁.toLinearMap v)) x = _
      simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
      change (ρ (c x) : ℂ) • C.frame.symmL ℂ x
        (C.localizedFunction (Q₁.toLinearMap v) (c x)) = _
      rw [hρβ x hxβ, Complex.ofReal_one, one_smul]
      simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
        sectionInChart]
      rw [c.left_inv hxc]
      rw [← C.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
      change C.frame.symmL ℂ x ((ρ (c x) : ℂ) •
        C.frame.continuousLinearMapAt ℂ x ((Q₁.toLinearMap v).val x)) = _
      rw [hρβ x hxβ, Complex.ofReal_one, one_smul,
        C.frame.symmL_continuousLinearMapAt hxf]
    · have hz := Q₁.toLinearMap_eq_zero v x hx
      change C.extendedFunction (C.localize P.chart_mem_atlas (Q₁.toLinearMap v)) x = _
      by_cases hxc : x ∈ c.source
      · simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
        change (C.cutoff (c x) : ℂ) • C.frame.symmL ℂ x
          (C.localizedFunction (Q₁.toLinearMap v) (c x)) = _
        simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
          sectionInChart]
        rw [c.left_inv hxc, hz]
        by_cases hxf : x ∈ C.frame.baseSet
        · rw [show (C.frame ⟨x, (0 : G x)⟩).2 = 0 from
            (C.frame.linear ℂ hxf).map_zero]
          simp
        · rw [C.frame.symmL_apply_of_notMem (R := ℂ) hxf]
          simp
      · simp [BundleChartCutoff.extendedFunction, hxc, hz]
  have hL : L.toLinearMap = Q₁.toLinearMap.comp P₁.toLinearMap := by
    apply LinearMap.ext
    intro u
    have hpaction := SchwartzMap.ext (hTpaction (A.localize P.chart_mem_atlas u))
    change C.extend P.chart_mem_atlas (Tq (Tp (A.localize P.chart_mem_atlas u))) = _
    rw [hpaction]
    have hqaction := SchwartzMap.ext
      (hTqaction (B.localize P.chart_mem_atlas
        (P₁.toLinearMap (A.extend P.chart_mem_atlas (A.localize P.chart_mem_atlas u)))))
    rw [hqaction, hmiddle, hinput, houtput]
    rfl
  -- Restore the original composite. The two discarded terms have separated cutoffs.
  let Yχ := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  let Xβ := smoothSectionMul (n := n) (r := r) E (fun x ↦ (β x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hβ)
  let Zβ := smoothSectionMul (n := n) (r := k) G (fun x ↦ (β x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hβ)
  let X₀ := P.cutoff χ (fun _ ↦ 1) hχ contMDiff_const
  have hX₀ : X₀.toLinearMap = Yχ.comp P.toLinearMap := by
    rw [PseudodifferentialPiece.toLinearMap_cutoff]
    simp only [Complex.ofReal_one, smoothSectionMul_one, LinearMap.comp_id]
    rfl
  have hcentral : Q.toLinearMap.comp (Yχ.comp (Yχ.comp P.toLinearMap)) =
      Q.toLinearMap.comp P.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Q.toLinearMap_eq_of_eq_on_support
    intro x hxQ
    by_cases hxP : x ∈ KP
    · change (χ x : ℂ) • ((χ x : ℂ) • (P.toLinearMap u).val x) = _
      rw [hχK x ⟨hxP, hxQ⟩, Complex.ofReal_one, one_smul, one_smul]
    · have hzero := P.toLinearMap_eq_zero u x hxP
      change (χ x : ℂ) • ((χ x : ℂ) • (P.toLinearMap u).val x) = _
      rw [hzero, smul_zero, smul_zero]
  have hzleft (x : M) : (1 - β x) * χ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · rw [hβχ x hx, sub_self, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hzright (x : M) : χ x * (1 - β x) = 0 := by
    rw [mul_comm]
    exact hzleft x
  have hminusE :
      smoothSectionMul E (fun x ↦ ((1 - β x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hβ)) = LinearMap.id - Xβ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change ((1 - β x : ℝ) : ℂ) • u.val x = u.val x - (β x : ℂ) • u.val x
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hminusG :
      smoothSectionMul G (fun x ↦ ((1 - β x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hβ)) = LinearMap.id - Zβ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change ((1 - β x : ℝ) : ℂ) • u.val x = u.val x - (β x : ℂ) • u.val x
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hQoff : IsSmoothingOperator μ ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ)) := by
    have h := Q.isSmoothingOperator_cutoff_of_mul_eq_zero (μ := μ)
      (fun x ↦ 1 - β x) χ (contMDiff_const.sub hβ) hχ hzleft
    rwa [hminusG] at h
  have hPoff : IsSmoothingOperator μ (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ))) := by
    have h := P.isSmoothingOperator_cutoff_of_mul_eq_zero (μ := μ)
      χ (fun x ↦ 1 - β x) hχ (contMDiff_const.sub hβ) hzright
    rwa [hminusE] at h
  have hleft := IsSmoothingOperator.comp_isPseudodifferentialOperator
    ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ)) X₀.toLinearMap hQoff
    (X₀.isPseudodifferentialOperator m)
  have hright := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q₁.toLinearMap (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ)))
    (Q₁.isPseudodifferentialOperator l) hPoff
  have hsumEq :
      ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ)).comp X₀.toLinearMap +
        Q₁.toLinearMap.comp (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ))) =
      Q.toLinearMap.comp P.toLinearMap - L.toLinearMap := by
    rw [hL, hX₀]
    simp only [P₁, Q₁, PseudodifferentialPiece.toLinearMap_cutoff]
    change ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ)).comp
        (Yχ.comp P.toLinearMap) +
      (Zβ.comp (Q.toLinearMap.comp Yχ)).comp
        (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ))) =
      Q.toLinearMap.comp P.toLinearMap -
        (Zβ.comp (Q.toLinearMap.comp Yχ)).comp (Yχ.comp (P.toLinearMap.comp Xβ))
    simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.comp_assoc]
    rw [hcentral]
    abel
  have hrem : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - L.toLinearMap) := by
    obtain ⟨AP⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
    obtain ⟨CG⟩ := nonempty_smoothBundlePresentation (n := n) (r := k) G
    apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ AP CG).mpr
    intro t
    rw [← hsumEq]
    exact (pseudodifferentialSpace E G μ t).add_mem
      (hleft.isPseudodifferentialOperator t _) (hright.isPseudodifferentialOperator t _)
  -- Every auxiliary factor is one on the support of the original principal product.
  have hPcut (x : M) (ξ) : P₁.globalSymbolFunction x ξ =
      ((χ x * β x : ℝ) : ℂ) • P.globalSymbolFunction x ξ := by
    by_cases hx : x ∈ DP
    · dsimp only [DP] at hx
      simp only [P₁, PseudodifferentialPiece.cutoff, BundleChartCutoff.mulSmooth,
        PseudodifferentialPiece.globalSymbolFunction, ite_eq_left hx,
        P.chart.left_inv hx.1.1]
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · dsimp only [DP] at hx
      simp [P₁, PseudodifferentialPiece.cutoff, BundleChartCutoff.mulSmooth,
        PseudodifferentialPiece.globalSymbolFunction, hx]
  have hQcut (x : M) (ξ) : Q₁.globalSymbolFunction x ξ =
      ((β x * χ x : ℝ) : ℂ) • Q.globalSymbolFunction x ξ := by
    by_cases hx : x ∈ DQ
    · dsimp only [DQ] at hx
      simp only [Q₁, PseudodifferentialPiece.cutoff, BundleChartCutoff.mulSmooth,
        PseudodifferentialPiece.globalSymbolFunction, ite_eq_left hx,
        Q.chart.left_inv hx.1.1]
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · dsimp only [DQ] at hx
      simp [Q₁, PseudodifferentialPiece.cutoff, BundleChartCutoff.mulSmooth,
        PseudodifferentialPiece.globalSymbolFunction, hx]
  have hprod : globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction =
      globalSymbolComp Q.globalSymbolFunction P.globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ K
    · have hxχ : x ∈ tsupport χ := by
        apply subset_tsupport
        change χ x ≠ 0
        rw [hχK x hx]
        exact one_ne_zero
      simp [globalSymbolComp, hPcut, hQcut, hχK x hx, hβχ x hxχ]
    · by_cases hxP : x ∈ KP
      · have hxQ : x ∉ KQ := fun h ↦ hx ⟨hxP, h⟩
        have hzero := Q.globalSymbolFunction_eq_zero x
          (fun h ↦ hxQ ((Set.image_mono Set.inter_subset_right) h)) ξ
        simp [globalSymbolComp, hQcut, hzero]
      · have hzero := P.globalSymbolFunction_eq_zero x
          (fun h ↦ hxP ((Set.image_mono Set.inter_subset_left) h)) ξ
        simp [globalSymbolComp, hPcut, hzero]
  let V := Vp ∩ Vq
  have hV : IsOpen V := hVp.inter hVq
  have hKV : tsupport ρ ⊆ V := fun z hz ↦ ⟨hKVp hz, hKVq hz⟩
  let ap := globalSymbolInChart E F P₁.globalSymbolFunction c A.frame B.frame
  let aq := globalSymbolInChart F G Q₁.globalSymbolFunction c B.frame C.frame
  have haq : IsSymbol V l aq :=
    (Q₁.isGlobalSymbol_globalSymbolFunction c P.chart_mem_atlas B.frame C.frame).restrict
      (Set.inter_subset_right.trans hVqD)
  have hprincipal : IsSymbol V (l + m - 1) (s - symbolComp aq ap) := by
    have hcomp := (isSymbol_compositionSymbol_sub l m qSym p hq hp Tq Tp hTq hTp
      (tsupport ρ) hcρ hTqK hTpK δ hδ hcδ honeδ).restrict (Set.subset_univ V)
    have hleft : IsSymbol V (l + m - 1) (symbolComp (qSym - aq) p) := by
      convert (hqlower.restrict (show V ⊆ Vq from Set.inter_subset_right)).symbolComp
        hV (hp.restrict (Set.subset_univ V)) using 1
      ring
    have hright : IsSymbol V (l + m - 1) (symbolComp aq (p - ap)) := by
      convert haq.symbolComp hV
        (hplower.restrict (show V ⊆ Vp from Set.inter_subset_left)) using 1
      ring
    have heq : s - symbolComp aq ap =
        (s - symbolComp qSym p) + symbolComp (qSym - aq) p + symbolComp aq (p - ap) := by
      ext z ξ v
      simp only [symbolComp, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.comp_apply,
        sub_apply, add_apply, map_sub]
      abel_nf
    rw [heq]
    exact (hcomp.add hV hleft).add hV hright
  -- Package the one-order error in the very same outer chart cutoffs.
  obtain ⟨Oγ, hOγ, hKγ, hOγV, hcOγ⟩ := exists_open_between_and_isCompact_closure hcρ hV hKV
  obtain ⟨γ, hγ, _, hsγ, honeγ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hOγ (isClosed_tsupport ρ) hKγ
  have hcγ : HasCompactSupport γ := by
    change IsCompact (tsupport γ)
    rw [show tsupport γ = closure Oγ from congrArg closure hsγ]
    exact hcOγ
  have hγV : tsupport γ ⊆ V := by rwa [show tsupport γ = closure Oγ from congrArg closure hsγ]
  let b := zeroExtendedSymbol V γ (s - symbolComp aq ap)
  have hb : IsSymbol Set.univ (l + m - 1) b :=
    isSymbol_zeroExtendedSymbol V hV (l + m - 1) γ hγ hcγ hγV _ hprincipal
  have hbc : HasCompactSupport b := hasCompactSupport_zeroExtendedSymbol V γ _ hcγ
  let R : PseudodifferentialPiece (n := n) (r := r) (q := k) E G (l + m - 1) :=
    { chart := c
      chart_mem_atlas := P.chart_mem_atlas
      input := A
      output := C
      input_support_in_output_frame := L.input_support_in_output_frame
      output_support_in_input_frame := L.output_support_in_input_frame
      operator := quantizeSchwartz (l + m - 1) b hb hbc
      symbol := b
      isSymbol := hb
      operator_apply := quantizeSchwartz_apply (l + m - 1) b hb hbc }
  have hQzero (x : M) (hx : x ∉ tsupport β) (ξ) : Q₁.globalSymbolFunction x ξ = 0 :=
    Q₁.globalSymbolFunction_eq_zero x (fun h ↦ hx (hQ₁
      ((Set.image_mono (fun _ hz ↦ Or.inl hz.1)) h))) ξ
  have hglobalDifference :
      L.globalSymbolFunction - globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction =
        R.globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ c.symm '' tsupport ρ
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzc : z ∈ c.target := (hsρ hz).1
      have hxD : c.symm z ∈ D := (hsρ hz).2
      have hxA : c.symm z ∈ A.frame.baseSet := hxD.1.1.2
      have hxB : c.symm z ∈ B.frame.baseSet := hxD.1.2
      have hxC : c.symm z ∈ C.frame.baseSet := hxD.2.2
      have hcoordDomain : z ∈ symbolChartDomain E G c A.frame C.frame :=
        ⟨⟨hzc, hxA⟩, hxC⟩
      have hscale : ((ρ z * ρ z : ℝ) : ℂ) • symbolComp aq ap z
          (covectorInChart c (c.symm z) ξ) =
          symbolComp aq ap z (covectorInChart c (c.symm z) ξ) := by
        by_cases hβx : c.symm z ∈ tsupport β
        · have hρz : ρ z = 1 := by simpa only [c.right_inv hzc] using hρβ (c.symm z) hβx
          rw [hρz, one_mul, Complex.ofReal_one, one_smul]
        · have hzero : aq z (covectorInChart c (c.symm z) ξ) = 0 := by
            simp [aq, globalSymbolInChart, hQzero (c.symm z) hβx]
          simp [symbolComp, hzero]
      have hcoord :
          globalSymbolInChart E G L.globalSymbolFunction c A.frame C.frame z
              (covectorInChart c (c.symm z) ξ) -
            globalSymbolInChart E G
              (globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction)
              c A.frame C.frame z (covectorInChart c (c.symm z) ξ) =
          globalSymbolInChart E G R.globalSymbolFunction c A.frame C.frame z
            (covectorInChart c (c.symm z) ξ) := by
        rw [L.globalSymbolInChart_globalSymbolFunction _ _ hcoordDomain,
          R.globalSymbolInChart_globalSymbolFunction _ _ hcoordDomain,
          globalSymbolInChart_globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction
            c A.frame B.frame C.frame z _ hxB]
        change ((ρ z * ρ z : ℝ) : ℂ) • s z _ - symbolComp aq ap z _ =
          ((ρ z * ρ z : ℝ) : ℂ) • b z _
        simp only [b, zeroExtendedSymbol, ite_eq_left (hKV hz), (honeγ z).mp hz,
          Complex.ofReal_one, one_smul, Pi.sub_apply, smul_sub, hscale]
      have hxc : c.symm z ∈ c.source := c.map_target hzc
      have h₁ := globalSymbolInChart_covectorInChart E G L.globalSymbolFunction
        c P.chart_mem_atlas A.frame C.frame (c.symm z) hxc ξ
      have h₂ := globalSymbolInChart_covectorInChart E G
        (globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction)
        c P.chart_mem_atlas A.frame C.frame (c.symm z) hxc ξ
      have h₃ := globalSymbolInChart_covectorInChart E G R.globalSymbolFunction
        c P.chart_mem_atlas A.frame C.frame (c.symm z) hxc ξ
      simp only [c.right_inv hzc] at h₁ h₂ h₃
      rw [h₁, h₂, h₃] at hcoord
      ext v : 1
      have hv := congrArg (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin k) ↦
        C.frame.symmL ℂ (c.symm z) (T (A.frame.continuousLinearMapAt ℂ (c.symm z) v))) hcoord
      simpa only [Pi.sub_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub,
        A.frame.symmL_continuousLinearMapAt hxA,
        C.frame.symmL_continuousLinearMapAt hxC] using hv
    · have hLzero := L.globalSymbolFunction_eq_zero x
        (by simpa only [L, A, C, Set.inter_self] using hx) ξ
      have hRzero := R.globalSymbolFunction_eq_zero x
        (by simpa only [R, A, C, Set.inter_self] using hx) ξ
      have hxβ : x ∉ tsupport β := by
        intro hxβ
        apply hx
        exact ⟨c x, subset_tsupport _ (by change ρ (c x) ≠ 0; rw [hρβ x hxβ]; exact one_ne_zero),
          c.left_inv (hbaseβ hxβ)⟩
      simp only [Pi.sub_apply, hLzero, hRzero, globalSymbolComp, hQzero x hxβ ξ,
        ContinuousLinearMap.zero_comp, sub_zero]
  refine ⟨1, fun _ ↦ L, ?_, ?_⟩
  · simpa only [Fin.sum_univ_one] using hrem
  · simp only [Fin.sum_univ_one]
    apply (globalPrincipalSymbolClass_eq_iff E G (l + m) _ _).mpr
    change IsGlobalSymbol E G (l + m - 1)
      (L.globalSymbolFunction - globalSymbolComp Q.globalSymbolFunction P.globalSymbolFunction)
    rw [← hprod, hglobalDifference]
    exact R.isGlobalSymbol_globalSymbolFunction

/-- Operators equivalent modulo smooth kernels have the same principal class at a fixed order. -/
theorem PseudodifferentialOperator.principalSymbol_eq_of_isSmoothingOperator_sub {m : ℝ}
    (P P' : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (h : IsSmoothingOperator μ (P.toLinearMap - P'.toLinearMap)) :
    P.principalSymbol = P'.principalSymbol := by
  /- Choose a finite local representation of P. Subtract the given smoothing
  difference from its remainder to obtain a smooth kernel for P' minus that same
  finite family. The representation formula for the two principal classes now
  gives equality. No converse from equality of principal classes is asserted. -/
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  obtain ⟨K', hK'⟩ := h
  -- Subtract the specified difference kernel from the original remainder.
  -- This retains exactly the same finite local family for both operators.
  let R : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun x y ↦ K.toFun x y - K'.toFun x y
      isSmooth := by
        intro e f _ _
        apply ((K.isSmooth e f).sub (K'.isSmooth e f)).congr
        intro z hz
        simp only [kernelInFrames, ContinuousLinearMap.sub_comp,
          ContinuousLinearMap.comp_sub] }
  have hR : R.toLinearMap μ = K.toLinearMap μ - K'.toLinearMap μ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    change (∫ y, (K.toFun x y - K'.toFun x y) (u.val y) ∂μ) =
      (∫ y, K.toFun x y (u.val y) ∂μ) - ∫ y, K'.toFun x y (u.val y) ∂μ
    simp only [sub_apply]
    exact integral_sub (K.integrable_apply μ u x) (K'.integrable_apply μ u x)
  have hrep : IsSmoothingOperator μ (P'.toLinearMap - ∑ j, (L j).toLinearMap) := by
    refine ⟨R, ?_⟩
    rw [hR, hK, hK']
    abel
  rw [P.principalSymbol_eq_of_representation N L ⟨K, hK⟩,
    P'.principalSymbol_eq_of_representation N L hrep]

/-- SG Theorem 3.17(iii): composing global PDOs adds their orders. -/
theorem IsPseudodifferentialOperator.comp {l m : ℝ}
    (Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := k) G)
    (P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F)
    (hQ : IsPseudodifferentialOperator F G μ l Q)
    (hP : IsPseudodifferentialOperator E F μ m P) :
    IsPseudodifferentialOperator E G μ (l + m) (Q.comp P) := by
  /- Expand the two actual finite local representations. Each product of two local
  pieces has the representation given above. Any term containing a smoothing
  remainder is smoothing by the ideal lemmas, since every local piece is a PDO
  and every smoothing map is a PDO of every order. Flatten the finite families
  and add their genuine smooth kernels. This is exactly the global PDO definition. -/
  classical
  have hPoriginal := hP
  obtain ⟨N, L, hL⟩ := hQ
  obtain ⟨N', L', hL'⟩ := hP
  let Q₀ := ∑ i, (L i).toLinearMap
  let P₀ := ∑ j, (L' j).toLinearMap
  have hQ₀ : IsPseudodifferentialOperator F G μ l Q₀ :=
    (pseudodifferentialSpace F G μ l).sum_mem
      (fun i _ ↦ (L i).isPseudodifferentialOperator l)
  have hpairs : IsPseudodifferentialOperator E G μ (l + m) (Q₀.comp P₀) := by
    have hpair (i : Fin N) (j : Fin N') :
        IsPseudodifferentialOperator E G μ (l + m)
          ((L i).toLinearMap.comp (L' j).toLinearMap) := by
      obtain ⟨R, J, hJ, _⟩ := (L i).exists_representation_comp (μ := μ) (L' j)
      exact ⟨R, J, hJ⟩
    have hsum := (pseudodifferentialSpace E G μ (l + m)).sum_mem
      (fun i (_ : i ∈ Finset.univ) ↦
        (pseudodifferentialSpace E G μ (l + m)).sum_mem
          (fun j (_ : j ∈ Finset.univ) ↦ hpair i j))
    have heq : Q₀.comp P₀ = ∑ i, ∑ j, (L i).toLinearMap.comp (L' j).toLinearMap := by
      apply LinearMap.ext
      intro u
      simp only [Q₀, P₀, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
      exact Finset.sum_comm
    rw [heq]
    exact hsum
  -- The two error terms use the original remainder kernels and the proved ideals.
  have hleft := IsSmoothingOperator.comp_isPseudodifferentialOperator
    (Q - Q₀) P hL hPoriginal
  have hright := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q₀ (P - P₀) hQ₀ hL'
  have htotal := (pseudodifferentialSpace E G μ (l + m)).add_mem
    ((pseudodifferentialSpace E G μ (l + m)).add_mem hpairs
      (hleft.isPseudodifferentialOperator (l + m) _))
    (hright.isPseudodifferentialOperator (l + m) _)
  have heq : Q.comp P = (Q₀.comp P₀ + (Q - Q₀).comp P) + Q₀.comp (P - P₀) := by
    simp only [LinearMap.sub_comp, LinearMap.comp_sub]
    abel
  rw [heq]
  exact htotal

namespace PseudodifferentialOperator

variable {l m : ℝ}
  (Q : PseudodifferentialOperator (n := n) (r := q) (q := k) F G μ l)
  (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- The actual composite of section maps, equipped with its derived global PDO property. -/
def comp : PseudodifferentialOperator (n := n) (r := r) (q := k) E G μ (l + m) where
  toLinearMap := Q.toLinearMap.comp P.toLinearMap
  isPseudodifferentialOperator :=
    Q.isPseudodifferentialOperator.comp Q.toLinearMap P.toLinearMap P.isPseudodifferentialOperator

/-- The principal symbol of the actual composite is the product of its two principal classes. -/
theorem principalSymbol_comp :
    (Q.comp P).principalSymbol = globalPrincipalSymbolComp Q.principalSymbol P.principalSymbol := by
  /- Choose finite representations for Q and P and use the common-chart product
  representation for every pair of local pieces. The smoothing ideal removes all
  remainder terms from the principal class. The principal class formula for each
  pair gives the product of the corresponding global symbols. Additivity in both
  factors regroups the finite double sum into the product of the two sums. Finally
  apply principalSymbol_eq_of_representation for Q, P and their actual composite. -/
  classical
  obtain ⟨N, L, hL⟩ := Q.isPseudodifferentialOperator
  obtain ⟨N', L', hL'⟩ := P.isPseudodifferentialOperator
  let Q₀ := ∑ i, (L i).toLinearMap
  let P₀ := ∑ j, (L' j).toLinearMap
  have hQ₀ : IsPseudodifferentialOperator F G μ l Q₀ :=
    (pseudodifferentialSpace F G μ l).sum_mem
      (fun i _ ↦ (L i).isPseudodifferentialOperator l)
  let T (i : Fin N) (j : Fin N') : pseudodifferentialSpace E G μ (l + m) :=
    ⟨(L i).toLinearMap.comp (L' j).toLinearMap,
      ((L i).isPseudodifferentialOperator l).comp _ _
        ((L' j).isPseudodifferentialOperator m)⟩
  have hleft := IsSmoothingOperator.comp_isPseudodifferentialOperator
    (Q.toLinearMap - Q₀) P.toLinearMap hL P.isPseudodifferentialOperator
  have hright := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q₀ (P.toLinearMap - P₀) hQ₀ hL'
  let R₁ : pseudodifferentialSpace E G μ (l + m) :=
    ⟨(Q.toLinearMap - Q₀).comp P.toLinearMap,
      hleft.isPseudodifferentialOperator (l + m) _⟩
  let R₂ : pseudodifferentialSpace E G μ (l + m) :=
    ⟨Q₀.comp (P.toLinearMap - P₀), hright.isPseudodifferentialOperator (l + m) _⟩
  let S := pseudodifferentialOperatorOfSpace (((∑ i, ∑ j, T i j) + R₁) + R₂)
  have hsum : (∑ i, ∑ j, T i j).val = Q₀.comp P₀ := by
    apply LinearMap.ext
    intro u
    simp only [Submodule.coe_sum, T, Q₀, P₀, LinearMap.comp_apply,
      LinearMap.sum_apply, map_sum]
    exact Finset.sum_comm
  have hmap : (Q.comp P).toLinearMap = S.toLinearMap := by
    change Q.toLinearMap.comp P.toLinearMap =
      ((∑ i, ∑ j, T i j).val + (Q.toLinearMap - Q₀).comp P.toLinearMap) +
        Q₀.comp (P.toLinearMap - P₀)
    rw [hsum]
    simp only [LinearMap.sub_comp, LinearMap.comp_sub]
    abel
  rw [(Q.comp P).principalSymbol_eq_of_toLinearMap_eq μ S hmap]
  let σ := principalSymbolLinearMap (n := n) (r := r) (q := k) E G μ (l + m)
  have hpair (i : Fin N) (j : Fin N') : σ (T i j) =
      globalPrincipalSymbolClass E G (l + m)
        (globalSymbolSpaceComp (L i).globalSymbol (L' j).globalSymbol) := by
    obtain ⟨R, J, hJ, hclass⟩ := (L i).exists_representation_comp (μ := μ) (L' j)
    exact ((pseudodifferentialOperatorOfSpace (T i j)).principalSymbol_eq_of_representation
      R J hJ).trans hclass
  have hR₁ : σ R₁ = 0 :=
    (pseudodifferentialOperatorOfSpace R₁).principalSymbol_eq_zero_of_isSmoothingOperator hleft
  have hR₂ : σ R₂ = 0 :=
    (pseudodifferentialOperatorOfSpace R₂).principalSymbol_eq_zero_of_isSmoothingOperator hright
  change σ (((∑ i, ∑ j, T i j) + R₁) + R₂) = _
  simp only [map_add, map_sum, hR₁, hR₂, add_zero, hpair]
  rw [Q.principalSymbol_eq_of_representation N L hL,
    P.principalSymbol_eq_of_representation N' L' hL', globalPrincipalSymbolComp_class]
  simp only [← map_sum]
  congr 1
  apply Subtype.ext
  funext x ξ
  apply ContinuousLinearMap.ext
  intro v
  simp only [globalSymbolSpaceComp, globalSymbolComp, Submodule.coe_sum,
    Finset.sum_apply, ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  exact Finset.sum_comm

/-- Bounded realizations compose after identifying the equal target orders by natural inclusion. -/
theorem sobolevExtension_comp
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (C : SmoothBundlePresentation (n := n) (r := k) G) (s : ℝ) :
    (Q.comp P).sobolevExtension A C s =
      (C.sobolevInclusion ((s - m) - l) (s - (l + m))
        (by rw [sub_sub, add_comm m l])).comp
        ((Q.sobolevExtension B C (s - m)).comp (P.sobolevExtension A B s)) := by
  /- Stage 1: on a smooth input, the right-hand side first applies P, then Q.
  The natural inclusion changes only the order expression (s-m)-l to the equal
  real number s-(l+m); its smooth-action formula retains the same output section.
  Stage 2: both sides are continuous maps with the same source and target. Density
  of the smooth image in H^s(E) extends the equality to all Sobolev inputs. -/
  apply DFunLike.coe_injective
  apply (A.denseRange_smoothToSobolev s).equalizer
    ((Q.comp P).sobolevExtension A C s).continuous
    ((C.sobolevInclusion ((s - m) - l) (s - (l + m))
      (by rw [sub_sub, add_comm m l])).comp
      ((Q.sobolevExtension B C (s - m)).comp (P.sobolevExtension A B s))).continuous
  funext u
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    sobolevExtension_smoothToSobolev, C.sobolevInclusion_smoothToSobolev]
  rfl

/-- Changing either factor by a smoothing operator changes the composite by a smoothing operator. -/
theorem isSmoothingOperator_comp_sub_comp
    (Q' : PseudodifferentialOperator (n := n) (r := q) (q := k) F G μ l)
    (P' : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hQ : IsSmoothingOperator μ (Q.toLinearMap - Q'.toLinearMap))
    (hP : IsSmoothingOperator μ (P.toLinearMap - P'.toLinearMap)) :
    IsSmoothingOperator μ ((Q.comp P).toLinearMap - (Q'.comp P').toLinearMap) := by
  /- Expand QP-Q'P' as (Q-Q')P + Q'(P-P') on the actual smooth section maps.
  The first term is smoothing by the left ideal property and the second by the
  right ideal property. Their smooth kernels add. This concerns SG's equivalence
  modulo all-order smoothing, which is stronger than equality of principal classes. -/
  have hleft := IsSmoothingOperator.comp_isPseudodifferentialOperator
    (Q.toLinearMap - Q'.toLinearMap) P.toLinearMap hQ P.isPseudodifferentialOperator
  have hright := IsPseudodifferentialOperator.comp_isSmoothingOperator
    Q'.toLinearMap (P.toLinearMap - P'.toLinearMap) Q'.isPseudodifferentialOperator hP
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  obtain ⟨C⟩ := nonempty_smoothBundlePresentation (n := n) (r := k) G
  apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ A C).mpr
  intro t
  have hsum := (pseudodifferentialSpace E G μ t).add_mem
    (hleft.isPseudodifferentialOperator t _) (hright.isPseudodifferentialOperator t _)
  have heq : (Q.comp P).toLinearMap - (Q'.comp P').toLinearMap =
      (Q.toLinearMap - Q'.toLinearMap).comp P.toLinearMap +
        Q'.toLinearMap.comp (P.toLinearMap - P'.toLinearMap) := by
    change Q.toLinearMap.comp P.toLinearMap - Q'.toLinearMap.comp P'.toLinearMap = _
    simp only [LinearMap.sub_comp, LinearMap.comp_sub]
    abel
  rw [heq]
  exact hsum

end PseudodifferentialOperator

end AtiyahSinger
