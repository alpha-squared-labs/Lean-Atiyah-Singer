/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialCutoff
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev
public import AtiyahSinger.Analysis.AtlasSymbolComposition
public import AtiyahSinger.Analysis.LocalComposition

import all AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol

/-!
# Composition of actual locally finite-rank bundle PDOs

Public module ID: M0281.

A02: SG III.3.10, III.3.17(iii) and III.3.18--3.19, pp.183--188.
The output is the actual composite on the original smooth sections.
Its order is the sum of the factor orders, and its principal class is
the fiberwise product of their original principal quotient classes.

The all-real-order smoothing maps form a two-sided ideal. This includes
off-diagonal maps between disconnected components; they are not discarded
by a componentwise decomposition. The intermediate bundle and atlas are
the same for both factors, with no equation on the three local ranks.

The finite-presentation PDO model requires a compact boundaryless smooth
base. Empty, disconnected and zero-dimensional bases remain allowed.
No metric, density, homogeneous symbol, positivity, parametrix or
Fredholm hypothesis is an input. All three composition assertions retain the original maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : M → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {C : SmoothComplexBundleAtlas (n := n) G}

/-- Every all-order smoothing map remains smoothing after an actual atlas PDO. -/
theorem IsAtlasSmoothingOperator.comp_isAtlasPseudodifferentialOperator {m : ℝ}
    (Q : B.smoothSections →ₗ[ℂ] C.smoothSections)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (hQ : IsAtlasSmoothingOperator B C Q)
    (hP : IsAtlasPseudodifferentialOperator A B m P) :
    IsAtlasSmoothingOperator A C (Q.comp P) := by
  /- Stage 1: fix arbitrary source and target atlas presentations and
  arbitrary real orders s,t. Choose one actual presentation of B, which
  exists on the given compact smooth base. The ordinary PDO bound extends
  this same P from order s to s-m in that intermediate presentation.
  Stage 2: hQ extends this same Q from order s-m to order t. Compose
  these bounded maps. Their specifications on original smooth sections
  give exactly Q(Pu), including cross-component contributions. Since
  both outer orders and presentations were arbitrary, this is the
  defining all-order smoothing condition; no composition theorem is used. -/
  -- Keep one intermediate presentation in both bounded realizations.
  obtain ⟨H⟩ := nonempty_atlasBundlePresentation B
  let p : AtlasPseudodifferentialOperator A B m := ⟨P, hP⟩
  intro L K s t
  obtain ⟨S, hS⟩ := hQ H K (s - m) t
  refine ⟨S.comp (p.sobolevExtension L H s), ?_⟩
  intro u
  simp only [ContinuousLinearMap.comp_apply, p.sobolevExtension_smoothToSobolev, hS]
  rfl

/-- Every actual atlas PDO preserves the all-order smoothing ideal on its input side. -/
theorem IsAtlasPseudodifferentialOperator.comp_isAtlasSmoothingOperator {l : ℝ}
    (Q : B.smoothSections →ₗ[ℂ] C.smoothSections)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (hQ : IsAtlasPseudodifferentialOperator B C l Q)
    (hP : IsAtlasSmoothingOperator A B P) :
    IsAtlasSmoothingOperator A C (Q.comp P) := by
  /- Stage 1: for arbitrary outer presentations and orders s,t, choose
  a presentation of the original intermediate atlas B. Extend P from
  order s to t+l using hP, then extend Q from t+l to (t+l)-l using
  the ordinary PDO bound. Identify the latter order with t.
  Stage 2: the composite has exactly the section action Q(Pu) by the
  two dense-image specifications. This proves all-order smoothing on
  the given outer presentations without a kernel, adjoint, component
  restriction or equality of the three local ranks. -/
  -- The same intermediate presentation carries the smoothing lift and the PDO input.
  obtain ⟨H⟩ := nonempty_atlasBundlePresentation B
  let q : AtlasPseudodifferentialOperator B C l := ⟨Q, hQ⟩
  intro L K s t
  obtain ⟨S, hS⟩ := hP L H s (t + l)
  let T := (K.sobolevInclusion ((t + l) - l) t (by linarith)).comp
    ((q.sobolevExtension H K (t + l)).comp S)
  refine ⟨T, ?_⟩
  intro u
  simp only [T, ContinuousLinearMap.comp_apply, hS,
    q.sobolevExtension_smoothToSobolev, K.sobolevInclusion_smoothToSobolev]
  rfl

omit [SecondCountableTopology M] [CompactSpace M] in
/-- A supported common-coordinate full symbol of the same localized atlas action. -/
private theorem AtlasPseudodifferentialPiece.exists_supported_localized_symbol {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c)
    (hAB : D₀.cutoff = K₀.cutoff)
    (hbase : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆
      c.source ∩ (A.chart D₀.frameIndex).baseSet ∩ (B.chart K₀.frameIndex).baseSet)
    (hone : c '' (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
      interior {z | D₀.cutoff z = 1})
    (hoverlap : tsupport D₀.cutoff ⊆ c.symm ⁻¹'
      (L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
        (B.chart L.output.frameIndex).baseSet)) :
    ∃ (p : SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex))
        (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex))) →L[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank K₀.frameIndex))))
        (V : Set (EuclideanSpace ℝ (Fin n))),
      IsSymbol Set.univ m p ∧ IsOpen V ∧ tsupport D₀.cutoff ⊆ V ∧
        V ⊆ atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∧
        IsSymbol V (m - 1)
          (p - atlasGlobalSymbolInChart A B L.globalSymbolFunction c D₀.frameIndex K₀.frameIndex) ∧
        (∀ u z, T u z = quantize p u z) ∧
        (∀ u z, T u z = K₀.localize hc (L.toLinearMap (D₀.extend hc u)) z) ∧
        HasOperatorSupport (tsupport D₀.cutoff) T := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨p, hp, haction, hprincipal⟩ := L.exists_localized_symbol c hc D₀ K₀
    hAB hbase hone hoverlap
  -- Compactify only in the output coordinate. The plateau is one on the full local support.
  obtain ⟨O, hO, hKO, _, hOc⟩ := exists_open_between_and_isCompact_closure
    D₀.compact_support isOpen_univ (Set.subset_univ _)
  -- Enlarge the plateau once so that it contains a neighborhood of the original support.
  obtain ⟨O', hO', hOO', _, hO'c⟩ := exists_open_between_and_isCompact_closure
    hOc isOpen_univ (Set.subset_univ _)
  obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO' hOc.isClosed hOO'
  have hcδ : HasCompactSupport δ := by
    change IsCompact (tsupport δ)
    rw [show tsupport δ = closure O' from congrArg closure hsδ]
    exact hO'c
  have hδone : tsupport D₀.cutoff ⊆ interior {z | δ z = 1} := by
    apply hKO.trans
    apply interior_maximal ?_ hO
    intro z hz
    exact (honeδ z).mp (subset_closure hz)
  let p' := zeroExtendedSymbol Set.univ δ p
  have hp' : IsSymbol Set.univ m p' := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ
    m δ hδ hcδ (Set.subset_univ _) p hp
  have hcp' : HasCompactSupport p' := hasCompactSupport_zeroExtendedSymbol Set.univ δ p hcδ
  let T := quantizeSchwartz m p' hp' hcp'
  have hT (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) (z : X) :
      T u z = K₀.localize hc (L.toLinearMap (D₀.extend hc u)) z := by
    rw [quantizeSchwartz_apply]
    have hscale : quantize p' u z = (δ z : ℂ) • quantize p u z := by
      simp only [p', zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, quantize, smul_apply]
      simp_rw [smul_comm (Complex.exp _) (δ z : ℂ)]
      rw [integral_smul, smul_comm]
    rw [hscale, haction]
    by_cases hz : z ∈ tsupport D₀.cutoff
    · rw [show δ z = 1 from (interior_subset (s := {z | δ z = 1})) (hδone hz),
        Complex.ofReal_one, one_smul]
    · have hzB : z ∉ tsupport K₀.cutoff := by rwa [← hAB]
      have hzero : K₀.localize hc (L.toLinearMap (D₀.extend hc u)) z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hzB
            ((K₀.localizedFunction_properties hc (L.toLinearMap (D₀.extend hc u))).2.1 h))
      rw [hzero, smul_zero]
  let W := atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∩ c.symm ⁻¹'
    (L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩ (B.chart L.output.frameIndex).baseSet)
  let V := W ∩ interior {z | δ z = 1}
  have hW : IsOpen W :=
    (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1)).isOpen_inter_preimage
      (isOpen_atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex)
      ((L.chart.open_source.inter (A.chart L.input.frameIndex).open_baseSet).inter
        (B.chart L.output.frameIndex).open_baseSet)
  have hV : IsOpen V := hW.inter isOpen_interior
  have hKV : tsupport D₀.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨⟨D₀.support_subset hz, (K₀.support_subset (by rwa [← hAB])).2⟩,
      hoverlap hz⟩, hδone hz⟩
  have hrem : IsSymbol V (m - 1)
      (p' - atlasGlobalSymbolInChart A B L.globalSymbolFunction c D₀.frameIndex K₀.frameIndex) := by
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
        ((p' - atlasGlobalSymbolInChart A B L.globalSymbolFunction c
          D₀.frameIndex K₀.frameIndex) y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j
        ((p - atlasGlobalSymbolInChart A B L.globalSymbolFunction c
          D₀.frameIndex K₀.frameIndex) y) ξ) := by
      filter_upwards [hV.mem_nhds (hKV' hx)] with y hy
      simp only [Pi.sub_apply, heq y hy]
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ
  refine ⟨p', T, V, hp', hV, hKV, fun z hz ↦ hz.1.1, hrem,
    quantizeSchwartz_apply m p' hp' hcp', hT, ?_⟩
  constructor
  · intro u
    have heq : (T u : X → EuclideanSpace ℂ (Fin (B.rank K₀.frameIndex))) =
        K₀.localizedFunction (L.toLinearMap (D₀.extend hc u)) := funext (hT u)
    rw [heq]
    simpa only [← hAB] using
      (K₀.localizedFunction_properties hc (L.toLinearMap (D₀.extend hc u))).2.1
  · intro u hu
    have hzero : D₀.extend hc u = 0 := by
      apply Subtype.ext
      funext x
      change D₀.extendedFunction u x = 0
      by_cases hx : x ∈ c.source ∩ (A.chart D₀.frameIndex).baseSet
      · by_cases hz : c x ∈ tsupport D₀.cutoff
        · have hu0 : u (c x) = 0 := image_eq_zero_of_notMem_tsupport
            (fun h ↦ Set.disjoint_left.mp hu h hz)
          simp [AtlasChartCutoff.extendedFunction, hx, hu0]
        · simp [AtlasChartCutoff.extendedFunction, hx, image_eq_zero_of_notMem_tsupport hz]
      · simp [AtlasChartCutoff.extendedFunction, hx]
    apply SchwartzMap.ext
    intro z
    rw [hT, hzero, map_zero]
    change K₀.localizeLinearMap hc 0 z = 0
    rw [map_zero]
    rfl

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- The transported principal representative vanishes off its original two-cutoff support. -/
private theorem AtlasPseudodifferentialPiece.globalSymbolFunction_eq_zero {m : ℝ}
    (L : AtlasPseudodifferentialPiece A B m) (x : M)
    (hx : x ∉ L.chart.symm '' (tsupport L.output.cutoff ∩ tsupport L.input.cutoff))
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    L.globalSymbolFunction x ξ = 0 := by
  /- Outside the chart/frame overlap this is the zero-extension branch. Inside
  it, the inverse-chart identity and hx imply at least one cutoff vanishes.
  Thus their product is zero. No support condition in the frequency is asserted. -/
  classical
  -- Nonzero cutoffs would put the original point back in the specified closed support.
  unfold AtlasPseudodifferentialPiece.globalSymbolFunction
  split_ifs with h
  · have hcut : L.output.cutoff (L.chart x) = 0 ∨ L.input.cutoff (L.chart x) = 0 := by
      by_contra hne
      push Not at hne
      apply hx
      exact ⟨L.chart x, ⟨subset_tsupport _ (by exact hne.1),
        subset_tsupport _ (by exact hne.2)⟩, L.chart.left_inv h.1.1⟩
    rcases hcut with hcut | hcut <;> simp [hcut]
  · rfl

set_option maxHeartbeats 400000 in
-- The extended limit accommodates the common-chart refinement and full principal-class comparison.

/-- Common-chart refinement composes two local pieces, retaining their actual principal class. -/
private theorem AtlasPseudodifferentialPiece.exists_piece_comp {l m : ℝ}
    (Q : AtlasPseudodifferentialPiece B C l)
    (P : AtlasPseudodifferentialPiece A B m) :
    ∃ L : AtlasPseudodifferentialPiece A C (l + m),
      IsAtlasSmoothingOperator A C (Q.toLinearMap.comp P.toLinearMap - L.toLinearMap) ∧
        atlasGlobalPrincipalSymbolClass A C (l + m) L.globalSymbol =
          atlasGlobalPrincipalSymbolClass A C (l + m)
            (atlasGlobalSymbolSpaceComp Q.globalSymbol P.globalSymbol) := by
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
  let KP := P.chart.symm '' tsupport P.output.cutoff
  let KQ := Q.chart.symm '' tsupport Q.input.cutoff
  let K := KP ∩ KQ
  let DP := P.chart.source ∩ (A.chart P.input.frameIndex).baseSet ∩
    (B.chart P.output.frameIndex).baseSet
  let DQ := Q.chart.source ∩ (B.chart Q.input.frameIndex).baseSet ∩
    (C.chart Q.output.frameIndex).baseSet
  let D := DP ∩ DQ
  have hKP : IsCompact KP := P.output.compact_support.image_of_continuousOn
    (P.chart.continuousOn_symm.mono (fun z hz ↦ (P.output.support_subset hz).1))
  have hKQ : IsCompact KQ := Q.input.compact_support.image_of_continuousOn
    (Q.chart.continuousOn_symm.mono (fun z hz ↦ (Q.input.support_subset hz).1))
  have hK : IsCompact K := hKP.inter hKQ
  have hD : IsOpen D :=
    ((P.chart.open_source.inter (A.chart P.input.frameIndex).open_baseSet).inter
      (B.chart P.output.frameIndex).open_baseSet).inter
      ((Q.chart.open_source.inter (B.chart Q.input.frameIndex).open_baseSet).inter
        (C.chart Q.output.frameIndex).open_baseSet)
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
  let D₀ : AtlasChartCutoff A c :=
    { frameIndex := P.input.frameIndex
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.1.1.2⟩ }
  let K₀ : AtlasChartCutoff B c :=
    { frameIndex := P.output.frameIndex
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.1.2⟩ }
  let H₀ : AtlasChartCutoff C c :=
    { frameIndex := Q.output.frameIndex
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.2.2⟩ }
  obtain ⟨p, Tp, Vp, hp, hVp, hKVp, hVpD, hplower, hTp, hTpaction, hTpK⟩ :=
    P₁.exists_supported_localized_symbol c P.chart_mem_atlas D₀ K₀ rfl
      (fun x hx ↦ ⟨⟨(hsβ (hP₁ hx)).1.1.1, (hsβ (hP₁ hx)).1.1.2⟩,
        (hsβ (hP₁ hx)).1.2⟩)
      ((Set.image_mono hP₁).trans honeρ)
      (fun z hz ↦ (hsρ hz).2.1)
  obtain ⟨qSym, Tq, Vq, hq, hVq, hKVq, hVqD, hqlower, hTq, hTqaction, hTqK⟩ :=
    Q₁.exists_supported_localized_symbol c P.chart_mem_atlas K₀ H₀ rfl
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
  let L : AtlasPseudodifferentialPiece A C (l + m) :=
    { chart := c
      chart_mem_atlas := P.chart_mem_atlas
      input := D₀
      output := H₀
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
  -- Round trips use the same plateau only on the actual support of each piece.
  have hinput (u : A.smoothSections) :
      P₁.toLinearMap (D₀.extend P.chart_mem_atlas (D₀.localize P.chart_mem_atlas u)) =
        P₁.toLinearMap u := by
    apply P₁.toLinearMap_support_properties.2
    intro x hx
    have hxβ := hP₁ ((Set.image_mono Set.subset_union_right) hx)
    rw [D₀.extend_localize_apply]
    have hdom : x ∈ c.source ∩ (A.chart D₀.frameIndex).baseSet :=
      ⟨(hsβ hxβ).1.1.1, (hsβ hxβ).1.1.2⟩
    simp only [dite_eq_left hdom, D₀, hρβ x hxβ, Complex.ofReal_one, one_smul]
  have hmiddle (u : A.smoothSections) :
      K₀.extend P.chart_mem_atlas (K₀.localize P.chart_mem_atlas (P₁.toLinearMap u)) =
        P₁.toLinearMap u := by
    apply Subtype.ext
    funext x
    rw [K₀.extend_localize_apply]
    by_cases hx : x ∈ P₁.chart.symm '' tsupport P₁.output.cutoff
    · have hxβ := hP₁ ((Set.image_mono Set.subset_union_left) hx)
      have hdom : x ∈ c.source ∩ (B.chart K₀.frameIndex).baseSet :=
        ⟨(hsβ hxβ).1.1.1, (hsβ hxβ).1.2⟩
      simp only [dite_eq_left hdom, K₀, hρβ x hxβ, Complex.ofReal_one, one_smul]
    · have hz := P₁.toLinearMap_support_properties.1 u x hx
      simp [hz]
  have houtput (v : B.smoothSections) :
      H₀.extend P.chart_mem_atlas (H₀.localize P.chart_mem_atlas (Q₁.toLinearMap v)) =
        Q₁.toLinearMap v := by
    apply Subtype.ext
    funext x
    rw [H₀.extend_localize_apply]
    by_cases hx : x ∈ Q₁.chart.symm '' tsupport Q₁.output.cutoff
    · have hxβ := hQ₁ ((Set.image_mono Set.subset_union_left) hx)
      have hdom : x ∈ c.source ∩ (C.chart H₀.frameIndex).baseSet :=
        ⟨(hsβ hxβ).1.1.1, (hsβ hxβ).2.2⟩
      simp only [dite_eq_left hdom, H₀, hρβ x hxβ, Complex.ofReal_one, one_smul]
    · have hz := Q₁.toLinearMap_support_properties.1 v x hx
      simp [hz]
  have hL : L.toLinearMap = Q₁.toLinearMap.comp P₁.toLinearMap := by
    apply LinearMap.ext
    intro u
    have hpaction := SchwartzMap.ext (hTpaction (D₀.localize P.chart_mem_atlas u))
    change H₀.extend P.chart_mem_atlas (Tq (Tp (D₀.localize P.chart_mem_atlas u))) = _
    rw [hpaction]
    have hqaction := SchwartzMap.ext
      (hTqaction (K₀.localize P.chart_mem_atlas
        (P₁.toLinearMap (D₀.extend P.chart_mem_atlas (D₀.localize P.chart_mem_atlas u)))))
    rw [hqaction, hmiddle, hinput, houtput]
    rfl
  -- Restore the original composite. The two discarded terms have separated cutoffs.
  let Yχ := atlasSectionMul B (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  let Xβ := atlasSectionMul A (fun x ↦ (β x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hβ)
  let Zβ := atlasSectionMul C (fun x ↦ (β x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hβ)
  let X₀ := P.cutoff χ (fun _ ↦ 1) hχ contMDiff_const
  have hX₀ : X₀.toLinearMap = Yχ.comp P.toLinearMap := by
    rw [AtlasPseudodifferentialPiece.toLinearMap_cutoff]
    have hone : atlasSectionMul A (fun _ ↦ (1 : ℂ))
        (Complex.ofRealCLM.contMDiff.comp contMDiff_const) = LinearMap.id := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change (1 : ℂ) • u.val x = u.val x
      rw [one_smul]
    simp only [Complex.ofReal_one, hone, LinearMap.comp_id, Yχ]
  have hcentral : Q.toLinearMap.comp (Yχ.comp (Yχ.comp P.toLinearMap)) =
      Q.toLinearMap.comp P.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Q.toLinearMap_support_properties.2
    intro x hxQ
    by_cases hxP : x ∈ KP
    · change (χ x : ℂ) • ((χ x : ℂ) • (P.toLinearMap u).val x) = _
      rw [hχK x ⟨hxP, hxQ⟩, Complex.ofReal_one, one_smul, one_smul]
    · have hzero := P.toLinearMap_support_properties.1 u x hxP
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
      atlasSectionMul A (fun x ↦ ((1 - β x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hβ)) = LinearMap.id - Xβ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change ((1 - β x : ℝ) : ℂ) • u.val x = u.val x - (β x : ℂ) • u.val x
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hminusG :
      atlasSectionMul C (fun x ↦ ((1 - β x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hβ)) = LinearMap.id - Zβ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change ((1 - β x : ℝ) : ℂ) • u.val x = u.val x - (β x : ℂ) • u.val x
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hQoff : IsAtlasSmoothingOperator B C ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ)) := by
    have h := Q.isAtlasSmoothingOperator_cutoff_of_mul_eq_zero
      (fun x ↦ 1 - β x) χ (contMDiff_const.sub hβ) hχ hzleft
    rwa [hminusG] at h
  have hPoff : IsAtlasSmoothingOperator A B (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ))) := by
    have h := P.isAtlasSmoothingOperator_cutoff_of_mul_eq_zero
      χ (fun x ↦ 1 - β x) hχ (contMDiff_const.sub hβ) hzright
    rwa [hminusE] at h
  have hX₀pdo (R₀ : AtlasPseudodifferentialPiece A B m) :
      IsAtlasPseudodifferentialOperator A B m R₀.toLinearMap := by
    refine ⟨1, fun _ ↦ R₀, ?_⟩
    rw [Fin.sum_univ_one, sub_self]
    intro D H s t
    refine ⟨0, ?_⟩
    intro u
    change 0 = H.smoothToSobolev t 0
    exact (map_zero (H.smoothToSobolev t)).symm
  have hQ₁pdo (R₀ : AtlasPseudodifferentialPiece B C l) :
      IsAtlasPseudodifferentialOperator B C l R₀.toLinearMap := by
    refine ⟨1, fun _ ↦ R₀, ?_⟩
    rw [Fin.sum_univ_one, sub_self]
    intro D H s t
    refine ⟨0, ?_⟩
    intro u
    change 0 = H.smoothToSobolev t 0
    exact (map_zero (H.smoothToSobolev t)).symm
  -- Fix the atlas and order parameters before instantiating either ideal with the actual maps.
  have hleftIdeal := IsAtlasSmoothingOperator.comp_isAtlasPseudodifferentialOperator
    (n := n) (M := M) (E := E) (F := F) (G := G)
    (A := A) (B := B) (C := C) (m := m)
  have hrightIdeal := IsAtlasPseudodifferentialOperator.comp_isAtlasSmoothingOperator
    (n := n) (M := M) (E := E) (F := F) (G := G)
    (A := A) (B := B) (C := C) (l := l)
  have hX₀proof : IsAtlasPseudodifferentialOperator A B m X₀.toLinearMap := hX₀pdo X₀
  have hQ₁proof : IsAtlasPseudodifferentialOperator B C l Q₁.toLinearMap := hQ₁pdo Q₁
  have hleftQ := hleftIdeal ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ))
  have hleftP := hleftQ X₀.toLinearMap
  have hleftSmoothing := hleftP hQoff
  have hleft := hleftSmoothing hX₀proof
  have hrightQ := hrightIdeal Q₁.toLinearMap
  have hrightP := hrightQ (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ)))
  have hrightPdo := hrightP hQ₁proof
  have hright := hrightPdo hPoff
  have hsumEq :
      ((LinearMap.id - Zβ).comp (Q.toLinearMap.comp Yχ)).comp X₀.toLinearMap +
        Q₁.toLinearMap.comp (Yχ.comp (P.toLinearMap.comp (LinearMap.id - Xβ))) =
      Q.toLinearMap.comp P.toLinearMap - L.toLinearMap := by
    rw [hL, hX₀]
    simp only [P₁, Q₁, AtlasPseudodifferentialPiece.toLinearMap_cutoff]
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
  have hrem : IsAtlasSmoothingOperator A C (Q.toLinearMap.comp P.toLinearMap - L.toLinearMap) := by
    rw [← hsumEq]
    intro D H s t
    obtain ⟨U, hU⟩ := hleft D H s t
    obtain ⟨V, hV⟩ := hright D H s t
    refine ⟨U + V, fun u ↦ ?_⟩
    rw [add_apply, hU, hV, ← map_add]
    rfl
  -- Every auxiliary factor is one on the support of the original principal product.
  have hPcut (x : M) (ξ) : P₁.globalSymbolFunction x ξ =
      ((χ x * β x : ℝ) : ℂ) • P.globalSymbolFunction x ξ := by
    by_cases hx : x ∈ DP
    · dsimp only [DP] at hx
      simp only [P₁, AtlasPseudodifferentialPiece.cutoff, AtlasChartCutoff.mulSmooth,
        AtlasPseudodifferentialPiece.globalSymbolFunction, dite_eq_left hx,
        P.chart.left_inv hx.1.1]
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · dsimp only [DP] at hx
      simp [P₁, AtlasPseudodifferentialPiece.cutoff, AtlasChartCutoff.mulSmooth,
        AtlasPseudodifferentialPiece.globalSymbolFunction, hx]
  have hQcut (x : M) (ξ) : Q₁.globalSymbolFunction x ξ =
      ((β x * χ x : ℝ) : ℂ) • Q.globalSymbolFunction x ξ := by
    by_cases hx : x ∈ DQ
    · dsimp only [DQ] at hx
      simp only [Q₁, AtlasPseudodifferentialPiece.cutoff, AtlasChartCutoff.mulSmooth,
        AtlasPseudodifferentialPiece.globalSymbolFunction, dite_eq_left hx,
        Q.chart.left_inv hx.1.1]
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · dsimp only [DQ] at hx
      simp [Q₁, AtlasPseudodifferentialPiece.cutoff, AtlasChartCutoff.mulSmooth,
        AtlasPseudodifferentialPiece.globalSymbolFunction, hx]
  have hprod : atlasSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction =
      atlasSymbolComp Q.globalSymbolFunction P.globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ K
    · have hxχ : x ∈ tsupport χ := by
        apply subset_tsupport
        change χ x ≠ 0
        rw [hχK x hx]
        exact one_ne_zero
      simp [atlasSymbolComp, hPcut, hQcut, hχK x hx, hβχ x hxχ]
    · by_cases hxP : x ∈ KP
      · have hxQ : x ∉ KQ := fun h ↦ hx ⟨hxP, h⟩
        have hzero := Q.globalSymbolFunction_eq_zero x
          (fun h ↦ hxQ ((Set.image_mono Set.inter_subset_right) h)) ξ
        simp [atlasSymbolComp, hQcut, hzero]
      · have hzero := P.globalSymbolFunction_eq_zero x
          (fun h ↦ hxP ((Set.image_mono Set.inter_subset_left) h)) ξ
        simp [atlasSymbolComp, hPcut, hzero]
  let V := Vp ∩ Vq
  have hV : IsOpen V := hVp.inter hVq
  have hKV : tsupport ρ ⊆ V := fun z hz ↦ ⟨hKVp hz, hKVq hz⟩
  let ap := atlasGlobalSymbolInChart A B P₁.globalSymbolFunction c D₀.frameIndex K₀.frameIndex
  let aq := atlasGlobalSymbolInChart B C Q₁.globalSymbolFunction c K₀.frameIndex H₀.frameIndex
  have haq : IsSymbol V l aq :=
    (Q₁.isAtlasGlobalSymbol_globalSymbolFunction c P.chart_mem_atlas
      K₀.frameIndex H₀.frameIndex).restrict
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
  let R : AtlasPseudodifferentialPiece A C (l + m - 1) :=
    { chart := c
      chart_mem_atlas := P.chart_mem_atlas
      input := D₀
      output := H₀
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
      L.globalSymbolFunction - atlasSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction =
        R.globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ c.symm '' tsupport ρ
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzc : z ∈ c.target := (hsρ hz).1
      have hxD : c.symm z ∈ D := (hsρ hz).2
      have hxA : c.symm z ∈ (A.chart D₀.frameIndex).baseSet := hxD.1.1.2
      have hxB : c.symm z ∈ (B.chart K₀.frameIndex).baseSet := hxD.1.2
      have hxC : c.symm z ∈ (C.chart H₀.frameIndex).baseSet := hxD.2.2
      have hxc : c.symm z ∈ c.source := c.map_target hzc
      let η := covectorInChart c (c.symm z) ξ
      have hscale : ((ρ z * ρ z : ℝ) : ℂ) • symbolComp aq ap z η =
          symbolComp aq ap z η := by
        by_cases hβx : c.symm z ∈ tsupport β
        · have hρz : ρ z = 1 := by simpa only [c.right_inv hzc] using hρβ (c.symm z) hβx
          rw [hρz, one_mul, Complex.ofReal_one, one_smul]
        · have hzero : aq z η = 0 := by
            simp [aq, atlasGlobalSymbolInChart, hQzero (c.symm z) hβx]
          simp [symbolComp, hzero]
      -- All coordinate conversions below use these same original outer frames and covector.
      have hLcoord : atlasGlobalSymbolInChart A C L.globalSymbolFunction c
          D₀.frameIndex H₀.frameIndex z η = ((ρ z * ρ z : ℝ) : ℂ) • s z η := by
        ext v
        simp [atlasGlobalSymbolInChart, AtlasPseudodifferentialPiece.globalSymbolFunction,
          L, D₀, H₀, hxA, hxC, hxc, c.right_inv hzc,
          covectorInChart_covectorFromChart c P.chart_mem_atlas _ hxc,
          EuclideanSpace.equiv, PiLp.continuousLinearEquiv]
      have hRcoord : atlasGlobalSymbolInChart A C R.globalSymbolFunction c
          D₀.frameIndex H₀.frameIndex z η = ((ρ z * ρ z : ℝ) : ℂ) • b z η := by
        ext v
        simp [atlasGlobalSymbolInChart, AtlasPseudodifferentialPiece.globalSymbolFunction,
          R, D₀, H₀, hxA, hxC, hxc, c.right_inv hzc,
          covectorInChart_covectorFromChart c P.chart_mem_atlas _ hxc,
          EuclideanSpace.equiv, PiLp.continuousLinearEquiv]
      have hprodcoord : atlasGlobalSymbolInChart A C
          (atlasSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction)
          c D₀.frameIndex H₀.frameIndex z η = symbolComp aq ap z η := by
        ext v
        simp [aq, ap, atlasGlobalSymbolInChart, atlasSymbolComp, symbolComp,
          hxA, hxB, hxC, EuclideanSpace.equiv, PiLp.continuousLinearEquiv]
      have hcoord :
          atlasGlobalSymbolInChart A C L.globalSymbolFunction c D₀.frameIndex H₀.frameIndex z η -
            atlasGlobalSymbolInChart A C
              (atlasSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction)
              c D₀.frameIndex H₀.frameIndex z η =
          atlasGlobalSymbolInChart A C R.globalSymbolFunction c
            D₀.frameIndex H₀.frameIndex z η := by
        rw [hLcoord, hRcoord, hprodcoord]
        simp only [b, zeroExtendedSymbol, ite_eq_left (hKV hz), (honeγ z).mp hz,
          Complex.ofReal_one, one_smul, Pi.sub_apply, smul_sub, hscale]
      apply LinearMap.ext
      intro v
      let eA := EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ
      let eC := EuclideanSpace.equiv (Fin (C.rank H₀.frameIndex)) ℂ
      let v₀ := eA.symm ((A.frameLinearEquiv D₀.frameIndex (c.symm z) hxA) v)
      have hrecover (a : AtlasSymbolFunction (n := n) E G) :
          (C.frameLinearEquiv H₀.frameIndex (c.symm z) hxC).symm
            (eC (atlasGlobalSymbolInChart A C a c D₀.frameIndex H₀.frameIndex z η v₀)) =
          a (c.symm z) ξ v := by
        simp only [atlasGlobalSymbolInChart, hxA, hxC, and_self, dite_true]
        rw [show covectorFromChart c (c.symm z) η = ξ from
          covectorFromChart_covectorInChart c P.chart_mem_atlas _ hxc ξ]
        change (C.frameLinearEquiv H₀.frameIndex (c.symm z) hxC).symm
          (eC (eC.symm ((C.frameLinearEquiv H₀.frameIndex (c.symm z) hxC)
            (a (c.symm z) ξ
              ((A.frameLinearEquiv D₀.frameIndex (c.symm z) hxA).symm (eA v₀)))))) = _
        rw [eC.apply_symm_apply, LinearEquiv.symm_apply_apply]
        simp only [v₀, eA.apply_symm_apply, LinearEquiv.symm_apply_apply]
      have hv := congrArg (fun T : EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)) →L[ℂ]
          EuclideanSpace ℂ (Fin (C.rank H₀.frameIndex)) ↦
        (C.frameLinearEquiv H₀.frameIndex (c.symm z) hxC).symm (eC (T v₀))) hcoord
      simpa only [sub_apply, map_sub, hrecover, Pi.sub_apply, LinearMap.sub_apply] using hv
    · have hLzero := L.globalSymbolFunction_eq_zero x
        (by simpa only [L, D₀, H₀, Set.inter_self] using hx) ξ
      have hRzero := R.globalSymbolFunction_eq_zero x
        (by simpa only [R, D₀, H₀, Set.inter_self] using hx) ξ
      have hxβ : x ∉ tsupport β := by
        intro hxβ
        apply hx
        exact ⟨c x, subset_tsupport _ (by change ρ (c x) ≠ 0; rw [hρβ x hxβ]; exact one_ne_zero),
          c.left_inv (hbaseβ hxβ)⟩
      simp only [Pi.sub_apply, hLzero, hRzero, atlasSymbolComp, hQzero x hxβ ξ,
        LinearMap.zero_comp, sub_zero]
  refine ⟨L, hrem, ?_⟩
  apply (atlasGlobalPrincipalSymbolClass_eq_iff A C (l + m) _ _).mpr
  change IsAtlasGlobalSymbol A C (l + m - 1)
    (L.globalSymbolFunction - atlasSymbolComp Q.globalSymbolFunction P.globalSymbolFunction)
  rw [← hprod, hglobalDifference]
  exact R.isAtlasGlobalSymbol_globalSymbolFunction

/-- One finite family realizes both the composite section map and its principal class. -/
private theorem AtlasPseudodifferentialOperator.exists_representation_comp {l m : ℝ}
    (Q : AtlasPseudodifferentialOperator B C l)
    (P : AtlasPseudodifferentialOperator A B m) :
    ∃ (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A C (l + m)),
      IsAtlasSmoothingOperator A C
        (Q.toLinearMap.comp P.toLinearMap - ∑ j, (L j).toLinearMap) ∧
      atlasGlobalPrincipalSymbolClass A C (l + m) (∑ j, (L j).globalSymbol) =
        atlasGlobalPrincipalSymbolComp Q.principalSymbol P.principalSymbol := by
  classical
  -- Keep the two original representations and one chosen piece for each ordered pair.
  obtain ⟨N, J, hJ⟩ := Q.isPseudodifferentialOperator
  obtain ⟨N', K, hK⟩ := P.isPseudodifferentialOperator
  choose R hR hclass using fun i j ↦ (J i).exists_piece_comp (K j)
  let Q₀ := ∑ i, (J i).toLinearMap
  let P₀ := ∑ j, (K j).toLinearMap
  have hQ₀ : IsAtlasPseudodifferentialOperator B C l Q₀ := by
    refine ⟨N, J, ?_⟩
    intro H H' s t
    refine ⟨0, ?_⟩
    intro u
    simp [Q₀]
  -- The original smoothing remainders remain smoothing under these actual maps.
  have hleft := IsAtlasSmoothingOperator.comp_isAtlasPseudodifferentialOperator
    (Q.toLinearMap - Q₀) P.toLinearMap hJ P.isPseudodifferentialOperator
  have hright := IsAtlasPseudodifferentialOperator.comp_isAtlasSmoothingOperator
    Q₀ (P.toLinearMap - P₀) hQ₀ hK
  -- Reindex the same pair family once for both its maps and its principal symbols.
  let e : Fin (Fintype.card (Fin N × Fin N')) ≃ Fin N × Fin N' :=
    (Fintype.equivFin (Fin N × Fin N')).symm
  let L (k : Fin (Fintype.card (Fin N × Fin N'))) := R (e k).1 (e k).2
  have hsumMap : (∑ k, (L k).toLinearMap) = ∑ i, ∑ j, (R i j).toLinearMap := by
    rw [← Fintype.sum_prod_type (fun ij : Fin N × Fin N' ↦
      (R ij.1 ij.2).toLinearMap)]
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  have hsumSymbol : (∑ k, (L k).globalSymbol) = ∑ i, ∑ j, (R i j).globalSymbol := by
    rw [← Fintype.sum_prod_type (fun ij : Fin N × Fin N' ↦
      (R ij.1 ij.2).globalSymbol)]
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  have hsumComp : Q₀.comp P₀ =
      ∑ i, ∑ j, (J i).toLinearMap.comp (K j).toLinearMap := by
    apply LinearMap.ext
    intro u
    simp only [Q₀, P₀, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_comm
  have hexpand : Q.toLinearMap.comp P.toLinearMap - ∑ k, (L k).toLinearMap =
      (Q.toLinearMap - Q₀).comp P.toLinearMap + Q₀.comp (P.toLinearMap - P₀) +
        ∑ i, ∑ j, ((J i).toLinearMap.comp (K j).toLinearMap - (R i j).toLinearMap) := by
    rw [hsumMap]
    simp only [Finset.sum_sub_distrib, LinearMap.sub_comp, LinearMap.comp_sub]
    rw [← hsumComp]
    abel
  refine ⟨Fintype.card (Fin N × Fin N'), L, ?_, ?_⟩
  · -- Finite sums of the specified bounded extensions realize the entire error map.
    rw [hexpand]
    intro H H' s t
    obtain ⟨Tleft, hTleft⟩ := hleft H H' s t
    obtain ⟨Tright, hTright⟩ := hright H H' s t
    choose T hT using fun i j ↦ hR i j H H' s t
    refine ⟨Tleft + Tright + ∑ i, ∑ j, T i j, ?_⟩
    intro u
    simp only [add_apply, sum_apply,
      hTleft, hTright, hT, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
  · -- Take the class of exactly that same finite family and distribute fiberwise composition.
    rw [hsumSymbol]
    simp only [map_sum, hclass]
    rw [Q.principalSymbol_eq_of_representation N J hJ,
      P.principalSymbol_eq_of_representation N' K hK,
      atlasGlobalPrincipalSymbolComp_class]
    simp only [← map_sum]
    congr 1
    apply Subtype.ext
    funext x ξ
    apply LinearMap.ext
    intro v
    simp only [atlasGlobalSymbolSpaceComp, atlasSymbolComp, Submodule.coe_sum,
      Finset.sum_apply, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    exact Finset.sum_comm


/-- SG III.3.17(iii): the actual composite has the sum of the two PDO orders. -/
theorem IsAtlasPseudodifferentialOperator.comp {l m : ℝ}
    (Q : B.smoothSections →ₗ[ℂ] C.smoothSections)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (hQ : IsAtlasPseudodifferentialOperator B C l Q)
    (hP : IsAtlasPseudodifferentialOperator A B m P) :
    IsAtlasPseudodifferentialOperator A C (l + m) (Q.comp P) := by
  /- Apply the shared finite-representation theorem to these same two
  section maps. Its proof composes each ordered pair of local pieces in
  one common chart, using nested cutoffs and the same intermediate frame.
  The two smoothing ideal properties retain every off-diagonal term and
  every original smoothing remainder. A single flattened finite family
  then represents the full composite and its principal product. Here its
  section-map specification gives the required order-l+m membership. -/
  obtain ⟨N, L, hL, _⟩ :=
    (AtlasPseudodifferentialOperator.exists_representation_comp
      (⟨Q, hQ⟩ : AtlasPseudodifferentialOperator B C l)
      (⟨P, hP⟩ : AtlasPseudodifferentialOperator A B m))
  exact ⟨N, L, hL⟩

namespace AtlasPseudodifferentialOperator

variable {l m : ℝ} (Q : AtlasPseudodifferentialOperator B C l)
  (P : AtlasPseudodifferentialOperator A B m)

/-- The original composite action, equipped with its derived PDO property. -/
def comp : AtlasPseudodifferentialOperator A C (l + m) where
  toLinearMap := Q.toLinearMap.comp P.toLinearMap
  isPseudodifferentialOperator :=
    IsAtlasPseudodifferentialOperator.comp Q.toLinearMap P.toLinearMap
      Q.isPseudodifferentialOperator P.isPseudodifferentialOperator

/-- The principal quotient of the actual composite is the original fiberwise quotient product. -/
theorem principalSymbol_comp :
    (Q.comp P).principalSymbol =
      atlasGlobalPrincipalSymbolComp Q.principalSymbol P.principalSymbol := by
  /- Use the same finite-representation theorem that establishes
  composition. It supplies one family with both the actual composite
  section-map specification and the original ordered principal product.
  The principalSymbol_eq_of_representation formula for Q.comp P identifies
  its selected class with that family's class; the supplied comparison
  then gives the desired product. No new representative is selected. -/
  obtain ⟨N, L, hL, hclass⟩ := Q.exists_representation_comp P
  exact ((Q.comp P).principalSymbol_eq_of_representation N L hL).trans hclass

/-- The bounded realizations of the same two section maps compose on the original completions. -/
theorem sobolevExtension_comp (L : AtlasBundlePresentation A)
    (K : AtlasBundlePresentation B) (H : AtlasBundlePresentation C) (s : ℝ) :
    let horder : (s - m) - l = s - (l + m) := by ring
    (Q.comp P).sobolevExtension L H s =
      cast (congrArg (fun t : ℝ ↦ L.SobolevSpace s →L[ℂ] H.SobolevSpace t) horder)
        ((Q.sobolevExtension K H (s - m)).comp (P.sobolevExtension L K s)) := by
  /- Stage 1: identify the two displayed target-order expressions by
  their arithmetic equality. This cast changes only the order index;
  the original presentation H and its concrete completion remain fixed.
  Stage 2: on every original smooth input u, the two dense-image
  specifications identify the right side with the inclusion of Q(Pu).
  The left side has exactly that same action by the definition of comp.
  Stage 3: both maps are continuous on L.SobolevSpace s. Density of
  its original smooth image extends equality to the full completion.
  The intermediate presentation is the same K in both factors; no
  independently chosen extension, Sobolev inclusion or norm comparison
  replaces either map. All real input and operator orders are retained. -/
  -- Equality induction keeps the same target completion and original smooth section action.
  have hext (t : ℝ) (h : t = s - (l + m))
      (T : L.SobolevSpace s →L[ℂ] H.SobolevSpace t)
      (hT : ∀ u : A.smoothSections,
        T (L.smoothToSobolev s u) = H.smoothToSobolev t (Q.toLinearMap (P.toLinearMap u))) :
      (Q.comp P).sobolevExtension L H s =
        cast (congrArg (fun a : ℝ ↦ L.SobolevSpace s →L[ℂ] H.SobolevSpace a) h) T := by
    subst t
    -- Density compares two maps into that fixed original completion.
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      ((Q.comp P).sobolevExtension L H s).continuous T.continuous
    funext u
    simp only [Function.comp_apply,
      AtlasPseudodifferentialOperator.sobolevExtension_smoothToSobolev, hT]
    rfl
  -- Both factors use K, so their defining actions compose on each original smooth section.
  apply hext ((s - m) - l) (by ring)
    ((Q.sobolevExtension K H (s - m)).comp (P.sobolevExtension L K s))
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    AtlasPseudodifferentialOperator.sobolevExtension_smoothToSobolev]


end AtlasPseudodifferentialOperator

end AtiyahSinger
