/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolEllipticity
public import AtiyahSinger.Analysis.GlobalEllipticSymbol

/-!
# Global inverse bounds and a first inverse symbol

Public module ID: M0671.

Compact-local quantitative ellipticity in every valid chart and frame.
This is the coordinate formulation of SG III.4.7. It uses frame norms, not the
unrelated norm inherited by a raw tangent-space type. A finite cover of a closed
base gives one inverse symbol with both pointwise errors of every order.
The metric formulation and its formal model comparison remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Quantitative full-symbol ellipticity in every valid cotangent chart and bundle frame. -/
def IsEllipticFullGlobalSymbol (m : ℝ) (a : GlobalSymbolFunction (n := n) E F) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
          (π (EuclideanSpace ℂ (Fin r)) E))
        (f : Trivialization (EuclideanSpace ℂ (Fin q))
          (π (EuclideanSpace ℂ (Fin q)) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        IsEllipticFullSymbol (symbolChartDomain E F c e f) m
          (globalSymbolInChart E F a c e f)

variable {E F}

/-- The coordinate inverse condition is stable under a strictly lower global symbol order. -/
theorem IsEllipticFullGlobalSymbol.add_lowerOrder {m : ℝ}
    {a b : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a)
    (ε : ℝ) (hε : 0 < ε) (hb : IsGlobalSymbol (r := r) (q := q) E F (m - ε) b) :
    IsEllipticFullGlobalSymbol (r := r) (q := q) E F m (a + b) := by
  /- In each valid chart and pair of frames the actual Hom sum is the sum of
  the local matrices. Apply the local perturbation theorem on every compact set
  in the common chart domain. Quantify over the original charts and frames. -/
  intro c hc e f _ _
  -- Transport the actual fiberwise sum through this same pair of frames.
  rw [globalSymbolInChart_add]
  exact (ha c hc e f).add_lowerOrder ε hε (hb c hc e f)

/-- Every representative of a principal class has the same quantitative ellipticity condition. -/
theorem isEllipticFullGlobalSymbol_iff_of_class_eq {m : ℝ}
    (a b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hab : globalPrincipalSymbolClass E F m a = globalPrincipalSymbolClass E F m b) :
    IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val ↔
      IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val := by
  /- The genuine quotient equality says a-b is globally of order m-1.
  In each chart use the local equivalence under a one-order perturbation.
  This prevents ellipticity of a PDO from depending on a selected representative. -/
  have hsub := (globalPrincipalSymbolClass_eq_iff E F m a b).mp hab
  -- Quotient equality gives the same one-order difference in every valid chart.
  have hlocal (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      IsEllipticFullSymbol (symbolChartDomain E F c e f) m
          (globalSymbolInChart E F a.val c e f) ↔
        IsEllipticFullSymbol (symbolChartDomain E F c e f) m
          (globalSymbolInChart E F b.val c e f) := by
    apply isEllipticFullSymbol_iff_of_isSymbol_sub
    have hcoord : globalSymbolInChart E F (a.val - b.val) c e f =
        globalSymbolInChart E F a.val c e f - globalSymbolInChart E F b.val c e f := by
      ext z η v
      simp [globalSymbolInChart]
    rw [← hcoord]
    exact hsub c hc e f
  constructor
  · intro ha c hc e f _ _
    exact (hlocal c hc e f).mp (ha c hc e f)
  · intro hb c hc e f _ _
    exact (hlocal c hc e f).mpr (hb c hc e f)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hE hF in
/-- The existing homogeneous realization satisfies the general inverse-bound definition exactly. -/
theorem isEllipticFullGlobalSymbol_regularizedSymbol_iff
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F) (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) :
    IsEllipticFullGlobalSymbol (r := r) (q := q) E F m
        (A.regularizedSymbol m a hs hh).val ↔ IsEllipticGlobalSymbol E F a := by
  /- On every compact coordinate set the regularization equals the homogeneous
  data above a uniform radius. Apply the local homogeneous inverse estimate.
  Conversely choose frames at x and a singleton compact base set, dilate a
  nonzero covector into that region, and use positive homogeneity to recover
  invertibility at the original covector. Atlas chart derivatives are isomorphisms;
  no smooth cotangent metric or invertibility at ξ=0 is required. -/
  classical
  have hcov_ne (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
      (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) :
      covectorFromChart c (c.symm z) η ≠ 0 := by
    intro hzero
    have h := covectorInChart_covectorFromChart c hc (c.symm z) (c.map_target hz) η
    rw [hzero] at h
    have hzero' : covectorInChart c (c.symm z) 0 = 0 := by ext u; rfl
    exact hη (h.symm.trans hzero')
  -- Recovery at high frequency compares the given presentation to the standard local cutoff.
  have hcomparison (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      IsEllipticFullSymbol (symbolChartDomain E F c e f) m
          (globalSymbolInChart E F (A.regularizedSymbol m a hs hh).val c e f) ↔
        IsEllipticSymbol (symbolChartDomain E F c e f)
          (globalSymbolInChart E F a c e f) := by
    rw [← isEllipticFullSymbol_frequencyCutoffSymbol_iff (isOpen_symbolChartDomain E F c e f)
      (globalSymbolInChart E F a c e f) (hs c hc e f) (hh.in_chart c hc e f)]
    have heq (K : Set (EuclideanSpace ℝ (Fin n))) (hKU : K ⊆ symbolChartDomain E F c e f)
        (hK : IsCompact K) : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
          globalSymbolInChart E F (A.regularizedSymbol m a hs hh).val c e f z η =
            frequencyCutoffSymbol (globalSymbolInChart E F a c e f) z η := by
      obtain ⟨R, hR, hbound⟩ :=
        A.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K hK hKU
      refine ⟨max R 1, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
      intro z hz η hη
      rw [frequencyCutoffSymbol_eq_of_one_le_norm _ z η ((le_max_right _ _).trans hη)]
      exact hbound z hz η ((le_max_left _ _).trans hη)
    constructor
    · intro hp K hKU hK
      obtain ⟨R, C, hR, hC, hbound⟩ := hp K hKU hK
      obtain ⟨S, hS, hsame⟩ := heq K hKU hK
      refine ⟨max R S, C, lt_of_lt_of_le hR (le_max_left _ _), hC, ?_⟩
      intro z hz η hη
      rw [← hsame z hz η ((le_max_right _ _).trans hη)]
      exact hbound z hz η ((le_max_left _ _).trans hη)
    · intro hp K hKU hK
      obtain ⟨R, C, hR, hC, hbound⟩ := hp K hKU hK
      obtain ⟨S, hS, hsame⟩ := heq K hKU hK
      refine ⟨max R S, C, lt_of_lt_of_le hR (le_max_left _ _), hC, ?_⟩
      intro z hz η hη
      rw [hsame z hz η ((le_max_right _ _).trans hη)]
      exact hbound z hz η ((le_max_left _ _).trans hη)
  -- Each valid pair of frames preserves bijectivity of the same original fiber map.
  have hframes (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f]
      (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F c e f)
      (η : EuclideanSpace ℝ (Fin n)) :
      Function.Bijective (globalSymbolInChart E F a c e f z η) ↔
        Function.Bijective (a (c.symm z) (covectorFromChart c (c.symm z) η)) := by
    unfold globalSymbolInChart
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hz.2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hz.1.2]
    let input := (e.continuousLinearEquivAt ℂ (c.symm z) hz.1.2).symm
    let output := f.continuousLinearEquivAt ℂ (c.symm z) hz.2
    change Function.Bijective (fun v ↦ output
      (a (c.symm z) (covectorFromChart c (c.symm z) η) (input v))) ↔ _
    constructor
    · intro h
      have h' := output.symm.bijective.comp (h.comp input.symm.bijective)
      simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.symm_apply_apply] using h'
    · intro h
      exact output.bijective.comp (h.comp input.bijective)
  constructor
  · intro he x ξ hξ
    -- A designated chart and frame pair recover the original point and cotangent vector.
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hc := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have heBase : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hfBase : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    have hz : c x ∈ symbolChartDomain E F c e f :=
      ⟨⟨c.map_source hx, by simpa only [Set.mem_preimage, c.left_inv hx] using heBase⟩,
        by simpa only [Set.mem_preimage, c.left_inv hx] using hfBase⟩
    have hη : covectorInChart c x ξ ≠ 0 := by
      intro hzero
      have h := covectorFromChart_covectorInChart c hc x hx ξ
      rw [hzero] at h
      have hz' : covectorFromChart c x 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (mfderiv _ _ c x v) = 0
        exact inner_zero_left _
      exact hξ (h.symm.trans hz')
    have hlocal := (hcomparison c hc e f).mp (he c hc e f)
      (c x) hz (covectorInChart c x ξ) hη
    have hmap := (hframes c e f (c x) hz (covectorInChart c x ξ)).mp hlocal
    have hxmap : Function.Bijective (a x (covectorFromChart c x (covectorInChart c x ξ))) :=
      (congrArg (fun z : M ↦ Function.Bijective
        (a z (covectorFromChart c z (covectorInChart c x ξ)))) (c.left_inv hx)).mp hmap
    rwa [covectorFromChart_covectorInChart c hc x hx ξ] at hxmap
  · intro he c hc e f _ _
    apply (hcomparison c hc e f).mpr
    intro z hz η hη
    apply (hframes c e f z hz η).mpr
    exact he (c.symm z) (covectorFromChart c (c.symm z) η)
      (hcov_ne c hc z hz.1.1 η hη)

set_option maxHeartbeats 1500000 in
-- The finite local assembly and both all-order residuals retain one common inverse symbol.
include hM hT hE hF in
/-- One global inverse symbol has both pointwise products equal to identity modulo every order. -/
theorem exists_inverse_globalSymbol_of_isEllipticFullGlobalSymbol
    [SecondCountableTopology M] [CompactSpace M] {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (he : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    ∃ b : globalSymbolSpace (n := n) (r := q) (q := r) F E (-m),
      ∀ l : ℝ,
        IsGlobalSymbol (r := r) (q := r) E E l
          (globalSymbolComp b.val a.val - globalSymbolId E) ∧
        IsGlobalSymbol (r := q) (q := q) F F l
          (globalSymbolComp a.val b.val - globalSymbolId F) := by
  set_option maxSynthPendingDepth 30 in
  open Filter Set in
  open scoped Topology in
  /- Construct inverse symbols in the fixed finite patch family and transport them
  through the actual reversed frames. Uniform lower bounds for cotangent chart
  changes give recovery of the same fiber inverse on each requested compact set.
  Both pointwise errors then vanish at high frequency on compact neighborhoods;
  their smoothness supplies every lower symbol order. -/
  classical
  let A : QuantizationPresentation (n := n) (r := q) (q := r) F E :=
    Classical.choice nonempty_quantizationPresentation
  let D (j : Fin A.size) := symbolChartDomain E F (A.patch j).chart
    (A.patch j).output.frame (A.patch j).input.frame
  have hD (j : Fin A.size) : IsOpen (D j) := isOpen_symbolChartDomain E F
    (A.patch j).chart (A.patch j).output.frame (A.patch j).input.frame
  have hinput (j : Fin A.size) : tsupport (A.patch j).input.cutoff ⊆ D j := by
    intro z hz
    exact ⟨⟨((A.patch j).input.support_subset hz).1,
      (A.patch j).input_support_in_output_frame hz⟩,
      ((A.patch j).input.support_subset hz).2⟩
  have houtput (j : Fin A.size) : tsupport (A.patch j).output.cutoff ⊆ D j := by
    intro z hz
    exact ⟨(A.patch j).output.support_subset hz,
      (A.patch j).output_support_in_input_frame hz⟩
  let (j : Fin A.size) : MemTrivializationAtlas (A.patch j).input.frame :=
    (A.patch j).input.frame_mem_atlas
  let (j : Fin A.size) : MemTrivializationAtlas (A.patch j).output.frame :=
    (A.patch j).output.frame_mem_atlas
  -- Invert in each original chart, retaining one high-frequency radius on its input support.
  have hlocal (j : Fin A.size) : ∃ p : SymbolFunction n q r, IsSymbol (D j) (-m) p ∧
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ tsupport (A.patch j).input.cutoff, ∀ η, R ≤ ‖η‖ →
        p z η = (globalSymbolInChart E F a.val (A.patch j).chart
          (A.patch j).output.frame (A.patch j).input.frame z η).inverse := by
    let := (A.patch j).input.frame_mem_atlas
    let := (A.patch j).output.frame_mem_atlas
    obtain ⟨p, hp, hpeq⟩ := exists_inverse_symbol_of_isEllipticFullSymbol (hD j)
      (globalSymbolInChart E F a.val (A.patch j).chart
        (A.patch j).output.frame (A.patch j).input.frame)
      (a.property (A.patch j).chart (A.patch j).chart_mem_atlas
        (A.patch j).output.frame (A.patch j).input.frame)
      (he (A.patch j).chart (A.patch j).chart_mem_atlas
        (A.patch j).output.frame (A.patch j).input.frame)
    obtain ⟨R, hR, hpeq⟩ := hpeq _ (hinput j) (A.patch j).input.compact_support
    exact ⟨p, hp, R, hR, hpeq⟩
  choose p hp R hR hpeq using hlocal
  let p' (j : Fin A.size) := zeroExtendedSymbol (D j) (A.patch j).output.cutoff (p j)
  have hp' (j : Fin A.size) : IsSymbol univ (-m) (p' j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) (-m) (A.patch j).output.cutoff
      (A.patch j).output.smooth_cutoff (A.patch j).output.compact_support (houtput j)
      (p j) (hp j)
  have hcp' (j : Fin A.size) : HasCompactSupport (p' j) :=
    hasCompactSupport_zeroExtendedSymbol _ _ _ (A.patch j).output.compact_support
  let L (j : Fin A.size) : PseudodifferentialPiece (n := n) (r := q) (q := r) F E (-m) :=
    { chart := (A.patch j).chart
      chart_mem_atlas := (A.patch j).chart_mem_atlas
      input := (A.patch j).input
      output := (A.patch j).output
      input_support_in_output_frame := (A.patch j).input_support_in_output_frame
      output_support_in_input_frame := (A.patch j).output_support_in_input_frame
      operator := quantizeSchwartz (-m) (p' j) (hp' j) (hcp' j)
      symbol := p' j
      isSymbol := hp' j
      operator_apply := quantizeSchwartz_apply (-m) (p' j) (hp' j) (hcp' j) }
  let b : globalSymbolSpace (n := n) (r := q) (q := r) F E (-m) := ∑ j, (L j).globalSymbol
  -- A contributing piece is its original partition weight times the actual fiber inverse.
  have hpiece (j : Fin A.size) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
      (hη : (A.patch j).weight x ≠ 0 → R j ≤ ‖covectorInChart (A.patch j).chart x ξ‖) :
      (L j).globalSymbolFunction x ξ = (A.patch j).weight x • (a.val x ξ).inverse := by
    let := (A.patch j).input.frame_mem_atlas
    let := (A.patch j).output.frame_mem_atlas
    by_cases hx : x ∈ (A.patch j).chart.source
    · by_cases hcut : (A.patch j).input.cutoff ((A.patch j).chart x) = 0
      · simp [PseudodifferentialPiece.globalSymbolFunction, L, QuantizationPatch.weight, hx, hcut]
      · have hsupport : (A.patch j).chart x ∈ tsupport (A.patch j).input.cutoff :=
          subset_tsupport _ hcut
        have hi : x ∈ (A.patch j).input.frame.baseSet := by
          have h := ((A.patch j).input.support_subset hsupport).2
          simpa only [Set.mem_preimage, (A.patch j).chart.left_inv hx] using h
        have ho : x ∈ (A.patch j).output.frame.baseSet := by
          have h := (A.patch j).input_support_in_output_frame hsupport
          simpa only [Set.mem_preimage, (A.patch j).chart.left_inv hx] using h
        have hout := (A.patch j).output_eq_one _ hsupport
        have hw : (A.patch j).weight x ≠ 0 := by
          simpa only [QuantizationPatch.weight, ite_eq_left hx] using hcut
        have hpval := hpeq j ((A.patch j).chart x) hsupport
          (covectorInChart (A.patch j).chart x ξ) (hη hw)
        simp only [PseudodifferentialPiece.globalSymbolFunction, L,
          ite_eq_left (show x ∈ (A.patch j).chart.source ∩ (A.patch j).input.frame.baseSet ∩
            (A.patch j).output.frame.baseSet from ⟨⟨hx, hi⟩, ho⟩), p',
          zeroExtendedSymbol_apply_of_mem _ _ _ _ _ (hinput j hsupport), hout,
          one_mul, Complex.ofReal_one, one_smul, hpval,
          QuantizationPatch.weight, ite_eq_left hx]
        rw [← globalSymbolInChart_globalSymbolInverse a.val (A.patch j).chart
          (A.patch j).output.frame (A.patch j).input.frame _ _ (hinput j hsupport)]
        rw [globalSymbolInChart_covectorInChart F E (globalSymbolInverse a.val)
          (A.patch j).chart (A.patch j).chart_mem_atlas (A.patch j).input.frame
          (A.patch j).output.frame x hx ξ]
        apply ContinuousLinearMap.ext
        intro v
        simp only [ContinuousLinearMap.comp_apply, smul_apply]
        rw [(A.patch j).input.frame.symmL_continuousLinearMapAt hi,
          (A.patch j).output.frame.symmL_continuousLinearMapAt ho]
        rfl
    · simp [PseudodifferentialPiece.globalSymbolFunction, L, QuantizationPatch.weight, hx]
  have hrecover (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKT : K ⊆ c.target) :
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
        b.val (c.symm z) (covectorFromChart c (c.symm z) η) =
          (a.val (c.symm z) (covectorFromChart c (c.symm z) η)).inverse := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let T (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (z η : EuclideanSpace ℝ (Fin n)) :=
      covectorInChart d (c.symm z) (covectorFromChart c (c.symm z) η)
    have htransition (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
        (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
        (hdz : c.symm z ∈ d.source) :
        ContDiffAt ℝ ∞ (Function.uncurry (T d)) (z, η) := by
      have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
      have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
      have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) z := by
        exact ((contMDiffAt_of_mem_maximalAtlas hdM hdz).comp z
          (contMDiffAt_symm_of_mem_maximalAtlas hcM hz)).contDiffAt
      have hinverse : ContDiffAt ℝ ∞ (c ∘ d.symm) (d (c.symm z)) := by
        have hbase : d.symm (d (c.symm z)) ∈ c.source := by
          rw [d.left_inv hdz]
          exact c.map_target hz
        exact ((contMDiffAt_of_mem_maximalAtlas hcM hbase).comp (d (c.symm z))
          (contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hdz))).contDiffAt
      have hderiv := (hinverse.fderiv_right (m := ∞) (by simp)).comp (z, η)
        (hforward.comp (z, η) contDiffAt_fst)
      apply contDiffAt_piLp'
      intro j
      have heval := hderiv.clm_apply (contDiffAt_const (c := EuclideanSpace.single j 1))
      have hscalar := contDiffAt_snd.inner ℝ heval
      apply hscalar.congr_of_eventuallyEq
      have hopen : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
        c.continuousOn_symm.isOpen_inter_preimage c.open_target d.open_source
      filter_upwards [hopen.prod isOpen_univ |>.mem_nhds
        (show (z, η) ∈ (c.target ∩ c.symm ⁻¹' d.source) ×ˢ univ from ⟨⟨hz, hdz⟩, trivial⟩)]
        with p hp
      have hsource := hp.1.2
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (d (c.symm p.1))
        (by
          simpa only [d.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hp.1.1)).mdifferentiableAt
              (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hsource)).mdifferentiableAt
          (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [d.left_inv hsource] at hcomp
      change inner ℝ p.2 ((mfderiv I I c (c.symm p.1))
          ((mfderiv I I d.symm (d (c.symm p.1))) (EuclideanSpace.single j 1))) =
        inner ℝ p.2
          ((fderiv ℝ (c ∘ d.symm) (d (c.symm p.1))) (EuclideanSpace.single j 1))
      change fderiv ℝ (c ∘ d.symm) (d (c.symm p.1)) =
        (mfderiv I I c (c.symm p.1)).comp (mfderiv I I d.symm (d (c.symm p.1))) at hcomp
      rw [hcomp]
      rfl
    -- Each original patch has a fixed compact support wholly inside its own valid chart.
    let P (j : Fin A.size) := (A.patch j).chart.symm '' tsupport (A.patch j).input.cutoff
    have hP (j : Fin A.size) : IsCompact (P j) :=
      (A.patch j).input.compact_support.image_of_continuousOn
        ((A.patch j).chart.continuousOn_symm.mono
          (fun y hy ↦ ((A.patch j).input.support_subset hy).1))
    have hPsource (j : Fin A.size) : P j ⊆ (A.patch j).chart.source := by
      rintro x ⟨y, hy, rfl⟩
      exact (A.patch j).chart.map_target (((A.patch j).input.support_subset hy).1)
    have hweight (j : Fin A.size) (x : M) (hx : (A.patch j).weight x ≠ 0) : x ∈ P j := by
      have hsource : x ∈ (A.patch j).chart.source := by
        by_contra hout
        exact hx (by simp [QuantizationPatch.weight, hout])
      have hcut : (A.patch j).input.cutoff ((A.patch j).chart x) ≠ 0 := by
        simpa only [QuantizationPatch.weight, ite_eq_left hsource] using hx
      exact ⟨(A.patch j).chart x, subset_tsupport _ hcut,
        (A.patch j).chart.left_inv hsource⟩
    have hbaseK : IsCompact (c.symm '' K) := hK.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ hKT hz))
    have hbaseKsource : c.symm '' K ⊆ c.source := by
      rintro x ⟨z, hz, rfl⟩
      exact c.map_target (hKT hz)
    -- On each compact overlap, invertibility gives a positive bound on the unit sphere.
    have hbound (j : Fin A.size) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ K, (A.patch j).weight (c.symm z) ≠ 0 →
          ∀ η, ρ ≤ ‖η‖ → R j ≤ ‖T (A.patch j).chart z η‖ := by
      let d := (A.patch j).chart
      have hd := (A.patch j).chart_mem_atlas
      let Q := c '' ((c.symm '' K) ∩ P j)
      have hQ : IsCompact Q := (hbaseK.inter (hP j)).image_of_continuousOn
        (c.continuousOn.mono (fun x hx ↦ hbaseKsource hx.1))
      have hQtarget : Q ⊆ c.target := by
        rintro z ⟨x, hx, rfl⟩
        exact c.map_source (hbaseKsource hx.1)
      have hQsource : ∀ z ∈ Q, c.symm z ∈ d.source := by
        rintro z ⟨x, hx, rfl⟩
        rw [c.left_inv (hbaseKsource hx.1)]
        exact hPsource j hx.2
      have hnonzero (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Q)
          (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) : T d z η ≠ 0 := by
        intro hzero
        have hinv := covectorFromChart_covectorInChart d hd (c.symm z) (hQsource z hz)
          (covectorFromChart c (c.symm z) η)
        have hd0 : covectorFromChart d (c.symm z) 0 = 0 := by
          ext v
          change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) ((mfderiv I I d (c.symm z)) v) = 0
          exact inner_zero_left _
        change covectorFromChart d (c.symm z) (T d z η) = _ at hinv
        rw [hzero, hd0] at hinv
        have hback := covectorInChart_covectorFromChart c hc (c.symm z)
          (c.map_target (hQtarget hz)) η
        rw [← hinv] at hback
        have hc0 : covectorInChart c (c.symm z) 0 = 0 := by
          ext i
          rfl
        exact hη (hback.symm.trans hc0)
      let S := Q ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      have hS : IsCompact S := hQ.prod (isCompact_sphere _ _)
      have hcontinuous : ContinuousOn (fun w ↦ ‖T d w.1 w.2‖) S := by
        intro w hw
        exact ((htransition d hd w.1 w.2 (hQtarget hw.1)
          (hQsource w.1 hw.1)).continuousAt.norm).continuousWithinAt
      obtain ⟨b, hb, hlow⟩ := hS.exists_forall_le' hcontinuous (a := 0) (by
        intro w hw
        apply norm_pos_iff.mpr
        apply hnonzero w.1 hw.1
        intro hzero
        simpa only [hzero, Metric.mem_sphere, dist_self, zero_ne_one] using hw.2)
      refine ⟨R j / b, div_pos (hR j) hb, ?_⟩
      intro z hz hw η hη
      have hzQ : z ∈ Q :=
        ⟨c.symm z, ⟨⟨z, hz, rfl⟩, hweight j (c.symm z) hw⟩, c.right_inv (hKT hz)⟩
      have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (div_pos (hR j) hb) hη
      have hηne := norm_pos_iff.mp hηpos
      let v := ‖η‖⁻¹ • η
      have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
      have hscale : ‖η‖ • v = η := by
        simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
      have hlinear (t : ℝ) : T d z (t • v) = t • T d z v := by
        ext i
        change inner ℝ (t • v) _ = t * inner ℝ v _
        exact real_inner_smul_left v _ t
      have hnorm : ‖T d z η‖ = ‖η‖ * ‖T d z v‖ := by
        calc
          ‖T d z η‖ = ‖T d z (‖η‖ • v)‖ :=
            congrArg (fun ξ ↦ ‖T d z ξ‖) hscale.symm
          _ = ‖η‖ * ‖T d z v‖ := by
            rw [hlinear, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg η)]
      rw [hnorm]
      have hone : R j ≤ ‖η‖ * b := (div_le_iff₀ hb).mp hη
      exact hone.trans (mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hzQ, hv⟩) (norm_nonneg η))
    choose R' hR' hRbound using hbound
    let radius : ℝ := 1 + ∑ j, max 0 (R' j)
    have hradius : 0 < radius := by dsimp [radius]; positivity
    refine ⟨radius, hradius, ?_⟩
    intro z hz η hη
    have hRle (j : Fin A.size) : R' j ≤ radius := by
      have hsum : max 0 (R' j) ≤ ∑ l, max 0 (R' l) :=
        Finset.single_le_sum (fun l _ ↦ le_max_left 0 (R' l)) (Finset.mem_univ j)
      exact (le_max_right 0 (R' j)).trans (hsum.trans (by dsimp [radius]; linarith))
    simp only [b, Submodule.coe_sum, Finset.sum_apply]
    change (∑ j, (L j).globalSymbolFunction (c.symm z)
      (covectorFromChart c (c.symm z) η)) = _
    simp_rw [hpiece _ _ _ (fun hw ↦ hRbound _ z hz hw η ((hRle _).trans hη))]
    rw [← Finset.sum_smul, A.sum_weight, one_smul]
  -- Invertibility in the specified frames is invertibility of the same actual fiber map.
  have hInvOfChart (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f]
      (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F c e f)
      (hi : (globalSymbolInChart E F a.val c e f z η).IsInvertible) :
      (a.val (c.symm z) (covectorFromChart c (c.symm z) η)).IsInvertible := by
    change ((f.continuousLinearMapAt ℂ (c.symm z)).comp
      ((a.val (c.symm z) (covectorFromChart c (c.symm z) η)).comp
        (e.symmL ℂ (c.symm z)))).IsInvertible at hi
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hz.2,
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hz.1.2] at hi
    simpa only [ContinuousLinearMap.isInvertible_equiv_comp,
      ContinuousLinearMap.isInvertible_comp_equiv] using hi
  refine ⟨b, ?_⟩
  intro l
  constructor
  · intro c hc e f _ _
    let U := symbolChartDomain E E c e f
    let p := globalSymbolInChart E E
      (globalSymbolComp b.val a.val - globalSymbolId E) c e f
    have hU : IsOpen U := isOpen_symbolChartDomain E E c e f
    have hsplit : p =
        globalSymbolInChart E E
          (globalSymbolComp b.val a.val) c e f -
          globalSymbolInChart E E (globalSymbolId E) c e f := by
      ext z η v
      simp [p, globalSymbolInChart]
    -- The finite inverse symbol and the given symbol have smooth pointwise products.
    have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ Set.univ) := by
      rw [hsplit]
      exact ((b.property.globalSymbolComp a.property) c hc e f).1.sub
        ((isGlobalSymbol_globalSymbolId (E := E) (r := r)) c hc e f).1
    change IsSymbol U l p
    refine ⟨hp, ?_⟩
    intro K hKU hK i j
    -- Work in smaller compact neighborhoods carrying one genuine intermediate F-frame.
    have hlocal (z : U) : ∃ N : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact N ∧ z.val ∈ interior N ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ x ∈ N, ∀ η, ‖symbolDerivative p i j x η‖ ≤
            C * (1 + ‖η‖) ^ (l - (j : ℝ)) := by
      let g := trivializationAt (EuclideanSpace ℂ (Fin q)) F (c.symm z.val)
      let V := symbolChartDomain E F c e g ∩ symbolChartDomain F E c g f
      have hg : c.symm z.val ∈ g.baseSet := mem_baseSet_trivializationAt _ _ _
      have hV : IsOpen V := (isOpen_symbolChartDomain E F c e g).inter
        (isOpen_symbolChartDomain F E c g f)
      have hzV : z.val ∈ V :=
        ⟨⟨⟨z.property.1.1, z.property.1.2⟩, hg⟩,
          ⟨⟨z.property.1.1, hg⟩, z.property.2⟩⟩
      have hVU : V ⊆ U := fun y hy ↦ ⟨⟨hy.1.1.1, hy.1.1.2⟩, hy.2.2⟩
      obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV hzV
      obtain ⟨N, hN, hzN, hNL⟩ := exists_compact_subset isOpen_interior hzL
      obtain ⟨RB, hRB, hrecoverB⟩ := hrecover c hc L hL (fun y hy ↦ (hLV hy).1.1.1)
      obtain ⟨RI, CI, hRI, hCI, hInv⟩ := he c hc e g L
        (fun y hy ↦ (hLV hy).1) hL
      -- Use a compact neighborhood before differentiating the exact vanishing identity.
      have hsupp : ∀ y ∈ interior L, ∀ η, max RB RI ≤ ‖η‖ → p y η = 0 := by
        intro y hy η hη
        have hyV := hLV (interior_subset hy)
        have hr := hrecoverB y (interior_subset hy) η ((le_max_left RB RI).trans hη)
        have hi := hInvOfChart c e g y η hyV.1
          (hInv y (interior_subset hy) η ((le_max_right RB RI).trans hη)).1
        dsimp only [p, globalSymbolInChart, Pi.sub_apply, globalSymbolComp, globalSymbolId]
        rw [hr, hi.inverse_comp_self, sub_self]
        simp
      have hint : interior L ⊆ U := (interior_subset.trans hLV).trans hVU
      have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p (max RB RI)
        (hp.mono (Set.prod_mono hint subset_rfl)) hsupp l
      obtain ⟨C, hC, hbound⟩ := hsmoothing.2 N hNL hN i j
      exact ⟨N, hN, hzN, C, hC, hbound⟩
    choose N hN hzN C hC hbound using hlocal
    -- A finite subcover gives one estimate on the original compact set, for this real order.
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (N z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzN ⟨x, hKU hx⟩⟩)
    refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg (fun z _ ↦ hC z), ?_⟩
    intro x hx η
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (hbound z x (interior_subset hxz) η).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hC z) hzt
  · intro c hc e f _ _
    let U := symbolChartDomain F F c e f
    let p := globalSymbolInChart F F
      (globalSymbolComp a.val b.val - globalSymbolId F) c e f
    have hU : IsOpen U := isOpen_symbolChartDomain F F c e f
    have hsplit : p =
        globalSymbolInChart F F
          (globalSymbolComp a.val b.val) c e f -
          globalSymbolInChart F F (globalSymbolId F) c e f := by
      ext z η v
      simp [p, globalSymbolInChart]
    -- The finite inverse symbol and the given symbol have smooth pointwise products.
    have hp : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ Set.univ) := by
      rw [hsplit]
      exact ((a.property.globalSymbolComp b.property) c hc e f).1.sub
        ((isGlobalSymbol_globalSymbolId (E := F) (r := q)) c hc e f).1
    change IsSymbol U l p
    refine ⟨hp, ?_⟩
    intro K hKU hK i j
    -- Work in smaller compact neighborhoods carrying one genuine intermediate E-frame.
    have hlocal (z : U) : ∃ N : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact N ∧ z.val ∈ interior N ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ x ∈ N, ∀ η, ‖symbolDerivative p i j x η‖ ≤
            C * (1 + ‖η‖) ^ (l - (j : ℝ)) := by
      let g := trivializationAt (EuclideanSpace ℂ (Fin r)) E (c.symm z.val)
      let V := symbolChartDomain F E c e g ∩ symbolChartDomain E F c g f
      have hg : c.symm z.val ∈ g.baseSet := mem_baseSet_trivializationAt _ _ _
      have hV : IsOpen V := (isOpen_symbolChartDomain F E c e g).inter
        (isOpen_symbolChartDomain E F c g f)
      have hzV : z.val ∈ V :=
        ⟨⟨⟨z.property.1.1, z.property.1.2⟩, hg⟩,
          ⟨⟨z.property.1.1, hg⟩, z.property.2⟩⟩
      have hVU : V ⊆ U := fun y hy ↦ ⟨⟨hy.1.1.1, hy.1.1.2⟩, hy.2.2⟩
      obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV hzV
      obtain ⟨N, hN, hzN, hNL⟩ := exists_compact_subset isOpen_interior hzL
      obtain ⟨RB, hRB, hrecoverB⟩ := hrecover c hc L hL (fun y hy ↦ (hLV hy).1.1.1)
      obtain ⟨RI, CI, hRI, hCI, hInv⟩ := he c hc g f L
        (fun y hy ↦ (hLV hy).2) hL
      -- Use a compact neighborhood before differentiating the exact vanishing identity.
      have hsupp : ∀ y ∈ interior L, ∀ η, max RB RI ≤ ‖η‖ → p y η = 0 := by
        intro y hy η hη
        have hyV := hLV (interior_subset hy)
        have hr := hrecoverB y (interior_subset hy) η ((le_max_left RB RI).trans hη)
        have hi := hInvOfChart c g f y η hyV.2
          (hInv y (interior_subset hy) η ((le_max_right RB RI).trans hη)).1
        dsimp only [p, globalSymbolInChart, Pi.sub_apply, globalSymbolComp, globalSymbolId]
        rw [hr, hi.self_comp_inverse, sub_self]
        simp
      have hint : interior L ⊆ U := (interior_subset.trans hLV).trans hVU
      have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p (max RB RI)
        (hp.mono (Set.prod_mono hint subset_rfl)) hsupp l
      obtain ⟨C, hC, hbound⟩ := hsmoothing.2 N hNL hN i j
      exact ⟨N, hN, hzN, C, hC, hbound⟩
    choose N hN hzN C hC hbound using hlocal
    -- A finite subcover gives one estimate on the original compact set, for this real order.
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (N z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzN ⟨x, hKU hx⟩⟩)
    refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg (fun z _ ↦ hC z), ?_⟩
    intro x hx η
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (hbound z x (interior_subset hxz) η).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hC z) hzt

end AtiyahSinger
