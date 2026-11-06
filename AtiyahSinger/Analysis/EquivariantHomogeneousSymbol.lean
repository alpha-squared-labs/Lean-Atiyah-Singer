/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology

/-!
# Equivariance of displayed homogeneous principal symbols

Public module ID: M0524.

Geometric transport of a regularized homogeneous principal class agrees with
another displayed homogeneous class exactly when their original Hom data
agree off the zero section after the same inverse-cotangent conjugation.
The two regularization presentations are independent and need not be invariant.
The fixed-class specialization supplies the input required by equivariant
quantization, while the converse recovers off-zero equivariance from an actual
equivariant operator with a displayed homogeneous principal representative.

Sources: SG III.3.13--3.14, p.186, and III.3.19, p.188, for covariance and the
principal quotient; III.13 (13.5), pp.244--245, for homogeneous leading data;
III.9, pp.211 and 214, for equivariance. This combined statement is an explicit
standard supplement, not a separately numbered assertion from SG.

The comparison is for each fixed group element. Its coordinate frequency
thresholds may depend on that element; it does not supply the separate uniform
lower-order estimates needed by Haar averaging.
No group compactness, invariant metric, invariant cutoff, or condition on the
arbitrary zero-section values is imposed. General principal quotient elements
are not asserted to have homogeneous representatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)

/-- Geometric equality of homogeneous principal classes is exact equality of off-zero data. -/
theorem QuantizationPresentation.equivariant_regularizedSymbol_class_eq_iff
    (A B : QuantizationPresentation (n := n) (r := r) (q := q) E F) (m : ℝ)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) (g : G) :
    equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ m g
        (globalPrincipalSymbolClass E F m
          (A.regularizedSymbol m a.val a.property.1 a.property.2)) =
      globalPrincipalSymbolClass E F m
        (B.regularizedSymbol m b.val b.property.1 b.property.2) ↔
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = b.val x ξ := by
  /- Use the same local cotangent substitution and moving-frame matrices as the
  geometric symbol action. The inverse frequency matrix is bounded on each compact
  coordinate neighborhood, so transported regularization recovers the transported
  homogeneous data above a common local radius. Those data retain degree m because
  the frequency map is invertible and linear, while the two matrices are independent
  of frequency. Forward, apply the existing local uniqueness theorem for homogeneous
  leading data using the one-order quotient estimate. Reverse, equality off zero makes
  the two smooth representatives equal at high frequency locally; their difference
  has every order by the finite-frequency-support theorem. This uses the original A
  and B independently, no invariant cutoff, and no assertion at the zero section.
  All radii may depend on the fixed g. They do not provide uniform-in-g lower-order
  estimates for Haar averaging. The zero-dimensional case is included automatically. -/
  classical
  rw [equivariantPrincipalSymbolRepresentation_class]
  let a₁ := equivariantGlobalSymbolLinearMap IG σ τ g a.val
  let pa := equivariantGlobalSymbolRepresentation IG σ τ hσ hτ m g
    (A.regularizedSymbol m a.val a.property.1 a.property.2)
  let pb := B.regularizedSymbol m b.val b.property.1 b.property.2
  change globalPrincipalSymbolClass E F m pa = globalPrincipalSymbolClass E F m pb ↔
    ∀ x ξ, ξ ≠ 0 → a₁ x ξ = b.val x ξ
  -- One original coordinate transport controls homogeneity and high-frequency recovery.
  have hlocal
      (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e' : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      (f' : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e'] [MemTrivializationAtlas f']
      (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F d e' f') :
      ∃ Z : Set (EuclideanSpace ℝ (Fin n)), IsOpen Z ∧ z ∈ Z ∧
        Z ⊆ symbolChartDomain E F d e' f' ∧
        IsHomogeneousSymbol Z m (globalSymbolInChart E F a₁ d e' f') ∧
        ∀ K, IsCompact K → K ⊆ Z → ∃ R : ℝ, 0 < R ∧
          ∀ y ∈ K, ∀ η, R ≤ ‖η‖ →
            globalSymbolInChart E F pa.val d e' f' y η =
              globalSymbolInChart E F a₁ d e' f' y η := by
    obtain ⟨c, e, f, he, hf, hc, Z, t, L, R, hZ, hzZ, hZU, hZt, htS,
      ht, hts, hL, hR, hformula⟩ :=
      exists_local_equivariantGlobalSymbolInChart IG σ τ hσ hτ g d hd e' f' z hz
    let := he
    let := hf
    let X := EuclideanSpace ℝ (Fin n)
    let Θ : X → X →L[ℝ] X := fun y ↦ (fderiv ℝ t (t.symm y)).adjoint
    let Ψ : X → X →L[ℝ] X := fun y ↦ (fderiv ℝ t.symm y).adjoint
    -- Differentiate the inverse identity once; its dual is the inverse frequency map.
    have hinverse (y : X) (hy : y ∈ Z) (η : X) : Ψ y (Θ y η) = η := by
      have hyT := hZt hy
      have hforwardSmooth := ht.contDiffAt (t.open_source.mem_nhds (t.map_target hyT))
      have hbackwardSmooth := hts.contDiffAt (t.open_target.mem_nhds hyT)
      have hforward := hforwardSmooth.differentiableAt (by simp)
      have hbackward := hbackwardSmooth.differentiableAt (by simp)
      have hright : (fderiv ℝ t (t.symm y)).comp (fderiv ℝ t.symm y) =
          ContinuousLinearMap.id ℝ X := by
        apply (hforward.hasFDerivAt.comp y hbackward.hasFDerivAt).unique
        apply (hasFDerivAt_id y).congr_of_eventuallyEq
        filter_upwards [t.open_target.mem_nhds hyT] with w hw
        exact t.right_inv hw
      have hdual := congrArg ContinuousLinearMap.adjoint hright
      have hid : ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ X) =
          ContinuousLinearMap.id ℝ X := ContinuousLinearMap.adjoint_id
      have hdual' : (Ψ y).comp (Θ y) = ContinuousLinearMap.id ℝ X := by
        simpa only [Θ, Ψ, ContinuousLinearMap.adjoint_comp] using hdual.trans hid
      exact congrArg (fun T ↦ T η) hdual'
    have hnonzero (y : X) (hy : y ∈ Z) (η : X) (hη : η ≠ 0) : Θ y η ≠ 0 := by
      intro hzero
      have h := hinverse y hy η
      rw [hzero, map_zero] at h
      exact hη h.symm
    refine ⟨Z, hZ, hzZ, hZU, ?_, ?_⟩
    · intro y hy η hη c₀ hc₀
      rw [hformula a.val y hy (c₀ • η), hformula a.val y hy η]
      change (L y).comp
        ((globalSymbolInChart E F a.val c e f (t.symm y) (Θ y (c₀ • η))).comp (R y)) = _
      rw [(Θ y).map_smul, a.property.2.in_chart c hc e f (t.symm y)
        (htS (t.map_target (hZt hy))) (Θ y η) (hnonzero y hy η hη) c₀ hc₀]
      simp only [matrixSymbol, cotangentSymbol, Θ,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    · -- A compact bound for the inverse dual turns a source frequency radius into a target one.
      intro K hK hKZ
      let K₀ := t.symm '' K
      have hK₀ : IsCompact K₀ := hK.image_of_continuousOn
        (t.continuousOn_symm.mono (hKZ.trans hZt))
      have hK₀S : K₀ ⊆ symbolChartDomain E F c e f := by
        rintro _ ⟨y, hy, rfl⟩
        exact htS (t.map_target (hZt (hKZ hy)))
      obtain ⟨R₀, hR₀, hrecover⟩ := A.regularizedSymbolFunction_eq_inChart_at_high_frequency
        a.val c hc e f K₀ hK₀ hK₀S
      have hcont := hts.continuousOn_fderiv_of_isOpen t.open_target (by simp)
      obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hcont.mono (hKZ.trans hZt))
      let C := max C₀ 1
      have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
      refine ⟨C * R₀, mul_pos hC hR₀, ?_⟩
      intro y hy η hη
      have hnorm : ‖η‖ ≤ C * ‖Θ y η‖ := by
        calc
          _ = ‖Ψ y (Θ y η)‖ := congrArg norm (hinverse y (hKZ hy) η).symm
          _ ≤ ‖Ψ y‖ * ‖Θ y η‖ := (Ψ y).le_opNorm _
          _ ≤ C * ‖Θ y η‖ := mul_le_mul_of_nonneg_right (by
            simpa only [Ψ, ContinuousLinearMap.adjoint.norm_map] using
              (hC₀ y hy).trans (le_max_left C₀ 1)) (norm_nonneg _)
      have hlarge : R₀ ≤ ‖Θ y η‖ := (mul_le_mul_iff_right₀ hC).mp (hη.trans hnorm)
      change globalSymbolInChart E F
        (equivariantGlobalSymbolLinearMap IG σ τ g (A.regularizedSymbolFunction a.val))
          d e' f' y η = _
      rw [hformula (A.regularizedSymbolFunction a.val) y (hKZ hy) η,
        hformula a.val y (hKZ hy) η]
      dsimp only [matrixSymbol, cotangentSymbol]
      rw [hrecover (t.symm y) ⟨y, hy, rfl⟩ _ hlarge]
  constructor
  · intro hclass x ξ hξ
    -- Restrict both representatives to one compact coordinate neighborhood of x.
    let d := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hd := chart_mem_atlas (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ d.source := mem_chart_source _ x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hf : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    have hz : d x ∈ symbolChartDomain E F d e f :=
      ⟨⟨d.map_source hx, by simpa only [Set.mem_preimage, d.left_inv hx] using he⟩,
        by simpa only [Set.mem_preimage, d.left_inv hx] using hf⟩
    obtain ⟨Z, hZ, hzZ, hZU, hhom, hrecover⟩ := hlocal d hd e f (d x) hz
    obtain ⟨K, hK, hzK, hKZ⟩ := exists_compact_subset hZ hzZ
    have hint : interior K ⊆ Z := interior_subset.trans hKZ
    have hKU := hKZ.trans hZU
    have hintU := hint.trans hZU
    obtain ⟨RA, hRA, hrecoverA⟩ := hrecover K hK hKZ
    obtain ⟨RB, hRB, hrecoverB⟩ :=
      B.regularizedSymbolFunction_eq_inChart_at_high_frequency b.val d hd e f K hK hKU
    let qa : symbolSpace (interior K) isOpen_interior m r q :=
      ⟨globalSymbolInChart E F pa.val d e f, (pa.property d hd e f).restrict hintU⟩
    let qb : symbolSpace (interior K) isOpen_interior m r q :=
      ⟨globalSymbolInChart E F pb.val d e f, (pb.property d hd e f).restrict hintU⟩
    have hdiff := (globalPrincipalSymbolClass_eq_iff E F m pa pb).mp hclass d hd e f
    have hsub : globalSymbolInChart E F (pa.val - pb.val) d e f = qa.val - qb.val := by
      ext y η v
      simp [globalSymbolInChart, qa, qb]
    rw [hsub] at hdiff
    have hclassLocal := (principalSymbolClass_eq_iff isOpen_interior qa qb).mpr
      (hdiff.restrict hintU)
    have hη : covectorInChart d x ξ ≠ 0 := by
      intro hzero
      have hinv := covectorFromChart_covectorInChart d hd x hx ξ
      rw [hzero] at hinv
      have hc0 : covectorFromChart d x 0 = 0 := by
        ext v
        change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) _ = 0
        exact inner_zero_left _
      exact hξ (hinv.symm.trans hc0)
    -- The existing uniqueness theorem uses precisely the one-order gain on positive rays.
    have hmap := homogeneous_eq_of_principalSymbolClass_eq isOpen_interior qa qb
      (globalSymbolInChart E F a₁ d e f) (globalSymbolInChart E F b.val d e f)
      (fun y hy ↦ hhom y (hint hy))
      (fun y hy ↦ b.property.2.in_chart d hd e f y (hintU hy))
      (max RA RB) (lt_of_lt_of_le hRA (le_max_left _ _))
      (fun y hy η hη ↦ hrecoverA y (interior_subset hy) η ((le_max_left _ _).trans hη))
      (fun y hy η hη ↦ hrecoverB y (interior_subset hy) η ((le_max_right _ _).trans hη))
      hclassLocal (d x) hzK (covectorInChart d x ξ) hη
    rw [globalSymbolInChart_covectorInChart E F a₁ d hd e f x hx ξ,
      globalSymbolInChart_covectorInChart E F b.val d hd e f x hx ξ] at hmap
    ext v
    have htest := congrArg
      (fun L : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) ↦
        f.symmL ℂ x (L (e.continuousLinearMapAt ℂ x v))) hmap
    simpa only [ContinuousLinearMap.comp_apply, e.symmL_continuousLinearMapAt he,
      f.symmL_continuousLinearMapAt hf] using htest
  · intro hab
    -- Equality of the off-zero data makes the smooth representative difference locally
    -- frequency-supported. All its mixed derivatives then have every lower order.
    apply (globalPrincipalSymbolClass_eq_iff E F m pa pb).mpr
    intro d hd e f _ _
    let U := symbolChartDomain E F d e f
    let q₁ := globalSymbolInChart E F pa.val d e f
    let q₂ := globalSymbolInChart E F pb.val d e f
    have hU : IsOpen U := isOpen_symbolChartDomain E F d e f
    have hsub : globalSymbolInChart E F (pa.val - pb.val) d e f = q₁ - q₂ := by
      ext y η v
      simp [globalSymbolInChart, q₁, q₂]
    rw [hsub]
    have hs : ContDiffOn ℝ ∞ (Function.uncurry (q₁ - q₂)) (U ×ˢ univ) :=
      (pa.property d hd e f).1.sub (pb.property d hd e f).1
    apply IsSymbol.of_locally hU
    intro z hz
    obtain ⟨Z, hZ, hzZ, hZU, hhom, hrecover⟩ := hlocal d hd e f z hz
    obtain ⟨K, hK, hzK, hKZ⟩ := exists_compact_subset hZ hzZ
    have hint : interior K ⊆ Z := interior_subset.trans hKZ
    have hKU := hKZ.trans hZU
    have hintU := hint.trans hZU
    obtain ⟨RA, hRA, hrecoverA⟩ := hrecover K hK hKZ
    obtain ⟨RB, hRB, hrecoverB⟩ :=
      B.regularizedSymbolFunction_eq_inChart_at_high_frequency b.val d hd e f K hK hKU
    have hsupport : ∀ y ∈ interior K, ∀ η, max RA RB ≤ ‖η‖ → (q₁ - q₂) y η = 0 := by
      intro y hy η hη
      change globalSymbolInChart E F pa.val d e f y η -
        globalSymbolInChart E F pb.val d e f y η = 0
      rw [hrecoverA y (interior_subset hy) η ((le_max_left _ _).trans hη)]
      change globalSymbolInChart E F a₁ d e f y η -
        globalSymbolInChart E F (B.regularizedSymbolFunction b.val) d e f y η = 0
      rw [hrecoverB y (interior_subset hy) η ((le_max_right _ _).trans hη)]
      have hηne : η ≠ 0 := norm_pos_iff.mp
        ((lt_of_lt_of_le hRA (le_max_left _ _)).trans_le hη)
      have hξne : covectorFromChart d (d.symm y) η ≠ 0 := by
        intro hzero
        have hinv := covectorInChart_covectorFromChart d hd (d.symm y)
          (d.map_target (hintU hy).1.1) η
        rw [hzero] at hinv
        have hcoord : covectorInChart d (d.symm y) 0 = 0 := by
          ext i
          rfl
        exact hηne (hinv.symm.trans hcoord)
      have heq : globalSymbolInChart E F a₁ d e f y η =
          globalSymbolInChart E F b.val d e f y η := by
        dsimp only [globalSymbolInChart]
        rw [hab (d.symm y) (covectorFromChart d (d.symm y) η) hξne]
      exact sub_eq_zero.mpr heq
    exact ⟨interior K, isOpen_interior, hzK, hintU,
      isSmoothingSymbol_of_frequency_support isOpen_interior (q₁ - q₂) (max RA RB)
        (hs.mono (Set.prod_mono hintU subset_rfl)) hsupport (m - 1)⟩

end AtiyahSinger
