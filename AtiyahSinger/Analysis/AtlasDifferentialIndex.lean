/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasAnalyticIndex
public import AtiyahSinger.Analysis.AtlasDifferentialPseudodifferential
public import AtiyahSinger.Analysis.BaseCohomologicalIndexTheorem

/-!
# The original atlas differential operator in the index formulas

Public module ID: M0238.

The actual leading polynomial of a variable-rank atlas differential operator
is smooth and homogeneous. Its radial regularization represents precisely
the principal quotient of that same differential section map regarded as a
PDO. Thus the existing analytic and oriented-base formulas apply without an
assumed principal-class equality or a replacement quantization.

The support class below always uses the original polynomial and original two
bundles. The chosen radial cotangent metric affects only its regularization;
it is independent of the supplied tangent metric used in musical transport.
In dimension zero the principal quotient is trivial, but the original support
class retains the source-minus-target bundle difference. Local ranks may vary.

Sources: SG III.3, the differential inclusion after Definition 3.15, p.186;
III.5, Theorem 5.2 and Corollary 5.3; III.13 (13.7) and the second Theorem 13.8, (13.24).
These are the variable-rank differential specializations of the existing
atlas PDO statements. Smoothness and homogeneity of the actual differential symbol
and its PDO principal-class and Sobolev index comparisons are proved below.
The analytic-index and characteristic-number comparisons use these same data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory Set
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {k : ℕ} (P : AtlasDifferentialOperator A B k)

namespace AtlasDifferentialOperator

/-- The actual differential principal polynomial is smooth on the punctured cotangent bundle. -/
theorem isSmoothOffZeroAtlasSymbol_principalSymbol :
    IsSmoothOffZeroAtlasSymbol A B P.principalSymbol := by
  /- In each chart and frame pair, apply
  contDiffOn_principalSymbol_in_chart to each coordinate basis vector.
  Reconstruct the Hom-valued leading polynomial from these finitely many
  smooth columns, then restrict to nonzero frequencies. The coordinate
  covector conversion and the two specified fiber frames remain the same. -/
  classical
  intro c hc i j
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let W := EuclideanSpace ℂ (Fin (B.rank j))
  let eA := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let eB := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
  let a := Function.uncurry (atlasGlobalSymbolInChart A B P.principalSymbol c i j)
  let Ω := atlasSymbolChartDomain A B c i j ×ˢ
    (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
  have hcolumn (v : V) : ContDiffOn ℝ ∞ (fun z ↦ a z v) Ω := by
    have hs := P.contDiffOn_principalSymbol_in_chart c hc i j (eA v)
    apply ((eB.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn hs).congr
    intro z hz
    have hvalid : c.symm z.1 ∈ (A.chart i).baseSet ∧
        c.symm z.1 ∈ (B.chart j).baseSet := ⟨hz.1.1.2, hz.1.2⟩
    have hpoint : (A.chart i).toPartialEquiv.symm (c.symm z.1, eA v) =
        (⟨c.symm z.1, (A.frameLinearEquiv i (c.symm z.1) hvalid.1).symm (eA v)⟩ :
          TotalSpace Unit E) := by
      exact (TotalSpace.mk_cast (F := Unit) (E := E)
        ((A.chart i).proj_symm_apply' (x := eA v) hvalid.1)
        ((A.chart i).toOpenPartialHomeomorph.symm (c.symm z.1, eA v)).2).symm
    change atlasGlobalSymbolInChart A B P.principalSymbol c i j z.1 z.2 v =
      eB.symm (let w := (A.chart i).toPartialEquiv.symm (c.symm z.1, eA v)
        (B.chart j ⟨w.proj, P.principalSymbol w.proj
          ((innerSL ℝ z.2).comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c w.proj)) w.snd⟩).2)
    rw [hpoint]
    simp only [atlasGlobalSymbolInChart, dite_eq_left hvalid]
    rfl
  -- Reconstruct the same Hom-valued symbol from its finitely many actual columns.
  have hsum (v : V) : ∑ j : Fin (A.rank i), v j • EuclideanSpace.single j 1 = v := by
    simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).toBasis.sum_repr v
  have hs : ContDiffOn ℝ ∞
      (fun z ↦ ∑ j : Fin (A.rank i), (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
        (a z (EuclideanSpace.single j 1))) Ω := by
    apply ContDiffOn.sum
    intro j _
    exact ((ContinuousLinearMap.smulRightL ℂ V W (EuclideanSpace.proj j)).restrictScalars
      ℝ).contDiff.comp_contDiffOn (hcolumn (EuclideanSpace.single j 1))
  have heq : (fun z ↦ ∑ j : Fin (A.rank i), (EuclideanSpace.proj (𝕜 := ℂ) j).smulRight
      (a z (EuclideanSpace.single j 1))) = a := by
    funext z
    apply ContinuousLinearMap.ext
    intro v
    simpa only [sum_apply, ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj,
      PiLp.proj_apply, ← map_smul, ← map_sum] using congrArg (a z) (hsum v)
  rw [heq] at hs
  exact hs.mono (Set.prod_mono le_rfl (Set.subset_univ _))

/-- The actual degree-k polynomial has the positive real homogeneity used by the PDO calculus. -/
theorem isHomogeneousAtlasSymbol_principalSymbol :
    IsHomogeneousAtlasSymbol (k : ℝ) P.principalSymbol := by
  /- Use principalSymbol_smul for the same real covector and positive t.
  For the natural exponent k, real rpow agrees with the ordinary power;
  the real-to-complex ring homomorphism preserves that power. Thus its
  scalar is exactly the one in IsHomogeneousAtlasSymbol. This conversion
  includes k=0 and the zero-dimensional empty punctured bundle. -/
  intro x ξ _ t _
  simpa only [Real.rpow_natCast, Complex.ofReal_pow] using P.principalSymbol_smul x ξ t

variable [CompactSpace M]

/-- The same differential action has the regularized class of its original principal polynomial. -/
theorem principalSymbol_toAtlasPseudodifferentialOperator_eq_regularized
    (q : SmoothCotangentMetric (n := n) (M := M)) :
    P.toAtlasPseudodifferentialOperator.principalSymbol =
      atlasGlobalPrincipalSymbolClass A B (k : ℝ)
        (atlasRegularizedSymbol A B q (k : ℝ) P.principalSymbol
          P.isSmoothOffZeroAtlasSymbol_principalSymbol
          P.isHomogeneousAtlasSymbol_principalSymbol) := by
  /- Stage 1: the existing differential-to-PDO theorem identifies this
  principal quotient with the class of P.principalGlobalSymbol. Its PDO
  stores precisely P.toLinearMap; no new section operator is selected.
  Stage 2: subtract the radial regularization of that same polynomial.
  The difference is smooth at zero because the polynomial itself is
  smooth and the cutoff vanishes near zero. On each compact spatial set,
  the metric q bounds the frequency support of the difference uniformly.
  Hence every mixed derivative satisfies every symbol order, in particular
  k-1. The existing quotient criterion identifies the two principal classes.
  Stage 3: when n=0 every frequency domain is a singleton and the same
  all-order estimate applies. This quotient comparison does not erase or
  identify the source and target bundles of their later support class. -/
  classical
  rw [P.principalSymbol_toAtlasPseudodifferentialOperator]
  apply (atlasGlobalPrincipalSymbolClass_eq_iff A B (k : ℝ) _ _).mpr
  have hcov_smul (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (z η : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      covectorFromChart c (c.symm z) (t • η) = t • covectorFromChart c (c.symm z) η := by
    ext v
    change inner ℝ (t • η) (mfderiv _ _ c (c.symm z) v) =
      t * inner ℝ η (mfderiv _ _ c (c.symm z) v)
    exact real_inner_smul_left η _ t
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
  have hrecovery (ℓ : SmoothCotangentMetric (n := n) (M := M))
      (p : AtlasSymbolFunction (n := n) E F)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hKV : K ⊆ atlasSymbolChartDomain A B c i j) :
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
        atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction ℓ p) c i j z η =
          atlasGlobalSymbolInChart A B p c i j z η := by
    let L (z η : EuclideanSpace ℝ (Fin n)) :=
      ℓ.length (c.symm z) (covectorFromChart c (c.symm z) η)
    let S := K ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
    have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
    have hne (η : EuclideanSpace ℝ (Fin n))
        (hη : η ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : η ≠ 0 := by
      intro hz
      simp [hz] at hη
    have hcont : ContinuousOn (Function.uncurry L) S :=
      (ℓ.contDiffOn_length_covectorFromChart c hc).continuousOn.mono
        (fun z hz ↦ ⟨(hKV hz.1).1.1, hne z.2 hz.2⟩)
    obtain ⟨d, hd, hlow⟩ := hS.exists_forall_le' hcont (a := 0) (by
      intro z hz
      exact ℓ.length_pos _ _ (hcov_ne c hc z.1 (hKV hz.1).1.1 z.2 (hne z.2 hz.2)))
    refine ⟨d⁻¹, inv_pos.mpr hd, ?_⟩
    intro z hz η hη
    have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (inv_pos.mpr hd) hη
    have hηne : η ≠ 0 := norm_pos_iff.mp hηpos
    let v := ‖η‖⁻¹ • η
    have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
    have hscale : ‖η‖ • v = η := by simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
    have hlen : L z η = ‖η‖ * L z v := by
      dsimp [L]
      conv_lhs => rw [← hscale, hcov_smul, ℓ.length_smul]
      rw [abs_of_nonneg (norm_nonneg η)]
    have hlength : 1 ≤ L z η := by
      rw [hlen]
      have h := mul_le_mul_of_nonneg_left hη hd.le
      rw [mul_inv_cancel₀ hd.ne'] at h
      have hl := mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hz, hv⟩) (norm_nonneg η)
      exact h.trans (by simpa only [Function.uncurry, mul_comm] using hl)
    have heq := (AtiyahSinger.atlasRegularizedSymbolFunction_cutoff ℓ p).2
      (c.symm z) (covectorFromChart c (c.symm z) η) hlength
    simp only [atlasGlobalSymbolInChart, heq]
  intro c hc i j
  let U := atlasSymbolChartDomain A B c i j
  let p := atlasGlobalSymbolInChart A B P.principalSymbol c i j
  let r := atlasGlobalSymbolInChart A B (atlasRegularizedSymbolFunction q P.principalSymbol)
    c i j
  have hopen : IsOpen U := by
    simpa only [U, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      c.continuousOn_symm.isOpen_inter_preimage c.open_target
        ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
  have hsub : atlasGlobalSymbolInChart A B
      (P.principalGlobalSymbol.val - (atlasRegularizedSymbol A B q (k : ℝ)
        P.principalSymbol P.isSmoothOffZeroAtlasSymbol_principalSymbol
          P.isHomogeneousAtlasSymbol_principalSymbol).val) c i j = p - r := by
    ext z η v
    by_cases hz : c.symm z ∈ (A.chart i).baseSet ∧ c.symm z ∈ (B.chart j).baseSet
    · simp [atlasGlobalSymbolInChart, principalGlobalSymbol, atlasRegularizedSymbol, p, r, hz]
    · simp [atlasGlobalSymbolInChart, p, r, hz]
  rw [hsub]
  have hp := P.isAtlasGlobalSymbol_principalSymbol c hc i j
  have hr := (isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B q (k : ℝ)
    P.principalSymbol P.isSmoothOffZeroAtlasSymbol_principalSymbol
      P.isHomogeneousAtlasSymbol_principalSymbol) c hc i j
  have hd : ContDiffOn ℝ ∞ (Function.uncurry (p - r)) (U ×ˢ Set.univ) := hp.1.sub hr.1
  refine ⟨hd, ?_⟩
  intro K hKU hK α β
  -- Recovery holds on an open neighborhood of K, so it controls spatial derivatives as well.
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hopen hKU
  obtain ⟨R, _, hR⟩ := hrecovery q P.principalSymbol c hc i j K' hK' hK'U
  have hint : interior K' ⊆ U := interior_subset.trans hK'U
  have hsupp : ∀ z ∈ interior K', ∀ η, R ≤ ‖η‖ → (p - r) z η = 0 := by
    intro z hz η hη
    change p z η - r z η = 0
    dsimp only [p, r]
    rw [hR z (interior_subset hz) η hη, sub_self]
  have hsmooth := isSmoothingSymbol_of_frequency_support isOpen_interior (p - r) R
    (hd.mono (Set.prod_mono hint subset_rfl)) hsupp ((k : ℝ) - 1)
  exact hsmooth.2 K hKK' hK α β

/-- Ellipticity gives finite original kernel and cokernel and the same critical Sobolev index. -/
theorem index_sobolevExtension_of_isElliptic
    (q : SmoothCotangentMetric (n := n) (M := M)) (hi : P.IsElliptic)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s : ℝ) :
    FiniteDimensional ℂ P.toLinearMap.ker ∧
      FiniteDimensional ℂ (B.smoothSections ⧸ P.toLinearMap.range) ∧
      (P.toAtlasPseudodifferentialOperator.sobolevExtension L K s).index =
        P.toLinearMap.index := by
  /- Stage 1: feed the exact polynomial, its smoothness and homogeneity,
  and the proved regularized principal equality to the existing atlas
  homogeneous Fredholm theorem. The hypothesis P.IsElliptic is precisely
  bijectivity of these same fiber maps off the zero section.
  Stage 2: use the natural smooth/Sobolev kernel and cokernel equivalences
  for this same PDO and these supplied L,K,s. They prove both finiteness
  assertions and preserve the two dimensions defining the index.
  Stage 3: its original section map is definitionally P.toLinearMap.
  Therefore this is the original algebraic index, with its finiteness
  justified, rather than an unverified use of a totalized infinite index. -/
  exact P.toAtlasPseudodifferentialOperator.index_sobolevExtension_of_homogeneous L K q
    P.principalSymbol P.isSmoothOffZeroAtlasSymbol_principalSymbol
    P.isHomogeneousAtlasSymbol_principalSymbol
    (P.principalSymbol_toAtlasPseudodifferentialOperator_eq_regularized q) hi s

section MeasuredBase

variable [MeasurableSpace M] [BorelSpace M]

/-- The existing analytic index evaluates the exact differential polynomial's support class. -/
theorem analyticIndexOfComponents_principalSymbol
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (q : SmoothCotangentMetric (n := n) (M := M)) (hi : P.IsElliptic) :
    analyticIndexOfComponents μ
        (atlasSymbolKClass A B P.principalSymbol
          P.isSmoothOffZeroAtlasSymbol_principalSymbol hi) =
      P.toLinearMap.index := by
  /- Stage 1: regard this exact differential operator as the existing
  atlas PDO. Use its own principal polynomial as the homogeneous data,
  with the regularized principal equality proved above and ellipticity hi.
  Stage 2: apply the existing component analytic-index evaluation to those
  same witnesses. The actual PDO stores the original smooth section map,
  so the right side is P.toLinearMap.index without any conjugation or
  quantized replacement. The original support class uses both actual
  bundles, retaining their difference even when n=0 and ranks differ. -/
  exact P.toAtlasPseudodifferentialOperator.analyticIndexOfComponents_atlasSymbolKClass μ q
    P.principalSymbol P.isSmoothOffZeroAtlasSymbol_principalSymbol
    P.isHomogeneousAtlasSymbol_principalSymbol
    (P.principalSymbol_toAtlasPseudodifferentialOperator_eq_regularized q) hi

end MeasuredBase

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The oriented-base index formula for the actual variable-rank differential operator. -/
theorem index_eq_base_characteristic_number
    (O : HomologicalOrientation n M)
    (g : SmoothTangentMetric (n := n) (M := M))
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x))
    (q : SmoothCotangentMetric (n := n) (M := M)) (hi : P.IsElliptic) :
    ((P.toLinearMap.index : ℤ) : ℚ) =
      (-1 : ℚ) ^ (n * (n + 1) / 2) * compactManifoldCohomologyIntegral O
        (baseIndexCharacteristicClass O g hV
          ((tangentCotangentKZeroEquiv g).symm
            (atlasSymbolKClass A B P.principalSymbol
              P.isSmoothOffZeroAtlasSymbol_principalSymbol hi))) := by
  /- Stage 1: the original operator's polynomial supplies its own smooth
  homogeneous representative, and the regularized principal equality is
  a theorem for this same operator, not an assumption on an unrelated PDO.
  Apply the existing atlas PDO oriented-base formula to these exact data.
  Stage 2: the stored original section map is P.toLinearMap. Retain the
  displayed support class and transport it by precisely the inverse
  musical map of g. The cotangent radial metric q is independent of g
  and affects no term of the resulting original support class.
  Stage 3: the base evaluation and fiber Thom inverse use the same O.
  Thus the inherited exponent n*(n+1)/2 is retained, including the
  dimension-zero orientation convention. No spin assumption, common rank,
  connectedness, positive dimension or additional characteristic-number
  equality is imposed in this differential specialization. -/
  exact P.toAtlasPseudodifferentialOperator.index_eq_base_characteristic_number O g hV q
    P.principalSymbol P.isSmoothOffZeroAtlasSymbol_principalSymbol
    P.isHomogeneousAtlasSymbol_principalSymbol
    (P.principalSymbol_toAtlasPseudodifferentialOperator_eq_regularized q) hi

end AtlasDifferentialOperator

end AtiyahSinger
