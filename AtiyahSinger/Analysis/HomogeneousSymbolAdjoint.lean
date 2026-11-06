/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import AtiyahSinger.Analysis.HermitianMetricSymbol
public import AtiyahSinger.Analysis.PrincipalSymbolAdjoint

/-!
# Hermitian adjoints of homogeneous elliptic principal data

Public module ID: M0743.

D03/D05/A07: connect the fiber adjoint to the regularized homogeneous principal
data used in the SG III.4 parametrix route. Homogeneity keeps the same real degree;
off-zero bijectivity is preserved in finite rank. Regularization choices differ
by all symbol orders, while actual PDO adjoints agree only at principal order.
These are explicit project bridges from SG III.3.11, III.4.3-4.7 and III.13 (13.5),
not a new definition of ellipticity for arbitrary full symbols.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- Positive real homogeneity is preserved with the same degree by the fiber adjoint. -/
theorem IsHomogeneousGlobalSymbol.globalSymbolAdjoint {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F} (hh : IsHomogeneousGlobalSymbol E F m a) :
    IsHomogeneousGlobalSymbol F E m (globalSymbolAdjoint (r := r) (q := q) a) := by
  /- Fix ξ≠0 and t>0. Adjoint the equality a(x,tξ)=t^m a(x,ξ). The scalar t^m
  is real, so conjugating it has no effect. The degree remains m, not -m. -/
  intro x ξ hξ t ht
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  change (a x (t • ξ)).adjoint = ((t ^ m : ℝ) : ℂ) • (a x ξ).adjoint
  rw [hh x ξ hξ t ht, map_smulₛₗ]
  simp

/-- Finite-rank fiber adjunction preserves exactly off-zero bijectivity. -/
theorem isEllipticGlobalSymbol_globalSymbolAdjoint_iff
    (a : GlobalSymbolFunction (n := n) E F) :
    IsEllipticGlobalSymbol F E (globalSymbolAdjoint (r := r) (q := q) a) ↔
      IsEllipticGlobalSymbol E F a := by
  /- At each nonzero covector, the orthogonal kernel and range identities show
  that injectivity and surjectivity of a finite-dimensional map pass to its
  adjoint. Apply these identities in both directions, using double adjunction
  for the converse. No equality of ranks or nonzero-rank assumption is supplied. -/
  constructor
  · intro ha x ξ hξ
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
    -- Orthogonal kernel and range identities turn adjoint bijectivity back into bijectivity.
    let T := (a x ξ).adjoint.toLinearMap
    have hT : Function.Bijective T := ha x ξ hξ
    have hinj : Function.Injective T.adjoint := by
      apply LinearMap.ker_eq_bot.mp
      rw [← LinearMap.orthogonal_range, LinearMap.range_eq_top.mpr hT.2]
      exact Submodule.top_orthogonal_eq_bot
    have hsurj : Function.Surjective T.adjoint := by
      apply LinearMap.range_eq_top.mp
      rw [← LinearMap.orthogonal_ker, LinearMap.ker_eq_bot.mpr hT.1]
      exact Submodule.bot_orthogonal_eq_top
    simpa only [Function.Bijective, T, ContinuousLinearMap.adjoint_toLinearMap,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.coe_coe] using And.intro hinj hsurj
  · intro ha x ξ hξ
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
    -- In finite dimension the adjoint range is exactly the orthogonal of the original kernel.
    let T := (a x ξ).toLinearMap
    have hinj : Function.Injective T.adjoint := by
      apply LinearMap.ker_eq_bot.mp
      rw [← LinearMap.orthogonal_range, LinearMap.range_eq_top.mpr (ha x ξ hξ).2]
      exact Submodule.top_orthogonal_eq_bot
    have hsurj : Function.Surjective T.adjoint := by
      apply LinearMap.range_eq_top.mp
      rw [← LinearMap.orthogonal_ker, LinearMap.ker_eq_bot.mpr (ha x ξ hξ).1]
      exact Submodule.bot_orthogonal_eq_top
    change Function.Bijective (a x ξ).adjoint
    simpa only [Function.Bijective, T, ContinuousLinearMap.adjoint_toLinearMap,
      ContinuousLinearMap.coe_coe] using And.intro hinj hsurj

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]

include hM hHE hHF in
/-- Smooth metrics preserve smoothness away from the zero section. -/
theorem IsSmoothOffZeroGlobalSymbol.globalSymbolAdjoint
    {a : GlobalSymbolFunction (n := n) E F}
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a) :
    IsSmoothOffZeroGlobalSymbol (n := n) (r := q) (q := r) F E
      (globalSymbolAdjoint (r := r) (q := q) a) := by
  /- In common frames use the weighted coordinate formula. Smooth Gram matrices
  and their inverses multiply the smooth conjugate transpose of a's coordinate
  expression. All operations are real-smooth on the open off-zero chart domain. -/
  -- Regard the installed smooth inner products as the original explicit metric data.
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let k := SmoothHermitianMetric.ofInnerProduct (n := n) (r := q) F
  have heq : h.symbolAdjoint k a = AtiyahSinger.globalSymbolAdjoint (r := r) (q := q) a := by
    funext x ξ
    apply h.adjoint_eq k x (a x ξ)
    intro u v
    change inner ℂ (a x ξ u) v =
      inner ℂ u (AtiyahSinger.globalSymbolAdjoint (r := r) (q := q) a x ξ v)
    exact globalSymbolAdjoint_inner a x ξ u v
  -- The already proved weighted Gram argument uses these exact two metric witnesses.
  rw [← heq]
  exact h.isSmoothOffZero_symbolAdjoint k hs

variable [hT : T2Space M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

set_option linter.overlappingInstances false in
-- Keep the original explicit and inherited smooth-bundle proofs in this included context.
include hM hHE hHF hT hE hF in
/-- Adjointing and regularizing in either direction differ by every symbol order. -/
theorem isGlobalSymbol_adjoint_regularizedSymbolFunction_sub
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E) (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) (l : ℝ) :
    IsGlobalSymbol (n := n) (r := q) (q := r) F E l
      (globalSymbolAdjoint (r := r) (q := q) (A.regularizedSymbolFunction a) -
        B.regularizedSymbolFunction (globalSymbolAdjoint (r := r) (q := q) a)) := by
  /- Stage 1: both terms are smooth order-m symbols by regularization and the
  three preceding adjoint properties. On each compact coordinate set the two
  high-frequency recovery formulas identify them with the same a(x,ξ)†.
  Stage 2: enlarge the compact set slightly within the common open domain before
  choosing a uniform radius. Their difference and all mixed derivatives then
  vanish outside a bounded frequency region on that neighborhood. Compact product
  bounds absorb any real order l. This is a statement about symbol functions,
  not equality of full symbols or of independently quantized operators. -/
  classical
  intro c hc f e _ _
  let V := symbolChartDomain E F c e f
  have hV : IsOpen V := isOpen_symbolChartDomain E F c e f
  have hswap : symbolChartDomain F E c f e = V := by
    ext z
    simp only [symbolChartDomain, V, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hswap]
  let pa := globalSymbolInChart F E
    (globalSymbolAdjoint (r := r) (q := q) (A.regularizedSymbolFunction a)) c f e
  let pb := globalSymbolInChart F E
    (B.regularizedSymbolFunction (globalSymbolAdjoint (r := r) (q := q) a)) c f e
  have hsub : globalSymbolInChart F E
      (globalSymbolAdjoint (r := r) (q := q) (A.regularizedSymbolFunction a) -
        B.regularizedSymbolFunction (globalSymbolAdjoint (r := r) (q := q) a)) c f e =
      pa - pb := by
    ext z η v
    simp [globalSymbolInChart, pa, pb]
  rw [hsub]
  -- Both representatives are smooth on this same full coordinate domain.
  have ha := (A.isGlobalSymbol_regularizedSymbolFunction m a hs hh).globalSymbolAdjoint
    c hc f e
  have hb := B.isGlobalSymbol_regularizedSymbolFunction m
    (globalSymbolAdjoint (r := r) (q := q) a) hs.globalSymbolAdjoint hh.globalSymbolAdjoint
    c hc f e
  rw [hswap] at ha hb
  have hd : ContDiffOn ℝ ∞ (Function.uncurry (pa - pb)) (V ×ˢ Set.univ) := ha.1.sub hb.1
  refine ⟨hd, ?_⟩
  intro K hKV hK i j
  -- Enlarge the compact base set before comparing frequencies, to control all base derivatives.
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hint : interior K' ⊆ V := interior_subset.trans hK'V
  have hK'swap : K' ⊆ symbolChartDomain F E c f e := by
    simpa only [hswap] using hK'V
  obtain ⟨RA, hRA, hrecoverA⟩ :=
    A.regularizedSymbolFunction_eq_inChart_at_high_frequency a c hc e f K' hK' hK'V
  obtain ⟨RB, hRB, hrecoverB⟩ :=
    B.regularizedSymbolFunction_eq_inChart_at_high_frequency
      (globalSymbolAdjoint (r := r) (q := q) a) c hc f e K' hK' hK'swap
  have hsupp : ∀ z ∈ interior K', ∀ η, max RA RB ≤ ‖η‖ → (pa - pb) z η = 0 := by
    intro z hz η hη
    have hzV := hint hz
    change globalSymbolInChart F E
        (globalSymbolAdjoint (r := r) (q := q) (A.regularizedSymbolFunction a)) c f e z η -
      globalSymbolInChart F E
        (B.regularizedSymbolFunction (globalSymbolAdjoint (r := r) (q := q) a)) c f e z η = 0
    -- The two Gram factors stay fixed while the original regularized symbol recovers a.
    rw [globalSymbolInChart_globalSymbolAdjoint (A.regularizedSymbolFunction a)
        c e f z η hzV.1.2 hzV.2,
      hrecoverA z (interior_subset hz) η ((le_max_left _ _).trans hη),
      hrecoverB z (interior_subset hz) η ((le_max_right _ _).trans hη),
      globalSymbolInChart_globalSymbolAdjoint a c e f z η hzV.1.2 hzV.2, sub_self]
  -- Smoothness and bounded frequency support on that neighborhood give every real order.
  have hlocal := isSmoothingSymbol_of_frequency_support isOpen_interior (pa - pb)
    (max RA RB) (hd.mono (Set.prod_mono hint subset_rfl)) hsupp l
  exact hlocal.2 K hKK' hK i j

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The homogeneous principal class commutes with adjunction across any two presentations. -/
theorem globalPrincipalSymbolAdjoint_regularizedSymbol
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E) (m : ℝ)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a) :
    globalPrincipalSymbolAdjoint
        (globalPrincipalSymbolClass E F m (A.regularizedSymbol m a hs hh)) =
      globalPrincipalSymbolClass F E m
        (B.regularizedSymbol m (globalSymbolAdjoint (r := r) (q := q) a)
          hs.globalSymbolAdjoint hh.globalSymbolAdjoint) := by
  /- Compute the quotient adjoint on A's regularized representative. The preceding
  all-order difference theorem at l=m-1 identifies its class with B's regularized
  adjoint data. No normalization at ξ=0 or ellipticity is required. -/
  rw [globalPrincipalSymbolAdjoint_class]
  apply (globalPrincipalSymbolClass_eq_iff F E m _ _).mpr
  exact isGlobalSymbol_adjoint_regularizedSymbolFunction_sub A B m a hs hh (m - 1)

variable [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- A PDO with homogeneous principal data has an adjoint with the adjoint homogeneous data. -/
theorem PseudodifferentialOperator.principalSymbol_formalAdjoint_of_homogeneous {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (A : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (B : QuantizationPresentation (n := n) (r := q) (q := r) F E)
    (a : GlobalSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroGlobalSymbol (n := n) (r := r) (q := q) E F a)
    (hh : IsHomogeneousGlobalSymbol E F m a)
    (hP : P.principalSymbol =
      globalPrincipalSymbolClass E F m (A.regularizedSymbol m a hs hh)) :
    P.formalAdjoint.principalSymbol = globalPrincipalSymbolClass F E m
      (B.regularizedSymbol m (globalSymbolAdjoint (r := r) (q := q) a)
        hs.globalSymbolAdjoint hh.globalSymbolAdjoint) := by
  -- The same homogeneous data and the two specified regularizations compute this class.
  rw [P.principalSymbol_formalAdjoint, hP]
  exact globalPrincipalSymbolAdjoint_regularizedSymbol A B m a hs hh

end AtiyahSinger
