/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.EquivariantHomogeneousAnalyticIndex
public import AtiyahSinger.Analysis.GlobalSymbolComposition
public import AtiyahSinger.Analysis.HomogeneousSymbolOperations
public import AtiyahSinger.Analysis.SmoothBundleMapOperator
public import AtiyahSinger.Analysis.ZeroOrderBundleMap
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

/-!
# Composition and invertible-bundle relations for the full symbol index

Public module ID: M0593.

The original degree-zero homogeneous symbol index is additive under
composition and vanishes when its off-zero map is a globally smooth
invertible equivariant bundle map. These are relations needed before descent
through compact-support K theory. No index on general K classes is assumed.

Sources: SG III.9, Definition 9.3 and the composition note following
Proposition 9.4, pp.212--213, referring to III.7(7.5); III.13, pp.246--247,
for elementary triples and identity stabilization. The precise original
smooth-symbol formulations are project supplements. Their proofs use
actual PDO realizations and the full kernel-minus-cokernel representations.

All ranks remain independent, with empty bases and dimension zero included.
The composition symbol is specified by its actual off-zero fiber map; its
values at zero are irrelevant. No new symbol carrier or composition is
introduced. Both relations are proved using the original geometric realizations
and full kernel and quotient-cokernel representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hLie : LieGroup IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)


include hM hT2 hSC hC hBorel hE hF hLie hGC hGT hGM hGB hAction hσE hσF

-- Reduce the original order-zero casts while retaining the exact operator interfaces.
set_option backward.isDefEq.respectTransparency false in
/-- A symbol given off zero by a smooth equivariant bundle isomorphism has zero full index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_zero_of_bundleIso
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      Iso E F)
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      IsSmoothBundleMap (n := n) (r := r) (q := q) e.toHom.linearMap)
    (heg : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      e.IsEquivariant σE σF)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (hes : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
        ∀ u : E x, s.val x ξ u = e.toHom.linearMap x u) :
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs = 0 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  obtain ⟨μ, hμ, hμInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h, hInvariant⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInvariant⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  -- Multiplication by the specified original isomorphism is the actual realization.
  let D : DifferentialOperator (n := n) (r := r) (q := q) E F 0 :=
    ⟨smoothSectionMap e.toHom.linearMap he,
      isDifferentialOperator_smoothSectionMap e.toHom.linearMap he⟩
  let P := smoothBundleMapOperator (μ := μ) e.toHom.linearMap he
  let : ∀ x, FiniteDimensional ℂ (E x) :=
    fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  have hsymbol (x : M) (ξ : CotangentFiber (n := n) x) :
      D.principalSymbolFunction x ξ = (e.toHom.linearMap x).toContinuousLinearMap := by
    ext v
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let e' := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    let f' := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hxc : x ∈ c.source := mem_chart_source _ x
    have hxe : x ∈ e'.baseSet := mem_baseSet_trivializationAt _ E x
    have hxf : x ∈ f'.baseSet := mem_baseSet_trivializationAt _ F x
    obtain ⟨U, hU, hxU, Q, hQ⟩ := D.isDifferentialOperator c (chart_mem_atlas _ x)
      e' f' x ⟨⟨hxc, hxe⟩, hxf⟩
    obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := r) x v
    -- At order zero both the operator and its principal polynomial use the same coefficient.
    have hvalue := hQ.2 u x hxU
    have hsection : sectionInChart E c e' u.val (c x) = (e' ⟨x, v⟩).2 := by
      unfold sectionInChart
      rw [c.left_inv hxc, hu]
    let : Inhabited (Fin (0 : Fin (0 + 1)).val → Fin n) := ⟨Fin.elim0⟩
    have hcoeff : (f' ⟨x, e.toHom.linearMap x v⟩).2 =
        Q.coefficient 0 default (c x) (e'.linearMapAt ℂ x v) := by
      simpa [CoordinateDifferentialOperator.apply, hsection, D, smoothSectionMap, hu,
        e'.coe_linearMapAt_of_mem hxe] using hvalue
    have hprincipal := LinearMap.congr_fun
      (D.hasPrincipalSymbol c (chart_mem_atlas _ x) e' f' U hU Q hQ x hxU ξ) v
    have hsame : f'.linearMapAt ℂ x (D.principalSymbol x ξ v) =
        f'.linearMapAt ℂ x (e.toHom.linearMap x v) := by
      simpa [CoordinateDifferentialOperator.principalSymbol,
        f'.coe_linearMapAt_of_mem hxf, hcoeff] using hprincipal
    have hcancel := congrArg (f'.symmL ℂ x) hsame
    change D.principalSymbol x ξ v = e.toHom.linearMap x v
    simpa only [f'.coe_linearMapAt_of_mem hxf, f'.symmL_apply hxf,
      f'.symm_apply_apply_mk hxf] using hcancel
  have hclass : P.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2) := by
    have hD := D.principalSymbol_eq_regularizedSymbol μ R
    have hhD : IsHomogeneousGlobalSymbol E F 0 D.principalSymbolFunction := by
      simpa only [Nat.cast_zero] using D.isHomogeneousGlobalSymbol_principalSymbolFunction
    have hregular := (R.regularizedSymbol_class_eq_iff R 0 D.principalSymbolFunction s.val
      D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction
      hhD s.property.1 s.property.2).mpr
        (fun x ξ hξ ↦ by
          rw [hsymbol]
          ext v
          exact (hes x ξ hξ v).symm)
    -- Transport the natural differential order to the exact real order of this PDO.
    have htransfer (l : ℝ) (hl : l = 0)
        (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ l)
        (hh : IsHomogeneousGlobalSymbol E F l D.principalSymbolFunction)
        (hQ : Q.toLinearMap = P.toLinearMap)
        (hQclass : Q.principalSymbol = globalPrincipalSymbolClass E F l
          (R.regularizedSymbol l D.principalSymbolFunction
            D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction hh)) :
        P.principalSymbol = globalPrincipalSymbolClass E F 0
          (R.regularizedSymbol 0 D.principalSymbolFunction
            D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction hhD) := by
      subst l
      exact (P.principalSymbol_eq_of_toLinearMap_eq μ Q hQ.symm).trans hQclass
    have hD0 := htransfer _ Nat.cast_zero (D.toPseudodifferentialOperator μ)
      D.isHomogeneousGlobalSymbol_principalSymbolFunction rfl hD
    exact hD0.trans hregular
  have hP : P.IsElliptic := ⟨_, hclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 s.val
      s.property.1 s.property.2).mpr hi⟩
  have hPg : P.IsEquivariant IG σE σF hσE hσF := by
    intro g
    ext u x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    change e.toHom.linearMap (g • y) (σE.sectionLinearMap g u.val (g • y)) =
      σF.sectionLinearMap g (fun z ↦ e.toHom.linearMap z (u.val z)) (g • y)
    rw [σE.sectionLinearMap_smul, σF.sectionLinearMap_smul]
    exact heg g y (u.val y)
  rw [equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF s hi hs
    μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP hclass]
  -- The exact L² realization is invertible, with the same dense smooth action.
  obtain ⟨U, hU⟩ := exists_l2Equiv_of_smoothBundleIso (μ := μ) e.linearEquiv he h k
  let T := P.metricL2Extension h k
  have hT : T = U.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer T.continuous U.continuous
    funext u
    exact (P.metricL2Extension_smooth h k u).trans (hU u).symm
  have hker : T.ker = ⊥ := by
    rw [hT]
    exact LinearMap.ker_eq_bot.mpr U.injective
  have hrange : T.range = ⊤ := by
    rw [hT]
    exact LinearMap.range_eq_top.mpr U.surjective
  let : Subsingleton T.ker := by rw [hker]; infer_instance
  let : Subsingleton (k.L2SectionSpace μ ⧸ T.range) := by rw [hrange]; infer_instance
  let hFred := P.isFredholm_metricL2Extension h k hP
  let : FiniteDimensional ℂ T.ker := hFred.finite_ker
  let : FiniteDimensional ℂ (k.L2SectionSpace μ ⧸ T.range) := hFred.finite_coker
  let : IsClosed (T.range : Set (k.L2SectionSpace μ)) := hFred.isClosed_range
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  have hTg := (P.isEquivariant_iff_metricL2Extension_intertwines
    IG σE σF hσE hσF h k hInvariant kInvariant hμInvariant).mp hPg
  -- Both finite representation carriers are zero, so their actual classes cancel.
  let Z : T.ker ≃L[ℂ] (k.L2SectionSpace μ ⧸ T.range) :=
    { toLinearEquiv := LinearEquiv.ofSubsingleton _ _
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  have hclasses := representationClass_eq_of_equiv
    (equivariantKernelRepresentation ρ τ T hTg)
    (equivariantCokernelRepresentation ρ τ T hTg)
    (continuous_equivariantKernelRepresentation ρ τ T hTg
      (h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant))
    (continuous_equivariantCokernelRepresentation ρ τ T hTg
      (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant))
    (ContRepresentation.Equiv.mk Z (fun _ ↦ Subsingleton.elim _ _))
  change representationClass _ _ - representationClass _ _ = 0
  exact sub_eq_zero.mpr hclasses

section Composition

variable {d : ℕ} {H : M → Type*}
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) H]
  [hH : IsSmoothComplexBundle (n := n) (r := d) H]
  (σH : letI := modelTopology (EuclideanSpace ℂ (Fin d)) H
    EquivariantStructure G H)
  (hσH : σH.IsSmooth (n := n) (r := d) IG)

include hH hσH

/-- Composition of the original elliptic equivariant symbols adds their full indices. -/
theorem equivariantHomogeneousAnalyticIndex_comp
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := q) (q := d) F H 0)
    (c : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := d) E H 0)
    (ha : IsEllipticGlobalSymbol E F a.val)
    (hb : IsEllipticGlobalSymbol F H b.val)
    (hc : IsEllipticGlobalSymbol E H c.val)
    (hag : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g a.val x ξ = a.val x ξ)
    (hbg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σF σH g b.val x ξ = b.val x ξ)
    (hcg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σH g c.val x ξ = c.val x ξ)
    (hcomp : ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      c.val x ξ = globalSymbolComp b.val a.val x ξ) :
    equivariantHomogeneousAnalyticIndex IG σE σH hσE hσH c hc hcg =
      equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF a ha hag +
        equivariantHomogeneousAnalyticIndex IG σF σH hσF hσH b hb hbg := by
  classical
  -- The same invariant geometry supplies one middle Hilbert representation for composition.
  obtain ⟨μ, hμ, hμInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h, hInvariant⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInvariant⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨j, jInvariant⟩ := exists_invariant_smoothHermitianMetric IG σH hσH
  obtain ⟨A⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  obtain ⟨B⟩ := nonempty_quantizationPresentation
    (n := n) (r := q) (q := d) (E := F) (F := H)
  obtain ⟨C⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := d) (E := E) (F := H)
  obtain ⟨P, hPg, hPclass⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG σE σF hσE hσF 0
    (globalPrincipalSymbolClass E F 0 (A.regularizedSymbol 0 a.val a.property.1 a.property.2))
    (fun g ↦ (A.equivariant_regularizedSymbol_class_eq_iff
      IG σE σF hσE hσF A 0 a a g).mpr (hag g))
  obtain ⟨Q, hQg, hQclass⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG σF σH hσF hσH 0
    (globalPrincipalSymbolClass F H 0 (B.regularizedSymbol 0 b.val b.property.1 b.property.2))
    (fun g ↦ (B.equivariant_regularizedSymbol_class_eq_iff
      IG σF σH hσF hσH B 0 b b g).mpr (hbg g))
  have hP : P.IsElliptic := ⟨_, hPclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff A 0 a.val
      a.property.1 a.property.2).mpr ha⟩
  have hQ : Q.IsElliptic := ⟨_, hQclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff B 0 b.val
      b.property.1 b.property.2).mpr hb⟩
  let S : PseudodifferentialOperator (n := n) (r := r) (q := d) E H μ 0 :=
    { toLinearMap := Q.toLinearMap.comp P.toLinearMap
      isPseudodifferentialOperator := by
        simpa only [PseudodifferentialOperator.comp, zero_add] using
          (Q.comp P).isPseudodifferentialOperator }
  -- The specified homogeneous product is compared before passing to any index.
  have hc' : IsHomogeneousGlobalSymbol E H (0 + 0) c.val := by
    simpa only [zero_add] using c.property.2
  let c' : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := d) E H (0 + 0) :=
    ⟨c.val, c.property.1, hc'⟩
  have hraw : (Q.comp P).principalSymbol = globalPrincipalSymbolClass E H (0 + 0)
      (C.regularizedSymbol (0 + 0) c.val c.property.1 hc') := by
    rw [Q.principalSymbol_comp P, hQclass, hPclass]
    exact globalPrincipalSymbolComp_regularizedSymbol_eq A B C a b c' hcomp
  have htransfer (l : ℝ) (hl : l = 0)
      (T : PseudodifferentialOperator (n := n) (r := r) (q := d) E H μ l)
      (hh : IsHomogeneousGlobalSymbol E H l c.val)
      (hT : T.toLinearMap = S.toLinearMap)
      (hclass : T.principalSymbol = globalPrincipalSymbolClass E H l
        (C.regularizedSymbol l c.val c.property.1 hh)) :
      S.principalSymbol = globalPrincipalSymbolClass E H 0
        (C.regularizedSymbol 0 c.val c.property.1 c.property.2) := by
    subst l
    exact (S.principalSymbol_eq_of_toLinearMap_eq μ T hT.symm).trans hclass
  have hSclass := htransfer _ (zero_add 0) (Q.comp P) hc' rfl hraw
  have hS : S.IsElliptic := ⟨_, hSclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff C 0 c.val
      c.property.1 c.property.2).mpr hc⟩
  have hSg : S.IsEquivariant IG σE σH hσE hσH := by
    intro g
    change (Q.toLinearMap.comp P.toLinearMap).comp _ = _
    rw [LinearMap.comp_assoc, hPg g, ← LinearMap.comp_assoc, hQg g,
      LinearMap.comp_assoc]
  rw [equivariantHomogeneousAnalyticIndex_eq IG σE σH hσE hσH c hc hcg
    μ hμ h j hInvariant jInvariant hμInvariant C S hSg hS hSclass,
    equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF a ha hag
    μ hμ h k hInvariant kInvariant hμInvariant A P hPg hP hPclass,
    equivariantHomogeneousAnalyticIndex_eq IG σF σH hσF hσH b hb hbg
    μ hμ k j kInvariant jInvariant hμInvariant B Q hQg hQ hQclass]
  -- Continuity and the common dense smooth sections identify the actual completed composite.
  have hSmetric : S.metricL2Extension h j =
      (Q.metricL2Extension k j).comp (P.metricL2Extension h k) := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer (S.metricL2Extension h j).continuous
      ((Q.metricL2Extension k j).comp (P.metricL2Extension h k)).continuous
    funext u
    change S.metricL2Extension h j (h.smoothToL2 μ u) =
      Q.metricL2Extension k j (P.metricL2Extension h k (h.smoothToL2 μ u))
    rw [S.metricL2Extension_smooth, P.metricL2Extension_smooth, Q.metricL2Extension_smooth]
    rfl
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let χ := j.l2ContRepresentation μ IG σH hσH jInvariant hμInvariant
  have hρ := h.continuous_l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  have hτ := k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  have hχ := j.continuous_l2ContRepresentation μ IG σH hσH jInvariant hμInvariant
  have hTg := (P.isEquivariant_iff_metricL2Extension_intertwines IG σE σF hσE hσF
    h k hInvariant kInvariant hμInvariant).mp hPg
  have hUg := (Q.isEquivariant_iff_metricL2Extension_intertwines IG σF σH hσF hσH
    k j kInvariant jInvariant hμInvariant).mp hQg
  have hindices := equivariantFredholmIndex_comp ρ τ χ hρ hτ hχ
    (fun g ↦ (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g).isometry)
    (fun g ↦ (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant g).isometry)
    (fun g ↦ (j.l2IsometryRepresentation μ IG σH hσH jInvariant hμInvariant g).isometry)
    (P.metricL2Extension h k) (Q.metricL2Extension k j) hTg hUg
    (P.isFredholm_metricL2Extension h k hP) (Q.isFredholm_metricL2Extension k j hQ)
  unfold PseudodifferentialOperator.equivariantAnalyticIndex
  simpa only [← hSmetric] using hindices

end Composition

end AtiyahSinger
