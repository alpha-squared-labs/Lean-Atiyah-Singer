/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.GeometricEquivariantIndex
public import AtiyahSinger.Analysis.ParametrixEllipticity
public import AtiyahSinger.Analysis.SmoothBundleMapOperator
public import AtiyahSinger.Analysis.ZeroOrderBundleMap

/-!
# Equivariant index under smooth bundle isomorphisms

Public module ID: M0475.

An original smooth equivariant source isomorphism and target isomorphism
transport an actual order-zero elliptic PDO to an actual PDO on the new
bundles. Its complete smooth-section action is the specified conjugation,
and its original representation-valued index is unchanged. The four invariant
Hermitian metrics are independent; the bundle isomorphisms need not be isometries.

Sources: SG III.3 Theorem 3.17(iii), printed p.187, for PDO composition, and
III.9 Definition 9.3 and Proposition 9.4, pp.212--213, for the equivariant index.
The exact bundle-isomorphism transport and its integral-completion comparison
are standard project supplements. The original smooth fiber maps act as the
zero-order differential operators described in SG III.1 and III.13.4.

The base, Borel structure and positive invariant density stay fixed. No
compactness of the group or isometry premise is needed after invariant metrics
and density are supplied. The four ranks are independent, including over an
empty base. This does not descend the index to arbitrary equivariant K classes
or supply a separate principal-symbol naturality interface. The proof constructs
the actual conjugated operator and compares its equivariant metric L² completions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
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
  {E' : M → Type*}
  [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) E']
  {F' : M → Type*}
  [∀ x, NormedAddCommGroup (F' x)] [∀ x, NormedSpace ℂ (F' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) F']
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hE' : IsSmoothComplexBundle (n := n) (r := r') E']
  [hF' : IsSmoothComplexBundle (n := n) (r := q') F']
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (σE' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    EquivariantStructure G E')
  (σF' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    EquivariantStructure G F')
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (hσE' : σE'.IsSmooth (n := n) (r := r') IG)
  (hσF' : σF'.IsSmooth (n := n) (r := q') IG)

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (h' : SmoothHermitianMetric (n := n) (r := r') E')
  (k' : SmoothHermitianMetric (n := n) (r := q') F')
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hInvariant' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    ∀ (g : G) (x : M) (u v : E' x),
      h'.pairing (g • x) (σE'.linearMap g x u) (σE'.linearMap g x v) = h'.pairing x u v)
  (kInvariant' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    ∀ (g : G) (x : M) (u v : F' x),
      k'.pairing (g • x) (σF'.linearMap g x u) (σF'.linearMap g x v) = k'.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hM hT2 hSC hC hBorel hE hF hE' hF' hμ hG hAction

/-- Smooth equivariant bundle isomorphisms transport actual PDOs and preserve the full index. -/
theorem exists_equivariant_bundleIso_transport
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      Iso E E')
    (f : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      Iso F F')
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      IsSmoothBundleMap (n := n) (r := r) (q := r') e.toHom.linearMap)
    (hf : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      IsSmoothBundleMap (n := n) (r := q) (q := q') f.toHom.linearMap)
    (heg : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      e.IsEquivariant σE σE')
    (hfg : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      f.IsEquivariant σF σF')
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    ∃ Q : PseudodifferentialOperator (n := n) (r := r') (q := q') E' F' μ 0,
      Q.toLinearMap = (smoothSectionEquiv f.linearEquiv hf).toLinearMap.comp
        (P.toLinearMap.comp (smoothSectionEquiv e.linearEquiv he).symm.toLinearMap) ∧
      ∃ hQg : Q.IsEquivariant IG σE' σF' hσE' hσF', ∃ hQ : Q.IsElliptic,
        P.equivariantAnalyticIndex IG σE σF hσE hσF
            h k hInvariant kInvariant hμInvariant hPg hP =
          Q.equivariantAnalyticIndex IG σE' σF' hσE' hσF'
            h' k' hInvariant' kInvariant' hμInvariant hQg hQ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin q')) F'
  let eS := smoothSectionEquiv e.linearEquiv he
  let fS := smoothSectionEquiv f.linearEquiv hf
  let A := smoothBundleMapOperator (μ := μ) e.toHom.linearMap he
  let Ai := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (e.linearEquiv x).symm.toLinearMap) (he.symm e.linearEquiv)
  let B := smoothBundleMapOperator (μ := μ) f.toHom.linearMap hf
  let Bi := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (f.linearEquiv x).symm.toLinearMap) (hf.symm f.linearEquiv)
  have hAmap : A.toLinearMap = eS.toLinearMap := rfl
  have hBmap : B.toLinearMap = fS.toLinearMap := rfl
  have hAimap : Ai.toLinearMap = eS.symm.toLinearMap := rfl
  have hBimap : Bi.toLinearMap = fS.symm.toLinearMap := rfl
  -- Compose the four actual multiplication operators with the specified PDO.
  let Q : PseudodifferentialOperator (n := n) (r := r') (q := q') E' F' μ 0 :=
    { toLinearMap := fS.toLinearMap.comp (P.toLinearMap.comp eS.symm.toLinearMap)
      isPseudodifferentialOperator := by
        have hp := P.isPseudodifferentialOperator.comp P.toLinearMap Ai.toLinearMap
          Ai.isPseudodifferentialOperator
        have hq := B.isPseudodifferentialOperator.comp B.toLinearMap _ hp
        rw [hBmap, hAimap] at hq
        simpa only [zero_add] using hq }
  obtain ⟨R, hR⟩ := P.exists_parametrix_of_isElliptic hP
  let Ri : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ 0 :=
    ⟨R.toLinearMap, by simpa only [neg_zero] using R.isPseudodifferentialOperator⟩
  let Q' : PseudodifferentialOperator (n := n) (r := q') (q := r') F' E' μ 0 :=
    { toLinearMap := eS.toLinearMap.comp (Ri.toLinearMap.comp fS.symm.toLinearMap)
      isPseudodifferentialOperator := by
        have hp := Ri.isPseudodifferentialOperator.comp Ri.toLinearMap Bi.toLinearMap
          Bi.isPseudodifferentialOperator
        have hq := A.isPseudodifferentialOperator.comp A.toLinearMap _ hp
        rw [hAmap, hBimap] at hq
        simpa only [zero_add] using hq }
  -- The same source and target equivalences conjugate the two genuine smooth remainders.
  have hQl : Q'.toLinearMap.comp Q.toLinearMap - LinearMap.id =
      eS.toLinearMap.comp ((R.toLinearMap.comp P.toLinearMap - LinearMap.id).comp
        eS.symm.toLinearMap) := by
    apply LinearMap.ext
    intro u
    change eS (R.toLinearMap (fS.symm (fS (P.toLinearMap (eS.symm u))))) - u =
      eS (R.toLinearMap (P.toLinearMap (eS.symm u)) - eS.symm u)
    rw [fS.symm_apply_apply, map_sub, eS.apply_symm_apply]
  have hQr : Q.toLinearMap.comp Q'.toLinearMap - LinearMap.id =
      fS.toLinearMap.comp ((P.toLinearMap.comp R.toLinearMap - LinearMap.id).comp
        fS.symm.toLinearMap) := by
    apply LinearMap.ext
    intro u
    change fS (P.toLinearMap (eS.symm (eS (R.toLinearMap (fS.symm u))))) - u =
      fS (P.toLinearMap (R.toLinearMap (fS.symm u)) - fS.symm u)
    rw [eS.symm_apply_apply, map_sub, fS.apply_symm_apply]
  have hQparam : IsParametrix μ Q.toLinearMap Q'.toLinearMap := by
    constructor
    · rw [hQl]
      exact A.isPseudodifferentialOperator.comp_isSmoothingOperator _ _
        (hR.1.comp_isPseudodifferentialOperator _ _ Ai.isPseudodifferentialOperator)
    · rw [hQr]
      exact B.isPseudodifferentialOperator.comp_isSmoothingOperator _ _
        (hR.2.comp_isPseudodifferentialOperator _ _ Bi.isPseudodifferentialOperator)
  have hQ : Q.IsElliptic := Q.isElliptic_of_isParametrix Q' hQparam
  -- The specified fiber squares intertwine the original smooth section actions.
  let RE := σE.smoothSectionRepresentation IG hσE
  let RF := σF.smoothSectionRepresentation IG hσF
  let RE' := σE'.smoothSectionRepresentation IG hσE'
  let RF' := σF'.smoothSectionRepresentation IG hσF'
  have heS (g : G) (u : smoothSections (n := n) (r := r) E) :
      eS (RE g u) = RE' g (eS u) := by
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    change e.toHom.linearMap (g • y) (σE.sectionLinearMap g u.val (g • y)) =
      σE'.sectionLinearMap g (fun z ↦ e.toHom.linearMap z (u.val z)) (g • y)
    rw [σE.sectionLinearMap_smul, σE'.sectionLinearMap_smul]
    exact heg g y (u.val y)
  have hfS (g : G) (u : smoothSections (n := n) (r := q) F) :
      fS (RF g u) = RF' g (fS u) := by
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    change f.toHom.linearMap (g • y) (σF.sectionLinearMap g u.val (g • y)) =
      σF'.sectionLinearMap g (fun z ↦ f.toHom.linearMap z (u.val z)) (g • y)
    rw [σF.sectionLinearMap_smul, σF'.sectionLinearMap_smul]
    exact hfg g y (u.val y)
  have hQg : Q.IsEquivariant IG σE' σF' hσE' hσF' := by
    intro g
    apply LinearMap.ext
    intro u
    have hin : eS.symm (RE' g u) = RE g (eS.symm u) := by
      apply eS.injective
      rw [eS.apply_symm_apply, heS, eS.apply_symm_apply]
    have hPgu : P.toLinearMap (RE g (eS.symm u)) =
        RF g (P.toLinearMap (eS.symm u)) := congrArg (fun T ↦ T (eS.symm u)) (hPg g)
    change fS (P.toLinearMap (eS.symm (RE' g u))) = RF' g (fS (P.toLinearMap (eS.symm u)))
    rw [hin, hPgu, hfS]
  -- Each original bundle isomorphism extends, with its own bounded inverse, to metric L².
  obtain ⟨eL, heL⟩ := exists_l2Equiv_of_smoothBundleIso (μ := μ) e.linearEquiv he h h'
  obtain ⟨fL, hfL⟩ := exists_l2Equiv_of_smoothBundleIso (μ := μ) f.linearEquiv hf k k'
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let ρ' := h'.l2ContRepresentation μ IG σE' hσE' hInvariant' hμInvariant
  let τ' := k'.l2ContRepresentation μ IG σF' hσF' kInvariant' hμInvariant
  have hequiv (g : G) : eL.toContinuousLinearMap.comp (ρ g) =
      (ρ' g).comp eL.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      (eL.toContinuousLinearMap.comp (ρ g)).continuous
      ((ρ' g).comp eL.toContinuousLinearMap).continuous
    funext u
    change eL (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g
      (h.smoothToL2 μ u)) = h'.l2IsometryRepresentation μ IG σE' hσE' hInvariant'
        hμInvariant g (eL (h.smoothToL2 μ u))
    rw [h.l2IsometryRepresentation_smoothToL2, heL, heL,
      h'.l2IsometryRepresentation_smoothToL2]
    exact congrArg (h'.smoothToL2 μ) (heS g u)
  have hfequiv (g : G) : fL.toContinuousLinearMap.comp (τ g) =
      (τ' g).comp fL.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply (k.denseRange_smoothToL2 μ).equalizer
      (fL.toContinuousLinearMap.comp (τ g)).continuous
      ((τ' g).comp fL.toContinuousLinearMap).continuous
    funext u
    change fL (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant g
      (k.smoothToL2 μ u)) = k'.l2IsometryRepresentation μ IG σF' hσF' kInvariant'
        hμInvariant g (fL (k.smoothToL2 μ u))
    rw [k.l2IsometryRepresentation_smoothToL2, hfL, hfL,
      k'.l2IsometryRepresentation_smoothToL2]
    exact congrArg (k'.smoothToL2 μ) (hfS g u)
  let eR : ContRepresentation.Equiv ρ ρ' := ContRepresentation.Equiv.mk eL hequiv
  let fR : ContRepresentation.Equiv τ τ' := ContRepresentation.Equiv.mk fL hfequiv
  -- The same four maps form the operator square on the dense smooth core and then on L².
  have hsquare : (Q.metricL2Extension h' k').comp eR.toContinuousLinearEquiv.toContinuousLinearMap =
      fR.toContinuousLinearEquiv.toContinuousLinearMap.comp (P.metricL2Extension h k) := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      ((Q.metricL2Extension h' k').comp eL.toContinuousLinearMap).continuous
      (fL.toContinuousLinearMap.comp (P.metricL2Extension h k)).continuous
    funext u
    change Q.metricL2Extension h' k' (eL (h.smoothToL2 μ u)) =
      fL (P.metricL2Extension h k (h.smoothToL2 μ u))
    rw [heL, Q.metricL2Extension_smooth, P.metricL2Extension_smooth, hfL]
    apply congrArg (k'.smoothToL2 μ)
    change fS (P.toLinearMap (eS.symm (eS u))) = fS (P.toLinearMap u)
    rw [eS.symm_apply_apply]
  refine ⟨Q, rfl, hQg, hQ, ?_⟩
  unfold equivariantAnalyticIndex
  exact equivariantFredholmIndex_eq_of_equiv ρ τ ρ' τ' _ _ _ _ eR fR _ _ _ _
    hsquare _ _

end AtiyahSinger.PseudodifferentialOperator
