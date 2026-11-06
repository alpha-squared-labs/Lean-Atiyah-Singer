/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Analysis.HermitianMetricDifferentialAdjoint
public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Geometry.AtlasConnectionContraction
public import AtiyahSinger.Geometry.ConnectionExistence
public import AtiyahSinger.Geometry.CotangentMetric
public import AtiyahSinger.Geometry.IteratedCovariantDerivative
public import AtiyahSinger.Geometry.NativeAtlasConnection

import AtiyahSinger.Analysis.CompactTestFormalAdjoint
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The connection Laplacian for the original metric and density

Public module ID: M1143.

A09: construct the actual second-order operator nabla-star nabla by its
integral adjunction identity. The connection, cotangent metric, Hermitian
metric and positive smooth measure remain explicit. The pointwise contraction
uses the original tangent fiber and its actual dual, not a new tensor carrier.
Its raw coordinate basis is not asserted to be a smooth global frame.

SG III.13, p.247, uses a unitary connection and integer powers of one plus
this Laplacian. Allowing any smooth complex connection and any supplied
positive density is a project supplement: its formal adjoint uses that same
metric and density, so nabla-star nabla remains nonnegative. The principal
symbol is the cotangent length squared with the convention D_j = -i partial_j.
The closed realization, real spectral powers and their PDO comparison are
separate constructions. Empty bases, zero dimension and rank zero are allowed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff ComplexConjugate Topology

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

/-- Contract the two original covariant derivatives with the supplied cotangent metric. -/
def connectionEnergyDensity (g : SmoothCotangentMetric (n := n) (M := M))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin r)) E)
    (u v : smoothSections (n := n) (r := r) E) (x : M) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    ((g.inner x (EuclideanSpace.proj i) (EuclideanSpace.proj j)) : ℂ) *
      h.pairing x (cov u.val x (EuclideanSpace.single i 1))
        (cov v.val x (EuclideanSpace.single j 1))

variable [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (cov : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)
  (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞)
  (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E cov)

include hM hE hT hSC hC hB hμ hcov hcomplex

set_option maxHeartbeats 1600000 in
-- The finite local-frame construction includes the full real bilinear change-of-basis argument.
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
omit hB hμ [MeasurableSpace M] in
/-- The original connection energy is a finite sum of pairings of actual first-order operators.
The same factorization constructs the Laplacian and supplies its integral symbol tests. -/
theorem exists_connectionEnergyDensity_decomposition :
    ∃ (N : ℕ)
      (A B : Fin N → DifferentialOperator (n := n) (r := r) (q := r) E E 1),
      ∀ (u v : smoothSections (n := n) (r := r) E) (x : M),
        connectionEnergyDensity g h cov u v x =
          ∑ i, h.pairing x (((A i).toLinearMap u).val x) (((B i).toLinearMap v).val x) := by
  classical
  -- Every original smooth tangent field defines its actual covariant first-order operator.
  have hdirectional (X : ∀ x : M, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
      (hX : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M))) :
      ∃ D : DifferentialOperator (n := n) (r := r) (q := r) E E 1,
        ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
          (D.toLinearMap u).val x = cov u.val x (X x) := by
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin r)
    let I := 𝓘(ℝ, H)
    let := ComplexBundle.modelTopology V E
    let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
    let e := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
    let c : AtlasSymbolFunction (n := n) E E :=
      fun x ξ ↦ (ξ (X x) : ℂ) • LinearMap.id
    have hc (x : M) : IsLinearMap ℝ (c x) := by
      constructor
      · intro ξ η
        simp only [c, add_apply, Complex.ofReal_add, add_smul]
      · intro a ξ
        simp only [c, smul_apply, smul_eq_mul, Complex.ofReal_mul]
        rw [mul_smul, Complex.coe_smul]
    -- Tangent coordinates of the given smooth vector field vary smoothly in every chart.
    have hXcoord (d : OpenPartialHomeomorph M H) (hd : d ∈ atlas H M) :
        ContDiffOn ℝ ∞ (fun z ↦ mfderiv I I d (d.symm z) (X (d.symm z))) d.target := by
      intro z hz
      have hd' := contMDiffAt_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd) (d.map_target hz)
      have htan := hd'.contMDiffAt_tangentMap
        (X := (⟨d.symm z, X (d.symm z)⟩ : TangentBundle I M)) (m := ∞) (by simp)
      have hmap := htan.comp (d.symm z) (hX (d.symm z))
      have hval := (contMDiff_snd_tangentBundle_modelSpace H I).contMDiffAt.comp
        (d.symm z) hmap
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd) hz
      exact ((hval.comp z hsymm).contDiffAt).contDiffWithinAt
    have hs : IsSmoothOffZeroAtlasSymbol A A c := by
      intro d hd i j
      let := i.property
      let := j.property
      let U := atlasSymbolChartDomain A A d i j ×ˢ {ξ : H | ξ ≠ 0}
      let scalar (z : H × H) : ℂ :=
        inner ℝ z.2 (mfderiv I I d (d.symm z.1) (X (d.symm z.1)))
      have hscalar : ContDiffOn ℝ ∞ scalar U := by
        apply Complex.ofRealCLM.contDiff.comp_contDiffOn
        exact contDiffOn_snd.inner ℝ ((hXcoord d hd).comp contDiffOn_fst
          (fun z hz ↦ hz.1.1.1))
      let T (z : H × H) : V →L[ℂ] V :=
        (i.val.coordChangeL ℂ j.val (d.symm z.1)).toContinuousLinearMap
      have hT : ContDiffOn ℝ ∞ T U := by
        have hbase := IsSmoothComplexBundle.contMDiffOn_coordChange
          (n := n) (E := E) i.val j.val
        have hsymm := contMDiffOn_symm_of_mem_maximalAtlas
          (I := I) (n := ∞) (IsManifold.subset_maximalAtlas hd)
        have htrans := hbase.comp
          (hsymm.mono (show atlasSymbolChartDomain A A d i j ⊆ d.target from
            fun _ hz ↦ hz.1.1)) (fun z hz ↦ ⟨hz.1.2, hz.2⟩)
        have htrans' : ContDiffOn ℝ ∞
            (fun z : H ↦ (i.val.coordChangeL ℂ j.val (d.symm z)).toContinuousLinearMap)
            (atlasSymbolChartDomain A A d i j) := contMDiffOn_iff_contDiffOn.mp htrans
        exact htrans'.comp contDiffOn_fst (fun z hz ↦ hz.1)
      apply (hscalar.smul hT).congr
      intro z hz
      have hi : d.symm z.1 ∈ (A.chart i).baseSet := hz.1.1.2
      have hj : d.symm z.1 ∈ (A.chart j).baseSet := hz.1.2
      let e₀ := EuclideanSpace.equiv (Fin r) ℂ
      let C (k : A.Index) (x : M) (hx : x ∈ (A.chart k).baseSet) : E x ≃ₗ[ℂ] V :=
        (A.frameLinearEquiv k x hx).trans e₀.symm.toLinearEquiv
      let (k : A.Index) : MemTrivializationAtlas k.val := k.property
      have hC (k : A.Index) (x : M) (hx : x ∈ (A.chart k).baseSet) :
          C k x hx = k.val.linearEquivAt ℂ x hx := by
        apply LinearEquiv.ext
        intro v
        exact e₀.symm_apply_apply (k.val ⟨x, v⟩).2
      apply ContinuousLinearMap.ext
      intro v
      dsimp only [Function.uncurry, atlasGlobalSymbolInChart]
      rw [dite_eq_left ⟨hi, hj⟩]
      change C j (d.symm z.1) hj
        ((covectorFromChart d (d.symm z.1) z.2 (X (d.symm z.1)) : ℂ) •
          ((C i (d.symm z.1) hi).symm v)) = scalar z • T z v
      rw [map_smul, hC, hC]
      congr 1
      change (j.val ⟨d.symm z.1, i.val.symm (d.symm z.1) v⟩).2 =
        i.val.coordChangeL ℂ j.val (d.symm z.1) v
      rw [i.val.coordChangeL_apply (R := ℂ) j.val ⟨hi, hj⟩]
    obtain ⟨covA, hcovA⟩ := exists_atlasComplexConnection_native cov hcov hcomplex
    let P := atlasConnectionContraction covA c hc hs
    let L := e.toLinearMap.comp (P.toLinearMap.comp e.symm.toLinearMap)
    have hL : IsDifferentialOperator E E 1 L := by
      intro d hd i hi j hj x hx
      let ia : A.Index := ⟨i, hi⟩
      let ja : A.Index := ⟨j, hj⟩
      obtain ⟨U, hU, hxU, Q, hQ⟩ := P.isAtlasDifferentialOperator d hd ia ja x hx
      refine ⟨U, hU, hxU, Q, hQ.1, ?_⟩
      intro u y hy
      have hlocal := hQ.2 (e.symm u) y hy
      have hcoord : atlasSectionInChart A d ia (e.symm u).val =
          sectionInChart E d i u.val := by
        funext z
        exact (EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply _
      rw [hcoord] at hlocal
      exact ((EuclideanSpace.equiv (Fin r) ℂ).symm_apply_apply _).symm.trans hlocal
    refine ⟨⟨L, hL⟩, ?_⟩
    intro u x
    change (P.toLinearMap (e.symm u)).val x = _
    rw [atlasConnectionContraction_apply]
    change (∑ a : Fin n, ((EuclideanSpace.proj (𝕜 := ℝ) a) (X x) : ℂ) •
      covA.covariantDerivative (e.symm u) x (EuclideanSpace.single a 1)) = _
    let w : EuclideanSpace ℝ (Fin n) := X x
    change (∑ a : Fin n, (w a : ℂ) •
      covA.covariantDerivative (e.symm u) x (EuclideanSpace.single a 1)) = _
    let T : EuclideanSpace ℝ (Fin n) →L[ℝ] E x := cov u.val x
    calc
      _ = ∑ a : Fin n, (w a : ℂ) • T (EuclideanSpace.single a 1) := by
        apply Finset.sum_congr rfl
        intro a _
        exact congrArg (fun v : E x ↦ (w a : ℂ) • v)
          (hcovA u x (EuclideanSpace.single a 1))
      _ = T (∑ a : Fin n, w a • EuclideanSpace.single a 1) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        exact (T.map_smul (w a) (EuclideanSpace.single a 1)).symm
      _ = T w := by
        congr 1
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr w
  -- A finite partition and two cutoffs retain each local tangent frame and its true dual.
  have hfields : ∃ (s : Finset M)
      (X Y : s × Fin n → ∀ x : M, TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
        (∀ a, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (fun x ↦ (⟨x, X a x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M))) ∧
        (∀ a, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (fun x ↦ (⟨x, Y a x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M))) ∧
        ∀ (u v : smoothSections (n := n) (r := r) E) (x : M),
          connectionEnergyDensity g h cov u v x =
            ∑ a, h.pairing x (cov u.val x (X a x)) (cov v.val x (Y a x)) := by
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, H)
    let TM := TangentSpace I (M := M)
    let e (x : M) := trivializationAt H TM x
    obtain ⟨b, hb⟩ : ∃ b : ∀ x : M, SmoothBumpFunction I x,
        ∀ x, tsupport (b x) ⊆ (e x).baseSet := by
      have hex (x : M) : ∃ b : SmoothBumpFunction I x, tsupport b ⊆ (e x).baseSet := by
        obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
          ((e x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x))
        exact ⟨b, hb⟩
      exact ⟨fun x ↦ (hex x).choose, fun x ↦ (hex x).choose_spec⟩
    let U (x : M) := interior {y : M | b x y = 1}
    have hU (x : M) : IsOpen (U x) := isOpen_interior
    have hxU (x : M) : x ∈ U x := mem_interior_iff_mem_nhds.mpr (b x).eventuallyEq_one
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    have hscover : (Set.univ : Set M) ⊆ ⋃ i : s, U i.val := by
      intro x _
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
      (fun i : s ↦ U i.val) (fun i ↦ hU i.val) hscover
    let t (i : s) (a : Fin n) (x : M) : TM x :=
      (e i.val).symmL ℝ x (EuclideanSpace.single a 1)
    let q (i : s) (a : Fin n) (x : M) : CotangentFiber (n := n) x :=
      (EuclideanSpace.proj a).comp ((e i.val).continuousLinearMapAt ℝ x)
    have ht (i : s) (a : Fin n) : ContMDiffOn I (I.prod 𝓘(ℝ, H)) ∞
        (fun x ↦ (⟨x, t i a x⟩ : TangentBundle I M)) (e i.val).baseSet := by
      intro x hx
      apply ContMDiffAt.contMDiffWithinAt
      apply ((e i.val).contMDiffAt_section_iff hx).mpr
      apply (contMDiffAt_const (c := EuclideanSpace.single a (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(e i.val).open_baseSet.mem_nhds hx] with y hy
      change ((e i.val) ⟨y, (e i.val).symmL ℝ y (EuclideanSpace.single a 1)⟩).2 = _
      rw [← (e i.val).continuousLinearMapAt_apply_of_mem ℝ hy,
        (e i.val).continuousLinearMapAt_symmL hy]
    have hq (i : s) (a : Fin n) : ContMDiffOn I (I.prod 𝓘(ℝ, H →L[ℝ] ℝ)) ∞
        (fun x ↦ (⟨x, q i a x⟩ : CotangentTotalSpace (n := n) (M := M)))
        (e i.val).baseSet := by
      let c := trivializationAt ℝ (Bundle.Trivial M ℝ) i.val
      let d := (e i.val).continuousLinearMap (RingHom.id ℝ) c
      apply (d.contMDiffOn_section_iff (e i.val).open_baseSet
        (fun x hx ↦ ⟨hx, by simp [c]⟩)).mpr
      apply (contMDiffOn_const (c := (EuclideanSpace.proj (𝕜 := ℝ) a))).congr
      intro x hx
      change (d ⟨x, q i a x⟩).2 = EuclideanSpace.proj a
      rw [Trivialization.continuousLinearMap_apply]
      ext z
      simp only [ContinuousLinearMap.comp_apply, q]
      rw [(e i.val).continuousLinearMapAt_symmL hx]
      simp [c]
      rfl
    let G (i : s) (a k : Fin n) (x : M) : ℝ := g.inner x (q i a x) (q i k x)
    have hG (i : s) (a k : Fin n) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (G i a k)
        (e i.val).baseSet := by
      have hp : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun x ↦ (⟨x, G i a k x⟩ : TotalSpace ℝ (Bundle.Trivial M ℝ)))
          (e i.val).baseSet :=
        g.contMDiff.contMDiffOn.clm_bundle_apply₂ (hq i a) (hq i k)
      intro x hx
      have hv := hp x hx
      rw [contMDiffWithinAt_totalSpace] at hv
      exact hv.2
    have hρsupport (i : s) : tsupport (ρ i) ⊆ (e i.val).baseSet := by
      intro x hx
      apply hb i.val
      apply subset_tsupport
      have hone : b i.val x = 1 :=
        interior_subset (s := {y : M | b i.val y = 1}) (hρ i hx)
      change b i.val x ≠ 0
      rw [hone]
      exact one_ne_zero
    let X (a : s × Fin n) (x : M) : TM x := b a.1.val x • t a.1 a.2 x
    let Y (a : s × Fin n) (x : M) : TM x :=
      ρ a.1 x • ∑ k : Fin n, G a.1 a.2 k x • t a.1 k x
    have hX (a : s × Fin n) : ContMDiff I (I.prod 𝓘(ℝ, H)) ∞
        (fun x ↦ (⟨x, X a x⟩ : TangentBundle I M)) :=
      (b a.1.val).contMDiff.contMDiffOn.smul_section_of_tsupport
        (e a.1.val).open_baseSet (hb a.1.val) (ht a.1 a.2)
    have hY (a : s × Fin n) : ContMDiff I (I.prod 𝓘(ℝ, H)) ∞
        (fun x ↦ (⟨x, Y a x⟩ : TangentBundle I M)) := by
      apply (ρ a.1).contMDiff.contMDiffOn.smul_section_of_tsupport
        (e a.1.val).open_baseSet (hρsupport a.1)
      exact ContMDiffOn.sum_section fun k _ ↦ (hG a.1 a.2 k).smul_section (ht a.1 k)
    have hframe (x : M) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
        (a b : EuclideanSpace ℝ (Fin n) →L[ℝ] E x) :
        (∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (EuclideanSpace.proj i) (EuclideanSpace.proj j) : ℂ) *
            h.pairing x (a (EuclideanSpace.single i 1)) (b (EuclideanSpace.single j 1))) =
          ∑ i : Fin n, ∑ j : Fin n,
            (g.inner x ((EuclideanSpace.proj i).comp L.toContinuousLinearMap)
              ((EuclideanSpace.proj j).comp L.toContinuousLinearMap) : ℂ) *
              h.pairing x (a (L.symm (EuclideanSpace.single i 1)))
                (b (L.symm (EuclideanSpace.single j 1))) := by
      classical
      let H := EuclideanSpace ℝ (Fin n)
      let p (i : Fin n) : H →L[ℝ] ℝ := EuclideanSpace.proj i
      let e (i : Fin n) : H := EuclideanSpace.single i 1
      have htrace (C : (H →L[ℝ] ℝ) →ₗ[ℝ] E x →ₗ[ℝ] ℂ)
          (P : H →ₗ[ℝ] E x) (T : H →L[ℝ] H) :
          ∑ i : Fin n, C (p i) (P (T (e i))) =
            ∑ i : Fin n, C ((p i).comp T) (P (e i)) := by
        have hsum (v : H) : ∑ i, v i • e i = v := by
          simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
            EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, e] using
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v
        have hpull (i : Fin n) : (p i).comp T = ∑ j, (T (e j)) i • p j := by
          apply ContinuousLinearMap.coe_injective
          apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
          intro j
          simp [p, e, EuclideanSpace.basisFun_apply]
          rfl
        calc
          _ = ∑ i, ∑ j, (T (e i)) j • C (p i) (P (e j)) := by
            apply Finset.sum_congr rfl
            intro i _
            conv_lhs => rw [← hsum (T (e i)), map_sum, map_sum]
            simp only [map_smul]
          _ = ∑ j, ∑ i, (T (e i)) j • C (p i) (P (e j)) := Finset.sum_comm
          _ = ∑ j, C ((p j).comp T) (P (e j)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hpull, map_sum]
            simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      let B : E x →ₗ[ℝ] E x →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (h.pairing x)
        (fun u v w ↦ (h.toCore x).add_left u v w)
        (by
          intro c u v
          change (h.toCore x).inner ((c : ℂ) • u) v = c • (h.toCore x).inner u v
          rw [InnerProductSpace.Core.inner_smul_left, Complex.conj_ofReal, Complex.real_smul])
        (fun u v w ↦ InnerProductSpace.Core.inner_add_right u v w)
        (by
          intro c u v
          change (h.toCore x).inner u ((c : ℂ) • v) = c • (h.toCore x).inner u v
          rw [InnerProductSpace.Core.inner_smul_right, Complex.real_smul])
      let C : (H →L[ℝ] ℝ) →ₗ[ℝ] E x →ₗ[ℝ] ℂ :=
        LinearMap.mk₂ ℝ (fun ξ u ↦ ∑ j : Fin n, g.inner x ξ (p j) • B u (b (e j)))
          (by intro ξ η u; simp [map_add, add_smul, Finset.sum_add_distrib])
          (by
            intro c ξ u
            simp only [map_smul, smul_apply, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
            ring)
          (by intro ξ u v; simp [map_add, smul_add, Finset.sum_add_distrib])
          (by
            intro c ξ u
            simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro j _
            exact smul_comm _ c _)
      have hfirst := htrace C (a.toLinearMap.comp L.symm.toLinearMap) L.toContinuousLinearMap
      change (∑ i : Fin n, C (p i) (a (L.symm (L (e i))))) =
        ∑ i : Fin n, C ((p i).comp L.toContinuousLinearMap) (a (L.symm (e i))) at hfirst
      simp only [ContinuousLinearEquiv.symm_apply_apply] at hfirst
      change (∑ i : Fin n, ∑ j : Fin n,
        g.inner x (p i) (p j) • B (a (e i)) (b (e j))) = _ at hfirst
      change (∑ i : Fin n, ∑ j : Fin n,
        g.inner x (p i) (p j) • B (a (e i)) (b (e j))) = _
      rw [hfirst]
      apply Finset.sum_congr rfl
      intro i _
      let C' : (H →L[ℝ] ℝ) →ₗ[ℝ] E x →ₗ[ℝ] ℂ :=
        LinearMap.mk₂ ℝ (fun ξ v ↦ g.inner x ((p i).comp L.toContinuousLinearMap) ξ •
          B (a (L.symm (e i))) v)
          (by intro ξ η u; simp [map_add, add_smul])
          (by
            intro c ξ u
            simp only [map_smul, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
            ring)
          (by intro ξ u v; simp [map_add, smul_add])
          (by
            intro c ξ u
            simp only [map_smul, Complex.real_smul]
            ring)
      have hsecond := htrace C' (b.toLinearMap.comp L.symm.toLinearMap) L.toContinuousLinearMap
      change (∑ j : Fin n, C' (p j) (b (L.symm (L (e j))))) =
        ∑ j : Fin n, C' ((p j).comp L.toContinuousLinearMap) (b (L.symm (e j))) at hsecond
      simp only [ContinuousLinearEquiv.symm_apply_apply] at hsecond
      simpa only [C, C', LinearMap.mk₂_apply, B, Complex.real_smul] using hsecond
    refine ⟨s, X, Y, hX, hY, ?_⟩
    intro u v x
    have hlocal (i : s) (hi : x ∈ (e i.val).baseSet) :
        connectionEnergyDensity g h cov u v x =
          ∑ a : Fin n, ∑ k : Fin n, (G i a k x : ℂ) *
            h.pairing x (cov u.val x (t i a x)) (cov v.val x (t i k x)) := by
      let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
        (e i.val).continuousLinearEquivAt ℝ x hi
      have hh := hframe x L (cov u.val x) (cov v.val x)
      have hsymm (a : Fin n) : L.symm (EuclideanSpace.single a 1) = t i a x :=
        congrFun ((e i.val).symm_continuousLinearEquivAt_eq hi) (EuclideanSpace.single a 1)
      simp only [hsymm] at hh
      dsimp only [L] at hh
      simp only [Trivialization.coe_continuousLinearEquivAt_eq'] at hh
      change connectionEnergyDensity g h cov u v x = _ at hh
      convert hh using 1
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    have hpairR (a z : E x) (c : ℝ) :
        h.pairing x a (c • z) = (c : ℂ) * h.pairing x a z := by
      change (h.toCore x).inner a ((c : ℂ) • z) = _
      exact InnerProductSpace.Core.inner_smul_right _ _
    have hpairSum (a : E x) (z : Fin n → E x) :
        h.pairing x a (∑ k, z k) = ∑ k, h.pairing x a (z k) := by
      let f : E x →+ ℂ := {
        toFun := h.pairing x a
        map_zero' := InnerProductSpace.Core.inner_zero_right _
        map_add' := fun z w ↦ InnerProductSpace.Core.inner_add_right a z w }
      exact map_sum f z Finset.univ
    have hterm (i : s) :
        (∑ a : Fin n, h.pairing x (cov u.val x (X (i, a) x))
          (cov v.val x (Y (i, a) x))) =
            (ρ i x : ℂ) * connectionEnergyDensity g h cov u v x := by
      by_cases hz : ρ i x = 0
      · simp only [Y, hz, zero_smul, map_zero, SmoothHermitianMetric.pairing,
          InnerProductSpace.Core.inner_zero_right, Finset.sum_const_zero,
          Complex.ofReal_zero, zero_mul]
      have hxs := subset_tsupport (ρ i) hz
      have hxe := hρsupport i hxs
      have hbone : b i.val x = 1 :=
        interior_subset (s := {y : M | b i.val y = 1}) (hρ i hxs)
      rw [hlocal i hxe, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [X, Y]
      rw [hbone, one_smul, map_smul, hpairR, map_sum, hpairSum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul, hpairR]
    rw [Fintype.sum_prod_type]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Complex.ofReal_sum]
    have hsum := ρ.sum_eq_one (Set.mem_univ x)
    rw [finsum_eq_sum_of_fintype] at hsum
    rw [hsum, Complex.ofReal_one, one_mul]
  obtain ⟨s, X, Y, hX, hY, henergy⟩ := hfields
  choose A hA using fun i : s × Fin n ↦ hdirectional (X i) (hX i)
  choose B hB using fun i : s × Fin n ↦ hdirectional (Y i) (hY i)
  let e := Fintype.equivFin (s × Fin n)
  refine ⟨Fintype.card (s × Fin n), (fun i ↦ A (e.symm i)), (fun i ↦ B (e.symm i)), ?_⟩
  intro u v x
  simp only [hA, hB]
  rw [henergy]
  exact (e.symm.sum_comp (fun i ↦
    h.pairing x (cov u.val x (X i x)) (cov v.val x (Y i x)))).symm

set_option maxHeartbeats 1600000 in
-- First-order composition is expanded into its original ordered second jets before summing.
set_option backward.isDefEq.respectTransparency false in
/-- Integral adjunction uniquely determines the actual second-order connection Laplacian. -/
theorem existsUnique_connectionLaplacian :
    ∃! P : DifferentialOperator (n := n) (r := r) (q := r) E E 2,
      ∀ u v : smoothSections (n := n) (r := r) E,
        h.sectionPairing μ u (P.toLinearMap v) =
          ∫ x, connectionEnergyDensity g h cov u v x ∂μ := by
  /- Stage 1: use the finite energy decomposition in actual global directional
  operators. Its simultaneous tangent/dual-basis change and two-cutoff argument
  have already retained the supplied connection and both metrics.
  Stage 2: compose each second directional operator with the metric formal
  adjoint of the first, using exactly h and μ, then sum. The local product rule
  proves that each actual composite has order at most two in every original
  chart and pair of bundle frames. Finite sums retain that certificate. The
  existing integral adjunction and the exact energy decomposition give the
  required global identity, without requiring the connection to preserve h.
  Stage 3: pair the difference of two candidate outputs with itself. Strict
  positivity of the same integral pairing makes their section maps equal;
  the differential-operator membership fields are propositions. -/
  classical
  -- Form actual second-order composites, with the product rule in every original chart.
  have hcomposition (P Q : DifferentialOperator (n := n) (r := r) (q := r) E E 1) :
      IsDifferentialOperator E E 2 (Q.toLinearMap.comp P.toLinearMap) := by
    classical
    have hcoordinate {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
        {r s q : ℕ} (P : CoordinateDifferentialOperator n r s 1 U)
        (Q : CoordinateDifferentialOperator n s q 1 U) :
        ∃ R : CoordinateDifferentialOperator n r q 2 U,
          ∀ (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)),
            ∀ x ∈ U, ContDiffAt ℝ ∞ v x → R.apply v x = Q.apply (P.apply v) x
   := by
      classical
      have hderiv {r q m : ℕ} (P : CoordinateDifferentialOperator n r q m U) (j : Fin n) :
          ∃ Q : CoordinateDifferentialOperator n r q (m + 1) U,
            ∀ (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r)),
              ∀ x ∈ U, ContDiffAt ℝ ∞ v x →
                Q.apply v x = (-Complex.I) • fderiv ℝ (P.apply v) x
                  (EuclideanSpace.single j 1) := by
        classical
        let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
        -- The product rule separates differentiated coefficients from the next ordered jet.
        let A : CoordinateDifferentialOperator n r q (m + 1) U := {
          coefficient := fun k α x ↦ if hk : k.val < m + 1 then
            (-Complex.I) • fderivWithin ℝ (P.coefficient ⟨k.val, hk⟩ α) U x e else 0
          smooth_coefficient := by
            intro k α
            by_cases hk : k.val < m + 1
            · simp only [dite_eq_left hk]
              exact ((P.smooth_coefficient ⟨k.val, hk⟩ α).fderivWithin hU.uniqueDiffOn
                (by simp)).clm_apply contDiffOn_const |>.const_smul _
            · simpa only [dite_eq_right hk] using (contDiffOn_const (c := (0 :
                EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))) }
        let B : CoordinateDifferentialOperator n r q (m + 1) U := {
          coefficient := Fin.cases (fun _ _ ↦ 0)
            (fun k α x ↦ if α ⟨0, Nat.zero_lt_succ k.val⟩ = j then
              P.coefficient k (Fin.tail α) x else 0)
          smooth_coefficient := by
            intro k
            refine Fin.cases (fun α ↦ contDiffOn_const) (fun k α ↦ ?_) k
            by_cases hα : α ⟨0, Nat.zero_lt_succ k.val⟩ = j
            · simpa only [Fin.cases_succ, ite_eq_left hα] using P.smooth_coefficient k (Fin.tail α)
            · simpa only [Fin.cases_succ, ite_eq_right hα] using (contDiffOn_const (c := (0 :
                EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))) }
        let Q : CoordinateDifferentialOperator n r q (m + 1) U := {
          coefficient := fun k α x ↦ A.coefficient k α x + B.coefficient k α x
          smooth_coefficient := fun k α ↦
            (A.smooth_coefficient k α).add (B.smooth_coefficient k α) }
        refine ⟨Q, ?_⟩
        intro v x hx hv
        -- Padding and reindexing retain the original redundant ordered-coefficient convention.
        have hA : A.apply v x = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
            (-Complex.I) • (fderivWithin ℝ (P.coefficient k α) U x e)
              (((-Complex.I) ^ k.val) • iteratedFDeriv ℝ k.val v x
                (fun t ↦ EuclideanSpace.single (α t) 1)) := by
          unfold CoordinateDifferentialOperator.apply
          rw [Fin.sum_univ_castSucc]
          simp only [A, Fin.val_castSucc, Fin.is_lt, dite_eq_left, Fin.eta,
            Fin.val_last, Nat.lt_irrefl, dite_false, zero_apply, Finset.sum_const_zero, add_zero,
            smul_apply]
        have hB : B.apply v x = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
            P.coefficient k α x (((-Complex.I) ^ (k.val + 1)) •
              iteratedFDeriv ℝ (k.val + 1) v x
                (Fin.cons e (fun t ↦ EuclideanSpace.single (α t) 1))) := by
          unfold CoordinateDifferentialOperator.apply
          rw [Fin.sum_univ_succ]
          simp only [B, Fin.cases_zero, zero_apply, Finset.sum_const_zero,
            zero_add, Fin.cases_succ, Fin.val_succ]
          apply Finset.sum_congr rfl
          intro k hk
          rw [← (Fin.consEquiv (fun _ : Fin (k.val + 1) ↦ Fin n)).sum_comp,
            Fintype.sum_prod_type]
          simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.tail_cons]
          rw [Finset.sum_eq_single j]
          · apply Finset.sum_congr rfl
            intro α hα
            have hhead : Fin.cons (α := fun _ : Fin (k.val + 1) ↦ Fin n) j α
                ⟨0, Nat.zero_lt_succ k.val⟩ = j := by simp [Fin.cons]
            rw [ite_eq_left hhead]
            congr 2
          · intro i hi hij
            simp [hij]
          · simp
        have hsplit : Q.apply v x = A.apply v x + B.apply v x := by
          simp only [CoordinateDifferentialOperator.apply, Q,
            add_apply, Finset.sum_add_distrib]
        -- Apply the real bilinear product rule to every coefficient and jet, then sum.
        let J (k : Fin (m + 1)) (α : Fin k.val → Fin n) := fun y ↦
          ((-Complex.I) ^ k.val) • iteratedFDeriv ℝ k.val v y
            (fun t ↦ EuclideanSpace.single (α t) 1)
        have hJ (k : Fin (m + 1)) (α : Fin k.val → Fin n) : ContDiffAt ℝ ∞ (J k α) x :=
          ((ContinuousMultilinearMap.apply ℝ _ _
            (fun t ↦ EuclideanSpace.single (α t) 1)).contDiff.contDiffAt.comp x
            (hv.iteratedFDeriv_right (m := ∞) (i := k.val) (by simp))).const_smul _
        have hc (k : Fin (m + 1)) (α : Fin k.val → Fin n) :
            DifferentiableAt ℝ (P.coefficient k α) x :=
          ((P.smooth_coefficient k α).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
        let B₀ := (ContinuousLinearMap.id ℂ
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))).bilinearRestrictScalars ℝ
        have ht (k : Fin (m + 1)) (α : Fin k.val → Fin n) :=
          B₀.hasFDerivAt_of_bilinear (hc k α).hasFDerivAt
            ((hJ k α).differentiableAt (by simp)).hasFDerivAt
        have hsum := HasFDerivAt.sum (u := Finset.univ) (fun k hk ↦
          HasFDerivAt.sum (u := Finset.univ) (fun α hα ↦ ht k α))
        have heq : P.apply v = ∑ k : Fin (m + 1), ∑ α : Fin k.val → Fin n,
            (fun y ↦ B₀ (P.coefficient k α y) (J k α y)) := by
          funext y
          simp only [Finset.sum_apply]
          rfl
        rw [hsplit, hA, hB, heq]
        rw [hsum.fderiv]
        simp only [sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro α hα
        have hdJ : fderiv ℝ (J k α) x e = ((-Complex.I) ^ k.val) •
            iteratedFDeriv ℝ (k.val + 1) v x
              (Fin.cons e (fun t ↦ EuclideanSpace.single (α t) 1)) := by
          let L := ContinuousMultilinearMap.apply ℝ
            (fun _ : Fin k.val ↦ EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin r))
            (fun t ↦ EuclideanSpace.single (α t) 1)
          have hD := (hv.iteratedFDeriv_right (m := ∞) (i := k.val) (by simp)).differentiableAt
            (by simp)
          have hL := L.hasFDerivAt.comp x hD.hasFDerivAt
          change (fderiv ℝ (((-Complex.I) ^ k.val) • (L ∘ iteratedFDeriv ℝ k.val v)) x) e = _
          rw [fderiv_const_smul hL.differentiableAt, hL.fderiv]
          rfl
        rw [fderivWithin_of_isOpen hU hx]
        change (-Complex.I) • (fderiv ℝ (P.coefficient k α) x e) (J k α x) +
            P.coefficient k α x (((-Complex.I) ^ (k.val + 1)) •
              iteratedFDeriv ℝ (k.val + 1) v x
                (Fin.cons e (fun t ↦ EuclideanSpace.single (α t) 1))) =
          (-Complex.I) • (P.coefficient k α x (fderiv ℝ (J k α) x e) +
            (fderiv ℝ (P.coefficient k α) x e) (J k α x))
        rw [hdJ]
        simp only [map_smul, smul_add, pow_succ, mul_smul]
        module
      choose D hD using fun j : Fin n ↦ hderiv P j
      let P₂ : CoordinateDifferentialOperator n r s 2 U := {
        coefficient := fun k α z ↦ if hk : k.val < 2 then P.coefficient ⟨k.val, hk⟩ α z else 0
        smooth_coefficient := by
          intro k α
          by_cases hk : k.val < 2
          · simpa only [dite_eq_left hk] using P.smooth_coefficient ⟨k.val, hk⟩ α
          · simp only [dite_eq_right hk]
            exact contDiffOn_const }
      have hP₂ (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
          (x : EuclideanSpace ℝ (Fin n)) : P₂.apply v x = P.apply v x := by
        unfold CoordinateDifferentialOperator.apply
        rw [Fin.sum_univ_castSucc]
        simp only [P₂, Fin.val_castSucc, Fin.is_lt, dite_eq_left, Fin.eta,
          Fin.val_last, Nat.lt_irrefl, dite_false, zero_apply, Finset.sum_const_zero, add_zero]
      let Z (z : EuclideanSpace ℝ (Fin n)) := Q.coefficient 0 (fun t ↦ Fin.elim0 t) z
      let B (j : Fin n) (z : EuclideanSpace ℝ (Fin n)) := Q.coefficient 1 (fun _ ↦ j) z
      have hZ : ContDiffOn ℝ ∞ Z U := Q.smooth_coefficient 0 _
      have hB (j : Fin n) : ContDiffOn ℝ ∞ (B j) U := Q.smooth_coefficient 1 _
      let mul := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin s)) (EuclideanSpace ℂ (Fin q))).bilinearRestrictScalars ℝ
      let R : CoordinateDifferentialOperator n r q 2 U := {
        coefficient := fun k α z ↦ (Z z).comp (P₂.coefficient k α z) +
          ∑ j : Fin n, (B j z).comp ((D j).coefficient k α z)
        smooth_coefficient := by
          intro k α
          apply ContDiffOn.add
          · exact (mul.contDiff.comp_contDiffOn hZ).clm_apply (P₂.smooth_coefficient k α)
          · apply ContDiffOn.sum
            intro j _
            exact (mul.contDiff.comp_contDiffOn (hB j)).clm_apply ((D j).smooth_coefficient k α) }
      have hR (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
          (x : EuclideanSpace ℝ (Fin n)) : R.apply v x =
            Z x (P₂.apply v x) + ∑ j : Fin n, B j x ((D j).apply v x) := by
        simp only [CoordinateDifferentialOperator.apply, R, add_apply, sum_apply,
          ContinuousLinearMap.comp_apply, Finset.sum_add_distrib, map_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      have hQ (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin s))
          (x : EuclideanSpace ℝ (Fin n)) : Q.apply v x =
            Z x (v x) + ∑ j : Fin n, B j x ((-Complex.I) •
              fderiv ℝ v x (EuclideanSpace.single j 1)) := by
        let reindex : (Fin 1 → Fin n) ≃ Fin n := {
          toFun α := α 0
          invFun j := fun _ ↦ j
          left_inv α := by
            funext t
            exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
          right_inv _ := rfl }
        unfold CoordinateDifferentialOperator.apply
        rw [Fin.sum_univ_two]
        simp only [Fin.val_zero, pow_zero, one_smul, iteratedFDeriv_zero_apply,
          Fintype.sum_unique, Fin.val_one, pow_one, iteratedFDeriv_one_apply]
        congr 1
        rw [← reindex.symm.sum_comp]
        rfl
      refine ⟨R, ?_⟩
      intro v x hx hv
      rw [hR, hP₂, hQ]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hD j v x hx hv]
    intro c hc e he f hf x hx
    obtain ⟨U, hU, hxU, A, hA⟩ := P.isDifferentialOperator c hc e e x ⟨hx.1, hx.1.2⟩
    obtain ⟨V, hV, hxV, B, hB⟩ := Q.isDifferentialOperator c hc e f x hx
    let W := U ∩ V
    have hW : IsOpen W := hU.inter hV
    have hWs : W ⊆ c.source := fun y hy ↦ (hA.1 hy.1).1.1
    have hcW : IsOpen (c '' W) := c.isOpen_image_of_subset_source hW hWs
    let A' : CoordinateDifferentialOperator n r r 1 (c '' W) := {
      coefficient := A.coefficient
      smooth_coefficient := fun k α ↦ (A.smooth_coefficient k α).mono
        (Set.image_mono Set.inter_subset_left) }
    let B' : CoordinateDifferentialOperator n r r 1 (c '' W) := {
      coefficient := B.coefficient
      smooth_coefficient := fun k α ↦ (B.smooth_coefficient k α).mono
        (Set.image_mono Set.inter_subset_right) }
    obtain ⟨C, hC⟩ := hcoordinate hcW A' B'
    refine ⟨W, hW, ⟨hxU, hxV⟩, C, (fun y hy ↦ hB.1 hy.2), ?_⟩
    intro s y hy
    change (f ⟨y, (Q.toLinearMap (P.toLinearMap s)).val y⟩).2 = _
    rw [hB.2 (P.toLinearMap s) y hy.2]
    have hyc := hWs hy
    have hye := (hA.1 hy.1).1.2
    have hcy : c y ∈ c '' W := Set.mem_image_of_mem c hy
    have hgerm : sectionInChart E c e (P.toLinearMap s).val =ᶠ[nhds (c y)]
        A'.apply (sectionInChart E c e s.val) := by
      filter_upwards [hcW.mem_nhds hcy] with z hz
      obtain ⟨t, ht, rfl⟩ := hz
      change (e ⟨c.symm (c t), (P.toLinearMap s).val (c.symm (c t))⟩).2 = _
      rw [c.left_inv (hWs ht)]
      exact hA.2 s t ht.1
    have hlocal : ContDiffAt ℝ ∞ (sectionInChart E c e s.val) (c y) := by
      have hsection := (s.property e he).contMDiffAt
        (e.open_baseSet.mem_nhds (show c.symm (c y) ∈ e.baseSet by
          simpa only [c.left_inv hyc] using hye))
      have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) hc)
        (c.map_source hyc)
      have hcomp := hsection.comp (c y) hsymm
      exact hcomp.contDiffAt
    rw [hC _ (c y) hcy hlocal]
    change B'.apply (sectionInChart E c e (P.toLinearMap s).val) (c y) = _
    simp only [CoordinateDifferentialOperator.apply]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro α _
    rw [(hgerm.iteratedFDeriv ℝ k.val).eq_of_nhds]
  -- Finite sums preserve the same order bound on the common original chart intersection.
  have hsum {N : ℕ} (T : Fin N → DifferentialOperator (n := n) (r := r) (q := r) E E 2) :
      IsDifferentialOperator E E 2 (∑ i, (T i).toLinearMap) := by
    classical
    intro c hc e he f hf x hx
    choose U hU hxU D hD using fun i : Fin N ↦
      (T i).isDifferentialOperator c hc e f x hx
    let W := (c.source ∩ e.baseSet ∩ f.baseSet) ∩ ⋂ i, U i
    have hW : IsOpen W :=
      ((c.open_source.inter e.open_baseSet).inter f.open_baseSet).inter
        (isOpen_iInter_of_finite hU)
    have hWU (i : Fin N) : W ⊆ U i := fun y hy ↦ Set.mem_iInter.mp hy.2 i
    let Q : CoordinateDifferentialOperator n r r 2 (c '' W) := {
      coefficient := fun k α z ↦ ∑ i, (D i).coefficient k α z
      smooth_coefficient := by
        intro k α
        apply ContDiffOn.sum
        intro i _
        exact ((D i).smooth_coefficient k α).mono (Set.image_mono (hWU i)) }
    refine ⟨W, hW, ⟨hx, Set.mem_iInter.mpr hxU⟩, Q, Set.inter_subset_left, ?_⟩
    intro s y hy
    change (f ⟨y, ((∑ i, (T i).toLinearMap) s).val y⟩).2 = _
    rw [← f.continuousLinearMapAt_apply_of_mem ℂ hy.1.2]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, map_sum]
    have hpoint (i : Fin N) :
        f.continuousLinearMapAt ℂ y (((T i).toLinearMap s).val y) =
          (D i).apply (sectionInChart E c e s.val) (c y) := by
      rw [f.continuousLinearMapAt_apply_of_mem ℂ hy.1.2]
      exact (hD i).2 s y (hWU i hy)
    simp_rw [hpoint]
    simp only [CoordinateDifferentialOperator.apply, Q, sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
  obtain ⟨N, A, B, henergy⟩ :=
    exists_connectionEnergyDensity_decomposition g h cov hcov hcomplex
  let T (i : Fin N) : DifferentialOperator (n := n) (r := r) (q := r) E E 2 := {
    toLinearMap := ((A i).metricFormalAdjoint (μ := μ) h h).toLinearMap.comp (B i).toLinearMap
    isDifferentialOperator := hcomposition (B i) ((A i).metricFormalAdjoint (μ := μ) h h) }
  let P : DifferentialOperator (n := n) (r := r) (q := r) E E 2 :=
    ⟨∑ i, (T i).toLinearMap, hsum T⟩
  have hP (u v : smoothSections (n := n) (r := r) E) :
      h.sectionPairing μ u (P.toLinearMap v) =
        ∫ x, connectionEnergyDensity g h cov u v x ∂μ := by
    -- Each summand uses precisely the supplied Hermitian metric and density in its adjoint.
    have hPv : P.toLinearMap v = ∑ i : Fin N,
        ((A i).metricFormalAdjoint (μ := μ) h h).toLinearMap ((B i).toLinearMap v) := by
      simp only [P, LinearMap.sum_apply, T, LinearMap.comp_apply]
    rw [← h.inner_smoothToL2, hPv, map_sum, inner_sum]
    simp_rw [h.inner_smoothToL2]
    have hterm (i : Fin N) := (A i).isMetricFormalAdjoint_metricFormalAdjoint
      (μ := μ) h h u ((B i).toLinearMap v)
    simp_rw [← hterm]
    unfold SmoothHermitianMetric.sectionPairing
    rw [← integral_finsetSum _ (fun i _ ↦
      h.integrable_pairing μ ((A i).toLinearMap u) ((B i).toLinearMap v))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (henergy u v x).symm)
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  -- The original positive integral form separates every smooth output of two candidates.
  have hmaps : Q.toLinearMap = P.toLinearMap := by
    apply LinearMap.ext
    intro v
    let δ := Q.toLinearMap v - P.toLinearMap v
    have heq := (hQ δ v).trans (hP δ v).symm
    have hzero : h.sectionPairing μ δ δ = 0 := by
      have hsub := inner_sub_right (𝕜 := ℂ) (h.smoothToL2 μ δ)
        (h.smoothToL2 μ (Q.toLinearMap v)) (h.smoothToL2 μ (P.toLinearMap v))
      rw [← map_sub, h.inner_smoothToL2, h.inner_smoothToL2, h.inner_smoothToL2] at hsub
      exact hsub.trans (sub_eq_zero.mpr heq)
    exact sub_eq_zero.mp ((h.sectionPairing_self_eq_zero_iff μ δ).mp hzero)
  cases Q with
  | mk L hL =>
    change L = ∑ i, (T i).toLinearMap at hmaps
    subst L
    rfl

/-- The actual connection Laplacian selected by its metric-density adjunction identity. -/
def connectionLaplacian : DifferentialOperator (n := n) (r := r) (q := r) E E 2 :=
  (existsUnique_connectionLaplacian μ g h cov hcov hcomplex).exists.choose

/-- The chosen operator retains the energy of the same connection, metric and density. -/
theorem connectionLaplacian_pairing (u v : smoothSections (n := n) (r := r) E) :
    h.sectionPairing μ u ((connectionLaplacian μ g h cov hcov hcomplex).toLinearMap v) =
      ∫ x, connectionEnergyDensity g h cov u v x ∂μ := by
  /- Apply the specification of the exact existence witness used to define
  connectionLaplacian. It retains all four supplied geometric data and both
  original smooth sections, rather than choosing another formal adjoint. -/
  exact (existsUnique_connectionLaplacian μ g h cov hcov hcomplex).exists.choose_spec u v

/-- The connection Laplacian is formally symmetric for the original integral pairing. -/
theorem connectionLaplacian_symmetric (u v : smoothSections (n := n) (r := r) E) :
    h.sectionPairing μ ((connectionLaplacian μ g h cov hcov hcomplex).toLinearMap u) v =
      h.sectionPairing μ u ((connectionLaplacian μ g h cov hcov hcomplex).toLinearMap v) := by
  /- The real cotangent form is symmetric, and the original fiber pairing
  is conjugate symmetric. Exchange the two finite-sum indices to obtain
  conjugate symmetry of the energy. Apply the adjunction identity to v,u,
  then conjugate the integral and both pairings. This is symmetry on the
  smooth core; unbounded self-adjointness belongs to the operator realization. -/
  rw [← h.sectionPairing_conj_symm μ,
    connectionLaplacian_pairing μ g h cov hcov hcomplex,
    connectionLaplacian_pairing μ g h cov hcov hcomplex, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    iteratedCovariantPairing_conj_symm g h 1 x (cov u.val x) (cov v.val x)

/-- The real quadratic form of the connection Laplacian is nonnegative. -/
theorem connectionLaplacian_nonneg (u : smoothSections (n := n) (r := r) E) :
    0 ≤ (h.sectionPairing μ u
      ((connectionLaplacian μ g h cov hcov hcomplex).toLinearMap u)).re := by
  /- Use the finite energy decomposition to obtain integrability in the same
  measure. The invariant covariant-pairing theorem at order one gives
  pointwise nonnegativity; its orthonormal-frame argument expresses the
  energy as squared h-lengths of the original covariant derivatives.
  Move the real part through this integral and apply integral nonnegativity.
  The adjunction identity gives the asserted quadratic form. -/
  rw [connectionLaplacian_pairing μ g h cov hcov hcomplex]
  -- The finite decomposition expresses the same energy through integrable smooth pairings.
  obtain ⟨N, A, B, henergy⟩ :=
    exists_connectionEnergyDensity_decomposition g h cov hcov hcomplex
  have hint : Integrable (connectionEnergyDensity g h cov u u) μ := by
    have hsum := integrable_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) ↦
      h.integrable_pairing μ ((A i).toLinearMap u) ((B i).toLinearMap u))
    simpa only [← henergy] using hsum
  have hre := integral_re hint
  simp only [RCLike.re_eq_complex_re] at hre
  rw [← hre]
  exact integral_nonneg fun x ↦
    iteratedCovariantPairing_self_nonneg g h 1 x (cov u.val x)

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
-- Normalize the original energy identity and scalar first-jet tests for the second-order symbol.
/-- The actual homogeneous principal symbol is length squared times the fiber identity. -/
theorem connectionLaplacian_principalSymbol (x : M) (ξ : CotangentFiber (n := n) x) :
    (connectionLaplacian μ g h cov hcov hcomplex).principalSymbol x ξ =
      (g.length x ξ ^ 2 : ℂ) • LinearMap.id := by
  /- Use real scalar multipliers to recover the second-order symbol from the
  original energy identity. Smooth cotangent contraction makes the comparison
  an equality of genuine smooth sections; positive integral pairing identifies
  their values. A prescribed scalar first jet and an arbitrary fiber value
  then test the original principal symbol, with its D_j = -i partial_j sign. -/
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let SE := smoothSections (n := n) (r := r) E
  let P := connectionLaplacian μ g h cov hcov hcomplex
  -- Stage 1: obtain integrable energy and smooth contraction of the actual differential.
  have henergy (u v : SE) : Integrable (connectionEnergyDensity g h cov u v) μ := by
    obtain ⟨N, A, B, heq⟩ := exists_connectionEnergyDensity_decomposition g h cov hcov hcomplex
    simpa only [← heq] using integrable_finsetSum Finset.univ
      (fun i (_ : i ∈ Finset.univ) ↦
        h.integrable_pairing μ ((A i).toLinearMap u) ((B i).toLinearMap v))
  have hdSmooth (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) :
      ContMDiff I (I.prod 𝓘(ℝ, CotangentModel n)) ∞
        (fun y ↦ (⟨y, mfderiv I 𝓘(ℝ, ℝ) φ y⟩ :
          CotangentTotalSpace (n := n) (M := M))) := by
    intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hd := (hφ x).mfderiv_const (m := ∞) (by simp)
    apply hd.congr_of_eventuallyEq
    filter_upwards [] with y
    simp +unfoldPartialApp only [ContinuousLinearMap.inCoordinates,
      Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp, inTangentCoordinates,
      TangentBundle.continuousLinearMapAt_model_space, id_eq]
    ext v
    rfl
  have hscalarSmooth (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y ↦ g.inner y
        (mfderiv I 𝓘(ℝ, ℝ) φ y) (mfderiv I 𝓘(ℝ, ℝ) φ y)) := by
    have hh := g.contMDiff.clm_bundle_apply₂ (hdSmooth φ hφ) (hdSmooth φ hφ)
    intro y
    exact (contMDiffAt_totalSpace.mp (hh y)).2
  have pair_add (u v w : SE) :
      h.sectionPairing μ u (v + w) = h.sectionPairing μ u v + h.sectionPairing μ u w := by
    let : InnerProductSpace.Core ℂ SE := h.smoothL2SectionCore μ
    exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) u v w
  have pair_sub (u v w : SE) :
      h.sectionPairing μ u (v - w) = h.sectionPairing μ u v - h.sectionPairing μ u w := by
    let : InnerProductSpace.Core ℂ SE := h.smoothL2SectionCore μ
    exact InnerProductSpace.Core.inner_sub_right (𝕜 := ℂ) u v w
  have pair_smul (u v : SE) (c : ℂ) :
      h.sectionPairing μ u (c • v) = c * h.sectionPairing μ u v := by
    let : InnerProductSpace.Core ℂ SE := h.smoothL2SectionCore μ
    exact InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) u v (r := c)
  -- Stage 2: realize a real scalar first jet, then compute its exact energy second difference.
  have exists_scalar_jet (x : M)
      (ξ : TangentSpace I x →L[ℝ] ℝ) :
      ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ φ ∧
        φ x = 0 ∧ mfderiv I 𝓘(ℝ, ℝ) φ x = ξ := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let b : SmoothBumpFunction I x := Classical.choice inferInstance
    let ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      ξ.comp (mfderiv I I c.symm (c x))
    let φ : M → ℝ := fun y ↦ b y * ℓ (c y - c x)
    have hc := contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (chart_mem_atlas _ x))
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ :=
      b.contMDiff_smul (ℓ.contMDiff.comp_contMDiffOn (hc.sub contMDiffOn_const))
    have heq : φ =ᶠ[𝓝 x] (fun y ↦ ℓ (c y - c x)) := by
      filter_upwards [b.eventuallyEq_one] with y hy
      simp [φ, hy]
    refine ⟨φ, hs, ?_, ?_⟩
    · simp [φ]
    · rw [heq.mfderiv_eq]
      have hchart := mdifferentiable_of_mem_atlas (I := I) (chart_mem_atlas _ x)
      have hcx := hchart.mdifferentiableAt (mem_chart_source _ x)
      change mfderiv I 𝓘(ℝ, ℝ) (ℓ ∘ (fun y ↦ c y - c x)) x = ξ
      erw [mfderiv_comp x (ℓ.contMDiff (n := ∞) |>.contMDiffAt.mdifferentiableAt (by simp))
        (hcx.sub (mdifferentiableAt_const (c := c x))), mfderiv_eq_fderiv, ℓ.fderiv,
        mfderiv_sub hcx (mdifferentiableAt_const (c := c x)), mfderiv_const, sub_zero]
      dsimp only [ℓ]
      change (ξ.comp (mfderiv I I c.symm (c x))).comp (mfderiv I I c x) = ξ
      erw [ContinuousLinearMap.comp_assoc, hchart.symm_comp_deriv (mem_chart_source _ x)]
      exact ContinuousLinearMap.comp_id ξ
  obtain ⟨φ, hφ, hφx, hφd⟩ := exists_scalar_jet x ξ
  let a : SE →ₗ[ℂ] SE := smoothSectionMul (n := n) (r := r) E (fun y ↦ (φ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hφ)
  let f (y : M) := g.inner y (mfderiv I 𝓘(ℝ, ℝ) φ y) (mfderiv I 𝓘(ℝ, ℝ) φ y)
  let b : SE →ₗ[ℂ] SE := smoothSectionMul (n := n) (r := r) E (fun y ↦ ((-2 : ℂ) * (f y : ℂ)))
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).comp_contMDiff (hscalarSmooth φ hφ))
  have move (u v : SE) : h.sectionPairing μ u (a v) = h.sectionPairing μ (a u) v := by
    apply integral_congr_ae
    filter_upwards [] with y
    change h.pairing y (u.val y) ((φ y : ℂ) • v.val y) =
      h.pairing y ((φ y : ℂ) • u.val y) (v.val y)
    let : InnerProductSpace.Core ℂ (E y) := h.toCore y
    have hr : h.pairing y (u.val y) ((φ y : ℂ) • v.val y) =
        (φ y : ℂ) * h.pairing y (u.val y) (v.val y) :=
      InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) (u.val y) (v.val y)
    have hl : h.pairing y ((φ y : ℂ) • u.val y) (v.val y) =
        conj (φ y : ℂ) * h.pairing y (u.val y) (v.val y) :=
      (h.toCore y).smul_left (u.val y) (v.val y) (φ y : ℂ)
    rw [hr, hl, Complex.conj_ofReal]
  have algebra (u v : SE) (x : M) :
      connectionEnergyDensity g h cov u (a (a v)) x -
          2 * connectionEnergyDensity g h cov (a u) (a v) x +
            connectionEnergyDensity g h cov (a (a u)) v x =
      (-2 : ℂ) * (f x : ℂ) * h.pairing x (u.val x) (v.val x) := by
    classical
    let a := smoothSectionMul (n := n) (r := r) E (fun y ↦ (φ y : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ)
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let H := EuclideanSpace ℝ (Fin n)
    let df : H →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) φ x
    let e (j : Fin n) : H := EuclideanSpace.single j 1
    let p (j : Fin n) : H →L[ℝ] ℝ := EuclideanSpace.proj j
    have hval (s : smoothSections (n := n) (r := r) E) :
        (a s).val x = φ x • s.val x := rfl
    have hleib (s : smoothSections (n := n) (r := r) E) (w : H) :
        cov (a s).val x w = φ x • cov s.val x w + df w • s.val x := by
      let t := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
      have ht : x ∈ t.baseSet := mem_baseSet_trivializationAt _ E x
      have hs : ContMDiffAt I (I.prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r))) ∞
          (fun y ↦ (⟨y, s.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x :=
        (t.contMDiffAt_section_iff ht).mpr
          ((s.property t inferInstance).contMDiffAt (t.open_baseSet.mem_nhds ht))
      have hmul : (a s).val = φ • s.val := rfl
      have hp := cov.isCovariantDerivativeOnUniv.leibniz
        (hs.mdifferentiableAt (by simp)) ((hφ x).mdifferentiableAt (by simp))
      rw [hmul, hp]
      rfl
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    have haddL (a b c : E x) :
        h.pairing x (a + b) c = h.pairing x a c + h.pairing x b c :=
      (h.toCore x).add_left a b c
    have haddR (a b c : E x) :
        h.pairing x a (b + c) = h.pairing x a b + h.pairing x a c :=
      InnerProductSpace.Core.inner_add_right a b c
    have hsmulL (c : ℝ) (a b : E x) :
        h.pairing x (c • a) b = (c : ℂ) * h.pairing x a b := by
      change (h.toCore x).inner ((c : ℂ) • a) b = _
      rw [InnerProductSpace.Core.inner_smul_left, Complex.conj_ofReal]
      rfl
    have hsmulR (c : ℝ) (a b : E x) :
        h.pairing x a (c • b) = (c : ℂ) * h.pairing x a b := by
      change (h.toCore x).inner a ((c : ℂ) • b) = _
      exact InnerProductSpace.Core.inner_smul_right a b
    -- The two real scalar Leibniz expansions cancel the lower-jet terms.
    have hpoint (i j : Fin n) :
        (g.inner x (p i) (p j) : ℂ) * h.pairing x (cov u.val x (e i))
            (cov (a (a v)).val x (e j)) -
          2 * ((g.inner x (p i) (p j) : ℂ) *
            h.pairing x (cov (a u).val x (e i)) (cov (a v).val x (e j))) +
          (g.inner x (p i) (p j) : ℂ) *
            h.pairing x (cov (a (a u)).val x (e i)) (cov v.val x (e j)) =
          (-2 : ℂ) * (g.inner x (p i) (p j) : ℂ) *
            (df (e i) : ℂ) * (df (e j) : ℂ) * h.pairing x (u.val x) (v.val x) := by
      simp only [hleib, hval, haddL, haddR, hsmulL, hsmulR]
      ring
    -- Reconstruct the original differential in the dual basis to recover g(df, df).
    have hsum (w : H) : ∑ j : Fin n, p j w • e j = w := by
      change (∑ j : Fin n, w j • EuclideanSpace.single j 1) = w
      simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr w
    have hdual : df = ∑ j : Fin n, df (e j) • p j := by
      apply ContinuousLinearMap.ext
      intro w
      simp only [sum_apply, smul_apply, smul_eq_mul]
      conv_lhs => rw [← hsum w]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    have hmetric : (g.inner x df df : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (p i) (p j) : ℂ) * (df (e i) : ℂ) * (df (e j) : ℂ) := by
      have hreplace := congrArg₂ (fun ξ η ↦ (g.inner x ξ η : ℂ)) hdual hdual
      rw [hreplace]
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul,
        Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [g.symm x (p j) (p i)]
      ring
    change connectionEnergyDensity g h cov u (a (a v)) x -
      2 * connectionEnergyDensity g h cov (a u) (a v) x +
        connectionEnergyDensity g h cov (a (a u)) v x = _
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
          (-2 : ℂ) * (g.inner x (p i) (p j) : ℂ) *
            (df (e i) : ℂ) * (df (e j) : ℂ) * h.pairing x (u.val x) (v.val x) := by
        unfold connectionEnergyDensity
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint i j
      _ = (-2 : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
          (g.inner x (p i) (p j) : ℂ) * (df (e i) : ℂ) * (df (e j) : ℂ)) *
            h.pairing x (u.val x) (v.val x) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [← hmetric]
  -- Stage 3: move the real multipliers across the original pairing and separate sections.
  have commutator (v : SE) : P.toLinearMap (a (a v)) -
      (2 : ℂ) • a (P.toLinearMap (a v)) + a (a (P.toLinearMap v)) = b v := by
    let w := P.toLinearMap (a (a v)) -
      (2 : ℂ) • a (P.toLinearMap (a v)) + a (a (P.toLinearMap v)) - b v
    have htest (u : SE) : h.sectionPairing μ u w = 0 := by
      dsimp only [w]
      rw [pair_sub, pair_add, pair_sub, pair_smul, move, move, move]
      rw [connectionLaplacian_pairing μ g h cov hcov hcomplex,
        connectionLaplacian_pairing μ g h cov hcov hcomplex,
        connectionLaplacian_pairing μ g h cov hcov hcomplex]
      have hint := integral_add
        ((henergy u (a (a v))).sub ((henergy (a u) (a v)).const_mul 2))
        (henergy (a (a u)) v)
      simp only [Pi.sub_apply] at hint
      rw [integral_sub (henergy u (a (a v)))
        ((henergy (a u) (a v)).const_mul 2), integral_const_mul] at hint
      rw [← hint]
      apply sub_eq_zero.mpr
      change (∫ y, _ ∂μ) = ∫ y, h.pairing y (u.val y) ((b v).val y) ∂μ
      apply integral_congr_ae
      filter_upwards [] with y
      rw [algebra]
      let : InnerProductSpace.Core ℂ (E y) := h.toCore y
      change (-2 : ℂ) * (f y : ℂ) * h.pairing y (u.val y) (v.val y) =
        h.pairing y (u.val y) (((-2 : ℂ) * (f y : ℂ)) • v.val y)
      exact (InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) (u.val y) (v.val y)).symm
    exact sub_eq_zero.mp ((h.sectionPairing_self_eq_zero_iff μ w).mp (htest w))
  -- Stage 4: realize any fiber value and evaluate the existing scalar-power symbol formula.
  have exists_sectionE (x : M) (v : E x) :
      ∃ (K : Set M), IsCompact K ∧
        ∃ s : supportedSmoothSections (n := n) (r := r) E K, s.val.val x = v := by
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds hx)
    let a : EuclideanSpace ℂ (Fin r) := (e.linearEquivAt ℂ x hx) v
    let s : ∀ y, E y := fun y ↦ (b y : ℂ) • e.symmL ℂ y a
    have hs : AtiyahSinger.IsSmoothSection (n := n) (r := r) E s := by
      intro f hf y hy
      let := hf
      by_cases hyb : y ∈ tsupport b
      · have hye : y ∈ e.baseSet := hb hyb
        have htransition :=
          (AtiyahSinger.IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f).contMDiffAt
            ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hye, hy⟩)
        have happly : ContDiff ℝ ∞
            (fun L : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) ↦ L a) :=
          (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
        have hcoord := happly.comp_contMDiffAt htransition
        have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
        have hmul : ContDiff ℝ ∞
            (fun p : ℂ × EuclideanSpace ℂ (Fin r) ↦ p.1 • p.2) := contDiff_smul
        have hlocal := hmul.comp_contMDiffAt (hscalar.contMDiffAt.prodMk_space hcoord)
        apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [e.open_baseSet.mem_nhds hye, f.open_baseSet.mem_nhds hy]
          with z hze hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) =
          (b z : ℂ) • e.coordChangeL ℂ f z a
        rw [map_smul, e.coordChangeL_apply f ⟨hze, hzf⟩, e.symmL_apply hze]
        rfl
      · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))
          |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [((isClosed_tsupport b).isOpen_compl.mem_nhds hyb),
          f.open_baseSet.mem_nhds hy] with z hzb hzf
        change (f.linearEquivAt ℂ z hzf) ((b z : ℂ) • e.symmL ℂ z a) = 0
        rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
    refine ⟨tsupport b, b.hasCompactSupport, ⟨⟨s, hs⟩, ?_⟩, ?_⟩
    · intro y hy
      change (b y : ℂ) • e.symmL ℂ y a = 0
      rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]
    · dsimp only [s]
      rw [b.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hx]
      exact e.symm_apply_apply_mk hx v
  -- The vanishing scalar jet removes the outer multipliers; both surviving factors are -2.
  apply LinearMap.ext
  intro v
  obtain ⟨K, hK, s, hs⟩ := exists_sectionE x v
  have hpow := P.apply_scalar_pow φ hφ x hφx s.val (a (a s.val)) (by
    intro y
    change (φ y : ℂ) • ((φ y : ℂ) • s.val.val y) = _
    rw [smul_smul, pow_two])
  have hcoeff : (-Complex.I) ^ 2 * (Nat.factorial 2 : ℂ) = -2 := by
    norm_num [pow_two]
  rw [hcoeff, hφd, hs] at hpow
  have hpoint := congrArg (fun w : SE ↦ w.val x) (commutator s.val)
  change (P.toLinearMap (a (a s.val))).val x -
    (2 : ℂ) • ((φ x : ℂ) • (P.toLinearMap (a s.val)).val x) +
      (φ x : ℂ) • ((φ x : ℂ) • (P.toLinearMap s.val).val x) =
        ((-2 : ℂ) * (f x : ℂ)) • s.val.val x at hpoint
  simp only [hφx, Complex.ofReal_zero, zero_smul, smul_zero, sub_zero, add_zero] at hpoint
  rw [hpow, hs] at hpoint
  have hnorm : (g.length x ξ : ℂ) ^ 2 = (f x : ℂ) := by
    rw [← Complex.ofReal_pow, g.length_sq]
    dsimp only [f]
    rw [hφd]
  change P.principalSymbol x ξ v = (g.length x ξ : ℂ) ^ 2 • v
  rw [hnorm]
  have heq := congrArg (fun z : E x ↦ (-2 : ℂ)⁻¹ • z) hpoint
  simpa only [smul_smul, ← mul_assoc,
    inv_mul_cancel₀ (show (-2 : ℂ) ≠ 0 by norm_num), one_mul, one_smul] using heq

/-- Positive definiteness of the supplied cotangent metric gives ellipticity. -/
theorem connectionLaplacian_isElliptic :
    (connectionLaplacian μ g h cov hcov hcomplex).IsElliptic := by
  /- At a nonzero covector the preceding symbol is a strictly positive
  scalar multiple of the identity. Its inverse is scalar multiplication
  by the reciprocal. This also covers a zero fiber; in base dimension zero
  there are no nonzero covectors, so the condition is vacuous. -/
  intro x ξ hξ
  rw [connectionLaplacian_principalSymbol μ g h cov hcov hcomplex]
  have hscalar : (g.length x ξ ^ 2 : ℂ) ≠ 0 :=
    pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (g.length_pos x ξ hξ)))
  exact (LinearEquiv.smulOfNeZero ℂ (E x) (g.length x ξ ^ 2 : ℂ) hscalar).bijective

end AtiyahSinger
