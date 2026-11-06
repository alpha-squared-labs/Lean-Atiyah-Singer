/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasClopenIndex
public import AtiyahSinger.Analysis.AtlasClopenQuantization
public import AtiyahSinger.Analysis.AtlasFullSymbolKClassRestriction
public import AtiyahSinger.Analysis.AtlasFullSymbolNativeIndex
public import AtiyahSinger.Analysis.AtlasPrincipalIndex
public import AtiyahSinger.Analysis.ComponentAnalyticIndex

import all AtiyahSinger.Analysis.AtlasPseudodifferentialFredholm

/-!
# Evaluation of the original variable-rank atlas full-symbol index

Public module ID: M2312.

The original all-order parametrix gives Fredholmness and the natural smooth/Sobolev
kernel and cokernel comparisons for arbitrary real-order elliptic atlas operators.
The existing handwritten smooth-lift predecessor from M0285 is reused for both
residuals. Principal quotient equality gives one lower-order compact perturbation
of the same dense smooth action, so the original smooth indices agree.

Restrict the prescribed complete symbol to the original clopen manifold components.
The original component quantizers assemble into the same diagonal section map from
M0234. M2311 evaluates each original constant-rank component; M2302 identifies its
genuine full-symbol compact-support K class with the original cotangent restriction.
This proves evaluation for the arbitrary original operator and its supplied full
representative, including cross-component smoothing terms and locally varying ranks.

Sources: SG III.4.6--4.7, III.5.2--5.3, III.7 and III.13 (13.1), (13.7)--(13.8).
SG means H. Blaine Lawson, Jr. and Marie-Louise Michelsohn, *Spin Geometry*
(Princeton University Press, 1989). The finite-atlas regularity and component
assembly are explicit project supplements. The general full-symbol native
evaluation uses the supplemental argument proved in M2310; the classical
representatives used in SG (13.5) are retained within that argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasPseudodifferentialOperator

variable {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
  (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)

/-- The parametrix argument gives Fredholmness for every critical real-order Sobolev extension.
This extends the differential-operator statement of SG III.5.2 using SG III.5.1. -/
theorem isFredholm_sobolevExtension_of_isElliptic (hP : P.IsElliptic) (s : ℝ) :
    (P.sobolevExtension L K s).IsFredholm := by
  -- The one return map below realizes the same parametrix at the original critical orders.
  obtain ⟨Q, hleft, hright⟩ := P.exists_parametrix_of_isElliptic hP
  have hreturn : ∃ S : K.SobolevSpace (s - m) →L[ℂ] L.SobolevSpace s,
      ∀ v : B.smoothSections,
        S (K.smoothToSobolev (s - m) v) = L.smoothToSobolev s (Q.toLinearMap v) := by
    have h := (Q.existsUnique_sobolevExtension K L (s - m)).exists
    rw [show (s - m) - (-m) = s by ring] at h
    exact h
  obtain ⟨S, hS⟩ := hreturn
  let T := P.sobolevExtension L K s
  -- Each actual residual factors through one higher order and the compact Sobolev inclusion.
  obtain ⟨R, hR⟩ := hleft L L s (s + 1)
  let J := L.sobolevInclusion (s + 1) s (by linarith)
  have hleft_eq : S.comp T - ContinuousLinearMap.id ℂ _ = J.comp R := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      (S.comp T - ContinuousLinearMap.id ℂ _).continuous (J.comp R).continuous
    funext u
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      P.sobolevExtension_smoothToSobolev, hS, hR, J,
      L.sobolevInclusion_smoothToSobolev, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  obtain ⟨R', hR'⟩ := hright K K (s - m) (s - m + 1)
  let J' := K.sobolevInclusion (s - m + 1) (s - m) (by linarith)
  have hright_eq : T.comp S - ContinuousLinearMap.id ℂ _ = J'.comp R' := by
    apply DFunLike.coe_injective
    apply (K.denseRange_smoothToSobolev (s - m)).equalizer
      (T.comp S - ContinuousLinearMap.id ℂ _).continuous (J'.comp R').continuous
    funext v
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      hS, P.sobolevExtension_smoothToSobolev, hR', J',
      K.sobolevInclusion_smoothToSobolev, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  apply (atkinson T).mpr
  refine ⟨S, ?_, ?_⟩
  · rw [hleft_eq]
    exact (L.isCompactOperator_sobolevInclusion (s + 1) s (by linarith)).comp_clm R
  · rw [hright_eq]
    exact (K.isCompactOperator_sobolevInclusion (s - m + 1) (s - m)
      (by linarith)).comp_clm R'

set_option maxHeartbeats 4000000 in
-- The natural kernel/cokernel maps elaborate nested dependent Sobolev instances.
set_option synthInstance.maxHeartbeats 100000 in
/-- The original dense smooth embeddings give the natural elliptic kernel/cokernel equivalences. -/
theorem exists_kernel_cokernel_sobolevEquiv_of_isElliptic
    (hP : P.IsElliptic) (s : ℝ) :
    ∃ e : P.toLinearMap.ker ≃ₗ[ℂ] (P.sobolevExtension L K s).ker,
      ∃ c : (B.smoothSections ⧸ P.toLinearMap.range) ≃ₗ[ℂ]
          (K.SobolevSpace (s - m) ⧸ (P.sobolevExtension L K s).range),
        (∀ u : P.toLinearMap.ker,
          (e u).val = L.smoothToSobolev s u.val) ∧
        ∀ v : B.smoothSections,
          c (P.toLinearMap.range.mkQ v) =
            (P.sobolevExtension L K s).range.mkQ (K.smoothToSobolev (s - m) v) := by
  classical
  obtain ⟨Q, hleft, hright⟩ := P.exists_parametrix_of_isElliptic hP
  let T := P.sobolevExtension L K s
  have hreturn : ∃ S : K.SobolevSpace (s - m) →L[ℂ] L.SobolevSpace s,
      ∀ v : B.smoothSections,
        S (K.smoothToSobolev (s - m) v) = L.smoothToSobolev s (Q.toLinearMap v) := by
    have h := (Q.existsUnique_sobolevExtension K L (s - m)).exists
    rw [show (s - m) - (-m) = s by ring] at h
    exact h
  obtain ⟨S, hS⟩ := hreturn
  obtain ⟨R, hR⟩ := hleft L L s s
  obtain ⟨R', hR'⟩ := hright K K (s - m) (s - m)
  -- Extend the two identities for these exact maps from the dense smooth sections.
  have hleft_eq : S.comp T - ContinuousLinearMap.id ℂ _ = R := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      (S.comp T - ContinuousLinearMap.id ℂ _).continuous R.continuous
    funext u
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      P.sobolevExtension_smoothToSobolev, hS, hR, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  have hright_eq : T.comp S - ContinuousLinearMap.id ℂ _ = R' := by
    apply DFunLike.coe_injective
    apply (K.denseRange_smoothToSobolev (s - m)).equalizer
      (T.comp S - ContinuousLinearMap.id ℂ _).continuous R'.continuous
    funext v
    simp only [Function.comp_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, T,
      hS, P.sobolevExtension_smoothToSobolev, hR', LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  -- The left residual gives a smooth preimage whenever the image is already smooth.
  have hlift (u : L.SobolevSpace s) (v : B.smoothSections)
      (hu : T u = K.smoothToSobolev (s - m) v) :
      ∃ w : A.smoothSections, L.smoothToSobolev s w = u ∧ P.toLinearMap w = v := by
    obtain ⟨z, hz⟩ := exists_smooth_lift_of_isAtlasSmoothingOperator L L
      (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) hleft s s R hR u
    let w := Q.toLinearMap v - z
    have hres : S (T u) - u = R u := DFunLike.congr_fun hleft_eq u
    rw [hu, hS] at hres
    have hw : L.smoothToSobolev s w = u := by
      change L.smoothToSobolev s (Q.toLinearMap v - z) = u
      rw [map_sub, hz]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hres).trans (add_comm _ _))
    refine ⟨w, hw, ?_⟩
    apply K.smoothToSobolev_injective (s - m)
    rw [← P.sobolevExtension_smoothToSobolev, hw]
    exact hu
  -- The forward kernel map is precisely the original smooth embedding.
  let e₀ : P.toLinearMap.ker →ₗ[ℂ] T.ker :=
    ((L.smoothToSobolev s).comp P.toLinearMap.ker.subtype).codRestrict _ (by
      intro u
      change T (L.smoothToSobolev s u.val) = 0
      rw [P.sobolevExtension_smoothToSobolev,
        show P.toLinearMap u.val = 0 from u.property, map_zero])
  have heinj : Function.Injective e₀ := by
    intro u v huv
    apply Subtype.ext
    apply L.smoothToSobolev_injective s
    exact congrArg Subtype.val huv
  have hesurj : Function.Surjective e₀ := by
    intro u
    obtain ⟨w, hw, hPw⟩ := hlift u.val 0 (by rw [map_zero]; exact u.property)
    exact ⟨⟨w, hPw⟩, Subtype.ext hw⟩
  -- Descend the specified target embedding to the actual algebraic ranges.
  have hrange : P.toLinearMap.range ≤ T.range.comap (K.smoothToSobolev (s - m)) := by
    rintro v ⟨u, rfl⟩
    exact ⟨L.smoothToSobolev s u, P.sobolevExtension_smoothToSobolev L K s u⟩
  let c₀ : (B.smoothSections ⧸ P.toLinearMap.range) →ₗ[ℂ]
      (K.SobolevSpace (s - m) ⧸ T.range) :=
    P.toLinearMap.range.mapQ T.range (K.smoothToSobolev (s - m)) hrange
  have hcinj : Function.Injective c₀ := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨v, rfl⟩ := P.toLinearMap.range.mkQ_surjective z
    change T.range.mkQ (K.smoothToSobolev (s - m) v) = 0 at hz
    obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero T.range).mp hz
    obtain ⟨w, _, hPw⟩ := hlift u v hu
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hPw⟩
  have hcsurj : Function.Surjective c₀ := by
    intro z
    obtain ⟨u, rfl⟩ := T.range.mkQ_surjective z
    -- The right residual represents each completed cokernel class by an actual smooth section.
    obtain ⟨w, hw⟩ := exists_smooth_lift_of_isAtlasSmoothingOperator K K
      (P.toLinearMap.comp Q.toLinearMap - LinearMap.id) hright
      (s - m) (s - m) R' hR' u
    refine ⟨P.toLinearMap.range.mkQ (-w), ?_⟩
    have hres : T (S u) - u = R' u := DFunLike.congr_fun hright_eq u
    have hzero : T.range.mkQ (T (S u)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨S u, rfl⟩
    change T.range.mkQ (K.smoothToSobolev (s - m) (-w)) = T.range.mkQ u
    rw [map_neg, hw, ← hres, map_neg, map_sub, hzero, zero_sub, neg_neg]
  refine ⟨LinearEquiv.ofBijective e₀ ⟨heinj, hesurj⟩,
    LinearEquiv.ofBijective c₀ ⟨hcinj, hcsurj⟩, ?_, ?_⟩
  · intro u
    rfl
  · intro v
    rfl

/-- The same original smooth kernel and cokernel are finite and compute every Sobolev index. -/
theorem index_sobolevExtension_of_isElliptic (hP : P.IsElliptic) (s : ℝ) :
    FiniteDimensional ℂ P.toLinearMap.ker ∧
      FiniteDimensional ℂ (B.smoothSections ⧸ P.toLinearMap.range) ∧
      (P.sobolevExtension L K s).index = P.toLinearMap.index := by
  -- Finiteness is established in the completed spaces and transported by the natural maps.
  have hFred := P.isFredholm_sobolevExtension_of_isElliptic L K hP s
  obtain ⟨e, c, _, _⟩ :=
    P.exists_kernel_cokernel_sobolevEquiv_of_isElliptic L K hP s
  let : FiniteDimensional ℂ (P.sobolevExtension L K s).ker := hFred.finite_ker
  let : FiniteDimensional ℂ
      (K.SobolevSpace (s - m) ⧸ (P.sobolevExtension L K s).range) := hFred.finite_coker
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective,
    FiniteDimensional.of_injective c.toLinearMap c.injective, ?_⟩
  -- Both dimensions refer to the same smooth and Sobolev actions fixed above.
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    ← e.finrank_eq, ← c.finrank_eq]

/-- A common full elliptic principal class preserves the original smooth index. -/
theorem index_eq_of_principalSymbol_eq_of_isElliptic
    (P Q : AtlasPseudodifferentialOperator A B m) (hP : P.IsElliptic)
    (hPQ : P.principalSymbol = Q.principalSymbol) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  classical
  let L := (nonempty_atlasBundlePresentation A).some
  let K := (nonempty_atlasBundlePresentation B).some
  have hQ : Q.IsElliptic := by
    obtain ⟨a, hPa, ha⟩ := hP
    exact ⟨a, hPQ.symm.trans hPa, ha⟩
  let R : AtlasPseudodifferentialOperator A B (m - 1) :=
    ⟨Q.toLinearMap - P.toLinearMap,
      Q.isAtlasPseudodifferentialOperator_sub_of_principalSymbol_eq P hPQ.symm⟩
  let T := P.sobolevExtension L K 0
  let S := Q.sobolevExtension L K 0
  let V := R.sobolevExtension L K 0
  have hord : 0 - m < 0 - (m - 1) := by linarith
  let J := K.sobolevInclusion (0 - (m - 1)) (0 - m) hord.le
  -- Density identifies the actual perturbation, not merely its principal class.
  have hsum : T + J.comp V = S := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev 0).equalizer
      (T + J.comp V).continuous S.continuous
    funext u
    simp only [Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
      T, S, V, J, sobolevExtension_smoothToSobolev,
      K.sobolevInclusion_smoothToSobolev, R, LinearMap.sub_apply, map_sub]
    abel
  have hcompact : IsCompactOperator (J.comp V) :=
    (K.isCompactOperator_sobolevInclusion (0 - (m - 1)) (0 - m) hord).comp_clm V
  have hindex := index_add_compact T (J.comp V)
    (P.isFredholm_sobolevExtension_of_isElliptic L K hP 0) hcompact
  rw [hsum] at hindex
  have hPT := (P.index_sobolevExtension_of_isElliptic L K hP 0).2.2
  have hQS := (Q.index_sobolevExtension_of_isElliptic L K hQ 0).2.2
  exact hPT.symm.trans (hindex.symm.trans hQS)

end AtlasPseudodifferentialOperator

variable [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isSmoothPositiveMeasure_comap_opens

namespace AtlasPseudodifferentialOperator

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxSynthPendingDepth 40 in
/-- The original component analytic index evaluates the given arbitrary atlas full symbol. -/
theorem analyticIndexOfComponents_atlasFullSymbolKClass
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (a : atlasGlobalSymbolSpace A B m) (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a) :
    analyticIndexOfComponents μ (atlasFullSymbolKClass A B a ha) = P.toLinearMap.index := by
  /- Quantize the exact full-symbol restrictions on the original clopen components.
  Their exact diagonal section map has the same principal class as the arbitrary
  original P. Lower-order compact perturbation therefore keeps its smooth index.
  Evaluate each actual block through the same compatible native witnesses and
  identify its K class with the proper pullback of the original full-symbol triple. -/
  classical
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let := Fintype.ofFinite (ConnectedComponents M)
  let U := manifoldComponent (n := n) (M := M)
  have hclosed (c : ConnectedComponents M) : IsClosed (U c : Set M) :=
    isClosed_singleton.preimage ConnectedComponents.continuous_coe
  have hdisjoint : Pairwise (fun c d ↦ Disjoint (U c : Set M) (U d : Set M)) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro x hc hd
    exact hcd (hc.symm.trans hd)
  have hcover : (⋃ c, (U c : Set M)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨ConnectedComponents.mk x, rfl⟩
  let q (c : ConnectedComponents M) :
      atlasGlobalSymbolSpace (A.restrictOpen (U c)) (B.restrictOpen (U c)) m :=
    ⟨fun x ξ ↦ a.val x.val ξ, a.property.restrictOpen A B (U c)⟩
  let haU (c : ConnectedComponents M) :
      IsEllipticFullAtlasSymbol (A.restrictOpen (U c)) (B.restrictOpen (U c)) m (q c).val :=
    ha.restrictOpen A B (U c)
  let R (c : ConnectedComponents M) :=
    (nonempty_atlasQuantizationPresentation (A.restrictOpen (U c)) (B.restrictOpen (U c))).some
  let PU (c : ConnectedComponents M) := (R c).quantize (q c)
  have hpU (c : ConnectedComponents M) : (PU c).principalSymbol =
      atlasGlobalPrincipalSymbolClass (A.restrictOpen (U c)) (B.restrictOpen (U c)) m (q c) :=
    (R c).principalSymbol_quantize (q c)
  have hiU (c : ConnectedComponents M) : (PU c).IsElliptic := ⟨q c, hpU c, haU c⟩
  -- The actual component defects are finite by the original parametrix and dense embeddings.
  have hfinite (c : ConnectedComponents M) :
      FiniteDimensional ℂ (PU c).toLinearMap.ker ∧
      FiniteDimensional ℂ
        ((B.restrictOpen (U c)).smoothSections ⧸ (PU c).toLinearMap.range) := by
    let L := (nonempty_atlasBundlePresentation (A.restrictOpen (U c))).some
    let K := (nonempty_atlasBundlePresentation (B.restrictOpen (U c))).some
    have h := (PU c).index_sobolevExtension_of_isElliptic L K (hiU c) 0
    exact ⟨h.1, h.2.1⟩
  let : ∀ c, FiniteDimensional ℂ (PU c).toLinearMap.ker := fun c ↦ (hfinite c).1
  let : ∀ c, FiniteDimensional ℂ
      ((B.restrictOpen (U c)).smoothSections ⧸ (PU c).toLinearMap.range) :=
    fun c ↦ (hfinite c).2
  obtain ⟨C, hC⟩ := exists_atlasClopenQuantization A B U hclosed hdisjoint hcover R
  have hsum : (C.quantize a).toLinearMap.index = ∑ c, (PU c).toLinearMap.index := by
    change (C.toLinearMap a).index = _
    rw [hC m a]
    exact index_atlasClopenBlockSum A B U hclosed hdisjoint hcover
      (fun c ↦ (PU c).toLinearMap)
  have hiP : P.IsElliptic := ⟨a, hP, ha⟩
  have hindex : P.toLinearMap.index = (C.quantize a).toLinearMap.index :=
    P.index_eq_of_principalSymbol_eq_of_isElliptic (C.quantize a) hiP
      (hP.trans (C.principalSymbol_quantize a).symm)
  -- Locally constant ranks become constant on each of these very original components.
  have heval (c : ConnectedComponents M) :
      analyticIndex (μ.comap (Subtype.val : U c → M))
        (atlasFullSymbolKClass (A.restrictOpen (U c)) (B.restrictOpen (U c))
          (q c) (haU c)) = (PU c).toLinearMap.index := by
    let := (A.restrictOpen (U c)).isFiniteRank
    let := (B.restrictOpen (U c)).isFiniteRank
    let x₀ : U c := Classical.choice inferInstance
    have hr (x : U c) : Module.finrank ℂ (E x.val) = Module.finrank ℂ (E x₀.val) :=
      IsLocallyConstant.apply_eq_of_preconnectedSpace (X := U c)
        (ComplexBundle.isLocallyConstant_finrank (ComplexBundle.Restrict E (U c))) x x₀
    have hq (x : U c) : Module.finrank ℂ (F x.val) = Module.finrank ℂ (F x₀.val) :=
      IsLocallyConstant.apply_eq_of_preconnectedSpace (X := U c)
        (ComplexBundle.isLocallyConstant_finrank (ComplexBundle.Restrict F (U c))) x x₀
    have h := (PU c).analyticIndexOfComponents_fullSymbolKClass_of_constant_rank
      (μ.comap (Subtype.val : U c → M)) _ _ hr hq (q c) (haU c) (hpU c)
    rw [analyticIndexOfComponents_eq_analyticIndex] at h
    exact h
  rw [hindex, hsum]
  unfold analyticIndexOfComponents
  rw [AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro c _
  change analyticIndex (μ.comap (Subtype.val : U c → M))
    (cotangentKZeroComponents (atlasFullSymbolKClass A B a ha) c) = _
  have hK := atlasFullSymbolKClass_restrictOpen A B (U c) (hclosed c) a ha
  rw [show cotangentKZeroComponents (atlasFullSymbolKClass A B a ha) c =
    atlasFullSymbolKClass (A.restrictOpen (U c)) (B.restrictOpen (U c))
      (q c) (haU c) from hK.symm]
  exact heval c

/-- The same full-symbol class evaluates every original real-order Sobolev realization. -/
theorem analyticIndexOfComponents_atlasFullSymbolKClass_sobolevExtension
    {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (a : atlasGlobalSymbolSpace A B m) (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s : ℝ) :
    analyticIndexOfComponents μ (atlasFullSymbolKClass A B a ha) =
      (P.sobolevExtension L K s).index := by
  -- The exact natural comparison concerns this same P and these same completed orders.
  have hiP : P.IsElliptic := ⟨a, hP, ha⟩
  exact (P.analyticIndexOfComponents_atlasFullSymbolKClass μ a ha hP).trans
    (P.index_sobolevExtension_of_isElliptic L K hiP s).2.2.symm

end AtlasPseudodifferentialOperator

end AtiyahSinger
