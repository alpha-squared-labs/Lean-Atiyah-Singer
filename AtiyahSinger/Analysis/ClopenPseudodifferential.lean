/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass
public import AtiyahSinger.Analysis.ClopenLocalization
public import AtiyahSinger.Analysis.OpenGlobalPrincipalSymbol
public import AtiyahSinger.Analysis.OpenHomogeneousComparison
public import AtiyahSinger.Analysis.OpenHomogeneousSymbol
public import AtiyahSinger.Geometry.OpenDensity

/-!
# Restriction of pseudodifferential operators to a clopen submanifold

Public module ID: M0332.

The native pullback bundles retain their original fibers, norms and atlases.
Open transport preserves the original covector and realizes the restriction of
the specified operator after genuine zero extension of its input section.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Restriction keeps the native pullback topology and every original fiber norm. -/
@[reducible]
def SmoothFiniteComplexBundle.restrictOpen (E : SmoothFiniteComplexBundle (n := n) M)
    (U : Opens M) : SmoothFiniteComplexBundle (n := n) U where
  rank := E.rank
  Fiber := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber
  isSmooth := isSmoothComplexBundle_pullback (M := M) (N := U) E.Fiber
    (ContinuousMap.subtypeVal (U : Set M)) contMDiff_subtype_val

/-- The native open restriction carries the smoothness certificate of the original bundle. -/
instance SmoothFiniteComplexBundle.restrictOpenIsSmooth
    (E : SmoothFiniteComplexBundle (n := n) M) (U : Opens M) :
    IsSmoothComplexBundle (M := U) (n := n) (r := E.rank) (E.restrictOpen U).Fiber :=
  (E.restrictOpen U).isSmooth

private def openTopDiffeomorph (U : Opens M) :
    U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ (⊤ : Opens U) where
  toFun x := ⟨x, Set.mem_univ x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

set_option backward.isDefEq.respectTransparency false in
private theorem isSmoothBundleMap_restrictOpen_identification
    (E : SmoothFiniteComplexBundle (n := n) M) (U : Opens M) :
    IsSmoothBundleMap (M := U) (n := n) (r := E.rank) (q := E.rank)
      (E := (ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber)
      (F := ((⟨openTopDiffeomorph (n := n) U, (openTopDiffeomorph (n := n) U).continuous⟩ :
        C(U, (⊤ : Opens U))) : U → (⊤ : Opens U)) *ᵖ
          ((ContinuousMap.subtypeVal ((⊤ : Opens U) : Set U) : (⊤ : Opens U) → U) *ᵖ
            (E.restrictOpen U).Fiber))
      (fun x ↦ (LinearEquiv.refl ℂ (E.Fiber x.val)).toLinearMap) := by
  -- Every native frame in the iterated pullback descends to an original E-frame.
  rintro _ ⟨e, he, rfl⟩ _ ⟨_, ⟨_, ⟨f, hf, rfl⟩, rfl⟩, rfl⟩ j
  let := he
  let := hf
  have h := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin E.rank))
    (EuclideanSpace.single j 1)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
      (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f)
  apply (h.comp (contMDiff_subtype_val (U := U)).contMDiffOn (fun _ hx ↦ hx)).congr
  intro x hx
  rw [(e.pullback (ContinuousMap.subtypeVal (U : Set M))).symmL_apply hx.1,
    (e.pullback (ContinuousMap.subtypeVal (U : Set M))).symm_apply hx.1]
  change (f ⟨x.val, e.symm x.val (EuclideanSpace.single j 1)⟩).2 =
    e.coordChangeL ℂ f x.val (EuclideanSpace.single j 1)
  rw [e.coordChangeL_apply f hx]

private theorem mfderiv_openTopDiffeomorph (U : Opens M) (x : U) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (openTopDiffeomorph (n := n) U) x =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let e := openTopDiffeomorph (n := n) U
  have h := mfderiv_comp x
    ((contMDiff_subtype_val (U := (⊤ : Opens U)) (n := ∞)).mdifferentiable (by simp) (e x))
    (e.mdifferentiable (by simp) x)
  rw [show (Subtype.val : (⊤ : Opens U) → U) ∘ e = id from rfl,
    mfderiv_id, mfderiv_openSubtypeVal] at h
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L ↦ L v) h.symm

variable [T2Space M]

set_option backward.isDefEq.respectTransparency false in
/-- Native restriction of a full symbol to a compact open submanifold keeps its order. -/
theorem isGlobalSymbol_restrictOpen (E F : SmoothFiniteComplexBundle (n := n) M)
    (U : Opens M) [CompactSpace U] {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m) :
    IsGlobalSymbol (M := U) (n := n) (r := E.rank) (q := F.rank)
      (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber m (fun x ξ ↦ p.val x.val ξ) := by
  let e := openTopDiffeomorph (n := n) U
  let α (x : U) := LinearEquiv.refl ℂ (E.Fiber x.val)
  let β (x : U) := LinearEquiv.refl ℂ (F.Fiber x.val)
  -- Full source control is permissible here: only its intersection with U is transported.
  obtain ⟨p', hp', _⟩ := exists_supported_openGlobalSymbol
    E F (E.restrictOpen U) (F.restrictOpen U) U ⊤ e univ univ isCompact_univ
    subset_rfl (by ext x; simp) α (isSmoothBundleMap_restrictOpen_identification E U)
    β (isSmoothBundleMap_restrictOpen_identification F U) p
    (fun _ hx ↦ False.elim (hx (mem_univ _)))
  have heq : p'.val = fun (x : U) ξ ↦ p.val x.val ξ := by
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    have h := hp' x ξ v
    change p'.val x ξ v = p.val x.val (ξ.comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (openTopDiffeomorph (n := n) U) x)) v at h
    rw [mfderiv_openTopDiffeomorph] at h
    have hc : ξ.comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) = ξ := by
      ext w
      rfl
    exact hc ▸ h
  exact heq ▸ p'.property

set_option backward.isDefEq.respectTransparency false in
/-- Elliptic homogeneous data restrict with their exact original fiber and covector action. -/
theorem exists_homogeneousSymbol_restrictOpen
    (E F : SmoothFiniteComplexBundle (n := n) M) (U : Opens M) [CompactSpace U]
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0) (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val) :
    ∃ aU : homogeneousGlobalSymbolSpace (M := U) (n := n) (r := E.rank) (q := F.rank)
        (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0,
      IsEllipticGlobalSymbol (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber aU.val ∧
      ∀ x ξ, aU.val x ξ = a.val x.val ξ := by
  let e := openTopDiffeomorph (n := n) U
  let α (x : U) := LinearEquiv.refl ℂ (E.Fiber x.val)
  let β (x : U) := LinearEquiv.refl ℂ (F.Fiber x.val)
  have hzero : IsSmoothBundleMap (M := U) (n := n) (r := E.rank) (q := F.rank)
      (E := (E.restrictOpen U).Fiber) (F := (F.restrictOpen U).Fiber)
      (fun _ ↦ 0) := by
    intro f hf g hg j
    let := hf
    let := hg
    apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin F.rank)))).congr
    intro x hx
    change (g ⟨x, (0 : (F.restrictOpen U).Fiber x)⟩).2 = 0
    exact (congrFun (g.coe_linearMapAt_of_mem (R := ℂ) hx.2) 0).symm.trans
      (g.linearMapAt ℂ x).map_zero
  -- Source and target exterior conditions are empty for the full control sets.
  obtain ⟨aU, hiU, haction, _⟩ := exists_openHomogeneousSymbol
    E F (E.restrictOpen U) (F.restrictOpen U) U ⊤ e univ univ isCompact_univ
    subset_rfl (by ext x; simp) α (isSmoothBundleMap_restrictOpen_identification E U)
    β (isSmoothBundleMap_restrictOpen_identification F U) a ha (fun _ ↦ 0)
    (fun _ hx ↦ False.elim (hx (mem_univ _))) (fun _ ↦ 0) hzero
    (fun _ _ ↦ rfl) (fun _ hx ↦ False.elim (hx (mem_univ _)))
  refine ⟨aU, hiU, ?_⟩
  intro x ξ
  apply ContinuousLinearMap.ext
  intro v
  have h := haction x ξ v
  change aU.val x (ξ.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Subtype.val : (⊤ : Opens U) → U) (e x))) v =
      a.val x.val ξ v at h
  rw [mfderiv_openSubtypeVal] at h
  have hc : ξ.comp (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) = ξ := by
    ext w
    rfl
  exact hc ▸ h

variable [CompactSpace M] [SecondCountableTopology M]

omit [CompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The extended limit accommodates the original zero extensions, clopen blocks and homogeneous
-- representatives.
/-- The principal class of native restriction agrees with regularizing the same restricted data. -/
theorem globalPrincipalSymbolClass_restrictOpen_regularized
    (E F : SmoothFiniteComplexBundle (n := n) M) (U : Opens M) [CompactSpace U]
    (R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (RU : QuantizationPresentation (M := U) (n := n) (r := E.rank) (q := F.rank)
      (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0) (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (aU : homogeneousGlobalSymbolSpace (M := U) (n := n) (r := E.rank) (q := F.rank)
      (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0)
    (haU : ∀ x ξ, aU.val x ξ = a.val x.val ξ) :
    globalPrincipalSymbolClass (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0
      ⟨fun x ξ ↦ R.regularizedSymbolFunction a.val x.val ξ,
        isGlobalSymbol_restrictOpen E F U (R.regularizedSymbol 0 a.val a.property.1
          a.property.2)⟩ =
    globalPrincipalSymbolClass (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0
      (RU.regularizedSymbol 0 aU.val aU.property.1 aU.property.2) := by
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
  obtain ⟨ℓ⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  let q : GlobalSymbolFunction (n := n) E.Fiber F.Fiber := fun x ξ ↦
    (highFrequencyCutoff 1 (EuclideanSpace.single (0 : Fin 1) (ℓ.length x ξ)) : ℂ) • a.val x ξ
  have hprops := nativeAtlasSymbolFunction_homogeneous_properties
    (n := n) (r := E.rank) (q := F.rank)
    0 a.val a.property.1 a.property.2 ha
  have hq : IsGlobalSymbol (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 q := by
    apply (isAtlasGlobalSymbol_native_iff (n := n) (r := E.rank) (q := F.rank) 0 q).mp
    exact isAtlasGlobalSymbol_atlasRegularizedSymbolFunction A B ℓ 0
      (nativeAtlasSymbolFunction a.val) hprops.1 hprops.2.1
  let pAtlas := atlasRegularizedSymbol A B ℓ 0 (nativeAtlasSymbolFunction a.val)
    hprops.1 hprops.2.1
  let rAtlas := nativeAtlasGlobalSymbol 0 (R.regularizedSymbol 0 a.val a.property.1 a.property.2)
  have hcompare : atlasGlobalPrincipalSymbolClass A B 0 pAtlas =
      atlasGlobalPrincipalSymbolClass A B 0 rAtlas :=
    atlasRegularizedSymbol_principalClass_native ℓ R 0 a.val a.property.1 a.property.2 ha
  have hdAtlas := (atlasGlobalPrincipalSymbolClass_eq_iff A B 0 pAtlas rAtlas).mp hcompare
  have hd : IsGlobalSymbol (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber (0 - 1)
      (q - R.regularizedSymbolFunction a.val) := by
    exact (isAtlasGlobalSymbol_native_iff (n := n) (r := E.rank) (q := F.rank)
      (0 - 1) (q - R.regularizedSymbolFunction a.val)).mp hdAtlas
  -- Restrict the actual lower-order difference between radial and presentation cutoffs.
  let qU : globalSymbolSpace (M := U) (n := n) (r := E.rank) (q := F.rank)
      (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0 :=
    ⟨fun x ξ ↦ q x.val ξ, isGlobalSymbol_restrictOpen E F U ⟨q, hq⟩⟩
  have hclasses : globalPrincipalSymbolClass (E.restrictOpen U).Fiber
      (F.restrictOpen U).Fiber 0 qU =
      globalPrincipalSymbolClass (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0
        ⟨fun x ξ ↦ R.regularizedSymbolFunction a.val x.val ξ,
          isGlobalSymbol_restrictOpen E F U
            (R.regularizedSymbol 0 a.val a.property.1 a.property.2)⟩ := by
    apply (globalPrincipalSymbolClass_eq_iff _ _ 0 _ _).mpr
    exact isGlobalSymbol_restrictOpen E F U ⟨q - R.regularizedSymbolFunction a.val, hd⟩
  let e := openTopDiffeomorph (n := n) U
  let α (x : U) := LinearEquiv.refl ℂ (E.Fiber x.val)
  let β (x : U) := LinearEquiv.refl ℂ (F.Fiber x.val)
  -- The metric radial cutoff has exact high-frequency agreement on the original covector.
  have hhigh : ∀ x ξ, 1 ≤ ℓ.length x ξ → q x ξ = a.val x ξ := by
    intro x ξ hξ
    have h := (atlasRegularizedSymbolFunction_cutoff ℓ (nativeAtlasSymbolFunction a.val)).2
      x ξ hξ
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L ↦ L v) h
  have hqaction : ∀ (x : U) η (v : E.Fiber x.val), qU.val (e x).val η (α x v) =
      β x (q x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v) := by
    intro x η v
    rw [mfderiv_openTopDiffeomorph]
    rfl
  have haaction : ∀ (x : U) η (v : E.Fiber x.val), aU.val (e x).val η (α x v) =
      β x (a.val x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v) := by
    intro x η v
    rw [mfderiv_openTopDiffeomorph]
    exact congrArg (fun L ↦ L v) (haU x η)
  exact hclasses.symm.trans (globalPrincipalSymbolClass_openTransport_eq_regularizedSymbol
    E F (E.restrictOpen U) (F.restrictOpen U) U ⊤ e α
    (isSmoothBundleMap_restrictOpen_identification E U) β
    (isSmoothBundleMap_restrictOpen_identification F U) univ isCompact_univ subset_rfl ℓ
    q a.val hhigh qU aU hqaction haaction (fun _ hx ↦ False.elim (hx (mem_univ _))) RU)

variable [MeasurableSpace M] [BorelSpace M]

attribute [local instance] isSmoothPositiveMeasure_comap_opens

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
-- The extended limit accommodates the original zero extensions, clopen blocks and homogeneous
-- representatives.
/-- A clopen diagonal block uses actual zero extension and the original homogeneous symbol. -/
theorem PseudodifferentialOperator.exists_clopen_restriction
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (E F : SmoothFiniteComplexBundle (n := n) M)
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ 0)
    (R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (R.regularizedSymbol 0 a.val a.property.1 a.property.2)) (hi : P.IsElliptic)
    (U : Opens M) (hclosed : IsClosed (U : Set M)) [CompactSpace U] :
    ∃ PU : PseudodifferentialOperator (M := U) (n := n) (r := E.rank) (q := F.rank)
        (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber
        (μ.comap (Subtype.val : U → M)) 0,
      ∃ RU : QuantizationPresentation (M := U) (n := n) (r := E.rank) (q := F.rank)
          (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber,
        ∃ aU : homogeneousGlobalSymbolSpace (M := U) (n := n) (r := E.rank) (q := F.rank)
            (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0,
          PU.principalSymbol = globalPrincipalSymbolClass
            (E.restrictOpen U).Fiber (F.restrictOpen U).Fiber 0
              (RU.regularizedSymbol 0 aU.val aU.property.1 aU.property.2) ∧
          PU.IsElliptic ∧
          (∀ x ξ, aU.val x ξ = a.val x.val ξ) ∧
          ∀ (u : smoothSections (M := U) (n := n) (r := E.rank) (E.restrictOpen U).Fiber)
            (x : U), (PU.toLinearMap u).val x =
              (P.toLinearMap (smoothSectionZeroExtension E.Fiber U (U : Set M)
                hclosed subset_rfl ⟨u, fun y hy ↦ False.elim (hy y.property)⟩)).val x.val := by
  classical
  let EU := E.restrictOpen U
  let FU := F.restrictOpen U
  let e := openTopDiffeomorph (n := n) U
  let α (x : U) := LinearEquiv.refl ℂ (E.Fiber x.val)
  let β (x : U) := LinearEquiv.refl ℂ (F.Fiber x.val)
  let ν := μ.comap (Subtype.val : U → M)
  let Z (v : smoothSections (M := U) (n := n) (r := E.rank) EU.Fiber) :
      smoothSections (n := n) (r := E.rank) E.Fiber :=
    smoothSectionZeroExtension E.Fiber U (U : Set M) hclosed subset_rfl
      ⟨v, fun y hy ↦ False.elim (hy y.property)⟩
  have hZ (v : smoothSections (M := U) (n := n) (r := E.rank) EU.Fiber) (x : M) :
      (Z v).val x = if hx : x ∈ U then v.val ⟨x, hx⟩ else 0 := rfl
  have hZrestrict (v : smoothSections (M := U) (n := n) (r := E.rank) EU.Fiber) :
      Z (smoothSectionRestriction E.Fiber U (Z v)) = Z v := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ U
    · simp only [hZ, hx, ↓reduceDIte]
      change (Z v).val x = v.val ⟨x, hx⟩
      rw [hZ, dite_eq_left hx]
    · simp only [hZ, hx, ↓reduceDIte]
  -- The genuine characteristic projections localize the supplied operator on both sides.
  obtain ⟨Q, c, hQc, hc, hQaction⟩ := P.exists_clopen_localization μ E F R a hp U hclosed
  have hQs : HasSectionOperatorSupport (U : Set M) Q.toLinearMap := by
    constructor
    · intro u
      apply closure_minimal ?_ hclosed
      intro x hx
      by_contra hnot
      exact hx ((hQaction u x).trans (ite_eq_right hnot))
    · intro u hu
      have hzero : Z (smoothSectionRestriction E.Fiber U u) = 0 := by
        apply Subtype.ext
        funext x
        rw [hZ]
        split_ifs with hx
        · change u.val x = 0
          by_contra hne
          exact Set.disjoint_left.mp hu (subset_closure hne) hx
        · rfl
      apply Subtype.ext
      funext x
      change (Q.toLinearMap u).val x = 0
      rw [hQaction]
      change (if x ∈ U then (P.toLinearMap (Z (smoothSectionRestriction E.Fiber U u))).val x
        else 0) = 0
      rw [hzero, map_zero]
      split_ifs <;> rfl
  -- Exact open transport provides one operator for both the section action and symbol witnesses.
  obtain ⟨PU, ⟨hPUs, hPUgerm⟩, _⟩ := Q.existsUnique_openExtension E F EU FU U ⊤ e
    (U : Set M) univ hclosed.isCompact isCompact_univ subset_rfl subset_rfl
    (by ext x; simp) α (isSmoothBundleMap_restrictOpen_identification E U)
    β (isSmoothBundleMap_restrictOpen_identification F U) ν μ hQs
  have hPUaction (v : smoothSections (M := U) (n := n) (r := E.rank) EU.Fiber) (x : U) :
      (PU.toLinearMap v).val x = (P.toLinearMap (Z v)).val x.val := by
    have hmatch : ∀ᶠ y : U in 𝓝ˢ ((Subtype.val : U → M) ⁻¹' (U : Set M)),
        v.val (e y).val = α y ((Z v).val y.val) := by
      filter_upwards with y
      change v.val y = (Z v).val y.val
      rw [hZ, dite_eq_left y.property]
    have h := hPUgerm (Z v) v hmatch x
    change (PU.toLinearMap v).val x = (Q.toLinearMap (Z v)).val x.val at h
    rw [hQaction, ite_eq_left x.property] at h
    change (PU.toLinearMap v).val x =
      (P.toLinearMap (Z (smoothSectionRestriction E.Fiber U (Z v)))).val x.val at h
    exact h.trans (congrArg (fun w ↦ (P.toLinearMap w).val x.val) (hZrestrict v))
  obtain ⟨p, pU, _, _, _, _, hQp, hPUp, hptransport, _⟩ :=
    exists_principalSymbols_openExtension E F EU FU U ⊤ e (U : Set M) univ
      hclosed.isCompact subset_rfl subset_rfl (by ext x; simp)
      α (isSmoothBundleMap_restrictOpen_identification E U)
      β (isSmoothBundleMap_restrictOpen_identification F U) ν μ Q hQs PU hPUs hPUgerm
  have hpU (x : U) ξ : pU.val x ξ = p.val x.val ξ := by
    apply ContinuousLinearMap.ext
    intro v
    have h := hptransport x ξ v
    change pU.val x ξ v = p.val x.val (ξ.comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (openTopDiffeomorph (n := n) U) x)) v at h
    rw [mfderiv_openTopDiffeomorph] at h
    exact h
  have hcU (x : U) ξ : c.val x.val ξ = a.val x.val ξ := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [x.property, ↓reduceIte] using hc x.val ξ v
  have hreg (x : U) ξ : R.regularizedSymbolFunction c.val x.val ξ =
      R.regularizedSymbolFunction a.val x.val ξ := by
    simp only [QuantizationPresentation.regularizedSymbolFunction, hcU]
  have hd : IsGlobalSymbol (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber (0 - 1)
      (p.val - R.regularizedSymbolFunction c.val) :=
    (globalPrincipalSymbolClass_eq_iff E.Fiber F.Fiber 0 p
      (R.regularizedSymbol 0 c.val c.property.1 c.property.2)).mp (hQp.symm.trans hQc)
  have hdU := isGlobalSymbol_restrictOpen E F U ⟨p.val - R.regularizedSymbolFunction c.val, hd⟩
  let rU : globalSymbolSpace (M := U) (n := n) (r := E.rank) (q := F.rank)
      EU.Fiber FU.Fiber 0 :=
    ⟨fun x ξ ↦ R.regularizedSymbolFunction a.val x.val ξ,
      isGlobalSymbol_restrictOpen E F U (R.regularizedSymbol 0 a.val a.property.1 a.property.2)⟩
  have hdiff : (fun (x : U) (ξ : CotangentFiber (n := n) x) ↦
      (p.val - R.regularizedSymbolFunction c.val) x.val ξ :
        GlobalSymbolFunction (M := U) (n := n) EU.Fiber FU.Fiber) = pU.val - rU.val := by
    funext x ξ
    simp only [Pi.sub_apply, rU, hpU, hreg]
  rw [hdiff] at hdU
  -- The restricted homogeneous symbol belongs to this same principal class and is elliptic.
  have ha := (P.isElliptic_iff_homogeneous R a hp).mp hi
  obtain ⟨aU, haUi, haU⟩ := exists_homogeneousSymbol_restrictOpen E F U a ha
  obtain ⟨RU⟩ := nonempty_quantizationPresentation (M := U) (n := n) (r := E.rank)
    (q := F.rank) (E := EU.Fiber) (F := FU.Fiber)
  have hclasses : globalPrincipalSymbolClass EU.Fiber FU.Fiber 0 pU =
      globalPrincipalSymbolClass EU.Fiber FU.Fiber 0 rU :=
    (globalPrincipalSymbolClass_eq_iff EU.Fiber FU.Fiber 0 pU rU).mpr hdU
  have hprincipal : PU.principalSymbol = globalPrincipalSymbolClass EU.Fiber FU.Fiber 0
      (RU.regularizedSymbol 0 aU.val aU.property.1 aU.property.2) :=
    hPUp.trans (hclasses.trans
      (globalPrincipalSymbolClass_restrictOpen_regularized E F U R RU a ha aU haU))
  exact ⟨PU, RU, aU, hprincipal, (PU.isElliptic_iff_homogeneous RU aU hprincipal).mpr haUi,
    haU, hPUaction⟩

end AtiyahSinger
