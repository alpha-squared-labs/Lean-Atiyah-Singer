/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DiffeomorphSymbolKClass
public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.EquivariantHomogeneousIndexDiffeomorph
public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbolPullback
public import AtiyahSinger.Analysis.EquivariantSectionPullback

/-!
# Equivariant elliptic data under the actual diffeomorphism

Public module ID: M0588.

Pull back the original smooth bundles along the inverse diffeomorphism, with
exactly their pulled actions. A single equivariant source operator transports
with its full section action. Its target principal symbol is therefore invariant,
and the same source and target section equivalences identify both finite defect
representations. The original inverse-dual cotangent map simultaneously gives
the proper pullback of the stored symbol K class. This is the transport needed
when comparing two native carriers of a common clopen refinement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace Set
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- The two native pullback bundles and their section, symbol and cotangent squares share witnesses.
/-- The actual inverse diffeomorphism transports both the full index and original symbol K class. -/
theorem EquivariantEllipticSymbolData.exists_diffeomorph_pullback
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N)
    (he : ∀ (g : G) (x : M), e (g • x) = g • e x)
    (hcot : letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
      letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
      ∀ (g : G) (z : CotangentTotalSpace (n := n) (M := N)),
        cotangentDiffeomorph e.symm (g • z) = g • cotangentDiffeomorph e.symm z) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃ b : EquivariantEllipticSymbolData (n := n) (M := N) (VG := VG) (G := G),
      b.index = a.index ∧ b.kClass = equivariantSupportTripleKZeroPullback
        ⟨cotangentDiffeomorph e.symm, (cotangentDiffeomorph e.symm).continuous⟩
        hcot (cotangentDiffeomorph e.symm).isProperMap a.kClass := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let IG := 𝓘(ℝ, VG)
  let E := a.source
  let F := a.target
  let f : C(N, M) := ⟨e.symm, e.symm.continuous⟩
  have hf (g : G) (y : N) : f (g • y) = g • f y := by
    apply e.injective
    change e (e.symm (g • y)) = e (g • e.symm y)
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  let B := E.pullback f e.symm.contMDiff
  let C := F.pullback f e.symm.contMDiff
  let := isSmoothComplexBundle_pullback (n := n) (m := n) (r := a.source.rank)
    a.source.Fiber f e.symm.contMDiff
  let := isSmoothComplexBundle_pullback (n := n) (m := n) (r := a.target.rank)
    a.target.Fiber f e.symm.contMDiff
  let τE := a.sourceAction.modelPullback f hf
  let τF := a.targetAction.modelPullback f hf
  have hτE := a.sourceAction.modelPullback_isSmooth IG a.source_smooth f hf e.symm.contMDiff
  have hτF := a.targetAction.modelPullback_isSmooth IG a.target_smooth f hf e.symm.contMDiff
  let α (x : (⊤ : Opens M)) :=
    LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x.val).symm
  let β (x : (⊤ : Opens M)) :=
    LinearEquiv.cast (R := ℂ) (M := F.Fiber) (e.symm_apply_apply x.val).symm
  have hα := isSmoothBundleMap_diffeomorphPullback_top E e
  have hβ := isSmoothBundleMap_diffeomorphPullback_top F e
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨ν, hν⟩ := exists_smoothPositiveMeasure (n := n) (M := N)
  let := hν
  obtain ⟨A⟩ := nonempty_quantizationPresentation
    (n := n) (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := B.rank) (q := C.rank) (E := B.Fiber) (F := C.Fiber)
  -- Select the actual transported symbol in these fixed inverse-pullback bundles.
  obtain ⟨_P₀, _Q₀, b, _hP₀, _hQ₀, hb, _hP₀a, _hQ₀b, hsquare, _hindex₀⟩ :=
    exists_elliptic_representatives_of_diffeomorph E F B C ⊤ ⊤ rfl rfl (diffeomorphTop e)
      α hα β hβ ν μ a.symbol a.elliptic A R
  -- The inverse-dual square is equivalently the forward derivative square used by PDO transport.
  have hab (x : (⊤ : Opens M)) (η : CotangentFiber (n := n) (e x.val))
      (v : E.Fiber x.val) : b.val (e x.val) η (α x v) =
      β x (a.symbol.val x.val (η.comp (mfderiv I I (diffeomorphTop e) x)) v) := by
    let t := diffeomorphTop e
    have hcomp := mfderiv_comp (t x)
      (t.mdifferentiable (by simp) (t.symm (t x)))
      (t.symm.mdifferentiable (by simp) (t x))
    rw [show (t : (⊤ : Opens M) → (⊤ : Opens N)) ∘ t.symm = id from
      funext t.apply_symm_apply, mfderiv_id] at hcomp
    erw [t.symm_apply_apply] at hcomp
    have hη : (cotangentDiffeomorphMap t
        ⟨x, η.comp (mfderiv I I t x)⟩).snd = η := by
      change (η.comp (mfderiv I I t x)).comp (mfderiv I I t.symm (t x)) = η
      rw [ContinuousLinearMap.comp_assoc, ← hcomp, ContinuousLinearMap.comp_id]
    have h := hsquare x (η.comp (mfderiv I I t x)) v
    rw [hη] at h
    exact h
  have sections (D : SmoothFiniteComplexBundle (n := n) M)
      (σ : letI := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
        EquivariantStructure G D.Fiber)
      (hσ : σ.IsSmooth (n := n) (r := D.rank) IG) :
      let D' := D.pullback f e.symm.contMDiff
      letI := isSmoothComplexBundle_pullback (n := n) (m := n) (r := D.rank)
        D.Fiber f e.symm.contMDiff
      let τ := σ.modelPullback f hf
      let hτ := σ.modelPullback_isSmooth IG hσ f hf e.symm.contMDiff
      ∃ S : smoothSections (n := n) (r := D.rank) D.Fiber ≃ₗ[ℂ]
          smoothSections (n := n) (r := D'.rank) D'.Fiber,
        (∀ u (x : (⊤ : Opens M)), (S u).val (e x.val) =
          LinearEquiv.cast (R := ℂ) (M := D.Fiber) (e.symm_apply_apply x.val).symm
            (u.val x.val)) ∧
        ∀ g u, S (σ.smoothSectionRepresentation IG hσ g u) =
          τ.smoothSectionRepresentation IG hτ g (S u) := by
    dsimp only
    let := isSmoothComplexBundle_pullback (n := n) (m := n) (r := D.rank)
      D.Fiber f e.symm.contMDiff
    let S := smoothSectionDiffeomorphEquiv (n := n) (m := n) (r := D.rank) D.Fiber e.symm
    refine ⟨S, ?_, ?_⟩
    · intro u x
      have hval (y z : M) (h : y = z) :
          u.val y = LinearEquiv.cast (R := ℂ) (M := D.Fiber) h.symm (u.val z) := by
        subst z
        rfl
      exact hval _ _ (e.symm_apply_apply x.val)
    · intro g u
      exact σ.smoothSectionPullback_intertwines IG hσ f hf e.symm.contMDiff g u
  obtain ⟨S, hS, hSg⟩ := sections E a.sourceAction a.source_smooth
  obtain ⟨T, hT, hTg⟩ := sections F a.targetAction a.target_smooth
  have hfixed (g : G) : equivariantPrincipalSymbolRepresentation IG
      a.sourceAction a.targetAction a.source_smooth a.target_smooth 0 g
      (globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (A.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2)) =
      globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (A.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2) :=
    (A.equivariant_regularizedSymbol_class_eq_iff IG a.sourceAction a.targetAction
      a.source_smooth a.target_smooth A 0 a.symbol a.symbol g).mpr (a.equivariant g)
  obtain ⟨P, hPg, hPa⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG a.sourceAction a.targetAction a.source_smooth a.target_smooth 0
      (globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (A.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2)) hfixed
  have hP : P.IsElliptic := (P.isElliptic_iff_homogeneous A a.symbol hPa).mpr a.elliptic
  obtain ⟨Q, hQb, hact⟩ := P.exists_diffeomorph_transport E F B C ⊤ ⊤ rfl rfl
    (diffeomorphTop e) α hα β hβ ν μ A R a.symbol a.elliptic b hPa hab
  have hQ : Q.IsElliptic := (Q.isElliptic_iff_homogeneous R b hQb).mpr hb
  have hinter (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      Q.toLinearMap (S u) = T (P.toLinearMap u) := by
    apply Subtype.ext
    funext y
    have h := hact u (S u) (hS u) ⟨e.symm y, mem_univ _⟩
    have ht := hT (P.toLinearMap u) ⟨e.symm y, mem_univ _⟩
    have hboth : (Q.toLinearMap (S u)).val (e (e.symm y)) =
        (T (P.toLinearMap u)).val (e (e.symm y)) := h.trans ht.symm
    erw [e.apply_symm_apply] at hboth
    exact hboth
  have hQg : Q.IsEquivariant IG τE τF hτE hτF := by
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := S.surjective v
    change Q.toLinearMap (τE.smoothSectionRepresentation IG hτE g (S u)) =
      τF.smoothSectionRepresentation IG hτF g (Q.toLinearMap (S u))
    rw [← hSg, hinter, hinter, ← hTg]
    exact congrArg T (LinearMap.congr_fun (hPg g) u)
  -- Equivariance of this same transported operator detects invariance of its homogeneous symbol.
  have hgb (g : G) (y : N) (η : CotangentFiber (n := n) y) (hη : η ≠ 0) :
      equivariantGlobalSymbolLinearMap IG τE τF g b.val y η = b.val y η := by
    have h := Q.equivariant_principalSymbol IG τE τF hτE hτF hQg g
    rw [hQb] at h
    exact ((R.equivariant_regularizedSymbol_class_eq_iff IG τE τF hτE hτF R 0 b b g).mp h)
      y η hη
  let data : EquivariantEllipticSymbolData (n := n) (M := N) (VG := VG) (G := G) := {
    source := B
    target := C
    sourceAction := τE
    targetAction := τF
    source_smooth := hτE
    target_smooth := hτF
    symbol := b
    elliptic := hb
    equivariant := hgb }
  refine ⟨data, ?_, ?_⟩
  · -- The same S and T identify kernels and quotient cokernels of the very same P and Q.
    change equivariantHomogeneousAnalyticIndex IG τE τF hτE hτF b hb hgb =
      equivariantHomogeneousAnalyticIndex IG a.sourceAction a.targetAction
        a.source_smooth a.target_smooth a.symbol a.elliptic a.equivariant
    rw [equivariantHomogeneousAnalyticIndex_eq_smooth IG τE τF hτE hτF b hb hgb ν R Q
      hQg hQ hQb,
      equivariantHomogeneousAnalyticIndex_eq_smooth IG a.sourceAction a.targetAction
        a.source_smooth a.target_smooth a.symbol a.elliptic a.equivariant μ A P hPg hP hPa]
    exact (P.smoothEquivariantAnalyticIndex_eq_of_sectionEquiv
      IG E F B C a.sourceAction a.targetAction τE τF a.source_smooth a.target_smooth
        hτE hτF μ ν Q hPg hP hQg hQ S T hSg hTg hinter).symm
  · -- The inverse-dual cotangent square retains these same bundles, actions and off-zero boundary.
    let d (y : N) (η : CotangentFiber (n := n) y) : CotangentFiber (n := n) (f y) :=
      η.comp (mfderiv I I e (e.symm y))
    let g := cotangentDiffeomorph e
    let h := cotangentDiffeomorph e.symm
    -- Differentiate the actual inverse identity, retaining the original cotangent fibers.
    have hcomp (y : N) : (mfderiv I I e (e.symm y)).comp (mfderiv I I e.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace I y) := by
      have hd := mfderiv_comp y (e.mdifferentiable (by simp) (e.symm y))
        (e.symm.mdifferentiable (by simp) y)
      rw [show (e : M → N) ∘ e.symm = id from funext e.apply_symm_apply, mfderiv_id] at hd
      exact hd.symm
    have hright (z : CotangentTotalSpace (n := n) (M := N)) : g (h z) = z := by
      rcases z with ⟨y, η⟩
      change (⟨e (e.symm y), (η.comp (mfderiv I I e (e.symm y))).comp
        (mfderiv I I e.symm (e (e.symm y)))⟩ : CotangentTotalSpace (n := n) (M := N)) = ⟨y, η⟩
      erw [e.apply_symm_apply]
      congr 1
      rw [ContinuousLinearMap.comp_assoc, hcomp, ContinuousLinearMap.comp_id]
    have hzero (y : N) (η : CotangentFiber (n := n) y) : d y η = 0 ↔ η = 0 := by
      constructor
      · intro hη
        have hz := congrArg (fun T ↦ T.comp (mfderiv I I e.symm y)) hη
        change (η.comp (mfderiv I I e (e.symm y))).comp (mfderiv I I e.symm y) = _ at hz
        rw [ContinuousLinearMap.comp_assoc, hcomp, ContinuousLinearMap.comp_id] at hz
        exact hz
      · rintro rfl
        exact ContinuousLinearMap.zero_comp _
    have hderiv (y : (⊤ : Opens N)) : mfderiv I I (diffeomorphTop e).symm y =
        mfderiv I I e.symm y.val := by
      have hleft := mfderiv_comp y
        ((contMDiff_subtype_val (U := (⊤ : Opens M)) (n := ∞)).mdifferentiable
          (by simp) ((diffeomorphTop e).symm y))
        ((diffeomorphTop e).symm.mdifferentiable (by simp) y)
      have hright := mfderiv_comp y (e.symm.mdifferentiable (by simp) y.val)
        ((contMDiff_subtype_val (U := (⊤ : Opens N)) (n := ∞)).mdifferentiable (by simp) y)
      rw [mfderiv_openSubtypeVal] at hleft hright
      apply ContinuousLinearMap.ext
      intro v
      exact congrArg (fun T ↦ T v) (hleft.symm.trans hright)
    have hsymbol (y : N) (η : CotangentFiber (n := n) y) (_hη : η ≠ 0)
        (v : E.Fiber (f y)) : b.val y η v = a.symbol.val (f y) (d y η) v := by
      have hs := hsquare ⟨e.symm y, mem_univ _⟩ (d y η) v
      dsimp only [cotangentDiffeomorphMap] at hs
      rw [hderiv] at hs
      let η' : CotangentFiber (n := n) (e (e.symm y)) :=
        (d y η).comp (mfderiv I I e.symm (e (e.symm y)))
      have retype (y' : N) (hy : y' = y) (θ : CotangentFiber (n := n) y')
          (hθ : HEq θ η) (w : F.Fiber (e.symm y))
          (heq : b.val y' θ
            (LinearEquiv.cast (R := ℂ) (M := E.Fiber) (congrArg e.symm hy).symm v) =
            LinearEquiv.cast (R := ℂ) (M := F.Fiber) (congrArg e.symm hy).symm w) :
          b.val y η v = w := by
        subst y'
        cases hθ
        exact heq
      have hs' : b.val (e (e.symm y)) η'
          (LinearEquiv.cast (R := ℂ) (M := E.Fiber)
            (congrArg e.symm (e.apply_symm_apply y)).symm v) =
          LinearEquiv.cast (R := ℂ) (M := F.Fiber)
            (congrArg e.symm (e.apply_symm_apply y)).symm (a.symbol.val (f y) (d y η) v) := hs
      have hsnd (u w : CotangentTotalSpace (n := n) (M := N)) (huw : u = w) :
          HEq u.snd w.snd := by
        cases huw
        rfl
      exact retype (e (e.symm y)) (e.apply_symm_apply y) η'
        (hsnd _ _ (hright ⟨y, η⟩)) _ hs'
    exact equivariantHomogeneousSymbolKClass_pullback IG E F a.sourceAction a.targetAction
      f τE τF (a.sourceAction.modelPullback_lift f hf) (a.targetAction.modelPullback_lift f hf)
      d h.continuous h.isProperMap hzero hcot 0 a.symbol b a.elliptic hb a.equivariant hgb hsymbol

end AtiyahSinger
