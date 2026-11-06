/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenSymbolCoordinates
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Open transport of a relative homogeneous elliptic symbol

Public module ID: M0824.

The specified inverse-dual differential and the two specified fiber equivalences
transport the original homogeneous symbol. Its exact exterior agreement glues
this transport to the supplied ambient bundle map, including the zero covectors.
This is the symbol construction of SG III.13.4, independent of quantization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40


variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [hT : T2Space M] [hT' : T2Space N]
  [hSC : SecondCountableTopology M] [hSC' : SecondCountableTopology N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (K : Set M) (L : Set N) (hL : IsCompact L)
  (hLV : L ⊆ (V : Set N))
  (hKL : e ⁻¹' ((Subtype.val : V → N) ⁻¹' L) = (Subtype.val : U → M) ⁻¹' K)
  (α : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (α x).toLinearMap))
  (β : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (β x).toLinearMap))


omit hT hSC hSC' in
include hL hLV hKL hα hβ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The original open fibers and the inverse-dual differential are retained throughout gluing.
/-- Relative homogeneous data glue to the specified exterior map under open identification. -/
theorem exists_openHomogeneousSymbol
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0)
    (ha : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x)
    (haext : ∀ x, x ∉ K → ∀ ξ, a.val x ξ = c x)
    (d : ∀ y, G.Fiber y →L[ℂ] H.Fiber y)
    (hd : IsSmoothBundleMap (n := n) (r := G.rank) (q := H.rank)
      (fun y ↦ (d y).toLinearMap))
    (hcd : ∀ (x : U) (v : E.Fiber x.val), d (e x).val (α x v) = β x (c x.val v))
    (hdext : ∀ y, y ∉ L → Function.Bijective (d y)) :
    ∃ a' : homogeneousGlobalSymbolSpace (n := n) (r := G.rank) (q := H.rank)
        G.Fiber H.Fiber 0,
      IsEllipticGlobalSymbol G.Fiber H.Fiber a'.val ∧
      (∀ (x : U) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val),
        a'.val (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (α x v) =
          β x (a.val x.val ξ v)) ∧
      (∀ y, y ∉ L → ∀ η, a'.val y η = d y) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let (x : M) : FiniteDimensional ℂ (E.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin E.rank)) E.Fiber x
  let (x : M) : FiniteDimensional ℂ (F.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x
  let (x : N) : FiniteDimensional ℂ (G.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin G.rank)) G.Fiber x
  let (x : N) : FiniteDimensional ℂ (H.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin H.rank)) H.Fiber x
  let α₀ (x : U) : E.Fiber x.val ≃ₗ[ℂ] G.Fiber (e x).val :=
    { toFun := α x
      invFun := (α x).symm
      left_inv := (α x).left_inv
      right_inv := (α x).right_inv
      map_add' := (α x).map_add
      map_smul' := (α x).map_smul }
  let β₀ (x : U) : F.Fiber x.val ≃ₗ[ℂ] H.Fiber (e x).val :=
    { toFun := β x
      invFun := (β x).symm
      left_inv := (β x).left_inv
      right_inv := (β x).right_inv
      map_add' := (β x).map_add
      map_smul' := (β x).map_smul }
  let P (y : V) := CotangentFiber (n := n) y.val → (G.Fiber y.val →L[ℂ] H.Fiber y.val)
  let T (x : U) : P (e x) := fun η ↦
    (β₀ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((a.val x.val (η.comp (mfderiv I I e x))).comp
        (α₀ x).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let T' : ∀ y : V, P y := Equiv.piCongrLeft P e.toEquiv T
  let J : GlobalSymbolFunction (n := n) G.Fiber H.Fiber := fun y ↦
    if hy : y ∈ V then T' ⟨y, hy⟩ else fun _ ↦ d y
  -- Pull the fiber-map family along the same open diffeomorphism before evaluation.
  have hJ (x : U) (η : CotangentFiber (n := n) (e x).val) :
      J (e x).val η = T x η := by
    simp only [J, (e x).property, ↓reduceDIte]
    exact congrFun (Equiv.piCongrLeft_apply_apply P e.toEquiv T x) η
  have hleft (x : U) : (mfderiv I I e.symm (e x)).comp (mfderiv I I e x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hc := mfderiv_comp x (e.symm.mdifferentiable (by simp) (e x))
      (e.mdifferentiable (by simp) x)
    rw [show (e.symm : V → U) ∘ e = id from funext e.symm_apply_apply, mfderiv_id] at hc
    exact hc.symm
  have hright (x : U) : (mfderiv I I e x).comp (mfderiv I I e.symm (e x)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hc := mfderiv_comp (e x) (e.mdifferentiable (by simp) (e.symm (e x)))
      (e.symm.mdifferentiable (by simp) (e x))
    rw [show (e : U → V) ∘ e.symm = id from funext e.apply_symm_apply, mfderiv_id,
      e.symm_apply_apply] at hc
    exact hc.symm
  have hformula (x : U) (ξ : CotangentFiber (n := n) x.val) (v : E.Fiber x.val) :
      J (e x).val (cotangentDiffeomorphMap e ⟨x, ξ⟩).snd (α x v) =
        β x (a.val x.val ξ v) := by
    rw [hJ]
    change β₀ x (a.val x.val
      ((ξ.comp (mfderiv I I e.symm (e x))).comp (mfderiv I I e x))
      ((α₀ x).symm (α₀ x v))) = _
    erw [ContinuousLinearMap.comp_assoc, hleft, ContinuousLinearMap.comp_id,
      (α₀ x).symm_apply_apply]
    rfl
  -- The transported and exterior definitions agree off L, including zero covectors.
  have hexterior (y : N) (hy : y ∉ L) (η : CotangentFiber (n := n) y) : J y η = d y := by
    by_cases hyV : y ∈ V
    · obtain ⟨x, hx⟩ := e.surjective ⟨y, hyV⟩
      have hxy : (e x).val = y := congrArg Subtype.val hx
      have hxK : x.val ∉ K := by
        have heq := Set.ext_iff.mp hKL x
        exact fun h ↦ hy (hxy ▸ heq.mpr h)
      subst y
      rw [hJ]
      apply ContinuousLinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := (α₀ x).surjective w
      change β₀ x (a.val x.val _ ((α₀ x).symm (α₀ x v))) = _
      rw [(α₀ x).symm_apply_apply, haext x.val hxK]
      exact (hcd x v).symm
    · simp only [J, hyV, ↓reduceDIte]
  have hsmooth : IsSmoothOffZeroGlobalSymbol (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber J := by
    intro C hC f g hf hg p hp
    let X := EuclideanSpace ℝ (Fin n)
    have hCinv : ContMDiffAt I I ∞ C.symm p.1 :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (subset_maximalAtlas (I := I) (n := ∞) hC) hp.1.1.1
    by_cases hpL : C.symm p.1 ∈ L
    · -- One shared coordinate formula retains the original cotangent and frame witnesses.
      obtain ⟨C₀, f₀, g₀, hf₀, hg₀, hC₀, Z, t, A, B, hZ, hpZ, _, hZt, htS,
        ht, hts, hA, hB, _, hcoordinate⟩ :=
        exists_local_openSymbolInChart E F G H U V e α hα β hβ C hC f g
          p.1 hp.1 (hLV hpL)
      let := hf₀
      let := hg₀
      have hraw (x : U) η (v : E.Fiber x.val) :
          J (e x).val η (α x v) = β x (a.val x.val (η.comp (mfderiv I I e x)) v) := by
        rw [hJ]
        change β₀ x (a.val x.val _ ((α₀ x).symm (α₀ x v))) = _
        rw [(α₀ x).symm_apply_apply]
        rfl
      have hpT := hZt hpZ
      have hforward := ht.contDiffAt (t.open_source.mem_nhds (t.map_target hpT))
      have hbackward := hts.contDiffAt (t.open_target.mem_nhds hpT)
      let D (y : X) := fderiv ℝ t (t.symm y)
      let adjointMap : (X →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) :=
        ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
      have hD : ContDiffAt ℝ ∞ D p.1 :=
        (hforward.fderiv_right (m := ∞) (by simp)).comp p.1 hbackward
      have hν : ContDiffAt ℝ ∞ (fun z : X × X ↦ (D z.1).adjoint z.2) p :=
        (adjointMap.contDiff.contDiffAt.comp p (hD.comp p contDiffAt_fst)).clm_apply
          contDiffAt_snd
      have hη : (D p.1).adjoint p.2 ≠ 0 := by
        have hrightD : (D p.1).comp (fderiv ℝ t.symm p.1) =
            ContinuousLinearMap.id ℝ X := by
          apply ((hforward.differentiableAt (by simp)).hasFDerivAt.comp p.1
            (hbackward.differentiableAt (by simp)).hasFDerivAt).unique
          apply (hasFDerivAt_id p.1).congr_of_eventuallyEq
          filter_upwards [t.open_target.mem_nhds hpT] with y hy
          exact t.right_inv hy
        have hdual := congrArg ContinuousLinearMap.adjoint hrightD
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at hdual
        intro hzero
        have h := congrArg (fun T ↦ T p.2) hdual
        change (fderiv ℝ t.symm p.1).adjoint ((D p.1).adjoint p.2) = p.2 at h
        rw [hzero, map_zero] at h
        exact hp.2 h.symm
      have hsource : ContDiffAt ℝ ∞
          (Function.uncurry (globalSymbolInChart E.Fiber F.Fiber a.val C₀ f₀ g₀))
          (t.symm p.1, (D p.1).adjoint p.2) := (a.property.1 C₀ hC₀ f₀ g₀).contDiffAt
        (((isOpen_symbolChartDomain E.Fiber F.Fiber C₀ f₀ g₀).prod isOpen_ne).mem_nhds
          ⟨htS (t.map_target hpT), hη⟩)
      have hcomposition : ContDiffAt ℝ ∞ (fun z : X × X ↦
          globalSymbolInChart E.Fiber F.Fiber a.val C₀ f₀ g₀
            (t.symm z.1) ((D z.1).adjoint z.2)) p :=
        ContDiffAt.comp
          (f := fun z : X × X ↦ (t.symm z.1, (D z.1).adjoint z.2))
          (g := Function.uncurry (globalSymbolInChart E.Fiber F.Fiber a.val C₀ f₀ g₀)) p
          hsource ((hbackward.comp p contDiffAt_fst).prodMk hν)
      have hcompose (i j k : ℕ) : ContDiff ℝ ∞
          (fun q : (EuclideanSpace ℂ (Fin j) →L[ℂ] EuclideanSpace ℂ (Fin k)) ×
              (EuclideanSpace ℂ (Fin i) →L[ℂ] EuclideanSpace ℂ (Fin j)) ↦
            q.1.comp q.2) :=
        (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin i))
          (F := EuclideanSpace ℂ (Fin j)) (G := EuclideanSpace ℂ (Fin k))).contDiff
            |>.restrict_scalars ℝ
      have hregular := (hcompose G.rank F.rank H.rank).comp₂_contDiffAt
        ((hA.contDiffAt (hZ.mem_nhds hpZ)).comp p contDiffAt_fst)
        ((hcompose G.rank E.rank F.rank).comp₂_contDiffAt hcomposition
          ((hB.contDiffAt (hZ.mem_nhds hpZ)).comp p contDiffAt_fst))
      apply (hregular.congr_of_eventuallyEq ?_).contDiffWithinAt
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hZ.mem_nhds hpZ)]
        with z hz
      exact hcoordinate a.val J hraw z.1 hz z.2
    · -- Away from L the same map is d on an open neighborhood, even at zero frequency.
      have hmat := hd.contMDiffOn_matrix (fun y ↦ (d y).toLinearMap) f g
      have hlocal := (hmat.contMDiffAt
        ((f.open_baseSet.inter g.open_baseSet).mem_nhds ⟨hp.1.1.2, hp.1.2⟩)).comp
          p.1 hCinv
      have hregular := hlocal.contDiffAt.comp p contDiffAt_fst
      apply (hregular.congr_of_eventuallyEq ?_).contDiffWithinAt
      have hbase : ContinuousAt (fun z : X × X ↦ C.symm z.1) p :=
        hCinv.continuousAt.comp continuousAt_fst
      filter_upwards [hbase.preimage_mem_nhds (hL.isClosed.isOpen_compl.mem_nhds hpL)]
        with z hz
      change globalSymbolInChart G.Fiber H.Fiber J C f g z.1 z.2 = _
      dsimp only [globalSymbolInChart]
      rw [hexterior (C.symm z.1) hz]
      rfl
  have hhomogeneous : IsHomogeneousGlobalSymbol (n := n) G.Fiber H.Fiber 0 J := by
    intro y η hη t ht
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul]
    by_cases hy : y ∈ V
    · obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
      have hxy : (e x).val = y := congrArg Subtype.val hx
      subst y
      rw [hJ, hJ]
      have hη' : η.comp (mfderiv I I e x) ≠ 0 := by
        intro h
        have heq := congrArg (fun Q ↦ Q.comp (mfderiv I I e.symm (e x))) h
        erw [ContinuousLinearMap.comp_assoc, hright, ContinuousLinearMap.comp_id,
          ContinuousLinearMap.zero_comp] at heq
        exact hη heq
      dsimp only [T]
      rw [ContinuousLinearMap.smul_comp, a.property.2 x.val _ hη' t ht]
      simp
    · simp only [J, hy, ↓reduceDIte]
  have helliptic : IsEllipticGlobalSymbol (n := n) G.Fiber H.Fiber J := by
    intro y η hη
    by_cases hy : y ∈ L
    · obtain ⟨x, hx⟩ := e.surjective ⟨y, hLV hy⟩
      have hxy : (e x).val = y := congrArg Subtype.val hx
      subst y
      rw [hJ]
      have hη' : η.comp (mfderiv I I e x) ≠ 0 := by
        intro h
        have heq := congrArg (fun Q ↦ Q.comp (mfderiv I I e.symm (e x))) h
        erw [ContinuousLinearMap.comp_assoc, hright, ContinuousLinearMap.comp_id,
          ContinuousLinearMap.zero_comp] at heq
        exact hη heq
      exact (β₀ x).bijective.comp ((ha x.val _ hη').comp (α₀ x).symm.bijective)
    · rw [hexterior y hy]
      exact hdext y hy
  exact ⟨⟨J, hsmooth, hhomogeneous⟩, helliptic, hformula, hexterior⟩

end AtiyahSinger
