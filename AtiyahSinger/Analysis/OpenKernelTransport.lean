/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Geometry.RelativeMetricDensity

/-!
# Compact smooth kernels transported through an open identification

Public module ID: M0827.

A compactly supported smooth bundle kernel can be carried through an open
manifold diffeomorphism and the specified two fiber equivalences, then extended
by zero. The proof keeps the complete two-variable kernel and the native bundle
frames. This supplies the smoothing part of exact open PDO extension; no compact
source manifold or Schwartz kernel theorem is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace Filter Set
open scoped Manifold ContDiff Topology SchwartzMap

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
  (a : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (a x).toLinearMap))
  (b : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hb : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (b x).toLinearMap))


include ha hb in
omit hN hT hSC hSC' in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- Native pullback frames and the three smooth matrix factors are compared pointwise.
/-- Open transport preserves the actual smooth kernel and compact support in both variables. -/
theorem SmoothKernel.exists_openTransport
    (S : SmoothKernel (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (C : Set M) (hC : IsCompact C) (hCU : C ⊆ (U : Set M))
    (hS : ∀ x y, x ∉ C ∨ y ∉ C → S.toFun x y = 0) :
    ∃ S' : SmoothKernel (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber,
      (∀ (x y : U) (v : E.Fiber y.val),
        S'.toFun (e x).val (e y).val (a y v) = b x (S.toFun x.val y.val v)) ∧
      ∃ C' : Set N, IsCompact C' ∧ C' ⊆ V ∧
        ∀ x y, x ∉ C' ∨ y ∉ C' → S'.toFun x y = 0 := by
  /- Transport the full two-variable kernel on U × U before extending by zero.
  In native frames the transported kernel is a product of the output matrix,
  the original kernel matrix, and the inverse input matrix. Compact support
  makes the extended kernel locally zero at every boundary point. -/
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
  let a₀ (x : U) : E.Fiber x.val ≃ₗ[ℂ] G.Fiber (e x).val :=
    { toFun := a x
      invFun := (a x).symm
      left_inv := (a x).left_inv
      right_inv := (a x).right_inv
      map_add' := (a x).map_add
      map_smul' := (a x).map_smul }
  let b₀ (x : U) : F.Fiber x.val ≃ₗ[ℂ] H.Fiber (e x).val :=
    { toFun := b x
      invFun := (b x).symm
      left_inv := (b x).left_inv
      right_inv := (b x).right_inv
      map_add' := (b x).map_add
      map_smul' := (b x).map_smul }
  -- Pull the full two-variable kernel along the product of the same diffeomorphism.
  let pairEquiv : (U × U) ≃ (V × V) := e.toEquiv.prodCongr e.toEquiv
  let P (z : V × V) := G.Fiber z.2.val →L[ℂ] H.Fiber z.1.val
  let T (z : U × U) : P (pairEquiv z) :=
    (b₀ z.1).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((S.toFun z.1.val z.2.val).comp
        (a₀ z.2).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  let T' : ∀ z : V × V, P z := Equiv.piCongrLeft P pairEquiv T
  let J (x y : N) : G.Fiber y →L[ℂ] H.Fiber x :=
    if hx : x ∈ V then
      if hy : y ∈ V then T' (⟨x, hx⟩, ⟨y, hy⟩) else 0
    else 0
  have hJ (x y : U) (v : E.Fiber y.val) :
      J (e x).val (e y).val (a y v) = b x (S.toFun x.val y.val v) := by
    simp only [J, (e x).property, (e y).property, ↓reduceDIte]
    have ht : T' (e x, e y) = T (x, y) :=
      Equiv.piCongrLeft_apply_apply P pairEquiv T (x, y)
    rw [ht]
    change b₀ x (S.toFun x.val y.val ((a₀ y).symm (a₀ y v))) = _
    rw [(a₀ y).symm_apply_apply]
    rfl
  -- The same image of the source support controls both target kernel variables.
  let C' : Set N := Set.range (fun x : C ↦ (e ⟨x.val, hCU x.property⟩).val)
  have hC' : IsCompact C' := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    apply isCompact_range
    exact continuous_subtype_val.comp (e.continuous.comp
      (continuous_subtype_val.subtype_mk (fun x : C ↦ hCU x.property)))
  have hC'V : C' ⊆ V := by
    rintro y ⟨x, rfl⟩
    exact (e ⟨x.val, hCU x.property⟩).property
  have hmemC' (x : U) (hx : x.val ∈ C) : (e x).val ∈ C' :=
    ⟨⟨x.val, hx⟩, rfl⟩
  have hJzero (x y : U) (hxy : x.val ∉ C ∨ y.val ∉ C) :
      J (e x).val (e y).val = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := (a₀ y).surjective w
    change J (e x).val (e y).val (a y v) = 0
    rw [hJ, hS x.val y.val hxy]
    exact map_zero _
  have hzero (x y : N) (hxy : x ∉ C' ∨ y ∉ C') : J x y = 0 := by
    by_cases hx : x ∈ V
    · by_cases hy : y ∈ V
      · obtain ⟨x₀, hx₀⟩ := e.surjective ⟨x, hx⟩
        obtain ⟨y₀, hy₀⟩ := e.surjective ⟨y, hy⟩
        have hxval : (e x₀).val = x := congrArg Subtype.val hx₀
        have hyval : (e y₀).val = y := congrArg Subtype.val hy₀
        have hout : x₀.val ∉ C ∨ y₀.val ∉ C := by
          rcases hxy with hout | hout
          · exact Or.inl (fun h ↦ hout (hxval ▸ hmemC' x₀ h))
          · exact Or.inr (fun h ↦ hout (hyval ▸ hmemC' y₀ h))
        have h := hJzero x₀ y₀ hout
        rw [hxval, hyval] at h
        exact h
      · simp only [J, hx, hy, ↓reduceDIte]
    · simp only [J, hx, ↓reduceDIte]
  -- Smoothness is local: use native matrices inside V and zero outside the compact support.
  have hsmooth : IsSmoothKernel (n := n) (r := G.rank) (q := H.rank)
      G.Fiber H.Fiber J := by
    intro f g _ _ p hp
    by_cases hpc : p ∈ C' ×ˢ C'
    · have hpV : p ∈ (V : Set N) ×ˢ V := ⟨hC'V hpc.1, hC'V hpc.2⟩
      let hVne : Nonempty V := ⟨⟨p.1, hpV.1⟩⟩
      let j := (V.openPartialHomeomorphSubtypeCoe hVne).symm
      have hjval (y : N) (hy : y ∈ V) : (j y).val = y :=
        (V.openPartialHomeomorphSubtypeCoe hVne).right_inv (by
          rw [Opens.openPartialHomeomorphSubtypeCoe_target]
          exact hy)
      have hj : ContMDiffOn I I ∞ j (V : Set N) := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff V j (V : Set N) y).mp
        apply contMDiffWithinAt_id.congr
        · intro z hz
          exact hjval z hz
        · exact hjval y hy
      let q (y : N) : U := e.symm (j y)
      have hq : ContMDiffOn I I ∞ q (V : Set N) :=
        e.symm.contMDiff.comp_contMDiffOn hj
      have hqval (y : N) (hy : y ∈ V) : (e (q y)).val = y := by
        simp only [q, e.apply_symm_apply, hjval y hy]
      let d := trivializationAt (EuclideanSpace ℂ (Fin E.rank)) E.Fiber (q p.2).val
      let k := trivializationAt (EuclideanSpace ℂ (Fin F.rank)) F.Fiber (q p.1).val
      let A (x : U) := ((d.linearMapAt ℂ x.val).comp
        ((a x).symm.toLinearMap.comp (f.symmL ℂ (e x).val).toLinearMap)).toContinuousLinearMap
      let B (x : U) := ((g.linearMapAt ℂ (e x).val).comp
        ((b x).toLinearMap.comp (k.symmL ℂ x.val).toLinearMap)).toContinuousLinearMap
      have hA := (contMDiffOn_openBundleMap_matrices E G U V e a ha d f).2
      have hB := (contMDiffOn_openBundleMap_matrices F H U V e b hb k g).1
      have hxq : ContMDiffAt (I.prod I) I ∞ (fun z : N × N ↦ q z.1) p :=
        (hq.contMDiffAt (V.isOpen.mem_nhds hpV.1)).comp p contMDiffAt_fst
      have hyq : ContMDiffAt (I.prod I) I ∞ (fun z : N × N ↦ q z.2) p :=
        (hq.contMDiffAt (V.isOpen.mem_nhds hpV.2)).comp p contMDiffAt_snd
      have hxM := (contMDiff_subtype_val (U := U) (I := I)).contMDiffAt.comp p hxq
      have hyM := (contMDiff_subtype_val (U := U) (I := I)).contMDiffAt.comp p hyq
      have hAat : ContMDiffAt I
          𝓘(ℝ, EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin E.rank))
          ∞ A (q p.2) := by
        apply hA.contMDiffAt
        apply ((d.open_baseSet.preimage continuous_subtype_val).inter
          (f.open_baseSet.preimage (continuous_subtype_val.comp e.continuous))).mem_nhds
        exact ⟨mem_baseSet_trivializationAt _ _ _, by
          change (e (q p.2)).val ∈ f.baseSet
          rw [hqval p.2 hpV.2]
          exact hp.2⟩
      have hBat : ContMDiffAt I
          𝓘(ℝ, EuclideanSpace ℂ (Fin F.rank) →L[ℂ] EuclideanSpace ℂ (Fin H.rank))
          ∞ B (q p.1) := by
        apply hB.contMDiffAt
        apply ((k.open_baseSet.preimage continuous_subtype_val).inter
          (g.open_baseSet.preimage (continuous_subtype_val.comp e.continuous))).mem_nhds
        exact ⟨mem_baseSet_trivializationAt _ _ _, by
          change (e (q p.1)).val ∈ g.baseSet
          rw [hqval p.1 hpV.1]
          exact hp.1⟩
      have hKat : ContMDiffAt (I.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin E.rank) →L[ℂ] EuclideanSpace ℂ (Fin F.rank))
          ∞ (kernelInFrames E.Fiber F.Fiber S.toFun d k) ((q p.1).val, (q p.2).val) :=
        (S.isSmooth d k).contMDiffAt
        ((k.open_baseSet.prod d.open_baseSet).mem_nhds
          ⟨mem_baseSet_trivializationAt _ _ _, mem_baseSet_trivializationAt _ _ _⟩)
      have hK := hKat.comp p (hxM.prodMk hyM)
      have hcomp₁ : ContDiff ℝ ∞ (fun z :
          (EuclideanSpace ℂ (Fin E.rank) →L[ℂ] EuclideanSpace ℂ (Fin F.rank)) ×
          (EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin E.rank)) ↦
            z.1.comp z.2) :=
        (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
      have hcomp₂ : ContDiff ℝ ∞ (fun z :
          (EuclideanSpace ℂ (Fin F.rank) →L[ℂ] EuclideanSpace ℂ (Fin H.rank)) ×
          (EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin F.rank)) ↦
            z.1.comp z.2) :=
        (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
      have hright := hcomp₁.comp_contMDiffAt (hK.prodMk_space (hAat.comp p hyq))
      have hfull := hcomp₂.comp_contMDiffAt ((hBat.comp p hxq).prodMk_space hright)
      have hformula (x y : U) (hx : x.val ∈ k.baseSet) (hy : y.val ∈ d.baseSet) :
          kernelInFrames G.Fiber H.Fiber J f g ((e x).val, (e y).val) =
            (B x).comp ((kernelInFrames E.Fiber F.Fiber S.toFun d k (x.val, y.val)).comp
              (A y)) := by
        apply ContinuousLinearMap.ext
        intro w
        let v := (a₀ y).symm (f.symmL ℂ (e y).val w)
        have heq := hJ x y v
        have hav : a y v = f.symmL ℂ (e y).val w := (a₀ y).apply_symm_apply _
        rw [hav] at heq
        change g.continuousLinearMapAt ℂ (e x).val
          (J (e x).val (e y).val (f.symmL ℂ (e y).val w)) =
          g.linearMapAt ℂ (e x).val (b x (k.symmL ℂ x.val
            (k.continuousLinearMapAt ℂ x.val (S.toFun x.val y.val
              (d.symmL ℂ y.val (d.linearMapAt ℂ y.val v))))))
        rw [heq]
        simp only [d.coe_linearMapAt_of_mem hy,
          k.continuousLinearMapAt_apply_of_mem ℂ hx, d.symmL_apply hy,
          k.symmL_apply hx, d.symm_apply_apply_mk hy, k.symm_apply_apply_mk hx]
        rfl
      apply hfull.congr_of_eventuallyEq ?_ |>.contMDiffWithinAt
      filter_upwards [(V.isOpen.prod V.isOpen).mem_nhds hpV,
        hxM.continuousAt.preimage_mem_nhds (k.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ _)),
        hyM.continuousAt.preimage_mem_nhds (d.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ _))] with z hz hx hy
      have h := hformula (q z.1) (q z.2) hx hy
      rw [hqval z.1 hz.1, hqval z.2 hz.2] at h
      exact h
    · have hn := (hC'.isClosed.prod hC'.isClosed).isOpen_compl.mem_nhds hpc
      apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin G.rank) →L[ℂ]
        EuclideanSpace ℂ (Fin H.rank)))).congr_of_eventuallyEq ?_ |>.contMDiffWithinAt
      filter_upwards [hn] with z hz
      have hxy : z.1 ∉ C' ∨ z.2 ∉ C' := by
        simpa only [Set.mem_compl_iff, Set.mem_prod, not_and_or] using hz
      simp only [kernelInFrames, hzero z.1 z.2 hxy, ContinuousLinearMap.zero_comp,
        ContinuousLinearMap.comp_zero]
  exact ⟨⟨J, hsmooth⟩, hJ, C', hC', hC'V, hzero⟩

end AtiyahSinger
