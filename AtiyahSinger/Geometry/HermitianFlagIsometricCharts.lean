/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianFlagLocalFrames

/-!
# Isometric local trivializations of the original flag topology

Public module ID: M1264.

A continuous local family of isometries acts on the original projection flags
by conjugation. Comparing with a native endomorphism-bundle chart proves that
this gives an actual flag trivialization in the existing topology. Only the
specified open set requires the isometry condition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped BigOperators

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- An isometry transports the original projection flag by conjugation. -/
def hermitianFlagEquivOfIsometry {r : ℕ} {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (H : InnerProductSpace.Core ℂ W)
    (s : EuclideanSpace ℂ (Fin r) ≃L[ℂ] W)
    (hs_inner : ∀ u v, H.inner (s u) (s v) = inner ℂ u v) :
    HermitianFlagSpace r W H ≃
      HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore := by
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let C : (W →L[ℂ] W) ≃A[ℂ] (V →L[ℂ] V) :=
    s.symm.conjContinuousAlgEquiv
  have hC_rank (P : W →L[ℂ] W) :
      Module.finrank ℂ (LinearMap.range (C P).toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
    change Module.finrank ℂ (LinearMap.range
      (s.symm.toLinearEquiv.toLinearMap.comp
        (P.toLinearMap.comp s.toLinearEquiv.toLinearMap))) = _
    rw [LinearMap.range_comp, LinearEquiv.range_comp, LinearEquiv.finrank_map_eq]
  have hC_symmetric (P : W →L[ℂ] W) :
      (∀ u v, H.inner (P u) v = H.inner u (P v)) ↔
        ∀ u v, inner ℂ (C P u) v = inner ℂ u (C P v) := by
    constructor
    · intro hP u v
      change inner ℂ (s.symm (P (s u))) v =
        inner ℂ u (s.symm (P (s v)))
      rw [← hs_inner, ← hs_inner]
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hP (s u) (s v)
    · intro hP u v
      have hp := hP (s.symm u) (s.symm v)
      change inner ℂ (s.symm (P (s (s.symm u)))) (s.symm v) =
        inner ℂ (s.symm u) (s.symm (P (s (s.symm v)))) at hp
      rw [← hs_inner, ← hs_inner] at hp
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp
  have hC_flag (P : Fin r → W →L[ℂ] W) :
      ((∀ i, (P i).comp (P i) = P i) ∧
        (∀ i, Module.finrank ℂ (LinearMap.range (P i).toLinearMap) = 1) ∧
        (∀ i j, i ≠ j → (P i).comp (P j) = 0) ∧
        (∑ i, P i) = ContinuousLinearMap.id ℂ W ∧
        ∀ i u v, H.inner (P i u) v = H.inner u (P i v)) ↔
      ((∀ i, (C (P i)).comp (C (P i)) = C (P i)) ∧
        (∀ i, Module.finrank ℂ (LinearMap.range (C (P i)).toLinearMap) = 1) ∧
        (∀ i j, i ≠ j → (C (P i)).comp (C (P j)) = 0) ∧
        (∑ i, C (P i)) = ContinuousLinearMap.id ℂ V ∧
        ∀ i u v, inner ℂ (C (P i) u) v = inner ℂ u (C (P i) v)) := by
    constructor
    · rintro ⟨hid, hrank, horth, hsum, hself⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        simpa only [← ContinuousLinearMap.mul_def, map_mul] using
          congrArg C (hid i)
      · intro i
        rw [hC_rank]
        exact hrank i
      · intro i j hij
        simpa only [← ContinuousLinearMap.mul_def, map_mul, map_zero] using
          congrArg C (horth i j hij)
      · simpa only [map_sum, ← ContinuousLinearMap.one_def, map_one] using
          congrArg C hsum
      · intro i
        exact (hC_symmetric (P i)).mp (hself i)
    · rintro ⟨hid, hrank, horth, hsum, hself⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        apply C.injective
        simpa only [← ContinuousLinearMap.mul_def, map_mul,
          ContinuousAlgEquiv.coe_toAlgEquiv] using hid i
      · intro i
        rw [← hC_rank (P i)]
        exact hrank i
      · intro i j hij
        apply C.injective
        simpa only [← ContinuousLinearMap.mul_def, map_mul, map_zero,
          ContinuousAlgEquiv.coe_toAlgEquiv] using horth i j hij
      · apply C.injective
        simpa only [map_sum, ← ContinuousLinearMap.one_def, map_one,
          ContinuousAlgEquiv.coe_toAlgEquiv] using hsum
      · intro i
        exact (hC_symmetric (P i)).mpr (hself i)
  let tupleEquiv : (Fin r → W →L[ℂ] W) ≃ (Fin r → V →L[ℂ] V) :=
    Equiv.piCongrRight (fun _ ↦ C.toEquiv)
  exact tupleEquiv.subtypeEquiv hC_flag

variable (r : ℕ) {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianFlagTopology

/-- Continuous local isometries give an actual flag chart with the same conjugation formulas. -/
theorem exists_hermitianFlagTrivialization_of_isometries (x : X)
    (U : TopologicalSpace.Opens X)
    (hU : (U : Set X) ⊆ (trivializationAt (EuclideanSpace ℂ (Fin r)) E x).baseSet)
    (s : ∀ y : X, EuclideanSpace ℂ (Fin r) ≃L[ℂ] E y)
    (hs : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ y ∈ U, ∀ u v, (h.toCore y).inner (s y u) (s y v) = inner ℂ u v)
    (hA : ContinuousOn (fun y ↦
      ((trivializationAt (EuclideanSpace ℂ (Fin r)) E x).continuousLinearMapAt ℂ y).comp
        (s y).toContinuousLinearMap) U)
    (hB : ContinuousOn (fun y ↦ (s y).symm.toContinuousLinearMap.comp
      ((trivializationAt (EuclideanSpace ℂ (Fin r)) E x).symmL ℂ y)) U) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∃ t : Trivialization
        (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
        (hermitianFlagProjection r E h : HermitianFlagBundle r E h → X),
      t.baseSet = U ∧
        (∀ p : HermitianFlagBundle r E h, ∀ hp : p.1 ∈ U,
          t p = (p.1, hermitianFlagEquivOfIsometry (h.toCore p.1) (s p.1) (hs p.1 hp) p.2)) ∧
        ∀ (y : X) (Q : HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
            InnerProductSpace.toCore) (hy : y ∈ U),
          t.toPartialEquiv.symm (y, Q) =
            ⟨y, (hermitianFlagEquivOfIsometry (h.toCore y) (s y) (hs y hy)).symm Q⟩ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let V := EuclideanSpace ℂ (Fin r)
  let F := HermitianFlagSpace r V InnerProductSpace.toCore
  let e := trivializationAt V E x
  let A (y : X) := (e.continuousLinearMapAt ℂ y).comp (s y).toContinuousLinearMap
  let B (y : X) := (s y).symm.toContinuousLinearMap.comp (e.symmL ℂ y)
  let C (y : X) (hy : y ∈ U) := hermitianFlagEquivOfIsometry (h.toCore y) (s y) (hs y hy)
  let Q₀ : F := orthonormalBasisFlag (EuclideanSpace.basisFun (Fin r) ℂ)
  let p₀ : HermitianFlagBundle r E h :=
    (exists_hermitianFlagTrivialization r E h x).choose.toPartialEquiv.symm (x, Q₀)
  let φ : HermitianFlagBundle r E h → X × F := fun p ↦
    (p.1, if hp : p.1 ∈ U then C p.1 hp p.2 else Q₀)
  let ψ : X × F → HermitianFlagBundle r E h := fun q ↦
    if hq : q.1 ∈ U then ⟨q.1, (C q.1 hq).symm q.2⟩ else p₀
  have hφval (p : HermitianFlagBundle r E h) (hp : p.1 ∈ U) :
      φ p = (p.1, C p.1 hp p.2) := by simp only [φ, dite_eq_left hp]
  have hψval (q : X × F) (hq : q.1 ∈ U) :
      ψ q = ⟨q.1, (C q.1 hq).symm q.2⟩ := by simp only [ψ, dite_eq_left hq]
  -- Read the existing flag topology through its original native endomorphism bundle.
  let ι (p : HermitianFlagBundle r E h) :=
    (p.1, fun i : Fin r ↦
      (⟨p.1, p.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)))
  have hι : Topology.IsInducing ι := ⟨rfl⟩
  have hproj : Continuous (fun p : HermitianFlagBundle r E h ↦ p.1) :=
    (hermitianFlagProjection r E h).continuous
  have hcolumn (i : Fin r) : Continuous (fun p : HermitianFlagBundle r E h ↦
      (⟨p.1, p.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y))) :=
    (continuous_apply i).comp (continuous_snd.comp hι.continuous)
  let t := e.continuousLinearMap (RingHom.id ℂ) e
  have hφ : ContinuousOn φ {p | p.1 ∈ U} := by
    have hnative (i : Fin r) : ContinuousOn
        (fun p : HermitianFlagBundle r E h ↦
          (t (⟨p.1, p.2.val i⟩ :
            TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y))).2) {p | p.1 ∈ U} :=
      (t.continuousOn.comp (hcolumn i).continuousOn
        (fun p hp ↦ t.mem_source.mpr ⟨hU hp, hU hp⟩)).snd
    have hmodel (i : Fin r) : ContinuousOn (fun p : HermitianFlagBundle r E h ↦
        (φ p).2.val i) {p | p.1 ∈ U} := by
      have hA' := hA.comp hproj.continuousOn (fun _ hp ↦ hp)
      have hB' := hB.comp hproj.continuousOn (fun _ hp ↦ hp)
      apply (hB'.clm_comp ((hnative i).clm_comp hA')).congr
      intro p hp
      refine (congrArg (fun q : X × F ↦ q.2.val i) (hφval p hp)).trans ?_
      apply ContinuousLinearMap.ext
      intro v
      change (s p.1).symm (p.2.val i (s p.1 v)) =
        (s p.1).symm (e.symmL ℂ p.1 (e.continuousLinearMapAt ℂ p.1
          (p.2.val i (e.symmL ℂ p.1 (e.continuousLinearMapAt ℂ p.1 (s p.1 v))))))
      rw [e.symmL_continuousLinearMapAt (hU hp), e.symmL_continuousLinearMapAt (hU hp)]
    exact hproj.continuousOn.prodMk
      (Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (continuousOn_pi.mpr hmodel))
  have hψcolumn (i : Fin r) : ContinuousOn
      (fun q : X × F ↦
        (⟨(ψ q).1, (ψ q).2.val i⟩ :
          TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)))
      ((U : Set X) ×ˢ Set.univ) := by
    have hA' : ContinuousOn (fun q : X × F ↦ A q.1) ((U : Set X) ×ˢ Set.univ) :=
      hA.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)
    have hB' : ContinuousOn (fun q : X × F ↦ B q.1) ((U : Set X) ×ˢ Set.univ) :=
      hB.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)
    have hQ : Continuous (fun q : X × F ↦ q.2.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
    have hmatrix : ContinuousOn
        (fun q : X × F ↦ (A q.1).comp ((q.2.val i).comp (B q.1)))
        ((U : Set X) ×ˢ Set.univ) := hA'.clm_comp (hQ.continuousOn.clm_comp hB')
    have hraw := t.toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_fst.continuousOn.prodMk hmatrix)
      (fun _ hq ↦ t.mem_target.mpr ⟨hU hq.1, hU hq.1⟩)
    apply hraw.congr
    intro q hq
    refine (congrArg (fun p : HermitianFlagBundle r E h ↦
      (⟨p.1, p.2.val i⟩ : TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)))
      (hψval q hq.1)).trans ?_
    have hcoords :
        t (⟨q.1, ((C q.1 hq.1).symm q.2).val i⟩ :
          TotalSpace (V →L[ℂ] V) (fun y ↦ E y →L[ℂ] E y)) =
            (q.1, (A q.1).comp ((q.2.val i).comp (B q.1))) := by
      apply Prod.ext
      · rfl
      · ext v
        rfl
    exact (t.left_inv (t.mem_source.mpr ⟨hU hq.1, hU hq.1⟩)).symm.trans
      (congrArg t.toOpenPartialHomeomorph.symm hcoords)
  have hψ : ContinuousOn ψ ((U : Set X) ×ˢ Set.univ) := by
    apply hι.continuousOn_iff.mpr
    have hbase : ContinuousOn (fun q : X × F ↦ (ψ q).1) ((U : Set X) ×ˢ Set.univ) := by
      apply continuousOn_fst.congr
      intro q hq
      exact congrArg (fun p : HermitianFlagBundle r E h ↦ p.1) (hψval q hq.1)
    exact hbase.prodMk (continuousOn_pi.mpr hψcolumn)
  let flagChart : Trivialization F (hermitianFlagProjection r E h) :=
    { toFun := φ
      invFun := ψ
      source := {p | p.1 ∈ U}
      target := (U : Set X) ×ˢ Set.univ
      map_source' := fun {_} hp ↦ ⟨hp, Set.mem_univ _⟩
      map_target' := by
        intro q hq
        rw [hψval q hq.1]
        exact hq.1
      left_inv' := by
        intro p hp
        rw [hφval p hp, hψval (p.1, C p.1 hp p.2) hp]
        exact congrArg (Sigma.mk p.1) ((C p.1 hp).symm_apply_apply p.2)
      right_inv' := by
        intro q hq
        rw [hψval q hq.1, hφval _ hq.1]
        exact Prod.ext rfl ((C q.1 hq.1).apply_symm_apply q.2)
      continuousOn_toFun := hφ
      continuousOn_invFun := hψ
      open_source := U.isOpen.preimage hproj
      open_target := U.isOpen.prod isOpen_univ
      baseSet := U
      open_baseSet := U.isOpen
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  exact ⟨flagChart, rfl, hφval, fun y Q hy ↦ hψval (y, Q) hy⟩

end AtiyahSinger.ComplexBundle
