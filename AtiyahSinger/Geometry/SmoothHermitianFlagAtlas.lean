/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.HermitianFlagIsometricCharts
public import AtiyahSinger.Geometry.SmoothFibrationAtlas
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Gluing the original smooth Hermitian flag charts

Public module ID: M1399.

Local isometries with smooth matrices in the original bundle atlas give smooth
changes of the actual flag trivializations. Smoothness is reflected through
the embedded standard projector space. The same matrices recover every
original projector column after the total-space atlas has been constructed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Set
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  (A : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    SmoothComplexBundleAtlas (n := n) E)

attribute [local instance] hermitianFlagTopology

set_option backward.isDefEq.respectTransparency.types false in
open Classical in
/-- Smooth local isometric frames glue to an atlas with the original smooth projector columns. -/
theorem exists_hermitianFlagAtlas_of_localFrames :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ {EF G : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [ChartedSpace EF (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
      InnerProductSpace.toCore)]
    [IsManifold 𝓘(ℝ, EF) ∞ (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
      InnerProductSpace.toCore)]
    (_hemb : Manifold.IsSmoothEmbedding 𝓘(ℝ, EF)
      𝓘(ℝ, Fin r → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      (fun Q : HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
        InnerProductSpace.toCore ↦ Q.val))
    {ι : Type*} (U : ι → TopologicalSpace.Opens M) (_hcover : ∀ x, ∃ k, x ∈ U k)
    (s : ι → ∀ y : M, EuclideanSpace ℂ (Fin r) ≃L[ℂ] E y)
    (hs : ∀ k y, y ∈ U k → ∀ u v, (h.toCore y).inner (s k y u) (s k y v) = inner ℂ u v)
    (t : ι → Trivialization
      (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
      (hermitianFlagProjection r E h : HermitianFlagBundle r E h → M))
    (_htBase : ∀ k, (t k).baseSet = U k)
    (_htForward : ∀ k (p : HermitianFlagBundle r E h) (hp : p.1 ∈ U k),
      t k p = (p.1, hermitianFlagEquivOfIsometry (h.toCore p.1) (s k p.1) (hs k p.1 hp) p.2))
    (_htInv : ∀ k y Q (hy : y ∈ U k),
      (t k).toPartialEquiv.symm (y, Q) =
        ⟨y, (hermitianFlagEquivOfIsometry (h.toCore y) (s k y) (hs k y hy)).symm Q⟩)
    (a : ∀ _k : ι, ∀ i : A.Index, M → EuclideanSpace ℂ (Fin r) →L[ℂ]
      EuclideanSpace ℂ (Fin (A.rank i)))
    (b : ∀ _k : ι, ∀ i : A.Index, M → EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
      EuclideanSpace ℂ (Fin r))
    (_ha : ∀ k i, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i))) ∞
      (a k i) ((U k : Set M) ∩ (A.chart i).baseSet))
    (_hb : ∀ k i, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      (b k i) ((U k : Set M) ∩ (A.chart i).baseSet))
    (_haApply : ∀ k i y (_hy : y ∈ U k) (hi : y ∈ (A.chart i).baseSet) (v : E y),
      a k i y ((s k y).symm v) = WithLp.toLp 2 (A.frameLinearEquiv i y hi v))
    (_hbApply : ∀ k i y (_hy : y ∈ U k) (hi : y ∈ (A.chart i).baseSet) (v : E y),
      b k i y (WithLp.toLp 2 (A.frameLinearEquiv i y hi v)) = (s k y).symm v)
    (_g : (EuclideanSpace ℝ (Fin n) × EF) ≃L[ℝ] G),
    ∃ C : ChartedSpace G (HermitianFlagBundle r E h), letI := C
      IsManifold 𝓘(ℝ, G) ∞ (HermitianFlagBundle r E h) ∧
      ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (hermitianFlagProjection r E h) ∧
      Manifold.IsSubmersion 𝓘(ℝ, G) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (hermitianFlagProjection r E h) ∧
      (∀ k, ContMDiffOn 𝓘(ℝ, G) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EF)) ∞
          (t k) (t k).source ∧
        ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EF)) 𝓘(ℝ, G) ∞
          (t k).toOpenPartialHomeomorph.symm (t k).target) ∧
      ∀ (i : A.Index) (j : Fin r) (k : Fin (A.rank i)),
        ContMDiffOn 𝓘(ℝ, G) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
          (fun p : HermitianFlagBundle r E h ↦
            if hp : p.1 ∈ (A.chart i).baseSet then
              A.frameLinearEquiv i p.1 hp
                (p.2.val j ((A.frameLinearEquiv i p.1 hp).symm (Pi.single k 1)))
            else 0) ((hermitianFlagProjection r E h) ⁻¹' (A.chart i).baseSet) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  intro EF G _ _ _ _ _ _ hemb ι U hcover s hs t htBase htForward htInv a b ha hb
    haApply hbApply g
  let V := EuclideanSpace ℂ (Fin r)
  let F := HermitianFlagSpace r V InnerProductSpace.toCore
  let X := HermitianFlagBundle r E h
  let IB := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let J := IB.prod 𝓘(ℝ, EF)
  have hcomp (d₁ d₂ d₃ : ℕ) : ContDiff ℝ ∞
      (fun z : (EuclideanSpace ℂ (Fin d₂) →L[ℂ] EuclideanSpace ℂ (Fin d₃)) ×
        (EuclideanSpace ℂ (Fin d₁) →L[ℂ] EuclideanSpace ℂ (Fin d₂)) ↦ z.1.comp z.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
  have happly (d₁ d₂ : ℕ) : ContDiff ℝ ∞
      (fun z : (EuclideanSpace ℂ (Fin d₁) →L[ℂ] EuclideanSpace ℂ (Fin d₂)) ×
        EuclideanSpace ℂ (Fin d₁) ↦ z.1 z.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
  have hsource (k : ι) (p : X) : p ∈ (t k).source ↔ p.1 ∈ U k := by
    rw [(t k).mem_source, htBase k]
    rfl
  have htarget (k : ι) (q : M × F) : q ∈ (t k).target ↔ q.1 ∈ U k := by
    rw [(t k).mem_target, htBase k]
    rfl
  have hchange (k l : ι) (i : A.Index) (y : M)
      (hk : y ∈ U k) (hl : y ∈ U l) (hi : y ∈ (A.chart i).baseSet) (v : V) :
      b l i y (a k i y v) = (s l y).symm (s k y v) := by
    have hc := haApply k i y hk hi (s k y v)
    rw [(s k y).symm_apply_apply] at hc
    rw [hc]
    exact hbApply l i y hl hi (s k y v)
  -- All transition matrices use the same local isometries and the same original A-frame.
  have htransition (k l : ι) : ContMDiffOn J J ∞
      ((t k).toOpenPartialHomeomorph.symm.trans (t l).toOpenPartialHomeomorph)
      ((t k).toOpenPartialHomeomorph.symm.trans (t l).toOpenPartialHomeomorph).source := by
    let T := (t k).toOpenPartialHomeomorph.symm.trans (t l).toOpenPartialHomeomorph
    intro q hq
    have hk : q.1 ∈ U k := (htarget k q).mp hq.1
    have hkl : (t k).toOpenPartialHomeomorph.symm q =
        ⟨q.1, (hermitianFlagEquivOfIsometry (h.toCore q.1) (s k q.1)
          (hs k q.1 hk)).symm q.2⟩ := htInv k q.1 q.2 hk
    have hl : q.1 ∈ U l := by
      have hq' := (hsource l _).mp hq.2
      change ((t k).toOpenPartialHomeomorph.symm q).1 ∈ U l at hq'
      rw [hkl] at hq'
      exact hq'
    obtain ⟨i, hi⟩ := A.covers q.1
    have hmat (k : ι) (hk : q.1 ∈ U k) :=
      ((U k).isOpen.inter (A.chart i).open_baseSet).mem_nhds ⟨hk, hi⟩
    have haK := (ha k i).contMDiffAt (hmat k hk)
    have haL := (ha l i).contMDiffAt (hmat l hl)
    have hbK := (hb k i).contMDiffAt (hmat k hk)
    have hbL := (hb l i).contMDiffAt (hmat l hl)
    have hL := ((hcomp r (A.rank i) r).contMDiff.contMDiffAt.comp q.1
      (hbL.prodMk_space haK)).comp q (contMDiffAt_fst (I := IB) (J := 𝓘(ℝ, EF)))
    have hR := ((hcomp r (A.rank i) r).contMDiff.contMDiffAt.comp q.1
      (hbK.prodMk_space haL)).comp q (contMDiffAt_fst (I := IB) (J := 𝓘(ℝ, EF)))
    have hQ := (hemb.contMDiff.comp (contMDiff_snd (I := IB))).contMDiffAt (x := q)
    have hconj : ContMDiffAt J 𝓘(ℝ, Fin r → V →L[ℂ] V) ∞
        (fun z : M × F ↦ fun j ↦ (b l i z.1).comp
          ((a k i z.1).comp ((z.2.val j).comp ((b k i z.1).comp (a l i z.1))))) q := by
      apply contMDiffAt_pi_space.mpr
      intro j
      have hQR := (hcomp r r r).contMDiff.contMDiffAt.comp q
        ((contMDiffAt_pi_space.mp hQ j).prodMk_space hR)
      exact (hcomp r r r).contMDiff.contMDiffAt.comp q (hL.prodMk_space hQR)
    have heq : (fun z : M × F ↦ (T z).2.val) =ᶠ[𝓝 q]
        (fun z : M × F ↦ fun j ↦ (b l i z.1).comp
          ((a k i z.1).comp ((z.2.val j).comp ((b k i z.1).comp (a l i z.1))))) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hmat k hk),
        continuous_fst.continuousAt.preimage_mem_nhds (hmat l hl)] with z hzK hzL
      change z.1 ∈ (U k : Set M) ∩ (A.chart i).baseSet at hzK
      change z.1 ∈ (U l : Set M) ∩ (A.chart i).baseSet at hzL
      have hzInv := htInv k z.1 z.2 hzK.1
      change (t k).toOpenPartialHomeomorph.symm z = _ at hzInv
      change (fun j ↦ ((t l) ((t k).toOpenPartialHomeomorph.symm z)).2.val j) = _
      rw [hzInv, htForward l _ hzL.1]
      funext j
      apply ContinuousLinearMap.ext
      intro v
      change (s l z.1).symm (s k z.1 (z.2.val j ((s k z.1).symm (s l z.1 v)))) =
        b l i z.1 (a k i z.1 (z.2.val j (b k i z.1 (a l i z.1 v))))
      rw [hchange l k i z.1 hzL.1 hzK.1 hzK.2,
        hchange k l i z.1 hzK.1 hzL.1 hzK.2]
    have hcont := T.continuousOn.continuousAt (T.open_source.mem_nhds hq)
    have hsecond : ContMDiffAt J 𝓘(ℝ, EF) ∞ (fun z : M × F ↦ (T z).2) q := by
      apply (ContMDiffAt.iff_comp_isImmersionAt (hemb.isImmersion.isImmersionAt _)).mpr
      exact ⟨hcont.snd, hconj.congr_of_eventuallyEq heq⟩
    have hfirst : ContMDiffAt J IB ∞ (fun z : M × F ↦ (T z).1) q := by
      apply contMDiffAt_fst.congr_of_eventuallyEq
      filter_upwards [T.open_source.mem_nhds hq] with z hz
      exact ((t l).coe_fst hz.2).trans ((t k).proj_symm_apply hz.1)
    exact (hfirst.prodMk hsecond).contMDiffWithinAt
  obtain ⟨C, hm, hp, hsub, htSmooth⟩ := exists_smoothFibrationAtlas
    (hermitianFlagProjection r E h) t (fun p ↦ by
      obtain ⟨k, hk⟩ := hcover p.1
      exact ⟨k, (hsource k p).mpr hk⟩) htransition g
  let := C
  let := hm
  refine ⟨C, hm, hp, hsub, htSmooth, ?_⟩
  -- The chosen product coordinates recover the actual projectors in every original frame.
  intro i j d p hpi
  obtain ⟨k, hk⟩ := hcover p.1
  have hpt : p ∈ (t k).source := (hsource k p).mpr hk
  have hneigh := ((U k).isOpen.inter (A.chart i).open_baseSet).mem_nhds ⟨hk, hpi⟩
  have haP := ((ha k i).contMDiffAt hneigh).comp p (hp p)
  have hbP := ((hb k i).contMDiffAt hneigh).comp p (hp p)
  have htP := (htSmooth k).1.contMDiffAt ((t k).open_source.mem_nhds hpt)
  have hQ := (hemb.contMDiff.contMDiffAt).comp p htP.snd
  let v : EuclideanSpace ℂ (Fin (A.rank i)) := WithLp.toLp 2 (Pi.single d 1)
  have hbV := (happly (A.rank i) r).contMDiff.contMDiffAt.comp p
    (hbP.prodMk_space (contMDiffAt_const (c := v)))
  have hQV := (happly r r).contMDiff.contMDiffAt.comp p
    ((contMDiffAt_pi_space.mp hQ j).prodMk_space hbV)
  have hvalue := (happly r (A.rank i)).contMDiff.contMDiffAt.comp p (haP.prodMk_space hQV)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (A.rank i) ↦ ℂ)
  have hcoords := (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff.contMDiffAt
    |>.comp p (show ContMDiffAt 𝓘(ℝ, G) 𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i))) ∞
      (fun z : X ↦ a k i z.1 ((t k z).2.val j (b k i z.1 v))) p from hvalue)
  apply ContMDiffAt.contMDiffWithinAt
  apply hcoords.congr_of_eventuallyEq
  filter_upwards [(hp.continuous.continuousAt).preimage_mem_nhds hneigh] with z hz
  change z.1 ∈ (U k : Set M) ∩ (A.chart i).baseSet at hz
  rw [dite_eq_left hz.2]
  change A.frameLinearEquiv i z.1 hz.2
      (z.2.val j ((A.frameLinearEquiv i z.1 hz.2).symm (Pi.single d 1))) =
    e (a k i z.1 ((t k z).2.val j (b k i z.1 v)))
  rw [htForward k z hz.1]
  let w : E z.1 := (A.frameLinearEquiv i z.1 hz.2).symm (Pi.single d 1)
  have hbW := hbApply k i z.1 hz.1 hz.2 w
  have hw : WithLp.toLp 2 (A.frameLinearEquiv i z.1 hz.2 w) = v := by
    rw [LinearEquiv.apply_symm_apply]
  rw [hw] at hbW
  change A.frameLinearEquiv i z.1 hz.2 (z.2.val j w) =
    e (a k i z.1 ((s k z.1).symm (z.2.val j (s k z.1 (b k i z.1 v)))))
  rw [hbW, (s k z.1).apply_symm_apply, haApply k i z.1 hz.1 hz.2]
  rfl

end AtiyahSinger.ComplexBundle
