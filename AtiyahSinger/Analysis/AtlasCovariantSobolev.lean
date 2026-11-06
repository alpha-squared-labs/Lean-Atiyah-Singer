/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasIntegerSobolevDerivatives
public import AtiyahSinger.Analysis.AtlasSobolev
public import AtiyahSinger.Analysis.CompactChartDensity
public import AtiyahSinger.Analysis.CovariantCoordinateTensors
public import AtiyahSinger.Analysis.CovariantJetEstimates
public import AtiyahSinger.Geometry.AtlasComplexConnection
public import AtiyahSinger.Geometry.AtlasCovariantFields
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.AtlasTensorMetricComparison
public import AtiyahSinger.Geometry.CotangentMetric
public import AtiyahSinger.Geometry.HermitianPairing
public import AtiyahSinger.Geometry.MultilinearContraction
public import AtiyahSinger.Geometry.TangentConnectionCoordinates
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Integer covariant norms for a varying-rank bundle

Public module ID: M0236.

A01: recursively construct the coordinate tensors of nabla^j u from the
section, its smooth bundle connection and the supplied smooth tangent
connection. Each new derivative includes the bundle connection and subtracts
the tangent Christoffel correction in every existing covariant slot. These
are full tensor derivatives, without exterior antisymmetrization or a
factorial factor.

Contraction with the cotangent and Hermitian metrics defines the squared
tensor length. Chart invariance makes its partition integral independent
of the finite presentation. On a compact base, a supplied smooth positive
measure and smooth Hermitian metric give comparison with the Fourier
Sobolev completion at every nonnegative integer order.

Sources: Spin Geometry III.2, (2.1) and Proposition 2.14, pp.170 and 176.
The tensor-connection recursion is the standard coordinate formula. Using
any supplied smooth tangent connection extends the Riemannian Levi-Civita
specialization; the comparison requires neither metric compatibility nor
vanishing torsion, and allows locally varying bundle rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The tangent connection coefficients in the actual coordinate vector fields of c.
This implementation expression uses the native tangent trivialization, not a global frame. -/
def atlasTangentChristoffel
    (covT : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (M := M) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (z : EuclideanSpace ℝ (Fin n)) (a b : Fin n) : EuclideanSpace ℝ (Fin n) :=
  let e := (tangentBundleCore 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M).localTriv ⟨c, hc⟩
  let Xb := fun x : M ↦ e.symmL ℝ x (EuclideanSpace.single b 1)
  e.continuousLinearMapAt ℝ (c.symm z)
    (covT Xb (c.symm z) (e.symmL ℝ (c.symm z) (EuclideanSpace.single a 1)))

variable {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {A : SmoothComplexBundleAtlas (n := n) E}

namespace AtlasComplexConnection

variable (cov : AtlasComplexConnection A)
  (covT : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (M := M) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
  (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
  (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index)

/-- The actual iterated tensor-connection components, recursively in the original frame.
The first index of the successor tensor is the newly added derivative direction. -/
def localIteratedCovariantDerivative (u : A.smoothSections) :
    (k : ℕ) → (Fin k → Fin n) → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin (A.rank i))
  | 0 => fun _ z ↦ atlasSectionInChart A c i u.val z
  | k + 1 => fun indices z ↦
      fderiv ℝ
          (localIteratedCovariantDerivative u k
            (fun a ↦ indices a.succ)) z
          (EuclideanSpace.single (indices 0) 1) +
        cov.connectionForm c i z (EuclideanSpace.single (indices 0) 1)
          (localIteratedCovariantDerivative u k
            (fun a ↦ indices a.succ) z) -
        ∑ a : Fin k, ∑ b : Fin n,
          ((atlasTangentChristoffel covT c hc z (indices 0) (indices a.succ) b : ℝ) : ℂ) •
            localIteratedCovariantDerivative u k
              (Function.update (fun j ↦ indices j.succ) a b) z

include hM in
/-- At first order the coordinate recursion is the already specified original connection. -/
theorem localIteratedCovariantDerivative_one (u : A.smoothSections)
    (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet) (a : Fin n) :
    (A.frameLinearEquiv i x hx.2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ)
          (cov.localIteratedCovariantDerivative covT c hc i u 1 (fun _ ↦ a) (c x))) =
      cov.covariantDerivative u x
        (((tangentBundleCore 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M).localTriv ⟨c, hc⟩).symmL
           ℝ x (EuclideanSpace.single a 1)) := by
  /- Stage 1: at order zero the recursive coordinate function is the original
  section coordinate. At order one the sum over existing covariant slots is
  empty, leaving its ordinary derivative plus the supplied connection form.
  Stage 2: the native tangent frame of c is the inverse of its actual chart
  derivative at x. The chosen coordinate direction therefore maps to the
  same basis vector. Apply covariantDerivative_eq and the frame inverse law.
  This anchors the recursion to the original first derivative on E x. -/
  let e := (tangentBundleCore 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M).localTriv ⟨c, hc⟩
  let v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x :=
    e.symmL ℝ x (EuclideanSpace.single a 1)
  -- The tangent trivialization is the derivative of the same original base chart.
  have hderiv : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x = e.continuousLinearMapAt ℝ x := by
    rw [(tangentBundleCore 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M).localTriv_continuousLinearMapAt
      (show x ∈ e.baseSet from hx.1)]
    rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas hc hx.1)]
    rfl
  have ht : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c x v = EuclideanSpace.single a 1 := by
    rw [hderiv]
    exact e.continuousLinearMapAt_symmL hx.1 _
  -- At order one the old-slot correction is empty, leaving the original connection formula.
  have hcov := cov.covariantDerivative_eq u c hc i x hx v
  simpa only [atlasConnectionExpression, ht, localIteratedCovariantDerivative,
    Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using hcov.symm

section LocalSmoothness

variable [T2Space M]

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace MI (M := M)
local notation "𝓧" => ContMDiffSection MI H ∞ TM

set_option backward.isDefEq.respectTransparency false in
/-- Every original iterated covariant derivative array is smooth on its valid chart domain. -/
theorem localIteratedCovariantDerivative_contDiffAt
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (u : A.smoothSections) (k : ℕ) (p : Fin k → Fin n) (z : H)
    (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
    ContDiffAt ℝ ∞ (cov.localIteratedCovariantDerivative covT c hc i u k p) z := by
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
  let : MemTrivializationAtlas t := ⟨⟨⟨c, hc⟩, rfl⟩⟩
  have hsymm (w : H) (hw : w ∈ c.target) : ContMDiffAt MI MI ∞ c.symm w :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hw
  have hdomain (w : H) (hw : w ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
      c.target ∩ c.symm ⁻¹' (A.chart i).baseSet ∈ nhds w := by
    apply Filter.inter_mem (c.open_target.mem_nhds hw.1)
    exact (hsymm w hw.1).continuousAt.preimage_mem_nhds
      ((A.chart i).open_baseSet.mem_nhds hw.2)
  have hchristoffel (a b d : Fin n) (w : H) (hw : w ∈ c.target) :
      ContDiffAt ℝ ∞ (fun y ↦ atlasTangentChristoffel covT c hc y a b d) w := by
    have hlocal := contMDiffAt_tangentCovariantDerivative_coord covT hcovT t
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) (c.symm w)
      (c.map_target hw)
    have hcolumn := (EuclideanSpace.proj d).contMDiff.contMDiffAt.comp (c.symm w) hlocal
    exact contMDiffAt_iff_contDiffAt.mp (hcolumn.comp w (hsymm w hw))
  induction k generalizing z with
  | zero =>
    let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
    have hcoord := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.contMDiffAt.comp
      (c.symm z) ((u.property i).contMDiffAt ((A.chart i).open_baseSet.mem_nhds hz.2))
    exact contMDiffAt_iff_contDiffAt.mp (hcoord.comp z (hsymm z hz.1))
  | succ k ih =>
    have hold := ih (fun a ↦ p a.succ) z hz
    have hderiv := (hold.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := EuclideanSpace.single (p 0) 1))
    have hΓ := (cov.smooth_connectionForm c hc i).contDiffAt (hdomain z hz)
    let restrict := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
    have hvalue := (restrict.contDiff.contDiffAt.comp z
      (hΓ.clm_apply (contDiffAt_const (c := EuclideanSpace.single (p 0) 1)))).clm_apply hold
    have hsum : ContDiffAt ℝ ∞ (fun y ↦ ∑ a : Fin k, ∑ b : Fin n,
        ((atlasTangentChristoffel covT c hc y (p 0) (p a.succ) b : ℝ) : ℂ) •
          cov.localIteratedCovariantDerivative covT c hc i u k
            (Function.update (fun j ↦ p j.succ) a b) y) z := by
      apply ContDiffAt.sum
      intro a _
      apply ContDiffAt.sum
      intro b _
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z
        (hchristoffel (p 0) (p a.succ) b z hz.1)).smul
          (ih (Function.update (fun j ↦ p j.succ) a b) z hz)
    exact (hderiv.add hvalue).sub hsum


set_option backward.isDefEq.respectTransparency false in
/-- Reconstructing the original successor array gives the full coordinate tensor derivative. -/
theorem tensorFromComponents_localIteratedCovariantDerivative_succ
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (u : A.smoothSections) (k : ℕ) (z : H)
    (hz : z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
    let V := EuclideanSpace ℂ (Fin (A.rank i))
    let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
    let F := fun w ↦ tensorFromComponents n k V
      (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p w)
    let ΓT : H →L[ℝ] H →L[ℝ] H := ∑ b : Fin n,
      (ContinuousLinearMap.smulRightL ℝ H H (EuclideanSpace.proj b)).comp
        ((t.continuousLinearMapAt ℝ (c.symm z)).comp
          ((covT (fun y ↦ t.symmL ℝ y (EuclideanSpace.single b 1)) (c.symm z)).comp
            (t.symmL ℝ (c.symm z))))
    tensorFromComponents n (k + 1) V
        (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u (k + 1) p z) =
      tensorConnectionDerivative n k V (F z) (fderiv ℝ F z)
        ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).comp (cov.connectionForm c i z))
        ΓT := by
  classical
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
  let F := fun w ↦ tensorFromComponents n k V
    (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p w)
  let ΓT : H →L[ℝ] H →L[ℝ] H := ∑ b : Fin n,
    (ContinuousLinearMap.smulRightL ℝ H H (EuclideanSpace.proj b)).comp
      ((t.continuousLinearMapAt ℝ (c.symm z)).comp
        ((covT (fun y ↦ t.symmL ℝ y (EuclideanSpace.single b 1)) (c.symm z)).comp
          (t.symmL ℝ (c.symm z))))
  have hΓT (a b : Fin n) : ΓT (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) =
      atlasTangentChristoffel covT c hc z a b := by
    simp [ΓT, atlasTangentChristoffel, t]
    rfl
  have hF : DifferentiableAt ℝ F z := by
    have harray : ContDiffAt ℝ ∞
        (fun w p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p w) z :=
      contDiffAt_pi.mpr (fun p ↦
        cov.localIteratedCovariantDerivative_contDiffAt covT hcovT c hc i u k p z hz)
    exact ((tensorFromComponents n k V).contDiff.contDiffAt.comp z harray).differentiableAt
      (by simp)
  -- Equality on ordered coordinate bases determines the whole multilinear tensor.
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin (k + 1) ↦ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
  intro p
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change tensorFromComponents n (k + 1) V
      (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u (k + 1) p z)
      (fun a ↦ EuclideanSpace.single (p a) 1) =
    tensorConnectionDerivative n k V (F z) (fderiv ℝ F z)
      ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).comp (cov.connectionForm c i z))
      ΓT (fun a ↦ EuclideanSpace.single (p a) 1)
  rw [tensorFromComponents_basis, tensorConnectionDerivative_apply]
  let Y : Fin k → H := fun a ↦ EuclideanSpace.single (p a.succ) 1
  have hFY : F z Y = cov.localIteratedCovariantDerivative covT c hc i u k
      (fun a ↦ p a.succ) z := tensorFromComponents_basis n k V _ _
  -- Differentiation commutes with evaluation on these fixed original basis vectors.
  have hdY : fderiv ℝ F z (EuclideanSpace.single (p 0) 1) Y =
      fderiv ℝ (cov.localIteratedCovariantDerivative covT c hc i u k
        (fun a ↦ p a.succ)) z (EuclideanSpace.single (p 0) 1) := by
    let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ H) V Y
    have heq : (fun w ↦ ev (F w)) =
        cov.localIteratedCovariantDerivative covT c hc i u k (fun a ↦ p a.succ) := by
      funext w
      exact tensorFromComponents_basis n k V _ _
    have hd := (ev.hasFDerivAt.comp z hF.hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [heq] at hd
    exact (congrArg (fun T ↦ T (EuclideanSpace.single (p 0) 1)) hd).symm
  have hslot (a : Fin k) :
      F z (Function.update Y a (ΓT (EuclideanSpace.single (p 0) 1) (Y a))) =
        ∑ b : Fin n, (atlasTangentChristoffel covT c hc z (p 0) (p a.succ) b : ℝ) •
          cov.localIteratedCovariantDerivative covT c hc i u k
            (Function.update (fun j ↦ p j.succ) a b) z := by
    change F z (Function.update Y a
      (ΓT (EuclideanSpace.single (p 0) 1) (EuclideanSpace.single (p a.succ) 1))) = _
    rw [hΓT]
    let w := atlasTangentChristoffel covT c hc z (p 0) (p a.succ)
    have hw : w = ∑ b : Fin n, w b • EuclideanSpace.single b 1 := by
      simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w).symm
    change (F z).toMultilinearMap (Function.update Y a w) = _
    rw [hw, (F z).toMultilinearMap.map_update_sum]
    change (∑ b : Fin n, F z (Function.update Y a (w b • EuclideanSpace.single b 1))) = _
    simp only [(F z).map_update_smul]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    have hupdate : Function.update Y a (EuclideanSpace.single b 1) =
        fun j ↦ EuclideanSpace.single ((Function.update (fun l ↦ p l.succ) a b) j) 1 := by
      funext j
      by_cases h : j = a
      · subst j
        simp
      · simp [Function.update_of_ne h, Y]
    rw [hupdate]
    exact tensorFromComponents_basis n k V _ _
  change cov.localIteratedCovariantDerivative covT c hc i u (k + 1) p z =
    fderiv ℝ F z (EuclideanSpace.single (p 0) 1) Y +
      cov.connectionForm c i z (EuclideanSpace.single (p 0) 1) (F z Y) -
        ∑ a : Fin k, F z (Function.update Y a
          (ΓT (EuclideanSpace.single (p 0) 1) (Y a)))
  rw [hdY, hFY]
  simp only [localIteratedCovariantDerivative, hslot, Complex.coe_smul]


set_option backward.isDefEq.respectTransparency false in
/-- Original arrays evaluated on smooth fields equal the intrinsic full covariant derivative. -/
theorem tensorFromComponents_eq_iteratedDirectionalDerivative
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (u : A.smoothSections) (k : ℕ) (X : Fin k → 𝓧) (x : M)
    (hx : x ∈ c.source ∩ (A.chart i).baseSet) :
    let V := EuclideanSpace ℂ (Fin (A.rank i))
    let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
    tensorFromComponents n k V
        (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p (c x))
        (fun a ↦ t.continuousLinearMapAt ℝ x (X a x)) =
      (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
        (A.frameLinearEquiv i x hx.2
          ((cov.iteratedDirectionalDerivative covT hcovT u k X).val x)) := by
  classical
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
  let : MemTrivializationAtlas t := ⟨⟨⟨c, hc⟩, rfl⟩⟩
  let q (σ : 𝓧) (z : H) : H :=
    t.continuousLinearMapAt ℝ (c.symm z) (σ (c.symm z))
  have hcoord (σ : 𝓧) (y : M) (hy : y ∈ c.source) :
      ContMDiffAt MI MI ∞ (fun z ↦ t.continuousLinearMapAt ℝ z (σ z)) y := by
    apply ((t.contMDiffAt_section_iff hy).mp σ.contMDiff.contMDiffAt).congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    exact t.continuousLinearMapAt_apply_of_mem ℝ hz _
  have hq (σ : 𝓧) (y : M) (hy : y ∈ c.source) :
      ContDiffAt ℝ ∞ (q σ) (c y) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hcoord σ y hy).comp_of_eq
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc)
        (c.map_source hy)) (c.left_inv hy)
  have hderiv (y : M) (hy : y ∈ c.source) :
      mfderiv MI MI c y = t.continuousLinearMapAt ℝ y := by
    rw [(tangentBundleCore MI M).localTriv_continuousLinearMapAt
      (show y ∈ t.baseSet from hy)]
    rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas hc hy)]
    rfl
  -- In the same chart, the tangent connection adds its original frame coefficients.
  have htangent (σ : 𝓧) (y : M) (hy : y ∈ c.source) (v : TM y) :
      t.continuousLinearMapAt ℝ y (covT σ y v) =
        fderiv ℝ (q σ) (c y) (t.continuousLinearMapAt ℝ y v) +
          ∑ b : Fin n, (t.continuousLinearMapAt ℝ y (σ y)) b •
            t.continuousLinearMapAt ℝ y
              (covT (fun z ↦ t.symmL ℝ z (EuclideanSpace.single b 1)) y v) := by
    rw [tangentCovariantDerivative_coord_apply covT t σ y hy
      (σ.contMDiff.mdifferentiableAt (by simp)) v]
    congr 1
    have hchart := mdifferentiable_of_mem_atlas (I := MI) hc
    have hchain := mvfderiv_comp (I := MI) (I' := MI) (c y)
      (by simpa only [c.left_inv hy] using
        (hcoord σ y hy).mdifferentiableAt (by simp))
      (hchart.mdifferentiableAt_symm (c.map_source hy))
    have hlocal : fderiv ℝ (q σ) (c y) =
        (mvfderiv MI (fun z ↦ t.continuousLinearMapAt ℝ z (σ z)) y).comp
          (mfderiv MI MI c.symm (c y)) := by
      rw [mvfderiv_eq_fderiv, c.left_inv hy] at hchain
      exact hchain
    rw [hlocal, ← hderiv y hy]
    change _ = (mvfderiv MI (fun z ↦ t.continuousLinearMapAt ℝ z (σ z)) y)
      (((mfderiv MI MI c.symm (c y)).comp (mfderiv MI MI c y)) v)
    rw [hchart.symm_comp_deriv hy]
    rfl
  -- Induction evaluates the full tensor, so each varying field contributes one old-slot term.
  induction k generalizing x with
  | zero =>
    simp only [tensorFromComponents_apply, localIteratedCovariantDerivative,
      iteratedDirectionalDerivative, atlasSectionInChart]
    rw [c.left_inv hx.1]
    simp
    rfl
  | succ k ih =>
    let F (z : H) := tensorFromComponents n k V
      (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p z)
    let Y (a : Fin k) : H → H := q (X a.succ)
    let v : H := t.continuousLinearMapAt ℝ x (X 0 x)
    let ΓT : H →L[ℝ] H →L[ℝ] H := ∑ b : Fin n,
      (ContinuousLinearMap.smulRightL ℝ H H (EuclideanSpace.proj b)).comp
        ((t.continuousLinearMapAt ℝ x).comp
          ((covT (fun y ↦ t.symmL ℝ y (EuclideanSpace.single b 1)) x).comp (t.symmL ℝ x)))
    let s := cov.iteratedDirectionalDerivative covT hcovT u k (Fin.tail X)
    let C : E x →ₗ[ℝ] V := (e.symm.toLinearEquiv.toLinearMap.restrictScalars ℝ).comp
      ((A.frameLinearEquiv i x hx.2).toLinearMap.restrictScalars ℝ)
    have hz : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet := by
      exact ⟨c.map_source hx.1, by simpa only [Set.mem_preimage, c.left_inv hx.1] using hx.2⟩
    have hF : DifferentiableAt ℝ F (c x) := by
      have harray : ContDiffAt ℝ ∞
          (fun z p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p z) (c x) :=
        contDiffAt_pi.mpr (fun p ↦
          cov.localIteratedCovariantDerivative_contDiffAt covT hcovT c hc i u k p (c x) hz)
      exact ((tensorFromComponents n k V).contDiff.contDiffAt.comp (c x)
        harray).differentiableAt (by simp)
    have hY (a : Fin k) : DifferentiableAt ℝ (Y a) (c x) :=
      (hq (X a.succ) x hx.1).differentiableAt (by simp)
    -- The induction identity holds on a neighborhood, so its two sides may be differentiated.
    have heval : (fun z ↦ F z (fun a ↦ Y a z)) =ᶠ[nhds (c x)]
        atlasSectionInChart A c i s.val := by
      have hsymm := (contMDiffAt_symm_of_mem_maximalAtlas (I := MI) (n := ∞)
        (IsManifold.subset_maximalAtlas hc) (c.map_source hx.1)).continuousAt
      have hframe : c.symm ⁻¹' (A.chart i).baseSet ∈ nhds (c x) := by
        apply hsymm.preimage_mem_nhds
        rw [c.left_inv hx.1]
        exact (A.chart i).open_baseSet.mem_nhds hx.2
      filter_upwards [c.open_target.mem_nhds (c.map_source hx.1), hframe] with z hzc hzi
      have h := ih (Fin.tail X) (c.symm z) ⟨c.map_target hzc, hzi⟩
      change F (c (c.symm z)) (fun a ↦ Y a z) = atlasSectionInChart A c i s.val z at h
      rw [c.right_inv hzc] at h
      exact h
    have hd := (hF.hasFDerivAt.continuousMultilinearMap_apply
      (fun a ↦ (hY a).hasFDerivAt)).fderiv
    have hdf : fderiv ℝ (atlasSectionInChart A c i s.val) (c x) v =
        fderiv ℝ F (c x) v (fun a ↦ Y a (c x)) +
          ∑ a : Fin k, F (c x)
            (Function.update (fun b ↦ Y b (c x)) a (fderiv ℝ (Y a) (c x) v)) := by
      rw [← heval.fderiv_eq, hd]
      simp only [add_apply, sum_apply]
      rfl
    have hvalue : C (s.val x) = F (c x) (fun a ↦ Y a (c x)) := by
      dsimp only [Y, q]
      rw [c.left_inv hx.1]
      exact (ih (Fin.tail X) x hx).symm
    have hconnection : C (cov.covariantDerivative s x (X 0 x)) =
        fderiv ℝ (atlasSectionInChart A c i s.val) (c x) v +
          cov.connectionForm c i (c x) v (C (s.val x)) := by
      rw [cov.covariantDerivative_eq s c hc i x hx (X 0 x)]
      change e.symm (A.frameLinearEquiv i x hx.2
        ((A.frameLinearEquiv i x hx.2).symm
          (e (fderiv ℝ (atlasSectionInChart A c i s.val) (c x)
            (mfderiv MI MI c x (X 0 x)) +
            cov.connectionForm c i (c x) (mfderiv MI MI c x (X 0 x))
              (atlasSectionInChart A c i s.val (c x)))))) = _
      rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
        hderiv x hx.1]
      simp only [atlasSectionInChart]
      rw [c.left_inv hx.1]
      rfl
    -- Each corrected field contributes its ordinary derivative and tangent-connection action.
    have hslot (a : Fin k) :
        C ((cov.iteratedDirectionalDerivative covT hcovT u k
          (Function.update (Fin.tail X) a
            (smoothTangentCovariantDerivative covT hcovT (X 0) (X a.succ)))).val x) =
        F (c x) (Function.update (fun b ↦ Y b (c x)) a
          (fderiv ℝ (Y a) (c x) v + ΓT v (Y a (c x)))) := by
      have hi := (ih (Function.update (Fin.tail X) a
        (smoothTangentCovariantDerivative covT hcovT (X 0) (X a.succ))) x hx).symm
      change C _ = F (c x) _ at hi
      refine hi.trans ?_
      congr 1
      have hcova : t.continuousLinearMapAt ℝ x (covT (X a.succ) x (X 0 x)) =
          fderiv ℝ (Y a) (c x) v + ΓT v (Y a (c x)) := by
        rw [htangent (X a.succ) x hx.1 (X 0 x)]
        congr 1
        dsimp only [ΓT, Y, q, v]
        rw [c.left_inv hx.1]
        simp only [sum_apply, ContinuousLinearMap.comp_apply]
        change (∑ b : Fin n, (t.continuousLinearMapAt ℝ x (X a.succ x)) b •
          t.continuousLinearMapAt ℝ x
            (covT (fun z ↦ t.symmL ℝ z (EuclideanSpace.single b 1)) x (X 0 x))) =
          ∑ b : Fin n, (t.continuousLinearMapAt ℝ x (X a.succ x)) b •
            t.continuousLinearMapAt ℝ x
              (covT (fun z ↦ t.symmL ℝ z (EuclideanSpace.single b 1)) x
                (t.symmL ℝ x (t.continuousLinearMapAt ℝ x (X 0 x))))
        rw [t.symmL_continuousLinearMapAt hx.1]
      funext b
      by_cases hb : b = a
      · subst b
        simp only [Function.update_self]
        exact hcova
      · simp only [Function.update_of_ne hb, Fin.tail_def, Y, q]
        rw [c.left_inv hx.1]
    have hrec := congrArg
      (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ H) V ↦
        T (fun a ↦ t.continuousLinearMapAt ℝ x (X a x)))
      (cov.tensorFromComponents_localIteratedCovariantDerivative_succ covT hcovT
        c hc i u k (c x) hz)
    have hrec' : tensorFromComponents n (k + 1) V
        (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u (k + 1) p (c x))
        (fun a ↦ t.continuousLinearMapAt ℝ x (X a x)) =
        fderiv ℝ F (c x) v (fun a ↦ Y a (c x)) +
          cov.connectionForm c i (c x) v (F (c x) (fun a ↦ Y a (c x))) -
          ∑ a : Fin k, F (c x) (Function.update (fun b ↦ Y b (c x)) a
            (ΓT v (Y a (c x)))) := by
      dsimp only at hrec
      rw [c.left_inv hx.1] at hrec
      change _ = tensorConnectionDerivative n k V (F (c x)) (fderiv ℝ F (c x))
        ((ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).comp
          (cov.connectionForm c i (c x))) ΓT
        (fun a ↦ t.continuousLinearMapAt ℝ x (X a x)) at hrec
      rw [tensorConnectionDerivative_apply] at hrec
      dsimp only [Y, q]
      rw [c.left_inv hx.1]
      exact hrec
    change tensorFromComponents n (k + 1) V
      (fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u (k + 1) p (c x))
      (fun a ↦ t.continuousLinearMapAt ℝ x (X a x)) = C _
    rw [hrec']
    change _ = C ((cov.directionalDerivative s (X 0) -
      ∑ a : Fin k, cov.iteratedDirectionalDerivative covT hcovT u k
        (Function.update (Fin.tail X) a
          (smoothTangentCovariantDerivative covT hcovT (X 0) (X a.succ)))).val x)
    simp only [Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply,
      map_sub, map_sum, directionalDerivative]
    rw [hconnection, hvalue, hdf]
    -- The ordinary field derivatives cancel, leaving exactly the full tensor recursion.
    simp only [hslot, (F (c x)).map_update_add, Finset.sum_add_distrib]
    abel


end LocalSmoothness

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace MI (M := M)
local notation "𝓧" => ContMDiffSection MI H ∞ TM

open Classical in
/-- The squared length of the recursively constructed tensor on a valid original chart.
The double sum is the full tensor contraction; zero is used only off its chart domain. -/
def localCovariantDerivativeNormSq
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : ComplexBundle.ContinuousHermitianMetric E)
    (k : ℕ) (u : A.smoothSections) (x : M) : ℝ :=
  if hx : x ∈ c.source ∩ (A.chart i).baseSet then
    let values := fun indices : Fin k → Fin n ↦
      (A.frameLinearEquiv i x hx.2).symm
        ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ)
          (cov.localIteratedCovariantDerivative covT c hc i u k indices (c x)))
    ∑ indices : Fin k → Fin n, ∑ indices' : Fin k → Fin n,
      (∏ a : Fin k, g.inner x
        (covectorFromChart c x (EuclideanSpace.single (indices a) 1))
        (covectorFromChart c x (EuclideanSpace.single (indices' a) 1))) *
        ((h.toCore x).inner (values indices) (values indices')).re
  else 0

variable [hT : T2Space M] [hSC : SecondCountableTopology M]
  (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)


set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
include hM hT hSC hcovT in
/-- The full tensor contraction has the same value in any two valid original chart pairs. -/
theorem localCovariantDerivativeNormSq_eq
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : ComplexBundle.ContinuousHermitianMetric E)
    (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (j : A.Index)
    (k : ℕ) (u : A.smoothSections) (x : M)
    (hx : x ∈ c.source ∩ (A.chart i).baseSet)
    (hy : x ∈ d.source ∩ (A.chart j).baseSet) :
    cov.localCovariantDerivativeNormSq covT c hc i g h k u x =
      cov.localCovariantDerivativeNormSq covT d hd j g h k u x := by
  /- Reconstruct the full covariant tensor at x in both original chart pairs.
  Their evaluations on all smooth tangent fields agree with the intrinsic
  iterated derivative. Bump-supported fields realize arbitrary vectors at x,
  so the two tensors coincide. The original chart covectors are the duals of
  the corresponding tangent bases; full contraction is basis-independent.
  Only the given pointwise Hermitian form is used, with no smoothness or
  compactness added to the original hypotheses. -/
  classical
  let triv (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M) :
      Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨f, hf⟩
  let B (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M) (hxf : x ∈ f.source) :
      Module.Basis (Fin n) ℝ (TM x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
      ((triv f hf).continuousLinearEquivAt ℝ x hxf).symm.toLinearEquiv
  let R (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M) (l : A.Index)
      (hxl : x ∈ f.source ∩ (A.chart l).baseSet) :
      MultilinearMap ℝ (fun _ : Fin k ↦ TM x) (E x) :=
    (((A.frameLinearEquiv l x hxl.2).symm.toLinearMap.restrictScalars ℝ).comp
      ((EuclideanSpace.equiv (Fin (A.rank l)) ℂ).toLinearEquiv.toLinearMap.restrictScalars ℝ))
      |>.compMultilinearMap
        ((tensorFromComponents n k (EuclideanSpace ℂ (Fin (A.rank l)))
          (fun p ↦ cov.localIteratedCovariantDerivative covT f hf l u k p (f x)))
          |>.toMultilinearMap.compLinearMap
            (fun _ ↦ ((triv f hf).continuousLinearMapAt ℝ x).toLinearMap))
  have hfieldEval (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M) (l : A.Index)
      (hxl : x ∈ f.source ∩ (A.chart l).baseSet) (X : Fin k → 𝓧) :
      R f hf l hxl (fun a ↦ X a x) =
        (cov.iteratedDirectionalDerivative covT hcovT u k X).val x := by
    have heq := cov.tensorFromComponents_eq_iteratedDirectionalDerivative covT hcovT
      f hf l u k X x hxl
    change (A.frameLinearEquiv l x hxl.2).symm
      ((EuclideanSpace.equiv (Fin (A.rank l)) ℂ)
        (tensorFromComponents n k (EuclideanSpace ℂ (Fin (A.rank l)))
          (fun p ↦ cov.localIteratedCovariantDerivative covT f hf l u k p (f x))
          (fun a ↦ (triv f hf).continuousLinearMapAt ℝ x (X a x)))) = _
    rw [heq, ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  -- A bump-supported local frame realizes every prescribed tangent vector at this point.
  have hextend (v : TM x) : ∃ X : 𝓧, X x = v := by
    let t := triv c hc
    let : MemTrivializationAtlas t := ⟨⟨⟨c, hc⟩, rfl⟩⟩
    obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := MI) x).mem_iff.mp
      (c.open_source.mem_nhds hx.1)
    let w := t.continuousLinearMapAt ℝ x v
    let σ (y : M) : TM y := t.symmL ℝ y w
    have hσ : ContMDiffOn MI (MI).tangent ∞
        (fun y ↦ (⟨y, σ y⟩ : TangentBundle MI M)) c.source := by
      intro y hyc
      apply ContMDiffAt.contMDiffWithinAt
      apply (t.contMDiffAt_section_iff hyc).mpr
      apply (contMDiffAt_const (c := w)).congr_of_eventuallyEq
      filter_upwards [c.open_source.mem_nhds hyc] with z hzc
      change (t ⟨z, t.symmL ℝ z w⟩).2 = w
      rw [t.symmL_apply hzc, t.apply_mk_symm hzc]
    let X : 𝓧 := {
      toFun := fun y ↦ (χ : M → ℝ) y • σ y
      contMDiff_toFun := ContMDiffOn.smul_section_of_tsupport χ.contMDiff.contMDiffOn
        c.open_source hχ hσ }
    refine ⟨X, ?_⟩
    change (χ : M → ℝ) x • t.symmL ℝ x (t.continuousLinearMapAt ℝ x v) = v
    rw [χ.eq_one, one_smul, t.symmL_continuousLinearMapAt hx.1]
  have hR : R c hc i hx = R d hd j hy := by
    apply MultilinearMap.ext
    intro v
    choose X hX using fun a : Fin k ↦ hextend (v a)
    have hv : (fun a ↦ X a x) = v := funext hX
    rw [← hv, hfieldEval c hc i hx X, hfieldEval d hd j hy X]
  -- The chart basis and its actual dual are exactly the original vectors and covectors.
  have hB (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M)
      (hxf : x ∈ f.source) (a : Fin n) :
      B f hf hxf a = (triv f hf).symmL ℝ x (EuclideanSpace.single a 1) := by
    simp only [B, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply]
    exact congrFun ((triv f hf).symm_continuousLinearEquivAt_eq hxf) _
  have hdual (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M)
      (hxf : x ∈ f.source) (a : Fin n) :
      ((B f hf hxf).coord a).toContinuousLinearMap =
        covectorFromChart f x (EuclideanSpace.single a 1) := by
    suffices hh : (((B f hf hxf).coord a).toContinuousLinearMap).toLinearMap =
        (covectorFromChart f x (EuclideanSpace.single a 1)).toLinearMap by
      exact DFunLike.ext _ _ (fun v ↦ LinearMap.congr_fun hh v)
    apply (B f hf hxf).ext
    intro b
    change (B f hf hxf).coord a (B f hf hxf b) =
      inner ℝ (EuclideanSpace.single a 1) (mfderiv MI MI f x (B f hf hxf b))
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, hB]
    have hfderiv : mfderiv MI MI f x = (triv f hf).continuousLinearMapAt ℝ x := by
      rw [(tangentBundleCore MI M).localTriv_continuousLinearMapAt
        (show x ∈ (triv f hf).baseSet from hxf)]
      rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas hf hxf)]
      rfl
    rw [hfderiv]
    change (if b = a then (1 : ℝ) else 0) = inner ℝ (EuclideanSpace.single a 1)
      ((triv f hf).continuousLinearMapAt ℝ x
        ((triv f hf).symmL ℝ x (EuclideanSpace.single b 1)))
    rw [(triv f hf).continuousLinearMapAt_symmL hxf]
    simp [EuclideanSpace.inner_single_left, eq_comm]
  have hRB (f : OpenPartialHomeomorph M H) (hf : f ∈ atlas H M) (l : A.Index)
      (hxl : x ∈ f.source ∩ (A.chart l).baseSet) (p : Fin k → Fin n) :
      R f hf l hxl (fun a ↦ B f hf hxl.1 (p a)) =
        (A.frameLinearEquiv l x hxl.2).symm
          ((EuclideanSpace.equiv (Fin (A.rank l)) ℂ)
            (cov.localIteratedCovariantDerivative covT f hf l u k p (f x))) := by
    change (A.frameLinearEquiv l x hxl.2).symm
      ((EuclideanSpace.equiv (Fin (A.rank l)) ℂ)
        (tensorFromComponents n k (EuclideanSpace ℂ (Fin (A.rank l)))
          (fun q ↦ cov.localIteratedCovariantDerivative covT f hf l u k q (f x))
          (fun a ↦ (triv f hf).continuousLinearMapAt ℝ x (B f hf hxl.1 (p a))))) = _
    simp only [hB, (triv f hf).continuousLinearMapAt_symmL hxl.1,
      tensorFromComponents_basis]
  -- The two fixed original metrics supply algebraic real bilinear forms at this point.
  let G : LinearMap.BilinForm ℝ (Module.Dual ℝ (TM x)) :=
    LinearMap.mk₂ ℝ (fun a b ↦ g.inner x a.toContinuousLinearMap b.toContinuousLinearMap)
      (by intros; simp only [map_add, add_apply])
      (by intros; simp only [map_smul, smul_apply, smul_eq_mul])
      (by intros; simp only [map_add])
      (by intros; simp only [map_smul, smul_eq_mul])
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  let Hform : LinearMap.BilinForm ℝ (E x) :=
    LinearMap.mk₂ ℝ (fun v w ↦ ((h.toCore x).inner v w).re)
      (by intros; rw [(h.toCore x).add_left, Complex.add_re])
      (by
        intro a v w
        change ((h.toCore x).inner ((a : ℂ) • v) w).re =
          a * ((h.toCore x).inner v w).re
        rw [(h.toCore x).smul_left]
        simp)
      (by
        intro v w z
        simpa only [Complex.add_re] using congrArg Complex.re
          (InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) v w z))
      (by
        intro a v w
        change ((h.toCore x).inner v ((a : ℂ) • w)).re =
          a * ((h.toCore x).inner v w).re
        have hs := InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) v w (r := (a : ℂ))
        simpa using congrArg Complex.re hs)
  have hinvariant := sum_multilinear_pairing_basis_eq (B c hc hx.1) (B d hd hy.1)
    G Hform k (R c hc i hx) (R c hc i hx)
  conv_rhs at hinvariant => rw [hR]
  simp only [G, Hform, LinearMap.mk₂_apply, hdual, hRB] at hinvariant
  simpa only [localCovariantDerivativeNormSq, dite_eq_left hx, dite_eq_left hy] using hinvariant


end AtlasComplexConnection

section CompactCovariantEstimates

open Filter

private def arrayDerivativeEquiv (n k : ℕ) (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] ((Fin k → Fin n) → V)) ≃L[ℝ]
      ((Fin (k + 1) → Fin n) → V) := by
  classical
  let e : (EuclideanSpace ℝ (Fin n) →L[ℝ] ((Fin k → Fin n) → V)) ≃ₗ[ℝ]
      ((Fin (k + 1) → Fin n) → V) := {
    toFun := fun f p ↦ f (EuclideanSpace.single (p 0) 1) (Fin.tail p)
    invFun := fun v ↦ ({
      toFun := fun x p ↦ ∑ a : Fin n, x a • v (Fin.cons a p)
      map_add' := by intros; ext p; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; ext p; simp [mul_smul, Finset.smul_sum] } :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ((Fin k → Fin n) → V)).toContinuousLinearMap
    left_inv := by
      intro f
      ext x p
      have h := congrArg (fun y ↦ f y p) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x)
      simpa [map_sum, map_smul, EuclideanSpace.basisFun_repr,
        EuclideanSpace.basisFun_apply] using h
    right_inv := by intro v; ext p; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  exact e.toContinuousLinearEquiv

private theorem arrayDerivativeEquiv_apply (n k : ℕ) (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : EuclideanSpace ℝ (Fin n) →L[ℝ] ((Fin k → Fin n) → V))
    (p : Fin (k + 1) → Fin n) :
    arrayDerivativeEquiv n k V f p = f (EuclideanSpace.single (p 0) 1) (Fin.tail p) := rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] {A : SmoothComplexBundleAtlas (n := n) E}

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace MI (M := M)

namespace AtlasComplexConnection

private def arrayConnectionTerm (cov : AtlasComplexConnection A)
    (covT : CovariantDerivative MI H TM)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (k : ℕ) (z : H) :
    ((Fin k → Fin n) → EuclideanSpace ℂ (Fin (A.rank i))) →L[ℝ]
      ((Fin (k + 1) → Fin n) → EuclideanSpace ℂ (Fin (A.rank i))) := by
  classical
  exact ContinuousLinearMap.pi fun p ↦
    ((cov.connectionForm c i z (EuclideanSpace.single (p 0) 1)).restrictScalars ℝ).comp
      (ContinuousLinearMap.proj (Fin.tail p)) -
    ∑ a : Fin k, ∑ b : Fin n,
      atlasTangentChristoffel covT c hc z (p 0) (p a.succ) b •
        ContinuousLinearMap.proj (Function.update (Fin.tail p) a b)

set_option backward.isDefEq.respectTransparency false in
private theorem arrayConnectionTerm_contDiffOn (cov : AtlasComplexConnection A)
    (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index) (k : ℕ) :
    ContDiffOn ℝ ∞ (arrayConnectionTerm cov covT c hc i k)
      (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) := by
  classical
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_pi.mpr
  intro p z hz
  apply ContDiffAt.contDiffWithinAt
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let t : Trivialization H (π H TM) := (tangentBundleCore MI M).localTriv ⟨c, hc⟩
  let : MemTrivializationAtlas t := ⟨⟨⟨c, hc⟩, rfl⟩⟩
  have hsymm : ContMDiffAt MI MI ∞ c.symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hz.1
  have hdomain : c.target ∩ c.symm ⁻¹' (A.chart i).baseSet ∈ nhds z :=
    inter_mem (c.open_target.mem_nhds hz.1)
      (hsymm.continuousAt.preimage_mem_nhds ((A.chart i).open_baseSet.mem_nhds hz.2))
  have hΓ := (cov.smooth_connectionForm c hc i).contDiffAt hdomain
  let restrict := ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ
  have hvalue := (restrict.contDiff.contDiffAt.comp z
    (hΓ.clm_apply (contDiffAt_const (c := EuclideanSpace.single (p 0) 1)))).clm_apply
      (contDiffAt_const (c := v (Fin.tail p)))
  have hchristoffel (a b d : Fin n) :
      ContDiffAt ℝ ∞ (fun y ↦ atlasTangentChristoffel covT c hc y a b d) z := by
    have hlocal := contMDiffAt_tangentCovariantDerivative_coord covT hcovT t
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) (c.symm z)
      (c.map_target hz.1)
    have hcolumn := (EuclideanSpace.proj d).contMDiff.contMDiffAt.comp (c.symm z) hlocal
    exact contMDiffAt_iff_contDiffAt.mp (hcolumn.comp z hsymm)
  simp only [arrayConnectionTerm, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    sub_apply, sum_apply, smul_apply]
  change ContDiffAt ℝ ∞ (fun y ↦
    cov.connectionForm c i y (EuclideanSpace.single (p 0) 1) (v (Fin.tail p)) -
      ∑ a : Fin k, ∑ b : Fin n,
        atlasTangentChristoffel covT c hc y (p 0) (p a.succ) b •
          v (Function.update (Fin.tail p) a b)) z
  apply hvalue.sub
  exact ContDiffAt.sum (fun a _ ↦ ContDiffAt.sum (fun b _ ↦
    (hchristoffel (p 0) (p a.succ) b).smul contDiffAt_const))

set_option backward.isDefEq.respectTransparency false in
/-- On a compact coordinate set the original full covariant arrays and ordinary jets
control each other, with constants fixed independently of the smooth section. -/
theorem exists_localIteratedCovariantDerivative_jet_comparison
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (K : Set H) (hK : IsCompact K)
    (hKU : K ⊆ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) (k : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ u : A.smoothSections, ∀ x ∈ K,
      ‖fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u k p x‖ ≤
        C * ∑ l ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ l (atlasSectionInChart A c i u.val) x‖ ∧
      ‖iteratedFDeriv ℝ k (atlasSectionInChart A c i u.val) x‖ ≤
        D * ∑ l ∈ Finset.range (k + 1),
          ‖fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u l p x‖ := by
  classical
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let U := c.target ∩ c.symm ⁻¹' (A.chart i).baseSet
  have hU : IsOpen U := by
    exact c.continuousOn_symm.isOpen_inter_preimage c.open_target (A.chart i).open_baseSet
  let e (l : ℕ) := arrayDerivativeEquiv n l V
  let Γ (l : ℕ) (x : H) := (e l).symm.toContinuousLinearMap.comp
    (arrayConnectionTerm cov covT c hc i l x)
  have hΓ (l : ℕ) : ContDiffOn ℝ ∞ (Γ l) U :=
    contDiffOn_const.clm_comp (arrayConnectionTerm_contDiffOn cov covT hcovT c hc i l)
  let f (u : A.smoothSections) (l : ℕ) (x : H) :=
    fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u l p x
  have hf (u : A.smoothSections) (l : ℕ) : ContDiffOn ℝ ∞ (f u l) U := by
    apply contDiffOn_pi.mpr
    intro p x hx
    exact (localIteratedCovariantDerivative_contDiffAt
      cov covT hcovT c hc i u l p x hx).contDiffWithinAt
  -- The leading derivative and every tangent-slot term match the original recursion.
  have hrec (u : A.smoothSections) (l : ℕ) (x : H) (hx : x ∈ U) :
      f u (l + 1) x = e l (fderiv ℝ (f u l) x + Γ l x (f u l x)) := by
    rw [map_add]
    simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    funext p
    change _ = arrayDerivativeEquiv n l V (fderiv ℝ (f u l) x) p +
      arrayConnectionTerm cov covT c hc i l x (f u l x) p
    rw [arrayDerivativeEquiv_apply]
    have hd := fderiv_pi (fun q ↦
      (localIteratedCovariantDerivative_contDiffAt
        cov covT hcovT c hc i u l q x hx).differentiableAt (by simp))
    simp only [f, localIteratedCovariantDerivative, arrayConnectionTerm,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, sub_apply, sum_apply, smul_apply, hd, Fin.tail_def]
    abel
  -- Order zero is the same original section coordinate, isometrically repeated on one index.
  let z₀ : V ≃ₗᵢ[ℝ] ((Fin 0 → Fin n) → V) := {
    (LinearEquiv.funUnique (Fin 0 → Fin n) ℝ V).symm with
    norm_map' := fun v ↦ by
      change ‖fun _ : Fin 0 → Fin n ↦ v‖ = ‖v‖
      simp only [pi_norm_const] }
  have hzero (u : A.smoothSections) (l : ℕ) (x : H) :
      ‖iteratedFDeriv ℝ l (f u 0) x‖ =
        ‖iteratedFDeriv ℝ l (atlasSectionInChart A c i u.val) x‖ :=
    z₀.norm_iteratedFDeriv_comp_left (atlasSectionInChart A c i u.val) x l
  obtain ⟨C, hC, hforward⟩ := exists_connectionJet_derivative_bound U K hU hKU hK e Γ hΓ k 0
  obtain ⟨D, hD, hreverse⟩ := exists_connectionJet_recovery_bound U K hU hKU hK e Γ hΓ 0 k
  refine ⟨C, D, hC, hD, fun u x hx ↦ ⟨?_, ?_⟩⟩
  · simpa only [norm_iteratedFDeriv_zero, Nat.add_zero, hzero] using
      hforward (f u) (hf u) (hrec u) x hx
  · simpa only [Nat.zero_add, hzero] using hreverse (f u) (hf u) (hrec u) x hx

omit [T2Space M] in
/-- The actual connection recursion is local: a locally zero original section coordinate
has zero covariant arrays of every order. -/
theorem localIteratedCovariantDerivative_eq_zero_of_eventuallyEq
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (u : A.smoothSections) (k : ℕ) (p : Fin k → Fin n) (x : H)
    (hu : atlasSectionInChart A c i u.val =ᶠ[nhds x] 0) :
    cov.localIteratedCovariantDerivative covT c hc i u k p x = 0 := by
  induction k generalizing x with
  | zero => exact hu.eq_of_nhds
  | succ k ih =>
    -- Local vanishing persists for each old array before differentiating it.
    have hz : cov.localIteratedCovariantDerivative covT c hc i u k (Fin.tail p)
        =ᶠ[nhds x] 0 := by
      filter_upwards [hu.eventually_nhds] with y hy
      exact ih (Fin.tail p) y hy
    have hd := hz.fderiv_eq (𝕜 := ℝ)
    simp only [Fin.tail_def, fderiv_zero] at hd
    simp only [localIteratedCovariantDerivative, hd, ih _ x hu, map_zero, smul_zero,
      Finset.sum_const_zero,
      add_zero, sub_zero]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of every original covariant array is complex linear in the smooth section
on its valid chart domain. -/
theorem isLinearMap_localIteratedCovariantDerivative
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (k : ℕ) (p : Fin k → Fin n) (x : H)
    (hx : x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :
    IsLinearMap ℂ (fun u : A.smoothSections ↦
      cov.localIteratedCovariantDerivative covT c hc i u k p x) := by
  classical
  let U := c.target ∩ c.symm ⁻¹' (A.chart i).baseSet
  have hU : IsOpen U :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (A.chart i).open_baseSet
  induction k generalizing x with
  | zero =>
    constructor
    · intro u v
      simp only [localIteratedCovariantDerivative, atlasSectionInChart,
        Submodule.coe_add, Pi.add_apply]
      rw [(A.linear i (c.symm x) hx.2).map_add]
      exact map_add _ _ _
    · intro a u
      simp only [localIteratedCovariantDerivative, atlasSectionInChart,
        Submodule.coe_smul, Pi.smul_apply]
      rw [(A.linear i (c.symm x) hx.2).map_smul]
      exact map_smul _ _ _
  | succ k ih =>
    have hdiff (u : A.smoothSections) :
        DifferentiableAt ℝ (cov.localIteratedCovariantDerivative covT c hc i u k
          (Fin.tail p)) x :=
      (localIteratedCovariantDerivative_contDiffAt
        cov covT hcovT c hc i u k (Fin.tail p) x hx).differentiableAt (by simp)
    constructor
    · intro u v
      have heq : cov.localIteratedCovariantDerivative covT c hc i (u + v) k (Fin.tail p)
          =ᶠ[nhds x] (fun y ↦
            cov.localIteratedCovariantDerivative covT c hc i u k (Fin.tail p) y +
              cov.localIteratedCovariantDerivative covT c hc i v k (Fin.tail p) y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact (ih (Fin.tail p) y hy).map_add u v
      have hd := heq.fderiv_eq (𝕜 := ℝ)
      rw [fderiv_fun_add (hdiff u) (hdiff v)] at hd
      simp only [Fin.tail_def] at hd
      simp only [localIteratedCovariantDerivative, hd, add_apply,
        (ih _ x hx).map_add, map_add, smul_add,
        Finset.sum_add_distrib]
      abel
    · intro a u
      have heq : cov.localIteratedCovariantDerivative covT c hc i (a • u) k (Fin.tail p)
          =ᶠ[nhds x] (fun y ↦ a •
            cov.localIteratedCovariantDerivative covT c hc i u k (Fin.tail p) y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact (ih (Fin.tail p) y hy).map_smul a u
      have hd := heq.fderiv_eq (𝕜 := ℝ)
      rw [fderiv_fun_const_smul (hdiff u)] at hd
      simp only [Fin.tail_def] at hd
      simp only [localIteratedCovariantDerivative, hd, smul_apply,
        (ih _ x hx).map_smul, map_smul, smul_add,
        smul_sub, Finset.smul_sum, smul_smul, mul_comm]

end AtlasComplexConnection

namespace AtlasBundlePresentation

/-- Multiplication of an original smooth section by a member of its fixed partition of unity. -/
def cutoffSection (L : AtlasBundlePresentation A) (a : Fin L.size) :
    A.smoothSections →ₗ[ℂ] A.smoothSections where
  toFun u := ⟨fun x ↦ (L.cutoff a x : ℂ) • u.val x, by
    intro i
    apply ((L.smooth_cutoff a).contMDiffOn.smul (u.property i)).congr
    intro x hx
    rw [(A.linear i x hx).map_smul]
    exact IsScalarTower.algebraMap_smul ℂ (L.cutoff a x)
      ((A.chart i) ⟨x, u.val x⟩).2⟩
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact smul_add _ _ _
  map_smul' a u := by
    apply Subtype.ext
    funext x
    exact smul_comm _ _ _

omit [T2Space M] [IsManifold MI ∞ M] in
/-- The specified cutoff sections sum to the same original smooth section. -/
theorem sum_cutoffSection (L : AtlasBundlePresentation A) (u : A.smoothSections) :
    ∑ a : Fin L.size, L.cutoffSection a u = u := by
  apply Subtype.ext
  funext x
  have hsum : ∑ a : Fin L.size, (L.cutoff a x : ℂ) = 1 := by
    exact_mod_cast L.sum_cutoff x
  simp only [Submodule.coe_sum, Finset.sum_apply]
  change (∑ a : Fin L.size, (L.cutoff a x : ℂ) • u.val x) = u.val x
  rw [← Finset.sum_smul, hsum, one_smul]

omit [T2Space M] [IsManifold MI ∞ M] in
/-- In its valid original chart, the cutoff section has exactly the specified localized
coordinate function. The frame-domain condition is retained explicitly. -/
theorem atlasSectionInChart_cutoffSection_eq (L : AtlasBundlePresentation A)
    (a : Fin L.size) (u : A.smoothSections) (x : H)
    (hx : x ∈ (L.chart a).target ∩ (L.chart a).symm ⁻¹' (A.chart (L.frameIndex a)).baseSet) :
    atlasSectionInChart A (L.chart a) (L.frameIndex a) (L.cutoffSection a u).val x =
      L.localizedFunction a u x := by
  change (EuclideanSpace.equiv (Fin (A.rank (L.frameIndex a))) ℂ).symm
      ((A.chart (L.frameIndex a)) ⟨(L.chart a).symm x,
        (L.cutoff a ((L.chart a).symm x) : ℂ) • u.val ((L.chart a).symm x)⟩).2 = _
  rw [localizedFunction, ite_eq_left hx.1]
  rw [(A.linear (L.frameIndex a) ((L.chart a).symm x) hx.2).map_smul]
  exact map_smul _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary derivatives of the original cutoff localization are bounded by the
actual covariant arrays of the same section on its fixed compact support. -/
theorem exists_localizedFunction_derivative_covariant_bound
    (L : AtlasBundlePresentation A) (cov : AtlasComplexConnection A)
    (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (a : Fin L.size) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.smoothSections,
      ∀ x ∈ (L.chart a) '' tsupport (L.cutoff a),
        ‖iteratedFDeriv ℝ k (L.localizedFunction a u) x‖ ≤
          C * ∑ l ∈ Finset.range (k + 1),
            ‖fun p ↦ cov.localIteratedCovariantDerivative covT (L.chart a)
              (L.chart_mem_atlas a) (L.frameIndex a) u l p x‖ := by
  classical
  let c := L.chart a
  let i := L.frameIndex a
  let K := c '' tsupport (L.cutoff a)
  let U := c.target ∩ c.symm ⁻¹' (A.chart i).baseSet
  let χ : H → ℝ := fun y ↦ L.cutoff a (c.symm y)
  have hK : IsCompact K := (L.compact_support a).image_of_continuousOn
    (c.continuousOn.mono (fun y hy ↦ (L.support_subset a hy).1))
  have hKU : K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    have hs := L.support_subset a hy
    refine ⟨c.map_source hs.1, ?_⟩
    change c.symm (c y) ∈ (A.chart i).baseSet
    rw [c.left_inv hs.1]
    exact hs.2
  have hU : IsOpen U :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (A.chart i).open_baseSet
  have hχ : ContDiffOn ℝ ∞ χ U := by
    intro x hx
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := MI) (n := ∞) (L.chart_mem_atlas a)) hx.1
    exact (contMDiffAt_iff_contDiffAt.mp
      ((L.smooth_cutoff a).contMDiffAt.comp x hsymm)).contDiffWithinAt
  -- First estimate the fixed scalar cutoff, then recover each derivative of the section.
  obtain ⟨B, hB, hcutoff⟩ := exists_iteratedFDeriv_smul_bound
    (V := EuclideanSpace ℂ (Fin (A.rank i))) U K hU hKU hK χ hχ k
  have hbounds (l : ℕ) :=
    cov.exists_localIteratedCovariantDerivative_jet_comparison covT hcovT c
      (L.chart_mem_atlas a) i K hK hKU l
  choose C D hC hD hlocal using hbounds
  let F : ℝ := ∑ l ∈ Finset.range (k + 1), D l
  have hF : 0 ≤ F := Finset.sum_nonneg (fun l _ ↦ hD l)
  refine ⟨B * F, mul_nonneg hB hF, fun u x hx ↦ ?_⟩
  have hcoords : ContDiffOn ℝ ∞ (atlasSectionInChart A c i u.val) U := by
    intro y hy
    exact (AtlasComplexConnection.localIteratedCovariantDerivative_contDiffAt
      cov covT hcovT c (L.chart_mem_atlas a) i u 0 Fin.elim0 y hy).contDiffWithinAt
  have heq : L.localizedFunction a u =ᶠ[nhds x]
      (fun y ↦ χ y • atlasSectionInChart A c i u.val y) := by
    filter_upwards [c.open_target.mem_nhds (hKU hx).1] with y hy
    simp only [localizedFunction, χ, c, i, ite_eq_left hy]
    exact_mod_cast (IsScalarTower.algebraMap_smul ℂ
      (L.cutoff a ((L.chart a).symm y)) (atlasSectionInChart A c i u.val y))
  rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
  apply (hcutoff _ hcoords x hx).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hB
  dsimp only [F]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro l hl
  have hlk := Finset.mem_range.mp hl
  apply ((hlocal l u x hx).2).trans
  apply mul_le_mul_of_nonneg_left _ (hD l)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun _ _ _ ↦ norm_nonneg _)

set_option backward.isDefEq.respectTransparency false in
/-- The covariant arrays of each actual cutoff section are controlled by ordinary
derivatives of its own original coordinate localization, with section-independent constants. -/
theorem exists_cutoffSection_covariant_derivative_bound
    (L : AtlasBundlePresentation A) (cov : AtlasComplexConnection A)
    (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (a : Fin L.size) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.smoothSections,
      ∀ x ∈ (L.chart a) '' tsupport (L.cutoff a),
        ‖fun p ↦ cov.localIteratedCovariantDerivative covT (L.chart a)
          (L.chart_mem_atlas a) (L.frameIndex a) (L.cutoffSection a u) k p x‖ ≤
            C * ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l (L.localizedFunction a u) x‖ := by
  classical
  let c := L.chart a
  let i := L.frameIndex a
  let K := c '' tsupport (L.cutoff a)
  let U := c.target ∩ c.symm ⁻¹' (A.chart i).baseSet
  have hK : IsCompact K := (L.compact_support a).image_of_continuousOn
    (c.continuousOn.mono (fun y hy ↦ (L.support_subset a hy).1))
  have hKU : K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    have hs := L.support_subset a hy
    refine ⟨c.map_source hs.1, ?_⟩
    change c.symm (c y) ∈ (A.chart i).baseSet
    rw [c.left_inv hs.1]
    exact hs.2
  have hU : IsOpen U :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target (A.chart i).open_baseSet
  obtain ⟨C, D, hC, hD, hbound⟩ :=
    cov.exists_localIteratedCovariantDerivative_jet_comparison covT hcovT c
      (L.chart_mem_atlas a) i K hK hKU k
  refine ⟨C, hC, fun u x hx ↦ ?_⟩
  have heq : atlasSectionInChart A c i (L.cutoffSection a u).val =ᶠ[nhds x]
      L.localizedFunction a u := by
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    exact L.atlasSectionInChart_cutoffSection_eq a u y hy
  have hder (l : ℕ) := (heq.iteratedFDeriv ℝ l).eq_of_nhds
  simpa only [hder] using (hbound (L.cutoffSection a u) x hx).1

omit [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
/-- Outside the specified cutoff support, every actual covariant derivative of its
cutoff section vanishes in every valid original chart. -/
theorem localIteratedCovariantDerivative_cutoffSection_eq_zero
    (L : AtlasBundlePresentation A) (cov : AtlasComplexConnection A)
    (covT : CovariantDerivative MI H TM) (a : Fin L.size) (u : A.smoothSections)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (k : ℕ) (p : Fin k → Fin n) (x : H)
    (hx : x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet)
    (hχ : c.symm x ∉ tsupport (L.cutoff a)) :
    cov.localIteratedCovariantDerivative covT c hc i (L.cutoffSection a u) k p x = 0 := by
  apply cov.localIteratedCovariantDerivative_eq_zero_of_eventuallyEq
  have hsymm := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := MI) (n := ∞) hc) hx.1).continuousAt
  have hzero := (notMem_tsupport_iff_eventuallyEq.mp hχ).comp_tendsto hsymm
  have hframe := hsymm.preimage_mem_nhds ((A.chart i).open_baseSet.mem_nhds hx.2)
  filter_upwards [hzero, hframe] with y hy hiy
  change atlasSectionInChart A c i (L.cutoffSection a u).val y = 0
  change L.cutoff a (c.symm y) = 0 at hy
  change (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
    ((A.chart i) ⟨c.symm y, (L.cutoff a (c.symm y) : ℂ) • u.val (c.symm y)⟩).2 = 0
  simp only [hy, Complex.ofReal_zero, zero_smul]
  rw [(A.linear i (c.symm y) hiy).map_zero, map_zero]

end AtlasBundlePresentation


namespace AtlasComplexConnection

/-- The squared tensor length is continuous on the valid chart and frame overlap. -/
theorem continuousOn_localCovariantDerivativeNormSq
    (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
    (hcovT : covT.ContMDiffCovariantDerivative ∞)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
    (k : ℕ) (u : A.smoothSections) :
    ContinuousOn (cov.localCovariantDerivativeNormSq covT c hc i g h k u)
      (c.source ∩ (A.chart i).baseSet) := by
  classical
  let U := c.source ∩ (A.chart i).baseSet
  let v (p : Fin k → Fin n) (x : M) :=
    cov.localIteratedCovariantDerivative covT c hc i u k p (c x)
  have hv (p : Fin k → Fin n) : ContinuousOn (v p) U := by
    intro x hx
    have hz : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet :=
      ⟨c.map_source hx.1, by simpa only [Set.mem_preimage, c.left_inv hx.1] using hx.2⟩
    exact (cov.localIteratedCovariantDerivative_contDiffAt covT hcovT c hc i u k p
      (c x) hz).continuousAt.comp_continuousWithinAt
        ((c.continuousOn.mono Set.inter_subset_left) x hx)
  let Q (x : M) : ℝ := ∑ p : Fin k → Fin n, ∑ q : Fin k → Fin n,
    (∏ a : Fin k, g.inner x
      (covectorFromChart c x (EuclideanSpace.single (p a) 1))
      (covectorFromChart c x (EuclideanSpace.single (q a) 1))) *
      (inner ℂ (v p x) (A.hermitianGramOperator h i x (v q x))).re
  -- Smooth coordinate tensors and metric coefficients give continuity term by term.
  have hQ : ContinuousOn Q U := by
    apply continuousOn_finsetSum
    intro p _
    apply continuousOn_finsetSum
    intro q _
    apply ContinuousOn.mul
    · apply continuousOn_finsetProd
      intro a _
      exact (g.contMDiffOn_inner_covectorFromChart c hc
        (EuclideanSpace.single (p a) 1) (EuclideanSpace.single (q a) 1)).continuousOn.mono
          Set.inter_subset_left
    · exact Complex.continuous_re.comp_continuousOn
        ((hv p).inner (((A.contMDiffOn_hermitianGramOperator h hh i).continuousOn.mono
          Set.inter_subset_right).clm_apply (hv q)))
  -- The coordinate Gram operator is the given original Hermitian form in this same frame.
  apply hQ.congr
  intro x hx
  rw [localCovariantDerivativeNormSq, dite_eq_left hx]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  have hp := A.pairing_eq_hermitianGramOperator h i x hx.2
    ((A.frameLinearEquiv i x hx.2).symm
      ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (v p x)))
    ((A.frameLinearEquiv i x hx.2).symm
      ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ) (v q x)))
  simpa only [v, LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    using congrArg Complex.re hp


end AtlasComplexConnection

end CompactCovariantEstimates

namespace AtlasBundlePresentation

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "TM" => TangentSpace MI (M := M)

variable (L : AtlasBundlePresentation A) [MeasurableSpace M] (μ : Measure M)
  (g : SmoothCotangentMetric (n := n) (M := M))
  (h : ComplexBundle.ContinuousHermitianMetric E)
  (cov : AtlasComplexConnection A)
  (covT : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (M := M) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))

/-- The geometric integer norm of the original section, via its actual derivative tensors. -/
def covariantSobolevNorm (k : ℕ) (u : A.smoothSections) : ℝ :=
  Real.sqrt (∑ j : Fin (k + 1), ∫ x : M,
    ∑ a : Fin L.size, L.cutoff a x *
      cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
        (L.frameIndex a) g h j.val u x ∂μ)

variable [hT : T2Space M] [hSC : SecondCountableTopology M]
  (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)

include hM hT hSC hcovT in
/-- The geometric norm does not depend on the charts or partition used to evaluate its integral. -/
theorem covariantSobolevNorm_eq (K : AtlasBundlePresentation A)
    (k : ℕ) (u : A.smoothSections) :
    L.covariantSobolevNorm μ g h cov covT k u =
      K.covariantSobolevNorm μ g h cov covT k u := by
  /- Stage 1: at each x, active cutoff terms lie in their designated valid
  chart/frame overlaps. Their local contractions agree by the preceding
  invariance theorem. A chart covering x therefore evaluates a single common
  squared tensor length, independent of the presentation.
  Stage 2: each partition sums to one. Both finite weighted sums equal that
  same scalar pointwise. Consequently their integrands, integrals, sums over
  derivative order and square roots are equal. This is exact independence of
  geometric evaluation data, not equality of different Fourier norms. -/
  classical
  -- Compare each pair of active chart weights using the same tensor and metrics.
  have hlocal (j : ℕ) (x : M) :
      (∑ a : Fin L.size, L.cutoff a x *
        cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
          (L.frameIndex a) g h j u x) =
      ∑ b : Fin K.size, K.cutoff b x *
        cov.localCovariantDerivativeNormSq covT (K.chart b) (K.chart_mem_atlas b)
          (K.frameIndex b) g h j u x := by
    let f (a : Fin L.size) := cov.localCovariantDerivativeNormSq covT (L.chart a)
      (L.chart_mem_atlas a) (L.frameIndex a) g h j u x
    let t (b : Fin K.size) := cov.localCovariantDerivativeNormSq covT (K.chart b)
      (K.chart_mem_atlas b) (K.frameIndex b) g h j u x
    have hpair (a : Fin L.size) (b : Fin K.size) :
        L.cutoff a x * K.cutoff b x * f a = L.cutoff a x * K.cutoff b x * t b := by
      by_cases ha : L.cutoff a x = 0
      · simp [ha]
      by_cases hb : K.cutoff b x = 0
      · simp [hb]
      have hx := L.support_subset a (subset_tsupport (L.cutoff a) ha)
      have hy := K.support_subset b (subset_tsupport (K.cutoff b) hb)
      rw [show f a = t b from cov.localCovariantDerivativeNormSq_eq covT
        (L.chart a) (L.chart_mem_atlas a) (L.frameIndex a) hcovT g h
        (K.chart b) (K.chart_mem_atlas b) (K.frameIndex b) j u x hx hy]
    change (∑ a, L.cutoff a x * f a) = ∑ b, K.cutoff b x * t b
    calc
      (∑ a, L.cutoff a x * f a) =
          ∑ a, ∑ b, L.cutoff a x * K.cutoff b x * f a := by
        simp only [← Finset.sum_mul, ← Finset.mul_sum, K.sum_cutoff, mul_one]
      _ = ∑ a, ∑ b, L.cutoff a x * K.cutoff b x * t b := by
        exact Finset.sum_congr rfl (fun a _ ↦ Finset.sum_congr rfl (fun b _ ↦ hpair a b))
      _ = ∑ b, K.cutoff b x * t b := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, L.sum_cutoff, one_mul]
  -- Pointwise equality passes through the original integrals and the same square root.
  unfold covariantSobolevNorm
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun f : M → ℝ ↦ ∫ x, f x ∂μ) (funext (hlocal j.val))

variable [BorelSpace M] [hC : CompactSpace M]
  [hμ : IsSmoothPositiveMeasure (n := n) μ] (hh : A.IsSmoothHermitianMetric h)

set_option backward.isDefEq.respectTransparency false in
include hM hT hSC hcovT hC hμ hh in
/-- SG III.2.14 for the actual varying-rank bundle: geometric and Fourier norms are equivalent. -/
theorem exists_covariantSobolevNorm_comparison (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : A.smoothSections,
      c * ‖L.smoothToSobolev (k : ℝ) u‖ ≤
        L.covariantSobolevNorm μ g h cov covT k u ∧
      L.covariantSobolevNorm μ g h cov covT k u ≤
        C * ‖L.smoothToSobolev (k : ℝ) u‖ := by
  /- Assemble local estimates for the supplied connections, metrics and cutoffs.
  Compact coordinate estimates and the positive density compare derivative
  energies. Chart invariance and the partition identify the full tensor
  integral. The Fourier comparison and positive square roots then give both
  bounds with constants chosen independently of the section. -/
  classical
  let S₀ : Type _ := A.smoothSections
  have hweightedEnergy [SecondCountableTopology M] [MeasurableSpace M]
      [BorelSpace M] [CompactSpace M]
      (L : AtlasBundlePresentation A) (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
      (cov : AtlasComplexConnection A) (covT : CovariantDerivative MI H TM)
      (hcovT : covT.ContMDiffCovariantDerivative ∞)
      (g : SmoothCotangentMetric (n := n) (M := M))
      (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h) :
      ∀ (a : Fin L.size) (j : ℕ) (u : A.smoothSections),
        let F := fun x ↦ L.cutoff a x * cov.localCovariantDerivativeNormSq covT
          (L.chart a) (L.chart_mem_atlas a) (L.frameIndex a) g h j u x
        (∀ x, 0 ≤ F x) ∧ Continuous F ∧ Integrable F μ := by
    let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
    intro a j u
    let N := cov.localCovariantDerivativeNormSq covT
      (L.chart a) (L.chart_mem_atlas a) (L.frameIndex a) g h j u
    have hnonneg (x : M) : 0 ≤ N x := by
      dsimp only [N, AtlasComplexConnection.localCovariantDerivativeNormSq]
      split_ifs with hx
      · obtain ⟨q, hq⟩ := A.exists_covariant_array_inner_core g h (L.chart a)
          (L.chart_mem_atlas a) (L.frameIndex a) j x hx
        rw [← hq]
        exact q.re_inner_nonneg _
      · exact le_refl 0
    have hcont : Continuous (fun x ↦ L.cutoff a x * N x) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ tsupport (L.cutoff a)
      · have hU : IsOpen ((L.chart a).source ∩ (A.chart (L.frameIndex a)).baseSet) :=
          (L.chart a).open_source.inter (A.chart (L.frameIndex a)).open_baseSet
        exact ((L.smooth_cutoff a).continuous.continuousAt).mul
          ((cov.continuousOn_localCovariantDerivativeNormSq covT hcovT g h hh
            (L.chart a) (L.chart_mem_atlas a) (L.frameIndex a) j u).continuousAt
              (hU.mem_nhds (L.support_subset a hx)))
      · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport (L.cutoff a)).isOpen_compl.mem_nhds hx] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    refine ⟨fun x ↦ mul_nonneg (L.cutoff_nonneg a x) (hnonneg x), hcont, ?_⟩
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Transport localized derivative energy through the same original chart.
  have hchartTransport [MeasurableSpace M] [BorelSpace M]
      (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
      (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
      (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.source) :
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ f : H → ℝ,
        Continuous f → tsupport f ⊆ c '' K → (∀ z, 0 ≤ f z) →
        let F := c.source.indicator (fun x ↦ f (c x))
        Continuous F ∧ tsupport F ⊆ K ∧
          a * (∫ z, f z) ≤ ∫ x, F x ∂μ ∧ (∫ x, F x ∂μ) ≤ b * (∫ z, f z) := by
    classical
    obtain ⟨a, b, ha, hb, hbound⟩ := exists_integral_chart_bounds μ c hc K hK hKc
    refine ⟨a, b, ha, hb, ?_⟩
    intro f hf hs hn
    let F := c.source.indicator (fun x ↦ f (c x))
    have hzero (x : M) (hx : x ∉ K) : F x = 0 := by
      by_cases hxc : x ∈ c.source
      · rw [show F x = f (c x) from Set.indicator_of_mem hxc _]
        apply image_eq_zero_of_notMem_tsupport
        intro h
        obtain ⟨y, hy, hxy⟩ := hs h
        exact hx ((c.injOn (hKc hy) hxc hxy) ▸ hy)
      · exact Set.indicator_of_notMem hxc _
    have hsupport : tsupport F ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hxK
      exact hx (hzero x hxK)
    have hcont : Continuous F := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ K
      · apply (hf.continuousAt.comp
          (c.continuousOn.continuousAt (c.open_source.mem_nhds (hKc hx)))).congr_of_eventuallyEq
        filter_upwards [c.open_source.mem_nhds (hKc hx)] with y hy
        exact Set.indicator_of_mem hy _
      · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact hzero y hy
    have hnonneg (x : M) : 0 ≤ F x := by
      by_cases hx : x ∈ c.source
      · simpa only [F, Set.indicator_of_mem hx] using hn (c x)
      · simp only [F, Set.indicator_of_notMem hx, le_refl]
    have hcoord : (∫ z in c.target, F (c.symm z)) = ∫ z, f z := by
      calc
        _ = ∫ z in c.target, f z := by
          apply setIntegral_congr_fun c.open_target.measurableSet
          intro z hz
          simp only [F, Set.indicator_of_mem (c.map_target hz), c.right_inv hz]
        _ = _ := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro z hz
          apply image_eq_zero_of_notMem_tsupport
          intro h
          obtain ⟨x, hx, rfl⟩ := hs h
          exact hz (c.map_source (hKc hx))
    refine ⟨hcont, hsupport, ?_⟩
    simpa only [hcoord] using hbound F hcont hsupport hnonneg
  -- The partition preserves full tensor energy and controls finite sums.
  have hglobalTensor [SecondCountableTopology M] (L : AtlasBundlePresentation A)
      (cov : AtlasComplexConnection A)
      (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
      (g : SmoothCotangentMetric (n := n) (M := M))
      (h : ComplexBundle.ContinuousHermitianMetric E) :
      let T (j : ℕ) (u : A.smoothSections) (x : M) :=
        ∑ b : Fin L.size, L.cutoff b x *
          cov.localCovariantDerivativeNormSq covT (L.chart b) (L.chart_mem_atlas b)
            (L.frameIndex b) g h j u x
      (∀ (m j : ℕ) (v : Fin m → A.smoothSections) (x : M),
        T j (∑ a, v a) x ≤ (m : ℝ) * ∑ a, T j (v a) x) ∧
      (∀ (a : Fin L.size) (j : ℕ) (u : A.smoothSections),
        tsupport (T j (L.cutoffSection a u)) ⊆ tsupport (L.cutoff a)) ∧
      (∀ (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
        (j : ℕ) (u : A.smoothSections) (x : M), x ∈ c.source ∩ (A.chart i).baseSet →
          T j u x = cov.localCovariantDerivativeNormSq covT c hc i g h j u x) := by
    classical
    let T (j : ℕ) (u : A.smoothSections) (x : M) :=
      ∑ b : Fin L.size, L.cutoff b x *
        cov.localCovariantDerivativeNormSq covT (L.chart b) (L.chart_mem_atlas b)
          (L.frameIndex b) g h j u x
    -- The finite-sum inequality holds for the original inner product in one valid chart.
    have hNsum (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
        (m j : ℕ) (v : Fin m → A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet) :
        cov.localCovariantDerivativeNormSq covT c hc i g h j (∑ a, v a) x ≤
          (m : ℝ) * ∑ a, cov.localCovariantDerivativeNormSq covT c hc i g h j (v a) x := by
      let F (u : A.smoothSections) : (Fin j → Fin n) → EuclideanSpace ℂ (Fin (A.rank i)) :=
        fun p ↦ cov.localIteratedCovariantDerivative covT c hc i u j p (c x)
      have hz : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet :=
        ⟨c.map_source hx.1, by simpa only [Set.mem_preimage, c.left_inv hx.1] using hx.2⟩
      have hFsum : F (∑ a, v a) = ∑ a, F (v a) := by
        funext p
        let D := IsLinearMap.mk'
          (fun u : A.smoothSections ↦ cov.localIteratedCovariantDerivative covT c hc i u j p (c x))
          (cov.isLinearMap_localIteratedCovariantDerivative covT hcovT c hc i j p (c x) hz)
        simp only [Finset.sum_apply]
        exact map_sum D v Finset.univ
      obtain ⟨q, hq⟩ := A.exists_covariant_array_inner_core g h c hc i j x hx
      let : InnerProductSpace.Core ℝ
          ((Fin j → Fin n) → EuclideanSpace ℂ (Fin (A.rank i))) := q
      -- Bilinearity and positivity suffice; the native coordinate norm is never changed.
      let B : LinearMap.BilinForm ℝ
          ((Fin j → Fin n) → EuclideanSpace ℂ (Fin (A.rank i))) :=
        LinearMap.mk₂ ℝ q.inner
          (fun u v w ↦ q.add_left u v w)
          (by intro t u v; simpa using q.smul_left u v t)
          (fun u v w ↦ InnerProductSpace.Core.inner_add_right u v w)
          (by
            intro t u v
            simpa using InnerProductSpace.Core.inner_smul_right (𝕜 := ℝ) u v (r := t))
      have hdiag (u : A.smoothSections) :
          B (F u) (F u) = cov.localCovariantDerivativeNormSq covT c hc i g h j u x := by
        rw [AtlasComplexConnection.localCovariantDerivativeNormSq, dite_eq_left hx]
        exact hq (F u) (F u)
      have hpair (a b : Fin m) :
          2 * B (F (v a)) (F (v b)) ≤ B (F (v a)) (F (v a)) + B (F (v b)) (F (v b)) := by
        have hp := q.re_inner_nonneg (F (v a) - F (v b))
        change 0 ≤ B (F (v a) - F (v b)) (F (v a) - F (v b)) at hp
        have hsymm : B (F (v b)) (F (v a)) = B (F (v a)) (F (v b)) :=
          q.conj_inner_symm (F (v a)) (F (v b))
        simp only [map_sub, LinearMap.sub_apply] at hp
        rw [hsymm] at hp
        linarith
      have hdouble : B (∑ a, F (v a)) (∑ a, F (v a)) =
          ∑ a, ∑ b, B (F (v a)) (F (v b)) := by
        rw [map_sum]
        simp only [LinearMap.sum_apply, map_sum]
        rw [Finset.sum_comm]
      have hp := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦
        Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) ↦ hpair a b))
      have hright : (∑ a : Fin m, ∑ b : Fin m,
          (B (F (v a)) (F (v a)) + B (F (v b)) (F (v b)))) =
            2 * ((m : ℝ) * ∑ a, B (F (v a)) (F (v a))) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [hright] at hp
      simp only [← Finset.mul_sum] at hp
      rw [← hdouble] at hp
      rw [← hdiag, hFsum]
      simp_rw [← hdiag]
      linarith
    have hTsum (m j : ℕ) (v : Fin m → A.smoothSections) (x : M) :
        T j (∑ a, v a) x ≤ (m : ℝ) * ∑ a, T j (v a) x := by
      calc
        T j (∑ a, v a) x ≤ ∑ b : Fin L.size, L.cutoff b x *
            ((m : ℝ) * ∑ a, cov.localCovariantDerivativeNormSq covT
              (L.chart b) (L.chart_mem_atlas b) (L.frameIndex b) g h j (v a) x) := by
          apply Finset.sum_le_sum
          intro b _
          by_cases hb : L.cutoff b x = 0
          · simp only [hb, zero_mul, le_refl]
          · exact mul_le_mul_of_nonneg_left
              (hNsum (L.chart b) (L.chart_mem_atlas b) (L.frameIndex b) m j v x
                (L.support_subset b (subset_tsupport (L.cutoff b) hb))) (L.cutoff_nonneg b x)
        _ = (m : ℝ) * ∑ a, T j (v a) x := by
          simp only [T, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          ring
    -- Off one cutoff support, that same cutoff section has zero arrays in every active chart.
    have hTsupport (a : Fin L.size) (j : ℕ) (u : A.smoothSections) :
        tsupport (T j (L.cutoffSection a u)) ⊆ tsupport (L.cutoff a) := by
      apply closure_minimal _ isClosed_closure
      intro x hx
      by_contra hχ
      change x ∉ tsupport (L.cutoff a) at hχ
      apply hx
      change (∑ b : Fin L.size, L.cutoff b x *
        cov.localCovariantDerivativeNormSq covT (L.chart b) (L.chart_mem_atlas b)
          (L.frameIndex b) g h j (L.cutoffSection a u) x) = 0
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : L.cutoff b x = 0
      · simp only [hb, zero_mul]
      have hxb := L.support_subset b (subset_tsupport (L.cutoff b) hb)
      have hz : L.chart b x ∈ (L.chart b).target ∩
          (L.chart b).symm ⁻¹' (A.chart (L.frameIndex b)).baseSet :=
        ⟨(L.chart b).map_source hxb.1,
          by simpa only [Set.mem_preimage, (L.chart b).left_inv hxb.1] using hxb.2⟩
      have hzχ : (L.chart b).symm (L.chart b x) ∉ tsupport (L.cutoff a) := by
        simpa only [(L.chart b).left_inv hxb.1] using hχ
      have hzero (p : Fin j → Fin n) :=
        L.localIteratedCovariantDerivative_cutoffSection_eq_zero cov covT a u
          (L.chart b) (L.chart_mem_atlas b) (L.frameIndex b) j p (L.chart b x) hz hzχ
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      simp only [AtlasComplexConnection.localCovariantDerivativeNormSq, dite_eq_left hxb,
        hzero, map_zero, InnerProductSpace.Core.inner_zero_left, Complex.zero_re,
        mul_zero, Finset.sum_const_zero]
    -- The partition evaluates one common tensor length, since all active original charts agree.
    have hTeq (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index)
        (j : ℕ) (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart i).baseSet) :
        T j u x = cov.localCovariantDerivativeNormSq covT c hc i g h j u x := by
      calc
        T j u x = ∑ b : Fin L.size, L.cutoff b x *
            cov.localCovariantDerivativeNormSq covT c hc i g h j u x := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : L.cutoff b x = 0
          · simp only [hb, zero_mul]
          · rw [cov.localCovariantDerivativeNormSq_eq covT (L.chart b)
              (L.chart_mem_atlas b) (L.frameIndex b) hcovT g h c hc i j u x
              (L.support_subset b (subset_tsupport (L.cutoff b) hb)) hx]
        _ = _ := by rw [← Finset.sum_mul, L.sum_cutoff, one_mul]
    exact ⟨hTsum, hTsupport, hTeq⟩
  -- Compare actual covariant arrays with ordinary jets on each fixed support.
  have hcompactEnergy
      (L : AtlasBundlePresentation A) (cov : AtlasComplexConnection A)
      (covT : CovariantDerivative MI H TM) (hcovT : covT.ContMDiffCovariantDerivative ∞)
      (g : SmoothCotangentMetric (n := n) (M := M))
      (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
      (a : Fin L.size) (k : ℕ) :
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ u : A.smoothSections, ∀ x ∈ tsupport (L.cutoff a),
        (∑ j ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ j (L.localizedFunction a u) (L.chart a x)‖ ^ 2) ≤
          C * ∑ j ∈ Finset.range (k + 1),
            cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
              (L.frameIndex a) g h j u x ∧
        (∑ j ∈ Finset.range (k + 1),
          cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
            (L.frameIndex a) g h j (L.cutoffSection a u) x) ≤
          D * ∑ j ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ j (L.localizedFunction a u) (L.chart a x)‖ ^ 2 := by
    classical
    let c := L.chart a
    let i := L.frameIndex a
    let F (j : ℕ) (u : A.smoothSections) (x : M) :=
      fun p ↦ cov.localIteratedCovariantDerivative covT c (L.chart_mem_atlas a) i u j p (c x)
    let N (j : ℕ) (u : A.smoothSections) (x : M) :=
      cov.localCovariantDerivativeNormSq covT c (L.chart_mem_atlas a) i g h j u x
    let J (j : ℕ) (u : A.smoothSections) (x : M) :=
      ‖iteratedFDeriv ℝ j (L.localizedFunction a u) (c x)‖
    have hmetric (j : ℕ) := A.exists_covariant_array_norm_sq_bounds g h hh c
      (L.chart_mem_atlas a) i j (tsupport (L.cutoff a)) (L.compact_support a)
      (L.support_subset a)
    choose α β hα hβ hmetric using hmetric
    have hmetricF (j : ℕ) (u : A.smoothSections) (x : M) (hx : x ∈ tsupport (L.cutoff a)) :
        α j * (∑ p, ‖F j u x p‖ ^ 2) ≤ N j u x ∧
          N j u x ≤ β j * (∑ p, ‖F j u x p‖ ^ 2) := by
      have hxU : x ∈ c.source ∩ (A.chart i).baseSet := L.support_subset a hx
      simpa only [N, F, AtlasComplexConnection.localCovariantDerivativeNormSq,
        dite_eq_left hxU] using hmetric j x hx (F j u x)
    have hN (j : ℕ) (u : A.smoothSections) (x : M) (hx : x ∈ tsupport (L.cutoff a)) :
        0 ≤ N j u x :=
      (mul_nonneg (hα j).le (Finset.sum_nonneg (fun p _ ↦ sq_nonneg ‖F j u x p‖))).trans
        (hmetricF j u x hx).1
    -- The finite-array supremum norm and the sum of coordinate squares compare even at rank zero.
    have hpi (j : ℕ) (u : A.smoothSections) (x : M) :
        ‖F j u x‖ ^ 2 ≤ ∑ p, ‖F j u x p‖ ^ 2 := by
      let S : ℝ := ∑ p, ‖F j u x p‖ ^ 2
      have hS : 0 ≤ S := Finset.sum_nonneg (fun p _ ↦ sq_nonneg ‖F j u x p‖)
      have hle : ‖F j u x‖ ≤ Real.sqrt S := by
        apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).mpr
        intro p
        apply Real.le_sqrt_of_sq_le
        exact Finset.single_le_sum (fun q _ ↦ sq_nonneg ‖F j u x q‖) (Finset.mem_univ p)
      exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg S)).mpr hle |>.trans
        (Real.sq_sqrt hS).le
    have hpiUpper (j : ℕ) (u : A.smoothSections) (x : M) :
        (∑ p, ‖F j u x p‖ ^ 2) ≤ (Fintype.card (Fin j → Fin n) : ℝ) * ‖F j u x‖ ^ 2 := by
      calc
        _ ≤ ∑ _p : Fin j → Fin n, ‖F j u x‖ ^ 2 := Finset.sum_le_sum (fun p _ ↦
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_le_pi_norm _ p))
        _ = _ := by simp
    have hforward (j : ℕ) := L.exists_localizedFunction_derivative_covariant_bound
      cov covT hcovT a j
    have hreverse (j : ℕ) := L.exists_cutoffSection_covariant_derivative_bound cov covT hcovT a j
    choose B hB hforward using hforward
    choose E hE hreverse using hreverse
    let Q : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), (α j)⁻¹
    have hQ : 0 < Q := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun j _ ↦ inv_nonneg.mpr (hα j).le))
    have hinv (j : ℕ) (hj : j ∈ Finset.range (k + 1)) : (α j)⁻¹ ≤ Q := by
      have he := Finset.single_le_sum
        (fun l _ ↦ inv_nonneg.mpr (hα l).le) hj
      dsimp only [Q]
      linarith
    let Cj (j : ℕ) : ℝ := B j ^ 2 * (j + 1 : ℕ) * Q
    let Dj (j : ℕ) : ℝ := β j * Fintype.card (Fin j → Fin n) * E j ^ 2 * (j + 1 : ℕ)
    have hCj (j : ℕ) : 0 ≤ Cj j :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hQ.le
    have hDj (j : ℕ) : 0 ≤ Dj j :=
      mul_nonneg (mul_nonneg (mul_nonneg (hβ j).le (Nat.cast_nonneg _)) (sq_nonneg _))
        (Nat.cast_nonneg _)
    let C : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), Cj j
    let D : ℝ := 1 + ∑ j ∈ Finset.range (k + 1), Dj j
    have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun j _ ↦ hCj j))
    have hD : 0 < D := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun j _ ↦ hDj j))
    refine ⟨C, D, hC, hD, fun u x hx ↦ ?_⟩
    let SN : ℝ := ∑ j ∈ Finset.range (k + 1), N j u x
    let SJ : ℝ := ∑ j ∈ Finset.range (k + 1), J j u x ^ 2
    have hSN : 0 ≤ SN := Finset.sum_nonneg (fun j _ ↦ hN j u x hx)
    have hSJ : 0 ≤ SJ := Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)
    have hxK : c x ∈ c '' tsupport (L.cutoff a) := ⟨x, hx, rfl⟩
    -- Each localized ordinary derivative is controlled by the same tensor lengths.
    have hf (j : ℕ) (hj : j ∈ Finset.range (k + 1)) : J j u x ^ 2 ≤ Cj j * SN := by
      have hbase := hforward j u (c x) hxK
      have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hB j)
        (Finset.sum_nonneg (fun l _ ↦ norm_nonneg _)))).mpr hbase
      rw [mul_pow] at hsq
      have hsum : (∑ l ∈ Finset.range (j + 1), ‖F l u x‖) ^ 2 ≤
          (j + 1 : ℕ) * ∑ l ∈ Finset.range (j + 1), ‖F l u x‖ ^ 2 := by
        simpa only [Finset.card_range] using
          (sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := fun l ↦ ‖F l u x‖))
      have harr : (∑ l ∈ Finset.range (j + 1), ‖F l u x‖ ^ 2) ≤ Q * SN := by
        have hsub : Finset.range (j + 1) ⊆ Finset.range (k + 1) :=
          Finset.range_mono (by have := Finset.mem_range.mp hj; omega)
        apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ ↦ sq_nonneg _))
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        have hbound : (∑ p, ‖F l u x p‖ ^ 2) ≤ (α l)⁻¹ * N l u x := by
          exact (le_inv_mul_iff₀ (hα l)).mpr (hmetricF l u x hx).1
        exact ((hpi l u x).trans hbound).trans
          (mul_le_mul_of_nonneg_right (hinv l hl) (hN l u x hx))
      calc
        J j u x ^ 2 ≤ B j ^ 2 * (∑ l ∈ Finset.range (j + 1), ‖F l u x‖) ^ 2 := hsq
        _ ≤ B j ^ 2 * ((j + 1 : ℕ) * (Q * SN)) := mul_le_mul_of_nonneg_left
          (hsum.trans (mul_le_mul_of_nonneg_left harr (Nat.cast_nonneg _))) (sq_nonneg _)
        _ = Cj j * SN := by dsimp only [Cj]; ring
    -- Conversely apply the metric upper bound to the same actual cutoff section.
    have hr (j : ℕ) (hj : j ∈ Finset.range (k + 1)) :
        N j (L.cutoffSection a u) x ≤ Dj j * SJ := by
      have hbase := hreverse j u (c x) hxK
      have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hE j)
        (Finset.sum_nonneg (fun l _ ↦ norm_nonneg _)))).mpr hbase
      rw [mul_pow] at hsq
      have hsum : (∑ l ∈ Finset.range (j + 1), J l u x) ^ 2 ≤
          (j + 1 : ℕ) * SJ := by
        apply (show (∑ l ∈ Finset.range (j + 1), J l u x) ^ 2 ≤
            (j + 1 : ℕ) * ∑ l ∈ Finset.range (j + 1), J l u x ^ 2 by
          simpa only [Finset.card_range] using
            (sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := fun l ↦ J l u x))).trans
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by have := Finset.mem_range.mp hj; omega))
          (fun _ _ _ ↦ sq_nonneg _)
      calc
        N j (L.cutoffSection a u) x ≤
            β j * (∑ p, ‖F j (L.cutoffSection a u) x p‖ ^ 2) :=
          (hmetricF j (L.cutoffSection a u) x hx).2
        _ ≤ β j * ((Fintype.card (Fin j → Fin n) : ℝ) *
            (E j ^ 2 * ((j + 1 : ℕ) * SJ))) := by
          apply mul_le_mul_of_nonneg_left _ (hβ j).le
          apply (hpiUpper j (L.cutoffSection a u) x).trans
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact hsq.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
        _ = Dj j * SJ := by dsimp only [Dj]; ring
    constructor
    · change SJ ≤ C * SN
      calc
        SJ ≤ ∑ j ∈ Finset.range (k + 1), Cj j * SN := Finset.sum_le_sum hf
        _ = (∑ j ∈ Finset.range (k + 1), Cj j) * SN := (Finset.sum_mul ..).symm
        _ ≤ C * SN := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hSN
    · change (∑ j ∈ Finset.range (k + 1), N j (L.cutoffSection a u) x) ≤ D * SJ
      calc
        _ ≤ ∑ j ∈ Finset.range (k + 1), Dj j * SJ := Finset.sum_le_sum hr
        _ = (∑ j ∈ Finset.range (k + 1), Dj j) * SJ := (Finset.sum_mul ..).symm
        _ ≤ D * SJ := mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) hSJ
  -- Integrate the inequalities, then pass from squared energies to norms.
  have hscalarComparison
      (μ : Measure M) (m : ℕ)
      (T : S₀ → M → ℝ) (F : Fin m → S₀ → M → ℝ) (v : Fin m → S₀ → S₀)
      (J : Fin m → S₀ → ℝ) (N : S₀ → ℝ)
      (hT : ∀ u, Integrable (T u) μ) (hTpos : ∀ u x, 0 ≤ T u x)
      (hF : ∀ a u, Integrable (F a u) μ) (hJ : ∀ a u, 0 ≤ J a u)
      (hN : ∀ u, 0 ≤ N u)
      (A B C D : Fin m → ℝ)
      (hA : ∀ a, 0 < A a) (hB : ∀ a, 0 < B a)
      (hC : ∀ a, 0 < C a) (hD : ∀ a, 0 < D a)
      (hchart : ∀ a u, A a * J a u ≤ ∫ x, F a u x ∂μ ∧
        (∫ x, F a u x ∂μ) ≤ B a * J a u)
      (hforward : ∀ a u x, F a u x ≤ C a * T u x)
      (hreverse : ∀ a u x, T (v a u) x ≤ D a * F a u x)
      (hpartition : ∀ u x, T u x ≤ (m : ℝ) * ∑ a, T (v a u) x)
      (c₁ C₁ : ℝ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
      (hFourier : ∀ u, c₁ * (∑ a, J a u) ≤ N u ^ 2 ∧
        N u ^ 2 ≤ C₁ * (∑ a, J a u)) :
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u,
        c * N u ≤ Real.sqrt (∫ x, T u x ∂μ) ∧
          Real.sqrt (∫ x, T u x ∂μ) ≤ C * N u := by
    let G (u : S₀) : ℝ := ∫ x, T u x ∂μ
    have hG (u : S₀) : 0 ≤ G u := integral_nonneg (hTpos u)
    let P : ℝ := 1 + ∑ a, (A a)⁻¹ * C a
    let Q : ℝ := 1 + (m : ℝ) * (1 + ∑ a, D a * B a)
    have hP : 0 < P := add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun a _ ↦ mul_nonneg (inv_nonneg.mpr (hA a).le) (hC a).le))
    have hQ : 0 < Q := by
      apply add_pos_of_pos_of_nonneg zero_lt_one
      apply mul_nonneg (Nat.cast_nonneg m)
      exact add_nonneg zero_le_one
        (Finset.sum_nonneg (fun a _ ↦ mul_nonneg (hD a).le (hB a).le))
    -- Integrate the two local estimates, always with the original integrable functions.
    have hleft (u : S₀) : (∑ a, J a u) ≤ P * G u := by
      have hpiece (a : Fin m) : J a u ≤ ((A a)⁻¹ * C a) * G u := by
        have hi : A a * J a u ≤ C a * G u := (hchart a u).1.trans (by
          simpa only [G, integral_const_mul] using
            integral_mono (hF a u) ((hT u).const_mul (C a)) (hforward a u))
        calc
          J a u = (A a)⁻¹ * (A a * J a u) := by
            rw [← mul_assoc, inv_mul_cancel₀ (hA a).ne', one_mul]
          _ ≤ (A a)⁻¹ * (C a * G u) :=
            mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (hA a).le)
          _ = _ := (mul_assoc _ _ _).symm
      calc
        _ ≤ ∑ a, ((A a)⁻¹ * C a) * G u := Finset.sum_le_sum (fun a _ ↦ hpiece a)
        _ = (∑ a, (A a)⁻¹ * C a) * G u := by rw [Finset.sum_mul]
        _ ≤ P * G u := mul_le_mul_of_nonneg_right (by dsimp [P]; linarith) (hG u)
    have hright (u : S₀) : G u ≤ Q * (∑ a, J a u) := by
      have hpiece (a : Fin m) : G (v a u) ≤ (D a * B a) * J a u := by
        calc
          _ ≤ D a * (∫ x, F a u x ∂μ) := by
            simpa only [G, integral_const_mul] using
              integral_mono (hT (v a u)) ((hF a u).const_mul (D a)) (hreverse a u)
          _ ≤ D a * (B a * J a u) :=
            mul_le_mul_of_nonneg_left (hchart a u).2 (hD a).le
          _ = _ := (mul_assoc _ _ _).symm
      have hcoeff (a : Fin m) : D a * B a ≤ 1 + ∑ b, D b * B b := by
        have hs := Finset.single_le_sum
          (fun b _ ↦ mul_nonneg (hD b).le (hB b).le) (Finset.mem_univ a)
        linarith
      have hsum : (∑ a, G (v a u)) ≤ (1 + ∑ a, D a * B a) * ∑ a, J a u := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun a _ ↦ (hpiece a).trans
          (mul_le_mul_of_nonneg_right (hcoeff a) (hJ a u)))
      calc
        G u ≤ (m : ℝ) * ∑ a, G (v a u) := by
          have hi := integral_mono (hT u)
            ((integrable_finsetSum Finset.univ (fun a _ ↦ hT (v a u))).const_mul (m : ℝ))
            (hpartition u)
          simpa only [G, integral_const_mul,
            integral_finsetSum Finset.univ (fun a _ ↦ hT (v a u))] using hi
        _ ≤ (m : ℝ) * ((1 + ∑ a, D a * B a) * ∑ a, J a u) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg m)
        _ ≤ Q * ∑ a, J a u := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (by dsimp [Q]; linarith)
            (Finset.sum_nonneg (fun a _ ↦ hJ a u))
    -- Positive square roots turn the squared energy comparison into the original norm bounds.
    let c : ℝ := Real.sqrt (C₁ * P)⁻¹
    let C : ℝ := Real.sqrt (Q * c₁⁻¹)
    have hc : 0 < c := Real.sqrt_pos.mpr (inv_pos.mpr (mul_pos hC₁ hP))
    have hCpos : 0 < C := Real.sqrt_pos.mpr (mul_pos hQ (inv_pos.mpr hc₁))
    refine ⟨c, C, hc, hCpos, fun u ↦ ?_⟩
    constructor
    · apply (sq_le_sq₀ (mul_nonneg hc.le (hN u)) (Real.sqrt_nonneg _)).mp
      rw [mul_pow, Real.sq_sqrt (hG u)]
      have hc_sq : c ^ 2 = (C₁ * P)⁻¹ := Real.sq_sqrt (inv_nonneg.mpr (mul_pos hC₁ hP).le)
      rw [hc_sq]
      have hi : N u ^ 2 ≤ (C₁ * P) * G u :=
        (hFourier u).2.trans (by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hleft u) hC₁.le)
      calc
        _ ≤ (C₁ * P)⁻¹ * ((C₁ * P) * G u) :=
          mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (mul_pos hC₁ hP).le)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (mul_pos hC₁ hP).ne', one_mul]
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hCpos.le (hN u))).mp
      rw [Real.sq_sqrt (hG u), mul_pow]
      have hC_sq : C ^ 2 = Q * c₁⁻¹ := Real.sq_sqrt (mul_nonneg hQ.le (inv_nonneg.mpr hc₁.le))
      rw [hC_sq]
      have hi : (∑ a, J a u) ≤ c₁⁻¹ * N u ^ 2 := by
        calc
          _ = c₁⁻¹ * (c₁ * ∑ a, J a u) := by
            rw [← mul_assoc, inv_mul_cancel₀ hc₁.ne', one_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hFourier u).1 (inv_nonneg.mpr hc₁.le)
      exact (hright u).trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hi hQ.le)
  -- Apply the local facts to the original presentation and specified integer order.
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  -- Keep the original tensor contraction, with one power of the original partition weight.
  let T₀ (j : ℕ) (u : A.smoothSections) (x : M) : ℝ :=
    ∑ a : Fin L.size, L.cutoff a x *
      cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
        (L.frameIndex a) g h j u x
  let T (u : A.smoothSections) (x : M) : ℝ := ∑ j ∈ Finset.range (k + 1), T₀ j u x
  obtain ⟨hTsum, hTsupport, hTeq⟩ := hglobalTensor L cov covT hcovT g h
  have hweighted := hweightedEnergy L μ cov covT hcovT g h hh
  have hT₀pos (j : ℕ) (u : A.smoothSections) (x : M) : 0 ≤ T₀ j u x :=
    Finset.sum_nonneg (fun a _ ↦ (hweighted a j u).1 x)
  have hT₀int (j : ℕ) (u : A.smoothSections) : Integrable (T₀ j u) μ :=
    integrable_finsetSum Finset.univ (fun a _ ↦ (hweighted a j u).2.2)
  have hTint (u : A.smoothSections) : Integrable (T u) μ :=
    integrable_finsetSum (Finset.range (k + 1)) (fun j _ ↦ hT₀int j u)
  have hTpos (u : A.smoothSections) (x : M) : 0 ≤ T u x :=
    Finset.sum_nonneg (fun j _ ↦ hT₀pos j u x)
  have hTlocal (a : Fin L.size) (u : A.smoothSections) (x : M)
      (hx : x ∈ tsupport (L.cutoff a)) :
      T u x = ∑ j ∈ Finset.range (k + 1),
        cov.localCovariantDerivativeNormSq covT (L.chart a) (L.chart_mem_atlas a)
          (L.frameIndex a) g h j u x := by
    apply Finset.sum_congr rfl
    intro j _
    exact hTeq (L.chart a) (L.chart_mem_atlas a) (L.frameIndex a) j u x
      (L.support_subset a hx)
  have hTzero (a : Fin L.size) (u : A.smoothSections) (x : M)
      (hx : x ∉ tsupport (L.cutoff a)) : T (L.cutoffSection a u) x = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hTsupport a j u h))
  have hpartition (u : A.smoothSections) (x : M) :
      T u x ≤ (L.size : ℝ) * ∑ a, T (L.cutoffSection a u) x := by
    calc
      T u x = ∑ j ∈ Finset.range (k + 1), T₀ j (∑ a, L.cutoffSection a u) x := by
        rw [L.sum_cutoffSection]
      _ ≤ ∑ j ∈ Finset.range (k + 1),
          (L.size : ℝ) * ∑ a, T₀ j (L.cutoffSection a u) x :=
        Finset.sum_le_sum (fun j _ ↦ hTsum L.size j (fun a ↦ L.cutoffSection a u) x)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  -- Ordinary derivative energy has fixed compact coordinate support at every order.
  let f (a : Fin L.size) (u : A.smoothSections) (z : H) : ℝ :=
    ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j (L.localizedFunction a u) z‖ ^ 2
  have hfpos (a : Fin L.size) (u : A.smoothSections) (z : H) : 0 ≤ f a u z :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hdercont (a : Fin L.size) (u : A.smoothSections) (j : ℕ) :
      Continuous (fun z ↦ ‖iteratedFDeriv ℝ j (L.localizedFunction a u) z‖ ^ 2) :=
    ((L.localizedFunction_properties a u).1.continuous_iteratedFDeriv (by simp)).norm.pow 2
  have hderint (a : Fin L.size) (u : A.smoothSections) (j : ℕ) :
      Integrable (fun z ↦ ‖iteratedFDeriv ℝ j (L.localizedFunction a u) z‖ ^ 2) := by
    have hs := ((L.localizedFunction_properties a u).2.2.iteratedFDeriv (𝕜 := ℝ) j).norm
    exact (hdercont a u j).integrable_of_hasCompactSupport (by
      simpa only [Pi.mul_def, pow_two] using hs.mul_right)
  have hfcont (a : Fin L.size) (u : A.smoothSections) : Continuous (f a u) :=
    continuous_finsetSum _ (fun j _ ↦ hdercont a u j)
  have hfsupport (a : Fin L.size) (u : A.smoothSections) :
      tsupport (f a u) ⊆ (L.chart a) '' tsupport (L.cutoff a) := by
    have hK := (L.compact_support a).image_of_continuousOn
      ((L.chart a).continuousOn.mono (fun _ hx ↦ (L.support_subset a hx).1))
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzc
    apply hz
    apply Finset.sum_eq_zero
    intro j _
    have hzder : z ∉ tsupport (iteratedFDeriv ℝ j (L.localizedFunction a u)) := by
      intro hd
      exact hzc ((L.localizedFunction_properties a u).2.1
        (tsupport_iteratedFDeriv_subset j hd))
    rw [image_eq_zero_of_notMem_tsupport hzder, norm_zero, zero_pow (by decide)]
  let F (a : Fin L.size) (u : A.smoothSections) : M → ℝ :=
    (L.chart a).source.indicator (fun x ↦ f a u (L.chart a x))
  let J (a : Fin L.size) (u : A.smoothSections) : ℝ := ∫ z, f a u z
  have hJpos (a : Fin L.size) (u : A.smoothSections) : 0 ≤ J a u :=
    integral_nonneg (hfpos a u)
  -- The given smooth positive density transports the same compactly supported functions.
  have hchart (a : Fin L.size) := hchartTransport μ (L.chart a) (L.chart_mem_atlas a)
    (tsupport (L.cutoff a)) (L.compact_support a) (fun _ hx ↦ (L.support_subset a hx).1)
  choose A₀ B₀ hA₀ hB₀ hchart using hchart
  have hFproperties (a : Fin L.size) (u : A.smoothSections) :
      Continuous (F a u) ∧ tsupport (F a u) ⊆ tsupport (L.cutoff a) ∧
      A₀ a * J a u ≤ ∫ x, F a u x ∂μ ∧ (∫ x, F a u x ∂μ) ≤ B₀ a * J a u :=
    hchart a (f a u) (hfcont a u) (hfsupport a u) (hfpos a u)
  have hFint (a : Fin L.size) (u : A.smoothSections) : Integrable (F a u) μ :=
    (hFproperties a u).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have henergy (a : Fin L.size) := hcompactEnergy L cov covT hcovT g h hh a k
  choose C₀ D₀ hC₀ hD₀ henergy using henergy
  have hforward (a : Fin L.size) (u : A.smoothSections) (x : M) :
      F a u x ≤ C₀ a * T u x := by
    by_cases hx : x ∈ tsupport (L.cutoff a)
    · rw [show F a u x = f a u (L.chart a x) from
        Set.indicator_of_mem (L.support_subset a hx).1 _, hTlocal a u x hx]
      exact (henergy a u x hx).1
    · rw [image_eq_zero_of_notMem_tsupport (fun hf ↦ hx ((hFproperties a u).2.1 hf))]
      exact mul_nonneg (hC₀ a).le (hTpos u x)
  have hreverse (a : Fin L.size) (u : A.smoothSections) (x : M) :
      T (L.cutoffSection a u) x ≤ D₀ a * F a u x := by
    by_cases hx : x ∈ tsupport (L.cutoff a)
    · rw [show F a u x = f a u (L.chart a x) from
        Set.indicator_of_mem (L.support_subset a hx).1 _, hTlocal a _ x hx]
      exact (henergy a u x hx).2
    · rw [hTzero a u x hx,
        image_eq_zero_of_notMem_tsupport (fun hf ↦ hx ((hFproperties a u).2.1 hf)), mul_zero]
  -- Plancherel applies to these actual localized functions with their existing Fourier convention.
  obtain ⟨c₁, C₁, hc₁, hC₁, hFourier⟩ :=
    L.exists_norm_smoothToSobolev_sq_derivatives_comparison k
  have hJintegral (a : Fin L.size) (u : A.smoothSections) :
      J a u = ∑ j : Fin (k + 1),
        ∫ z, ‖iteratedFDeriv ℝ j.val (L.localizedFunction a u) z‖ ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
      ∫ z, ‖iteratedFDeriv ℝ j (L.localizedFunction a u) z‖ ^ 2)]
    exact integral_finsetSum _ (fun j _ ↦ hderint a u j)
  have hfourier (u : A.smoothSections) :
      c₁ * (∑ a, J a u) ≤ ‖L.smoothToSobolev (k : ℝ) u‖ ^ 2 ∧
        ‖L.smoothToSobolev (k : ℝ) u‖ ^ 2 ≤ C₁ * (∑ a, J a u) := by
    simpa only [hJintegral] using hFourier u
  obtain ⟨c, C, hc, hC, hbound⟩ := hscalarComparison μ L.size T F
    (fun a ↦ L.cutoffSection a) J (fun u ↦ ‖L.smoothToSobolev (k : ℝ) u‖)
    hTint hTpos hFint hJpos (fun _ ↦ norm_nonneg _)
    A₀ B₀ C₀ D₀ hA₀ hB₀ hC₀ hD₀ (fun a u ↦ (hFproperties a u).2.2)
    hforward hreverse hpartition c₁ C₁ hc₁ hC₁ hfourier
  -- Commuting finite sums and integrals recovers precisely the original geometric norm.
  have hnorm (u : A.smoothSections) :
      Real.sqrt (∫ x, T u x ∂μ) = L.covariantSobolevNorm μ g h cov covT k u := by
    unfold AtlasBundlePresentation.covariantSobolevNorm
    congr 1
    change (∫ x, T u x ∂μ) = ∑ j : Fin (k + 1), ∫ x, T₀ j.val u x ∂μ
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ ∫ x, T₀ j u x ∂μ)]
    exact integral_finsetSum _ (fun j _ ↦ hT₀int j u)
  exact ⟨c, C, hc, hC, fun u ↦ by simpa only [hnorm] using hbound u⟩

end AtlasBundlePresentation

end AtiyahSinger
