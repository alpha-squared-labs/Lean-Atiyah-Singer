/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasComplexConnection
public import AtiyahSinger.Geometry.AtlasFrameTransition

/-!
# Descent of connection forms from a covering family of original frames

Public module ID: M1092.

Genuine matrix gauge identities on a covering family determine smooth connection
forms in every frame of the same atlas. The construction uses local germs and
pointwise independence of the selected covering frame. It needs no Hausdorffness,
second countability, partition of unity, or extension of local sections globally.

Source: the local connection-form transformation law, Spin Geometry II.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)

local notation "H" => EuclideanSpace ℝ (Fin n)
local notation "MI" => 𝓘(ℝ, H)
local notation "V" i:max => EuclideanSpace ℂ (Fin (A.rank i))

private def descentCoord (i : A.Index) (σ : ∀ x : M, E x) (x : M) : V i :=
  (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm (A.chart i ⟨x, σ x⟩).2

private theorem descentTransition_apply (i j : A.Index) (x : M)
    (hi : x ∈ (A.chart i).baseSet) (hj : x ∈ (A.chart j).baseSet) (a : V i) :
    A.coordChangeL i j x a =
      (EuclideanSpace.equiv (Fin (A.rank j)) ℂ).symm
        (A.frameLinearEquiv j x hj ((A.frameLinearEquiv i x hi).symm
          (EuclideanSpace.equiv (Fin (A.rank i)) ℂ a))) := by
  have h := A.coordChangeL_apply i j x ⟨hi, hj⟩
    ((A.frameLinearEquiv i x hi).symm (EuclideanSpace.equiv (Fin (A.rank i)) ℂ a))
  change _ = A.coordChangeL i j x
    ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
      (A.frameLinearEquiv i x hi ((A.frameLinearEquiv i x hi).symm
        (EuclideanSpace.equiv (Fin (A.rank i)) ℂ a)))) at h
  rw [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

private theorem descentTransition_smooth (i j : A.Index) :
    ContMDiffOn MI 𝓘(ℝ, V i →L[ℂ] V j) ∞ (A.coordChangeL i j)
      ((A.chart i).baseSet ∩ (A.chart j).baseSet) := by
  apply contMDiffOn_finsetSum
  intro a _
  let e := EuclideanSpace.equiv (Fin (A.rank j)) ℂ
  have hc := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
    |>.comp_contMDiffOn (A.contMDiffOn_coordChange i j a)
  exact ((ContinuousLinearMap.smulRightL ℂ (V i) (V j)
    ((ContinuousLinearMap.proj a).comp
      (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toContinuousLinearMap)).restrictScalars ℝ).contMDiff
    |>.comp_contMDiffOn hc

private theorem descentCoord_smooth (i : A.Index) (u : A.smoothSections)
    (x : M) (hx : x ∈ (A.chart i).baseSet) :
    ContMDiffAt MI 𝓘(ℝ, V i) ∞ (descentCoord A i u.val) x :=
  ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
    |>.contMDiffAt.comp x ((u.property i).contMDiffAt ((A.chart i).open_baseSet.mem_nhds hx))

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

private theorem descentChart_derivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
    (f : M → F) (x : M) (hx : x ∈ c.source)
    (hf : MDifferentiableAt MI 𝓘(ℝ, F) f x) (v : TangentSpace MI x) :
    fderiv ℝ (fun z ↦ f (c.symm z)) (c x) (mfderiv MI MI c x v) =
      mvfderiv MI f x v := by
  have hchart := mdifferentiable_of_mem_atlas (I := MI) hc
  have hc' := hchart.mdifferentiableAt_symm (c.map_source hx)
  have hchain := mvfderiv_comp (I := MI) (I' := MI) (c x)
    (by simpa only [c.left_inv hx] using hf) hc'
  rw [mvfderiv_eq_fderiv, c.left_inv hx] at hchain
  have hlocal : fderiv ℝ (fun z ↦ f (c.symm z)) (c x) =
      (mvfderiv MI f x).comp (mfderiv MI MI c.symm (c x)) := hchain
  rw [hlocal]
  change (mvfderiv MI f x) (((mfderiv MI MI c.symm (c x)).comp (mfderiv MI MI c x)) v) = _
  rw [hchart.symm_comp_deriv hx]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descentCoord_change (i j : A.Index) (σ : ∀ x : M, E x)
    (x : M) (hi : x ∈ (A.chart i).baseSet) (hj : x ∈ (A.chart j).baseSet)
    (hσ : ContMDiffAt MI 𝓘(ℝ, V i) ∞ (descentCoord A i σ) x) :
    ContMDiffAt MI 𝓘(ℝ, V j) ∞ (descentCoord A j σ) x ∧
      ∀ v : TangentSpace MI x,
        mvfderiv MI (descentCoord A j σ) x v =
          A.coordChangeL i j x (mvfderiv MI (descentCoord A i σ) x v) +
            (mvfderiv MI (A.coordChangeL i j) x v) (descentCoord A i σ x) := by
  let T := A.coordChangeL i j
  have hT := (descentTransition_smooth A i j).contMDiffAt
    (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds ⟨hi, hj⟩)
  have heq : descentCoord A j σ =ᶠ[nhds x] (fun y ↦ T y (descentCoord A i σ y)) := by
    filter_upwards [(A.chart i).open_baseSet.mem_nhds hi,
      (A.chart j).open_baseSet.mem_nhds hj] with y hyi hyj
    exact A.coordChangeL_apply i j y ⟨hyi, hyj⟩ (σ y)
  let R := ContinuousLinearMap.restrictScalarsL ℂ (V i) (V j) ℝ ℝ
  have hTR := R.contMDiff.contMDiffAt.comp x hT
  have hprod := hTR.clm_apply hσ
  have hjσ := hprod.congr_of_eventuallyEq heq
  refine ⟨hjσ, ?_⟩
  intro v
  let c := chartAt H x
  have hc : c ∈ atlas H M := chart_mem_atlas _ _
  have hx : x ∈ c.source := mem_chart_source _ _
  let a := fun z ↦ descentCoord A i σ (c.symm z)
  let b := fun z ↦ T (c.symm z)
  have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
    (I := MI) (n := ∞) (IsManifold.subset_maximalAtlas hc) (c.map_source hx)
  have ha : DifferentiableAt ℝ a (c x) :=
    (contMDiffAt_iff_contDiffAt.mp
      (hσ.comp_of_eq hsymm (c.left_inv hx))).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ b (c x) :=
    (contMDiffAt_iff_contDiffAt.mp
      (hT.comp_of_eq hsymm (c.left_inv hx))).differentiableAt (by simp)
  have hnear : (fun z ↦ descentCoord A j σ (c.symm z)) =ᶠ[nhds (c x)]
      (fun z ↦ b z (a z)) := by
    exact heq.comp_tendsto (by simpa only [ContinuousAt, c.left_inv hx] using hsymm.continuousAt)
  have hder := congrArg (fun L ↦ L (mfderiv MI MI c x v))
    (hnear.fderiv_eq.trans ((R.hasFDerivAt.comp (c x) hb.hasFDerivAt).clm_apply
      ha.hasFDerivAt).fderiv)
  change fderiv ℝ (fun z ↦ descentCoord A j σ (c.symm z)) (c x)
      (mfderiv MI MI c x v) =
    b (c x) (fderiv ℝ a (c x) (mfderiv MI MI c x v)) +
      fderiv ℝ b (c x) (mfderiv MI MI c x v) (a (c x)) at hder
  rw [descentChart_derivative c hc _ x hx (hjσ.mdifferentiableAt (by simp)) v] at hder
  have ha' := descentChart_derivative c hc (descentCoord A i σ) x hx
    (hσ.mdifferentiableAt (by simp)) v
  have hb' := descentChart_derivative c hc T x hx (hT.mdifferentiableAt (by simp)) v
  change _ = T (c.symm (c x))
    (fderiv ℝ a (c x) (mfderiv MI MI c x v)) +
      fderiv ℝ b (c x) (mfderiv MI MI c x v) (descentCoord A i σ (c.symm (c x))) at hder
  rw [c.left_inv hx, ha', hb'] at hder
  exact hder

-- All values below live in the original fiber, including for merely local section germs.
private def descentValue (c : OpenPartialHomeomorph M H) (i : A.Index)
    (Γ : H → H →L[ℝ] (V i →L[ℂ] V i)) (σ : ∀ x : M, E x)
    (x : M) (hx : x ∈ (A.chart i).baseSet) (v : TangentSpace MI x) : E x :=
  (A.frameLinearEquiv i x hx).symm
    (EuclideanSpace.equiv (Fin (A.rank i)) ℂ
      (mvfderiv MI (descentCoord A i σ) x v +
        Γ (c x) (mfderiv MI MI c x v) (descentCoord A i σ x)))

private theorem descentValue_expression (c : OpenPartialHomeomorph M H)
    (hc : c ∈ atlas H M) (i : A.Index) (Γ : H → H →L[ℝ] (V i →L[ℂ] V i))
    (u : A.smoothSections) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
    (v : TangentSpace MI x) :
    descentValue A c i Γ u.val x hx.2 v =
      atlasConnectionExpression A c i Γ u x hx.2 v := by
  have h := descentChart_derivative c hc (descentCoord A i u.val) x hx.1
    ((descentCoord_smooth A i u x hx.2).mdifferentiableAt (by simp)) v
  change _ = (A.frameLinearEquiv i x hx.2).symm
    (EuclideanSpace.equiv (Fin (A.rank i)) ℂ
      (fderiv ℝ (fun z ↦ descentCoord A i u.val (c.symm z)) (c x)
        (mfderiv MI MI c x v) +
          Γ (c x) (mfderiv MI MI c x v) (descentCoord A i u.val (c.symm (c x)))))
  rw [h, c.left_inv hx.1]
  rfl

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] in
private theorem descentTransition_inverse (i j : A.Index) (x : M)
    (hi : x ∈ (A.chart i).baseSet) (hj : x ∈ (A.chart j).baseSet) (a : V i) :
    A.coordChangeL j i x (A.coordChangeL i j x a) = a := by
  rw [descentTransition_apply A i j x hi hj, descentTransition_apply A j i x hj hi,
    ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descentValue_gauge (c d : OpenPartialHomeomorph M H) (i j : A.Index)
    (Γ : H → H →L[ℝ] (V i →L[ℂ] V i)) (Δ : H → H →L[ℝ] (V j →L[ℂ] V j))
    (σ : ∀ x : M, E x) (x : M) (hi : x ∈ (A.chart i).baseSet)
    (hj : x ∈ (A.chart j).baseSet)
    (hσ : ContMDiffAt MI 𝓘(ℝ, V i) ∞ (descentCoord A i σ) x)
    (v : TangentSpace MI x)
    (hgauge : ∀ a : V i,
      Δ (d x) (mfderiv MI MI d x v) (A.coordChangeL i j x a) +
        (mvfderiv MI (A.coordChangeL i j) x v) a =
          A.coordChangeL i j x (Γ (c x) (mfderiv MI MI c x v) a)) :
    descentValue A c i Γ σ x hi v = descentValue A d j Δ σ x hj v := by
  have hchange := descentCoord_change A i j σ x hi hj hσ
  have hcoord : descentCoord A j σ x = A.coordChangeL i j x (descentCoord A i σ x) :=
    A.coordChangeL_apply i j x ⟨hi, hj⟩ (σ x)
  apply (A.frameLinearEquiv j x hj).injective
  apply (EuclideanSpace.equiv (Fin (A.rank j)) ℂ).symm.injective
  change (EuclideanSpace.equiv (Fin (A.rank j)) ℂ).symm
    (A.frameLinearEquiv j x hj ((A.frameLinearEquiv i x hi).symm
      (EuclideanSpace.equiv (Fin (A.rank i)) ℂ
        (mvfderiv MI (descentCoord A i σ) x v +
          Γ (c x) (mfderiv MI MI c x v) (descentCoord A i σ x))))) = _
  rw [← descentTransition_apply A i j x hi hj]
  simp only [descentValue, LinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  change A.coordChangeL i j x
    (mvfderiv MI (descentCoord A i σ) x v +
      Γ (c x) (mfderiv MI MI c x v) (descentCoord A i σ x)) =
    mvfderiv MI (descentCoord A j σ) x v +
      Δ (d x) (mfderiv MI MI d x v) (descentCoord A j σ x)
  rw [map_add, hchange.2 v, hcoord, ← hgauge]
  abel

private def descentTransportForm (c : OpenPartialHomeomorph M H) (i j : A.Index)
    (Γ : H → H →L[ℝ] (V j →L[ℂ] V j)) (z : H) : H →L[ℝ] (V i →L[ℂ] V i) :=
  ((ContinuousLinearMap.compL ℂ (V i) (V j) (V i)
    (A.coordChangeL j i (c.symm z))).restrictScalars ℝ).comp
      (fderiv ℝ (fun w ↦ A.coordChangeL i j (c.symm w)) z +
        ((((ContinuousLinearMap.compL ℂ (V i) (V j) (V j)).flip
          (A.coordChangeL i j (c.symm z))).restrictScalars ℝ).comp (Γ z)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descentValue_transport (c : OpenPartialHomeomorph M H)
    (hc : c ∈ atlas H M) (i j : A.Index)
    (Γ : H → H →L[ℝ] (V j →L[ℂ] V j)) (σ : ∀ x : M, E x)
    (x : M) (hx : x ∈ c.source) (hi : x ∈ (A.chart i).baseSet)
    (hj : x ∈ (A.chart j).baseSet)
    (hσ : ContMDiffAt MI 𝓘(ℝ, V i) ∞ (descentCoord A i σ) x)
    (v : TangentSpace MI x) :
    descentValue A c i (descentTransportForm A c i j Γ) σ x hi v =
      descentValue A c j Γ σ x hj v := by
  have hchange := descentCoord_change A i j σ x hi hj hσ
  have hcoord : descentCoord A j σ x = A.coordChangeL i j x (descentCoord A i σ x) :=
    A.coordChangeL_apply i j x ⟨hi, hj⟩ (σ x)
  have hT := (descentTransition_smooth A i j).contMDiffAt
    (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds ⟨hi, hj⟩)
  have hD := descentChart_derivative c hc (A.coordChangeL i j) x hx
    (hT.mdifferentiableAt (by simp)) v
  have hform (a : V i) :
      descentTransportForm A c i j Γ (c x) (mfderiv MI MI c x v) a =
        A.coordChangeL j i x ((mvfderiv MI (A.coordChangeL i j) x v) a +
          Γ (c x) (mfderiv MI MI c x v) (A.coordChangeL i j x a)) := by
    change A.coordChangeL j i (c.symm (c x))
      (fderiv ℝ (fun z ↦ A.coordChangeL i j (c.symm z)) (c x)
        (mfderiv MI MI c x v) a +
          Γ (c x) (mfderiv MI MI c x v) (A.coordChangeL i j (c.symm (c x)) a)) = _
    rw [c.left_inv hx, hD]
  apply (A.frameLinearEquiv j x hj).injective
  apply (EuclideanSpace.equiv (Fin (A.rank j)) ℂ).symm.injective
  change (EuclideanSpace.equiv (Fin (A.rank j)) ℂ).symm
    (A.frameLinearEquiv j x hj ((A.frameLinearEquiv i x hi).symm
      (EuclideanSpace.equiv (Fin (A.rank i)) ℂ
        (mvfderiv MI (descentCoord A i σ) x v +
          descentTransportForm A c i j Γ (c x) (mfderiv MI MI c x v)
            (descentCoord A i σ x))))) = _
  rw [← descentTransition_apply A i j x hi hj]
  simp only [descentValue, LinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  change A.coordChangeL i j x
    (mvfderiv MI (descentCoord A i σ) x v +
      descentTransportForm A c i j Γ (c x) (mfderiv MI MI c x v)
        (descentCoord A i σ x)) =
    mvfderiv MI (descentCoord A j σ) x v +
      Γ (c x) (mfderiv MI MI c x v) (descentCoord A j σ x)
  rw [hform, map_add, descentTransition_inverse A j i x hj hi, hchange.2 v, hcoord]
  abel

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descentTransportForm_smooth (c : OpenPartialHomeomorph M H)
    (hc : c ∈ atlas H M) (i j : A.Index)
    (Γ : H → H →L[ℝ] (V j →L[ℂ] V j))
    (hΓ : ContDiffOn ℝ ∞ Γ (c.target ∩ c.symm ⁻¹' (A.chart j).baseSet))
    (z : H) (hz : z ∈ c.target ∩ c.symm ⁻¹' ((A.chart i).baseSet ∩ (A.chart j).baseSet)) :
    ContDiffAt ℝ ∞ (descentTransportForm A c i j Γ) z := by
  have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
    (I := MI) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
  have hij := ((descentTransition_smooth A i j).contMDiffAt
    (((A.chart i).open_baseSet.inter (A.chart j).open_baseSet).mem_nhds hz.2)).comp z hsymm
  have hji := ((descentTransition_smooth A j i).contMDiffAt
    (((A.chart j).open_baseSet.inter (A.chart i).open_baseSet).mem_nhds
      ⟨hz.2.2, hz.2.1⟩)).comp z hsymm
  have hd : ContDiffAt ℝ ∞
      (fderiv ℝ (fun w ↦ A.coordChangeL i j (c.symm w))) z :=
    (contMDiffAt_iff_contDiffAt.mp hij).fderiv_right (by simp)
  have hΓ' := hΓ.contDiffAt (Filter.inter_mem (c.open_target.mem_nhds hz.1)
    (hsymm.continuousAt.preimage_mem_nhds ((A.chart j).open_baseSet.mem_nhds hz.2.2)))
  have hout₀ := ((ContinuousLinearMap.compL ℂ (V i) (V j) (V i)).restrictScalars ℝ).contDiff
    |>.contDiffAt.comp z (contMDiffAt_iff_contDiffAt.mp hji)
  have hout := (ContinuousLinearMap.restrictScalarsL ℂ
    (V i →L[ℂ] V j) (V i →L[ℂ] V i) ℝ ℝ).contDiff.contDiffAt.comp z hout₀
  let C := ((ContinuousLinearMap.compL ℂ (V i) (V j) (V j)).flip).restrictScalars ℝ
  have hin₀ := C.contDiff.contDiffAt.comp z (contMDiffAt_iff_contDiffAt.mp hij)
  have hin := (ContinuousLinearMap.restrictScalarsL ℂ
    (V j →L[ℂ] V j) (V i →L[ℂ] V j) ℝ ℝ).contDiff.contDiffAt.comp z hin₀
  exact hout.clm_comp (hd.add (hin.clm_comp hΓ'))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem descentForm_eq_of_germs (c : OpenPartialHomeomorph M H)
    (hc : c ∈ atlas H M) (i : A.Index)
    (Γ Δ : H → H →L[ℝ] (V i →L[ℂ] V i)) (x : M)
    (hx : x ∈ c.source ∩ (A.chart i).baseSet)
    (h : ∀ (σ : ∀ y : M, E y),
      ContMDiffAt MI 𝓘(ℝ, V i) ∞ (descentCoord A i σ) x → ∀ v : TangentSpace MI x,
        descentValue A c i Γ σ x hx.2 v = descentValue A c i Δ σ x hx.2 v) :
    Γ (c x) = Δ (c x) := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro a
  -- A constant vector is realized only on this open frame; no global smooth extension is used.
  let σ (y : M) : E y := if hy : y ∈ (A.chart i).baseSet then
    (A.frameLinearEquiv i y hy).symm (EuclideanSpace.equiv (Fin (A.rank i)) ℂ a) else 0
  have hnear : descentCoord A i σ =ᶠ[nhds x] (fun _ ↦ a) := by
    filter_upwards [(A.chart i).open_baseSet.mem_nhds hx.2] with y hy
    change (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
      (A.frameLinearEquiv i y hy (σ y)) = a
    dsimp only [σ]
    rw [dite_eq_left hy, LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hσ : ContMDiffAt MI 𝓘(ℝ, V i) ∞ (descentCoord A i σ) x :=
    contMDiffAt_const.congr_of_eventuallyEq hnear
  let v : TangentSpace MI x := mfderiv MI MI c.symm (c x) w
  have hv : mfderiv MI MI c x v = w := by
    have hc' := (mdifferentiable_of_mem_atlas (I := MI) hc).comp_symm_deriv
      (c.map_source hx.1)
    rw [c.left_inv hx.1] at hc'
    exact congrArg (fun L ↦ L w) hc'
  have hh := congrArg
    (fun y ↦ (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm (A.frameLinearEquiv i x hx.2 y))
    (h σ hσ v)
  simp only [descentValue, LinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply] at hh
  rw [hv, hnear.self_of_nhds] at hh
  exact add_left_cancel hh

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Genuine gauge-compatible forms on covering original frames extend to an atlas connection. -/
theorem exists_atlasComplexConnection_of_cover_forms {J : Type*} (good : J → A.Index)
    (covers : ∀ x : M, ∃ j : J, x ∈ (A.chart (good j)).baseSet)
    (Γ : ∀ (_c : OpenPartialHomeomorph M H) (j : J), H → H →L[ℝ]
      (V (good j) →L[ℂ] V (good j)))
    (hsmooth : ∀ (c : OpenPartialHomeomorph M H), c ∈ atlas H M → ∀ j : J,
      ContDiffOn ℝ ∞ (Γ c j) (c.target ∩ c.symm ⁻¹' (A.chart (good j)).baseSet))
    (hgauge : ∀ (c d : OpenPartialHomeomorph M H),
      c ∈ atlas H M → d ∈ atlas H M → ∀ (j k : J) (x : M),
      x ∈ c.source ∩ (A.chart (good j)).baseSet →
      x ∈ d.source ∩ (A.chart (good k)).baseSet → ∀ (v : TangentSpace MI x) (a : V (good j)),
        Γ d k (d x) (mfderiv MI MI d x v) (A.coordChangeL (good j) (good k) x a) +
          (mvfderiv MI (A.coordChangeL (good j) (good k)) x v) a =
            A.coordChangeL (good j) (good k) x (Γ c j (c x) (mfderiv MI MI c x v) a)) :
    ∃ cov : AtlasComplexConnection A,
      ∀ (c : OpenPartialHomeomorph M H) (_hc : c ∈ atlas H M) (j : J)
        (u : A.smoothSections) (x : M)
        (hx : x ∈ c.source ∩ (A.chart (good j)).baseSet) (v : TangentSpace MI x),
        cov.covariantDerivative u x v =
          atlasConnectionExpression A c (good j) (Γ c j) u x hx.2 v := by
  classical
  /- Transport through any covering frame, then prove that the transported
  coefficient is independent of that choice. Local constancy of the choice is
  unnecessary: near each point its value equals one fixed smooth formula. -/
  let K (c : OpenPartialHomeomorph M H) (i : A.Index) (j : J) :=
    descentTransportForm A c i (good j) (Γ c j)
  have hK (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
      (i : A.Index) (j k : J) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
      (hj : x ∈ (A.chart (good j)).baseSet) (hk : x ∈ (A.chart (good k)).baseSet) :
      K c i j (c x) = K c i k (c x) := by
    apply descentForm_eq_of_germs A c hc i (K c i j) (K c i k) x hx
    intro σ hσ v
    have hσj := (descentCoord_change A i (good j) σ x hx.2 hj hσ).1
    exact (descentValue_transport A c hc i (good j) (Γ c j) σ x hx.1 hx.2 hj hσ v).trans
      ((descentValue_gauge A c c (good j) (good k) (Γ c j) (Γ c k) σ x hj hk hσj v
        (hgauge c c hc hc j k x ⟨hx.1, hj⟩ ⟨hx.1, hk⟩ v)).trans
        (descentValue_transport A c hc i (good k) (Γ c k) σ x hx.1 hx.2 hk hσ v).symm)
  let pick (x : M) : J := (covers x).choose
  have hpick (x : M) : x ∈ (A.chart (good (pick x))).baseSet := (covers x).choose_spec
  let Ω (c : OpenPartialHomeomorph M H) (i : A.Index) (z : H) :
      H →L[ℝ] (V i →L[ℂ] V i) :=
    if z ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet then K c i (pick (c.symm z)) z else 0
  have hΩ (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
      (i : A.Index) (j : J) (x : M) (hx : x ∈ c.source ∩ (A.chart i).baseSet)
      (hj : x ∈ (A.chart (good j)).baseSet) : Ω c i (c x) = K c i j (c x) := by
    have hv : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet :=
      ⟨c.map_source hx.1, by simpa only [Set.mem_preimage, c.left_inv hx.1] using hx.2⟩
    dsimp only [Ω]
    rw [ite_eq_left hv, c.left_inv hx.1]
    exact hK c hc i (pick x) j x hx (hpick x) hj
  -- Each glued coefficient has a fixed smooth representative on a neighborhood.
  have hΩsmooth (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M) (i : A.Index) :
      ContDiffOn ℝ ∞ (Ω c i) (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) := by
    intro z hz
    let x := c.symm z
    let j := pick x
    have hj : x ∈ (A.chart (good j)).baseSet := hpick x
    have hs := descentTransportForm_smooth A c hc i (good j) (Γ c j) (hsmooth c hc j)
      z ⟨hz.1, hz.2, hj⟩
    have hsymm := contMDiffAt_symm_of_mem_maximalAtlas
      (I := MI) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1
    have hnear : Ω c i =ᶠ[nhds z] K c i j := by
      have hframe := hsymm.continuousAt.preimage_mem_nhds
        (((A.chart i).open_baseSet.inter (A.chart (good j)).open_baseSet).mem_nhds
          ⟨hz.2, hj⟩)
      filter_upwards [c.open_target.mem_nhds hz.1, hframe] with w hw hfw
      have heq := hΩ c hc i j (c.symm w) ⟨c.map_target hw, hfw.1⟩ hfw.2
      simpa only [c.right_inv hw] using heq
    exact (hs.congr_of_eventuallyEq hnear).contDiffWithinAt
  -- Every local expression gives the supplied connection in any covering good frame.
  have hvalue (c : OpenPartialHomeomorph M H) (hc : c ∈ atlas H M)
      (i : A.Index) (j : J) (u : A.smoothSections) (x : M)
      (hx : x ∈ c.source ∩ (A.chart i).baseSet)
      (hj : x ∈ (A.chart (good j)).baseSet) (v : TangentSpace MI x) :
      atlasConnectionExpression A c i (Ω c i) u x hx.2 v =
        descentValue A c (good j) (Γ c j) u.val x hj v := by
    have heq : descentValue A c i (Ω c i) u.val x hx.2 v =
        descentValue A c i (K c i j) u.val x hx.2 v := by
      dsimp only [descentValue]
      rw [hΩ c hc i j x hx hj]
    exact (descentValue_expression A c hc i (Ω c i) u x hx v).symm.trans
      (heq.trans (descentValue_transport A c hc i (good j) (Γ c j) u.val x
        hx.1 hx.2 hj (descentCoord_smooth A i u x hx.2) v))
  let cov : AtlasComplexConnection A := {
    connectionForm := Ω
    smooth_connectionForm := hΩsmooth
    compatible := by
      intro c d hc hd i k u x hx hy v
      let j := pick x
      have hj := hpick x
      exact (hvalue c hc i j u x hx hj v).trans
        ((descentValue_gauge A c d (good j) (good j) (Γ c j) (Γ d j)
          u.val x hj hj (descentCoord_smooth A (good j) u x hj) v
          (hgauge c d hc hd j j x ⟨hx.1, hj⟩ ⟨hy.1, hj⟩ v)).trans
          (hvalue d hd k j u x hy hj v).symm) }
  refine ⟨cov, ?_⟩
  intro c hc j u x hx v
  exact (cov.covariantDerivative_eq u c hc (good j) x hx v).trans
    ((hvalue c hc (good j) j u x hx hx.2 v).trans
      (descentValue_expression A c hc (good j) (Γ c j) u x hx v))

end AtiyahSinger
