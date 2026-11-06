/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.CoordinateOperator
public import AtiyahSinger.Geometry.SpinCliffordSymbol
public import AtiyahSinger.Geometry.SpinSmoothLift
public import AtiyahSinger.Geometry.SpinorHermitianMetric
public import AtiyahSinger.Geometry.TangentDualMetric

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The original smooth cotangent half-spin Clifford symbol

Public module ID: M1413.

The supplied tangent metric fixes the original spin frames and the actual
musical inverse. Clifford multiplication is the previously constructed map
on the original associated parity quotients. Smoothness is asserted in the
same half-spin atlases selected from this very lifted frame map. The
Fourier factor i is not inserted here: this is c(sharp xi), to be used in
the actual connection contraction whose principal symbol is i times it.

Sources: Spin Geometry II.3--5, pp.93--114, and III.13.10, p.256.
Positive even rank uses the existing TopologicalSpinStructure interface.
The separate native rank-zero extension is not inferred from a two-sheeted
cover. Real linearity, smoothness, the order-one estimates, ellipticity and
skewness are proved on the original cotangent and half-spin fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold
open scoped Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

set_option maxSynthPendingDepth 40

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type _)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

/-- The positive cotangent Clifford map is the original geometric map after the same sharp. -/
def cotangentCliffordPlus :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  TopologicalSpinStructure m TM o hm hP →
    AtlasSymbolFunction (n := 2 * m) (HalfSpinorBundle m hP 0) (HalfSpinorBundle m hP 1) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S x ξ
  exact Eq.mp
    (congrArg (fun i : ZMod 2 ↦
      HalfSpinorBundle m hP 0 x →ₗ[ℂ] HalfSpinorBundle m hP i x) (zero_add 1))
    (S.cliffordParity x (g.sharp x ξ) 0)

/-- The negative-to-positive symbol is the other original parity Clifford map. -/
def cotangentCliffordMinus :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  TopologicalSpinStructure m TM o hm hP →
    AtlasSymbolFunction (n := 2 * m) (HalfSpinorBundle m hP 1) (HalfSpinorBundle m hP 0) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S x ξ
  exact Eq.mp
    (congrArg (fun i : ZMod 2 ↦
      HalfSpinorBundle m hP 1 x →ₗ[ℂ] HalfSpinorBundle m hP i x)
      (show (1 : ZMod 2) + 1 = 0 from rfl))
    (S.cliffordParity x (g.sharp x ξ) 1)

/-- The original half-spin Clifford symbol is real linear in the actual covector. -/
theorem isLinearMap_cotangentCliffordPlus :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  ∀ (S : TopologicalSpinStructure m TM o hm hP) (x : M),
    letI : Module ℝ (HalfSpinorBundle m hP 0 x →ₗ[ℂ] HalfSpinorBundle m hP 1 x) :=
      Module.compHom _ Complex.ofRealHom
    IsLinearMap ℝ (S.cotangentCliffordPlus g x) := by
  /- Fix one original principal point over x. The representative formula
  conjugates the real-linear model Clifford action through the same two
  original fiber coordinate maps. The tangent frame and sharp are real
  linear, so their composite retains addition and real scalar multiplication.
  Independence of that principal point is the original Clifford descent. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S x
  let : Module ℝ (HalfSpinorBundle m hP 0 x →ₗ[ℂ] HalfSpinorBundle m hP 1 x) :=
    Module.compHom _ Complex.ofRealHom
  -- Use exactly the principal point and fiber coordinates from the original action.
  let p : {p : P // projection p = x} :=
    ⟨Classical.choose (hP.projection_properties.2.2 x),
      Classical.choose_spec (hP.projection_properties.2.2 x)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m 0) p.val p.property
  let f := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m 1) p.val p.property
  let w : CotangentFiber (n := 2 * m) x →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    (realSpinorCoordinateIsometry m).toLinearEquiv.toLinearMap.comp
      ((S.frame p.val x p.property).symm.toLinearEquiv.toLinearMap.comp (g.sharp x))
  -- Wedge is linear and contraction is conjugate linear, hence both are real linear.
  have hadd (v z : EuclideanSpace ℂ (Fin m)) :
      cliffordSymbol (v + z) = cliffordSymbol v + cliffordSymbol z := by
    simp only [cliffordSymbol, exteriorMultiplication, contraction, map_add]
    abel
  have hsmul (a : ℝ) (v : EuclideanSpace ℂ (Fin m)) :
      cliffordSymbol (a • v) = (a : ℂ) • cliffordSymbol v := by
    have hscalar : a • v = (a : ℂ) • v := by simp
    rw [hscalar]
    simp only [cliffordSymbol, exteriorMultiplication, contraction, map_smul,
      map_smulₛₗ, Complex.conj_ofReal, smul_sub]
  refine IsLinearMap.mk ?_ ?_
  · intro ξ η
    apply LinearMap.ext
    intro u
    change f (cliffordSymbolParity (w (ξ + η)) 0 (e.symm u)) =
      f (cliffordSymbolParity (w ξ) 0 (e.symm u)) +
        f (cliffordSymbolParity (w η) 0 (e.symm u))
    rw [w.map_add]
    have hparity : cliffordSymbolParity (w ξ + w η) 0 (e.symm u) =
        cliffordSymbolParity (w ξ) 0 (e.symm u) +
          cliffordSymbolParity (w η) 0 (e.symm u) := by
      apply Subtype.ext
      exact LinearMap.congr_fun (hadd (w ξ) (w η)) (e.symm u).val
    rw [hparity]
    exact f.map_add _ _
  · intro a ξ
    apply LinearMap.ext
    intro u
    change f (cliffordSymbolParity (w (a • ξ)) 0 (e.symm u)) =
      (a : ℂ) • f (cliffordSymbolParity (w ξ) 0 (e.symm u))
    rw [w.map_smul]
    have hparity : cliffordSymbolParity (a • w ξ) 0 (e.symm u) =
        (a : ℂ) • cliffordSymbolParity (w ξ) 0 (e.symm u) := by
      apply Subtype.ext
      exact LinearMap.congr_fun (hsmul a (w ξ)) (e.symm u).val
    rw [hparity]
    exact f.map_smul (a : ℂ) _

set_option maxHeartbeats 8000000 in
-- Verify smoothness and ellipticity of the same native parity Clifford symbol in all charts.
/-- The same symbol is smooth, first-order homogeneous and invertible away from zero. -/
theorem cotangentCliffordPlus_properties :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ S : TopologicalSpinStructure m TM o hm hP,
    let A := S.smoothPrincipalAtlas I
    let H := halfSpinorBundleSmoothAtlas m hP A
    IsSmoothOffZeroAtlasSymbol (H 0) (H 1) (S.cotangentCliffordPlus g) ∧
      IsHomogeneousAtlasSymbol 1 (S.cotangentCliffordPlus g) ∧
      IsEllipticAtlasSymbol (S.cotangentCliffordPlus g) ∧
      IsAtlasGlobalSymbol (H 0) (H 1) 1 (S.cotangentCliffordPlus g) := by
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S
  let A := S.smoothPrincipalAtlas I
  let H := halfSpinorBundleSmoothAtlas m hP A
  let V := EuclideanSpace ℂ (Fin m)
  let W (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let b₀ := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  -- The native parity Clifford map is real bilinear, with the original complex fiber action.
  have hmodel (i : ZMod 2) : ContDiff ℝ ∞
      (fun v : V ↦ (cliffordSymbolParity v i).toContinuousLinearMap) := by
    let L : V →ₗ[ℝ] (W i →L[ℂ] W (i + 1)) := {
      toFun v := (cliffordSymbolParity v i).toContinuousLinearMap
      map_add' v w := by
        apply ContinuousLinearMap.ext
        intro u
        apply Subtype.ext
        change cliffordSymbol (v + w) u.val =
          cliffordSymbol v u.val + cliffordSymbol w u.val
        simp only [cliffordSymbol, exteriorMultiplication, contraction, map_add,
          LinearMap.add_apply, LinearMap.sub_apply]
        abel
      map_smul' t v := by
        apply ContinuousLinearMap.ext
        intro u
        apply Subtype.ext
        change cliffordSymbol (t • v) u.val = t • cliffordSymbol v u.val
        have hscalar : t • v = (t : ℂ) • v := by simp
        rw [hscalar]
        simp only [cliffordSymbol, exteriorMultiplication, contraction, map_smul,
          map_smulₛₗ, Complex.conj_ofReal, LinearMap.smul_apply, LinearMap.sub_apply]
        simp only [Complex.coe_smul]
        exact (smul_sub t _ _).symm }
    exact L.toContinuousLinearMap.contDiff
  -- The actual compatible unit-section frames are smooth in the original tangent bundle.
  let p (b x : M) := (A.trivialization b).toPartialEquiv.symm (x, 1)
  have hp (b x : M) (hx : x ∈ (A.trivialization b).baseSet) : projection (p b x) = x :=
    (A.trivialization b).proj_symm_apply' hx
  let frame (b : M) (a : Fin (2 * m)) (x : M) : TangentSpace I x :=
    if hx : x ∈ (A.trivialization b).baseSet then S.frame (p b x) x (hp b x hx) (b₀ a)
    else 0
  have hframe₀ (q : P) (x : M) (hq : projection q = x) (v : TModel) :
      (⟨x, S.frame q x hq v⟩ : TangentBundle I M) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 v⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  have hframe (b : M) (a : Fin (2 * m)) :
      ContMDiffOn I (I).tangent ∞ (fun x ↦ (⟨x, frame b a x⟩ : TangentBundle I M))
        (A.trivialization b).baseSet := by
    apply (S.smoothPrincipalAtlas_compatible I b a).congr
    intro x hx
    have hf : frame b a x = S.frame (p b x) x (hp b x hx) (b₀ a) := dite_eq_left hx
    exact (congrArg (fun v : TangentSpace I x ↦
      (⟨x, v⟩ : TangentBundle I M)) hf).trans (hframe₀ (p b x) x (hp b x hx) (b₀ a))
  -- Smoothness of the fixed covector chart map retains the actual chart derivative.
  have hcovector (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (z : TModel × TModel) (hz : z.1 ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, TModel × TModel) ((I).prod 𝓘(ℝ, CotangentModel (2 * m))) ∞
        (fun z ↦ (⟨c.symm z.1, covectorFromChart c (c.symm z.1) z.2⟩ :
          CotangentTotalSpace)) z := by
    have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas («I» := I) hc
    have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hcm hz).comp z
      contDiffAt_fst.contMDiffAt
    have hd := ((contMDiffAt_of_mem_maximalAtlas hcm (c.map_target hz)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).comp z hbase
    have hinner : ContMDiffAt 𝓘(ℝ, TModel × TModel) 𝓘(ℝ, CotangentModel (2 * m)) ∞
        (fun z ↦ innerSL ℝ z.2) z :=
      (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp z contDiffAt_snd.contMDiffAt
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨hbase, ?_⟩
    apply (hinner.clm_comp hd).congr_of_eventuallyEq
    filter_upwards with y
    ext v
    simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Function.id_def, ContinuousLinearMap.comp_apply]
    rfl
  -- The atlas transition matrices keep the actual original fiber equivalences.
  let Vc (l : ZMod 2) (i : (H l).Index) := EuclideanSpace ℂ (Fin ((H l).rank i))
  let ec (l : ZMod 2) (i : (H l).Index) := EuclideanSpace.equiv (Fin ((H l).rank i)) ℂ
  let column (l : ZMod 2) (i j : (H l).Index) (x : M) (a : Fin ((H l).rank i)) :
      Vc l j :=
    (ec l j).symm ((H l).chart j (((H l).chart i).toPartialEquiv.symm
      (x, Pi.single a 1))).2
  let T (l : ZMod 2) (i j : (H l).Index) (x : M) : Vc l i →L[ℂ] Vc l j :=
    ∑ a, (EuclideanSpace.proj a).smulRight (column l i j x a)
  have hpoint (l : ZMod 2) (i : (H l).Index) (x : M)
      (hx : x ∈ ((H l).chart i).baseSet) (v : Fin ((H l).rank i) → ℂ) :
      (⟨x, ((H l).frameLinearEquiv i x hx).symm v⟩ :
        TotalSpace Unit (HalfSpinorBundle m hP l)) =
          ((H l).chart i).toPartialEquiv.symm (x, v) :=
    TotalSpace.mk_cast (F := Unit) (((H l).chart i).proj_symm_apply' hx) _
  have hT (l : ZMod 2) (i j : (H l).Index) (x : M)
      (hi : x ∈ ((H l).chart i).baseSet) (hj : x ∈ ((H l).chart j).baseSet)
      (v : Vc l i) :
      T l i j x v = (ec l j).symm
        ((H l).frameLinearEquiv j x hj (((H l).frameLinearEquiv i x hi).symm (ec l i v))) := by
    let R : Vc l i →ₗ[ℂ] Vc l j :=
      (ec l j).symm.toLinearMap.comp (((H l).frameLinearEquiv j x hj).toLinearMap.comp
        (((H l).frameLinearEquiv i x hi).symm.toLinearMap.comp (ec l i).toLinearMap))
    have hcol (a : Fin ((H l).rank i)) :
        column l i j x a = R ((ec l i).symm (Pi.single a 1)) := by
      change (ec l j).symm ((H l).chart j (((H l).chart i).toPartialEquiv.symm
        (x, Pi.single a 1))).2 = (ec l j).symm
          ((H l).frameLinearEquiv j x hj (((H l).frameLinearEquiv i x hi).symm
            ((ec l i) ((ec l i).symm (Pi.single a 1)))))
      rw [(ec l i).apply_symm_apply, ← hpoint l i x hi]
      rfl
    have hsum : ∑ a, v a • (ec l i).symm (Pi.single a 1) = v := by
      apply (ec l i).injective
      ext a
      simp only [map_sum, map_smul, ContinuousLinearEquiv.apply_symm_apply,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ b, v b * (Pi.single b (1 : ℂ) : Fin ((H l).rank i) → ℂ) a) = v a
      simp [Pi.single_apply]
    change (∑ a, (EuclideanSpace.proj a).smulRight (column l i j x a)) v = R v
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, hcol]
    change ∑ a, v a • R ((ec l i).symm (Pi.single a 1)) = R v
    simpa only [map_sum, map_smul] using congrArg R hsum
  have hTsmooth (l : ZMod 2) (i j : (H l).Index) :
      ContMDiffOn I 𝓘(ℝ, Vc l i →L[ℂ] Vc l j) ∞ (T l i j)
        (((H l).chart i).baseSet ∩ ((H l).chart j).baseSet) := by
    apply contMDiffOn_finsetSum
    intro a _
    have hc := ((ec l j).symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn ((H l).contMDiffOn_coordChange i j a)
    exact ((ContinuousLinearMap.smulRightL ℂ (Vc l i) (Vc l j)
      (EuclideanSpace.proj a)).restrictScalars ℝ).contMDiff.comp_contMDiffOn hc
  -- Inverse-frame coordinates are the metric pairings with its orthonormal columns.
  let w (b : M) (c : OpenPartialHomeomorph M TModel) (z : TModel × TModel) : V :=
    realSpinorCoordinateIsometry m ((EuclideanSpace.equiv (Fin (2 * m)) ℝ).symm
      (fun a ↦ inner ℝ (frame b a (c.symm z.1))
        (g.sharp (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2))))
  have hw (b : M) (c : OpenPartialHomeomorph M TModel) (z : TModel × TModel)
      (hb : c.symm z.1 ∈ (A.trivialization b).baseSet) :
      w b c z = realSpinorCoordinateIsometry m
        ((S.frame (p b (c.symm z.1)) (c.symm z.1) (hp b (c.symm z.1) hb)).symm
          (g.sharp (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2))) := by
    apply congrArg (realSpinorCoordinateIsometry m)
    apply (EuclideanSpace.equiv (Fin (2 * m)) ℝ).injective
    funext a
    change inner ℝ (frame b a (c.symm z.1))
      (g.sharp (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2)) = _
    have hf : frame b a (c.symm z.1) =
        S.frame (p b (c.symm z.1)) (c.symm z.1) (hp b (c.symm z.1) hb) (b₀ a) :=
      dite_eq_left hb
    let f := S.frame (p b (c.symm z.1)) (c.symm z.1) (hp b (c.symm z.1) hb)
    let v := g.sharp (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2)
    change inner ℝ (frame b a (c.symm z.1)) v = (f.symm v) a
    calc
      inner ℝ (frame b a (c.symm z.1)) v = inner ℝ (f (b₀ a)) v :=
        congrArg (fun t ↦ inner ℝ t v) hf
      _ = inner ℝ (f (b₀ a)) (f (f.symm v)) :=
        (congrArg (fun t ↦ inner ℝ (f (b₀ a)) t) (f.apply_symm_apply v)).symm
      _ = inner ℝ (b₀ a) (f.symm v) := f.inner_map_map _ _
      _ = _ := EuclideanSpace.basisFun_inner (Fin (2 * m)) ℝ _ a
  have hwsmooth (b : M) (c : OpenPartialHomeomorph M TModel)
      (hc : c ∈ atlas TModel M) (z : TModel × TModel) (hz : z.1 ∈ c.target)
      (hb : c.symm z.1 ∈ (A.trivialization b).baseSet) : ContDiffAt ℝ ∞ (w b c) z := by
    have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas («I» := I) hc
    have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hcm hz).comp z
      contDiffAt_fst.contMDiffAt
    have hsharp := g.contMDiff_sharp.contMDiffAt.comp z (hcovector c hc z hz)
    have hcoords : ContMDiffAt 𝓘(ℝ, TModel × TModel)
        𝓘(ℝ, Fin (2 * m) → ℝ) ∞
        (fun z a ↦ inner ℝ (frame b a (c.symm z.1))
          (g.sharp (c.symm z.1) (covectorFromChart c (c.symm z.1) z.2))) z := by
      apply contMDiffAt_pi_space.mpr
      intro a
      exact (((hframe b a).contMDiffAt
        ((A.trivialization b).open_baseSet.mem_nhds hb)).comp z hbase).inner_bundle hsharp
    exact ((realSpinorCoordinateIsometry m).contDiff.contDiffAt.comp z
      ((EuclideanSpace.equiv (Fin (2 * m)) ℝ).symm.contDiff.contDiffAt.comp z
        hcoords.contDiffAt))
  -- Unit-section representatives identify each selected associated chart exactly.
  have hrepresentative (l : ZMod 2) (b : M) (k : (H l).Index)
      (e : W l ≃ₗ[ℂ] (Fin ((H l).rank k) → ℂ))
      (he : ((H l).chart k).baseSet = (A.trivialization b).baseSet)
      (hr : ∀ (q : P) (x : M) (hq : projection q = x),
        x ∈ (A.trivialization b).baseSet → ∀ v : W l,
          ((H l).chart k ⟨x, associatedVectorFiberMk hP
            (complexSpinParityContRepresentation m l) q hq v⟩).2 =
              e (complexSpinParityContRepresentation m l ((A.trivialization b) q).2 v))
      (x : M) (hx : x ∈ (A.trivialization b).baseSet) (v : W l) :
      (H l).frameLinearEquiv k x (he.symm ▸ hx)
        (associatedVectorFiberMk hP (complexSpinParityContRepresentation m l)
          (p b x) (hp b x hx) v) = e v := by
    have hunit : ((A.trivialization b) (p b x)).2 = 1 :=
      congrArg Prod.snd ((A.trivialization b).toPartialEquiv.right_inv
        ((A.trivialization b).mem_target.mpr hx))
    have h := hr (p b x) x (hp b x hx) hx v
    rw [hunit, map_one, one_apply_eq_self] at h
    exact h
  have hsmooth (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (i : (H 0).Index) (j : (H 1).Index) :
      ContDiffOn ℝ ∞ (Function.uncurry
        (atlasGlobalSymbolInChart (H 0) (H 1) (S.cotangentCliffordPlus g) c i j))
          (atlasSymbolChartDomain (H 0) (H 1) c i j ×ˢ Set.univ) := by
    intro z hz
    let b := c.symm z.1
    have hb : b ∈ (A.trivialization b).baseSet := A.mem_baseSet b
    obtain ⟨k₀, e₀, he₀, hr₀⟩ := (spinorBundleSmoothAtlases_compatibility m hP A).2.1 0 b
    obtain ⟨k₁, e₁, he₁, hr₁⟩ := (spinorBundleSmoothAtlases_compatibility m hP A).2.1 1 b
    let d₀ : Vc 0 k₀ ≃L[ℂ] W 0 := (ec 0 k₀).trans e₀.symm.toContinuousLinearEquiv
    let d₁ : W 1 ≃L[ℂ] Vc 1 k₁ := e₁.toContinuousLinearEquiv.trans (ec 1 k₁).symm
    let C : (W 0 →L[ℂ] W 1) →L[ℂ] (Vc 0 k₀ →L[ℂ] Vc 1 k₁) :=
      (ContinuousLinearMap.compL ℂ (Vc 0 k₀) (W 1) (Vc 1 k₁) d₁.toContinuousLinearMap).comp
        ((ContinuousLinearMap.compL ℂ (Vc 0 k₀) (W 0) (W 1)).flip d₀.toContinuousLinearMap)
    let R (y : TModel × TModel) : Vc 0 i →L[ℂ] Vc 1 j :=
      (T 1 k₁ j (c.symm y.1)).comp
        ((C (cliffordSymbolParity (w b c y) 0).toContinuousLinearMap).comp
          (T 0 i k₀ (c.symm y.1)))
    have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas («I» := I) hc
    have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hcm hz.1.1.1).comp z
      contDiffAt_fst.contMDiffAt
    have hleft : ContDiffAt ℝ ∞ (fun y : TModel × TModel ↦ T 1 k₁ j (c.symm y.1)) z := by
      have ht : ContMDiffAt I 𝓘(ℝ, Vc 1 k₁ →L[ℂ] Vc 1 j) ∞ (T 1 k₁ j) b :=
        (hTsmooth 1 k₁ j).contMDiffAt
          ((((H 1).chart k₁).open_baseSet.inter ((H 1).chart j).open_baseSet).mem_nhds
            ⟨he₁.symm ▸ hb, hz.1.2⟩)
      exact (ht.comp z hbase).contDiffAt
    have hright : ContDiffAt ℝ ∞ (fun y : TModel × TModel ↦ T 0 i k₀ (c.symm y.1)) z := by
      have ht : ContMDiffAt I 𝓘(ℝ, Vc 0 i →L[ℂ] Vc 0 k₀) ∞ (T 0 i k₀) b :=
        (hTsmooth 0 i k₀).contMDiffAt
          ((((H 0).chart i).open_baseSet.inter ((H 0).chart k₀).open_baseSet).mem_nhds
            ⟨hz.1.1.2, he₀.symm ▸ hb⟩)
      exact (ht.comp z hbase).contDiffAt
    have hmiddle := (C.restrictScalars ℝ).contDiff.contDiffAt.comp z
      ((hmodel 0).contDiffAt.comp z (hwsmooth b c hc z hz.1.1.1 hb))
    have hR : ContDiffAt ℝ ∞ R z := by
      let μ := (ContinuousLinearMap.compL ℂ (Vc 0 i) (Vc 0 k₀)
        (Vc 1 k₁)).bilinearRestrictScalars ℝ
      let ν := (ContinuousLinearMap.compL ℂ (Vc 0 i) (Vc 1 k₁)
        (Vc 1 j)).bilinearRestrictScalars ℝ
      exact (ν.contDiff.contDiffAt.comp z hleft).clm_apply
        ((μ.contDiff.contDiffAt.comp z hmiddle).clm_apply hright)
    have hnb := hbase.continuousAt ((A.trivialization b).open_baseSet.mem_nhds hb)
    have hni := hbase.continuousAt (((H 0).chart i).open_baseSet.mem_nhds hz.1.1.2)
    have hnj := hbase.continuousAt (((H 1).chart j).open_baseSet.mem_nhds hz.1.2)
    apply (hR.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hnb, hni, hnj] with y hy hi hj
    let x := c.symm y.1
    let q := p b x
    let hq := hp b x hy
    let ξ := covectorFromChart c x y.2
    have hk₀ : x ∈ ((H 0).chart k₀).baseSet := he₀.symm ▸ hy
    have hk₁ : x ∈ ((H 1).chart k₁).baseSet := he₁.symm ▸ hy
    have hrep₀ (v : W 0) := hrepresentative 0 b k₀ e₀ he₀ hr₀ x hy v
    have hrep₁ (v : W 1) := hrepresentative 1 b k₁ e₁ he₁ hr₁ x hy v
    apply ContinuousLinearMap.ext
    intro u
    let s := ((H 0).frameLinearEquiv i x hi).symm (ec 0 i u)
    let v := (associatedVectorFiberMkLinearEquiv hP
      (complexSpinParityContRepresentation m 0) q hq).symm s
    have hin : d₀ (T 0 i k₀ x u) = v := by
      apply e₀.injective
      change e₀ (e₀.symm (ec 0 k₀ (T 0 i k₀ x u))) = e₀ v
      rw [e₀.apply_symm_apply, hT 0 i k₀ x hi hk₀, (ec 0 k₀).apply_symm_apply]
      have h := hrep₀ v
      have hv : associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0)
          q hq v = s :=
        (associatedVectorFiberMkLinearEquiv hP
          (complexSpinParityContRepresentation m 0) q hq).apply_symm_apply s
      exact (congrArg ((H 0).frameLinearEquiv k₀ x hk₀) hv).symm.trans h
    have hout (v' : W 1) : T 1 k₁ j x (d₁ v') =
        (ec 1 j).symm ((H 1).frameLinearEquiv j x hj
          (associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) q hq v')) := by
      rw [hT 1 k₁ j x hk₁ hj]
      apply congrArg (ec 1 j).symm
      apply congrArg ((H 1).frameLinearEquiv j x hj)
      apply ((H 1).frameLinearEquiv k₁ x hk₁).injective
      change (H 1).frameLinearEquiv k₁ x hk₁
        (((H 1).frameLinearEquiv k₁ x hk₁).symm
          (ec 1 k₁ ((ec 1 k₁).symm (e₁ v')))) = _
      rw [((H 1).frameLinearEquiv k₁ x hk₁).apply_symm_apply, (ec 1 k₁).apply_symm_apply]
      exact (hrep₁ v').symm
    have hcliff : S.cotangentCliffordPlus g x ξ s =
        associatedVectorFiberMk hP (complexSpinParityContRepresentation m 1) q hq
          (cliffordSymbolParity (w b c y) 0 v) := by
      have hv : associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0)
          q hq v = s :=
        (associatedVectorFiberMkLinearEquiv hP
          (complexSpinParityContRepresentation m 0) q hq).apply_symm_apply s
      have h := S.cliffordParity_apply_mk q x hq (g.sharp x ξ) 0 v
      change S.cotangentCliffordPlus g x ξ
        (associatedVectorFiberMk hP (complexSpinParityContRepresentation m 0) q hq v) = _ at h
      rw [hv] at h
      exact h.trans (congrArg (associatedVectorFiberMk hP
        (complexSpinParityContRepresentation m 1) q hq)
          (congrArg (fun t ↦ cliffordSymbolParity t 0 v) (hw b c y hy).symm))
    change atlasGlobalSymbolInChart (H 0) (H 1) (S.cotangentCliffordPlus g) c i j
      y.1 y.2 u = R y u
    simp only [atlasGlobalSymbolInChart, dite_eq_left (show
      c.symm y.1 ∈ ((H 0).chart i).baseSet ∧ c.symm y.1 ∈ ((H 1).chart j).baseSet
        from ⟨hi, hj⟩)]
    change (ec 1 j).symm ((H 1).frameLinearEquiv j x hj
      (S.cotangentCliffordPlus g x ξ s)) =
        T 1 k₁ j x (d₁ (cliffordSymbolParity (w b c y) 0 (d₀ (T 0 i k₀ x u))))
    rw [hin, hout, hcliff]
  -- Fiberwise real linearity is unchanged by the chart derivative and complex frames.
  have hlinear (c : OpenPartialHomeomorph M TModel) (i : (H 0).Index)
      (j : (H 1).Index) (z : TModel) :
      IsLinearMap ℝ
        (atlasGlobalSymbolInChart (H 0) (H 1) (S.cotangentCliffordPlus g) c i j z) := by
    by_cases hz : c.symm z ∈ ((H 0).chart i).baseSet ∧
        c.symm z ∈ ((H 1).chart j).baseSet
    · let x := c.symm z
      let input := (ec 0 i).toLinearEquiv.trans ((H 0).frameLinearEquiv i x hz.1).symm
      let output := ((H 1).frameLinearEquiv j x hz.2).trans (ec 1 j).symm.toLinearEquiv
      have hcovadd (ξ η : TModel) : covectorFromChart c x (ξ + η) =
          covectorFromChart c x ξ + covectorFromChart c x η := by
        ext v
        change inner ℝ (ξ + η) (mfderiv I I c x v) =
          inner ℝ ξ (mfderiv I I c x v) + inner ℝ η (mfderiv I I c x v)
        exact inner_add_left ξ η _
      have hcovsmul (t : ℝ) (ξ : TModel) : covectorFromChart c x (t • ξ) =
          t • covectorFromChart c x ξ := by
        ext v
        change inner ℝ (t • ξ) (mfderiv I I c x v) =
          t * inner ℝ ξ (mfderiv I I c x v)
        exact real_inner_smul_left ξ _ t
      let : Module ℝ (HalfSpinorBundle m hP 0 x →ₗ[ℂ] HalfSpinorBundle m hP 1 x) :=
        Module.compHom _ Complex.ofRealHom
      have hlin := S.isLinearMap_cotangentCliffordPlus g x
      refine ⟨?_, ?_⟩
      · intro ξ η
        apply ContinuousLinearMap.ext
        intro u
        simp only [atlasGlobalSymbolInChart, dite_eq_left hz]
        change output (S.cotangentCliffordPlus g x (covectorFromChart c x (ξ + η)) (input u)) =
          output (S.cotangentCliffordPlus g x (covectorFromChart c x ξ) (input u)) +
            output (S.cotangentCliffordPlus g x (covectorFromChart c x η) (input u))
        rw [hcovadd, hlin.map_add, LinearMap.add_apply]
        exact output.map_add _ _
      · intro t ξ
        apply ContinuousLinearMap.ext
        intro u
        simp only [atlasGlobalSymbolInChart, dite_eq_left hz]
        change output (S.cotangentCliffordPlus g x (covectorFromChart c x (t • ξ)) (input u)) =
          (t : ℂ) • output (S.cotangentCliffordPlus g x (covectorFromChart c x ξ) (input u))
        rw [hcovsmul, hlin.map_smul]
        change output ((t : ℂ) • S.cotangentCliffordPlus g x (covectorFromChart c x ξ)
          (input u)) = _
        exact output.map_smul (t : ℂ) _
    · constructor <;> intros <;> simp only [atlasGlobalSymbolInChart, dite_eq_right hz,
        add_zero, smul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc i j
    exact (hsmooth c hc i j).mono (Set.prod_mono Set.Subset.rfl (Set.subset_univ _))
  · intro x ξ _ t _
    let : Module ℝ (HalfSpinorBundle m hP 0 x →ₗ[ℂ] HalfSpinorBundle m hP 1 x) :=
      Module.compHom _ Complex.ofRealHom
    have hlin : IsLinearMap ℝ (S.cotangentCliffordPlus g x) :=
      S.isLinearMap_cotangentCliffordPlus g x
    have h : S.cotangentCliffordPlus g x (t • ξ) =
        (t : ℂ) • S.cotangentCliffordPlus g x ξ := hlin.map_smul t ξ
    simpa only [Real.rpow_one] using h
  · intro x ξ hξ
    have hv : g.sharp x ξ ≠ 0 := by
      intro hzero
      apply hξ
      calc
        ξ = g.inner x (g.sharp x ξ) := (g.sharp_flat_inverse x 0 ξ).2.symm
        _ = g.inner x 0 := congrArg (g.inner x) hzero
        _ = 0 := map_zero _
    exact S.cliffordParity_bijective x (g.sharp x ξ) hv 0
  · intro c hc i j
    let U := atlasSymbolChartDomain (H 0) (H 1) c i j
    let symbol := atlasGlobalSymbolInChart (H 0) (H 1) (S.cotangentCliffordPlus g) c i j
    have hU : IsOpen U := by
      simpa only [U, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.continuousOn_symm.isOpen_inter_preimage c.open_target
          (((H 0).chart i).open_baseSet.inter ((H 1).chart j).open_baseSet)
    let e := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    have hcoeff (a : Fin (2 * m)) : ContDiffOn ℝ ∞ (fun z ↦ symbol z (e a)) U :=
      (hsmooth c hc i j).comp (contDiffOn_id.prodMk contDiffOn_const)
        (fun _ hz ↦ ⟨hz, Set.mem_univ _⟩)
    let Q : CoordinateDifferentialOperator (2 * m) ((H 0).rank i) ((H 1).rank j) 1 U := {
      coefficient := Fin.cases (fun _ _ ↦ 0)
        (fun k α z ↦ symbol z (e (α ⟨0, Nat.zero_lt_succ k.val⟩)))
      smooth_coefficient := by
        intro k
        refine Fin.cases (fun _ ↦ contDiffOn_const) (fun k α ↦ ?_) k
        exact hcoeff (α ⟨0, Nat.zero_lt_succ k.val⟩) }
    have hQ : Q.principalSymbol = symbol := by
      funext z ξ
      let L : TModel →ₗ[ℝ] (Vc 0 i →L[ℂ] Vc 1 j) := {
        toFun := symbol z
        map_add' := (hlinear c i j z).map_add
        map_smul' := (hlinear c i j z).map_smul }
      have hsum : ∑ a, ξ a • e a = ξ := by
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
          EuclideanSpace.basisFun_repr, e] using e.toBasis.sum_repr ξ
      let reindex : (Fin 1 → Fin (2 * m)) ≃ Fin (2 * m) := {
        toFun α := α 0
        invFun a := fun _ ↦ a
        left_inv α := by
          funext t
          exact congrArg α (Subsingleton.elim (0 : Fin 1) t)
        right_inv _ := rfl }
      have hr : (∑ α : Fin 1 → Fin (2 * m), ξ (α 0) • symbol z (e (α 0))) =
          ∑ a : Fin (2 * m), ξ a • symbol z (e a) :=
        reindex.sum_comp (fun a ↦ ξ a • symbol z (e a))
      change (∑ α : Fin 1 → Fin (2 * m), (∏ t, ξ (α t)) •
        Q.coefficient ⟨1, by omega⟩ α z) = _
      simp only [Q, Fin.prod_univ_one, Fin.val_zero]
      apply hr.trans
      have h := congrArg L hsum
      simp only [map_sum, map_smul] at h
      exact h
    have h := Q.isSymbol_principalSymbol hU
    rw [hQ] at h
    simpa only [Nat.cast_one] using h

/-- The two original half-spin actions are mutually skew for the same Fock metrics. -/
theorem cotangentClifford_skew :
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  ∀ (S : TopologicalSpinStructure m TM o hm hP) (x : M)
    (ξ : CotangentFiber (n := 2 * m) x)
    (u : HalfSpinorBundle m hP 0 x) (v : HalfSpinorBundle m hP 1 x),
    let A := S.smoothPrincipalAtlas I
    let h := halfSpinorHermitianMetric m hP A
    ((h 1).toCore x).inner (S.cotangentCliffordPlus g x ξ u) v =
      -((h 0).toCore x).inner u (S.cotangentCliffordMinus g x ξ v) := by
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  intro S x ξ u v
  let A := S.smoothPrincipalAtlas I
  let h := halfSpinorHermitianMetric m hP A
  -- Use the same principal point and coordinate identifications as the original Clifford maps.
  let p : {p : P // projection p = x} :=
    ⟨Classical.choose (hP.projection_properties.2.2 x),
      Classical.choose_spec (hP.projection_properties.2.2 x)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m 0) p.val p.property
  let f := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m 1) p.val p.property
  let w := realSpinorCoordinateIsometry m ((S.frame p.val x p.property).symm (g.sharp x ξ))
  change ((h 1).toCore x).inner (f (cliffordSymbolParity w 0 (e.symm u))) v =
    -((h 0).toCore x).inner u (e (cliffordSymbolParity w 1 (f.symm v)))
  -- Both quotient metrics restrict to the same original Fock form at this point.
  have hpair (i : ZMod 2)
      (a b : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
      ((h i).toCore x).inner
        (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p.val p.property a)
        (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p.val p.property b) =
          spinorFockPairing m a.val b.val :=
    (halfSpinorHermitianMetric_properties m hP A i).2 p.val x p.property a b
  have hplus := hpair 1 (cliffordSymbolParity w 0 (e.symm u)) (f.symm v)
  have hminus := hpair 0 (e.symm u) (cliffordSymbolParity w 1 (f.symm v))
  change ((h 1).toCore x).inner (f (cliffordSymbolParity w 0 (e.symm u)))
    (f (f.symm v)) = _ at hplus
  change ((h 0).toCore x).inner (e (e.symm u))
    (e (cliffordSymbolParity w 1 (f.symm v))) = _ at hminus
  rw [f.apply_symm_apply] at hplus
  rw [e.apply_symm_apply] at hminus
  rw [hplus, hminus]
  exact spinorFockPairing_cliffordSymbol m w (e.symm u).val (f.symm v).val

end TopologicalSpinStructure

end AtiyahSinger
