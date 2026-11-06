/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentHomologicalOrientation
public import AtiyahSinger.Geometry.TangentTubeDerivative
public import AtiyahSinger.Geometry.VectorBundleZeroDerivative

/-!
# Derivatives of the original tube in doubled and interleaved normal coordinates

Public module ID: M1475.

The specified tangent-normal splitting transports the actual tube derivative to
the native double of the pulled-back base normal bundle. The derivative at zero
uses the same original quotient frames; its normalized determinant remains one.
The accompanying linear-algebra comparison proves positivity in interleaved
base-then-normal coordinates. The exact interleaving agrees with the realification
of a complex direct sum, and the remaining real change of basis occurs twice.

The fibers remain the original topological real modules; no independent normal
fiber norm is introduced. All derivative norms are on the native model spaces.
This is a local input to the tangent orientation and Thom-integral comparison.
Its conclusions concern the local derivative and coordinate orientation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem interleaving_sum (n r : ℕ) :
    let E := EuclideanSpace ℝ (Fin n)
    let Q := EuclideanSpace ℝ (Fin r)
    let a := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 2 * r)
    let d := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (Nat.mul_add 2 n r).symm)).toContinuousLinearEquiv
    ((ContinuousLinearEquiv.prodProdProdComm ℝ E E Q Q).trans
      ((a.symm.prodCongr a.symm).trans (tangentModelCoordinateEquiv (n + r)))) =
        ((tangentModelCoordinateEquiv n).prodCongr (tangentModelCoordinateEquiv r)).trans
          (b.symm.trans d) := by
  let a := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 2 * r)
  ext p k
  let ρ (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))
  obtain ⟨⟨i, j⟩, rfl⟩ := (ρ (n + r)).surjective k
  change tangentModelCoordinateEquiv (n + r)
      (a.symm (p.1.1, p.2.1), a.symm (p.1.2, p.2.2)) (ρ (n + r) (i, j)) =
    b.symm (tangentModelCoordinateEquiv n p.1, tangentModelCoordinateEquiv r p.2)
      ((finCongr (Nat.mul_add 2 n r).symm).symm (ρ (n + r) (i, j)))
  revert i
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)
  · have hi : (finCongr (Nat.mul_add 2 n r).symm).symm
        (ρ (n + r) (Fin.castAdd r i, j)) = Fin.castAdd (2 * r) (ρ n (i, j)) := by
      apply Fin.ext
      rfl
    rw [hi]
    fin_cases j <;>
      simp [tangentModelCoordinateEquiv, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd, ρ, a, b]
  · have hi : (finCongr (Nat.mul_add 2 n r).symm).symm
        (ρ (n + r) (Fin.natAdd n i, j)) = Fin.natAdd (2 * n) (ρ r (i, j)) := by
      apply Fin.ext
      change j.val + 2 * (n + i.val) = 2 * n + (j.val + 2 * i.val)
      omega
    rw [hi]
    fin_cases j <;>
      simp [tangentModelCoordinateEquiv, EuclideanSpace.finAddEquivProd,
        EuclideanSpace.sumEquivProd, ρ, a, b]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A determinant-one normalized double becomes positive in the specified interleaved
base-then-normal coordinates, regardless of the sign of the original real lift. -/
theorem det_pos_interleaved_of_normalized_double (n r N : ℕ) (hN : n + r = N) {Q : Type}
    [AddCommGroup Q] [Module ℝ Q] [TopologicalSpace Q] [FiniteDimensional ℝ Q]
    (q : Q ≃L[ℝ] EuclideanSpace ℝ (Fin r))
    (e : (EuclideanSpace ℝ (Fin n) × Q) ≃L[ℝ] EuclideanSpace ℝ (Fin N))
    (A : ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × (Q × Q)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)))
    (hA : LinearMap.det ((e.prodCongr e).symm.toLinearMap.comp
      (A.toLinearMap.comp
        (LinearEquiv.prodProdProdComm ℝ
          (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) Q Q).symm.toLinearMap)) = 1) :
    let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 2 * r)
    let d := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (show 2 * n + 2 * r = 2 * N by omega))).toContinuousLinearEquiv
    let P := ((ContinuousLinearEquiv.refl ℝ
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))).prodCongr (q.prodCongr q)).trans
        (((tangentModelCoordinateEquiv n).prodCongr (tangentModelCoordinateEquiv r)).trans
          (b.symm.trans d))
    0 < LinearMap.det ((P.symm.trans A).trans
      (tangentModelCoordinateEquiv N)).toLinearMap := by
  subst N
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin (n + r))
  let W := EuclideanSpace ℝ (Fin (2 * (n + r)))
  let a := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let b := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 2 * r)
  let d := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finCongr (Nat.mul_add 2 n r).symm)).toContinuousLinearEquiv
  let P := ((ContinuousLinearEquiv.refl ℝ (E × E)).prodCongr (q.prodCongr q)).trans
    (((tangentModelCoordinateEquiv n).prodCongr (tangentModelCoordinateEquiv r)).trans
      (b.symm.trans d))
  let J := ContinuousLinearEquiv.prodProdProdComm ℝ E E Q Q
  let e₀ := ((ContinuousLinearEquiv.refl ℝ E).prodCongr q).trans a.symm
  let t := tangentModelCoordinateEquiv (n + r)
  let Z := (e₀.prodCongr e₀).trans t
  have hP : P = J.trans Z := by
    apply DFunLike.ext
    intro v
    have h := congrArg (fun L ↦ L (v.1, (q v.2.1, q v.2.2))) (interleaving_sum n r)
    exact h.symm
  let K := J.symm.trans (A.trans (e.prodCongr e).symm)
  have hK : LinearMap.det K.toLinearMap = 1 := hA
  let KZ : W ≃L[ℝ] W := Z.symm.trans (K.trans Z)
  have hKZ : LinearMap.det KZ.toLinearMap = 1 :=
    (LinearMap.det_conj K.toLinearMap Z.toLinearEquiv).trans hK
  let B : F ≃L[ℝ] F := e₀.symm.trans e
  let L₀ : W ≃L[ℝ] W := t.symm.trans ((B.prodCongr B).trans t)
  have hL₀ : 0 < LinearMap.det L₀.toLinearMap := by
    rw [show LinearMap.det L₀.toLinearMap = LinearMap.det (B.prodCongr B).toLinearMap from
      LinearMap.det_conj (B.prodCongr B).toLinearMap t.toLinearEquiv]
    change 0 < LinearMap.det (B.toLinearMap.prodMap B.toLinearMap)
    rw [LinearMap.det_prodMap]
    exact mul_self_pos.mpr B.toLinearEquiv.isUnit_det'.ne_zero
  have hfactor : (P.symm.trans A).trans t = KZ.trans L₀ := by
    rw [hP]
    apply DFunLike.ext
    intro v
    let w := A (J.symm (Z.symm v))
    change t w = t ((e.prodCongr e)
      ((e₀.prodCongr e₀).symm (t.symm
        (t ((e₀.prodCongr e₀) ((e.prodCongr e).symm w))))))
    rw [t.symm_apply_apply, (e₀.prodCongr e₀).symm_apply_apply,
      (e.prodCongr e).apply_symm_apply]
  change 0 < LinearMap.det ((P.symm.trans A).trans t).toLinearMap
  rw [hfactor]
  change 0 < LinearMap.det (L₀.toLinearMap.comp KZ.toLinearMap)
  rw [LinearMap.det_comp, hKZ, mul_one]
  exact hL₀


set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- The same nested pullback/product and quotient bundle instances occur in both chain-rule factors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The same tangent tube and prescribed splitting have the actual normalized derivative
in the native double of the original pulled-back base normal bundle. -/
theorem exists_tangentDoubleTube_normalized_derivative {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (S : TangentNormalSplitting f hf)
    (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
    (z : TangentBundle 𝓘(ℝ, E) M) :
    letI := normalBundleFiberBundle f hf.isImmersion
    letI := normalBundleVectorBundle f hf.isImmersion
    let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
    let V := NormalModel E F
    let πM := smoothTangentBundleProjection E M
    let νP := ((πM : TangentBundle 𝓘(ℝ, E) M → M) *ᵖ ν)
    letI : ChartedSpace ((E × E) × (V × V)) (TotalSpace (V × V) (νP ×ᵇ νP)) :=
      inferInstanceAs (ChartedSpace (ModelProd (E × E) (V × V))
        (TotalSpace (V × V) (νP ×ᵇ νP)))
    let w₀ : TotalSpace (V × V) (νP ×ᵇ νP) := ⟨z, 0⟩
    let c := chartAt ((E × E) × (V × V)) w₀
    let q := VectorBundle.continuousLinearEquivAt ℝ V νP z
    ∃ e : (E × ν z.proj) ≃L[ℝ] F,
      ∃ A : ((E × E) × (V × V)) ≃L[ℝ] (F × F),
        HasFDerivAt (fun p ↦ chartAt (F × F) (smoothTangentMap f z)
          (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
            ((S.totalHomeomorph f hf).symm (c.symm p))))
          A.toContinuousLinearMap (c w₀) ∧
        LinearMap.det ((e.prodCongr e).symm.toLinearMap.comp
          (A.toLinearMap.comp ((LinearMap.prodMap LinearMap.id (q.prodCongr q).toLinearMap).comp
            (LinearEquiv.prodProdProdComm ℝ E E (ν z.proj) (ν z.proj)).symm.toLinearMap))) =
          1 := by
  classical
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
  let V := NormalModel E F
  let VT := NormalModel (E × E) (F × F)
  let πM := smoothTangentBundleProjection E M
  let νP := ((πM : TangentBundle 𝓘(ℝ, E) M → M) *ᵖ ν)
  let : ChartedSpace ((E × E) × (V × V)) (TotalSpace (V × V) (νP ×ᵇ νP)) :=
    inferInstanceAs (ChartedSpace (ModelProd (E × E) (V × V))
      (TotalSpace (V × V) (νP ×ᵇ νP)))
  let : ChartedSpace ((E × E) × VT) (TotalSpace VT νT) :=
    inferInstanceAs (ChartedSpace (ModelProd (E × E) VT) (TotalSpace VT νT))
  let w₀ : TotalSpace (V × V) (νP ×ᵇ νP) := ⟨z, 0⟩
  let z₀ : TotalSpace VT νT := ⟨z, 0⟩
  let c := chartAt ((E × E) × (V × V)) w₀
  let d := chartAt ((E × E) × VT) z₀
  let q := VectorBundle.continuousLinearEquivAt ℝ V νP z
  let eP := VectorBundle.continuousLinearEquivAt ℝ (V × V) (νP ×ᵇ νP) z
  let eT := VectorBundle.continuousLinearEquivAt ℝ VT νT z
  have heP : eP = q.prodCongr q := by
    exact Trivialization.continuousLinearEquivAt_prod
      (𝕜 := ℝ) (e₁ := trivializationAt V νP z) (e₂ := trivializationAt V νP z)
      ⟨mem_baseSet_trivializationAt V νP z, mem_baseSet_trivializationAt V νP z⟩
  obtain ⟨e, _, _, A, hA, hdet⟩ := exists_tangentTube_normalized_derivative f hf S T z
  let H := (S.totalHomeomorph f hf).symm
  let R := (ContinuousLinearEquiv.refl ℝ (E × E)).prodCongr
    (eP.symm.trans ((S.equiv z).symm.trans eT))
  let A' := R.trans A
  have hR : HasFDerivAt (fun p ↦ d (H (c.symm p))) R.toContinuousLinearMap (c w₀) := by
    let Q (y : TangentBundle 𝓘(ℝ, E) M) : (νP ×ᵇ νP) y →L[ℝ] νT y :=
      (S.equiv y).symm.toContinuousLinearMap
    have hQ : ContMDiff (𝓘(ℝ, E × E).prod 𝓘(ℝ, V × V))
        (𝓘(ℝ, E × E).prod 𝓘(ℝ, VT)) ∞
        (fun w : TotalSpace (V × V) (νP ×ᵇ νP) ↦
          (⟨w.proj, Q w.proj w.snd⟩ : TotalSpace VT νT)) := S.contMDiff_invFun
    have h := hasFDerivAt_bundleMap_zero
      (B := E × E) (F := V × V) (G := VT) (E₁ := νP ×ᵇ νP) (E₂ := νT) Q hQ z
    change HasFDerivAt (fun p ↦ d (H (c.symm p)))
      (ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ (E × E))
        (eT.toContinuousLinearMap.comp ((Q z).comp eP.symm.toContinuousLinearMap)))
      (c w₀) at h
    exact h
  have hH : H w₀ = z₀ := by
    change (⟨z, (S.equiv z).symm 0⟩ : TotalSpace VT νT) = ⟨z, 0⟩
    rw [map_zero]
  have hcenter : H (c.symm (c w₀)) = z₀ := by
    rw [c.left_inv (mem_chart_source _ w₀), hH]
  have hAat : HasFDerivAt (fun p ↦ chartAt (F × F) (smoothTangentMap f z)
      (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf) (d.symm p)))
      A.toContinuousLinearMap (d (H (c.symm (c w₀)))) := by
    rw [hcenter]
    exact hA
  have hcomp := hAat.comp (c w₀) hR
  have hc : ContinuousAt (fun p ↦ H (c.symm p)) (c w₀) :=
    H.continuous.continuousAt.comp
      (c.continuousAt_symm (c.map_source (mem_chart_source _ w₀)))
  have hlocal : ∀ᶠ p in 𝓝 (c w₀), H (c.symm p) ∈ d.source := by
    apply hc
    change d.source ∈ 𝓝 (H (c.symm (c w₀)))
    rw [hcenter]
    exact d.open_source.mem_nhds (mem_chart_source _ z₀)
  refine ⟨e, A', ?_, ?_⟩
  · apply hcomp.congr_of_eventuallyEq
    filter_upwards [hlocal] with p hp
    exact congrArg (fun v ↦ chartAt (F × F) (smoothTangentMap f z)
      (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf) v))
        (d.left_inv hp).symm
  · have hmaps : A'.toLinearMap.comp
        (LinearMap.prodMap LinearMap.id (q.prodCongr q).toLinearMap) =
      A.toLinearMap.comp (LinearMap.prodMap LinearMap.id
        (eT.toLinearMap.comp (S.equiv z).symm.toLinearMap)) := by
      apply LinearMap.ext
      rintro ⟨v, w⟩
      change A (v, eT ((S.equiv z).symm (eP.symm ((q.prodCongr q) w)))) =
        A (v, eT ((S.equiv z).symm w))
      rw [heP, (q.prodCongr q).symm_apply_apply]
    change LinearMap.det ((e.prodCongr e).symm.toLinearMap.comp
      ((A'.toLinearMap.comp (LinearMap.prodMap LinearMap.id
        (q.prodCongr q).toLinearMap)).comp
        (LinearEquiv.prodProdProdComm ℝ E E (ν z.proj) (ν z.proj)).symm.toLinearMap)) = 1
    rw [hmaps]
    exact hdet


end AtiyahSinger
