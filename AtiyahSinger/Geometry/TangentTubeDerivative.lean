/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentChartOrientation
public import AtiyahSinger.Geometry.TangentNormalHomotopy
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

/-!
# The actual tangent tube derivative and its normalized determinant

Public module ID: M1496.

At the zero section of the original tangent normal bundle, the derivative of the
specified tubular map is an isomorphism. Its tangent block is the actual derivative
of the tangent map, and its normal block induces the original quotient map.
The prescribed tangent-normal splitting identifies that quotient with the ordered
double of the base normal quotient. Relative to the same base tangent-normal lift
in both factors, the resulting derivative has determinant one.

The proof retains the lower-left second-derivative block. It factors the comparison
into two unipotent block shears instead of dropping connection or Hessian terms.
No orientation assumption is imposed on the base immersion or the auxiliary lift.
The result is the local linear-algebra input for the tangent tube orientation and
Thom-integral comparison; by itself it does not assert that global comparison.

Source: the tangent exact-sequence argument used in SG III.13.8. The explicit
same-witness derivative and two-shear calculation are project supplements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem normalized_double_det {E Q F : Type}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup Q] [Module ℝ Q] [FiniteDimensional ℝ Q]
    [AddCommGroup F] [Module ℝ F]
    (e : (E × Q) ≃ₗ[ℝ] F)
    (D : (E × E) →ₗ[ℝ] (F × F)) (σ : (F × F) →ₗ[ℝ] (Q × Q))
    (S : (Q × Q) →ₗ[ℝ] (F × F))
    (hDfirst : ∀ p, (D p).1 = e (p.1, 0))
    (hDvertical : ∀ v, D (0, v) = (0, e (v, 0)))
    (hσD : ∀ p, σ (D p) = 0) (hσS : ∀ w, σ (S w) = w)
    (hσfirst : ∀ p, (σ p).1 = (e.symm p.1).2)
    (hσvertical : ∀ w, σ (0, w) = (0, (e.symm w).2)) :
    let J := LinearEquiv.prodProdProdComm ℝ E E Q Q
    let C := D.comp (LinearMap.fst ℝ (E × E) (Q × Q)) +
      S.comp (LinearMap.snd ℝ (E × E) (Q × Q))
    LinearMap.det ((e.prodCongr e).symm.toLinearMap.comp
      (C.comp J.symm.toLinearMap)) = 1 := by
  classical
  dsimp only
  let J := LinearEquiv.prodProdProdComm ℝ E E Q Q
  let C := D.comp (LinearMap.fst ℝ (E × E) (Q × Q)) +
    S.comp (LinearMap.snd ℝ (E × E) (Q × Q))
  let B : E →ₗ[ℝ] (E × Q) := e.symm.toLinearMap.comp
    ((LinearMap.snd ℝ F F).comp (D.comp (LinearMap.inl ℝ E E)))
  let t : (Q × Q) →ₗ[ℝ] E := (LinearMap.fst ℝ E Q).comp
    (e.symm.toLinearMap.comp ((LinearMap.fst ℝ F F).comp S))
  let r : (Q × Q) →ₗ[ℝ] E := (LinearMap.fst ℝ E Q).comp
    (e.symm.toLinearMap.comp ((LinearMap.snd ℝ F F).comp S))
  let k : Q →ₗ[ℝ] Q := (LinearMap.snd ℝ Q Q).comp
    (σ.comp ((LinearMap.inl ℝ F F).comp (e.toLinearMap.comp (LinearMap.inr ℝ E Q))))
  let T : (Q × Q) →ₗ[ℝ] (E × E) :=
    t.prod (r - (LinearMap.fst ℝ E Q).comp (B.comp t))
  let H : (E × Q) →ₗ[ℝ] (E × Q) :=
    ((LinearMap.fst ℝ E Q).comp (B.comp (LinearMap.fst ℝ E Q))).prod
      ((LinearMap.snd ℝ E Q).comp (B.comp (LinearMap.fst ℝ E Q)) -
        k.comp (LinearMap.snd ℝ E Q))
  let U : ((E × E) × (Q × Q)) →ₗ[ℝ] ((E × E) × (Q × Q)) :=
    ((LinearMap.fst ℝ (E × E) (Q × Q)) +
      T.comp (LinearMap.snd ℝ (E × E) (Q × Q))).prod
        (LinearMap.snd ℝ (E × E) (Q × Q))
  let V : ((E × Q) × (E × Q)) →ₗ[ℝ] ((E × Q) × (E × Q)) :=
    (LinearMap.fst ℝ (E × Q) (E × Q)).prod
      ((LinearMap.snd ℝ (E × Q) (E × Q)) + H.comp (LinearMap.fst ℝ (E × Q) (E × Q)))
  -- The first normal quotient and the prescribed vertical quotient determine the last block.
  have hfirst (w : Q × Q) : e.symm (S w).1 = (t w, w.1) := by
    apply Prod.ext
    · rfl
    · exact (hσfirst (S w)).symm.trans (congrArg Prod.fst (hσS w))
  have hDsecond (u v : E) : e.symm (D (u, v)).2 = B u + (v, 0) := by
    have hsum : D (u, v) = D (u, 0) + D (0, v) := by
      rw [← map_add]
      simp
    rw [hsum, hDvertical]
    change e.symm ((D (u, 0)).2 + e (v, 0)) = _
    rw [map_add, e.symm_apply_apply]
    rfl
  have hσhorizontal (u : E) : (σ (e (u, 0), 0)).2 = -(B u).2 := by
    have hsplit : σ (D (u, 0)) = σ (e (u, 0), 0) + σ (0, (D (u, 0)).2) := by
      rw [← map_add]
      congr 1
      apply Prod.ext
      · simpa only [Prod.fst_add, add_zero] using hDfirst (u, 0)
      · simp
    have h := congrArg Prod.snd hsplit
    rw [hσD, hσvertical] at h
    change 0 = (σ (e (u, 0), 0)).2 + (B u).2 at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hSsecond (w : Q × Q) : (e.symm (S w).2).2 = w.2 + (B (t w)).2 - k w.1 := by
    have hSfirst : (S w).1 = e (t w, w.1) := by
      rw [← hfirst, e.apply_symm_apply]
    have hsplit : σ (S w) =
        σ (e (t w, 0), 0) + σ (e (0, w.1), 0) + σ (0, (S w).2) := by
      rw [← map_add, ← map_add]
      congr 1
      apply Prod.ext
      · change (S w).1 = e (t w, 0) + e (0, w.1) + 0
        rw [add_zero, ← map_add]
        simpa using hSfirst
      · simp
    have h := congrArg Prod.snd hsplit
    rw [hσS, hσvertical] at h
    change w.2 = (σ (e (t w, 0), 0)).2 + k w.1 + (e.symm (S w).2).2 at h
    rw [hσhorizontal] at h
    rw [h]
    abel
  -- Relative to the same doubled stable coordinates the map is a product of two shears.
  have hfactor : (e.prodCongr e).symm.toLinearMap.comp (C.comp J.symm.toLinearMap) =
      V.comp (J.toLinearMap.comp (U.comp J.symm.toLinearMap)) := by
    apply LinearMap.ext
    rintro ⟨⟨u, a⟩, v, b⟩
    change (e.symm ((D (u, v)).1 + (S (a, b)).1),
      e.symm ((D (u, v)).2 + (S (a, b)).2)) = _
    rw [map_add, map_add, hDfirst, e.symm_apply_apply, hfirst, hDsecond]
    apply Prod.ext
    · change (u, 0) + (t (a, b), a) = (u + t (a, b), a)
      simp
    · apply Prod.ext
      · change (B u).1 + v + r (a, b) =
          v + (r (a, b) - (B (t (a, b))).1) + (B (u + t (a, b))).1
        rw [map_add]
        change (B u).1 + v + r (a, b) =
          v + (r (a, b) - (B (t (a, b))).1) + ((B u).1 + (B (t (a, b))).1)
        abel
      · change (B u).2 + 0 + (e.symm (S (a, b)).2).2 =
          b + ((B (u + t (a, b))).2 - k a)
        rw [hSsecond, map_add]
        change (B u).2 + 0 + (b + (B (t (a, b))).2 - k a) =
          b + ((B u).2 + (B (t (a, b))).2 - k a)
        abel
  -- A block shear has determinant one in any finite-dimensional pair of real spaces.
  have detShear {A B : Type} [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A]
      [AddCommGroup B] [Module ℝ B] [FiniteDimensional ℝ B] (L : B →ₗ[ℝ] A) :
      LinearMap.det (((LinearMap.fst ℝ A B) + L.comp (LinearMap.snd ℝ A B)).prod
        (LinearMap.snd ℝ A B)) = 1 := by
    let a := Module.finBasis ℝ A
    let b := Module.finBasis ℝ B
    have hm : LinearMap.toMatrix (a.prod b) (a.prod b)
        (((LinearMap.fst ℝ A B) + L.comp (LinearMap.snd ℝ A B)).prod
          (LinearMap.snd ℝ A B)) =
        Matrix.fromBlocks 1 (LinearMap.toMatrix b a L) 0 1 := by
      ext i j
      cases i <;> cases j <;>
        simp [LinearMap.toMatrix_apply, Module.Basis.prod_apply, Module.Basis.prod_repr_inl,
          Module.Basis.prod_repr_inr, Matrix.fromBlocks, Matrix.one_apply, Finsupp.single_apply,
          eq_comm]
    rw [← LinearMap.det_toMatrix (a.prod b), hm, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hU : LinearMap.det U = 1 := detShear T
  have hV : LinearMap.det V = 1 := by
    let K := LinearEquiv.prodComm ℝ (E × Q) (E × Q)
    have hconj : K.toLinearMap.comp
        ((((LinearMap.fst ℝ (E × Q) (E × Q)) + H.comp
          (LinearMap.snd ℝ (E × Q) (E × Q))).prod
            (LinearMap.snd ℝ (E × Q) (E × Q))).comp K.symm.toLinearMap) = V := by
      rfl
    rw [← hconj, LinearMap.det_conj]
    exact detShear H
  rw [hfactor, LinearMap.det_comp, LinearMap.det_conj, hU, hV, one_mul]


set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem native_tube_derivative {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (T : TubularNeighborhood f hf) (x : M) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
    let G := NormalModel E F
    letI : ChartedSpace (E × G) (TotalSpace G V) :=
      inferInstanceAs (ChartedSpace (ModelProd E G) (TotalSpace G V))
    let z : TotalSpace G V := ⟨x, 0⟩
    let e := (trivializationAt G V x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt G V x)
    ∃ A : (E × G) ≃L[ℝ] F,
      HasFDerivAt (fun p ↦ chartAt F (f x)
        (T.totalMap f hf ((chartAt (E × G) z).symm p)))
        A.toContinuousLinearMap (chartAt (E × G) z z) ∧
      (∀ v : E, A (v, 0) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v) ∧
      ∀ w : G, (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
        (A (0, w)) = e.symm w := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let G := NormalModel E F
  let NB := TotalSpace G V
  let : ChartedSpace (E × G) NB := inferInstanceAs (ChartedSpace (ModelProd E G) NB)
  let z : NB := ⟨x, 0⟩
  let t := trivializationAt G V x
  have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt G V x
  let e := t.continuousLinearEquivAt ℝ x hx
  let κ := chartAt E x
  let a := κ x
  let φ := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) z
  let ψ := chartAt F (f x)
  let C : E × G → F := ψ ∘ T.totalMap f hf ∘ φ.symm
  let D : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  let Q : F →ₗ[ℝ] V x := (LinearMap.range D.toLinearMap).mkQ
  have hφzero : φ z = (a, 0) := by
    dsimp only [φ]
    rw [FiberBundle.extChartAt]
    change (κ (t ⟨x, 0⟩).1, (t ⟨x, 0⟩).2) = _
    rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx, map_zero]
  have hφvertical (w : G) : φ.symm (a, w) = (⟨x, e.symm w⟩ : NB) := by
    dsimp only [φ]
    rw [FiberBundle.extChartAt]
    change t.toOpenPartialHomeomorph.symm (κ.symm (κ x), w) = _
    rw [κ.left_inv (mem_chart_source E x)]
    exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm x hx w
  have hφhorizontal : (fun u : E ↦ φ.symm (u, 0)) =ᶠ[𝓝 a]
      (fun u : E ↦ (⟨κ.symm u, 0⟩ : NB)) := by
    have hκ : ContinuousAt κ.symm a := κ.continuousAt_symm
      (κ.map_source (mem_chart_source E x))
    have hκx : κ.symm a = x := κ.left_inv (mem_chart_source E x)
    filter_upwards [hκ (hκx ▸ t.open_baseSet.mem_nhds hx)] with u hu
    dsimp only [φ]
    rw [FiberBundle.extChartAt]
    change t.toOpenPartialHomeomorph.symm (κ.symm u, 0) = _
    rw [t.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ hu, map_zero]
  -- The actual tube is smooth on its original quotient bundle, before any metric frame change.
  have hT : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) ∞ (T.totalMap f hf) :=
    contMDiff_subtype_val.comp T.diffeomorph.contMDiff
  have hzero (y : M) : T.totalMap f hf ⟨y, 0⟩ = f y := T.map_zero y
  have hC : ContDiffAt ℝ ∞ C (a, 0) := by
    have h := (contMDiffAt_iff.mp (hT z)).2
    change ContDiffWithinAt ℝ ∞
      (extChartAt 𝓘(ℝ, F) (T.totalMap f hf z) ∘ T.totalMap f hf ∘ φ.symm)
      (Set.range (𝓘(ℝ, E).prod 𝓘(ℝ, G))) (φ z) at h
    rw [hφzero, hzero x] at h
    simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using! h
  let A := fderiv ℝ C (a, 0)
  have hA : HasFDerivAt C A (a, 0) := (hC.differentiableAt (by simp)).hasFDerivAt
  have hD : HasFDerivAt (ψ ∘ f ∘ κ.symm) D a := by
    simpa only [writtenInExtChartAt, mfld_simps, hasFDerivWithinAt_univ] using!
      (f.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.2
  have hhorizontal (v : E) : A (v, 0) = D v := by
    have heq : (fun u : E ↦ C (u, 0)) =ᶠ[𝓝 a] (ψ ∘ f ∘ κ.symm) := by
      filter_upwards [hφhorizontal] with u hu
      change ψ (T.totalMap f hf (φ.symm (u, 0))) = ψ (f (κ.symm u))
      rw [hu, hzero]
    have hc : HasFDerivAt (fun u : E ↦ C (u, 0))
        (A.comp (ContinuousLinearMap.inl ℝ E G)) a := by
      simpa only [Function.comp_def] using!
        HasFDerivAt.comp a hA (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : G))
    exact congrArg (fun L : E →L[ℝ] F ↦ L v)
      ((hc.congr_of_eventuallyEq heq.symm).unique hD)
  have hinc : ContMDiff 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
      (fun w : G ↦ (⟨x, e.symm w⟩ : NB)) := by
    intro w
    apply (t.contMDiffAt_iff (t.mem_source.mpr hx)).mpr
    refine ⟨contMDiffAt_const, ?_⟩
    have heq : (fun v : G ↦ (t (⟨x, e.symm v⟩ : NB)).2) = id := by
      funext v
      rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx]
      exact e.apply_symm_apply v
    rw [heq]
    exact contMDiffAt_id
  -- The normalized quotient derivative is the actual vertical block of this same A.
  have hvertical (w : G) : Q (A (0, w)) = e.symm w := by
    let g : G → N := fun v ↦ T.totalMap f hf (⟨x, e.symm v⟩ : NB)
    have hg := ((hT.comp hinc) 0).mdifferentiableAt (by simp)
    have hDg : HasFDerivAt (fun v : G ↦ ψ (g v))
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) g 0) 0 := by
      have h := hg.hasMFDerivAt.2
      simpa only [writtenInExtChartAt, mfld_simps, map_zero, hzero,
        hasFDerivWithinAt_univ, g] using! h
    have heq : (fun v : G ↦ C (a, v)) = (fun v : G ↦ ψ (g v)) := by
      funext v
      exact congrArg (ψ ∘ T.totalMap f hf) (hφvertical v)
    have hd := hA.comp 0 (hasFDerivAt_prodMk_right a (0 : G))
    simp only [Function.comp_def] at hd
    rw [heq] at hd
    have hAw := congrArg (fun L : G →L[ℝ] F ↦ L w) (hd.unique hDg)
    change A (0, w) = mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) g 0 w at hAw
    rw [hAw]
    exact T.normal_deriv x w
  have hdecomp (v : E) (w : G) : A (v, w) = D v + A (0, w) := by
    calc
      A (v, w) = A ((v, 0) + (0, w)) := by congr 1; simp
      _ = A (v, 0) + A (0, w) := A.map_add _ _
      _ = _ := by rw [hhorizontal]
  have hQD (v : E) : Q (D v) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
  -- The quotient separates the original tangent block from the normal block.
  have hbij : Function.Bijective A := by
    constructor
    · apply (injective_iff_map_eq_zero A).mpr
      rintro ⟨v, w⟩ h
      have hq := congrArg Q h
      rw [hdecomp, map_add, hQD, hvertical, map_zero, zero_add] at hq
      have hw : w = 0 := e.symm.injective (hq.trans e.symm.map_zero.symm)
      subst w
      rw [hhorizontal] at h
      exact Prod.ext (hf.mfderiv_injective (by simp) x (h.trans D.map_zero.symm)) rfl
    · intro y
      let w := e (Q y)
      have hq : Q (y - A (0, w)) = 0 := by
        rw [map_sub, hvertical, e.symm_apply_apply, sub_self]
      obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
      refine ⟨(v, w), ?_⟩
      rw [hdecomp]
      change D v = y - A (0, w) at hv
      rw [hv, sub_add_cancel]
  let L := (LinearEquiv.ofBijective A.toLinearMap hbij).toContinuousLinearEquiv
  refine ⟨L, ?_, hhorizontal, hvertical⟩
  change HasFDerivAt C A (φ z)
  rw [hφzero]
  exact hA


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem native_tangent_blocks {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞) (z : TangentBundle 𝓘(ℝ, E) M) :
    (∀ v : E × E,
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z v).1 =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj v.1) ∧
    ∀ v : E, mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z (0, v) =
      (0, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj v) := by
  have native_trivM (x : M) (w : TangentSpace 𝓘(ℝ, E) x) :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) x) w = w := by
    rw [Trivialization.coe_continuousLinearEquivAt_eq]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source E x),
      mfderiv_extChartAt_self]
    rfl
  have native_chartM (z : TangentBundle 𝓘(ℝ, E) M) (w : E) :
      chartAt (E × E) z (⟨z.proj, w⟩ : TangentBundle 𝓘(ℝ, E) M) =
        (chartAt E z.proj z.proj, w) := by
    apply Prod.ext
    · rfl
    · change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj
          ⟨z.proj, w⟩).2 = w
      exact native_trivM z.proj w
  have affine_smoothM (z : TangentBundle 𝓘(ℝ, E) M) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × E) ∞
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
    intro a
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_const
    · simp only [show ∀ b : E, (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj
          ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from b)⟩).2 = (show E from z.snd)
            + b from fun b ↦ native_trivM _ _]
      change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun b : E ↦ (show E from z.snd) + b) a
      exact (contMDiffAt_const.add contMDiffAt_id :
          ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun b : E ↦ (show E from z.snd) + b) a)
  have affine_derivM (z : TangentBundle 𝓘(ℝ, E) M) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E)
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) 0 =
          ContinuousLinearMap.inr ℝ E E := by
    let g : E → TangentBundle 𝓘(ℝ, E) M := fun a ↦ ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E)
      z.proj from a)⟩
    have hg0 : g 0 = z := by simp [g]
    have hg := (affine_smoothM z 0).mdifferentiableAt (by simp)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E × E))
      (mem_chart_source (E × E) (g 0))
    have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E × E))
      (I'' := 𝓘(ℝ, E × E)) 0 hc hg
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    rw [← hd]
    have heq : (extChartAt 𝓘(ℝ, E × E) (g 0) ∘ g) =
        (fun a : E ↦ (chartAt E z.proj z.proj, (show E from z.snd) + a)) := by
      funext a
      rw [hg0]
      exact native_chartM z _
    rw [heq, mfderiv_eq_fderiv]
    change fderiv ℝ (fun a : E ↦ (chartAt E z.proj z.proj, (show E from z.snd) + a)) 0 = _
    convert! ((hasFDerivAt_const (chartAt E z.proj z.proj) (0 : E)).prodMk
      ((hasFDerivAt_const (show E from z.snd) (0 : E)).add (hasFDerivAt_id (0 : E)))).fderiv using 1
    · ext w <;> simp
    · infer_instance
    · infer_instance
  have vertical_formulaM (z : TangentBundle 𝓘(ℝ, E) M) :
      tangentVerticalLift E M z = ContinuousLinearMap.inr ℝ E E := by
    let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj).continuousLinearEquivAt
      ℝ z.proj (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj)
    have he (w : E) : e w = w := native_trivM z.proj w
    have hei (w : E) : e.symm w = w := by
      rw [← he (e.symm w), e.apply_symm_apply]
    have hg : (fun a : E ↦ (⟨z.proj, z.snd + e.symm a⟩ : TangentBundle 𝓘(ℝ, E) M)) =
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
      funext a
      rw [hei]
    change ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) _ 0).comp
      (NormedSpace.fromTangentSpace (0 : E)).symm.toContinuousLinearMap).comp
      e.toContinuousLinearMap = _
    rw [hg, affine_derivM z]
    ext w
    change (0, e w) = (0, w)
    rw [he]
  have projection_formulaM (z : TangentBundle 𝓘(ℝ, E) M) :
      mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (smoothTangentBundleProjection E M) z =
        ContinuousLinearMap.fst ℝ E E := by
    let p := smoothTangentBundleProjection E M
    have hp := p.contMDiff.mdifferentiable (by simp) z
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
      (mem_chart_source E z.proj)
    have hd := mfderiv_comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) z hc hp
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    have heq : (extChartAt 𝓘(ℝ, E) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M)) =
        Prod.fst ∘ extChartAt 𝓘(ℝ, E × E) z := rfl
    change (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M)) z :
        (E × E) →L[ℝ] E) = (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
          (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M) z : (E × E) →L[ℝ] E) at hd
    have hf : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) Prod.fst
        (extChartAt 𝓘(ℝ, E × E) z z) := differentiableAt_fst.mdifferentiableAt
    rw [heq, mfderiv_comp z hf (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E × E))
      (mem_chart_source (E × E) z)), mfderiv_extChartAt_self,
      ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] at hd
    change fderiv ℝ (Prod.fst : E × E → E) _ = _ at hd
    rw [fderiv_fst] at hd
    exact hd.symm
  have native_trivN (x : N) (w : TangentSpace 𝓘(ℝ, F) x) :
      (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) x) w = w := by
    rw [Trivialization.coe_continuousLinearEquivAt_eq]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source F x),
      mfderiv_extChartAt_self]
    rfl
  have native_chartN (z : TangentBundle 𝓘(ℝ, F) N) (w : F) :
      chartAt (F × F) z (⟨z.proj, w⟩ : TangentBundle 𝓘(ℝ, F) N) =
        (chartAt F z.proj z.proj, w) := by
    apply Prod.ext
    · rfl
    · change (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj
          ⟨z.proj, w⟩).2 = w
      exact native_trivN z.proj w
  have affine_smoothN (z : TangentBundle 𝓘(ℝ, F) N) :
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F × F) ∞
        (fun a : F ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, F) N)) := by
    intro a
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_const
    · simp only [show ∀ b : F, (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj
          ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from b)⟩).2 = (show F from z.snd)
            + b from fun b ↦ native_trivN _ _]
      change ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun b : F ↦ (show F from z.snd) + b) a
      exact (contMDiffAt_const.add contMDiffAt_id :
          ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ (fun b : F ↦ (show F from z.snd) + b) a)
  have affine_derivN (z : TangentBundle 𝓘(ℝ, F) N) :
      mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F)
        (fun a : F ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, F) N)) 0 =
          ContinuousLinearMap.inr ℝ F F := by
    let g : F → TangentBundle 𝓘(ℝ, F) N := fun a ↦ ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F)
      z.proj from a)⟩
    have hg0 : g 0 = z := by simp [g]
    have hg := (affine_smoothN z 0).mdifferentiableAt (by simp)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F × F))
      (mem_chart_source (F × F) (g 0))
    have hd := mfderiv_comp (I := 𝓘(ℝ, F)) (I' := 𝓘(ℝ, F × F))
      (I'' := 𝓘(ℝ, F × F)) 0 hc hg
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    rw [← hd]
    have heq : (extChartAt 𝓘(ℝ, F × F) (g 0) ∘ g) =
        (fun a : F ↦ (chartAt F z.proj z.proj, (show F from z.snd) + a)) := by
      funext a
      rw [hg0]
      exact native_chartN z _
    rw [heq, mfderiv_eq_fderiv]
    change fderiv ℝ (fun a : F ↦ (chartAt F z.proj z.proj, (show F from z.snd) + a)) 0 = _
    convert! ((hasFDerivAt_const (chartAt F z.proj z.proj) (0 : F)).prodMk
      ((hasFDerivAt_const (show F from z.snd) (0 : F)).add (hasFDerivAt_id (0 : F)))).fderiv using 1
    · ext w <;> simp
    · infer_instance
    · infer_instance
  have vertical_formulaN (z : TangentBundle 𝓘(ℝ, F) N) :
      tangentVerticalLift F N z = ContinuousLinearMap.inr ℝ F F := by
    let e := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj).continuousLinearEquivAt
      ℝ z.proj (mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) z.proj)
    have he (w : F) : e w = w := native_trivN z.proj w
    have hei (w : F) : e.symm w = w := by
      rw [← he (e.symm w), e.apply_symm_apply]
    have hg : (fun a : F ↦ (⟨z.proj, z.snd + e.symm a⟩ : TangentBundle 𝓘(ℝ, F) N)) =
        (fun a : F ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, F) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, F) N)) := by
      funext a
      rw [hei]
    change ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) _ 0).comp
      (NormedSpace.fromTangentSpace (0 : F)).symm.toContinuousLinearMap).comp
      e.toContinuousLinearMap = _
    rw [hg, affine_derivN z]
    ext w
    change (0, e w) = (0, w)
    rw [he]
  have projection_formulaN (z : TangentBundle 𝓘(ℝ, F) N) :
      mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N) z =
        ContinuousLinearMap.fst ℝ F F := by
    let p := smoothTangentBundleProjection F N
    have hp := p.contMDiff.mdifferentiable (by simp) z
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F))
      (mem_chart_source F z.proj)
    have hd := mfderiv_comp (I := 𝓘(ℝ, F × F)) (I' := 𝓘(ℝ, F))
      (I'' := 𝓘(ℝ, F)) z hc hp
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    have heq : (extChartAt 𝓘(ℝ, F) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) N → N)) =
        Prod.fst ∘ extChartAt 𝓘(ℝ, F × F) z := rfl
    change (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
      (extChartAt 𝓘(ℝ, F) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) N → N)) z :
        (F × F) →L[ℝ] F) = (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F)
          (TotalSpace.proj : TangentBundle 𝓘(ℝ, F) N → N) z : (F × F) →L[ℝ] F) at hd
    have hf : MDifferentiableAt 𝓘(ℝ, F × F) 𝓘(ℝ, F) Prod.fst
        (extChartAt 𝓘(ℝ, F × F) z z) := differentiableAt_fst.mdifferentiableAt
    rw [heq, mfderiv_comp z hf (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, F × F))
      (mem_chart_source (F × F) z)), mfderiv_extChartAt_self,
      ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] at hd
    change fderiv ℝ (Prod.fst : F × F → F) _ = _ at hd
    rw [fderiv_fst] at hd
    exact hd.symm
  have hNat
      (z : TangentBundle 𝓘(ℝ, E) M) :
      (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z).comp
          (tangentVerticalLift E M z) =
        (tangentVerticalLift F N (smoothTangentMap f z)).comp
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) := by
    let a : E → TangentBundle 𝓘(ℝ, E) M := fun v ↦
      ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from v)⟩
    let b : F → TangentBundle 𝓘(ℝ, F) N := fun v ↦
      ⟨f z.proj, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj) z.snd +
        (show TangentSpace 𝓘(ℝ, F) (f z.proj) from v)⟩
    let L : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj
    have ha0 : a 0 = z := by simp [a]
    have hb0 : b 0 = smoothTangentMap f z := by simp [b, smoothTangentMap, tangentMap]
    have ha : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 :=
      (affine_smoothM z 0).mdifferentiableAt (by simp)
    have hb : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 :=
      (affine_smoothN (smoothTangentMap f z) 0).mdifferentiableAt (by simp)
    have heq : smoothTangentMap f ∘ a = b ∘ L := by
      funext v
      change (⟨f z.proj, L ((show E from z.snd) + v)⟩ : TangentBundle 𝓘(ℝ, F) N) =
        ⟨f z.proj, L z.snd + L v⟩
      exact congrArg (fun w ↦ (⟨f z.proj, w⟩ : TangentBundle 𝓘(ℝ, F) N))
        (map_add L (show E from z.snd) v)
    have hleft := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E × E))
      (I'' := 𝓘(ℝ, F × F)) 0
      (ha0 ▸ (smoothTangentMap f).contMDiff.mdifferentiable (by simp) z) ha
    have hright := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
      (I'' := 𝓘(ℝ, F × F)) 0
      (show MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F × F) b (L 0) from by simpa using hb)
      ((L.contDiff (n := ∞)).contMDiff.mdifferentiableAt (by simp))
    have hLder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) L 0 = L := by
      rw [mfderiv_eq_fderiv]
      exact L.fderiv
    have hDa : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) a 0 = ContinuousLinearMap.inr ℝ E E :=
      affine_derivM z
    have hDb : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 = ContinuousLinearMap.inr ℝ F F :=
      affine_derivN (smoothTangentMap f z)
    rw [heq, hright, hDa, hLder] at hleft
    have hzder : mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) (a 0) =
        mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z := by
      congr 1
    rw [hzder] at hleft
    have hzero : L 0 = 0 := map_zero L
    have hbder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b (L 0) =
        mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F × F) b 0 := by
      congr 1
    rw [hbder, hDb] at hleft
    rw [vertical_formulaM z, vertical_formulaN (smoothTangentMap f z)]
    exact hleft.symm
  have hcomm :
      (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N)
        (smoothTangentMap f z)).comp
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z) =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).comp
          (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (smoothTangentBundleProjection E M) z) := by
    have hleft := mfderiv_comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ, F × F))
      (I'' := 𝓘(ℝ, F)) z
      ((smoothTangentBundleProjection F N).contMDiff.mdifferentiable (by simp) _)
      ((smoothTangentMap f).contMDiff.mdifferentiable (by simp) z)
    have hright := mfderiv_comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, F)) z (f.contMDiff.mdifferentiable (by simp) z.proj)
      ((smoothTangentBundleProjection E M).contMDiff.mdifferentiable (by simp) z)
    exact hleft.symm.trans hright
  constructor
  · intro v
    rw [projection_formulaN, projection_formulaM] at hcomm
    exact congrArg (fun L : (E × E) →L[ℝ] F ↦ L v) hcomm
  · intro v
    have h := hNat z
    rw [vertical_formulaM, vertical_formulaN] at h
    exact congrArg (fun L : E →L[ℝ] (F × F) ↦ L v) h


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem native_tangent_differentials {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] :
    (∀ z : TangentBundle 𝓘(ℝ, E) M,
      mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (smoothTangentBundleProjection E M) z =
        ContinuousLinearMap.fst ℝ E E) ∧
    ∀ z : TangentBundle 𝓘(ℝ, E) M,
      tangentVerticalLift E M z = ContinuousLinearMap.inr ℝ E E := by
  have native_trivM (x : M) (w : TangentSpace 𝓘(ℝ, E) x) :
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearEquivAt ℝ x
        (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) x) w = w := by
    rw [Trivialization.coe_continuousLinearEquivAt_eq]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source E x),
      mfderiv_extChartAt_self]
    rfl
  have native_chartM (z : TangentBundle 𝓘(ℝ, E) M) (w : E) :
      chartAt (E × E) z (⟨z.proj, w⟩ : TangentBundle 𝓘(ℝ, E) M) =
        (chartAt E z.proj z.proj, w) := by
    apply Prod.ext
    · rfl
    · change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj
          ⟨z.proj, w⟩).2 = w
      exact native_trivM z.proj w
  have affine_smoothM (z : TangentBundle 𝓘(ℝ, E) M) :
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E × E) ∞
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
    intro a
    rw [modelWithCornersSelf_prod, Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_const
    · simp only [show ∀ b : E, (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj
          ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from b)⟩).2 = (show E from z.snd)
            + b from fun b ↦ native_trivM _ _]
      change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun b : E ↦ (show E from z.snd) + b) a
      exact (contMDiffAt_const.add contMDiffAt_id :
          ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun b : E ↦ (show E from z.snd) + b) a)
  have affine_derivM (z : TangentBundle 𝓘(ℝ, E) M) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E)
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) 0 =
          ContinuousLinearMap.inr ℝ E E := by
    let g : E → TangentBundle 𝓘(ℝ, E) M := fun a ↦ ⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E)
      z.proj from a)⟩
    have hg0 : g 0 = z := by simp [g]
    have hg := (affine_smoothM z 0).mdifferentiableAt (by simp)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E × E))
      (mem_chart_source (E × E) (g 0))
    have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E × E))
      (I'' := 𝓘(ℝ, E × E)) 0 hc hg
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    rw [← hd]
    have heq : (extChartAt 𝓘(ℝ, E × E) (g 0) ∘ g) =
        (fun a : E ↦ (chartAt E z.proj z.proj, (show E from z.snd) + a)) := by
      funext a
      rw [hg0]
      exact native_chartM z _
    rw [heq, mfderiv_eq_fderiv]
    change fderiv ℝ (fun a : E ↦ (chartAt E z.proj z.proj, (show E from z.snd) + a)) 0 = _
    convert! ((hasFDerivAt_const (chartAt E z.proj z.proj) (0 : E)).prodMk
      ((hasFDerivAt_const (show E from z.snd) (0 : E)).add (hasFDerivAt_id (0 : E)))).fderiv using 1
    · ext w <;> simp
    · infer_instance
    · infer_instance
  have vertical_formulaM (z : TangentBundle 𝓘(ℝ, E) M) :
      tangentVerticalLift E M z = ContinuousLinearMap.inr ℝ E E := by
    let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj).continuousLinearEquivAt
      ℝ z.proj (mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) z.proj)
    have he (w : E) : e w = w := native_trivM z.proj w
    have hei (w : E) : e.symm w = w := by
      rw [← he (e.symm w), e.apply_symm_apply]
    have hg : (fun a : E ↦ (⟨z.proj, z.snd + e.symm a⟩ : TangentBundle 𝓘(ℝ, E) M)) =
        (fun a : E ↦ (⟨z.proj, z.snd + (show TangentSpace 𝓘(ℝ, E) z.proj from a)⟩ :
          TangentBundle 𝓘(ℝ, E) M)) := by
      funext a
      rw [hei]
    change ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E × E) _ 0).comp
      (NormedSpace.fromTangentSpace (0 : E)).symm.toContinuousLinearMap).comp
      e.toContinuousLinearMap = _
    rw [hg, affine_derivM z]
    ext w
    change (0, e w) = (0, w)
    rw [he]
  have projection_formulaM (z : TangentBundle 𝓘(ℝ, E) M) :
      mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (smoothTangentBundleProjection E M) z =
        ContinuousLinearMap.fst ℝ E E := by
    let p := smoothTangentBundleProjection E M
    have hp := p.contMDiff.mdifferentiable (by simp) z
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
      (mem_chart_source E z.proj)
    have hd := mfderiv_comp (I := 𝓘(ℝ, E × E)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) z hc hp
    rw [mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    have heq : (extChartAt 𝓘(ℝ, E) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M)) =
        Prod.fst ∘ extChartAt 𝓘(ℝ, E × E) z := rfl
    change (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) z.proj ∘ (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M)) z :
        (E × E) →L[ℝ] E) = (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E)
          (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) M → M) z : (E × E) →L[ℝ] E) at hd
    have hf : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) Prod.fst
        (extChartAt 𝓘(ℝ, E × E) z z) := differentiableAt_fst.mdifferentiableAt
    rw [heq, mfderiv_comp z hf (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E × E))
      (mem_chart_source (E × E) z)), mfderiv_extChartAt_self,
      ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] at hd
    change fderiv ℝ (Prod.fst : E × E → E) _ = _ at hd
    rw [fderiv_fst] at hd
    exact hd.symm
  exact ⟨projection_formulaM, vertical_formulaM⟩

attribute [local instance] normalBundleTopology

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem native_quotient_blocks {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (S : TangentNormalSplitting f hf) (z : TangentBundle 𝓘(ℝ, E) M) :
    let q := (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ
    let D := mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z
    let qT := (LinearMap.range D.toLinearMap).mkQ
    let σ := (S.equiv z).toLinearMap.comp qT
    (∀ w : F × F, (σ w).1 = q w.1) ∧
    (∀ w : F, σ (0, w) = (0, q w)) ∧
    ∀ v : E × E, σ (D v) = 0 := by
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let := normalBundleContMDiffVectorBundle f hf.isImmersion
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let q := (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ
  let D := mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z
  let qT := (LinearMap.range D.toLinearMap).mkQ
  let σ := (S.equiv z).toLinearMap.comp qT
  obtain ⟨hproj, hvertical⟩ := native_tangent_differentials (E := F) (M := N)
  have hi := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.1
  have hp := (exists_tangentNormal_exactSequence f hf).choose_spec.choose_spec.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro w
    change (S.equiv z (qT w)).1 = q w.1
    rw [S.fst_equiv]
    have h := hp z w
    change tangentNormalProjection f hf z (qT w) =
      q (mfderiv 𝓘(ℝ, F × F) 𝓘(ℝ, F) (smoothTangentBundleProjection F N)
        (smoothTangentMap f z) w) at h
    rw [hproj] at h
    exact h
  · intro w
    have h := hi z w
    change tangentNormalVerticalMap f hf z (q w) =
      qT (tangentVerticalLift F N (smoothTangentMap f z) w) at h
    rw [hvertical] at h
    change tangentNormalVerticalMap f hf z (q w) = qT (0, w) at h
    change S.equiv z (qT (0, w)) = (0, q w)
    rw [← h]
    exact S.equiv_vertical z (q w)
  · intro v
    have hq : qT (D v) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
    change S.equiv z (qT (D v)) = 0
    rw [hq, map_zero]


set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original tangent tube has determinant one after normalization by the same doubled
base tangent-normal lift and the specified canonical normal splitting. -/
theorem exists_tangentTube_normalized_derivative {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (S : TangentNormalSplitting f hf)
    (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
    (z : TangentBundle 𝓘(ℝ, E) M) :
    letI := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    letI := normalBundleContMDiffVectorBundle
      (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
    let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
    let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
    let VT := NormalModel (E × E) (F × F)
    letI : ChartedSpace ((E × E) × VT) (TotalSpace VT νT) :=
      inferInstanceAs (ChartedSpace (ModelProd (E × E) VT) (TotalSpace VT νT))
    let z₀ : TotalSpace VT νT := ⟨z, 0⟩
    let c := chartAt ((E × E) × VT) z₀
    let eT := (trivializationAt VT νT z).continuousLinearEquivAt ℝ z
      (mem_baseSet_trivializationAt VT νT z)
    ∃ e : (E × ν z.proj) ≃L[ℝ] F,
      (∀ v : E, e (v, 0) = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj v) ∧
      (∀ w : E × ν z.proj,
        (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj).toLinearMap).mkQ (e w) = w.2) ∧
      ∃ A : ((E × E) × VT) ≃L[ℝ] (F × F),
        HasFDerivAt (fun p ↦ chartAt (F × F) (smoothTangentMap f z)
          (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf) (c.symm p)))
          A.toContinuousLinearMap (c z₀) ∧
        let J := LinearEquiv.prodProdProdComm ℝ E E (ν z.proj) (ν z.proj)
        let C := A.toLinearMap.comp (LinearMap.prodMap (LinearMap.id : (E × E) →ₗ[ℝ] _)
          (eT.toLinearMap.comp (S.equiv z).symm.toLinearMap))
        LinearMap.det ((e.prodCongr e).symm.toLinearMap.comp (C.comp J.symm.toLinearMap)) = 1 := by
  classical
  let := normalBundleFiberBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleVectorBundle (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let := normalBundleContMDiffVectorBundle
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
  let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
  let VT := NormalModel (E × E) (F × F)
  let : ChartedSpace ((E × E) × VT) (TotalSpace VT νT) :=
    inferInstanceAs (ChartedSpace (ModelProd (E × E) VT) (TotalSpace VT νT))
  let eT := (trivializationAt VT νT z).continuousLinearEquivAt ℝ z
    (mem_baseSet_trivializationAt VT νT z)
  let D₀ : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z.proj
  let q : F →ₗ[ℝ] ν z.proj := (LinearMap.range D₀.toLinearMap).mkQ
  let D : (E × E) →L[ℝ] (F × F) :=
    mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f) z
  let qT : (F × F) →ₗ[ℝ] νT z := (LinearMap.range D.toLinearMap).mkQ
  let σ := (S.equiv z).toLinearMap.comp qT
  -- Choose a lift of the actual quotient, keeping df as the stable tangent summand.
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  have hqs (w : ν z.proj) : q (s w) = w := congrArg (fun L ↦ L w) hs
  have hqD (v : E) : q (D₀ v) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
  let L : (E × ν z.proj) →ₗ[ℝ] F := D₀.toLinearMap.coprod s
  have hL : Function.Bijective L := by
    constructor
    · apply (injective_iff_map_eq_zero L).mpr
      rintro ⟨v, w⟩ h
      have hw := congrArg q h
      change q (D₀ v + s w) = q 0 at hw
      rw [map_add, hqD, hqs, map_zero, zero_add] at hw
      subst w
      change D₀ v + s 0 = 0 at h
      rw [map_zero, add_zero] at h
      exact Prod.ext (hf.isImmersion.mfderiv_injective (by simp) z.proj
        (h.trans D₀.map_zero.symm)) rfl
    · intro y
      have hq : q (y - s (q y)) = 0 := by rw [map_sub, hqs, sub_self]
      obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
      refine ⟨(v, q y), ?_⟩
      change D₀ v + s (q y) = y
      change D₀ v = y - s (q y) at hv
      rw [hv, sub_add_cancel]
  let e : (E × ν z.proj) ≃L[ℝ] F :=
    (LinearEquiv.ofBijective L hL).toContinuousLinearEquiv
  have hefirst (v : E) : e (v, 0) = D₀ v := by
    change D₀ v + s 0 = D₀ v
    rw [map_zero, add_zero]
  have hequot (w : E × ν z.proj) : q (e w) = w.2 := by
    change q (D₀ w.1 + s w.2) = w.2
    rw [map_add, hqD, hqs, zero_add]
  have hqcoord (w : F) : (e.symm w).2 = q w := by
    rw [← hequot (e.symm w), e.apply_symm_apply]
  obtain ⟨A, hA, hAtangent, hAnormal⟩ := native_tube_derivative
    (smoothTangentMap f) (isImmersion_smoothTangentMap f hf) T z
  change ∀ v : E × E, A (v, 0) = D v at hAtangent
  change ∀ w : VT, qT (A (0, w)) = eT.symm w at hAnormal
  let R : (ν z.proj × ν z.proj) →ₗ[ℝ] (F × F) :=
    A.toLinearMap.comp ((LinearMap.inr ℝ (E × E) VT).comp
      (eT.toLinearMap.comp (S.equiv z).symm.toLinearMap))
  have hσR (w : ν z.proj × ν z.proj) : σ (R w) = w := by
    change S.equiv z (qT (A (0, eT ((S.equiv z).symm w)))) = w
    rw [hAnormal, eT.symm_apply_apply, (S.equiv z).apply_symm_apply]
  obtain ⟨hDfirst, hDvertical⟩ := native_tangent_blocks f z
  obtain ⟨hσfirst, hσvertical, hσD⟩ := native_quotient_blocks f hf S z
  have hdet := normalized_double_det e.toLinearEquiv D.toLinearMap σ R
    (fun p ↦ (hDfirst p).trans (hefirst p.1).symm)
    (fun v ↦ (hDvertical v).trans (congrArg (fun w : F ↦ (0, w)) (hefirst v).symm))
    hσD hσR
    (fun p ↦ (hσfirst p).trans (hqcoord p.1).symm)
    (fun w ↦ (hσvertical w).trans (congrArg (fun w : ν z.proj ↦ (0, w)) (hqcoord w).symm))
  refine ⟨e, hefirst, hequot, A, hA, ?_⟩
  have hC : A.toLinearMap.comp (LinearMap.prodMap (LinearMap.id : (E × E) →ₗ[ℝ] _)
      (eT.toLinearMap.comp (S.equiv z).symm.toLinearMap)) =
      D.toLinearMap.comp (LinearMap.fst ℝ (E × E) (ν z.proj × ν z.proj)) +
        R.comp (LinearMap.snd ℝ (E × E) (ν z.proj × ν z.proj)) := by
    apply LinearMap.ext
    rintro ⟨v, w⟩
    change A (v, eT ((S.equiv z).symm w)) = D v + A (0, eT ((S.equiv z).symm w))
    rw [← hAtangent v, ← map_add]
    congr 1
    simp
  rw [hC]
  exact hdet

end AtiyahSinger
