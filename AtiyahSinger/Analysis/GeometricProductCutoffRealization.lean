/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricTensorDomain
public import AtiyahSinger.Analysis.ProductCutoffRealization
public import AtiyahSinger.Analysis.SchwartzTensorDensity
public import AtiyahSinger.Analysis.SmoothProjectionApproximation
public import AtiyahSinger.Geometry.ExternalTensorChartCutoff

/-!
# Product cutoffs on the original geometric Sobolev domain

Public module ID: M0657.

The local Fourier cutoff is compared with the actual factorwise action in the
same Bessel coordinates. These comparisons are the inputs to finite-atlas
assembly on the native external tensor bundles.

Source: SG III.13.5, pp.249--250. The factorwise lift is not assumed to be an
isotropic symbol. Its error is the already constructed bounded Fourier error.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap TensorProduct

set_option maxSynthPendingDepth 40

/-- Tensoring a coefficient matrix with the identity in the original finite tensor basis.
This implementation map fixes the coordinate ordering used by the product PDO pieces. -/
def tensorIdentitySymbolMap (r q s : ℕ) :
    (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℂ]
      (EuclideanSpace ℂ (Fin (r * s)) →L[ℂ] EuclideanSpace ℂ (Fin (q * s))) := by
  let ei := (((EuclideanSpace.basisFun (Fin r) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin s) ℂ)).reindex finProdFinEquiv).repr.toContinuousLinearEquiv
  let eo := (((EuclideanSpace.basisFun (Fin q) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin s) ℂ)).reindex finProdFinEquiv).repr.toContinuousLinearEquiv
  let Φ : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin (r * s)) →L[ℂ] EuclideanSpace ℂ (Fin (q * s))) := {
    toFun a := eo.toContinuousLinearMap.comp
      ((TensorProduct.mapL a (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin s)))).comp
        ei.symm.toContinuousLinearMap)
    map_add' a b := by
      rw [TensorProduct.mapL_add_left, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_add]
    map_smul' c a := by
      rw [TensorProduct.mapL_smul_left, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul]
      rfl }
  exact Φ.toContinuousLinearMap

/-- The tensor coefficient map acts in the fixed finite-coordinate order on pure tensors. -/
theorem tensorIdentitySymbolMap_apply {r q s : ℕ}
    (a : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (u : EuclideanSpace ℂ (Fin r)) (v : EuclideanSpace ℂ (Fin s))
    (w : EuclideanSpace ℂ (Fin (r * s)))
    (hw : ∀ i j, w (finProdFinEquiv (i, j)) = u i * v j) (i : Fin q) (j : Fin s) :
    tensorIdentitySymbolMap r q s a w (finProdFinEquiv (i, j)) = a u i * v j := by
  let e (d : ℕ) := (((EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin s) ℂ)).reindex finProdFinEquiv).repr.toContinuousLinearEquiv
  have he (d : ℕ) (x : EuclideanSpace ℂ (Fin d)) (y : EuclideanSpace ℂ (Fin s))
      (a : Fin d) (b : Fin s) : e d (x ⊗ₜ[ℂ] y) (finProdFinEquiv (a, b)) = x a * y b := by
    change (((EuclideanSpace.basisFun (Fin d) ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin s) ℂ)).reindex finProdFinEquiv).repr
        (x ⊗ₜ[ℂ] y) (finProdFinEquiv (a, b)) = _
    rw [OrthonormalBasis.repr_reindex, OrthonormalBasis.tensorProduct_repr_tmul_apply']
    simp only [EuclideanSpace.basisFun_repr, Equiv.symm_apply_apply]
    exact mul_comm _ _
  have hw' : w = e r (u ⊗ₜ[ℂ] v) := by
    apply PiLp.ext
    intro k
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [hw, he]
  change e q ((TensorProduct.mapL a (ContinuousLinearMap.id ℂ _)) ((e r).symm w))
    (finProdFinEquiv (i, j)) = _
  rw [hw', (e r).symm_apply_apply, TensorProduct.mapL_tmul, ContinuousLinearMap.id_apply]
  exact he q (a u) v i j

/-- Tensoring the finite coefficient space commutes with the original Fourier quantizer. -/
theorem quantize_tensorIdentitySymbolMap {n r q s : ℕ}
    (a : SymbolFunction n r q)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (v : EuclideanSpace ℂ (Fin s))
    (w : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (r * s))))
    (hw : ∀ x i j, w x (finProdFinEquiv (i, j)) = u x i * v j)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin q) (j : Fin s) :
    quantize (fun y ξ ↦ tensorIdentitySymbolMap r q s (a y ξ)) w x
      (finProdFinEquiv (i, j)) = quantize a u x i * v j := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let J (d : ℕ) : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin (d * s)) :=
    LinearMap.toContinuousLinearMap {
      toFun z := WithLp.toLp 2 (fun k ↦ z (finProdFinEquiv.symm k).1 *
        v (finProdFinEquiv.symm k).2)
      map_add' z z' := by ext k; simp [add_mul]
      map_smul' c z := by ext k; simp [mul_assoc] }
  have hJ (d : ℕ) (z : EuclideanSpace ℂ (Fin d)) (b : Fin d) (c : Fin s) :
      J d z (finProdFinEquiv (b, c)) = z b * v c := by
    change z (finProdFinEquiv.symm (finProdFinEquiv (b, c))).1 *
      v (finProdFinEquiv.symm (finProdFinEquiv (b, c))).2 = _
    rw [Equiv.symm_apply_apply]
  have hw' (y : X) : w y = J r (u y) := by
    apply PiLp.ext
    intro k
    obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [hw, hJ]
  by_cases hv : v = 0
  · have hz : w = 0 := by
      apply SchwartzMap.ext
      intro y
      apply PiLp.ext
      intro k
      obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective k
      simp [hw, hv]
    simp [hz, hv, quantize, fourierSG]
  -- A nonzero fixed tensor factor gives an injective finite-dimensional map.
  -- This also preserves the totalized integral when the integrand is not integrable.
  have hj : ∃ c : Fin s, v c ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    exact PiLp.ext (fun c ↦ h c)
  obtain ⟨c, hc⟩ := hj
  have hinj (d : ℕ) : Function.Injective (J d) := by
    intro z z' h
    apply PiLp.ext
    intro b
    have he := congrArg (fun y : EuclideanSpace ℂ (Fin (d * s)) ↦
      y (finProdFinEquiv (b, c))) h
    rw [hJ, hJ] at he
    exact mul_right_cancel₀ hc he
  have hanti (d : ℕ) := (J d).toLinearMap.injective_iff_antilipschitz.mp (hinj d)
  obtain ⟨Kr, _, hKr⟩ := hanti r
  obtain ⟨Kq, _, hKq⟩ := hanti q
  have hf (ξ : X) : (FourierTransform.fourier w) ξ = J r ((FourierTransform.fourier u) ξ) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq']
    simp_rw [hw', ← map_smul]
    exact (J r).integral_comp_comm' hKr _
  have hmatrix (y ξ : X) (z : EuclideanSpace ℂ (Fin r)) :
      tensorIdentitySymbolMap r q s (a y ξ) (J r z) = J q (a y ξ z) := by
    apply PiLp.ext
    intro k
    obtain ⟨⟨b, c'⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [tensorIdentitySymbolMap_apply _ z v _ (hJ r z), hJ]
  have hquant : quantize (fun y ξ ↦ tensorIdentitySymbolMap r q s (a y ξ)) w x =
      J q (quantize a u x) := by
    simp only [quantize, fourierSG, hf, hmatrix, ← map_smul]
    rw [(J q).integral_comp_comm' hKq]
    exact ((J q).map_smul_of_tower ((2 * Real.pi) ^ n)⁻¹ _).symm
  rw [hquant, hJ]

/-- A fixed continuous linear operation on coefficient matrices preserves symbol order. -/
theorem isSymbol_continuousLinearMap {n r q r' q' : ℕ} (d : ℝ)
    (a : SymbolFunction n r q) (ha : IsSymbol Set.univ d a)
    (L : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ]
      (EuclideanSpace ℂ (Fin r') →L[ℂ] EuclideanSpace ℂ (Fin q'))) :
    IsSymbol Set.univ d (fun x ξ ↦ L (a x ξ)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let W := EuclideanSpace ℂ (Fin r') →L[ℂ] EuclideanSpace ℂ (Fin q')
  have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  have hparametric (j : ℕ) :
      ContDiff ℝ ∞ (fun z : X × X ↦ iteratedFDeriv ℝ j (a z.1) z.2) := by
    induction j with
    | zero =>
      exact hs.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ X V).symm : _ →L[ℝ] X [×0]→L[ℝ] V)
    | succ j ih =>
      have h : ContDiff ℝ ∞ (Function.uncurry
          (fun z : X × X ↦ fun ξ : X ↦ iteratedFDeriv ℝ j (a z.1) ξ)) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞
          (fun z : X × X ↦ fderiv ℝ (iteratedFDeriv ℝ j (a z.1)) z.2) :=
        h.fderiv contDiff_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) V).symm :
          _ →L[ℝ] X [×(j + 1)]→L[ℝ] V)
  refine ⟨(L.contDiff.comp hs).contDiffOn, ?_⟩
  intro K hK hc i j
  obtain ⟨C, hC, hbound⟩ := ha.2 K hK hc i j
  let J := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j ↦ X) V W L
  refine ⟨‖J‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro x hx ξ
  have heq : (fun y : X ↦ iteratedFDeriv ℝ j (fun η ↦ L (a y η)) ξ) =
      J ∘ (fun y : X ↦ iteratedFDeriv ℝ j (a y) ξ) := by
    funext y
    exact L.iteratedFDeriv_comp_left
      ((hs.comp (contDiff_const.prodMk contDiff_id)).contDiffAt) (by simp)
  change ‖iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ L (a y η)) ξ) x‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖J‖ * ‖symbolDerivative a i j x ξ‖ :=
      J.norm_iteratedFDeriv_comp_left
        (((hparametric j).comp (contDiff_id.prodMk contDiff_const)).contDiffAt) (by simp)
    _ ≤ ‖J‖ * (C * (1 + ‖ξ‖) ^ (d - (j : ℝ))) := by gcongr; exact hbound x hx ξ
    _ = _ := (mul_assoc _ _ _).symm

private theorem productCutoffSobolevOperator_eq_sub
    {n m r q : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) (ε : ℝ) (hε : 0 < ε)
    (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
    (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q)))
    (hv : ∀ x, quantize (liftedProductSymbol a χ) u x = v x) :
    productCutoffSobolevOperator a ha haK χ hχ hχK ε hε
        (schwartzSobolevCoordinate 1 u) =
      schwartzSobolevCoordinate 0 v -
        productCutoffErrorOperator a ha haK χ hχ hχK ε
          (schwartzSobolevCoordinate 1 u) := by
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let V := EuclideanSpace ℂ (Fin q)
  let hc := isSymbol_productCutoffSymbol a ha χ hχ ε hε
  let hcK := hasCompactSupport_productCutoffSymbol a haK χ hχK ε
  let w : 𝓢(Z, V) := quantizeSchwartz 1 (productCutoffSymbol a χ ε) hc hcK u
  have hw (x : Z) : w x = quantize (productCutoffSymbol a χ ε) u x :=
    quantizeSchwartz_apply 1 _ hc hcK u x
  -- The same Bessel realizations are fixed by their Fourier-integral specifications.
  have hcut := Classical.choose_spec
    (existsUnique_productCutoffSobolevOperator a ha haK χ hχ hχK ε hε).exists
  have herr := Classical.choose_spec
    (existsUnique_productCutoffErrorOperator a ha haK χ hχ hχK ε).exists
  apply besselRealization_injective (n + m) q 0
  ext1 φ
  rw [map_sub, sub_apply,
    besselRealization_schwartzSobolevCoordinate]
  change _ = (∫ x, φ x • v x) - _
  rw [show besselRealization (n + m) q 0
      (productCutoffSobolevOperator a ha haK χ hχ hχK ε hε
        (schwartzSobolevCoordinate 1 u)) φ =
        ∫ x, φ x • quantize (productCutoffSymbol a χ ε) u x from hcut u φ]
  rw [show besselRealization (n + m) q 0
      (productCutoffErrorOperator a ha haK χ hχ hχK ε
        (schwartzSobolevCoordinate 1 u)) φ =
        ∫ x, φ x • quantize (productCutoffErrorSymbol a χ ε) u x from herr u φ]
  -- Both comparison outputs are actual Schwartz functions. This supplies the
  -- integrability needed to split the original error integral, without imposing
  -- joint symbol estimates on the uncut lift.
  have hiv : Integrable (fun x : Z ↦ φ x • v x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM V φ v).integrable (μ := volume)
  have hiw : Integrable (fun x : Z ↦ φ x • w x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM V φ w).integrable (μ := volume)
  simp_rw [quantize_productCutoffErrorSymbol a ha χ hχ ε hε, hv, ← hw, smul_sub]
  rw [integral_sub hiv hiw]
  exact (sub_sub_cancel _ _).symm

private theorem exists_schwartz_liftedProductSymbol
    {n m r q : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (v : 𝓢(EuclideanSpace ℝ (Fin m), ℂ))
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
    (hw : ∀ x y, w (EuclideanSpace.finAddEquivProd.symm (x, y)) = v y • u x) :
    ∃ z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q)),
      (∀ x, quantize (liftedProductSymbol a χ) w x = z x) ∧
        ∀ x y, z (EuclideanSpace.finAddEquivProd.symm (x, y)) =
          ((χ y : ℂ) * v y) • quantize a u x := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let u₀ := quantizeSchwartz 1 a ha haK u
  let f := fun x : EuclideanSpace ℝ (Fin (n + m)) ↦
    ((χ (e x).2 : ℂ) * v (e x).2) • u₀ (e x).1
  have hf : ContDiff ℝ ∞ f := by
    exact ((Complex.ofRealCLM.contDiff.comp
      (hχ.comp (contDiff_snd.comp e.contDiff))).mul
        ((v.smooth ⊤).comp (contDiff_snd.comp e.contDiff))).smul
          ((u₀.smooth ⊤).comp (contDiff_fst.comp e.contDiff))
  have hu₀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport a) : u₀ x = 0 := by
    rw [quantizeSchwartz_apply]
    have ha0 := image_eq_zero_of_notMem_tsupport hx
    simp only [quantize, ha0, Pi.zero_apply, zero_apply, smul_zero, integral_zero]
  have hcompact : HasCompactSupport f := by
    have hK := (haK.prod hχK).image e.symm.continuous
    apply hK.of_isClosed_subset (isClosed_tsupport f)
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    refine ⟨e x, ⟨?_, ?_⟩, e.symm_apply_apply x⟩
    · by_contra h
      exact hx (by simp only [f, hu₀ _ h, smul_zero])
    · by_contra h
      have hχ0 := image_eq_zero_of_notMem_tsupport h
      exact hx (by simp only [f, hχ0, Complex.ofReal_zero, zero_mul, zero_smul])
  refine ⟨hcompact.toSchwartzMap hf, ?_, ?_⟩
  · intro x
    have hv := quantize_liftedProductSymbol a χ u v w hw (e x).1 (e x).2
    change quantize (liftedProductSymbol a χ) w (e.symm (e x)) = _ at hv
    rw [e.symm_apply_apply] at hv
    simpa only [f, HasCompactSupport.toSchwartzMap_toFun, u₀, quantizeSchwartz_apply] using hv
  · intro x y
    change f (e.symm (x, y)) = _
    simp only [f, e.apply_symm_apply, u₀, quantizeSchwartz_apply]

set_option maxHeartbeats 800000 in
-- Scalar tensor density is transported through the original finite fiber coordinates.
set_option backward.isDefEq.respectTransparency false in
private theorem eq_of_schwartz_products_bessel
    {n m r q : ℕ}
    (T S : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))))
    (h : ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (v : 𝓢(EuclideanSpace ℝ (Fin m), ℂ))
      (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r))),
      (∀ x y, w (EuclideanSpace.finAddEquivProd.symm (x, y)) = v y • u x) →
        T (schwartzSobolevCoordinate 1 w) = S (schwartzSobolevCoordinate 1 w)) : T = S := by
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let U := EuclideanSpace ℂ (Fin r)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let c : 𝓢(Z, U) →L[ℂ] Lp U 2 (volume : Measure Z) :=
    (SchwartzMap.toLpCLM ℂ U 2 volume).comp
      (SchwartzMap.fourierMultiplierCLM U (fun ξ : Z ↦ ((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ)))
  have hc (w : 𝓢(Z, U)) : c w = schwartzSobolevCoordinate 1 w := by
    change (SchwartzMap.fourierMultiplierCLM U
      (fun ξ : Z ↦ (((1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) w).toLp 2 = _
    unfold schwartzSobolevCoordinate
    congr 1
    exact SchwartzMap.fourierMultiplierCLM_ofReal ℂ
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow Z ((1 : ℝ) / 2)) w
  let lift (v : U) : 𝓢(Z, ℂ) →L[ℂ] 𝓢(Z, U) :=
    SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight v)
  have hlift (v : U) (f : 𝓢(Z, ℂ)) (x : Z) : lift v f x = f x • v := rfl
  have hscalar (v : U) (f : 𝓢(Z, ℂ)) : T (c (lift v f)) = S (c (lift v f)) := by
    have hd := dense_span_schwartz_products n m
    apply hd.induction (P := fun f : 𝓢(Z, ℂ) ↦ T (c (lift v f)) = S (c (lift v f)))
      (fun f hf ↦ ?_) (isClosed_eq
        (((T.comp c).comp (lift v)).continuous)
        (((S.comp c).comp (lift v)).continuous)) f
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, b, hab⟩ := hf
      let u := SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight v) a
      rw [hc]
      apply h u b (lift v f)
      intro x y
      change f (e.symm (x, y)) • v = b y • (a x • v)
      rw [hab, e.apply_symm_apply, smul_smul, mul_comm]
    | zero => simp only [map_zero]
    | add x y hx hy hxx hyy => simp only [map_add, hxx, hyy]
    | smul a x hx hxx => simp only [map_smul, hxx]
  have hall (w : 𝓢(Z, U)) : T (c w) = S (c w) := by
    let f (j : Fin r) := SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) j) w
    have hsum : w = ∑ j : Fin r, lift (EuclideanSpace.single j 1) (f j) := by
      apply SchwartzMap.ext
      intro z
      simp only [sum_apply, hlift]
      symm
      have hproj (j : Fin r) (v : U) : (EuclideanSpace.proj (𝕜 := ℂ) j) v = v j := rfl
      simpa only [f, SchwartzMap.postcompCLM_apply, hproj,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr (w z)
    rw [hsum, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hscalar _ _)
  exact DFunLike.ext' ((denseRange_schwartzSobolevCoordinate (n + m) r 1).equalizer
    T.continuous S.continuous
      (funext (fun w ↦ by simpa only [hc, Function.comp_apply] using hall w)))

/-- The cutoff operators converge to the bounded lift determined by the original separated
Fourier action. All operators act in the same first and zeroth Bessel coordinates. -/
theorem exists_liftedProductSobolev_approximation
    {n m r q : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ L : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin m), ℂ))
        (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r))),
        (∀ x y, w (EuclideanSpace.finAddEquivProd.symm (x, y)) = v y • u x) →
          ∃ z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q)),
            (∀ x y, z (EuclideanSpace.finAddEquivProd.symm (x, y)) =
              ((χ y : ℂ) * v y) • quantize a u x) ∧
            L (schwartzSobolevCoordinate 1 w) = schwartzSobolevCoordinate 0 z) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
        ‖productCutoffSobolevOperator a ha haK χ hχ hχK ε hε - L‖ ≤ C * ε := by
  let L := productCutoffSobolevOperator a ha haK χ hχ hχK 1 zero_lt_one +
    productCutoffErrorOperator a ha haK χ hχ hχK 1
  -- One fixed positive cutoff plus its actual error constructs the bounded uncut lift.
  have hL (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
      (z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin q)))
      (hz : ∀ x, quantize (liftedProductSymbol a χ) u x = z x) :
      L (schwartzSobolevCoordinate 1 u) = schwartzSobolevCoordinate 0 z := by
    dsimp only [L]
    rw [add_apply]
    rw [productCutoffSobolevOperator_eq_sub a ha haK χ hχ hχK 1 zero_lt_one u z hz]
    exact sub_add_cancel _ _
  refine ⟨L, ?_, ?_⟩
  · intro u v w hw
    obtain ⟨z, hz, hz'⟩ := exists_schwartz_liftedProductSymbol a ha haK χ hχ hχK u v w hw
    exact ⟨z, hz', hL w z hz⟩
  · obtain ⟨C, hC, hbound⟩ :=
      (productCutoffErrorOperator_approximation a ha haK χ hχ hχK).1
    refine ⟨C, hC, ?_⟩
    intro ε hε hε1
    -- Density upgrades the exact Fourier action on pure tensors to full operator equality.
    have heq : productCutoffSobolevOperator a ha haK χ hχ hχK ε hε +
        productCutoffErrorOperator a ha haK χ hχ hχK ε = L := by
      apply eq_of_schwartz_products_bessel
      intro u v w hw
      obtain ⟨z, hz, _⟩ := exists_schwartz_liftedProductSymbol a ha haK χ hχ hχK u v w hw
      rw [add_apply]
      rw [productCutoffSobolevOperator_eq_sub a ha haK χ hχ hχK ε hε w z hz,
        sub_add_cancel, hL w z hz]
    have hnorm : ‖productCutoffSobolevOperator a ha haK χ hχ hχK ε hε - L‖ =
        ‖productCutoffErrorOperator a ha haK χ hχ hχK ε‖ := by
      rw [← heq]
      simp only [sub_add_cancel_left, norm_neg]
    rw [hnorm]
    exact hbound ε hε hε1


/-- The bounded coordinate tensor action is the norm limit of the actual positive cutoffs. -/
theorem exists_tensorProductSobolev_approximation
    {n m r q s : ℕ} (a : SymbolFunction n r q)
    (α : SymbolFunction n (r * s) (q * s))
    (hα : IsSymbol Set.univ 1 α) (hαK : HasCompactSupport α)
    (hαeq : α = fun x ξ ↦ tensorIdentitySymbolMap r q s (a x ξ))
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ L : Lp (EuclideanSpace ℂ (Fin (r * s))) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin (q * s))) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
        (v : 𝓢(EuclideanSpace ℝ (Fin m), EuclideanSpace ℂ (Fin s)))
        (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s)))),
        (∀ x y i j, w (EuclideanSpace.finAddEquivProd.symm (x, y))
          (finProdFinEquiv (i, j)) = u x i * v y j) →
          ∃ z : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (q * s))),
            (∀ x y i j, z (EuclideanSpace.finAddEquivProd.symm (x, y))
              (finProdFinEquiv (i, j)) = (χ y : ℂ) * (quantize a u x i * v y j)) ∧
            L (schwartzSobolevCoordinate 1 w) = schwartzSobolevCoordinate 0 z) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
        ‖productCutoffSobolevOperator α hα hαK χ hχ hχK ε hε - L‖ ≤ C * ε := by
  classical
  obtain ⟨L, hL, hbound⟩ := exists_liftedProductSobolev_approximation α hα hαK χ hχ hχK
  refine ⟨L, ?_, hbound⟩
  intro u v w hw
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  -- Resolve the second finite fiber into its original coordinate columns.
  let J (d : ℕ) (j : Fin s) :
      EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin (d * s)) :=
    LinearMap.toContinuousLinearMap {
      toFun z := WithLp.toLp 2 (fun k ↦
        z (finProdFinEquiv.symm k).1 * (EuclideanSpace.single j 1) (finProdFinEquiv.symm k).2)
      map_add' z z' := by
        ext k
        change (z (finProdFinEquiv.symm k).1 + z' (finProdFinEquiv.symm k).1) * _ = _
        exact add_mul _ _ _
      map_smul' c z := by
        ext k
        change (c * z (finProdFinEquiv.symm k).1) * _ = _
        exact mul_assoc _ _ _ }
  let D (j : Fin s) : EuclideanSpace ℂ (Fin (r * s)) →L[ℂ] EuclideanSpace ℂ (Fin r) :=
    LinearMap.toContinuousLinearMap {
      toFun z := WithLp.toLp 2 (fun i ↦ z (finProdFinEquiv (i, j)))
      map_add' z z' := by ext i; rfl
      map_smul' c z := by ext i; rfl }
  have hJ (d : ℕ) (j : Fin s) (z : EuclideanSpace ℂ (Fin d)) (i : Fin d) (k : Fin s) :
      J d j z (finProdFinEquiv (i, k)) = z i * (EuclideanSpace.single j 1) k := by
    change z (finProdFinEquiv.symm (finProdFinEquiv (i, k))).1 *
      (EuclideanSpace.single j 1) (finProdFinEquiv.symm (finProdFinEquiv (i, k))).2 = _
    rw [Equiv.symm_apply_apply]
  have hD (j : Fin s) (z : EuclideanSpace ℂ (Fin (r * s))) (i : Fin r) :
      D j z i = z (finProdFinEquiv (i, j)) := rfl
  let u' (j : Fin s) := SchwartzMap.postcompCLM (J r j) u
  let v' (j : Fin s) := SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) j) v
  let w' (j : Fin s) := SchwartzMap.postcompCLM ((J r j).comp (D j)) w
  have hw' (j : Fin s) (x : X) (y : Y) : w' j (e.symm (x, y)) = v' j y • u' j x := by
    apply PiLp.ext
    intro k
    obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective k
    change J r j (D j (w (e.symm (x, y)))) (finProdFinEquiv (b, c)) =
      (v y j) * J r j (u x) (finProdFinEquiv (b, c))
    rw [hJ, hJ, hD, hw]
    ring
  have hsum : w = ∑ j : Fin s, w' j := by
    apply SchwartzMap.ext
    intro z
    apply PiLp.ext
    intro k
    obtain ⟨⟨b, c⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, w',
      SchwartzMap.postcompCLM_apply, ContinuousLinearMap.comp_apply]
    change w z (finProdFinEquiv (b, c)) =
      ∑ j : Fin s, J r j (D j (w z)) (finProdFinEquiv (b, c))
    simp [hJ, hD]
  have hparts (j : Fin s) := hL (u' j) (v' j) (w' j) (hw' j)
  choose z hz hcoord using hparts
  have hz' (j : Fin s) (x : X) (y : Y) (i : Fin q) (k : Fin s) :
      z j (e.symm (x, y)) (finProdFinEquiv (i, k)) =
        ((χ y : ℂ) * (quantize a u x i * v y j)) * (EuclideanSpace.single j 1) k := by
    rw [hz]
    change (((χ y : ℂ) * v y j) • quantize α (u' j) x) (finProdFinEquiv (i, k)) = _
    change ((χ y : ℂ) * v y j) * quantize α (u' j) x (finProdFinEquiv (i, k)) = _
    rw [hαeq, quantize_tensorIdentitySymbolMap a u (EuclideanSpace.single j 1) (u' j)
      (fun x i k ↦ hJ r j (u x) i k)]
    ring
  refine ⟨∑ j, z j, ?_, ?_⟩
  · intro x y i j
    simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
    change (∑ k : Fin s, z k (e.symm (x, y)) (finProdFinEquiv (i, j))) = _
    simp [hz']
  · -- Sum the exact Bessel identities; no choice of new tensor coordinates is involved.
    rw [hsum]
    change L ((schwartzSobolevCoordinateLinearMap (n + m) (r * s) 1) (∑ j, w' j)) =
      (schwartzSobolevCoordinateLinearMap (n + m) (q * s) 0) (∑ j, z j)
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hcoord j)

section TensorPiece

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₀)) E₀]
  [IsSmoothComplexBundle (n := n) (r := r₀) E₀]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r₁)) E₁]
  [IsSmoothComplexBundle (n := n) (r := r₁) E₁]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := m) (r := s) F]

set_option maxHeartbeats 1000000 in
-- The two native tensor bundle instances and their chosen product frames must be unfolded together.
set_option backward.isDefEq.respectTransparency false in
/-- A compact first-factor piece gives an actual cutoff PDO piece in the selected
external tensor charts, with the same second-factor frame on both sides. -/
def PseudodifferentialPiece.productCutoff
    (L : PseudodifferentialPiece (n := n) (r := r₀) (q := r₁) E₀ E₁ 1)
    (hLK : HasCompactSupport L.symbol)
    (d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin m)) N)
    (B C : BundleChartCutoff (r := s) F d) (hCB : C.frame = B.frame)
    (ε : ℝ) (hε : 0 < ε) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
    letI := externalTensorTopology (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    letI := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
    letI := externalTensorTopology (r := r₁) (s := s) E₁ F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    PseudodifferentialPiece (n := n + m) (r := r₀ * s) (q := r₁ * s)
      (externalTensorFiber E₀ F) (externalTensorFiber E₁ F) 1 := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedSpace (r := r₀) (s := s) E₀ F
  let := externalTensorTopology (r := r₀) (s := s) E₀ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
  let := externalTensorFiberNormedAddCommGroup (r := r₁) (s := s) E₁ F
  let := externalTensorFiberNormedSpace (r := r₁) (s := s) E₁ F
  let := externalTensorTopology (r := r₁) (s := s) E₁ F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let A := externalTensorChartCutoff L.input B
  let D := externalTensorChartCutoff L.output C
  let Φ := tensorIdentitySymbolMap r₀ r₁ s
  let a : SymbolFunction n (r₀ * s) (r₁ * s) := fun x ξ ↦ Φ (L.symbol x ξ)
  have ha : IsSymbol Set.univ 1 a := by
    exact isSymbol_continuousLinearMap 1 L.symbol L.isSymbol (Φ.restrictScalars ℝ)
  have haK : HasCompactSupport a := by
    apply hLK.of_isClosed_subset (isClosed_tsupport a)
    apply closure_minimal ?_ (isClosed_tsupport L.symbol)
    intro x hx
    by_contra h
    have hzero := image_eq_zero_of_notMem_tsupport h
    apply hx
    funext ξ
    change Φ (L.symbol x ξ) = 0
    rw [hzero]
    exact Φ.map_zero
  let p := productCutoffSymbol a C.cutoff ε
  have hp : IsSymbol Set.univ 1 p :=
    isSymbol_productCutoffSymbol a ha C.cutoff C.smooth_cutoff ε hε
  have hpK : HasCompactSupport p :=
    hasCompactSupport_productCutoffSymbol a haK C.cutoff C.compact_support ε
  have hB : A.frame.baseSet = L.input.frame.baseSet ×ˢ B.frame.baseSet := by
    let h := exists_externalTensorBundle (n := n) (m := m) (r := r₀) (s := s) E₀ F
    exact (h.choose_spec.choose_spec.2.1 L.input.frame L.input.frame_mem_atlas
        B.frame B.frame_mem_atlas).choose_spec.2.1
  have hC : D.frame.baseSet = L.output.frame.baseSet ×ˢ C.frame.baseSet := by
    let h := exists_externalTensorBundle (n := n) (m := m) (r := r₁) (s := s) E₁ F
    exact (h.choose_spec.choose_spec.2.1 L.output.frame L.output.frame_mem_atlas
        C.frame C.frame_mem_atlas).choose_spec.2.1
  have hsupp (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin m) → ℝ) :
      tsupport (fun z ↦ f (e z).1 * g (e z).2) ⊆
        e ⁻¹' (tsupport f ×ˢ tsupport g) := by
    apply closure_minimal ?_
      (((isClosed_tsupport f).prod (isClosed_tsupport g)).preimage e.continuous)
    intro z hz
    constructor
    · apply subset_tsupport
      intro h
      exact hz (by simp only [h, zero_mul])
    · apply subset_tsupport
      intro h
      exact hz (by simp only [h, mul_zero])
  refine {
    chart := (L.chart.prod d).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
    chart_mem_atlas := ?_
    input := A
    output := D
    input_support_in_output_frame := ?_
    output_support_in_input_frame := ?_
    operator := quantizeSchwartz 1 p hp hpK
    symbol := p
    isSymbol := hp
    operator_apply := quantizeSchwartz_apply 1 p hp hpK }
  · refine ⟨L.chart.prod d, ?_, e.symm.toHomeomorph.toOpenPartialHomeomorph,
      Set.mem_singleton _, rfl⟩
    exact ⟨L.chart, L.chart_mem_atlas, d, hd, rfl⟩
  · intro z hz
    have hz' := hsupp L.input.cutoff B.cutoff hz
    change (L.chart.symm (e z).1, d.symm (e z).2) ∈ D.frame.baseSet
    rw [hC, hCB]
    exact ⟨L.input_support_in_output_frame hz'.1, (B.support_subset hz'.2).2⟩
  · intro z hz
    have hz' := hsupp L.output.cutoff C.cutoff hz
    change (L.chart.symm (e z).1, d.symm (e z).2) ∈ A.frame.baseSet
    rw [hB, ← hCB]
    exact ⟨L.output_support_in_input_frame hz'.1, (C.support_subset hz'.2).2⟩

end TensorPiece

end AtiyahSinger
