/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TubularNeighborhood

/-!
# Normal derivatives of reference-tube overlaps

Public module ID: M1314.

A smooth identification of a vector bundle with the actual quotient normal
transports a normalized tubular neighborhood to that bundle. If another local
map has the same quotient derivative, the local overlap has identity vertical
derivative in the original selected bundle chart. The argument differentiates
the exact overlap equation and retains the supplied fiber identification.

This is the normal-derivative step in the local tubular composition argument.
Only smoothness near the specified zero vector is needed for the other map;
no global smoothness or fiber-preserving property of the overlap is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
  {R : M → Type*}
  [∀ x, AddCommGroup (R x)] [∀ x, Module ℝ (R x)] [∀ x, TopologicalSpace (R x)]
  [TopologicalSpace (TotalSpace W R)] [FiberBundle W R] [VectorBundle ℝ W R]

local notation "V" => NormalModel E F
local notation "ν" => NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option maxHeartbeats 1600000 in
-- The fixed native bundle and ambient charts remain visible throughout the chain rule.
/-- An exact overlap with the same quotient derivative has identity vertical derivative. -/
theorem fderiv_snd_eq_id_of_normalized_bundleReference
    (T : TubularNeighborhood f hf) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∀ (L : ∀ x : M, R x ≃L[ℝ] ν x)
      (Q : Diffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, W)) (𝓘(ℝ, E).prod 𝓘(ℝ, V))
        (TotalSpace W R) (TotalSpace V ν) ∞),
      (∀ z : TotalSpace W R, Q z = ⟨z.proj, L z.proj z.snd⟩) →
      ∀ (x : M) (Ψ : E × W → N) (Γ : E × W → TotalSpace W R),
        let a := chartAt E x x
        let c := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) (⟨x, 0⟩ : TotalSpace W R)
        let e := (trivializationAt W R x).continuousLinearEquivAt ℝ x
          (mem_baseSet_trivializationAt W R x)
        ContMDiffAt 𝓘(ℝ, E × W) 𝓘(ℝ, F) ∞ Ψ (a, 0) →
        ContMDiffAt 𝓘(ℝ, E × W) (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞ Γ (a, 0) →
        Γ (a, 0) = ⟨x, 0⟩ →
        (fun p ↦ T.totalMap f hf (Q (Γ p))) =ᶠ[𝓝 (a, 0)] Ψ →
        (∀ w : W,
          (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
            (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, F) (fun u ↦ Ψ (a, u)) 0
              ((NormedSpace.fromTangentSpace (0 : W)).symm w)) = L x (e.symm w)) →
        (fderiv ℝ (fun p ↦ (c (Γ p)).2) (a, 0)).comp
          (ContinuousLinearMap.inr ℝ E W) = ContinuousLinearMap.id ℝ W := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  intro L Q hQ x Ψ Γ a c₀ e₀ hΨ hΓ hΓ₀ hcomp hnormal
  let z₀ : TotalSpace W R := ⟨x, 0⟩
  let κ := chartAt E x
  let t := trivializationAt W R x
  have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt W R x
  let e := t.continuousLinearEquivAt ℝ x hx
  let c : OpenPartialHomeomorph (TotalSpace W R) (E × W) :=
    { toPartialEquiv := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) z₀
      open_source := isOpen_extChartAt_source z₀
      open_target := isOpen_extChartAt_target z₀
      continuousOn_toFun := continuousOn_extChartAt z₀
      continuousOn_invFun := continuousOn_extChartAt_symm z₀ }
  have hc₀ : z₀ ∈ c.source := mem_extChartAt_source z₀
  have hcpoint : c z₀ = (a, 0) := by
    change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) z₀) z₀ = _
    rw [FiberBundle.extChartAt]
    change (κ (t ⟨x, 0⟩).1, (t ⟨x, 0⟩).2) = (a, 0)
    rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx, map_zero]
  have hcvertical (w : W) : c.symm (a, w) = (⟨x, e.symm w⟩ : TotalSpace W R) := by
    change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) z₀).symm (a, w) = _
    rw [FiberBundle.extChartAt]
    change t.toOpenPartialHomeomorph.symm (κ.symm (κ x), w) = _
    rw [κ.left_inv (mem_chart_source E x)]
    exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm x hx w
  have hchorizontal : (fun u : E ↦ c.symm (u, 0)) =ᶠ[𝓝 a]
      (fun u : E ↦ (⟨κ.symm u, 0⟩ : TotalSpace W R)) := by
    have hκ : ContinuousAt κ.symm a := κ.continuousAt_symm
      (κ.map_source (mem_chart_source E x))
    have hκx : κ.symm a = x := κ.left_inv (mem_chart_source E x)
    filter_upwards [hκ (hκx ▸ t.open_baseSet.mem_nhds hx)] with u hu
    change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) z₀).symm (u, 0) = _
    rw [FiberBundle.extChartAt]
    change t.toOpenPartialHomeomorph.symm (κ.symm u, 0) = _
    rw [t.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ hu, map_zero]
  let τ : TotalSpace W R → N := T.totalMap f hf ∘ Q
  have hτs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, F) ∞ τ :=
    (contMDiff_subtype_val.comp T.diffeomorph.contMDiff).comp Q.contMDiff
  have hτzero (y : M) : τ ⟨y, 0⟩ = f y := by
    change T.totalMap f hf (Q ⟨y, 0⟩) = f y
    rw [hQ, map_zero]
    exact T.map_zero y
  let ψ := chartAt F (f x)
  let τc : E × W → F := ψ ∘ τ ∘ c.symm
  have hτc : ContDiffAt ℝ ∞ τc (a, 0) := by
    have h := (contMDiffAt_iff.mp (hτs z₀)).2
    change ContDiffWithinAt ℝ ∞
      (extChartAt 𝓘(ℝ, F) (τ z₀) ∘ τ ∘ c.symm)
      (Set.range (𝓘(ℝ, E).prod 𝓘(ℝ, W))) (c z₀) at h
    rw [hcpoint, hτzero x] at h
    simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using! h
  let A : (E × W) →L[ℝ] F := fderiv ℝ τc (a, 0)
  have hA : HasFDerivAt τc A (a, 0) := (hτc.differentiableAt (by simp)).hasFDerivAt
  let B : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
  have hB : HasFDerivAt (ψ ∘ f ∘ κ.symm) B a := by
    simpa only [writtenInExtChartAt, mfld_simps, hasFDerivWithinAt_univ] using!
      (f.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.2
  let q : F →ₗ[ℝ] ν x :=
    (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
  have hqB (v : E) : q (B v) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
  -- The reference map kills horizontal directions in the quotient because it agrees with f.
  have hhorizontal (v : E) : A (v, 0) = B v := by
    have heq : (fun u : E ↦ τc (u, 0)) =ᶠ[𝓝 a] (ψ ∘ f ∘ κ.symm) := by
      filter_upwards [hchorizontal] with u hu
      change ψ (τ (c.symm (u, 0))) = _
      rw [hu, hτzero]
      rfl
    have hd : HasFDerivAt (fun u : E ↦ τc (u, 0))
        (A.comp (ContinuousLinearMap.inl ℝ E W)) a := by
      simpa only [Function.comp_def] using!
        HasFDerivAt.comp a hA (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : W))
    exact congrArg (fun K : E →L[ℝ] F ↦ K v) ((hd.congr_of_eventuallyEq heq.symm).unique hB)
  -- In the vertical direction, change only the fixed normal frame of the original tube.
  let tN := trivializationAt V ν x
  have hxN : x ∈ tN.baseSet := mem_baseSet_trivializationAt V ν x
  let eN := tN.continuousLinearEquivAt ℝ x hxN
  let b : V → N := fun w ↦ T.totalMap f hf ⟨x, eN.symm w⟩
  have hb : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ b := by
    apply (contMDiff_subtype_val.comp T.diffeomorph.contMDiff).comp
    intro w
    rw [tN.contMDiffAt_iff (tN.mem_source.mpr hxN)]
    refine ⟨contMDiffAt_const, ?_⟩
    apply contMDiffAt_id.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro v
    change (tN ⟨x, eN.symm v⟩).2 = v
    rw [tN.apply_eq_prod_continuousLinearEquivAt ℝ x hxN]
    exact eN.apply_symm_apply v
  let D : V →L[ℝ] F := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, F) b 0
  have hD : HasFDerivAt (ψ ∘ b) D 0 := by
    have hbD := (hb.mdifferentiable (by simp) 0).hasMFDerivAt
    have hTzero : T.totalMap f hf ⟨x, 0⟩ = f x := T.map_zero x
    simpa only [writtenInExtChartAt, mfld_simps, b, Function.comp_def, map_zero,
      hTzero, hasFDerivWithinAt_univ] using! hbD.2
  let K : W →L[ℝ] V :=
    eN.toContinuousLinearMap.comp ((L x).toContinuousLinearMap.comp e.symm.toContinuousLinearMap)
  have hvertical (w : W) : A (0, w) = D (K w) := by
    have heq : (fun u : W ↦ τc (a, u)) = (ψ ∘ b) ∘ K := by
      funext u
      change ψ (T.totalMap f hf (Q (c.symm (a, u)))) = _
      rw [hcvertical, hQ]
      change ψ (T.totalMap f hf ⟨x, L x (e.symm u)⟩) =
        ψ (T.totalMap f hf ⟨x, eN.symm (eN (L x (e.symm u)))⟩)
      rw [eN.symm_apply_apply]
    have hd : HasFDerivAt (fun u : W ↦ τc (a, u))
        (A.comp (ContinuousLinearMap.inr ℝ E W)) 0 := by
      simpa only [Function.comp_def] using!
        HasFDerivAt.comp 0 hA (hasFDerivAt_prodMk_right (𝕜 := ℝ) a (0 : W))
    have hdK : HasFDerivAt ((ψ ∘ b) ∘ K) (D.comp K) 0 := by
      apply HasFDerivAt.comp 0
      · simpa only [map_zero] using hD
      · exact K.hasFDerivAt
    rw [heq] at hd
    exact congrArg (fun J : W →L[ℝ] F ↦ J w) (hd.unique hdK)
  have hquotient (v : E × W) : q (A v) = L x (e.symm v.2) := by
    have hsplit : A v = A (v.1, 0) + A (0, v.2) := by
      rw [← map_add]
      congr 1
      ext <;> simp
    have hqD : q (D (K v.2)) = eN.symm (K v.2) := T.normal_deriv x (K v.2)
    rw [hsplit, map_add, hhorizontal, hqB, zero_add, hvertical, hqD]
    exact eN.symm_apply_apply _
  -- Differentiate the actual overlap equation in one fixed ambient chart.
  have hΨ₀ : Ψ (a, 0) = f x := by
    rw [← hcomp.eq_of_nhds, hΓ₀]
    exact hτzero x
  let C : E × W → E × W := c ∘ Γ
  have hC₀ : C (a, 0) = (a, 0) := by
    change c (Γ (a, 0)) = _
    rw [hΓ₀, hcpoint]
  have hC : ContDiffAt ℝ ∞ C (a, 0) := by
    have h := (contMDiffAt_iff.mp hΓ).2
    rw [hΓ₀] at h
    simpa only [C, c, z₀, mfld_simps, contDiffWithinAt_univ] using! h
  have hΨc : ContDiffAt ℝ ∞ (ψ ∘ Ψ) (a, 0) := by
    have h := (contMDiffAt_iff.mp hΨ).2
    rw [hΨ₀] at h
    simpa only [ψ, mfld_simps, contDiffWithinAt_univ] using! h
  let DC : (E × W) →L[ℝ] (E × W) := fderiv ℝ C (a, 0)
  let DΨ : (E × W) →L[ℝ] F := fderiv ℝ (ψ ∘ Ψ) (a, 0)
  have hDC : HasFDerivAt C DC (a, 0) := (hC.differentiableAt (by simp)).hasFDerivAt
  have hDΨ : HasFDerivAt (ψ ∘ Ψ) DΨ (a, 0) :=
    (hΨc.differentiableAt (by simp)).hasFDerivAt
  have hτcomp : (τc ∘ C) =ᶠ[𝓝 (a, 0)] ψ ∘ Ψ := by
    have hnear : ∀ᶠ p in 𝓝 (a, 0), Γ p ∈ c.source :=
      hΓ.continuousAt (by rw [hΓ₀]; exact c.open_source.mem_nhds hc₀)
    filter_upwards [hnear, hcomp] with p hp hpc
    change ψ (τ (c.symm (c (Γ p)))) = ψ (Ψ p)
    rw [c.left_inv hp]
    exact congrArg ψ hpc
  have hchain : A.comp DC = DΨ := by
    have hAat : HasFDerivAt τc A (C (a, 0)) := by rw [hC₀]; exact hA
    exact ((hAat.comp (a, 0) hDC).congr_of_eventuallyEq hτcomp.symm).unique hDΨ
  let Ψv : W → N := fun w ↦ Ψ (a, w)
  let Dv : W →L[ℝ] F := mfderiv 𝓘(ℝ, W) 𝓘(ℝ, F) Ψv 0
  have hΨv : ContMDiffAt 𝓘(ℝ, W) 𝓘(ℝ, F) ∞ Ψv 0 :=
    hΨ.comp 0 ((contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt)
  have hDv : HasFDerivAt (ψ ∘ Ψv) Dv 0 := by
    have h := (hΨv.mdifferentiableAt (by simp)).hasMFDerivAt.2
    change Ψv 0 = f x at hΨ₀
    simpa only [writtenInExtChartAt, hΨ₀, mfld_simps, hasFDerivWithinAt_univ] using! h
  have hDΨv (w : W) : DΨ (0, w) = Dv w := by
    have hd : HasFDerivAt (ψ ∘ Ψv) (DΨ.comp (ContinuousLinearMap.inr ℝ E W)) 0 := by
      simpa only [Ψv, Function.comp_def] using!
        HasFDerivAt.comp 0 hDΨ (hasFDerivAt_prodMk_right (𝕜 := ℝ) a (0 : W))
    exact congrArg (fun J : W →L[ℝ] F ↦ J w) (hd.unique hDv)
  have hDCnormal (w : W) : (DC (0, w)).2 = w := by
    apply e.symm.injective
    apply (L x).injective
    calc
      L x (e.symm (DC (0, w)).2) = q (A (DC (0, w))) := (hquotient _).symm
      _ = q (DΨ (0, w)) := congrArg q (congrArg (fun J : (E × W) →L[ℝ] F ↦
        J (0, w)) hchain)
      _ = q (Dv w) := congrArg q (hDΨv w)
      _ = L x (e.symm w) := hnormal w
  have hDsnd : fderiv ℝ (fun p ↦ (C p).2) (a, 0) =
      (ContinuousLinearMap.snd ℝ E W).comp DC :=
    ((hasFDerivAt_snd (p := C (a, 0))).comp (a, 0) hDC).fderiv
  change (fderiv ℝ (fun p ↦ (C p).2) (a, 0)).comp _ = _
  rw [hDsnd]
  apply ContinuousLinearMap.ext
  intro w
  exact hDCnormal w

end AtiyahSinger
