/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TubularNeighborhood

/-!
# Normalized transitions between tubular neighborhoods

Public module ID: M1315.

Two normalized tubular neighborhoods of the same actual quotient normal bundle determine
a partial diffeomorphism on the inverse images of their overlapping ambient neighborhoods.
It fixes the zero section and has identity normal derivative in both directions, expressed
in the exact native bundle chart required by bundle rescaling.

The transition is the original inverse of the first tube composed with the second tube.
Outside its source we use the input point itself, so the total function is defined even when
the base is empty. Smoothness is needed only on the specified open source.

To compare derivatives, we first use each tube's original quotient normalization and its
zero-section equation: applying the quotient to its entire differential gives the same
projection to the normal coordinate. Differentiating the exact transition equation then
forces the vertical coordinate block of the transition to be identity. Reversing the two
tubes supplies the same conclusion for the actual inverse; no fiber-preserving assumption
or independent choice of normal identification is made.

This is the standard local transition step in uniqueness of tubular neighborhoods up to
open isotopy. Parameter rescaling and extension to the whole normal bundle are separate steps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
  (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
  (hf : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)

/-- The overlap transition of two normalized tubes has the same identity normal derivative
in both directions, on the original quotient normal bundle and its selected chart. -/
theorem exists_normalized_tubeTransition (T₀ T₁ : TubularNeighborhood f hf) :
    letI := normalBundleFiberBundle f hf
    letI := normalBundleVectorBundle f hf
    letI := normalBundleContMDiffVectorBundle f hf
    ∃ e : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
        (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))
        (TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)) ∞,
      e.source = (TubularNeighborhood.totalMap f hf T₁) ⁻¹' T₀.target ∧
      e.target = (TubularNeighborhood.totalMap f hf T₀) ⁻¹' T₁.target ∧
      (∀ x, (⟨x, 0⟩ : TotalSpace _ _) ∈ e.source) ∧
      (∀ x, e ⟨x, 0⟩ = ⟨x, 0⟩) ∧
      (∀ (z : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f)),
        z ∈ e.source → (TubularNeighborhood.totalMap f hf T₀) (e z) =
          (TubularNeighborhood.totalMap f hf T₁) z) ∧
      (∀ x : M,
        let c := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
          (⟨x, 0⟩ : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))
        (fderiv ℝ (fun z : E × NormalModel E F ↦ (c (e (c.symm z))).2) (c ⟨x, 0⟩)).comp
          (ContinuousLinearMap.inr ℝ E (NormalModel E F)) =
            ContinuousLinearMap.id ℝ (NormalModel E F)) ∧
      ∀ x : M,
        let c := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, NormalModel E F))
          (⟨x, 0⟩ : TotalSpace (NormalModel E F) (NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f))
        (fderiv ℝ (fun z : E × NormalModel E F ↦ (c (e.symm (c.symm z))).2) (c ⟨x, 0⟩)).comp
          (ContinuousLinearMap.inr ℝ E (NormalModel E F)) =
            ContinuousLinearMap.id ℝ (NormalModel E F) := by
  classical
  let := normalBundleFiberBundle f hf
  let := normalBundleVectorBundle f hf
  let := normalBundleContMDiffVectorBundle f hf
  let G := NormalModel E F
  let V := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let NB := TotalSpace G V
  have hTsmooth (T : TubularNeighborhood f hf) :
      ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) ∞ (TubularNeighborhood.totalMap f hf T) :=
    contMDiff_subtype_val.comp T.diffeomorph.contMDiff
  have hTinj (T : TubularNeighborhood f hf) :
      Function.Injective (TubularNeighborhood.totalMap f hf T) :=
    Subtype.val_injective.comp T.diffeomorph.injective
  have hTzero (T : TubularNeighborhood f hf) (x : M) :
      (TubularNeighborhood.totalMap f hf T) ⟨x, 0⟩ = f x :=
    T.map_zero x
  -- The two actual tube maps give one partial diffeomorphism on their precise overlap.
  let U (A B : TubularNeighborhood f hf) : TopologicalSpace.Opens NB :=
    ⟨(TubularNeighborhood.totalMap f hf B) ⁻¹' A.target,
      A.target.2.preimage (TubularNeighborhood.totalMap f hf B).continuous⟩
  let φ (A B : TubularNeighborhood f hf) (z : NB) : NB :=
    if h : (TubularNeighborhood.totalMap f hf B) z ∈ A.target then
      A.diffeomorph.symm ⟨(TubularNeighborhood.totalMap f hf B) z, h⟩ else z
  have hmap (A B : TubularNeighborhood f hf) (z : NB) (hz : z ∈ U A B) :
      (TubularNeighborhood.totalMap f hf A) (φ A B z) =
        (TubularNeighborhood.totalMap f hf B) z := by
    dsimp only [φ]
    rw [dite_eq_left (show (TubularNeighborhood.totalMap f hf B) z ∈ A.target from hz)]
    exact congrArg Subtype.val
      (A.diffeomorph.apply_symm_apply ⟨(TubularNeighborhood.totalMap f hf B) z, hz⟩)
  have hsource (A B : TubularNeighborhood f hf) (x : M) : (⟨x, 0⟩ : NB) ∈ U A B := by
    change (TubularNeighborhood.totalMap f hf B) ⟨x, 0⟩ ∈ A.target
    rw [hTzero, ← hTzero A x]
    exact (A.diffeomorph ⟨x, 0⟩).property
  have hzero (A B : TubularNeighborhood f hf) (x : M) : φ A B ⟨x, 0⟩ = ⟨x, 0⟩ := by
    apply hTinj A
    rw [hmap A B _ (hsource A B x), hTzero, hTzero]
  have hmaps (A B : TubularNeighborhood f hf) (z : NB) (hz : z ∈ U A B) :
      φ A B z ∈ U B A := by
    change (TubularNeighborhood.totalMap f hf A) (φ A B z) ∈ B.target
    rw [hmap A B z hz]
    exact (B.diffeomorph z).property
  have hinverse (A B : TubularNeighborhood f hf) (z : NB) (hz : z ∈ U A B) :
      φ B A (φ A B z) = z := by
    apply hTinj B
    rw [hmap B A _ (hmaps A B z hz), hmap A B z hz]
  -- Restrict to the open source before composing the original smooth inverse.
  have hsmooth (A B : TubularNeighborhood f hf) :
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞
        (φ A B) (U A B) := by
    let k : U A B → A.target := fun z ↦ ⟨(TubularNeighborhood.totalMap f hf B) z.val, z.property⟩
    have hk : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G)) 𝓘(ℝ, F) ∞ k := by
      apply (ContMDiff.subtypeVal_comp_iff A.target k).mp
      exact (hTsmooth B).comp contMDiff_subtype_val
    have hφU : (fun z : U A B ↦ φ A B z.val) = A.diffeomorph.symm ∘ k := by
      funext z
      dsimp only [φ]
      rw [dite_eq_left (show (TubularNeighborhood.totalMap f hf B) z.val ∈ A.target from
        z.property)]
      rfl
    have hφsmooth : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, G))
        (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞ (fun z : U A B ↦ φ A B z.val) := by
      rw [hφU]
      exact A.diffeomorph.symm.contMDiff.comp hk
    intro z hz
    exact (contMDiffAt_subtype_iff.mp (hφsmooth ⟨z, hz⟩)).contMDiffWithinAt
  have hnormal (P Q : TubularNeighborhood f hf) (x : M) :
      let c := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (⟨x, 0⟩ : NB)
      (fderiv ℝ (fun z : E × G ↦ (c (φ P Q (c.symm z))).2) (c ⟨x, 0⟩)).comp
        (ContinuousLinearMap.inr ℝ E G) = ContinuousLinearMap.id ℝ G := by
    let z₀ : NB := ⟨x, 0⟩
    let κ := chartAt E x
    let a : E := κ x
    let t := trivializationAt G V x
    have hx : x ∈ t.baseSet := mem_baseSet_trivializationAt G V x
    let e := t.continuousLinearEquivAt ℝ x hx
    let c : OpenPartialHomeomorph NB (E × G) :=
      { toPartialEquiv := extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) z₀
        open_source := isOpen_extChartAt_source z₀
        open_target := isOpen_extChartAt_target z₀
        continuousOn_toFun := continuousOn_extChartAt z₀
        continuousOn_invFun := continuousOn_extChartAt_symm z₀ }
    have hc₀ : z₀ ∈ c.source := mem_extChartAt_source z₀
    have hcpoint : c z₀ = (a, 0) := by
      change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) z₀) z₀ = _
      rw [FiberBundle.extChartAt]
      change (κ (t ⟨x, 0⟩).1, (t ⟨x, 0⟩).2) = (a, 0)
      rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx, map_zero]
    have hcinv : c.symm (a, 0) = z₀ := by
      rw [← hcpoint]
      exact c.left_inv hc₀
    have hcvertical (w : G) : c.symm (a, w) = (⟨x, e.symm w⟩ : NB) := by
      change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) z₀).symm (a, w) = _
      rw [FiberBundle.extChartAt]
      change t.toOpenPartialHomeomorph.symm (κ.symm (κ x), w) = _
      rw [κ.left_inv (mem_chart_source E x)]
      exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm x hx w
    have hchorizontal : (fun u : E ↦ c.symm (u, 0)) =ᶠ[𝓝 a]
        (fun u : E ↦ (⟨κ.symm u, 0⟩ : NB)) := by
      have hκ : ContinuousAt κ.symm a := κ.continuousAt_symm
        (κ.map_source (mem_chart_source E x))
      have hκx : κ.symm a = x := κ.left_inv (mem_chart_source E x)
      filter_upwards [hκ (hκx ▸ t.open_baseSet.mem_nhds hx)] with u hu
      change (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) z₀).symm (u, 0) = _
      rw [FiberBundle.extChartAt]
      change t.toOpenPartialHomeomorph.symm (κ.symm u, 0) = _
      rw [t.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ hu, map_zero]
    let incl : G → NB := fun w ↦ ⟨x, e.symm w⟩
    have hi : ContMDiff 𝓘(ℝ, G) (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞ incl := by
      intro w
      rw [t.contMDiffAt_iff (t.mem_source.mpr hx)]
      refine ⟨contMDiffAt_const, ?_⟩
      apply contMDiffAt_id.congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro v
      change (t ⟨x, e.symm v⟩).2 = v
      rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x hx]
      exact e.apply_symm_apply v
    let ψ := chartAt F (f x)
    let τ (T : TubularNeighborhood f hf) : E × G → F :=
      ψ ∘ (TubularNeighborhood.totalMap f hf T) ∘ c.symm
    have hτ (T : TubularNeighborhood f hf) : ContDiffAt ℝ ∞ (τ T) (a, 0) := by
      have h := (contMDiffAt_iff.mp ((hTsmooth T) z₀)).2
      change ContDiffWithinAt ℝ ∞
        (extChartAt 𝓘(ℝ, F) ((TubularNeighborhood.totalMap f hf T) z₀) ∘
          (TubularNeighborhood.totalMap f hf T) ∘ c.symm)
        (Set.range (𝓘(ℝ, E).prod 𝓘(ℝ, G))) (c z₀) at h
      rw [hcpoint, hTzero T x] at h
      simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using! h
    let A (T : TubularNeighborhood f hf) : (E × G) →L[ℝ] F := fderiv ℝ (τ T) (a, 0)
    have hA (T : TubularNeighborhood f hf) : HasFDerivAt (τ T) (A T) (a, 0) :=
      ((hτ T).differentiableAt (by simp)).hasFDerivAt
    let B : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x
    have hB : HasFDerivAt (ψ ∘ f ∘ κ.symm) B a := by
      simpa only [writtenInExtChartAt, mfld_simps, hasFDerivWithinAt_univ] using!
        (f.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt.2
    let qN : F →ₗ[ℝ] V x :=
      (LinearMap.range (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).toLinearMap).mkQ
    have hqB (v : E) : qN (B v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
    -- Every normalized tube induces the same quotient map on the entire tangent space.
    have hquotient (T : TubularNeighborhood f hf) (v : E × G) :
        qN (A T v) = e.symm v.2 := by
      have hh (u : E) : A T (u, 0) = B u := by
        have heq : (fun u : E ↦ τ T (u, 0)) =ᶠ[𝓝 a] (ψ ∘ f ∘ κ.symm) := by
          filter_upwards [hchorizontal] with u hu
          change ψ ((TubularNeighborhood.totalMap f hf T) (c.symm (u, 0))) = _
          rw [hu, hTzero]
          rfl
        have hc : HasFDerivAt (fun u : E ↦ τ T (u, 0))
            ((A T).comp (ContinuousLinearMap.inl ℝ E G)) a := by
          simpa only [Function.comp_def] using!
            HasFDerivAt.comp a (hA T) (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : G))
        exact congrArg (fun L : E →L[ℝ] F ↦ L u)
          ((hc.congr_of_eventuallyEq heq.symm).unique hB)
      let b : G → N := (TubularNeighborhood.totalMap f hf T) ∘ incl
      let L : G →L[ℝ] F := mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) b 0
      have hb : HasMFDerivAt 𝓘(ℝ, G) 𝓘(ℝ, F) b 0 L :=
        (((hTsmooth T).comp hi).mdifferentiable (by simp) 0).hasMFDerivAt
      have hL : HasFDerivAt (fun w : G ↦ ψ (b w)) L 0 := by
        simpa only [writtenInExtChartAt, mfld_simps, b, incl, Function.comp_def,
          map_zero, hTzero, hasFDerivWithinAt_univ] using! hb.2
      have hv (w : G) : A T (0, w) = L w := by
        have heq : (fun w : G ↦ τ T (a, w)) =ᶠ[𝓝 (0 : G)] (fun w : G ↦ ψ (b w)) :=
          Filter.Eventually.of_forall fun w ↦
            congrArg (ψ ∘ (TubularNeighborhood.totalMap f hf T)) (hcvertical w)
        have hc : HasFDerivAt (fun w : G ↦ τ T (a, w))
            ((A T).comp (ContinuousLinearMap.inr ℝ E G)) 0 := by
          simpa only [Function.comp_def] using!
            HasFDerivAt.comp 0 (hA T) (hasFDerivAt_prodMk_right (𝕜 := ℝ) a (0 : G))
        exact congrArg (fun L : G →L[ℝ] F ↦ L w)
          ((hc.congr_of_eventuallyEq heq.symm).unique hL)
      have hqL (w : G) : qN (L w) = e.symm w := T.normal_deriv x w
      have hsplit : A T v = A T (v.1, 0) + A T (0, v.2) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      rw [hsplit, hh, hv, map_add, hqB, hqL, zero_add]
    -- Differentiate the exact transition equation, then apply that common quotient map.
    let C : E × G → E × G := c ∘ φ P Q ∘ c.symm
    have hφx : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, G))
        (𝓘(ℝ, E).prod 𝓘(ℝ, G)) ∞ (φ P Q) z₀ :=
      (hsmooth P Q).contMDiffAt ((U P Q).2.mem_nhds (hsource P Q x))
    have hφz : φ P Q z₀ = z₀ := hzero P Q x
    have hCpoint : C (a, 0) = (a, 0) := by
      change c (φ P Q (c.symm (a, 0))) = _
      rw [hcinv, hφz, hcpoint]
    have hC : ContDiffAt ℝ ∞ C (a, 0) := by
      have h := (contMDiffAt_iff.mp hφx).2
      change ContDiffWithinAt ℝ ∞
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, G)) (φ P Q z₀) ∘ φ P Q ∘ c.symm)
        (Set.range (𝓘(ℝ, E).prod 𝓘(ℝ, G))) (c z₀) at h
      rw [hφz, hcpoint] at h
      simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using! h
    let D : (E × G) →L[ℝ] (E × G) := fderiv ℝ C (a, 0)
    have hD : HasFDerivAt C D (a, 0) := (hC.differentiableAt (by simp)).hasFDerivAt
    have hcomp : (τ P ∘ C) =ᶠ[𝓝 (a, 0)] τ Q := by
      have hcInv : ContinuousAt c.symm (a, 0) :=
        c.continuousAt_symm (hcpoint ▸ c.map_source hc₀)
      have hk : ContinuousAt (φ P Q ∘ c.symm) (a, 0) :=
        hφx.continuousAt.comp_of_eq hcInv hcinv
      have hcMem : c.source ∈ 𝓝 ((φ P Q ∘ c.symm) (a, 0)) := by
        simpa only [Function.comp_apply, hcinv, hφz] using c.open_source.mem_nhds hc₀
      have hUMem : (U P Q : Set NB) ∈ 𝓝 (c.symm (a, 0)) := by
        rw [hcinv]
        exact (U P Q).2.mem_nhds (hsource P Q x)
      filter_upwards [hk hcMem, hcInv hUMem] with z hz hUz
      change φ P Q (c.symm z) ∈ c.source at hz
      change ψ ((TubularNeighborhood.totalMap f hf P)
        (c.symm (c (φ P Q (c.symm z))))) = ψ ((TubularNeighborhood.totalMap f hf Q) (c.symm z))
      rw [c.left_inv hz, hmap P Q _ hUz]
    have hAat : HasFDerivAt (τ P) (A P) (C (a, 0)) := by
      rw [hCpoint]
      exact hA P
    have hchain : (A P).comp D = A Q :=
      (((hAat.comp (a, 0) hD).congr_of_eventuallyEq hcomp.symm).unique (hA Q))
    have hDnormal (w : G) : (D (0, w)).2 = w := by
      apply e.symm.injective
      calc
        e.symm (D (0, w)).2 = qN (A P (D (0, w))) := (hquotient P _).symm
        _ = qN (A Q (0, w)) := congrArg qN (congrArg (fun L : (E × G) →L[ℝ] F ↦
          L (0, w)) hchain)
        _ = e.symm w := hquotient Q _
    have hDsnd : fderiv ℝ (fun z : E × G ↦ (C z).2) (a, 0) =
        (ContinuousLinearMap.snd ℝ E G).comp D :=
      ((hasFDerivAt_snd (p := C (a, 0))).comp (a, 0) hD).fderiv
    change (fderiv ℝ (fun z : E × G ↦ (C z).2) (c z₀)).comp
      (ContinuousLinearMap.inr ℝ E G) = ContinuousLinearMap.id ℝ G
    rw [hcpoint, hDsnd]
    apply ContinuousLinearMap.ext
    intro w
    change (D (0, w)).2 = w
    exact hDnormal w
  let e : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, G))
      (𝓘(ℝ, E).prod 𝓘(ℝ, G)) NB NB ∞ :=
    { toFun := φ T₀ T₁
      invFun := φ T₁ T₀
      source := U T₀ T₁
      target := U T₁ T₀
      map_source' := hmaps T₀ T₁
      map_target' := hmaps T₁ T₀
      left_inv' := hinverse T₀ T₁
      right_inv' := hinverse T₁ T₀
      open_source := (U T₀ T₁).2
      open_target := (U T₁ T₀).2
      contMDiffOn_toFun := hsmooth T₀ T₁
      contMDiffOn_invFun := hsmooth T₁ T₀ }
  exact ⟨e, rfl, rfl, hsource T₀ T₁, hzero T₀ T₁, hmap T₀ T₁,
    hnormal T₀ T₁, hnormal T₁ T₀⟩

end AtiyahSinger
