/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Local coordinates of open symbol transport

Public module ID: M0837.

Two specified bundle equivalences and the differential of an open-region
diffeomorphism relate two given fiberwise symbol functions. In the original
charts this becomes cotangent substitution composed with the two frame matrices.
The comparison holds at every covector on the chart overlap and requires no
symbol order, homogeneity or ellipticity. Local choices also yield smooth
invertible frame matrices.

These are coordinate identities for the transport used in SG III.13.4.
Quantization and gluing to an ambient symbol are separate constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

set_option backward.isDefEq.respectTransparency false in
/-- An open inclusion has the identity derivative in the inherited native tangent charts. -/
theorem mfderiv_openSubtypeVal {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (U : Opens M) (x : U) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (Subtype.val : U → M) x = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  -- Both native charts have identity differential at their own basepoint.
  have hU := mfderiv_extChartAt_self (I := I) (x := x)
  have hM := mfderiv_extChartAt_self (I := I) (x := x.val)
  simp only [I, extChartAt, mfld_simps] at hU hM
  have h := mfderiv_comp (I := I) (I' := I) (I'' := I) x
    (mdifferentiableAt_atlas (I := I) (chart_mem_atlas _ _) (mem_chart_source _ _))
    ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) x)
  change mfderiv I I (chartAt (EuclideanSpace ℝ (Fin n)) x) x = _ at h
  rw [hU, hM] at h
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun T ↦ T v) h.symm

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)
  (U : Opens M) (V : Opens N)
  (e : U ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ V)
  (α : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ G.Fiber)) x)
  (hα : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
    (fun x ↦ (α x).toLinearMap))
  (β : ∀ x : U,
    ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber) x ≃ₗ[ℂ]
      (((⟨e, e.continuous⟩ : C(U, V)) : U → V) *ᵖ
        ((ContinuousMap.subtypeVal (V : Set N) : V → N) *ᵖ H.Fiber)) x)
  (hβ : IsSmoothBundleMap (n := n) (r := F.rank) (q := H.rank)
    (fun x ↦ (β x).toLinearMap))


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- The same dependent fiber maps are compared before and after two chart differentials.
/-- The actual open transport in specified original charts is the cotangent substitution
and the two specified fiber matrices. No symbol order or ellipticity is required. -/
theorem globalSymbolInChart_openTransport
    (hU : Nonempty U) (hV : Nonempty V)
    (C₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (C : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)))
    (hC₀ : C₀ ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hC : C ∈ atlas (EuclideanSpace ℝ (Fin n)) N)
    (f₀ : Trivialization (EuclideanSpace ℂ (Fin E.rank))
      (π (EuclideanSpace ℂ (Fin E.rank)) E.Fiber))
    (g₀ : Trivialization (EuclideanSpace ℂ (Fin F.rank))
      (π (EuclideanSpace ℂ (Fin F.rank)) F.Fiber))
    (f : Trivialization (EuclideanSpace ℂ (Fin G.rank))
      (π (EuclideanSpace ℂ (Fin G.rank)) G.Fiber))
    (g : Trivialization (EuclideanSpace ℂ (Fin H.rank))
      (π (EuclideanSpace ℂ (Fin H.rank)) H.Fiber))
    [MemTrivializationAtlas f₀] [MemTrivializationAtlas g₀]
    [MemTrivializationAtlas f] [MemTrivializationAtlas g]
    (p : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
    (J : GlobalSymbolFunction (n := n) G.Fiber H.Fiber)
    (hJ : ∀ (x : U) η (v : E.Fiber x.val),
      J (e x).val η (α x v) =
        β x (p x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) :
    let t := (C₀.subtypeRestr hU).symm.trans
      (e.toHomeomorph.toOpenPartialHomeomorph.trans (C.subtypeRestr hV))
    let x := fun z : EuclideanSpace ℝ (Fin n) ↦ e.symm ((C.subtypeRestr hV).symm z)
    let A := fun z ↦ ((g.linearMapAt ℂ (e (x z)).val).comp
      ((β (x z)).toLinearMap.comp (g₀.symmL ℂ (x z).val).toLinearMap)).toContinuousLinearMap
    let B := fun z ↦ ((f₀.linearMapAt ℂ (x z).val).comp
      ((α (x z)).symm.toLinearMap.comp
        (f.symmL ℂ (e (x z)).val).toLinearMap)).toContinuousLinearMap
    ∀ z ∈ t.target, (x z).val ∈ f₀.baseSet → (x z).val ∈ g₀.baseSet → ∀ η,
      globalSymbolInChart G.Fiber H.Fiber J C f g z η =
        matrixSymbol A B (cotangentSymbol t
          (globalSymbolInChart E.Fiber F.Fiber p C₀ f₀ g₀)) z η := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let C₁ := C₀.subtypeRestr hU
  let CV := C.subtypeRestr hV
  let t := C₁.symm.trans (e.toHomeomorph.toOpenPartialHomeomorph.trans CV)
  let old (z : X) : U := e.symm (CV.symm z)
  dsimp only
  intro z hz hzf hzg η
  let x := old z
  have hxC₁ : x ∈ C₁.source := hz.2
  have hxC : x.val ∈ C₀.source := by simpa [C₁] using hxC₁
  have hxreturn : (e x).val = C.symm z := by
    change (e (e.symm (CV.symm z))).val = _
    rw [e.apply_symm_apply]
    exact C.subtypeRestr_symm_apply hV hz.1.1
  have hyC : (e x).val ∈ C.source := by
    rw [hxreturn]
    exact C.map_target hz.1.1.1
  have hc₁ : C₁ ∈ (contDiffGroupoid ∞ I).maximalAtlas U :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hC₀ hU
  -- Open inclusions are the identity on the inherited native tangent models.
  have hCinvD : mfderiv I I C₁.symm (C₀ x.val) =
      mfderiv I I C₀.symm (C₀ x.val) := by
    have heq : (Subtype.val : U → M) ∘ C₁.symm =ᶠ[𝓝 (C₀ x.val)] C₀.symm := by
      filter_upwards [C₁.open_target.mem_nhds (C₁.map_source hxC₁)] with w hw
      exact (C₀.subtypeRestr_symm_eqOn hU hw).symm
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (C₀ x.val)
      ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) _)
      ((contMDiffAt_symm_of_mem_maximalAtlas hc₁
        (C₁.map_source hxC₁)).mdifferentiableAt (by simp))
    rw [mfderiv_openSubtypeVal] at hcomp
    have heqD := heq.mfderiv_eq (I := I) (I' := I)
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T ↦ T v) (hcomp.symm.trans heqD)
  let move : U → X := fun y ↦ C (e y).val
  have hmove : MDifferentiableAt I I move x :=
    (mdifferentiableAt_atlas (I := I) hC hyC).comp x
      (((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) _).comp x
        (e.mdifferentiable (by simp) x))
  have hmoveD : mfderiv I I move x =
      (mfderiv I I C (e x).val).comp (mfderiv I I e x) := by
    have hsub := mfderiv_comp (I := I) (I' := I) (I'' := I) x
      ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) _)
      (e.mdifferentiable (by simp) x)
    have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) x
      (mdifferentiableAt_atlas (I := I) hC hyC)
      (((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiable (by simp) _).comp x
        (e.mdifferentiable (by simp) x))
    rw [hsub, mfderiv_openSubtypeVal] at hcomp
    exact hcomp
  -- The derivative is of this same original chart composite, not a chosen matrix model.
  have htD : fderiv ℝ t (t.symm z) = (mfderiv I I C (e x).val).comp
      ((mfderiv I I e x).comp (mfderiv I I C₀.symm (C₀ x.val))) := by
    have hcs := (contMDiffAt_symm_of_mem_maximalAtlas hc₁
      (C₁.map_source hxC₁)).mdifferentiableAt (by simp)
    have hmove' : MDifferentiableAt I I move (C₁.symm (C₀ x.val)) := by
      change MDifferentiableAt I I move (C₁.symm (C₁ x))
      rwa [C₁.left_inv hxC₁]
    have hchain := mfderiv_comp (I := I) (I' := I) (I'' := I)
      (C₀ x.val) hmove' hcs
    change mfderiv I I (move ∘ C₁.symm) (C₀ x.val) = _ at hchain
    rw [mfderiv_eq_fderiv] at hchain
    have hc := C₁.left_inv hxC₁
    change C₁.symm (C₀ x.val) = x at hc
    rw [hc, hmoveD, hCinvD, ContinuousLinearMap.comp_assoc] at hchain
    exact hchain
  have hfreq : covectorInChart C₀ x.val
      ((covectorFromChart C (e x).val η).comp (mfderiv I I e x)) =
        (fderiv ℝ t (t.symm z)).adjoint η := by
    ext i
    change inner ℝ η ((mfderiv I I C (e x).val)
      ((mfderiv I I e x) ((mfderiv I I C₀.symm (C₀ x.val))
        (EuclideanSpace.single i 1)))) = _
    erw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← htD]
    exact ((fderiv ℝ t (t.symm z)).adjoint_inner_left
      (EuclideanSpace.single i 1) η).symm.trans
        (by
          simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) i 1
            ((fderiv ℝ t (t.symm z)).adjoint η))
  have hco := globalSymbolInChart_covectorInChart E.Fiber F.Fiber p C₀ hC₀ f₀ g₀
    x.val hxC ((covectorFromChart C (e x).val η).comp (mfderiv I I e x))
  rw [hfreq] at hco
  -- Cancel the original source frames around the same transported input vector.
  dsimp only [matrixSymbol, cotangentSymbol]
  change globalSymbolInChart G.Fiber H.Fiber J C f g z η =
    ContinuousLinearMap.comp _ ((globalSymbolInChart E.Fiber F.Fiber p C₀ f₀ g₀
      (C₀ x.val) ((fderiv ℝ t (t.symm z)).adjoint η)).comp _)
  rw [hco]
  apply ContinuousLinearMap.ext
  intro v
  have htarget : globalSymbolInChart G.Fiber H.Fiber J C f g z η v =
      g.continuousLinearMapAt ℂ (e x).val
        (J (e x).val (covectorFromChart C (e x).val η)
          (f.symmL ℂ (e x).val v)) := by
    dsimp only [globalSymbolInChart]
    rw [← hxreturn]
    rfl
  rw [htarget]
  let ζ := (covectorFromChart C (e x).val η).comp (mfderiv I I e x)
  let w : E.Fiber x.val := (α x).symm (f.symmL ℂ (e x).val v)
  have htrans : J (e x).val (covectorFromChart C (e x).val η)
      (f.symmL ℂ (e x).val v) = β x (p x.val ζ w) := by
    have h := hJ x (covectorFromChart C (e x).val η) w
    rwa [(α x).apply_symm_apply] at h
  rw [htrans]
  have hfCancel : f₀.symmL ℂ x.val (f₀.linearMapAt ℂ x.val w) = w :=
    f₀.symmL_continuousLinearMapAt (R := ℂ) hzf w
  have hgCancel : g₀.symmL ℂ x.val
      (g₀.continuousLinearMapAt ℂ x.val (p x.val ζ w)) = p x.val ζ w :=
    g₀.symmL_continuousLinearMapAt (R := ℂ) hzg _
  change g.continuousLinearMapAt ℂ (e x).val (β x (p x.val ζ w)) =
    g.linearMapAt ℂ (e x).val (β x (g₀.symmL ℂ x.val
      (g₀.continuousLinearMapAt ℂ x.val (p x.val ζ
        (f₀.symmL ℂ x.val (f₀.linearMapAt ℂ x.val w))))))
  rw [hfCancel, hgCancel]
  rfl

include hα hβ in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
-- One choice of charts and matrices serves every source and target symbol with the given transport.
/-- Open transport locally has the original cotangent formula and smooth invertible frame maps. -/
theorem exists_local_openSymbolInChart
    (C : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin n)))
    (hC : C ∈ atlas (EuclideanSpace ℝ (Fin n)) N)
    (f : Trivialization (EuclideanSpace ℂ (Fin G.rank))
      (π (EuclideanSpace ℂ (Fin G.rank)) G.Fiber))
    (g : Trivialization (EuclideanSpace ℂ (Fin H.rank))
      (π (EuclideanSpace ℂ (Fin H.rank)) H.Fiber))
    [MemTrivializationAtlas f] [MemTrivializationAtlas g]
    (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ symbolChartDomain G.Fiber H.Fiber C f g) (hzV : C.symm z ∈ V) :
    ∃ (C₀ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (f₀ : Trivialization (EuclideanSpace ℂ (Fin E.rank))
        (π (EuclideanSpace ℂ (Fin E.rank)) E.Fiber))
      (g₀ : Trivialization (EuclideanSpace ℂ (Fin F.rank))
        (π (EuclideanSpace ℂ (Fin F.rank)) F.Fiber))
      (hf₀ : MemTrivializationAtlas f₀) (hg₀ : MemTrivializationAtlas g₀),
      letI := hf₀
      letI := hg₀
      C₀ ∈ atlas (EuclideanSpace ℝ (Fin n)) M ∧
      ∃ (Z : Set (EuclideanSpace ℝ (Fin n)))
        (t : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℂ (Fin F.rank) →L[ℂ] EuclideanSpace ℂ (Fin H.rank))
        (B : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin E.rank)),
        IsOpen Z ∧ z ∈ Z ∧ Z ⊆ symbolChartDomain G.Fiber H.Fiber C f g ∧ Z ⊆ t.target ∧
        t.source ⊆ symbolChartDomain E.Fiber F.Fiber C₀ f₀ g₀ ∧
        ContDiffOn ℝ ∞ t t.source ∧ ContDiffOn ℝ ∞ t.symm t.target ∧
        ContDiffOn ℝ ∞ A Z ∧ ContDiffOn ℝ ∞ B Z ∧
        (∀ y ∈ Z, Function.Bijective (A y) ∧ Function.Bijective (B y)) ∧
        ∀ (p : GlobalSymbolFunction (n := n) E.Fiber F.Fiber)
          (J : GlobalSymbolFunction (n := n) G.Fiber H.Fiber),
          (∀ (x : U) η (v : E.Fiber x.val),
            J (e x).val η (α x v) = β x
              (p x.val (η.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e x)) v)) →
          ∀ y ∈ Z, ∀ η, globalSymbolInChart G.Fiber H.Fiber J C f g y η =
            matrixSymbol A B (cotangentSymbol t
              (globalSymbolInChart E.Fiber F.Fiber p C₀ f₀ g₀)) y η := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let hV : Nonempty V := ⟨⟨C.symm z, hzV⟩⟩
  let CV := C.subtypeRestr hV
  have hCV : CV ∈ (contDiffGroupoid ∞ I).maximalAtlas V :=
    StructureGroupoid.subtypeRestr_mem_maximalAtlas hC hV
  have hzCV : z ∈ CV.target := by
    refine ⟨hz.1.1, ?_⟩
    simpa using hzV
  let old (y : X) : U := e.symm (CV.symm y)
  let x₀ := old z
  let hU : Nonempty U := ⟨x₀⟩
  let C₀ := chartAt X x₀.val
  let f₀ := trivializationAt (EuclideanSpace ℂ (Fin E.rank)) E.Fiber x₀.val
  let g₀ := trivializationAt (EuclideanSpace ℂ (Fin F.rank)) F.Fiber x₀.val
  have hC₀ : C₀ ∈ atlas X M := chart_mem_atlas _ _
  let W := symbolChartDomain G.Fiber H.Fiber C f g ∩ CV.target
  have hW : IsOpen W := (isOpen_symbolChartDomain G.Fiber H.Fiber C f g).inter CV.open_target
  have hOld : ContMDiffOn I I ∞ old W := by
    intro y hy
    exact (e.symm.contMDiffAt.comp y
      (contMDiffAt_symm_of_mem_maximalAtlas hCV hy.2)).contMDiffWithinAt
  let S₀ := C₀.source ∩ f₀.baseSet ∩ g₀.baseSet
  have hS₀ : IsOpen S₀ := (C₀.open_source.inter f₀.open_baseSet).inter g₀.open_baseSet
  let Z := W ∩ (fun y ↦ (old y).val) ⁻¹' S₀
  have hZ : IsOpen Z :=
    (contMDiff_subtype_val.comp_contMDiffOn hOld).continuousOn.isOpen_inter_preimage hW hS₀
  have hzZ : z ∈ Z := ⟨⟨hz, hzCV⟩, ⟨⟨mem_chart_source _ _,
    mem_baseSet_trivializationAt _ _ _⟩, mem_baseSet_trivializationAt _ _ _⟩⟩
  let S := symbolChartDomain E.Fiber F.Fiber C₀ f₀ g₀
  have hS : IsOpen S := isOpen_symbolChartDomain E.Fiber F.Fiber C₀ f₀ g₀
  let t₀ := (C₀.subtypeRestr hU).symm.trans
    (e.toHomeomorph.toOpenPartialHomeomorph.trans CV)
  let t := t₀.restrOpen S hS
  obtain ⟨ht₀, hts₀, _⟩ := contDiff_openChartTransition U V e hU hV C₀ C hC₀ hC
  have ht : ContDiffOn ℝ ∞ t t.source := ht₀.mono Set.inter_subset_left
  have hts : ContDiffOn ℝ ∞ t.symm t.target := hts₀.mono Set.inter_subset_left
  have hZt : Z ⊆ t.target := by
    intro y hy
    refine ⟨⟨⟨hy.1.2, Set.mem_univ _⟩, ?_⟩, ?_⟩
    · change old y ∈ (C₀.subtypeRestr hU).source
      simpa using hy.2.1.1
    · change C₀ (old y).val ∈ S
      refine ⟨⟨C₀.map_source hy.2.1.1, ?_⟩, ?_⟩
      · change C₀.symm (C₀ (old y).val) ∈ f₀.baseSet
        simpa only [C₀.left_inv hy.2.1.1] using hy.2.1.2
      · change C₀.symm (C₀ (old y).val) ∈ g₀.baseSet
        simpa only [C₀.left_inv hy.2.1.1] using hy.2.2
  have hreturn (y : X) (hy : y ∈ Z) : (e (old y)).val = C.symm y := by
    change (e (e.symm (CV.symm y))).val = _
    rw [e.apply_symm_apply]
    exact C.subtypeRestr_symm_apply hV hy.1.2
  let A (y : X) := ((g.linearMapAt ℂ (e (old y)).val).comp
    ((β (old y)).toLinearMap.comp (g₀.symmL ℂ (old y).val).toLinearMap)).toContinuousLinearMap
  let B (y : X) := ((f₀.linearMapAt ℂ (old y).val).comp
    ((α (old y)).symm.toLinearMap.comp
      (f.symmL ℂ (e (old y)).val).toLinearMap)).toContinuousLinearMap
  have hA : ContDiffOn ℝ ∞ A Z :=
    ((contMDiffOn_openBundleMap_matrices F H U V e β hβ g₀ g).1.comp
      (hOld.mono Set.inter_subset_left) (fun y hy ↦
        ⟨hy.2.2, (hreturn y hy).symm ▸ hy.1.1.2⟩)).contDiffOn
  have hB : ContDiffOn ℝ ∞ B Z :=
    ((contMDiffOn_openBundleMap_matrices E G U V e α hα f₀ f).2.comp
      (hOld.mono Set.inter_subset_left) (fun y hy ↦
        ⟨hy.2.1.2, (hreturn y hy).symm ▸ hy.1.1.1.2⟩)).contDiffOn
  have hbijective (y : X) (hy : y ∈ Z) :
      Function.Bijective (A y) ∧ Function.Bijective (B y) := by
    have hyf : (e (old y)).val ∈ f.baseSet := (hreturn y hy).symm ▸ hy.1.1.1.2
    have hyg : (e (old y)).val ∈ g.baseSet := (hreturn y hy).symm ▸ hy.1.1.2
    constructor
    · have heq : ⇑(A y) = fun v ↦
          (g.linearEquivAt ℂ (e (old y)).val hyg)
            (β (old y) ((g₀.linearEquivAt ℂ (old y).val hy.2.2).symm v)) := by
        funext v
        change g.linearMapAt ℂ (e (old y)).val
          (β (old y) (g₀.symmL ℂ (old y).val v)) = _
        rw [g.coe_linearMapAt_of_mem hyg, g₀.symmL_apply hy.2.2]
        rfl
      rw [heq]
      exact (g.linearEquivAt ℂ (e (old y)).val hyg).bijective.comp
        ((β (old y)).bijective.comp (g₀.linearEquivAt ℂ (old y).val hy.2.2).symm.bijective)
    · have heq : ⇑(B y) = fun v ↦ (f₀.linearEquivAt ℂ (old y).val hy.2.1.2)
          ((α (old y)).symm ((f.linearEquivAt ℂ (e (old y)).val hyf).symm v)) := by
        funext v
        change f₀.linearMapAt ℂ (old y).val
          ((α (old y)).symm (f.symmL ℂ (e (old y)).val v)) = _
        rw [f₀.coe_linearMapAt_of_mem hy.2.1.2, f.symmL_apply hyf]
        rfl
      rw [heq]
      exact (f₀.linearEquivAt ℂ (old y).val hy.2.1.2).bijective.comp
        ((α (old y)).symm.bijective.comp (f.linearEquivAt ℂ (e (old y)).val hyf).symm.bijective)
  refine ⟨C₀, f₀, g₀, inferInstance, inferInstance, hC₀, Z, t, A, B,
    hZ, hzZ, fun _ hy ↦ hy.1.1, hZt, Set.inter_subset_right, ht, hts, hA, hB,
    hbijective, ?_⟩
  intro p J hJ y hy η
  exact globalSymbolInChart_openTransport E F G H U V e α β hU hV C₀ C hC₀ hC
    f₀ g₀ f g p J hJ y (hZt hy).1 hy.2.1.2 hy.2.2 η

end AtiyahSinger
