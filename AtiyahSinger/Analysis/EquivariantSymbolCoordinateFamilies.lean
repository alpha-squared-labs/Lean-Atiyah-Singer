/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol

/-!
# Original symbol transport in specified moving coordinates

Public module ID: M0586.

The coordinate expression of the original geometric symbol action is given
using any specified source and target charts and frames on their actual moving
overlap. The formula selects no new chart as the group parameter varies. It is
the shared coordinate identity for uniform families of the original symbols.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM in
/-- The original symbol action has the exact matrix-cotangent formula in specified frames. -/
theorem equivariantGlobalSymbolInChart_eq (g : G)
    (p : GlobalSymbolFunction (n := n) E F)
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f']
    (y : EuclideanSpace ℝ (Fin n))
    (hy₀ : y ∈ symbolChartDomain E F d e' f')
    (hmove₀ : g⁻¹ • d.symm y ∈ c.source ∩ e.baseSet ∩ f.baseSet)
    (η : EuclideanSpace ℝ (Fin n)) :
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    letI (x : M) : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let D := Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g
    let t := c.symm.trans (D.toHomeomorph.toOpenPartialHomeomorph.trans d)
    let x := fun y ↦ g⁻¹ • d.symm y
    let A := fun y ↦ (f'.continuousLinearMapAt ℂ (g • x y)).comp
      ((τ.linearMap g (x y)).toContinuousLinearMap.comp (f.symmL ℂ (x y)))
    let B := fun y ↦ (e.continuousLinearMapAt ℂ (g⁻¹ • d.symm y)).comp
      ((σ.linearMap g⁻¹ (d.symm y)).toContinuousLinearMap.comp (e'.symmL ℂ (d.symm y)))
    globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ g p) d e' f' y η =
      matrixSymbol A B (cotangentSymbol t (globalSymbolInChart E F p c e f)) y η := by
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := Diffeomorph.smul (M := M) IG I ∞ g
  let t := c.symm.trans (D.toHomeomorph.toOpenPartialHomeomorph.trans d)
  let oldBase : X → M := fun y ↦ g⁻¹ • d.symm y
  let A : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    fun y ↦ (f'.continuousLinearMapAt ℂ (g • oldBase y)).comp
      ((τ.linearMap g (oldBase y)).toContinuousLinearMap.comp (f.symmL ℂ (oldBase y)))
  let B : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    fun y ↦ (e.continuousLinearMapAt ℂ (g⁻¹ • d.symm y)).comp
      ((σ.linearMap g⁻¹ (d.symm y)).toContinuousLinearMap.comp (e'.symmL ℂ (d.symm y)))
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hy := And.intro hy₀ hmove₀
  change globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ g p)
    d e' f' y η = matrixSymbol A B (cotangentSymbol t (globalSymbolInChart E F p c e f)) y η
  symm
  let ξ := covectorFromChart d (d.symm y) η
  let ζ := (cotangentDiffeomorphMap D.symm ⟨d.symm y, ξ⟩).snd
  have hreturn : D (oldBase y) = d.symm y := smul_inv_smul g (d.symm y)
  have hcOld : c.symm (c (oldBase y)) = oldBase y := c.left_inv hy.2.1.1
  -- The chain rule identifies the transported covector with this same coordinate dual.
  have hfreq : covectorInChart c (oldBase y) ζ =
      (fderiv ℝ t (t.symm y)).adjoint η := by
    have hcs := (contMDiffAt_symm_of_mem_maximalAtlas hcM
      (c.map_source hy.2.1.1)).mdifferentiableAt (by simp)
    have hmove := mfderiv_comp (c (oldBase y))
      (D.mdifferentiable (by simp) (c.symm (c (oldBase y)))) hcs
    have htarget := (contMDiffAt_of_mem_maximalAtlas hdM
      (d.map_target hy.1.1.1)).mdifferentiableAt (by simp)
    have htarget' : MDifferentiableAt I I d (D (c.symm (c (oldBase y)))) := by
      simpa only [hcOld, hreturn] using htarget
    have hchain := mfderiv_comp (c (oldBase y)) htarget'
      ((D.mdifferentiable (by simp) _).comp _ hcs)
    rw [hmove, hcOld, hreturn] at hchain
    have htcomp : fderiv ℝ t (t.symm y) =
        (mfderiv I I d (d.symm y)).comp
          ((mfderiv I I D (oldBase y)).comp
            (mfderiv I I c.symm (c (oldBase y)))) := by
      rw [mfderiv_eq_fderiv] at hchain
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel,
        Function.comp_apply] at hchain
      rw [hcOld, hreturn] at hchain
      exact hchain
    ext a
    change inner ℝ η ((mfderiv I I d (d.symm y))
        ((mfderiv I I D (oldBase y))
          ((mfderiv I I c.symm (c (oldBase y)))
            (EuclideanSpace.single a 1)))) = _
    have hadj := (fderiv ℝ t (t.symm y)).adjoint_inner_left
      (EuclideanSpace.single a 1) η
    calc
      _ = inner ℝ η ((fderiv ℝ t (t.symm y)) (EuclideanSpace.single a 1)) := by
        rw [htcomp]
        rfl
      _ = inner ℝ ((fderiv ℝ t (t.symm y)).adjoint η)
          (EuclideanSpace.single a 1) := hadj.symm
      _ = _ := by
        simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) a 1
          ((fderiv ℝ t (t.symm y)).adjoint η)
  have hpcoord := globalSymbolInChart_covectorInChart E F p c hc e f
    (oldBase y) hy.2.1.1 ζ
  rw [hfreq] at hpcoord
  -- Cancel only the selected original frames and the actual output-index transport.
  apply ContinuousLinearMap.ext
  intro v
  change A y ((globalSymbolInChart E F p c e f (c (oldBase y))
    ((fderiv ℝ t (t.symm y)).adjoint η)) (B y v)) = _
  rw [hpcoord]
  change f'.continuousLinearMapAt ℂ (g • oldBase y)
    (τ.linearMap g (oldBase y)
      (f.symmL ℂ (oldBase y) (f.continuousLinearMapAt ℂ (oldBase y)
        (p (oldBase y) ζ (e.symmL ℂ (oldBase y)
          (e.continuousLinearMapAt ℂ (oldBase y)
            (σ.linearMap g⁻¹ (d.symm y) (e'.symmL ℂ (d.symm y) v)))))))) = _
  erw [f.symmL_continuousLinearMapAt (R := ℂ) hy.2.2,
    e.symmL_continuousLinearMapAt (R := ℂ) hy.2.1.2]
  have hfo : g • oldBase y ∈ f'.baseSet := by
    change D (oldBase y) ∈ f'.baseSet
    rw [hreturn]
    exact hy.1.2
  have hvector : (⟨d.symm y,
      equivariantGlobalSymbolLinearMap IG σ τ g p (d.symm y) ξ
        (e'.symmL ℂ (d.symm y) v)⟩ : TotalSpace Unit F) =
      ⟨g • oldBase y, τ.linearMap g (oldBase y)
        (p (oldBase y) ζ (σ.linearMap g⁻¹ (d.symm y)
          (e'.symmL ℂ (d.symm y) v)))⟩ := by
    let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
      subst y
      exact ContinuousLinearMap.id ℂ (F x)
    have ht {x y : M} (h : x = y) (w : F x) :
        (⟨y, transport h w⟩ : TotalSpace Unit F) = ⟨x, w⟩ := by
      subst y
      rfl
    change (⟨d.symm y, transport (smul_inv_smul g (d.symm y)) _⟩ :
      TotalSpace Unit F) = _
    exact ht (smul_inv_smul g (d.symm y)) _
  have hcoord := congrArg (fun w : TotalSpace Unit F ↦
    (f' (⟨w.proj, w.snd⟩ : TotalSpace (EuclideanSpace ℂ (Fin q)) F)).2) hvector
  change f'.continuousLinearMapAt ℂ (g • oldBase y)
    (τ.linearMap g (oldBase y)
      (p (oldBase y) ζ (σ.linearMap g⁻¹ (d.symm y) (e'.symmL ℂ (d.symm y) v)))) =
    f'.continuousLinearMapAt ℂ (d.symm y)
      (equivariantGlobalSymbolLinearMap IG σ τ g p (d.symm y) ξ (e'.symmL ℂ (d.symm y) v))
  rw [f'.continuousLinearMapAt_apply_of_mem ℂ hfo,
    f'.continuousLinearMapAt_apply_of_mem ℂ hy.1.2]
  exact hcoord.symm

end AtiyahSinger
