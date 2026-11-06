/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantPseudodifferentialOperator
public import AtiyahSinger.Analysis.EquivariantSmoothing
public import AtiyahSinger.Analysis.GlobalComposition
public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.PseudodifferentialRefinement
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# The geometric action on the original principal-symbol quotient

Public module ID: M0554.

SG III.3.13--3.14, printed p.186, and III.3.19, p.188, give coordinate covariance
and the principal-symbol quotient. SG III.9, p.214, states invariance of the
principal symbol of an equivariant differential operator. Its extension here
to the existing pseudodifferential quotient is a standard supplement combining
those two ingredients; it is not a separately numbered theorem in SG.

The action uses the actual moving-fiber maps of the original equivariant bundles
and the inverse cotangent lift of the specified smooth base action. It preserves
the existing `S^m / S^(m-1)` quotient. The action selects no preferred full symbol,
homogeneous representative, topology, or invariant metric, and does not require
compactness of the group. Its compatibility with operators uses one actual finite
conjugated representation for both the operator qualification and the symbol class.
Finite-dimensionality of the original fibers supplies continuity of their
linear action maps, without imposing an extra continuity hypothesis on each map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

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

/-- Conjugate a genuine Hom-valued symbol using the original inverse cotangent lift. -/
def equivariantGlobalSymbolLinearMap (g : G) :
    GlobalSymbolFunction (n := n) E F →ₗ[ℂ] GlobalSymbolFunction (n := n) E F := by
  letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  letI (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  letI (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  -- Transport changes only the dependent output index g*(g⁻¹*x)=x.
  let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
    subst y
    exact ContinuousLinearMap.id ℂ (F x)
  -- The frequency at g⁻¹*x is ξ precomposed with d(g) at g⁻¹*x.
  let inverseLift := cotangentDiffeomorphMap
    (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm
  exact
    { toFun := fun p x ξ ↦
        (transport (smul_inv_smul g x)).comp
          ((τ.linearMap g (g⁻¹ • x)).toContinuousLinearMap.comp
            ((p (g⁻¹ • x) (inverseLift ⟨x, ξ⟩).snd).comp
              (σ.linearMap g⁻¹ x).toContinuousLinearMap))
      map_add' := by
        intro p p'
        funext x ξ
        ext v
        change (transport (smul_inv_smul g x))
            (τ.linearMap g (g⁻¹ • x)
              ((p (g⁻¹ • x) (inverseLift ⟨x, ξ⟩).snd +
                p' (g⁻¹ • x) (inverseLift ⟨x, ξ⟩).snd) (σ.linearMap g⁻¹ x v))) = _
        simp
      map_smul' := by
        intro c p
        funext x ξ
        ext v
        change (transport (smul_inv_smul g x))
            (τ.linearMap g (g⁻¹ • x)
              ((c • p (g⁻¹ • x) (inverseLift ⟨x, ξ⟩).snd) (σ.linearMap g⁻¹ x v))) = _
        simp }

variable [hG : IsManifold IG ∞ G]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)

omit hG hM hE in
include hσ in
set_option linter.unusedSectionVars false in
/-- Original moving-frame action matrices remain smooth after a smooth base substitution. -/
private theorem contDiffOn_equivariantFrameMap
    (g : G)
    (e f : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → M)
    (hc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ c U)
    (he : ∀ y ∈ U, c y ∈ e.baseSet)
    (hf : ∀ y ∈ U, g • c y ∈ f.baseSet) :
    let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    let (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    ContDiffOn ℝ ∞ (fun y ↦
      (f.continuousLinearMapAt ℂ (g • c y)).comp
        ((σ.linearMap g (c y)).toContinuousLinearMap.comp (e.symmL ℂ (c y)))) U := by
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let L (y : EuclideanSpace ℝ (Fin n)) :=
    (f.continuousLinearMapAt ℂ (g • c y)).comp
      ((σ.linearMap g (c y)).toContinuousLinearMap.comp (e.symmL ℂ (c y)))
  -- Assemble the smooth original action columns into the same finite-dimensional map.
  have hcol (j : Fin r) : ContDiffOn ℝ ∞
      (fun y ↦ L y (EuclideanSpace.single j 1)) U := by
    have h := (hσ e f j).comp (contMDiffOn_const.prodMk hc)
      (fun y hy ↦ ⟨he y hy, hf y hy⟩)
    exact h.contDiffOn.congr (fun y hy ↦ by
      simp only [L, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
      exact f.continuousLinearMapAt_apply_of_mem ℂ (hf y hy) _)
  have hsum : ContDiffOn ℝ ∞ (fun y ↦ ∑ j : Fin r,
      ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
        (EuclideanSpace ℂ (Fin r)) (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j)
        (L y (EuclideanSpace.single j 1))) U := by
    apply ContDiffOn.sum
    intro j _
    let R := ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
      (EuclideanSpace ℂ (Fin r)) (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) j)
    exact (R.restrictScalars ℝ).contDiff.comp_contDiffOn (hcol j)
  apply hsum.congr
  intro y _
  apply ContinuousLinearMap.ext
  intro v
  change L y v = _
  have h := congrArg (L y) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v)
  simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr] using h.symm

omit hG hE hF in
include hM hσ hτ in
/-- In original frames, geometric symbol transport is a cotangent coordinate change
with the two specified smooth action matrices. The same local witnesses work for every symbol. -/
theorem exists_local_equivariantGlobalSymbolInChart (g : G)
    (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e'] [MemTrivializationAtlas f']
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F d e' f') :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F))
      (he : MemTrivializationAtlas e) (hf : MemTrivializationAtlas f),
      letI := he
      letI := hf
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M ∧
      ∃ (Z : Set (EuclideanSpace ℝ (Fin n)))
        (t : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
        (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q))
        (B : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)),
        IsOpen Z ∧ z ∈ Z ∧ Z ⊆ symbolChartDomain E F d e' f' ∧ Z ⊆ t.target ∧
        t.source ⊆ symbolChartDomain E F c e f ∧
        ContDiffOn ℝ ∞ t t.source ∧ ContDiffOn ℝ ∞ t.symm t.target ∧
        ContDiffOn ℝ ∞ A Z ∧ ContDiffOn ℝ ∞ B Z ∧
        ∀ (p : GlobalSymbolFunction (n := n) E F) y, y ∈ Z → ∀ η,
          globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ g p)
            d e' f' y η =
              matrixSymbol A B (cotangentSymbol t (globalSymbolInChart E F p c e f)) y η := by
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let U := symbolChartDomain E F d e' f'
  have hU : IsOpen U := isOpen_symbolChartDomain E F d e' f'
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  let D := Diffeomorph.smul (M := M) IG I ∞ g
  have hDinv : ContMDiff I I ∞ (fun x : M ↦ g⁻¹ • x) := D.symm.contMDiff
  -- Choose original source charts and frames on an overlap around the moved base point.
  let x₀ := g⁻¹ • d.symm z
  let c := chartAt X x₀
  have hc : c ∈ atlas X M := chart_mem_atlas _ _
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x₀
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x₀
  let W := c.source ∩ e.baseSet ∩ f.baseSet
  have hW : IsOpen W := (c.open_source.inter e.open_baseSet).inter f.open_baseSet
  let oldBase : X → M := fun y ↦ g⁻¹ • d.symm y
  let Z := U ∩ oldBase ⁻¹' W
  have hdU : ContMDiffOn I I ∞ d.symm U := by
    intro y hy
    exact (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1.1).contMDiffWithinAt
  have hOld : ContMDiffOn I I ∞ oldBase U := hDinv.comp_contMDiffOn hdU
  have hZ : IsOpen Z := hOld.continuousOn.isOpen_inter_preimage hU hW
  have hzZ : z ∈ Z := ⟨hz, ⟨⟨mem_chart_source _ _,
    mem_baseSet_trivializationAt _ _ _⟩, mem_baseSet_trivializationAt _ _ _⟩⟩
  let S := symbolChartDomain E F c e f
  have hS : IsOpen S := isOpen_symbolChartDomain E F c e f
  -- The coordinate map is the actual composite: source chart inverse, g, target chart.
  let t₀ : OpenPartialHomeomorph X X :=
    c.symm.trans (D.toHomeomorph.toOpenPartialHomeomorph.trans d)
  let t := t₀.restrOpen S hS
  have ht₀ : ContDiffOn ℝ ∞ t₀ t₀.source := by
    intro y hy
    have hchart : ContMDiffAt I I ∞ c.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1
    have hmove : ContMDiffAt I I ∞ (fun w : X ↦ D (c.symm w)) y :=
      D.contMDiffAt.comp y hchart
    have hcomp : ContMDiffAt I I ∞ (fun w : X ↦ d (D (c.symm w))) y :=
      (contMDiffAt_of_mem_maximalAtlas hdM hy.2.2).comp y hmove
    exact hcomp.contDiffAt.contDiffWithinAt
  have hts₀ : ContDiffOn ℝ ∞ t₀.symm t₀.target := by
    intro y hy
    have hchart : ContMDiffAt I I ∞ d.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1.1
    have hmove : ContMDiffAt I I ∞ (fun w : X ↦ D.symm (d.symm w)) y :=
      D.symm.contMDiffAt.comp y hchart
    have hcomp : ContMDiffAt I I ∞ (fun w : X ↦ c (D.symm (d.symm w))) y :=
      (contMDiffAt_of_mem_maximalAtlas hcM hy.2).comp y hmove
    exact hcomp.contDiffAt.contDiffWithinAt
  have ht : ContDiffOn ℝ ∞ t t.source := ht₀.mono Set.inter_subset_left
  have hts : ContDiffOn ℝ ∞ t.symm t.target := hts₀.mono Set.inter_subset_left
  have hOldS (y : X) (hy : y ∈ Z) : c (oldBase y) ∈ S := by
    refine ⟨⟨c.map_source hy.2.1.1, ?_⟩, ?_⟩
    · change c.symm (c (oldBase y)) ∈ e.baseSet
      simpa only [c.left_inv hy.2.1.1] using hy.2.1.2
    · change c.symm (c (oldBase y)) ∈ f.baseSet
      simpa only [c.left_inv hy.2.1.1] using hy.2.2
  have hZt : Z ⊆ t.target := by
    intro y hy
    exact ⟨⟨⟨hy.1.1.1, Set.mem_univ _⟩, hy.2.1.1⟩, hOldS y hy⟩
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  -- Assemble the two original moving-frame maps; their columns are smooth by hσ and hτ.
  let A : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    fun y ↦ (f'.continuousLinearMapAt ℂ (g • oldBase y)).comp
      ((τ.linearMap g (oldBase y)).toContinuousLinearMap.comp (f.symmL ℂ (oldBase y)))
  let B : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    fun y ↦ (e.continuousLinearMapAt ℂ (g⁻¹ • d.symm y)).comp
      ((σ.linearMap g⁻¹ (d.symm y)).toContinuousLinearMap.comp (e'.symmL ℂ (d.symm y)))
  have hA : ContDiffOn ℝ ∞ A Z := contDiffOn_equivariantFrameMap IG τ hτ
    g f f' Z oldBase (hOld.mono Set.inter_subset_left)
    (fun y hy ↦ hy.2.2) (fun y hy ↦ by
      change g • (g⁻¹ • d.symm y) ∈ f'.baseSet
      rw [smul_inv_smul]
      exact hy.1.2)
  have hB : ContDiffOn ℝ ∞ B Z := contDiffOn_equivariantFrameMap IG σ hσ
    g⁻¹ e' e Z d.symm (hdU.mono Set.inter_subset_left)
    (fun y hy ↦ hy.1.1.2) (fun y hy ↦ hy.2.1.2)
  refine ⟨c, e, f, inferInstance, inferInstance, hc, Z, t, A, B,
    hZ, hzZ, Set.inter_subset_left, hZt, Set.inter_subset_right, ht, hts, hA, hB, ?_⟩
  intro p y hy η
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


include hG hM hE hF hσ hτ in
set_option linter.unusedSectionVars false in
/-- Smooth geometric transport preserves every symbol order and the original group laws. -/
theorem equivariantGlobalSymbolAction_properties :
    (∀ (m : ℝ) (g : G) (p : GlobalSymbolFunction (n := n) E F),
      IsGlobalSymbol (n := n) (r := r) (q := q) E F m p →
        IsGlobalSymbol (n := n) (r := r) (q := q) E F m
          (equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ g p)) ∧
      equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ 1 = LinearMap.id ∧
      ∀ g h : G, equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ (g * h) =
        (equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ g).comp
          (equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ h) := by
  /- Stage 1: fix g and use original frames near x and g⁻¹*x. The formula
  is multiplication by the two smooth action matrices, together with the
  cotangent substitution ξ ↦ ξ∘d(g) at g⁻¹*x. The latter is fiberwise
  invertible, with inverse given by d(g⁻¹). On compact coordinate subsets
  these matrices, their inverse-frequency matrices, and their derivatives
  are bounded. Each base derivative of the frequency substitution contributes
  one ξ factor and one frequency derivative, preserving the same S^m order.
  A finite cover of each compact coordinate subset supplies the global estimate.
  Stage 2: the cotangent chain rule and the original fiber action equations
  identify transport by g*h with transport first by h and then by g. At the
  identity their original maps are identities. Equality induction eliminates
  only the actual dependent base-index transports; no new identification of
  fibers is chosen. Rank-zero fibers and a zero-dimensional base remain valid.
  The construction uses no invariant norm, group compactness or Haar measure. -/
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : MulAction G (TotalSpace Unit F) := τ.toMulAction
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let T := equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ
  let eval (p : GlobalSymbolFunction (n := n) E F) (x : M)
      (ξ : CotangentFiber (n := n) x) (v : E x) : TotalSpace Unit F :=
    ⟨x, p x ξ v⟩
  have heval (p : GlobalSymbolFunction (n := n) E F) {x y : M}
      (ξ : CotangentFiber (n := n) x) (η : CotangentFiber (n := n) y)
      (v : E x) (w : E y)
      (hξ : (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) = ⟨y, η⟩)
      (hv : (⟨x, v⟩ : TotalSpace Unit E) = ⟨y, w⟩) :
      eval p x ξ v = eval p y η w := by
    have hxy : x = y := congrArg TotalSpace.proj hξ
    subst y
    have hξη := TotalSpace.mk_injective (F := CotangentModel n) x hξ
    have hvw := TotalSpace.mk_injective (F := Unit) x hv
    rw [hξη, hvw]
  have hinverse (g : G) :
      (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm =
        Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g⁻¹ := by
    apply Diffeomorph.ext
    intro x
    rfl
  have htotal (g : G) (p : GlobalSymbolFunction (n := n) E F) (x : M)
      (ξ : CotangentFiber (n := n) x) (v : E x) :
      eval (T g p) x ξ v =
        g • eval p (g⁻¹ • x)
          ((g⁻¹ • (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M))).snd)
          (σ.linearMap g⁻¹ x v) := by
    let (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let (x : M) : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
      subst y
      exact ContinuousLinearMap.id ℂ (F x)
    have ht {x y : M} (h : x = y) (w : F x) :
        (⟨y, transport h w⟩ : TotalSpace Unit F) = ⟨x, w⟩ := by
      subst y
      rfl
    change (⟨x, transport (smul_inv_smul g x)
      (τ.linearMap g (g⁻¹ • x) (p (g⁻¹ • x)
        ((cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm
            ⟨x, ξ⟩).snd) (σ.linearMap g⁻¹ x v)))⟩ : TotalSpace Unit F) = _
    rw [hinverse]
    exact ht (smul_inv_smul g x) _
  refine ⟨?_, ?_, ?_⟩
  · -- Local coordinates retain the exact cotangent substitution and moving-frame maps.
    intro m g p hp d hd e' f' _ _
    let X := EuclideanSpace ℝ (Fin n)
    let U := symbolChartDomain E F d e' f'
    have hU : IsOpen U := isOpen_symbolChartDomain E F d e' f'
    have congrSymbol {W : Set X} (hW : IsOpen W) (a b : SymbolFunction n r q)
        (ha : IsSymbol W m a) (hab : ∀ x ∈ W, ∀ ξ, a x ξ = b x ξ) :
        IsSymbol W m b := by
      refine ⟨ha.1.congr (fun z hz ↦ (hab z.1 hz.1 z.2).symm), ?_⟩
      intro C hCW hC i j
      obtain ⟨B, hB, hbound⟩ := ha.2 C hCW hC i j
      refine ⟨B, hB, ?_⟩
      intro x hx ξ
      have hnear : (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) =ᶠ[nhds x]
          (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) := by
        filter_upwards [hW.mem_nhds (hCW hx)] with y hy
        rw [funext (hab y hy)]
      have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
      change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
      rw [← hder]
      exact hbound x hx ξ
    apply IsSymbol.of_locally hU
    intro z hz
    obtain ⟨c, e, f, he, hf, hc, Z, t, A, B, hZ, hzZ, hZU, hZt, htS,
      ht, hts, hA, hB, hformula⟩ :=
      exists_local_equivariantGlobalSymbolInChart IG σ τ hσ hτ g d hd e' f' z hz
    let := he
    let := hf
    have hpt : IsSymbol Z m
        (cotangentSymbol t (globalSymbolInChart E F p c e f)) :=
      (isSymbol_cotangentSymbol t ht hts m _ ((hp c hc e f).restrict htS)).restrict hZt
    exact ⟨Z, hZ, hzZ, hZU,
      congrSymbol hZ _ _ (isSymbol_matrixSymbol Z hZ m _ hpt A B hA hB)
        (fun y hy η ↦ (hformula p y hy η).symm)⟩
  · -- The same identity acts on the covector, the input vector and the output vector.
    apply LinearMap.ext
    intro p
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    apply TotalSpace.mk_injective (F := Unit) x
    change eval (T 1 p) x ξ v = eval p x ξ v
    rw [htotal, one_smul]
    apply heval
    · change (1 : G)⁻¹ • (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) = _
      rw [inv_one, one_smul]
    · change (1 : G)⁻¹ • (⟨x, v⟩ : TotalSpace Unit E) = _
      rw [inv_one, one_smul]
  · -- Both actions use h⁻¹(g⁻¹x), with the same transported covector and input vector.
    intro g h
    apply LinearMap.ext
    intro p
    funext x ξ
    apply ContinuousLinearMap.ext
    intro v
    apply TotalSpace.mk_injective (F := Unit) x
    change eval (T (g * h) p) x ξ v = eval (T g (T h p)) x ξ v
    rw [htotal, htotal]
    erw [htotal]
    rw [mul_smul]
    apply congrArg (fun w : TotalSpace Unit F ↦ g • h • w)
    apply heval
    · exact (show (g * h)⁻¹ • (⟨x, ξ⟩ : CotangentTotalSpace (n := n) (M := M)) =
        h⁻¹ • g⁻¹ • ⟨x, ξ⟩ by rw [mul_inv_rev, mul_smul])
    · exact (show (g * h)⁻¹ • (⟨x, v⟩ : TotalSpace Unit E) =
        h⁻¹ • g⁻¹ • ⟨x, v⟩ by rw [mul_inv_rev, mul_smul])

/-- Restrict geometric symbol transport to the original space of order-m symbols. -/
def equivariantGlobalSymbolRepresentation (m : ℝ) :
    Representation ℂ G (globalSymbolSpace (n := n) (r := r) (q := q) E F m) := by
  let h := equivariantGlobalSymbolAction_properties (n := n) (r := r) (q := q) IG σ τ hσ hτ
  exact
    { toFun := fun g ↦
        { toFun := fun p ↦
            ⟨equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ g p.val,
              h.1 m g p.val p.property⟩
          map_add' := fun p p' ↦ Subtype.ext
            ((equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ g).map_add
              p.val p'.val)
          map_smul' := fun c p ↦ Subtype.ext
            ((equivariantGlobalSymbolLinearMap (n := n) (r := r) (q := q) IG σ τ g).map_smul
              c p.val) }
      map_one' := by
        apply LinearMap.ext
        intro p
        apply Subtype.ext
        exact congrArg (fun T ↦ T p.val) h.2.1
      map_mul' := by
        intro g k
        apply LinearMap.ext
        intro p
        apply Subtype.ext
        exact congrArg (fun T ↦ T p.val) (h.2.2 g k) }

/-- Descend the same action to the existing S^m/S^(m-1) principal-symbol quotient. -/
def equivariantPrincipalSymbolRepresentation (m : ℝ) :
    Representation ℂ G (GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :=
  (equivariantGlobalSymbolRepresentation (n := n) (r := r) (q := q) IG σ τ hσ hτ m).quotient
    (lowerOrderGlobalSymbols (n := n) (r := r) (q := q) E F m) (by
      intro g p hp
      exact (equivariantGlobalSymbolAction_properties (n := n) (r := r) (q := q) IG σ τ hσ hτ).1
        (m - 1) g p.val hp)

/-- The canonical quotient map intertwines the specified geometric symbol actions. -/
theorem equivariantPrincipalSymbolRepresentation_class (m : ℝ) (g : G)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    equivariantPrincipalSymbolRepresentation (n := n) (r := r) (q := q) IG σ τ hσ hτ m g
        (globalPrincipalSymbolClass E F m p) =
      globalPrincipalSymbolClass E F m
        (equivariantGlobalSymbolRepresentation (n := n) (r := r) (q := q) IG σ τ hσ hτ m g p) := by
  /- The displayed quotient is the original quotient by S^(m-1).
  Its action was defined by mapping the original order-m representative and
  then taking its class. Preservation of order m-1 makes the map independent
  of the representative. This is the native quotient map's defining equation,
  without any homogeneous-symbol choice or symbol surjectivity hypothesis. -/
  rfl

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {μ : Measure M}
  [IsSmoothPositiveMeasure (n := n) μ]

omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 2000000 in
-- The coordinate, frame, and cotangent comparisons use one shared exact local witness.
/-- The same local covariance witnesses the exact conjugated action and its leading class. -/
private theorem PseudodifferentialPiece.exists_localized_conjugate_symbol {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) (g : G)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (hbase : (fun x : M ↦ g • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
      c.source ∩ A.frame.baseSet ∩ B.frame.baseSet)
    (hone : c '' ((fun x : M ↦ g • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff))) ⊆
      interior {z | A.cutoff z = 1})
    (hoverlap : tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) :
    letI := A.frame_mem_atlas
    letI := B.frame_mem_atlas
    ∃ (p : SymbolFunction n r q)
        (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q))),
      IsSymbol Set.univ m p ∧
      (∀ u z, T u z = quantize p u z) ∧
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) z,
        T u z = B.localize hc (τ.smoothSectionRepresentation IG hτ g
          (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)))) z) ∧
      HasOperatorSupport (c '' ((fun x : M ↦ g • x) ''
        (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)))) T ∧
      IsSymbol (symbolChartDomain E F c A.frame B.frame ∩ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
        (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) (m - 1)
        (p - globalSymbolInChart E F
          (equivariantGlobalSymbolLinearMap IG σ τ g L.globalSymbolFunction)
            c A.frame B.frame) := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let eG := Diffeomorph.smul (M := M) IG I ∞ g
  let D := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  let V := symbolChartDomain E F c A.frame B.frame ∩ (fun z ↦ g⁻¹ • c.symm z) ⁻¹' D
  have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  have hcD : ContMDiffOn I I ∞ c.symm (symbolChartDomain E F c A.frame B.frame) := by
    intro z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1.1).contMDiffWithinAt
  have hmoveD := eG.symm.contMDiff.comp_contMDiffOn hcD
  have hV : IsOpen V := hmoveD.continuousOn.isOpen_inter_preimage
    (isOpen_symbolChartDomain E F c A.frame B.frame)
    ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hAV : tsupport A.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap hz⟩
  let K := tsupport L.output.cutoff ∪ tsupport L.input.cutoff
  have hK : IsCompact K := L.output.compact_support.union L.input.compact_support
  have hKD : L.chart.symm '' K ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact ⟨⟨L.chart.map_target (L.output.support_subset hz).1,
        L.output_support_in_input_frame hz⟩, (L.output.support_subset hz).2⟩
    · exact ⟨⟨L.chart.map_target (L.input.support_subset hz).1,
        (L.input.support_subset hz).2⟩, L.input_support_in_output_frame hz⟩
  let t : OpenPartialHomeomorph X X :=
    L.chart.symm.trans (eG.toHomeomorph.toOpenPartialHomeomorph.trans c)
  have ht : ContDiffOn ℝ ∞ t t.source := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1
    have hmove := eG.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hcM hy.2.2).comp y hmove).contDiffAt.contDiffWithinAt
  have hts : ContDiffOn ℝ ∞ t.symm t.target := by
    intro y hy
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1
    have hmove := eG.symm.contMDiffAt.comp y hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y hmove).contDiffAt.contDiffWithinAt
  have hKt : K ⊆ t.source := by
    intro z hz
    have hb := hbase ⟨L.chart.symm z, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨?_, Set.mem_univ _, hb.1.1⟩
    rcases hz with hz | hz
    · exact (L.output.support_subset hz).1
    · exact (L.input.support_subset hz).1
  have hVt : V ⊆ t.target := fun z hz ↦
    ⟨⟨hz.1.1.1, Set.mem_univ _⟩, hz.2.1.1⟩
  have htarget : IsCompact (t '' K) := hK.image_of_continuousOn (t.continuousOn.mono hKt)
  have htargetOne : t '' K ⊆ interior {z | A.cutoff z = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hone ⟨g • L.chart.symm z, ⟨L.chart.symm z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
  -- Choose the auxiliary source cutoff to be one on a whole neighborhood of the support.
  obtain ⟨O, hOo, hKO, hOt, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK t.open_source hKt
  obtain ⟨O', hO'o, hOO', hO't, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc t.open_source hOt
  obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hχsupport : tsupport χ = closure O' := congrArg closure hsχ
  have hcχ : HasCompactSupport χ := by simpa [HasCompactSupport, hχsupport] using hO'c
  have hχt : tsupport χ ⊆ t.source := by rwa [hχsupport]
  have hχone : K ⊆ interior {z | χ z = 1} := by
    intro z hz
    apply mem_interior.mpr
    refine ⟨O, ?_, hOo, hKO hz⟩
    intro w hw
    exact (honeχ w).mp (subset_closure hw)
  let p₀ := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp₀ : IsSymbol univ m p₀ := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff L.output.compact_support L.input.compact_support
  have hP₀ : ∀ u z, L.coordinateOperator u z = quantize p₀ u z :=
    L.coordinateOperator_eq_quantize
  let P := coordinatePushforward t ht hts χ A.cutoff hχ hcχ hχt
    A.smooth_cutoff A.compact_support (hAV.trans hVt) L.coordinateOperator
  obtain ⟨s, hs, hPs, hrem⟩ := exists_symbol_coordinatePushforward t ht hts χ A.cutoff
    hχ hcχ hχt A.smooth_cutoff A.compact_support (hAV.trans hVt) m p₀ hp₀
    L.coordinateOperator hP₀ K hK hKt L.hasOperatorSupport_coordinateOperator
    hχone htargetOne
  have hPK : HasOperatorSupport (t '' K) P := hasOperatorSupport_coordinatePushforward
    t ht hts χ A.cutoff hχ hcχ hχt A.smooth_cutoff A.compact_support (hAV.trans hVt)
    L.coordinateOperator K hK hKt L.hasOperatorSupport_coordinateOperator
  let CE (x : M) : E x ≃ₗ[ℂ] E (g⁻¹ • x) :=
    LinearEquiv.ofBijective (σ.linearMap g⁻¹ x) (σ.linearMap_bijective g⁻¹ x)
  let CF (x : M) : F x ≃ₗ[ℂ] F (g⁻¹ • x) :=
    LinearEquiv.ofBijective (τ.linearMap g⁻¹ x) (τ.linearMap_bijective g⁻¹ x)
  let FE (z : X) (hz : z ∈ V) :
      EuclideanSpace ℂ (Fin r) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r) :=
    (((A.frame.linearEquivAt ℂ (c.symm z) hz.1.1.2).symm.trans (CE (c.symm z))).trans
      (L.input.frame.linearEquivAt ℂ (g⁻¹ • c.symm z) hz.2.1.2))
  let FF (z : X) (hz : z ∈ V) :
      EuclideanSpace ℂ (Fin q) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
    (((B.frame.linearEquivAt ℂ (c.symm z) hz.1.2).symm.trans (CF (c.symm z))).trans
      (L.output.frame.linearEquivAt ℂ (g⁻¹ • c.symm z) hz.2.2))
  let Fout (z : X) : EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q) :=
    if hz : z ∈ V then (FF z hz).symm.toContinuousLinearEquiv else ContinuousLinearEquiv.refl ℂ _
  let Finp (z : X) : EuclideanSpace ℂ (Fin r) ≃L[ℂ] EuclideanSpace ℂ (Fin r) :=
    if hz : z ∈ V then (FE z hz).symm.toContinuousLinearEquiv else ContinuousLinearEquiv.refl ℂ _
  let RA (z : X) := (L.output.frame.continuousLinearMapAt ℂ (g⁻¹ • c.symm z)).comp
    ((τ.linearMap g⁻¹ (c.symm z)).toContinuousLinearMap.comp (B.frame.symmL ℂ (c.symm z)))
  let RB (z : X) := (L.input.frame.continuousLinearMapAt ℂ (g⁻¹ • c.symm z)).comp
    ((σ.linearMap g⁻¹ (c.symm z)).toContinuousLinearMap.comp (A.frame.symmL ℂ (c.symm z)))
  have hcV : ContMDiffOn I I ∞ c.symm V := hcD.mono Set.inter_subset_left
  have hRA : ContDiffOn ℝ ∞ RA V := contDiffOn_equivariantFrameMap IG τ hτ
    g⁻¹ B.frame L.output.frame V c.symm hcV
    (fun z hz ↦ hz.1.2) (fun z hz ↦ hz.2.2)
  have hRB : ContDiffOn ℝ ∞ RB V := contDiffOn_equivariantFrameMap IG σ hσ
    g⁻¹ A.frame L.input.frame V c.symm hcV
    (fun z hz ↦ hz.1.1.2) (fun z hz ↦ hz.2.1.2)
  have hFF (z : X) (hz : z ∈ V) : (FF z hz).toContinuousLinearEquiv.toContinuousLinearMap =
      RA z := by
    ext w
    simp [FF, CF, RA, ContinuousLinearMap.comp_apply,
      B.frame.symmL_apply hz.1.2,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply,
      L.output.frame.continuousLinearMapAt_apply_of_mem ℂ hz.2.2]
  have hFout : ContDiffOn ℝ ∞ (fun z ↦ (Fout z).toContinuousLinearMap) V := by
    intro z hz
    have hi := (contDiffAt_map_inverse (n := ∞)
      (FF z hz).toContinuousLinearEquiv).restrict_scalars ℝ
    rw [hFF z hz] at hi
    have hsmooth := hi.comp z (hRA.contDiffAt (hV.mem_nhds hz))
    apply (hsmooth.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hV.mem_nhds hz] with y hy
    change (Fout y).toContinuousLinearMap = (RA y).inverse
    rw [← hFF y hy, ContinuousLinearMap.inverse_equiv]
    simp only [Fout, dite_eq_left hy]
    rfl
  have hFinp : ContDiffOn ℝ ∞ (fun z ↦ (Finp z).symm.toContinuousLinearMap) V := by
    apply hRB.congr
    intro z hz
    ext w
    simp [Finp, dite_eq_left hz, FE, CE, RB, ContinuousLinearMap.comp_apply,
      A.frame.symmL_apply hz.1.1.2,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply,
      L.input.frame.continuousLinearMapAt_apply_of_mem ℂ hz.2.1.2]
  let p := frameChangeSymbol Fout Finp A.cutoff s
  have hp : IsSymbol univ m p := isSymbol_frameChangeSymbol V hV Fout Finp hFout hFinp
    A.cutoff A.smooth_cutoff A.compact_support hAV m s hs
  let Tin := matrixMultiplierCLM (cutoffMatrix A.cutoff
    (fun z ↦ (Finp z).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix V hV _ hFinp A.cutoff A.smooth_cutoff hAV)
    (hasCompactSupport_cutoffMatrix A.cutoff _ A.compact_support)
  have hTin (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      Tin u z = A.cutoff z • (Finp z).symm (u z) := by
    rw [matrixMultiplierCLM_apply]
    rfl
  have hinputFrame (u : smoothSections (n := n) (r := r) E) (z : X) (hz : z ∈ V) :
      (Finp z).symm ((A.frame ⟨c.symm z, u.val (c.symm z)⟩).2) =
        (L.input.frame ⟨g⁻¹ • c.symm z,
          (σ.smoothSectionRepresentation IG hσ g⁻¹ u).val (g⁻¹ • c.symm z)⟩).2 := by
    change _ = (L.input.frame ⟨g⁻¹ • c.symm z,
      σ.sectionLinearMap g⁻¹ u.val (g⁻¹ • c.symm z)⟩).2
    rw [σ.sectionLinearMap_smul]
    simp [Finp, dite_eq_left hz, FE, CE,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply, A.frame.symm_apply_apply_mk hz.1.1.2]
  have houtputFrame (u : smoothSections (n := n) (r := q) F) (z : X) (hz : z ∈ V) :
      (Fout z) ((L.output.frame ⟨g⁻¹ • c.symm z, u.val (g⁻¹ • c.symm z)⟩).2) =
        (B.frame ⟨c.symm z, (τ.smoothSectionRepresentation IG hτ g u).val (c.symm z)⟩).2 := by
    let ρ := τ.smoothSectionRepresentation IG hτ
    have hcancel : ρ g⁻¹ (ρ g u) = u := by
      change (ρ g⁻¹ * ρ g) u = u
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    have hcancelAt := congrArg (fun v : smoothSections (n := n) (r := q) F ↦
      v.val (g⁻¹ • c.symm z)) hcancel
    change τ.sectionLinearMap g⁻¹ (ρ g u).val (g⁻¹ • c.symm z) = _ at hcancelAt
    rw [τ.sectionLinearMap_smul] at hcancelAt
    have hCF : (CF (c.symm z)).symm (u.val (g⁻¹ • c.symm z)) = (ρ g u).val (c.symm z) := by
      apply (CF (c.symm z)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact hcancelAt.symm
    simpa [Fout, dite_eq_left hz, FF,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply,
      L.output.frame.symm_apply_apply_mk hz.2.2] using
        congrArg (fun v : F (c.symm z) ↦ (B.frame ⟨c.symm z, v⟩).2) hCF
  -- Compare the same localized input after the coordinate and fiber changes.
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun w ↦ (L.input.cutoff w : ℂ))
          (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) =
        L.input.localize L.chart_mem_atlas
          (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)) := by
    apply SchwartzMap.ext
    intro w
    have hgrowth : (fun w ↦ (L.input.cutoff w : ℂ)).HasTemperateGrowth :=
      (L.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth, cutoffPullbackCLM_apply, hTin]
    by_cases hw : w ∈ tsupport L.input.cutoff
    · have hwK : w ∈ K := Or.inr hw
      have hwt := hKt hwK
      have hb := hbase ⟨L.chart.symm w, ⟨w, hwK, rfl⟩, rfl⟩
      have hχw : χ w = 1 := interior_subset (s := {z : X | χ z = 1}) (hχone hwK)
      have hcw : c.symm (t w) = g • L.chart.symm w := c.left_inv hb.1.1
      have hOld : g⁻¹ • c.symm (t w) = L.chart.symm w := by
        rw [hcw, inv_smul_smul]
      have hwV : t w ∈ V := by
        refine ⟨⟨⟨(t.map_source hwt).1.1, ?_⟩, ?_⟩, ?_⟩
        · change c.symm (t w) ∈ A.frame.baseSet
          rw [hcw]
          exact hb.1.2
        · change c.symm (t w) ∈ B.frame.baseSet
          rw [hcw]
          exact hb.2
        · change g⁻¹ • c.symm (t w) ∈ D
          rw [hOld]
          exact hKD ⟨w, hwK, rfl⟩
      have hframes := hinputFrame (A.extend hc u) (t w) hwV
      have hframeExt : (A.frame ⟨c.symm (t w), (A.extend hc u).val (c.symm (t w))⟩).2 =
          (A.cutoff (t w) : ℂ) • u (t w) := by
        change (A.frame ⟨c.symm (t w), A.extendedFunction u (c.symm (t w))⟩).2 = _
        rw [BundleChartCutoff.extendedFunction,
          ite_eq_left (c.map_target hwV.1.1.1), c.right_inv hwV.1.1.1]
        change (A.frame.linearEquivAt ℂ _ hwV.1.1.2)
          ((A.cutoff (t w) : ℂ) • A.frame.symmL ℂ (c.symm (t w)) (u (t w))) = _
        rw [map_smul, A.frame.symmL_apply hwV.1.1.2]
        change (A.cutoff (t w) : ℂ) • (A.frame.linearEquivAt ℂ _ hwV.1.1.2)
          ((A.frame.linearEquivAt ℂ _ hwV.1.1.2).symm (u (t w))) = _
        rw [LinearEquiv.apply_symm_apply]
      rw [hframeExt, map_smul, hOld] at hframes
      change (L.input.cutoff w : ℂ) •
          (χ w • (A.cutoff (t w) • (Finp (t w)).symm (u (t w)))) =
        L.input.localizedFunction
          (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)) w
      rw [hχw, one_smul]
      have hwTarget : w ∈ L.chart.target := hwt.1
      simp only [BundleChartCutoff.localizedFunction, sectionInChart]
      rw [ite_eq_left hwTarget]
      rw [← hframes]
      simp only [Complex.coe_smul]
    · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
        image_eq_zero_of_notMem_tsupport hw]
  have happly : ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) z,
      quantize p u z = B.localize hc (τ.smoothSectionRepresentation IG hτ g
        (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)))) z := by
    intro u z
    rw [show quantize p u z = frameChangeOperator V hV Fout Finp hFout hFinp
      A.cutoff A.smooth_cutoff A.compact_support hAV P u z from
        quantize_frameChangeSymbol V hV Fout Finp hFout hFinp A.cutoff
          A.smooth_cutoff A.compact_support hAV P m s hs hPs u z]
    change matrixMultiplierCLM _ _ _ (P (Tin u)) z = _
    rw [matrixMultiplierCLM_apply]
    by_cases hz : z ∈ tsupport A.cutoff
    · have hzV := hAV hz
      have hzt := hVt hzV
      rw [show P (Tin u) z = L.coordinateOperator
        (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) (t.symm z) from
          coordinatePushforward_apply t ht hts χ A.cutoff hχ hcχ hχt
            A.smooth_cutoff A.compact_support (hAV.trans hVt) L.coordinateOperator K hKt
            L.hasOperatorSupport_coordinateOperator
            (fun w hw ↦ interior_subset (s := {z : X | A.cutoff z = 1}) (htargetOne hw))
            (Tin u) z hzt]
      rw [L.coordinateOperator_apply, hinput, L.operator_apply]
      have hf := houtputFrame
        (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u))) z hzV
      rw [L.toLinearMap_in_frame _ _ hzV.2.1.1 hzV.2.2] at hf
      change A.cutoff z • (Fout z)
        (L.output.cutoff (L.chart (g⁻¹ • c.symm z)) •
          quantize L.symbol _ (L.chart (g⁻¹ • c.symm z))) = _
      change _ = B.localizedFunction (τ.smoothSectionRepresentation IG hτ g
        (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ (A.extend hc u)))) z
      have hzTarget : z ∈ c.target := hzV.1.1.1
      simp only [BundleChartCutoff.localizedFunction, sectionInChart]
      rw [ite_eq_left hzTarget, ← hf, ← hAB]
      simp only [Complex.coe_smul]
    · have hAz : A.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hBz : B.cutoff z = 0 := by rwa [← hAB]
      simp [cutoffMatrix, BundleChartCutoff.localize, BundleChartCutoff.localizedFunction, hAz, hBz]
  -- Coordinate change, frame change, and cutoff reduction each contribute one lower order.
  let pdiag : SymbolFunction n r q := fun z ξ ↦
    ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) • L.symbol z ξ
  have hdiag : IsSymbol univ (m - 1) (p₀ - pdiag) := by
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero,
      cutoffAmplitude, p₀, pdiag, Complex.coe_smul] using h
  have h₁ : IsSymbol V (m - 1) (p - frameSymbol Fout Finp s) :=
    isSymbol_frameChangeSymbol_sub V hV Fout Finp hFout hFinp A.cutoff
      A.smooth_cutoff A.compact_support hAV P m s hs hPs (t '' K) htarget.isClosed
      hPK htargetOne
  have h₂ := isSymbol_frameSymbol V hV Fout Finp hFout hFinp (m - 1)
    (s - cotangentSymbol t p₀) (hrem.restrict hVt)
  have h₃ := isSymbol_frameSymbol V hV Fout Finp hFout hFinp (m - 1)
    (cotangentSymbol t (p₀ - pdiag))
      ((isSymbol_cotangentSymbol t ht hts (m - 1) (p₀ - pdiag)
        (hdiag.restrict (Set.subset_univ _))).restrict hVt)
  have htotal : IsSymbol V (m - 1)
      (p - frameSymbol Fout Finp (cotangentSymbol t pdiag)) := by
    convert IsSymbol.add hV (IsSymbol.add hV h₁ h₂) h₃ using 1
    ext z ξ v
    simp only [Pi.add_apply, Pi.sub_apply, frameSymbol, matrixSymbol, cotangentSymbol,
      add_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel_nf
  have hsame (y : X) (hy : y ∈ V) (η : X) :
      frameSymbol Fout Finp (cotangentSymbol t pdiag) y η =
        globalSymbolInChart E F
          (equivariantGlobalSymbolLinearMap IG σ τ g L.globalSymbolFunction)
            c A.frame B.frame y η := by
    let oldBase := g⁻¹ • c.symm y
    let ξ := covectorFromChart c (c.symm y) η
    let ζ := (cotangentDiffeomorphMap eG.symm ⟨c.symm y, ξ⟩).snd
    have hreturn : eG oldBase = c.symm y := smul_inv_smul g (c.symm y)
    have hcOld : L.chart.symm (L.chart oldBase) = oldBase := L.chart.left_inv hy.2.1.1
    -- The very coordinate diffeomorphism used in quantization gives the cotangent action.
    have hfreq : covectorInChart L.chart oldBase ζ =
        (fderiv ℝ t (t.symm y)).adjoint η := by
      have hcs := (contMDiffAt_symm_of_mem_maximalAtlas hdM
        (L.chart.map_source hy.2.1.1)).mdifferentiableAt (by simp)
      have hmove := mfderiv_comp (L.chart oldBase)
        (eG.mdifferentiable (by simp) (L.chart.symm (L.chart oldBase))) hcs
      have htarget := (contMDiffAt_of_mem_maximalAtlas hcM
        (c.map_target hy.1.1.1)).mdifferentiableAt (by simp)
      have htarget' : MDifferentiableAt I I c (eG (L.chart.symm (L.chart oldBase))) := by
        simpa only [hcOld, hreturn] using htarget
      have hchain := mfderiv_comp (L.chart oldBase) htarget'
        ((eG.mdifferentiable (by simp) _).comp _ hcs)
      rw [hmove, hcOld, hreturn] at hchain
      have htcomp : fderiv ℝ t (t.symm y) =
          (mfderiv I I c (c.symm y)).comp
            ((mfderiv I I eG oldBase).comp
              (mfderiv I I L.chart.symm (L.chart oldBase))) := by
        rw [mfderiv_eq_fderiv] at hchain
        dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel,
          Function.comp_apply] at hchain
        rw [hcOld, hreturn] at hchain
        exact hchain
      ext a
      change inner ℝ η ((mfderiv I I c (c.symm y))
        ((mfderiv I I eG oldBase)
          ((mfderiv I I L.chart.symm (L.chart oldBase))
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
    have hOldDomain : L.chart oldBase ∈
        symbolChartDomain E F L.chart L.input.frame L.output.frame := by
      refine ⟨⟨L.chart.map_source hy.2.1.1, ?_⟩, ?_⟩
      · change L.chart.symm (L.chart oldBase) ∈ L.input.frame.baseSet
        rw [hcOld]
        exact hy.2.1.2
      · change L.chart.symm (L.chart oldBase) ∈ L.output.frame.baseSet
        rw [hcOld]
        exact hy.2.2
    have hpcoord := globalSymbolInChart_covectorInChart E F L.globalSymbolFunction
      L.chart L.chart_mem_atlas L.input.frame L.output.frame oldBase hy.2.1.1 ζ
    rw [hfreq] at hpcoord
    have hdiagCoord := L.globalSymbolInChart_globalSymbolFunction
      (L.chart oldBase) ((fderiv ℝ t (t.symm y)).adjoint η) hOldDomain
    have hactual (v : E (c.symm y)) :
        (CF (c.symm y)).symm
          (L.globalSymbolFunction oldBase ζ (σ.linearMap g⁻¹ (c.symm y) v)) =
          equivariantGlobalSymbolLinearMap IG σ τ g L.globalSymbolFunction (c.symm y) ξ v := by
      let : MulAction G (TotalSpace Unit F) := τ.toMulAction
      apply (CF (c.symm y)).injective
      rw [LinearEquiv.apply_symm_apply]
      have hvector : (⟨c.symm y,
          equivariantGlobalSymbolLinearMap IG σ τ g L.globalSymbolFunction (c.symm y) ξ v⟩ :
            TotalSpace Unit F) =
          g • ⟨oldBase, L.globalSymbolFunction oldBase ζ (σ.linearMap g⁻¹ (c.symm y) v)⟩ := by
        let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
          subst y
          exact ContinuousLinearMap.id ℂ (F x)
        have ht {x y : M} (h : x = y) (w : F x) :
            (⟨y, transport h w⟩ : TotalSpace Unit F) = ⟨x, w⟩ := by
          subst y
          rfl
        change (⟨c.symm y, transport (smul_inv_smul g (c.symm y)) _⟩ :
          TotalSpace Unit F) = _
        exact ht (smul_inv_smul g (c.symm y)) _
      have hcancel := congrArg (fun z : TotalSpace Unit F ↦ g⁻¹ • z) hvector
      have hcancel' := hcancel.trans (inv_smul_smul g _)
      exact (TotalSpace.mk_injective (F := Unit) oldBase hcancel').symm
    apply ContinuousLinearMap.ext
    intro v
    have hOldOut : oldBase ∈ L.output.frame.baseSet := hy.2.2
    have hOldIn : oldBase ∈ L.input.frame.baseSet := hy.2.1.2
    change (Fout y) (pdiag (L.chart oldBase) ((fderiv ℝ t (t.symm y)).adjoint η)
      ((Finp y).symm v)) = _
    rw [show pdiag (L.chart oldBase) ((fderiv ℝ t (t.symm y)).adjoint η) =
        globalSymbolInChart E F L.globalSymbolFunction L.chart L.input.frame L.output.frame
          (L.chart oldBase) ((fderiv ℝ t (t.symm y)).adjoint η) from hdiagCoord.symm,
      hpcoord]
    simp only [Fout, Finp, dite_eq_left hy]
    change (B.frame.linearEquivAt ℂ (c.symm y) hy.1.2)
      ((CF (c.symm y)).symm ((L.output.frame.linearEquivAt ℂ oldBase hy.2.2).symm
        (L.output.frame.continuousLinearMapAt ℂ oldBase
          (L.globalSymbolFunction oldBase ζ (L.input.frame.symmL ℂ oldBase
            ((L.input.frame.linearEquivAt ℂ oldBase hy.2.1.2)
              (CE (c.symm y) ((A.frame.linearEquivAt ℂ (c.symm y) hy.1.1.2).symm v)))))))) = _
    simpa only [globalSymbolInChart, ContinuousLinearMap.comp_apply, CE,
      LinearEquiv.ofBijective_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply,
      L.output.frame.continuousLinearMapAt_apply_of_mem ℂ hOldOut,
      L.output.frame.symm_apply_apply_mk hOldOut,
      L.input.frame.symmL_apply hOldIn,
      L.input.frame.symm_apply_apply_mk hOldIn,
      B.frame.continuousLinearMapAt_apply_of_mem ℂ hy.1.2,
      A.frame.symmL_apply hy.1.1.2] using
        congrArg (fun w : F (c.symm y) ↦ (B.frame ⟨c.symm y, w⟩).2)
          (hactual (A.frame.symmL ℂ (c.symm y) v))
  let T := frameChangeOperator V hV Fout Finp hFout hFinp
    A.cutoff A.smooth_cutoff A.compact_support hAV P
  have hT (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) : T u z = quantize p u z :=
    (quantize_frameChangeSymbol V hV Fout Finp hFout hFinp A.cutoff
      A.smooth_cutoff A.compact_support hAV P m s hs hPs u z).symm
  have hSupport : HasOperatorSupport (c '' ((fun x : M ↦ g • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)))) T := by
    have htSupport := hasOperatorSupport_frameChangeOperator V hV Fout Finp hFout hFinp
      A.cutoff A.smooth_cutoff A.compact_support hAV P (t '' K) hPK
    have hSet : t '' K = c '' ((fun x : M ↦ g • x) '' (L.chart.symm '' K)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨g • L.chart.symm z, ⟨L.chart.symm z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨w, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rwa [hSet] at htSupport
  refine ⟨p, T, hp, hT, fun u z ↦ (hT u z).trans (happly u z), hSupport, ?_⟩
  refine ⟨htotal.1.congr (fun z hz ↦ ?_), ?_⟩
  · change p z.1 z.2 - _ = p z.1 z.2 - _
    rw [hsame z.1 hz.1 z.2]
  · intro C hCV hC i j
    obtain ⟨R, hR, hbound⟩ := htotal.2 C hCV hC i j
    refine ⟨R, hR, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j
        ((p - frameSymbol Fout Finp (cotangentSymbol t pdiag)) y) ξ) =ᶠ[nhds x]
      (fun y ↦ iteratedFDeriv ℝ j
        ((p - globalSymbolInChart E F
          (equivariantGlobalSymbolLinearMap IG σ τ g L.globalSymbolFunction)
            c A.frame B.frame) y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      congr 1
      funext η
      exact congrArg (fun v ↦ p y η - v) (hsame y hy η)
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ


omit [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 2000000 in
-- The exact cutoff round trips and the global principal comparison share one local operator.
/-- A transported compact piece contained in one original chart has an exact native realization. -/
private theorem PseudodifferentialPiece.exists_conjugate_piece {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) (g : G)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (hbase : (fun x : M ↦ g • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
        c.source ∩ A.frame.baseSet ∩ B.frame.baseSet)
    (hone : c '' ((fun x : M ↦ g • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff))) ⊆
        interior {z | A.cutoff z = 1})
    (hoverlap : tsupport A.cutoff ⊆ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) :
    ∃ Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m,
      Q.toLinearMap = (τ.smoothSectionRepresentation IG hτ g).comp
        (L.toLinearMap.comp (σ.smoothSectionRepresentation IG hσ g⁻¹)) ∧
      globalPrincipalSymbolClass E F m Q.globalSymbol =
        equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ m g
          (globalPrincipalSymbolClass E F m L.globalSymbol) := by
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  obtain ⟨p, T, hp, hTp, hT, hTsupport, hlower⟩ :=
    L.exists_localized_conjugate_symbol IG σ τ hσ hτ g c hc A B hAB hbase hone hoverlap
  let Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { chart := c
      chart_mem_atlas := hc
      input := A
      output := B
      input_support_in_output_frame := fun z hz ↦
        (B.support_subset (by rwa [← hAB])).2
      output_support_in_input_frame := fun z hz ↦
        (A.support_subset (by rwa [hAB])).2
      operator := T
      symbol := p
      isSymbol := hp
      operator_apply := hTp }
  let K := (fun x : M ↦ g • x) ''
    (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff))
  have hK : IsCompact K :=
    ((L.output.compact_support.union L.input.compact_support).image_of_continuousOn
      (L.chart.continuousOn_symm.mono (fun z hz ↦ by
        rcases hz with hz | hz
        · exact (L.output.support_subset hz).1
        · exact (L.input.support_subset hz).1))).image (continuous_const_smul g)
  have hχone (x : M) (hx : x ∈ K) : A.cutoff (c x) = 1 :=
    interior_subset (s := {z | A.cutoff z = 1}) (hone ⟨x, hx, rfl⟩)
  have hinputRoundtrip (u : smoothSections (n := n) (r := r) E)
      (x : M) (hx : x ∈ K) : (A.extend hc (A.localize hc u)).val x = u.val x := by
    have hxc : x ∈ c.source := (hbase hx).1.1
    have hxf : x ∈ A.frame.baseSet := (hbase hx).1.2
    change A.extendedFunction (A.localize hc u) x = _
    simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
    change (A.cutoff (c x) : ℂ) • A.frame.symmL ℂ x (A.localizedFunction u (c x)) = _
    rw [hχone x hx, Complex.ofReal_one, one_smul]
    simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
      sectionInChart]
    rw [c.left_inv hxc, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
    rw [hχone x hx, Complex.ofReal_one, one_smul, A.frame.symmL_continuousLinearMapAt hxf]
  -- Only the original input cutoff support is used to remove the added input round trip.
  have hinput (u : smoothSections (n := n) (r := r) E) :
      L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹
        (A.extend hc (A.localize hc u))) =
      L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ u) := by
    apply L.toLinearMap_eq_of_eq_on_support
    intro x hx
    apply TotalSpace.mk_injective (F := Unit) x
    change (⟨x, σ.sectionLinearMap g⁻¹ (A.extend hc (A.localize hc u)).val x⟩ :
        TotalSpace Unit E) = ⟨x, σ.sectionLinearMap g⁻¹ u.val x⟩
    rw [σ.mk_sectionLinearMap, σ.mk_sectionLinearMap]
    rw [inv_inv]
    rw [hinputRoundtrip u (g • x) ⟨x,
      (Set.image_mono Set.subset_union_right) hx, rfl⟩]
  have houtputSupport (u : smoothSections (n := n) (r := r) E) :
      closure {x | (τ.smoothSectionRepresentation IG hτ g
        (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ u))).val x ≠ 0} ⊆ K := by
    change closure {x | τ.sectionLinearMap g
      (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ u)).val x ≠ 0} ⊆ _
    rw [τ.closure_support_sectionLinearMap]
    apply Set.image_mono
    have hcompact : IsCompact
        (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) :=
      (L.output.compact_support.union L.input.compact_support).image_of_continuousOn
        (L.chart.continuousOn_symm.mono (fun z hz ↦ by
          rcases hz with hz | hz
          · exact (L.output.support_subset hz).1
          · exact (L.input.support_subset hz).1))
    apply closure_minimal _ hcompact.isClosed
    intro x hx
    by_contra h
    exact hx (L.toLinearMap_eq_zero _ x (fun hx ↦ h ((Set.image_mono Set.subset_union_left) hx)))
  have houtput (u : smoothSections (n := n) (r := r) E) :
      B.extend hc (B.localize hc (τ.smoothSectionRepresentation IG hτ g
        (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ u)))) =
      τ.smoothSectionRepresentation IG hτ g
        (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ u)) := by
    let v := τ.smoothSectionRepresentation IG hτ g
      (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹ u))
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ K
    · have hxc : x ∈ c.source := (hbase hx).1.1
      have hxf : x ∈ B.frame.baseSet := (hbase hx).2
      have hχ : B.cutoff (c x) = 1 := by rw [← hAB]; exact hχone x hx
      change B.extendedFunction (B.localize hc v) x = v.val x
      simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
      change (B.cutoff (c x) : ℂ) • B.frame.symmL ℂ x (B.localizedFunction v (c x)) = _
      rw [hχ, Complex.ofReal_one, one_smul]
      simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
        sectionInChart]
      rw [c.left_inv hxc, ← B.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
      rw [hχ, Complex.ofReal_one, one_smul, B.frame.symmL_continuousLinearMapAt hxf]
    · have hz : v.val x = 0 := by
        by_contra hne
        exact hx (houtputSupport u (subset_closure hne))
      change B.extendedFunction (B.localize hc v) x = v.val x
      by_cases hxc : x ∈ c.source
      · simp only [BundleChartCutoff.extendedFunction, hxc, ↓reduceIte]
        change (B.cutoff (c x) : ℂ) • B.frame.symmL ℂ x (B.localizedFunction v (c x)) = _
        simp only [BundleChartCutoff.localizedFunction, c.map_source hxc, ↓reduceIte,
          sectionInChart]
        rw [c.left_inv hxc, hz]
        by_cases hxf : x ∈ B.frame.baseSet
        · rw [show (B.frame ⟨x, (0 : F x)⟩).2 = 0 from (B.frame.linear ℂ hxf).map_zero]
          simp
        · rw [B.frame.symmL_apply_of_notMem (R := ℂ) hxf]
          simp
      · simp [BundleChartCutoff.extendedFunction, hxc, hz]
  have hmap : Q.toLinearMap = (τ.smoothSectionRepresentation IG hτ g).comp
      (L.toLinearMap.comp (σ.smoothSectionRepresentation IG hσ g⁻¹)) := by
    apply LinearMap.ext
    intro u
    have hlocal : T (A.localize hc u) = B.localize hc
        (τ.smoothSectionRepresentation IG hτ g
          (L.toLinearMap (σ.smoothSectionRepresentation IG hσ g⁻¹
            (A.extend hc (A.localize hc u))))) :=
      SchwartzMap.ext (hT (A.localize hc u))
    change B.extend hc (T (A.localize hc u)) = _
    rw [hlocal, hinput]
    exact houtput u
  refine ⟨Q, hmap, ?_⟩
  let a := equivariantGlobalSymbolLinearMap IG σ τ g L.globalSymbolFunction
  let V := symbolChartDomain E F c A.frame B.frame ∩ (fun z ↦ g⁻¹ • c.symm z) ⁻¹'
    (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hV : IsOpen V :=
    ((Homeomorph.smul g⁻¹).continuous.comp_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1))).isOpen_inter_preimage
        (isOpen_symbolChartDomain E F c A.frame B.frame)
        ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hAV : tsupport A.cutoff ⊆ V := fun z hz ↦
    ⟨⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap hz⟩
  -- Realize the local one-order error as a lower-order native piece with the same cutoffs.
  obtain ⟨O, hO, hAO, hOV, hOc⟩ :=
    exists_open_between_and_isCompact_closure A.compact_support hV hAV
  obtain ⟨γ, hγ, _, hsγ, honeγ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO (isClosed_tsupport A.cutoff) hAO
  have hcγ : HasCompactSupport γ := by
    change IsCompact (tsupport γ)
    rw [show tsupport γ = closure O from congrArg closure hsγ]
    exact hOc
  have hγV : tsupport γ ⊆ V := by
    rwa [show tsupport γ = closure O from congrArg closure hsγ]
  let b := zeroExtendedSymbol V γ (p - globalSymbolInChart E F a c A.frame B.frame)
  have hb : IsSymbol Set.univ (m - 1) b :=
    isSymbol_zeroExtendedSymbol V hV (m - 1) γ hγ hcγ hγV _ hlower
  have hbc : HasCompactSupport b := hasCompactSupport_zeroExtendedSymbol V γ _ hcγ
  let R : PseudodifferentialPiece (n := n) (r := r) (q := q) E F (m - 1) :=
    { chart := c
      chart_mem_atlas := hc
      input := A
      output := B
      input_support_in_output_frame := Q.input_support_in_output_frame
      output_support_in_input_frame := Q.output_support_in_input_frame
      operator := quantizeSchwartz (m - 1) b hb hbc
      symbol := b
      isSymbol := hb
      operator_apply := quantizeSchwartz_apply (m - 1) b hb hbc }
  have hzero (x : M) (hx : x ∉ K) (ξ) : a x ξ = 0 := by
    have hOld (ζ) : L.globalSymbolFunction (g⁻¹ • x) ζ = 0 := by
      apply L.globalSymbolFunction_eq_zero
      intro h
      apply hx
      exact ⟨g⁻¹ • x, (Set.image_mono (fun _ hz ↦ Or.inl hz.1)) h, smul_inv_smul g x⟩
    simp only [a, equivariantGlobalSymbolLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    erw [hOld]
    simp
  have hglobalDifference : Q.globalSymbolFunction - a = R.globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ c.symm '' tsupport A.cutoff
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzc : z ∈ c.target := (A.support_subset hz).1
      have hxA : c.symm z ∈ A.frame.baseSet := (A.support_subset hz).2
      have hxB : c.symm z ∈ B.frame.baseSet :=
        (B.support_subset (by rwa [← hAB])).2
      have hcoordDomain : z ∈ symbolChartDomain E F c A.frame B.frame :=
        ⟨⟨hzc, hxA⟩, hxB⟩
      have hscale : ((A.cutoff z * B.cutoff z : ℝ) : ℂ) •
          globalSymbolInChart E F a c A.frame B.frame z
            (covectorInChart c (c.symm z) ξ) =
          globalSymbolInChart E F a c A.frame B.frame z
            (covectorInChart c (c.symm z) ξ) := by
        by_cases hxK : c.symm z ∈ K
        · have hAz : A.cutoff z = 1 := by
            simpa only [c.right_inv hzc] using hχone (c.symm z) hxK
          rw [← hAB, hAz, one_mul, Complex.ofReal_one, one_smul]
        · simp [globalSymbolInChart, hzero (c.symm z) hxK]
      have hcoord :
          globalSymbolInChart E F Q.globalSymbolFunction c A.frame B.frame z
              (covectorInChart c (c.symm z) ξ) -
            globalSymbolInChart E F a c A.frame B.frame z (covectorInChart c (c.symm z) ξ) =
          globalSymbolInChart E F R.globalSymbolFunction c A.frame B.frame z
            (covectorInChart c (c.symm z) ξ) := by
        rw [Q.globalSymbolInChart_globalSymbolFunction _ _ hcoordDomain,
          R.globalSymbolInChart_globalSymbolFunction _ _ hcoordDomain]
        change ((B.cutoff z * A.cutoff z : ℝ) : ℂ) • p z _ -
          globalSymbolInChart E F a c A.frame B.frame z _ =
          ((B.cutoff z * A.cutoff z : ℝ) : ℂ) • b z _
        simp only [b, zeroExtendedSymbol, ite_eq_left (hAV hz), (honeγ z).mp hz,
          Complex.ofReal_one, one_smul, Pi.sub_apply, smul_sub]
        rw [mul_comm (B.cutoff z) (A.cutoff z), hscale]
      have hxc : c.symm z ∈ c.source := c.map_target hzc
      have h₁ := globalSymbolInChart_covectorInChart E F Q.globalSymbolFunction
        c hc A.frame B.frame (c.symm z) hxc ξ
      have h₂ := globalSymbolInChart_covectorInChart E F a c hc A.frame B.frame (c.symm z) hxc ξ
      have h₃ := globalSymbolInChart_covectorInChart E F R.globalSymbolFunction
        c hc A.frame B.frame (c.symm z) hxc ξ
      simp only [c.right_inv hzc] at h₁ h₂ h₃
      rw [h₁, h₂, h₃] at hcoord
      ext v : 1
      have hv := congrArg (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) ↦
        B.frame.symmL ℂ (c.symm z) (T (A.frame.continuousLinearMapAt ℂ (c.symm z) v))) hcoord
      simpa only [Pi.sub_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub,
        A.frame.symmL_continuousLinearMapAt hxA,
        B.frame.symmL_continuousLinearMapAt hxB] using hv
    · have hQzero := Q.globalSymbolFunction_eq_zero x
        (by simpa only [Q, ← hAB, Set.inter_self] using hx) ξ
      have hRzero := R.globalSymbolFunction_eq_zero x
        (by simpa only [R, ← hAB, Set.inter_self] using hx) ξ
      have hxK : x ∉ K := by
        intro hxK
        apply hx
        exact ⟨c x, subset_tsupport _ (by
          change A.cutoff (c x) ≠ 0
          rw [hχone x hxK]
          exact one_ne_zero),
          c.left_inv (hbase hxK).1.1⟩
      simp only [Pi.sub_apply, hQzero, hRzero, hzero x hxK ξ, sub_zero]
  rw [equivariantPrincipalSymbolRepresentation_class]
  apply (globalPrincipalSymbolClass_eq_iff E F m _ _).mpr
  change IsGlobalSymbol E F (m - 1) (Q.globalSymbolFunction - a)
  rw [hglobalDifference]
  exact R.isGlobalSymbol_globalSymbolFunction

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 2000000 in
-- Compact refinement and the principal comparison retain one finite family throughout.
/-- One actual finite representation computes both geometric conjugation and its principal class. -/
theorem PseudodifferentialOperator.exists_representation_conjugate {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) (g : G) :
    ∃ (N : ℕ) (Q : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m),
      IsSmoothingOperator μ ((τ.smoothSectionRepresentation IG hτ g).comp
        (P.toLinearMap.comp (σ.smoothSectionRepresentation IG hσ g⁻¹)) -
          ∑ j, (Q j).toLinearMap) ∧
      globalPrincipalSymbolClass E F m (∑ j, (Q j).globalSymbol) =
        equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ m g P.principalSymbol := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let C : (smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F) →ₗ[ℂ]
      (smoothSections (n := n) (r := r) E →ₗ[ℂ]
        smoothSections (n := n) (r := q) F) :=
    { toFun := fun T ↦ (τ.smoothSectionRepresentation IG hτ g).comp
        (T.comp (σ.smoothSectionRepresentation IG hσ g⁻¹))
      map_add' := fun T S ↦ by simp only [LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun a T ↦ by
        simp only [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply] }
  let ρ := equivariantPrincipalSymbolRepresentation IG σ τ hσ hτ m g
  -- A compact piece whose image fits one original chart admits common target plateaus.
  have hchart (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (c : OpenPartialHomeomorph M X) (hc : c ∈ atlas X M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f]
      (hbase : (fun x : M ↦ g • x) ''
        (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
          c.source ∩ e.baseSet ∩ f.baseSet) :
      ∃ Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m,
        Q.toLinearMap = C L.toLinearMap ∧
        globalPrincipalSymbolClass E F m Q.globalSymbol =
          ρ (globalPrincipalSymbolClass E F m L.globalSymbol) := by
    let K := (fun x : M ↦ g • x) ''
      (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff))
    have hK : IsCompact K :=
      ((L.output.compact_support.union L.input.compact_support).image_of_continuousOn
        (L.chart.continuousOn_symm.mono (fun z hz ↦ by
          rcases hz with hz | hz
          · exact (L.output.support_subset hz).1
          · exact (L.input.support_subset hz).1))).image (continuous_const_smul g)
    let D := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
    have hD : IsOpen D :=
      (L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet
    have hKD : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆ D := by
      rintro x ⟨z, hz, rfl⟩
      rcases hz with hz | hz
      · exact ⟨⟨L.chart.map_target (L.output.support_subset hz).1,
          L.output_support_in_input_frame hz⟩, (L.output.support_subset hz).2⟩
      · exact ⟨⟨L.chart.map_target (L.input.support_subset hz).1,
          (L.input.support_subset hz).2⟩, L.input_support_in_output_frame hz⟩
    let U := symbolChartDomain E F c e f ∩ (fun z ↦ g⁻¹ • c.symm z) ⁻¹' D
    have hU : IsOpen U :=
      ((Homeomorph.smul g⁻¹).continuous.comp_continuousOn
        (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1))).isOpen_inter_preimage
          (isOpen_symbolChartDomain E F c e f) hD
    have hKc : IsCompact (c '' K) :=
      hK.image_of_continuousOn (c.continuousOn.mono (fun x hx ↦ (hbase hx).1.1))
    have hKU : c '' K ⊆ U := by
      rintro z ⟨x, hx, rfl⟩
      have hb := hbase hx
      refine ⟨⟨⟨c.map_source hb.1.1, ?_⟩, ?_⟩, ?_⟩
      · change c.symm (c x) ∈ e.baseSet
        rw [c.left_inv hb.1.1]
        exact hb.1.2
      · change c.symm (c x) ∈ f.baseSet
        rw [c.left_inv hb.1.1]
        exact hb.2
      · change g⁻¹ • c.symm (c x) ∈ D
        rw [c.left_inv hb.1.1]
        obtain ⟨y, hy, rfl⟩ := hx
        rw [inv_smul_smul]
        exact hKD hy
    obtain ⟨O, hO, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hKc hU hKU
    obtain ⟨O', hO', hOO', hO'U, hO'c⟩ := exists_open_between_and_isCompact_closure hOc hU hOU
    obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO' hOc.isClosed hOO'
    have htsχ : tsupport χ = closure O' := congrArg closure hsχ
    have hcχ : HasCompactSupport χ := by
      change IsCompact (tsupport χ)
      rwa [htsχ]
    have hχU : tsupport χ ⊆ U := by rwa [htsχ]
    have hplateau : c '' K ⊆ interior {z | χ z = 1} := by
      apply hKO.trans
      apply interior_maximal _ hO
      intro z hz
      exact (honeχ z).mp (subset_closure hz)
    let A : BundleChartCutoff (r := r) E c :=
      { frame := e
        frame_mem_atlas := inferInstance
        cutoff := χ
        smooth_cutoff := hχ
        compact_support := hcχ
        support_subset := fun z hz ↦ (hχU hz).1.1 }
    let B : BundleChartCutoff (r := q) F c :=
      { frame := f
        frame_mem_atlas := inferInstance
        cutoff := χ
        smooth_cutoff := hχ
        compact_support := hcχ
        support_subset := fun z hz ↦ ⟨(hχU hz).1.1.1, (hχU hz).1.2⟩ }
    exact L.exists_conjugate_piece IG σ τ hσ hτ g c hc A B rfl hbase hplateau
      (fun z hz ↦ (hχU hz).2)
  let c (x : M) := chartAt X (g • x)
  let e (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E (g • x)
  let f (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F (g • x)
  let U (x : M) := (fun y : M ↦ g • y) ⁻¹'
    ((c x).source ∩ (e x).baseSet ∩ (f x).baseSet)
  have hU (x : M) : IsOpen (U x) :=
    (((c x).open_source.inter (e x).open_baseSet).inter (f x).open_baseSet).preimage
      (continuous_const_smul g)
  have hxU (x : M) : x ∈ U x :=
    ⟨⟨mem_chart_source X (g • x), mem_baseSet_trivializationAt _ _ _⟩,
      mem_baseSet_trivializationAt _ _ _⟩
  -- Each refinement uses actual off-diagonal kernels and the exact sum of original symbols.
  have hpiece (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
      ∃ (N : ℕ) (Q : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m),
        IsSmoothingOperator μ (C L.toLinearMap - ∑ j, (Q j).toLinearMap) ∧
        globalPrincipalSymbolClass E F m (∑ j, (Q j).globalSymbol) =
          ρ (globalPrincipalSymbolClass E F m L.globalSymbol) := by
    obtain ⟨N, a, R, hrem, hsum, hsupport⟩ := L.exists_refinement (μ := μ) U hU
      (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    have hrealize (j : Fin N) :
        ∃ Q : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m,
          Q.toLinearMap = C (R j).toLinearMap ∧
          globalPrincipalSymbolClass E F m Q.globalSymbol =
            ρ (globalPrincipalSymbolClass E F m (R j).globalSymbol) := by
      apply hchart (R j) (c (a j)) (chart_mem_atlas _ _) (e (a j)) (f (a j))
      rintro x ⟨y, hy, rfl⟩
      exact hsupport j hy
    choose Q hQmap hQsymbol using hrealize
    refine ⟨N, Q, ?_, ?_⟩
    · have hconj := IsSmoothingOperator.conjugate IG σ τ hσ hτ _ hrem g
      change IsSmoothingOperator μ (C ((L.toLinearMap - ∑ j, (R j).toLinearMap))) at hconj
      have hmaps : ∑ j, (Q j).toLinearMap = C (∑ j, (R j).toLinearMap) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun j _ ↦ hQmap j)
      rwa [map_sub, ← hmaps] at hconj
    · calc
        _ = ∑ j, globalPrincipalSymbolClass E F m (Q j).globalSymbol := map_sum _ _ _
        _ = ∑ j, ρ (globalPrincipalSymbolClass E F m (R j).globalSymbol) :=
          Finset.sum_congr rfl (fun j _ ↦ hQsymbol j)
        _ = ρ (globalPrincipalSymbolClass E F m (∑ j, (R j).globalSymbol)) := by
          rw [map_sum, map_sum]
        _ = _ := by rw [hsum]
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  choose d Q hQrem hQsymbol using fun i : Fin N ↦ hpiece (L i)
  let J := (i : Fin N) × Fin (d i)
  let enum : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let R (j : Fin (Fintype.card J)) := Q (enum j).1 (enum j).2
  have hmapSum : ∑ j, (R j).toLinearMap = ∑ i, ∑ j, (Q i j).toLinearMap := by
    change (∑ j, (fun k : J ↦ (Q k.1 k.2).toLinearMap) (enum j)) = _
    exact (enum.sum_comp (fun k : J ↦ (Q k.1 k.2).toLinearMap)).trans (Fintype.sum_sigma _)
  have hsymbolSum : ∑ j, (R j).globalSymbol = ∑ i, ∑ j, (Q i j).globalSymbol := by
    change (∑ j, (fun k : J ↦ (Q k.1 k.2).globalSymbol) (enum j)) = _
    exact (enum.sum_comp (fun k : J ↦ (Q k.1 k.2).globalSymbol)).trans (Fintype.sum_sigma _)
  refine ⟨Fintype.card J, R, ?_, ?_⟩
  · have hconj := IsSmoothingOperator.conjugate IG σ τ hσ hτ _ hL g
    change IsSmoothingOperator μ (C (P.toLinearMap - ∑ i, (L i).toLinearMap)) at hconj
    have hactual : C P.toLinearMap - ∑ j, (R j).toLinearMap =
        C (P.toLinearMap - ∑ i, (L i).toLinearMap) +
          ∑ i, (C (L i).toLinearMap - ∑ j, (Q i j).toLinearMap) := by
      rw [hmapSum, map_sub, map_sum, Finset.sum_sub_distrib]
      abel
    change IsSmoothingOperator μ (C P.toLinearMap - ∑ j, (R j).toLinearMap)
    rw [hactual]
    obtain ⟨AE⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
    obtain ⟨BF⟩ := nonempty_smoothBundlePresentation (n := n) (r := q) F
    apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ AE BF).mpr
    intro t
    exact (pseudodifferentialSpace E F μ t).add_mem
      (hconj.isPseudodifferentialOperator t _)
      ((pseudodifferentialSpace E F μ t).sum_mem
        (fun i _ ↦ (hQrem i).isPseudodifferentialOperator t _))
  · rw [hsymbolSum, P.principalSymbol_eq_of_representation N L hL]
    change globalPrincipalSymbolClass E F m (∑ i, ∑ j, (Q i j).globalSymbol) =
      ρ (globalPrincipalSymbolClass E F m (∑ i, (L i).globalSymbol))
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ hQsymbol i)

/-- An equivariant PDO has a fixed principal class for the same geometric bundle actions. -/
theorem PseudodifferentialOperator.equivariant_principalSymbol {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hP : P.IsEquivariant IG σ τ hσ hτ) (g : G) :
    equivariantPrincipalSymbolRepresentation (n := n) (r := r) (q := q) IG σ τ hσ hτ m g
        P.principalSymbol = P.principalSymbol := by
  /- Stage 1: conjugate a finite local representation of P by its original
  smooth-section actions, using g on the output and g inverse on the input.
  Move each chart, cutoff and frame by the specified smooth action, refining
  into the original valid charts and frames where needed. Coordinate-change
  covariance identifies the leading symbol with precisely the inverse
  cotangent and moving-fiber formula of equivariantGlobalSymbolLinearMap.
  Derivatives of the coordinate change and frame matrices beyond that leading
  term contribute symbols of order m-1, not equality of full symbols.
  Stage 2: the conjugated smoothing kernel remains smooth with respect to
  the same μ. The input change of variables contributes the smooth positive
  density ratio of the pushed-forward measure to μ, including the absolute
  inverse Jacobian. No invariance of μ is assumed or needed: this factor is
  absorbed in the original smooth kernel. Thus the transported finite pieces
  give a representation of the conjugated operator modulo a smooth remainder.
  Stage 3: hP and the group laws identify that conjugated operator with P
  on the actual smooth sections. The original principal-symbol uniqueness
  theorem and the quotient class formula identify their principal classes.
  Only this quotient class is fixed; an arbitrary full-symbol representative
  need not be fixed. This implication does not assert the converse, an
  invariant quantization, ellipticity, or boundedness on a Hilbert space. -/
  obtain ⟨N, Q, hQ, hclass⟩ := P.exists_representation_conjugate IG σ τ hσ hτ g
  -- Equivariance and the original representation law identify this actual conjugate with P.
  have hmap : (τ.smoothSectionRepresentation IG hτ g).comp
      (P.toLinearMap.comp (σ.smoothSectionRepresentation IG hσ g⁻¹)) = P.toLinearMap := by
    rw [hP g⁻¹, ← LinearMap.comp_assoc]
    change ((τ.smoothSectionRepresentation IG hτ g) *
      (τ.smoothSectionRepresentation IG hτ g⁻¹)).comp P.toLinearMap = P.toLinearMap
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hmap] at hQ
  exact hclass.symm.trans (P.principalSymbol_eq_of_representation N Q hQ).symm

end AtiyahSinger
