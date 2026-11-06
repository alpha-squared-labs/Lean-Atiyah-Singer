/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Fiber Hermitian adjoints and the global principal symbol quotient

Public module ID: M0678.

The Hermitian symbol operation in SG III.3.11 and pp.194-195,
expressed on actual fibers and descended to S^m/S^(m-1). It is conjugate-linear,
involutive, and uses the same covector. Arbitrary frames require both Gram weights.
Finite bundle rank supplies fiber completeness. Smooth metric coefficients suffice
for symbol estimates; no compact base, density, or ellipticity is used here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The Hermitian adjoint on the actual fibers, at the unchanged cotangent vector. -/
def globalSymbolAdjoint (p : GlobalSymbolFunction (n := n) E F) :
    GlobalSymbolFunction (n := n) F E := by
  letI (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  letI (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  letI (x : M) : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  letI (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  exact fun x ξ ↦ (p x ξ).adjoint

/-- Fiber adjunction uses the same covector and the specified Hermitian metrics. -/
theorem globalSymbolAdjoint_inner (p : GlobalSymbolFunction (n := n) E F)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
    (u : E x) (v : F x) :
    inner ℂ (p x ξ u) v = inner ℂ u (globalSymbolAdjoint (r := r) (q := q) p x ξ v) := by
  /- Supply the finite-dimensional completeness instances and apply the defining
  identity of ContinuousLinearMap.adjoint. Mathlib's first slot is conjugate-linear.
  The same ξ appears on both sides, including at the zero covector. -/
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  exact ((p x ξ).adjoint_inner_right u v).symm

/-- Taking fiber adjoints preserves sums. -/
theorem globalSymbolAdjoint_add (p p' : GlobalSymbolFunction (n := n) E F) :
    globalSymbolAdjoint (r := r) (q := q) (p + p') =
      globalSymbolAdjoint (r := r) (q := q) p + globalSymbolAdjoint (r := r) (q := q) p' := by
  /- Evaluate at x and ξ. Additivity of the continuous linear map adjoint gives
  equality on each finite-dimensional fiber; function extensionality finishes. -/
  funext x ξ
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  exact map_add ContinuousLinearMap.adjoint (p x ξ) (p' x ξ)

/-- The fiber adjoint conjugates complex scalars. -/
theorem globalSymbolAdjoint_smul (z : ℂ) (p : GlobalSymbolFunction (n := n) E F) :
    globalSymbolAdjoint (r := r) (q := q) (z • p) =
      starRingEnd ℂ z • globalSymbolAdjoint (r := r) (q := q) p := by
  /- Use conjugate-linearity of the Hilbert adjoint on each fiber. In particular,
  multiplication by i changes to multiplication by -i; no frequency reflection occurs. -/
  funext x ξ
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  exact map_smulₛₗ (ContinuousLinearMap.adjoint :
    (E x →L[ℂ] F x) ≃ₗᵢ⋆[ℂ] (F x →L[ℂ] E x)) z (p x ξ)

/-- Taking fiber adjoints twice recovers the entire symbol function. -/
theorem globalSymbolAdjoint_adjoint (p : GlobalSymbolFunction (n := n) E F) :
    globalSymbolAdjoint (r := q) (q := r) (globalSymbolAdjoint (r := r) (q := q) p) = p := by
  /- At every x and ξ both fibers are finite-dimensional Hilbert spaces. Apply
  adjoint_adjoint and then extensionality. This also controls the value at ξ=0. -/
  funext x ξ
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  exact ContinuousLinearMap.adjoint_adjoint (p x ξ)

/-- The Gram operator of a bundle frame, formed from its actual inverse fiber map. -/
def hermitianFrameGram (E : M → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (x : M) :
    EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) := by
  letI : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  letI : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  exact (e.symmL ℂ x).adjoint.comp (e.symmL ℂ x)

/-- The Gram operator records exactly the pullback of the fiber metric. -/
theorem hermitianFrameGram_inner
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (x : M) (u v : EuclideanSpace ℂ (Fin r)) :
    inner ℂ u (hermitianFrameGram E e x v) =
      inner ℂ (e.symmL ℂ x u) (e.symmL ℂ x v) := by
  /- Expand S†S and apply adjunction for S=e.symmL. This identity holds even
  outside e.baseSet, where S is totalized; invertibility is not asserted there. -/
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  exact (e.symmL ℂ x).adjoint_inner_right u (e.symmL ℂ x v)

/-- In arbitrary valid frames the geometric adjoint is the weighted matrix adjoint. -/
theorem globalSymbolInChart_globalSymbolAdjoint (p : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (z η : EuclideanSpace ℝ (Fin n)) (he : c.symm z ∈ e.baseSet)
    (hf : c.symm z ∈ f.baseSet) :
    globalSymbolInChart F E (globalSymbolAdjoint (r := r) (q := q) p) c f e z η =
      (hermitianFrameGram E e (c.symm z)).inverse.comp
        ((globalSymbolInChart E F p c e f z η).adjoint.comp
          (hermitianFrameGram F f (c.symm z))) := by
  /- Stage 1: the valid frame maps are linear equivalences. Their pullback Gram
  operators are positive definite and invertible. Express the fiber adjunction
  identity using the two Gram identities, obtaining G_E A†_geom = A* G_F.
  Stage 2: multiply by G_E^(-1) on the left and use nondegeneracy of the standard
  inner product. Both expressions use the same pulled-back covector; no condition
  on c or its derivative is needed for this pointwise fiber calculation. -/
  classical
  let x := c.symm z
  let GE := hermitianFrameGram E e x
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
  let : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
  -- On the valid frame the Gram operator has zero kernel, hence is invertible.
  have hGE : GE.IsInvertible := by
    have hinj : Function.Injective GE := by
      apply (ContinuousLinearMap.adjoint_comp_self_injective_iff (e.symmL ℂ x)).mpr
      exact Function.LeftInverse.injective (e.continuousLinearMapAt_symmL he)
    exact ⟨(LinearEquiv.ofBijective GE.toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv, rfl⟩
  apply ContinuousLinearMap.ext
  intro v
  -- Test the weighted equation against every model vector before applying the Gram inverse.
  have hweighted : GE
      (globalSymbolInChart F E (globalSymbolAdjoint (r := r) (q := q) p) c f e z η v) =
      (globalSymbolInChart E F p c e f z η).adjoint
        (hermitianFrameGram F f x v) := by
    apply ext_inner_left ℂ
    intro u
    rw [ContinuousLinearMap.adjoint_inner_right, hermitianFrameGram_inner]
    change inner ℂ (e.symmL ℂ x u) (e.symmL ℂ x
        (e.continuousLinearMapAt ℂ x
          (globalSymbolAdjoint (r := r) (q := q) p x (covectorFromChart c x η)
            (f.symmL ℂ x v)))) = _
    rw [e.symmL_continuousLinearMapAt he, ← globalSymbolAdjoint_inner,
      hermitianFrameGram_inner]
    change inner ℂ (p x (covectorFromChart c x η) (e.symmL ℂ x u))
        (f.symmL ℂ x v) =
      inner ℂ (f.symmL ℂ x
        (f.continuousLinearMapAt ℂ x
          (p x (covectorFromChart c x η) (e.symmL ℂ x u)))) (f.symmL ℂ x v)
    rw [f.symmL_continuousLinearMapAt hf]
  exact (hGE.inverse_apply_self _).symm.trans (congrArg GE.inverse hweighted)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hHE : IsSmoothHermitianBundle (n := n) (r := r) E]
  [hHF : IsSmoothHermitianBundle (n := n) (r := q) F]

include hM hHE hHF in
/-- Smooth Hermitian metrics preserve every real symbol order under fiber adjunction. -/
theorem IsGlobalSymbol.globalSymbolAdjoint {m : ℝ}
    {p : GlobalSymbolFunction (n := n) E F}
    (hp : IsGlobalSymbol (n := n) (r := r) (q := q) E F m p) :
    IsGlobalSymbol (n := n) (r := q) (q := r) F E m (globalSymbolAdjoint (r := r) (q := q) p) := by
  /- On the common chart/frame domain use G_E^(-1) A* G_F. Smooth metric entries
  and finite-dimensional matrix inversion give smooth Gram factors and derivatives
  bounded on compact coordinate sets. They are independent of frequency. Leibniz
  bounds therefore preserve the order m; conjugate transpose is real-linear and
  bounded. Swapping the frame domains changes only the order of intersections.
  This argument needs no smooth transition functions beyond the given estimates. -/
  classical
  let P := EuclideanSpace ℝ (Fin n)
  -- A smooth coefficient independent of frequency is an order-zero symbol.
  have coefficientSymbol {s t : ℕ} (U : Set P) (hU : IsOpen U)
      (A : P → EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))
      (hA : ContDiffOn ℝ ∞ A U) : IsSymbol U 0 (fun x _ ↦ A x) := by
    refine ⟨hA.comp contDiffOn_fst (fun _ hx ↦ hx.1), ?_⟩
    intro K hK hcompact i j
    cases j with
    | zero =>
      have hcont : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ i A x‖) K := by
        intro x hx
        exact ((hA.contDiffAt (hU.mem_nhds (hK hx))).continuousAt_iteratedFDeriv
          (by simp)).norm.continuousWithinAt
      obtain ⟨C, hC⟩ := (hcompact.image_of_continuousOn hcont).bddAbove
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro x hx ξ
      have heq : (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : P ↦ A y) ξ) =
          (continuousMultilinearCurryFin0 ℝ P
            (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t))).symm ∘ A := rfl
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ 0 (fun _ : P ↦ A y) ξ) x‖ ≤ _
      rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      simp only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
      exact (hC ⟨x, hx, rfl⟩).trans (le_max_left C 0)
    | succ j =>
      refine ⟨0, le_rfl, ?_⟩
      intro x hx ξ
      have hz : (fun y : P ↦ iteratedFDeriv ℝ (j + 1) (fun _ : P ↦ A y) ξ) = 0 := by
        funext y
        exact congrFun (iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) (A y)) ξ
      change ‖iteratedFDeriv ℝ i
        (fun y ↦ iteratedFDeriv ℝ (j + 1) (fun _ : P ↦ A y) ξ) x‖ ≤ _
      rw [hz, iteratedFDeriv_zero]
      simp
  -- The complex adjoint is a real-linear isometry, also on every derivative target.
  have adjointSymbol {s t : ℕ} (U : Set P) (m : ℝ)
      (a : SymbolFunction n s t) (ha : IsSymbol U m a) :
      IsSymbol U m (fun x ξ ↦ (a x ξ).adjoint) := by
    let V := EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t)
    let W := EuclideanSpace ℂ (Fin t) →L[ℂ] EuclideanSpace ℂ (Fin s)
    let J : V ≃ₗᵢ[ℝ] W := {
      toEquiv := (ContinuousLinearMap.adjoint : V ≃ₗᵢ⋆[ℂ] W).toEquiv
      map_add' := map_add ContinuousLinearMap.adjoint
      map_smul' := by
        intro t A
        change (t • A).adjoint = t • A.adjoint
        rw [← Complex.coe_smul t A, map_smulₛₗ]
        simp
      norm_map' := ContinuousLinearMap.adjoint.norm_map }
    refine ⟨J.contDiff.comp_contDiffOn ha.1, ?_⟩
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    let Jj : (P [×j]→L[ℝ] V) ≃ₗᵢ[ℝ] (P [×j]→L[ℝ] W) := {
      toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
        (fun _ : Fin j ↦ P)).toLinearEquiv
      norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a y η).adjoint) ξ) =
        Jj ∘ (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) := by
      funext y
      exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    change ‖iteratedFDeriv ℝ i
      (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a y η).adjoint) ξ) x‖ ≤ _
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hbound x hx ξ
  -- Native smoothness of metric entries reconstructs the actual Gram operator.
  have gramSmooth {s : ℕ} (U : Set M)
      (G : M → EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s))
      (A : M → Fin s → Fin s → ℂ)
      (hA : ∀ i j, ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, ℂ) ∞ (fun x ↦ A x i j) U)
      (hG : ∀ x i j, inner ℂ (EuclideanSpace.single i 1)
        (G x (EuclideanSpace.single j 1)) = A x i j) :
      ContMDiffOn 𝓘(ℝ, P)
        𝓘(ℝ, EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s)) ∞ G U := by
    let toOp : (Fin s → Fin s → ℂ) →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s)) :=
      LinearMap.toContinuousLinearMap.toLinearMap.comp
        (Matrix.toEuclideanLin.toLinearMap.comp (Matrix.ofLinearEquiv ℂ).toLinearMap)
    let toOpC : (Fin s → Fin s → ℂ) →L[ℝ]
        (EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin s)) :=
      LinearMap.toContinuousLinearMap (toOp.restrictScalars ℝ)
    have hAsmooth : ContMDiffOn 𝓘(ℝ, P) 𝓘(ℝ, Fin s → Fin s → ℂ) ∞ A U := by
      exact contMDiffOn_pi_space.mpr (fun i ↦ contMDiffOn_pi_space.mpr (hA i))
    have heq : (fun x ↦ toOpC (A x)) = G := by
      funext x
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin s) ℂ).toBasis.ext
      intro j
      apply PiLp.ext
      intro i
      have h := hG x i j
      change (Matrix.toEuclideanLin (Matrix.of (A x))
        ((EuclideanSpace.basisFun (Fin s) ℂ).toBasis j)) i = _
      rw [Matrix.toLpLin_apply]
      simpa [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct,
        EuclideanSpace.inner_single_left] using h.symm
    rw [← heq]
    exact toOpC.contDiff.contMDiff.comp_contMDiffOn hAsmooth
  intro c hc f e hf he
  let U := symbolChartDomain E F c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hswap : symbolChartDomain F E c f e = U := by
    ext z
    simp only [symbolChartDomain, U, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hswap]
  -- Both Gram weights are smooth in the same original coordinate domain.
  have hGE : ContDiffOn ℝ ∞ (fun z ↦ hermitianFrameGram E e (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := (gramSmooth e.baseSet (hermitianFrameGram E e) _
      (IsSmoothHermitianBundle.contMDiffOn_inner e)
      (fun x i j ↦ hermitianFrameGram_inner e x _ _)).contMDiffAt
        (e.open_baseSet.mem_nhds hz.1.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  have hGF : ContDiffOn ℝ ∞ (fun z ↦ hermitianFrameGram F f (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := (gramSmooth f.baseSet (hermitianFrameGram F f) _
      (IsSmoothHermitianBundle.contMDiffOn_inner f)
      (fun x i j ↦ hermitianFrameGram_inner f x _ _)).contMDiffAt
        (f.open_baseSet.mem_nhds hz.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  have hGEinv : ContDiffOn ℝ ∞
      (fun z ↦ (hermitianFrameGram E e (c.symm z)).inverse) U := by
    intro z hz
    let x := c.symm z
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    have hinj : Function.Injective (hermitianFrameGram E e x) := by
      apply (ContinuousLinearMap.adjoint_comp_self_injective_iff (e.symmL ℂ x)).mpr
      exact Function.LeftInverse.injective (e.continuousLinearMapAt_symmL hz.1.2)
    have hinv : (hermitianFrameGram E e x).IsInvertible :=
      ⟨(LinearEquiv.ofBijective (hermitianFrameGram E e x).toLinearMap
        ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv, rfl⟩
    have hi := hinv.contDiffAt_map_inverse (n := ∞)
    exact (hi.restrict_scalars ℝ).comp_contDiffWithinAt z (hGE z hz)
  -- Composition adds orders: the two Gram weights contribute exactly zero.
  have hweighted := (coefficientSymbol U hU _ hGEinv).symbolComp hU
    ((adjointSymbol U m _ (hp c hc e f)).symbolComp hU
      (coefficientSymbol U hU _ hGF))
  simp only [zero_add, add_zero] at hweighted
  have heq (z : P) (hz : z ∈ U) (η : P) :
      globalSymbolInChart F E (AtiyahSinger.globalSymbolAdjoint (r := r) (q := q) p) c f e z η =
        symbolComp (fun z _ ↦ (hermitianFrameGram E e (c.symm z)).inverse)
          (symbolComp (fun z η ↦ (globalSymbolInChart E F p c e f z η).adjoint)
            (fun z _ ↦ hermitianFrameGram F f (c.symm z))) z η :=
    globalSymbolInChart_globalSymbolAdjoint p c e f z η hz.1.2 hz.2
  refine ⟨hweighted.1.congr (fun z hz ↦ heq z.1 hz.1 z.2), ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, hbound⟩ := hweighted.2 K hK hcompact i j
  refine ⟨C, hC, ?_⟩
  intro z hz η
  -- Equality throughout the open overlap identifies the full, totalized mixed derivatives.
  have hnear : (fun y ↦ iteratedFDeriv ℝ j
      (globalSymbolInChart F E
        (AtiyahSinger.globalSymbolAdjoint (r := r) (q := q) p) c f e y) η) =ᶠ[nhds z]
      (fun y ↦ iteratedFDeriv ℝ j
        (symbolComp (fun y _ ↦ (hermitianFrameGram E e (c.symm y)).inverse)
          (symbolComp (fun y ξ ↦ (globalSymbolInChart E F p c e f y ξ).adjoint)
            (fun y _ ↦ hermitianFrameGram F f (c.symm y))) y) η) := by
    filter_upwards [hU.mem_nhds (hK hz)] with y hy
    rw [show globalSymbolInChart F E
      (AtiyahSinger.globalSymbolAdjoint (r := r) (q := q) p) c f e y =
      _ from funext (heq y hy)]
  change ‖iteratedFDeriv ℝ i _ z‖ ≤ _
  rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hbound z hz η

/-- The fiber adjoint packaged with its preserved global symbol estimate. -/
def globalSymbolSpaceAdjoint {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalSymbolSpace (n := n) (r := q) (q := r) F E m :=
  ⟨globalSymbolAdjoint (r := r) (q := q) p.val, p.property.globalSymbolAdjoint⟩

/-- Symbols with the same principal class have adjoints with the same target class. -/
theorem globalPrincipalSymbolClass_adjoint_congr {m : ℝ}
    (p p' : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (h : globalPrincipalSymbolClass E F m p = globalPrincipalSymbolClass E F m p') :
    globalPrincipalSymbolClass F E m (globalSymbolSpaceAdjoint p) =
      globalPrincipalSymbolClass F E m (globalSymbolSpaceAdjoint p') := by
  /- The quotient criterion says p-p' has order m-1. Apply order preservation
  there and use additivity and conjugation of -1 to identify its adjoint with the
  difference of the two adjoints. The target quotient criterion gives equality. -/
  apply (globalPrincipalSymbolClass_eq_iff F E m _ _).mpr
  have hsub := ((globalPrincipalSymbolClass_eq_iff E F m p p').mp h).globalSymbolAdjoint
  have heq : globalSymbolAdjoint (r := r) (q := q) (p.val - p'.val) =
      (globalSymbolSpaceAdjoint p).val - (globalSymbolSpaceAdjoint p').val := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ p'.val, globalSymbolAdjoint_add,
      globalSymbolAdjoint_smul]
    simp only [map_neg, map_one, neg_one_smul, sub_eq_add_neg, globalSymbolSpaceAdjoint]
  exact heq ▸ hsub

/-- Fiber Hermitian adjunction descended to the actual principal-symbol quotient. -/
def globalPrincipalSymbolAdjoint {m : ℝ} :
    GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m →
      GlobalPrincipalSymbolSpace (n := n) (r := q) (q := r) F E m :=
  Quotient.lift
    (fun p ↦ globalPrincipalSymbolClass F E m (globalSymbolSpaceAdjoint p))
    (fun p p' h ↦ globalPrincipalSymbolClass_adjoint_congr p p' (Quotient.sound h))

/-- An actual representative computes its quotient adjoint by fiberwise adjunction. -/
theorem globalPrincipalSymbolAdjoint_class {m : ℝ}
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolAdjoint (globalPrincipalSymbolClass E F m p) =
      globalPrincipalSymbolClass F E m (globalSymbolSpaceAdjoint p) := by
  /- Evaluate Quotient.lift on p. The congruence certificate handles all other
  representatives; no homogeneous leading term or chosen representative is needed. -/
  rfl

/-- The zero principal class has zero adjoint. -/
theorem globalPrincipalSymbolAdjoint_zero (m : ℝ) :
    globalPrincipalSymbolAdjoint
        (0 : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) = 0 := by
  /- Represent zero by the zero symbol. Its fiber adjoint and its target class
  are both zero. Apply the representative formula and linearity of the class map. -/
  have hz : globalSymbolSpaceAdjoint
      (0 : globalSymbolSpace (n := n) (r := r) (q := q) E F m) = 0 := by
    apply Subtype.ext
    have h := globalSymbolAdjoint_smul (r := r) (q := q) (n := n) (M := M)
      (E := E) (F := F) (0 : ℂ) (0 : GlobalSymbolFunction (n := n) E F)
    change globalSymbolAdjoint (r := r) (q := q) 0 = 0
    simpa only [zero_smul, map_zero] using h
  rw [← map_zero (globalPrincipalSymbolClass E F m), globalPrincipalSymbolAdjoint_class,
    hz, map_zero]

/-- The principal-symbol adjoint is additive. -/
theorem globalPrincipalSymbolAdjoint_add {m : ℝ}
    (p p' : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolAdjoint (p + p') =
      globalPrincipalSymbolAdjoint p + globalPrincipalSymbolAdjoint p' := by
  /- Choose representatives and apply fiber additivity. Both quotient maps
  preserve sums; quotient surjectivity removes the choices of representatives. -/
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  obtain ⟨b, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p'
  rw [← map_add, globalPrincipalSymbolAdjoint_class,
    globalPrincipalSymbolAdjoint_class, globalPrincipalSymbolAdjoint_class, ← map_add]
  apply congrArg (globalPrincipalSymbolClass F E m)
  apply Subtype.ext
  exact globalSymbolAdjoint_add (r := r) (q := q) a.val b.val

/-- Scalar conjugation survives passage to the principal-symbol quotient. -/
theorem globalPrincipalSymbolAdjoint_smul {m : ℝ} (z : ℂ)
    (p : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolAdjoint (z • p) = starRingEnd ℂ z • globalPrincipalSymbolAdjoint p := by
  /- On a representative use the conjugate-scalar fiber identity, followed by
  complex linearity of both class projections. This operation is not complex-linear. -/
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  rw [← map_smul, globalPrincipalSymbolAdjoint_class, globalPrincipalSymbolAdjoint_class,
    ← map_smul]
  apply congrArg (globalPrincipalSymbolClass F E m)
  apply Subtype.ext
  exact globalSymbolAdjoint_smul (r := r) (q := q) z a.val

/-- The principal-symbol adjoint is an involution between the two bundle directions. -/
theorem globalPrincipalSymbolAdjoint_adjoint {m : ℝ}
    (p : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    globalPrincipalSymbolAdjoint (globalPrincipalSymbolAdjoint p) = p := by
  /- Choose a representative and apply the representative formula twice. The
  fiber double-adjoint identity recovers it exactly, so its class is unchanged. -/
  obtain ⟨a, rfl⟩ := globalPrincipalSymbolClass_surjective E F m p
  rw [globalPrincipalSymbolAdjoint_class, globalPrincipalSymbolAdjoint_class]
  apply congrArg (globalPrincipalSymbolClass E F m)
  apply Subtype.ext
  exact globalSymbolAdjoint_adjoint (r := r) (q := q) a.val

end AtiyahSinger
