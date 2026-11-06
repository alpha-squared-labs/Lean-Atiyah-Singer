/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalCutoff
public import AtiyahSinger.Analysis.ProductTensorSchwartzSlice

/-!
# Full joint Fourier coordinates of the associated horizontal action

Public module ID: M0167.

The associated tensor chart input has a full joint Schwartz output under the
amplified horizontal lift. Its support lies in the product of the base output
cutoff support and the sphere cutoff support. Each sphere-frame column equals
the specified horizontal family in the original output frame, with the output
cutoff included exactly once.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space B]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)
local notation "V₁" => EuclideanSpace ℂ (Fin a')

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Full joint quantization retains every original horizontal output column. -/
theorem exists_associatedSphereTensorHorizontalJointCutoff
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (c : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hc : c ∈ atlas Y (OrthogonalSphere r)) (C : AtlasChartCutoff A c)
    (ρ : Y → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρK : HasCompactSupport ρ)
    (hρone : ∀ y ∈ tsupport C.cutoff, ρ y = 1) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b
      L.chart L.input hinput c C
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    ∀ I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank C.frameIndex))),
      (∀ w z, I w z = Din.localizedFunction w z) →
      ∀ w : AT.smoothSections,
        ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank C.frameIndex))),
          (∀ z, quantize (liftedProductSymbol
            (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank C.frameIndex) (α x ξ)) ρ)
              (I w) z = v z) ∧
          tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
            (tsupport L.output.cutoff ×ˢ tsupport C.cutoff) ∧
          ∀ (y : Y) (hy : y ∈ tsupport C.cutoff) (x : B)
            (_hx : x ∈ L.chart.source) (_hf : x ∈ L.output.frame.baseSet)
            (j : Fin (A.rank C.frameIndex)) (i : Fin a'),
            let l := (C.cutoff y : ℂ) • (LinearMap.proj j).comp
              (A.frameLinearEquiv C.frameIndex (c.symm y) (C.support_subset hy).2).toLinearMap
            v (EuclideanSpace.finAddEquivProd.symm (L.chart x, y))
                (finProdFinEquiv (i, j)) =
              (L.output.frame ⟨x, TensorProduct.lid ℂ (E' x)
                (TensorProduct.map l LinearMap.id
                  ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
                    hχ hχsupport (c.symm y) w).val x))⟩).2 i := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let Din := associatedSphereTensorChartCutoff S E A σ hσ b L.chart L.input hinput c C
  let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  let hα := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 L.output.cutoff
    L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _) L.symbol L.isSymbol
  let hαK := hasCompactSupport_zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    L.output.compact_support
  dsimp only
  intro I hI w
  change AT.smoothSections →ₗ[ℂ] 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank C.frameIndex))) at I
  change ∀ w z, I w z = Din.localizedFunction w z at hI
  let β : SymbolFunction n (a * A.rank C.frameIndex) (a' * A.rank C.frameIndex) :=
    fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank C.frameIndex) (α x ξ)
  have hβ : IsSymbol Set.univ 1 β := isSymbol_continuousLinearMap 1 α hα
    ((tensorIdentitySymbolMap a a' (A.rank C.frameIndex)).restrictScalars ℝ)
  have hβK : HasCompactSupport β := by
    apply hαK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport α)
    intro x hx
    by_contra hout
    apply hx
    funext ξ
    change tensorIdentitySymbolMap a a' (A.rank C.frameIndex) (α x ξ) = 0
    rw [image_eq_zero_of_notMem_tsupport hout]
    exact (tensorIdentitySymbolMap a a' (A.rank C.frameIndex)).map_zero
  have hIK : HasCompactSupport (I w) := by
    apply Din.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport Din.cutoff)
    intro z hz
    by_contra hout
    apply hz
    rw [hI]
    have hzero : Din.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hout
    simp only [AtlasChartCutoff.localizedFunction, hzero, Complex.ofReal_zero, zero_smul, ite_self]
  obtain ⟨v, hv, hvsupport⟩ := exists_schwartz_quantize_liftedProductSymbol_of_hasCompactSupport
    β hβ hβK ρ hρ hρK (I w) hIK
  have hsupport : tsupport v ⊆ e.symm ''
      (tsupport L.output.cutoff ×ˢ tsupport C.cutoff) := by
    -- The base factor retains the original output cutoff exactly once.
    have hβout : tsupport β ⊆ tsupport L.output.cutoff := by
      apply closure_minimal _ (isClosed_tsupport L.output.cutoff)
      intro x hx
      by_contra hout
      apply hx
      funext ξ
      change tensorIdentitySymbolMap a a' (A.rank C.frameIndex)
        (zeroExtendedSymbol Set.univ L.output.cutoff L.symbol x ξ) = 0
      simp [zeroExtendedSymbol, image_eq_zero_of_notMem_tsupport hout]
    -- Outside the sphere input-cutoff support, every base-coordinate slice is zero.
    have hysupport : tsupport v ⊆ (fun z : XY ↦ (e z).2) ⁻¹' tsupport C.cutoff := by
      apply closure_minimal _
        ((isClosed_tsupport C.cutoff).preimage (continuous_snd.comp e.continuous))
      intro z hz
      by_contra hy
      have hslice (x : X) :
          (0 : 𝓢(X, EuclideanSpace ℂ (Fin (a * A.rank C.frameIndex)))) x =
            I w (e.symm (x, (e z).2)) := by
        symm
        rw [hI]
        have hcut : Din.cutoff (e.symm (x, (e z).2)) =
            L.input.cutoff x * C.cutoff (e z).2 := by
          change L.input.cutoff (e (e.symm (x, (e z).2))).1 *
            C.cutoff (e (e.symm (x, (e z).2))).2 = _
          rw [e.apply_symm_apply]
        have hzero : C.cutoff (e z).2 = 0 := image_eq_zero_of_notMem_tsupport hy
        simp only [AtlasChartCutoff.localizedFunction, hcut, hzero, mul_zero,
          Complex.ofReal_zero, zero_smul, ite_self, zero_apply]
      have hvalue := quantize_liftedProductSymbol_eq_slice β hβ hβK ρ (I w)
        (e z).2 0 hslice (e z).1
      rw [e.symm_apply_apply, hv] at hvalue
      apply hz
      simpa [quantize, fourierSG] using hvalue
    intro z hz
    have hxβ : (e z).1 ∈ tsupport β := by
      obtain ⟨p, hp, hpoint⟩ := hvsupport hz
      rw [← hpoint, e.apply_symm_apply]
      exact hp.1
    exact ⟨e z, ⟨hβout hxβ, hysupport hz⟩, e.symm_apply_apply z⟩
  refine ⟨v, hv, hsupport, ?_⟩
  -- The actual tensor input columns are exactly the normalized original whole-sphere family.
  obtain ⟨_, hcolumns, _⟩ := exists_associatedSphereTensorHorizontalCutoff (a := a)
    S E A σ E' L hσ b hinput χ hχ hχsupport hχone c hc C ρ hρ hρK hρone
  obtain ⟨u, hu, f, g, hf, _hfK, hg, _hR, hH⟩ := hcolumns w
  have hcolumn (j : Fin (A.rank C.frameIndex)) (z : XY) (i : Fin a) :
      f j z i = I w z (finProdFinEquiv (i, j)) := by
    have hleft := hf (e z).1 (e z).2 i j
    rw [e.symm_apply_apply] at hleft
    rw [hleft, hu]
    have hright := associatedSphereTensorChartCutoff_localizedFunction (a := a)
      S E A σ hσ b L.chart L.input hinput c hc C w (e z).1 (e z).2 i j
    rw [e.symm_apply_apply] at hright
    rw [hI]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    convert hright.symm using 1
  -- Tensor amplification commutes with extraction of each sphere-frame column.
  intro y hy x hx hframe j i
  rw [← hv]
  rw [quantize_liftedProductSymbol_tensorIdentity_column α hα hαK ρ (I w) j
    (f j) (hcolumn j), hg]
  exact congrArg (fun z : V₁ ↦ z i) (hH y hy x hx hframe j)

end AtiyahSinger

