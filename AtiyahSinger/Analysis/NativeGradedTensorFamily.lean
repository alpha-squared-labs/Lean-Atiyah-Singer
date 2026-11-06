/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedMetricFormalAdjoint
public import AtiyahSinger.Analysis.GradedBundleOperator
public import AtiyahSinger.Analysis.GradedTensorGlobalSymbol
public import AtiyahSinger.Geometry.NativeOrthogonalSum
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# One native graded cutoff family on fixed orthogonal sums

Public module ID: M0812.

The specified four corner families and their actual tensor full symbols form
one graded PDO family. The two native sums are selected before the parameter.
The literal metric adjoint, the actual Sobolev matrix, and the reciprocal full
symbol all retain the same corners and the original metric cores.
The four actual corner families are supplied;
no target K identity, ellipticity, approximation limit or index is assumed.
-/

@[expose] public noncomputable section


open Lean Elab Tactic Meta in
local elab "as_aux_lemma_zeta" " => " s:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic s)
  unless remaining.isEmpty do
    throwError "Cannot abstract an unfinished proof"
  let value ← instantiateMVars (mkMVar goal)
  if value.hasSorry then
    throwError "Cannot abstract a proof containing a recovery placeholder"
  let value ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign value

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct Topology

attribute [local instance] sumTopology

variable {n : ℕ} {M ι : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  (N₀₀ N₁₀ N₀₁ N₁₁ : SmoothFiniteComplexBundle (n := n) M)
  (E₀ E₁ F₀ F₁ : M → Type*)
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]
  [∀ x, FiniteDimensional ℂ (E₀ x)] [∀ x, FiniteDimensional ℂ (E₁ x)]
  [∀ x, FiniteDimensional ℂ (F₀ x)] [∀ x, FiniteDimensional ℂ (F₁ x)]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- Retain the fixed sums, original four operators and their actual Sobolev and symbol matrices.
/-- Four specified native tensor families determine one graded family with its literal adjoint. -/
theorem exists_native_graded_family_of_tensor_symbols
    (e₀₀ : ∀ x, (E₀ x ⊗[ℂ] F₀ x) ≃ₗ[ℂ] N₀₀.Fiber x)
    (e₁₀ : ∀ x, (E₁ x ⊗[ℂ] F₀ x) ≃ₗ[ℂ] N₁₀.Fiber x)
    (e₀₁ : ∀ x, (E₀ x ⊗[ℂ] F₁ x) ≃ₗ[ℂ] N₀₁.Fiber x)
    (e₁₁ : ∀ x, (E₁ x ⊗[ℂ] F₁ x) ≃ₗ[ℂ] N₁₁.Fiber x)
    (k₀₀ : SmoothHermitianMetric (n := n) (r := N₀₀.rank) N₀₀.Fiber)
    (k₁₀ : SmoothHermitianMetric (n := n) (r := N₁₀.rank) N₁₀.Fiber)
    (k₀₁ : SmoothHermitianMetric (n := n) (r := N₀₁.rank) N₀₁.Fiber)
    (k₁₁ : SmoothHermitianMetric (n := n) (r := N₁₁.rank) N₁₁.Fiber)
    (c₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
    (c₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
    (d₀ : ∀ x, InnerProductSpace.Core ℂ (F₀ x))
    (d₁ : ∀ x, InnerProductSpace.Core ℂ (F₁ x))
    (hk₁₀ : ∀ x u v a b, k₁₀.pairing x (e₁₀ x (u ⊗ₜ[ℂ] a))
      (e₁₀ x (v ⊗ₜ[ℂ] b)) = (c₁ x).inner u v * (d₀ x).inner a b)
    (hk₀₁ : ∀ x u v a b, k₀₁.pairing x (e₀₁ x (u ⊗ₜ[ℂ] a))
      (e₀₁ x (v ⊗ₜ[ℂ] b)) = (c₀ x).inner u v * (d₁ x).inner a b)
    (hk₁₁ : ∀ x u v a b, k₁₁.pairing x (e₁₁ x (u ⊗ₜ[ℂ] a))
      (e₁₁ x (v ⊗ₜ[ℂ] b)) = (c₁ x).inner u v * (d₁ x).inner a b)
    (U₀Family : ι → PseudodifferentialOperator (n := n) (r := N₀₀.rank) (q := N₁₀.rank)
      N₀₀.Fiber N₁₀.Fiber μ 1)
    (U₁Family : ι → PseudodifferentialOperator (n := n) (r := N₀₁.rank) (q := N₁₁.rank)
      N₀₁.Fiber N₁₁.Fiber μ 1)
    (V₀Family : ι → PseudodifferentialOperator (n := n) (r := N₀₀.rank) (q := N₀₁.rank)
      N₀₀.Fiber N₀₁.Fiber μ 1)
    (V₁Family : ι → PseudodifferentialOperator (n := n) (r := N₁₀.rank) (q := N₁₁.rank)
      N₁₀.Fiber N₁₁.Fiber μ 1)
    (a₀Family : ι → globalSymbolSpace (n := n) (r := N₀₀.rank) (q := N₁₀.rank)
      N₀₀.Fiber N₁₀.Fiber 1)
    (a₁Family : ι → globalSymbolSpace (n := n) (r := N₀₁.rank) (q := N₁₁.rank)
      N₀₁.Fiber N₁₁.Fiber 1)
    (b₀Family : ι → globalSymbolSpace (n := n) (r := N₀₀.rank) (q := N₀₁.rank)
      N₀₀.Fiber N₀₁.Fiber 1)
    (b₁Family : ι → globalSymbolSpace (n := n) (r := N₁₀.rank) (q := N₁₁.rank)
      N₁₀.Fiber N₁₁.Fiber 1)
    (ha₀ : ∀ t, (U₀Family t).principalSymbol =
      globalPrincipalSymbolClass N₀₀.Fiber N₁₀.Fiber 1 (a₀Family t))
    (ha₁ : ∀ t, (U₁Family t).principalSymbol =
      globalPrincipalSymbolClass N₀₁.Fiber N₁₁.Fiber 1 (a₁Family t))
    (hb₀ : ∀ t, (V₀Family t).principalSymbol =
      globalPrincipalSymbolClass N₀₀.Fiber N₀₁.Fiber 1 (b₀Family t))
    (hb₁ : ∀ t, (V₁Family t).principalSymbol =
      globalPrincipalSymbolClass N₁₀.Fiber N₁₁.Fiber 1 (b₁Family t))
    (pfFamily : ι → ∀ x, CotangentFiber (n := n) x → E₀ x →ₗ[ℂ] E₁ x)
    (qfFamily : ι → ∀ x, CotangentFiber (n := n) x → F₀ x →ₗ[ℂ] F₁ x)
    (ha₀tensor : ∀ t x ξ u v, (a₀Family t).val x ξ (e₀₀ x (u ⊗ₜ[ℂ] v)) =
      e₁₀ x (pfFamily t x ξ u ⊗ₜ[ℂ] v))
    (ha₁tensor : ∀ t x ξ u v, (a₁Family t).val x ξ (e₀₁ x (u ⊗ₜ[ℂ] v)) =
      e₁₁ x (pfFamily t x ξ u ⊗ₜ[ℂ] v))
    (hb₀tensor : ∀ t x ξ u v, (b₀Family t).val x ξ (e₀₀ x (u ⊗ₜ[ℂ] v)) =
      e₀₁ x (u ⊗ₜ[ℂ] qfFamily t x ξ v))
    (hb₁tensor : ∀ t x ξ u v, (b₁Family t).val x ξ (e₁₀ x (u ⊗ₜ[ℂ] v)) =
      e₁₁ x (u ⊗ₜ[ℂ] qfFamily t x ξ v)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
    ∃ (Nplus Nminus : SmoothFiniteComplexBundle (n := n) M),
      Nplus.rank = N₀₀.rank + N₁₁.rank ∧ Nminus.rank = N₁₀.rank + N₀₁.rank ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
      ∃ (ePlus : Iso (N₀₀.Fiber ×ᵇ N₁₁.Fiber) Nplus.Fiber)
        (eMinus : Iso (N₁₀.Fiber ×ᵇ N₀₁.Fiber) Nminus.Fiber)
        (hPlus₀ : IsSmoothBundleMap (n := n) (r := N₀₀.rank) (q := Nplus.rank)
          (fun z ↦ (ePlus.linearEquiv z).toLinearMap.comp
            (LinearMap.inl ℂ (N₀₀.Fiber z) (N₁₁.Fiber z))))
        (hPlus₁ : IsSmoothBundleMap (n := n) (r := N₁₁.rank) (q := Nplus.rank)
          (fun z ↦ (ePlus.linearEquiv z).toLinearMap.comp
            (LinearMap.inr ℂ (N₀₀.Fiber z) (N₁₁.Fiber z))))
        (hMinus₀ : IsSmoothBundleMap (n := n) (r := N₁₀.rank) (q := Nminus.rank)
          (fun z ↦ (eMinus.linearEquiv z).toLinearMap.comp
            (LinearMap.inl ℂ (N₁₀.Fiber z) (N₀₁.Fiber z))))
        (hMinus₁ : IsSmoothBundleMap (n := n) (r := N₀₁.rank) (q := Nminus.rank)
          (fun z ↦ (eMinus.linearEquiv z).toLinearMap.comp
            (LinearMap.inr ℂ (N₁₀.Fiber z) (N₀₁.Fiber z))))
        (kPlus : SmoothHermitianMetric (n := n) (r := Nplus.rank) Nplus.Fiber)
        (kMinus : SmoothHermitianMetric (n := n) (r := Nminus.rank) Nminus.Fiber),
        (∀ z u v, kPlus.pairing z (ePlus.linearEquiv z u) (ePlus.linearEquiv z v) =
          k₀₀.pairing z u.1 v.1 + k₁₁.pairing z u.2 v.2) ∧
        (∀ z u v, kMinus.pairing z (eMinus.linearEquiv z u) (eMinus.linearEquiv z v) =
          k₁₀.pairing z u.1 v.1 + k₀₁.pairing z u.2 v.2) ∧
        let AA : Fin 2 → SmoothFiniteComplexBundle (n := n) M := ![N₀₀, N₁₁]
        let BB : Fin 2 → SmoothFiniteComplexBundle (n := n) M := ![N₁₀, N₀₁]
        ∀ (DD : ∀ i, SmoothBundlePresentation (n := n) (r := (AA i).rank) (AA i).Fiber)
          (HH : ∀ i, SmoothBundlePresentation (n := n) (r := (BB i).rank) (BB i).Fiber)
          (Dplus : SmoothBundlePresentation (n := n) (r := Nplus.rank) Nplus.Fiber)
          (Dminus : SmoothBundlePresentation (n := n) (r := Nminus.rank) Nminus.Fiber)
          (t : ι),
        let U₀ := U₀Family t
        let U₁ := U₁Family t
        let V₀ := V₀Family t
        let V₁op := V₁Family t
        let _a₀ := a₀Family t
        let _a₁ := a₁Family t
        let _b₀ := b₀Family t
        let _b₁ := b₁Family t
        let pf := pfFamily t
        let qf := qfFamily t
        let Φ := smoothSectionSumEquiv ePlus.linearEquiv hPlus₀ hPlus₁
        let Ψ := smoothSectionSumEquiv eMinus.linearEquiv hMinus₀ hMinus₁
        ∃ K : PseudodifferentialOperator (n := n)
            (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber μ 1,
          (∀ u v, K.toLinearMap (Φ (u, v)) =
            Ψ (U₀.toLinearMap u - (V₁op.metricFormalAdjoint k₁₀ k₁₁).toLinearMap v,
              V₀.toLinearMap u + (U₁.metricFormalAdjoint k₀₁ k₁₁).toLinearMap v)) ∧
          (∀ u v, (K.metricFormalAdjoint kPlus kMinus).toLinearMap (Ψ (u, v)) =
            Φ ((U₀.metricFormalAdjoint k₀₀ k₁₀).toLinearMap u +
              (V₀.metricFormalAdjoint k₀₀ k₀₁).toLinearMap v,
              -V₁op.toLinearMap u + U₁.toLinearMap v)) ∧
          (∃ (I : Dplus.SobolevSpace 1 ≃L[ℂ]
                WithLp 2 ((DD 0).SobolevSpace 1 × (DD 1).SobolevSpace 1))
              (O : Dminus.SobolevSpace 0 ≃L[ℂ]
                WithLp 2 ((HH 0).SobolevSpace 0 × (HH 1).SobolevSpace 0)),
            (∀ u v, I (Dplus.smoothToSobolev 1 (Φ (u, v))) =
              WithLp.toLp 2 ((DD 0).smoothToSobolev 1 u, (DD 1).smoothToSobolev 1 v)) ∧
            (∀ u v, O (Dminus.smoothToSobolev 0 (Ψ (u, v))) =
              WithLp.toLp 2 ((HH 0).smoothToSobolev 0 u, (HH 1).smoothToSobolev 0 v)) ∧
            O.toContinuousLinearMap.comp (K.sobolevRealization Dplus Dminus 1 0 (by norm_num)) =
              (gradedBlockOperator
                (U₀.sobolevRealization (DD 0) (HH 0) 1 0 (by norm_num))
                (V₀.sobolevRealization (DD 0) (HH 1) 1 0 (by norm_num))
                ((V₁op.metricFormalAdjoint k₁₀ k₁₁).sobolevRealization
                  (DD 1) (HH 0) 1 0 (by norm_num))
                ((U₁.metricFormalAdjoint k₀₁ k₁₁).sobolevRealization
                  (DD 1) (HH 1) 1 0 (by norm_num))).comp
                  I.toContinuousLinearMap) ∧
          ∃ (pi : ∀ z, CotangentFiber (n := n) z → E₁ z →ₗ[ℂ] E₀ z)
            (qi : ∀ z, CotangentFiber (n := n) z → F₁ z →ₗ[ℂ] F₀ z),
            (∀ z ξ u v, (c₁ z).inner (pf z ξ u) v = (c₀ z).inner u (pi z ξ v)) ∧
            (∀ z ξ u v, (d₁ z).inner (qf z ξ u) v = (d₀ z).inner u (qi z ξ v)) ∧
            ∃ qK : globalSymbolSpace (n := n)
                (r := Nplus.rank) (q := Nminus.rank) Nplus.Fiber Nminus.Fiber 1,
              K.principalSymbol = globalPrincipalSymbolClass Nplus.Fiber Nminus.Fiber 1 qK ∧
              ∀ z ξ (u : E₀ z ⊗[ℂ] F₀ z) (v : E₁ z ⊗[ℂ] F₁ z),
                let w := reciprocalTensorSymbol (pf z ξ) (pi z ξ) (qf z ξ) (qi z ξ) (u, v)
                qK.val z ξ (ePlus.linearEquiv z
                  (e₀₀ z u, e₁₁ z v)) =
                    eMinus.linearEquiv z (e₁₀ z w.1, e₀₁ z w.2) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₀.rank)) N₀₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₀.rank)) N₁₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₀₁.rank)) N₀₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin N₁₁.rank)) N₁₁.Fiber
  as_aux_lemma_zeta =>
    -- Select the two orthogonal sums once, before the common cutoff parameter.
    obtain ⟨Nplus, hNplus, ePlus, hePlus, hiPlus, hPlus₀, hPlus₁, kPlus, hkPlus⟩ :=
      SmoothFiniteComplexBundle.exists_orthogonal_sum N₀₀ N₁₁ k₀₀ k₁₁
    obtain ⟨Nminus, hNminus, eMinus, heMinus, hiMinus, hMinus₀, hMinus₁, kMinus, hkMinus⟩ :=
      SmoothFiniteComplexBundle.exists_orthogonal_sum N₁₀ N₀₁ k₁₀ k₀₁
    refine Exists.intro Nplus ?_
    refine Exists.intro Nminus ?_
    refine And.intro hNplus ?_
    refine And.intro hNminus ?_
    let := modelTopology (EuclideanSpace ℂ (Fin Nplus.rank)) Nplus.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin Nminus.rank)) Nminus.Fiber
    refine Exists.intro ePlus ?_
    refine Exists.intro eMinus ?_
    refine Exists.intro hPlus₀ ?_
    refine Exists.intro hPlus₁ ?_
    refine Exists.intro hMinus₀ ?_
    refine Exists.intro hMinus₁ ?_
    refine Exists.intro kPlus ?_
    refine Exists.intro kMinus ?_
    refine And.intro hkPlus ?_
    refine And.intro hkMinus ?_
    intro AA BB DD HH Dplus Dminus t U₀ U₁ V₀ V₁op a₀ a₁ b₀ b₁ pf qf Φ Ψ
    let hA (i : Fin 2) : SmoothHermitianMetric (n := n) (r := (AA i).rank) (AA i).Fiber := by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact k₀₀
      · exact Fin.cases k₁₁ (fun k ↦ Fin.elim0 k) j
    let hB (i : Fin 2) : SmoothHermitianMetric (n := n) (r := (BB i).rank) (BB i).Fiber := by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact k₁₀
      · exact Fin.cases k₀₁ (fun k ↦ Fin.elim0 k) j
    -- The original four native corners determine one PDO on these same sum bundles.
    obtain ⟨K, hK, hSob⟩ := exists_gradedBundlePseudodifferentialOperator Nplus Nminus AA BB
      ePlus.linearEquiv eMinus.linearEquiv hPlus₀ hPlus₁ hMinus₀ hMinus₁ U₀ V₀
      (V₁op.metricFormalAdjoint k₁₀ k₁₁) (U₁.metricFormalAdjoint k₀₁ k₁₁)
      DD HH Dplus Dminus 1 0 (by norm_num)
    refine Exists.intro K ?_
    refine And.intro hK ?_
    refine And.intro ?_ ?_
    · -- Uniqueness identifies the actual metric adjoint; no second PDO is chosen.
      exact graded_metricFormalAdjoint_call Nplus Nminus AA BB
        ePlus.linearEquiv eMinus.linearEquiv hPlus₀ hPlus₁ hMinus₀ hMinus₁
        hA hB U₀ V₀ U₁ V₁op K hK kPlus kMinus hkPlus hkMinus
    refine And.intro hSob ?_
    -- The factor adjoints use exactly the original supplied positive forms.
    have hpiExists (z : M) (ξ : CotangentFiber (n := n) z) :
        ∃ pi : E₁ z →ₗ[ℂ] E₀ z, ∀ u v,
          (c₁ z).inner (pf z ξ u) v = (c₀ z).inner u (pi v) := by
      let moduleE : Module ℂ (E₀ z) := inferInstance
      let moduleE' : Module ℂ (E₁ z) := inferInstance
      let : NormedAddCommGroup (E₀ z) := (c₀ z).toNormedAddCommGroup
      let : Module ℂ (E₀ z) := moduleE
      let : InnerProductSpace ℂ (E₀ z) := InnerProductSpace.ofCore (c₀ z).toCore
      let : NormedAddCommGroup (E₁ z) := (c₁ z).toNormedAddCommGroup
      let : Module ℂ (E₁ z) := moduleE'
      let : InnerProductSpace ℂ (E₁ z) := InnerProductSpace.ofCore (c₁ z).toCore
      exact ⟨(pf z ξ).adjoint, fun u v ↦ ((pf z ξ).adjoint_inner_right u v).symm⟩
    have hqiExists (z : M) (ξ : CotangentFiber (n := n) z) :
        ∃ qi : F₁ z →ₗ[ℂ] F₀ z, ∀ u v,
          (d₁ z).inner (qf z ξ u) v = (d₀ z).inner u (qi v) := by
      let moduleD : Module ℂ (F₀ z) := inferInstance
      let moduleD₁ : Module ℂ (F₁ z) := inferInstance
      let : NormedAddCommGroup (F₀ z) := (d₀ z).toNormedAddCommGroup
      let : Module ℂ (F₀ z) := moduleD
      let : InnerProductSpace ℂ (F₀ z) := InnerProductSpace.ofCore (d₀ z).toCore
      let : NormedAddCommGroup (F₁ z) := (d₁ z).toNormedAddCommGroup
      let : Module ℂ (F₁ z) := moduleD₁
      let : InnerProductSpace ℂ (F₁ z) := InnerProductSpace.ofCore (d₁ z).toCore
      exact ⟨(qf z ξ).adjoint, fun u v ↦ ((qf z ξ).adjoint_inner_right u v).symm⟩
    let pi (z : M) (ξ : CotangentFiber (n := n) z) :
        E₁ z →ₗ[ℂ] E₀ z := (hpiExists z ξ).choose
    let qi (z : M) (ξ : CotangentFiber (n := n) z) :
        F₁ z →ₗ[ℂ] F₀ z := (hqiExists z ξ).choose
    have hpi (z : M) (ξ : CotangentFiber (n := n) z) (u : E₀ z) (v : E₁ z) :
        (c₁ z).inner (pf z ξ u) v = (c₀ z).inner u (pi z ξ v) :=
      (hpiExists z ξ).choose_spec u v
    have hqi (z : M) (ξ : CotangentFiber (n := n) z) (u : F₀ z) (v : F₁ z) :
        (d₁ z).inner (qf z ξ u) v = (d₀ z).inner u (qi z ξ v) :=
      (hqiExists z ξ).choose_spec u v
    -- The supplied full representatives are those of the same four original corners.
    obtain ⟨qK, hqK, hclass⟩ := exists_tensorGlobalSymbol_of_gradedBundlePseudodifferentialOperator
      Nplus Nminus AA BB ePlus.linearEquiv eMinus.linearEquiv hPlus₀ hPlus₁ hMinus₀ hMinus₁
      hA hB U₀ V₀ U₁ V₁op K hK a₀ b₀ a₁ b₁ (ha₀ t) (hb₀ t) (ha₁ t) (hb₁ t)
      c₀ c₁ d₀ d₁ e₀₀ e₁₁ e₁₀ e₀₁ hk₁₁ hk₁₀ hk₀₁
      pf pi qf qi hpi hqi (ha₀tensor t) (hb₀tensor t) (ha₁tensor t) (hb₁tensor t)
    exact ⟨pi, qi, hpi, hqi, qK, hclass, hqK⟩

end AtiyahSinger
