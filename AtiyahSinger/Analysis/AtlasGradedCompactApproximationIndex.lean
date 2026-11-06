/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasMetricL2Equivalence
public import AtiyahSinger.Analysis.GradedCoreDomainComparison
public import AtiyahSinger.Analysis.FredholmPairApproximation

/-!
# The same atlas graph index through its actual compact vertical residuals

Public module ID: M0246.

The original four atlas presentations, metric inclusions and eight exact block
extensions give the two original closed graph domains. Their graph values
transport the original closed ranges, finite kernels and formal pairing to
these same bounded H1 realizations. Paired norm convergence then invokes the
existing Fredholm comparison, retaining the actual inclusion-induced quotient
maps. The same graph equivalences also make the original domain inclusions
into equivalences of the exact two kernels, giving the closed-kernel index
formula. The two original bounded L2 residuals and their literal adjoints produce compact
perturbations through the same four Rellich inclusions. The cutoff PDO family
is never altered: compact perturbation is used only in the bounded comparison,
and the final eventual index equality returns to the original cutoff family.
The original Green consequences and paired cutoff errors remain explicit inputs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open Filter
open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E₀₀ : M → Type*} [∀ x, AddCommGroup (E₀₀ x)] [∀ x, Module ℂ (E₀₀ x)]
  [TopologicalSpace (TotalSpace Unit E₀₀)]
  {X₀₀ : Type*} [NormedAddCommGroup X₀₀] [InnerProductSpace ℂ X₀₀]
  [CompleteSpace X₀₀]
  {E₁₀ : M → Type*} [∀ x, AddCommGroup (E₁₀ x)] [∀ x, Module ℂ (E₁₀ x)]
  [TopologicalSpace (TotalSpace Unit E₁₀)]
  {X₁₀ : Type*} [NormedAddCommGroup X₁₀] [InnerProductSpace ℂ X₁₀]
  [CompleteSpace X₁₀]
  {E₀₁ : M → Type*} [∀ x, AddCommGroup (E₀₁ x)] [∀ x, Module ℂ (E₀₁ x)]
  [TopologicalSpace (TotalSpace Unit E₀₁)]
  {X₀₁ : Type*} [NormedAddCommGroup X₀₁] [InnerProductSpace ℂ X₀₁]
  [CompleteSpace X₀₁]
  {E₁₁ : M → Type*} [∀ x, AddCommGroup (E₁₁ x)] [∀ x, Module ℂ (E₁₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁₁)]
  {X₁₁ : Type*} [NormedAddCommGroup X₁₁] [InnerProductSpace ℂ X₁₁]
  [CompleteSpace X₁₁]

omit [CompactSpace M] in
set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the paired compact approximations and original cutoff indices.
/-- Joint core bounds and paired compact approximation determine the original cutoff indices. -/
theorem exists_graded_index_eq_of_compact_approximation
    (A₀₀ : SmoothComplexBundleAtlas (n := n) E₀₀) (L₀₀ : AtlasBundlePresentation A₀₀)
    (i₀₀ : A₀₀.smoothSections →ₗ[ℂ] X₀₀)
    (Φ₀₀ : L₀₀.SobolevSpace 0 ≃L[ℂ] X₀₀)
    (hΦ₀₀ : ∀ u, Φ₀₀ (L₀₀.smoothToSobolev 0 u) = i₀₀ u)
    (A₁₀ : SmoothComplexBundleAtlas (n := n) E₁₀) (L₁₀ : AtlasBundlePresentation A₁₀)
    (i₁₀ : A₁₀.smoothSections →ₗ[ℂ] X₁₀)
    (Φ₁₀ : L₁₀.SobolevSpace 0 ≃L[ℂ] X₁₀)
    (hΦ₁₀ : ∀ u, Φ₁₀ (L₁₀.smoothToSobolev 0 u) = i₁₀ u)
    (A₀₁ : SmoothComplexBundleAtlas (n := n) E₀₁) (L₀₁ : AtlasBundlePresentation A₀₁)
    (i₀₁ : A₀₁.smoothSections →ₗ[ℂ] X₀₁)
    (Φ₀₁ : L₀₁.SobolevSpace 0 ≃L[ℂ] X₀₁)
    (hΦ₀₁ : ∀ u, Φ₀₁ (L₀₁.smoothToSobolev 0 u) = i₀₁ u)
    (A₁₁ : SmoothComplexBundleAtlas (n := n) E₁₁) (L₁₁ : AtlasBundlePresentation A₁₁)
    (i₁₁ : A₁₁.smoothSections →ₗ[ℂ] X₁₁)
    (Φ₁₁ : L₁₁.SobolevSpace 0 ≃L[ℂ] X₁₁)
    (hΦ₁₁ : ∀ u, Φ₁₁ (L₁₁.smoothToSobolev 0 u) = i₁₁ u)
    (H₀ : A₀₀.smoothSections →ₗ[ℂ] A₁₀.smoothSections)
    (H₀s : L₀₀.SobolevSpace 1 →L[ℂ] L₁₀.SobolevSpace 0)
    (hH₀s : ∀ u, H₀s (L₀₀.smoothToSobolev 1 u) = L₁₀.smoothToSobolev 0 (H₀ u))
    (V₀ : A₀₀.smoothSections →ₗ[ℂ] A₀₁.smoothSections)
    (V₀s : L₀₀.SobolevSpace 1 →L[ℂ] L₀₁.SobolevSpace 0)
    (hV₀s : ∀ u, V₀s (L₀₀.smoothToSobolev 1 u) = L₀₁.smoothToSobolev 0 (V₀ u))
    (V₁a : A₁₁.smoothSections →ₗ[ℂ] A₁₀.smoothSections)
    (V₁as : L₁₁.SobolevSpace 1 →L[ℂ] L₁₀.SobolevSpace 0)
    (hV₁as : ∀ u, V₁as (L₁₁.smoothToSobolev 1 u) = L₁₀.smoothToSobolev 0 (V₁a u))
    (H₁a : A₁₁.smoothSections →ₗ[ℂ] A₀₁.smoothSections)
    (H₁as : L₁₁.SobolevSpace 1 →L[ℂ] L₀₁.SobolevSpace 0)
    (hH₁as : ∀ u, H₁as (L₁₁.smoothToSobolev 1 u) = L₀₁.smoothToSobolev 0 (H₁a u))
    (H₀a : A₁₀.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
    (H₀as : L₁₀.SobolevSpace 1 →L[ℂ] L₀₀.SobolevSpace 0)
    (hH₀as : ∀ u, H₀as (L₁₀.smoothToSobolev 1 u) = L₀₀.smoothToSobolev 0 (H₀a u))
    (V₁ : A₁₀.smoothSections →ₗ[ℂ] A₁₁.smoothSections)
    (V₁s : L₁₀.SobolevSpace 1 →L[ℂ] L₁₁.SobolevSpace 0)
    (hV₁s : ∀ u, V₁s (L₁₀.smoothToSobolev 1 u) = L₁₁.smoothToSobolev 0 (V₁ u))
    (V₀a : A₀₁.smoothSections →ₗ[ℂ] A₀₀.smoothSections)
    (V₀as : L₀₁.SobolevSpace 1 →L[ℂ] L₀₀.SobolevSpace 0)
    (hV₀as : ∀ u, V₀as (L₀₁.smoothToSobolev 1 u) = L₀₀.smoothToSobolev 0 (V₀a u))
    (H₁ : A₀₁.smoothSections →ₗ[ℂ] A₁₁.smoothSections)
    (H₁s : L₀₁.SobolevSpace 1 →L[ℂ] L₁₁.SobolevSpace 0)
    (hH₁s : ∀ u, H₁s (L₀₁.smoothToSobolev 1 u) = L₁₁.smoothToSobolev 0 (H₁ u))
    (C₀₀ : ℝ) (hC₀₀ : 0 ≤ C₀₀)
    (hbound₀₀ : ∀ u, ‖L₀₀.smoothToSobolev 1 u‖ ≤
      C₀₀ * (‖i₀₀ u‖ + ‖i₁₀ (H₀ u)‖ + ‖i₀₁ (V₀ u)‖))
    (C₁₁ : ℝ) (hC₁₁ : 0 ≤ C₁₁)
    (hbound₁₁ : ∀ u, ‖L₁₁.smoothToSobolev 1 u‖ ≤
      C₁₁ * (‖i₁₁ u‖ + ‖i₁₀ (V₁a u)‖ + ‖i₀₁ (H₁a u)‖))
    (C₁₀ : ℝ) (hC₁₀ : 0 ≤ C₁₀)
    (hbound₁₀ : ∀ u, ‖L₁₀.smoothToSobolev 1 u‖ ≤
      C₁₀ * (‖i₁₀ u‖ + ‖i₀₀ (H₀a u)‖ + ‖i₁₁ (V₁ u)‖))
    (C₀₁ : ℝ) (hC₀₁ : 0 ≤ C₀₁)
    (hbound₀₁ : ∀ u, ‖L₀₁.smoothToSobolev 1 u‖ ≤
      C₀₁ * (‖i₀₁ u‖ + ‖i₀₀ (V₀a u)‖ + ‖i₁₁ (H₁ u)‖))
    (hcross : ∀ s t, inner ℂ (i₁₀ (H₀ s)) (i₁₀ (V₁a t)) =
      inner ℂ (i₀₁ (V₀ s)) (i₀₁ (H₁a t)))
    (hcrossa : ∀ s t, inner ℂ (i₀₀ (H₀a s)) (i₀₀ (V₀a t)) =
      inner ℂ (i₁₁ (V₁ s)) (i₁₁ (H₁ t))) :
    let Even := WithLp 2 (X₀₀ × X₁₁)
    let Odd := WithLp 2 (X₁₀ × X₀₁)
    let XE := WithLp 2 (L₀₀.SobolevSpace 1 × L₁₁.SobolevSpace 1)
    let XO := WithLp 2 (L₁₀.SobolevSpace 1 × L₀₁.SobolevSpace 1)
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ X₀₀ X₁₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ X₁₀ X₀₁
    let cXE := WithLp.prodContinuousLinearEquiv 2 ℂ
      (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)
    let cXO := WithLp.prodContinuousLinearEquiv 2 ℂ
      (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)
    let iEven := cEven.symm.toLinearMap.comp (i₀₀.prodMap i₁₁)
    let iOdd := cOdd.symm.toLinearMap.comp (i₁₀.prodMap i₀₁)
    let dSmooth := cOdd.symm.toLinearMap.comp
      (((i₁₀.comp H₀).coprod (-(i₁₀.comp V₁a))).prod
        ((i₀₁.comp V₀).coprod (i₀₁.comp H₁a)))
    let aSmooth := cEven.symm.toLinearMap.comp
      (((i₀₀.comp H₀a).coprod (i₀₀.comp V₀a)).prod
        ((-(i₁₁.comp V₁)).coprod (i₁₁.comp H₁)))
    let J₀₀ := Φ₀₀.toContinuousLinearMap.comp (L₀₀.sobolevInclusion 1 0 (by norm_num))
    let J₁₀ := Φ₁₀.toContinuousLinearMap.comp (L₁₀.sobolevInclusion 1 0 (by norm_num))
    let J₀₁ := Φ₀₁.toContinuousLinearMap.comp (L₀₁.sobolevInclusion 1 0 (by norm_num))
    let J₁₁ := Φ₁₁.toContinuousLinearMap.comp (L₁₁.sobolevInclusion 1 0 (by norm_num))
    let BH₀ := Φ₁₀.toContinuousLinearMap.comp H₀s
    let BV₀ := Φ₀₁.toContinuousLinearMap.comp V₀s
    let BV₁a := Φ₁₀.toContinuousLinearMap.comp V₁as
    let BH₁a := Φ₀₁.toContinuousLinearMap.comp H₁as
    let BH₀a := Φ₀₀.toContinuousLinearMap.comp H₀as
    let BV₁ := Φ₁₁.toContinuousLinearMap.comp V₁s
    let BV₀a := Φ₀₀.toContinuousLinearMap.comp V₀as
    let BH₁ := Φ₁₁.toContinuousLinearMap.comp H₁s
    let JE := cEven.symm.toContinuousLinearMap.comp
      ((J₀₀.prodMap J₁₁).comp cXE.toContinuousLinearMap)
    let JO := cOdd.symm.toContinuousLinearMap.comp
      ((J₁₀.prodMap J₀₁).comp cXO.toContinuousLinearMap)
    let TE := cOdd.symm.toContinuousLinearMap.comp
      (((BH₀.coprod (-BV₁a)).prod (BV₀.coprod BH₁a)).comp cXE.toContinuousLinearMap)
    let TO := cEven.symm.toContinuousLinearMap.comp
      (((BH₀a.coprod BV₀a).prod ((-BV₁).coprod BH₁)).comp cXO.toContinuousLinearMap)
    ∀ (D : Even →ₗ.[ℂ] Odd) (Da : Odd →ₗ.[ℂ] Even),
      D.IsClosed → Da.IsClosed →
      D.graph = (iEven.prod dSmooth).range.topologicalClosure →
      Da.graph = (iOdd.prod aSmooth).range.topologicalClosure →
      let Result (Tmap : XE →L[ℂ] Odd) (Smap : XO →L[ℂ] Even) : Prop :=
        letI : AddCommGroup (Even ⧸ Smap.range) := Submodule.Quotient.addCommGroup _
        letI : Module ℂ (Even ⧸ Smap.range) := Submodule.Quotient.module _
        letI : AddCommGroup (Odd ⧸ Tmap.range) := Submodule.Quotient.addCommGroup _
        letI : Module ℂ (Odd ⧸ Tmap.range) := Submodule.Quotient.module _
        Tmap.IsFredholm ∧ Smap.IsFredholm ∧ Tmap.index + Smap.index = 0 ∧
          ∃ e : ↥Tmap.ker ≃ₗ[ℂ] (Even ⧸ Smap.range),
            e.toLinearMap = Smap.range.mkQ.comp (JE.toLinearMap.comp Tmap.ker.subtype) ∧
            ∃ f : ↥Smap.ker ≃ₗ[ℂ] (Odd ⧸ Tmap.range),
              f.toLinearMap = Tmap.range.mkQ.comp (JO.toLinearMap.comp Smap.ker.subtype) ∧
              ∃ κE : ↥Tmap.ker ≃ₗ[ℂ] ↥D.ker,
                D.ker.subtype.comp κE.toLinearMap =
                  JE.toLinearMap.comp Tmap.ker.subtype ∧
                ∃ κO : ↥Smap.ker ≃ₗ[ℂ] ↥Da.ker,
                  Da.ker.subtype.comp κO.toLinearMap =
                    JO.toLinearMap.comp Smap.ker.subtype ∧
                  Tmap.index = (Module.finrank ℂ D.ker : ℤ) - Module.finrank ℂ Da.ker
      D.IsFormalAdjoint Da →
      IsClosed (D.toFun.range : Set Odd) → IsClosed (Da.toFun.range : Set Even) →
      FiniteDimensional ℂ D.ker → FiniteDimensional ℂ Da.ker →
      ∀ (W₀ : X₀₀ →L[ℂ] X₀₁) (W₁ : X₁₀ →L[ℂ] X₁₁),
      let pE₀ := (ContinuousLinearMap.fst ℂ
        (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)).comp cXE.toContinuousLinearMap
      let pE₁ := (ContinuousLinearMap.snd ℂ
        (L₀₀.SobolevSpace 1) (L₁₁.SobolevSpace 1)).comp cXE.toContinuousLinearMap
      let pO₀ := (ContinuousLinearMap.fst ℂ
        (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)).comp cXO.toContinuousLinearMap
      let pO₁ := (ContinuousLinearMap.snd ℂ
        (L₁₀.SobolevSpace 1) (L₀₁.SobolevSpace 1)).comp cXO.toContinuousLinearMap
      let WE : XE →L[ℂ] Odd :=
        cOdd.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inr ℂ X₁₀ X₀₁).comp
          (W₀.comp (J₀₀.comp pE₀))) +
        cOdd.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inl ℂ X₁₀ X₀₁).comp
          ((-W₁.adjoint).comp (J₁₁.comp pE₁)))
      let WO : XO →L[ℂ] Even :=
        cEven.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inl ℂ X₀₀ X₁₁).comp
          (W₀.adjoint.comp (J₀₁.comp pO₁))) +
        cEven.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inr ℂ X₀₀ X₁₁).comp
          ((-W₁).comp (J₁₀.comp pO₀)))
      ∀ {ι : Type*} (l : Filter ι) [l.NeBot]
        (Ts : ι → XE →L[ℂ] Odd) (Ss : ι → XO →L[ℂ] Even),
        Tendsto (fun a ↦ Ts a + WE) l (𝓝 TE) →
        Tendsto (fun a ↦ Ss a + WO) l (𝓝 TO) →
        (∀ᶠ a in l, (Ts a).IsFredholm ∧ (Ss a).IsFredholm) →
        (∀ᶠ a in l, (Ts a).index + (Ss a).index = 0) →
        Result TE TO ∧ ∀ᶠ a in l,
          (Ts a).index = (Module.finrank ℂ D.ker : ℤ) - Module.finrank ℂ Da.ker ∧
          (Ss a).index = -((Module.finrank ℂ D.ker : ℤ) - Module.finrank ℂ Da.ker) := by
  intro Even Odd XE XO cEven cOdd cXE cXO iEven iOdd dSmooth aSmooth
    J₀₀ J₁₀ J₀₁ J₁₁ BH₀ BV₀ BV₁a BH₁a BH₀a BV₁ BV₀a BH₁
    JE JO TE TO D Da hD hDa hgraph hgrapha Result hformal hDrange hDarange hDker hDaker
    W₀ W₁ pE₀ pE₁ pO₀ pO₁ WE WO ι l hl Ts Ss hTs hSs hFredholm hindex
  -- The same H1-to-L2 inclusions make the actual bounded residual blocks compact.
  have hcompact₀₀ : IsCompactOperator J₀₀ :=
    (L₀₀.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      Φ₀₀.toContinuousLinearMap
  have hcompact₁₀ : IsCompactOperator J₁₀ :=
    (L₁₀.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      Φ₁₀.toContinuousLinearMap
  have hcompact₀₁ : IsCompactOperator J₀₁ :=
    (L₀₁.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      Φ₀₁.toContinuousLinearMap
  have hcompact₁₁ : IsCompactOperator J₁₁ :=
    (L₁₁.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      Φ₁₁.toContinuousLinearMap
  have hWE : IsCompactOperator WE :=
    ((((hcompact₀₀.comp_clm pE₀).clm_comp W₀).clm_comp
      (ContinuousLinearMap.inr ℂ X₁₀ X₀₁)).clm_comp cOdd.symm.toContinuousLinearMap).add
      ((((hcompact₁₁.comp_clm pE₁).clm_comp (-W₁.adjoint)).clm_comp
        (ContinuousLinearMap.inl ℂ X₁₀ X₀₁)).clm_comp cOdd.symm.toContinuousLinearMap)
  have hWO : IsCompactOperator WO :=
    ((((hcompact₀₁.comp_clm pO₁).clm_comp W₀.adjoint).clm_comp
      (ContinuousLinearMap.inl ℂ X₀₀ X₁₁)).clm_comp cEven.symm.toContinuousLinearMap).add
      ((((hcompact₁₀.comp_clm pO₀).clm_comp (-W₁)).clm_comp
        (ContinuousLinearMap.inr ℂ X₀₀ X₁₁)).clm_comp cEven.symm.toContinuousLinearMap)
  have hFredholmW : ∀ᶠ a in l, (Ts a + WE).IsFredholm ∧ (Ss a + WO).IsFredholm :=
    hFredholm.mono fun a ha ↦
      ⟨isFredholm_add_compact (Ts a) WE ha.1 hWE,
        isFredholm_add_compact (Ss a) WO ha.2 hWO⟩
  have hindexW : ∀ᶠ a in l, (Ts a + WE).index + (Ss a + WO).index = 0 := by
    filter_upwards [hFredholm, hindex] with a ha hi
    rw [index_add_compact (Ts a) WE ha.1 hWE, index_add_compact (Ss a) WO ha.2 hWO]
    exact hi
  let ΓE := D.graph.comap (WithLp.linearEquiv 2 ℂ (Even × Odd)).toLinearMap
  let ΓO := Da.graph.comap (WithLp.linearEquiv 2 ℂ (Odd × Even)).toLinearMap
  -- Every inclusion and block uses the same original completion equivalence at its endpoint.
  have hJ₀₀ (u : A₀₀.smoothSections) : J₀₀ (L₀₀.smoothToSobolev 1 u) = i₀₀ u := by
    change Φ₀₀ (L₀₀.sobolevInclusion 1 0 (by norm_num) (L₀₀.smoothToSobolev 1 u)) = _
    exact (congrArg Φ₀₀ (L₀₀.sobolevInclusion_smoothToSobolev 1 0 (by norm_num) u)).trans
      (hΦ₀₀ u)
  have hJ₀₀inj : Function.Injective J₀₀ :=
    Φ₀₀.injective.comp (L₀₀.sobolevInclusion_injective 1 0 (by norm_num))
  have hJ₁₀ (u : A₁₀.smoothSections) : J₁₀ (L₁₀.smoothToSobolev 1 u) = i₁₀ u := by
    change Φ₁₀ (L₁₀.sobolevInclusion 1 0 (by norm_num) (L₁₀.smoothToSobolev 1 u)) = _
    exact (congrArg Φ₁₀ (L₁₀.sobolevInclusion_smoothToSobolev 1 0 (by norm_num) u)).trans
      (hΦ₁₀ u)
  have hJ₁₀inj : Function.Injective J₁₀ :=
    Φ₁₀.injective.comp (L₁₀.sobolevInclusion_injective 1 0 (by norm_num))
  have hJ₀₁ (u : A₀₁.smoothSections) : J₀₁ (L₀₁.smoothToSobolev 1 u) = i₀₁ u := by
    change Φ₀₁ (L₀₁.sobolevInclusion 1 0 (by norm_num) (L₀₁.smoothToSobolev 1 u)) = _
    exact (congrArg Φ₀₁ (L₀₁.sobolevInclusion_smoothToSobolev 1 0 (by norm_num) u)).trans
      (hΦ₀₁ u)
  have hJ₀₁inj : Function.Injective J₀₁ :=
    Φ₀₁.injective.comp (L₀₁.sobolevInclusion_injective 1 0 (by norm_num))
  have hJ₁₁ (u : A₁₁.smoothSections) : J₁₁ (L₁₁.smoothToSobolev 1 u) = i₁₁ u := by
    change Φ₁₁ (L₁₁.sobolevInclusion 1 0 (by norm_num) (L₁₁.smoothToSobolev 1 u)) = _
    exact (congrArg Φ₁₁ (L₁₁.sobolevInclusion_smoothToSobolev 1 0 (by norm_num) u)).trans
      (hΦ₁₁ u)
  have hJ₁₁inj : Function.Injective J₁₁ :=
    Φ₁₁.injective.comp (L₁₁.sobolevInclusion_injective 1 0 (by norm_num))
  have hBH₀ (u : A₀₀.smoothSections) : BH₀ (L₀₀.smoothToSobolev 1 u) = i₁₀ (H₀ u) :=
    (congrArg Φ₁₀ (hH₀s u)).trans (hΦ₁₀ (H₀ u))
  have hBV₀ (u : A₀₀.smoothSections) : BV₀ (L₀₀.smoothToSobolev 1 u) = i₀₁ (V₀ u) :=
    (congrArg Φ₀₁ (hV₀s u)).trans (hΦ₀₁ (V₀ u))
  have hBV₁a (u : A₁₁.smoothSections) : BV₁a (L₁₁.smoothToSobolev 1 u) = i₁₀ (V₁a u) :=
    (congrArg Φ₁₀ (hV₁as u)).trans (hΦ₁₀ (V₁a u))
  have hBH₁a (u : A₁₁.smoothSections) : BH₁a (L₁₁.smoothToSobolev 1 u) = i₀₁ (H₁a u) :=
    (congrArg Φ₀₁ (hH₁as u)).trans (hΦ₀₁ (H₁a u))
  have hBH₀a (u : A₁₀.smoothSections) : BH₀a (L₁₀.smoothToSobolev 1 u) = i₀₀ (H₀a u) :=
    (congrArg Φ₀₀ (hH₀as u)).trans (hΦ₀₀ (H₀a u))
  have hBV₁ (u : A₁₀.smoothSections) : BV₁ (L₁₀.smoothToSobolev 1 u) = i₁₁ (V₁ u) :=
    (congrArg Φ₁₁ (hV₁s u)).trans (hΦ₁₁ (V₁ u))
  have hBV₀a (u : A₀₁.smoothSections) : BV₀a (L₀₁.smoothToSobolev 1 u) = i₀₀ (V₀a u) :=
    (congrArg Φ₀₀ (hV₀as u)).trans (hΦ₀₀ (V₀a u))
  have hBH₁ (u : A₀₁.smoothSections) : BH₁ (L₀₁.smoothToSobolev 1 u) = i₁₁ (H₁ u) :=
    (congrArg Φ₁₁ (hH₁s u)).trans (hΦ₁₁ (H₁ u))
  -- Use the H¹ cores from the four specified atlas presentations.
  let coreE := cXE.symm.toLinearMap.comp
    ((L₀₀.smoothToSobolev 1).prodMap (L₁₁.smoothToSobolev 1))
  let coreO := cXO.symm.toLinearMap.comp
    ((L₁₀.smoothToSobolev 1).prodMap (L₀₁.smoothToSobolev 1))
  have hcoreE : ((JE.prod TE).toLinearMap.comp coreE) = iEven.prod dSmooth := by
    apply LinearMap.ext
    rintro ⟨s, t⟩
    apply Prod.ext <;> apply WithLp.ofLp_injective
    · change (J₀₀ (L₀₀.smoothToSobolev 1 s), J₁₁ (L₁₁.smoothToSobolev 1 t)) = _
      rw [hJ₀₀, hJ₁₁]
      rfl
    · change (BH₀ (L₀₀.smoothToSobolev 1 s) + -(BV₁a (L₁₁.smoothToSobolev 1 t)),
        BV₀ (L₀₀.smoothToSobolev 1 s) + BH₁a (L₁₁.smoothToSobolev 1 t)) = _
      rw [hBH₀, hBV₁a, hBV₀, hBH₁a]
      rfl
  have hcoreO : ((JO.prod TO).toLinearMap.comp coreO) = iOdd.prod aSmooth := by
    apply LinearMap.ext
    rintro ⟨s, t⟩
    apply Prod.ext <;> apply WithLp.ofLp_injective
    · change (J₁₀ (L₁₀.smoothToSobolev 1 s), J₀₁ (L₀₁.smoothToSobolev 1 t)) = _
      rw [hJ₁₀, hJ₀₁]
      rfl
    · change (BH₀a (L₁₀.smoothToSobolev 1 s) + BV₀a (L₀₁.smoothToSobolev 1 t),
        -BV₁ (L₁₀.smoothToSobolev 1 s) + BH₁ (L₀₁.smoothToSobolev 1 t)) = _
      rw [hBH₀a, hBV₀a, hBV₁, hBH₁]
      rfl
  have hdomains :
      (∃ ΨE : XE ≃L[ℂ] ΓE, ∀ x, (ΨE x).val = WithLp.toLp 2 (JE x, TE x)) ∧
      (∃ ΨO : XO ≃L[ℂ] ΓO, ∀ y, (ΨO y).val = WithLp.toLp 2 (JO y, TO y)) := by
    constructor
    · -- The even graph uses its original four block values and original cross pairing.
      apply LinearPMap.exists_graded_graphDomainEquiv_of_joint_core_bounds
        J₀₀ J₁₁ hJ₀₀inj hJ₁₁inj BH₀ BV₀ BV₁a BH₁a
        (L₀₀.smoothToSobolev 1) (L₁₁.smoothToSobolev 1)
        (L₀₀.denseRange_smoothToSobolev 1) (L₁₁.denseRange_smoothToSobolev 1)
        C₀₀ C₁₁ hC₀₀ hC₁₁
      · intro s
        simpa only [hJ₀₀, hBH₀, hBV₀] using hbound₀₀ s
      · intro t
        simpa only [hJ₁₁, hBV₁a, hBH₁a] using hbound₁₁ t
      · intro s t
        simpa only [hBH₀, hBV₁a, hBV₀, hBH₁a] using hcross s t
      · exact hD
      · exact hgraph.trans (congrArg (fun f ↦ f.range.topologicalClosure) hcoreE.symm)
    · -- Negating both vertical blocks gives the literal transpose without changing joint norms.
      have hzero₁ : - -BV₀a = BV₀a := neg_neg _
      have h := LinearPMap.exists_graded_graphDomainEquiv_of_joint_core_bounds
        J₁₀ J₀₁ hJ₁₀inj hJ₀₁inj BH₀a (-BV₁) (-BV₀a) BH₁
        (L₁₀.smoothToSobolev 1) (L₀₁.smoothToSobolev 1)
        (L₁₀.denseRange_smoothToSobolev 1) (L₀₁.denseRange_smoothToSobolev 1)
        C₁₀ C₀₁ hC₁₀ hC₀₁
        (fun s ↦ by simpa only [neg_apply, norm_neg, hJ₁₀, hBH₀a, hBV₁] using hbound₁₀ s)
        (fun t ↦ by simpa only [neg_apply, norm_neg, hJ₀₁, hBV₀a, hBH₁] using hbound₀₁ t)
        (fun s t ↦ by
          simpa only [neg_apply, inner_neg_left, inner_neg_right, hBH₀a, hBV₀a, hBV₁, hBH₁]
            using congrArg Neg.neg (hcrossa s t))
      simp only [hzero₁] at h
      exact h Da hDa (hgrapha.trans
        (congrArg (fun f ↦ f.range.topologicalClosure) hcoreO.symm))
  obtain ⟨⟨ΨE, hΨE⟩, ⟨ΨO, hΨO⟩⟩ := hdomains
  have hJE : Function.Injective JE := by
    intro x y hxy
    apply WithLp.ofLp_injective
    exact Prod.ext (hJ₀₀inj (congrArg (fun z : Even ↦ z.ofLp.1) hxy))
      (hJ₁₁inj (congrArg (fun z : Even ↦ z.ofLp.2) hxy))
  have hJO : Function.Injective JO := by
    intro x y hxy
    apply WithLp.ofLp_injective
    exact Prod.ext (hJ₁₀inj (congrArg (fun z : Odd ↦ z.ofLp.1) hxy))
      (hJ₀₁inj (congrArg (fun z : Odd ↦ z.ofLp.2) hxy))
  -- Both bounded realizations retain points of the actual two original closed graphs.
  have hgE (x : XE) : (JE x, TE x) ∈ D.graph := by
    have hx := (ΨE x).property
    change WithLp.ofLp (ΨE x).val ∈ D.graph at hx
    rw [hΨE] at hx
    exact hx
  have hgO (y : XO) : (JO y, TO y) ∈ Da.graph := by
    have hy := (ΨO y).property
    change WithLp.ofLp (ΨO y).val ∈ Da.graph at hy
    rw [hΨO] at hy
    exact hy
  have hTErange : TE.range = D.toFun.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact LinearPMap.mem_range_iff.mpr ⟨JE x, hgE x⟩
    · intro hy
      obtain ⟨x, hxy⟩ := LinearPMap.mem_range_iff.mp hy
      let z : ΓE := ⟨WithLp.toLp 2 (x, y), hxy⟩
      let w := ΨE.symm z
      have hw : WithLp.toLp 2 (JE w, TE w) = WithLp.toLp 2 (x, y) :=
        (hΨE w).symm.trans (congrArg Subtype.val (ΨE.apply_symm_apply z))
      exact ⟨w, congrArg (fun z : WithLp 2 (Even × Odd) ↦ z.ofLp.2) hw⟩
  have hTOrange : TO.range = Da.toFun.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact LinearPMap.mem_range_iff.mpr ⟨JO y, hgO y⟩
    · intro hx
      obtain ⟨y, hyx⟩ := LinearPMap.mem_range_iff.mp hx
      let z : ΓO := ⟨WithLp.toLp 2 (y, x), hyx⟩
      let w := ΨO.symm z
      have hw : WithLp.toLp 2 (JO w, TO w) = WithLp.toLp 2 (y, x) :=
        (hΨO w).symm.trans (congrArg Subtype.val (ΨO.apply_symm_apply z))
      exact ⟨w, congrArg (fun z : WithLp 2 (Odd × Even) ↦ z.ofLp.2) hw⟩
  -- The actual inclusions inject both bounded kernels into their original finite kernels.
  let fE : TE.ker →ₗ[ℂ] D.ker :=
    (JE.toLinearMap.comp TE.ker.subtype).codRestrict D.ker (fun x ↦ by
      obtain ⟨u, hu, hTu⟩ := D.mem_graph_iff.mp (hgE x.val)
      exact D.mem_ker_iff.mpr ⟨u, hu.symm, hTu.trans x.property⟩)
  let fO : TO.ker →ₗ[ℂ] Da.ker :=
    (JO.toLinearMap.comp TO.ker.subtype).codRestrict Da.ker (fun y ↦ by
      obtain ⟨v, hv, hTv⟩ := Da.mem_graph_iff.mp (hgO y.val)
      exact Da.mem_ker_iff.mpr ⟨v, hv.symm, hTv.trans y.property⟩)
  -- Every original zero-output graph point has a unique preimage under the same graph equivalence.
  have hfE : Function.Injective fE := fun x y hxy ↦
    Subtype.ext (hJE (congrArg Subtype.val hxy))
  have hfO : Function.Injective fO := fun x y hxy ↦
    Subtype.ext (hJO (congrArg Subtype.val hxy))
  have hfEsurj : Function.Surjective fE := by
    intro u
    have hg : (u.val, (0 : Odd)) ∈ D.graph := by
      obtain ⟨v, hv, hzero⟩ := D.mem_ker_iff.mp u.property
      rw [hv]
      exact D.mem_graph_iff'.mpr ⟨v, Prod.ext rfl hzero⟩
    let z : ΓE := ⟨WithLp.toLp 2 (u.val, 0), hg⟩
    let w := ΨE.symm z
    have hw : WithLp.toLp 2 (JE w, TE w) = WithLp.toLp 2 (u.val, 0) :=
      (hΨE w).symm.trans (congrArg Subtype.val (ΨE.apply_symm_apply z))
    have hzero : TE w = 0 :=
      congrArg (fun z : WithLp 2 (Even × Odd) ↦ z.ofLp.2) hw
    refine ⟨⟨w, hzero⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : WithLp 2 (Even × Odd) ↦ z.ofLp.1) hw
  have hfOsurj : Function.Surjective fO := by
    intro u
    have hg : (u.val, (0 : Even)) ∈ Da.graph := by
      obtain ⟨v, hv, hzero⟩ := Da.mem_ker_iff.mp u.property
      rw [hv]
      exact Da.mem_graph_iff'.mpr ⟨v, Prod.ext rfl hzero⟩
    let z : ΓO := ⟨WithLp.toLp 2 (u.val, 0), hg⟩
    let w := ΨO.symm z
    have hw : WithLp.toLp 2 (JO w, TO w) = WithLp.toLp 2 (u.val, 0) :=
      (hΨO w).symm.trans (congrArg Subtype.val (ΨO.apply_symm_apply z))
    have hzero : TO w = 0 :=
      congrArg (fun z : WithLp 2 (Odd × Even) ↦ z.ofLp.2) hw
    refine ⟨⟨w, hzero⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : WithLp 2 (Odd × Even) ↦ z.ofLp.1) hw
  let κE : TE.ker ≃ₗ[ℂ] D.ker := LinearEquiv.ofBijective fE ⟨hfE, hfEsurj⟩
  let κO : TO.ker ≃ₗ[ℂ] Da.ker := LinearEquiv.ofBijective fO ⟨hfO, hfOsurj⟩
  let := hDker
  let := hDaker
  have hTEker : FiniteDimensional ℂ TE.ker :=
    FiniteDimensional.of_injective fE (fun x y hxy ↦
      Subtype.ext (hJE (congrArg Subtype.val hxy)))
  have hTOker : FiniteDimensional ℂ TO.ker :=
    FiniteDimensional.of_injective fO (fun x y hxy ↦
      Subtype.ext (hJO (congrArg Subtype.val hxy)))
  have hpair (x : XE) (y : XO) : inner ℂ (TE x) (JO y) = inner ℂ (JE x) (TO y) := by
    obtain ⟨u, hu, hTu⟩ := D.mem_graph_iff.mp (hgE x)
    obtain ⟨v, hv, hTv⟩ := Da.mem_graph_iff.mp (hgO y)
    have h := hformal u v
    rw [hu, hv, hTu, hTv] at h
    exact h
  -- The same parameter filter compares the two original fixed H1 realizations.
  dsimp only [Result]
  obtain ⟨hTE, hTO, hsum, e, he, f, hf⟩ :=
    exists_ker_coker_equiv_of_formalAdjoint_of_tendsto
      TE TO JE.toLinearMap JO.toLinearMap hJE hJO hpair
      (by rwa [hTErange]) (by rwa [hTOrange]) hTEker hTOker
      l (fun a ↦ Ts a + WE) (fun a ↦ Ss a + WO) hTs hSs hFredholmW hindexW
  -- The actual quotient and graph-kernel maps compute the original limiting index.
  have hkernelIndex : TE.index =
      (Module.finrank ℂ D.ker : ℤ) - Module.finrank ℂ Da.ker := by
    rw [LinearMap.index_eq_finrank_sub, κE.finrank_eq, ← f.finrank_eq, κO.finrank_eq]
  have hTindex : ∀ᶠ a in l, (Ts a).index = TE.index := by
    filter_upwards [hTs.eventually hTE.eventually_nhds_index_eq, hFredholm] with a ha hF
    exact (index_add_compact (Ts a) WE hF.1 hWE).symm.trans ha
  have hSindex : ∀ᶠ a in l, (Ss a).index = TO.index := by
    filter_upwards [hSs.eventually hTO.eventually_nhds_index_eq, hFredholm] with a ha hF
    exact (index_add_compact (Ss a) WO hF.2 hWO).symm.trans ha
  refine ⟨?_, ?_⟩
  · refine ⟨hTE, hTO, hsum, e, ?_, f, ?_, κE, ?_, κO, ?_, hkernelIndex⟩
    · apply LinearMap.ext
      exact he
    · apply LinearMap.ext
      exact hf
    · rfl
    · rfl
  · -- Return to the actual cutoff family, whose index was never changed by the comparison.
    filter_upwards [hTindex, hSindex] with a ha hb
    constructor
    · exact ha.trans hkernelIndex
    · rw [hb]
      omega

end AtiyahSinger
