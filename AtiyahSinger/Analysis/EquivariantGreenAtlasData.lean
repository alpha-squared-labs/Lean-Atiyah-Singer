/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Analysis.EquivariantSmoothGreenOperator
public import AtiyahSinger.Analysis.MetricL2AtlasSobolev

/-!
# Actual equivariant Green data in the original native atlases

Public module ID: M0518.

The original elliptic PDO determines its canonical smooth Green map and
orthogonal kernel projection. These same maps are equivariant and transport
to the original native atlases, preserving the full Green and kernel identities.
Their H⁰ realizations use the given two presentations and original metrics.
This supplies the actual sphere operators and bounded inputs for the associated
vertical construction, without replacing the elliptic operator or its kernel.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
  (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    ∀ (g : G) (x : M) (u v : E.Fiber x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : G) (x : M) (u v : F.Fiber x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
  (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
    E.Fiber F.Fiber μ 1)
  (hPg : P.IsEquivariant IG σE σF hσE hσF)


include hPg hInvariant kInvariant hμInvariant

set_option maxHeartbeats 1200000 in
-- Preserve both native-to-atlas maps, the actual finite kernel and the two H⁰ presentations.
/-- The original equivariant elliptic PDO has actual atlas Green and kernel-projection data. -/
theorem PseudodifferentialOperator.exists_equivariantGreenAtlasData
    (A : SmoothBundlePresentation (n := n) (r := E.rank) E.Fiber)
    (B : SmoothBundlePresentation (n := n) (r := F.rank) F.Fiber) (hP : P.IsElliptic) :
    let W : Submodule ℂ (h.SmoothL2Section μ) := P.toLinearMap.ker
    letI : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let AE := nativeSmoothComplexBundleAtlas (n := n) (r := E.rank) E.Fiber
    let AF := nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber
    let hAE := σE.isSmoothAtlas_native IG hσE
    let hAF := σF.isSmoothAtlas_native IG hσF
    let en := nativeSmoothSectionLinearEquiv (n := n) (r := E.rank) E.Fiber
    let Q := P.toAtlasPseudodifferentialOperator
    ∃ (R : AtlasPseudodifferentialOperator AF AE (-1))
      (J : AtlasPseudodifferentialOperator AE AE 0),
      R.IsEquivariant IG σF σE hAF hAE ∧ J.IsEquivariant IG σE σE hAE hAE ∧
      (∀ u : AE.smoothSections, J.toLinearMap u = en.symm (W.starProjection (en u))) ∧
      Q.toLinearMap.comp J.toLinearMap = 0 ∧
      R.toLinearMap.comp Q.toLinearMap = LinearMap.id - J.toLinearMap ∧
      ∃ R₀ : B.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
          A.toAtlasBundlePresentation.SobolevSpace 0,
        (∀ u, R₀ (B.toAtlasBundlePresentation.smoothToSobolev 0 u) =
          A.toAtlasBundlePresentation.smoothToSobolev 0 (R.toLinearMap u)) ∧
        ∃ J₀ : A.toAtlasBundlePresentation.SobolevSpace 0 →L[ℂ]
            A.toAtlasBundlePresentation.SobolevSpace 0,
          ∀ u, J₀ (A.toAtlasBundlePresentation.smoothToSobolev 0 u) =
            A.toAtlasBundlePresentation.smoothToSobolev 0 (J.toLinearMap u) := by
  classical
  intro W
  let : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  intro AE AF hAE hAF en Q
  let en' := nativeSmoothSectionLinearEquiv (n := n) (r := F.rank) F.Fiber
  -- Construct the original bounded Green solution, then prove PDO membership and equivariance.
  obtain ⟨Green, hGP, hPG, horth, hunique⟩ := P.exists_smoothGreenOperator h k A B hP
  have hGreen := P.isPseudodifferentialOperator_smoothGreenOperator h k A B hP Green hGP hPG
  let Rn : PseudodifferentialOperator (n := n) (r := F.rank) (q := E.rank)
      F.Fiber E.Fiber μ (-1) := ⟨Green.toLinearMap, hGreen⟩
  have hRn : Rn.IsEquivariant IG σF σE hσF hσE :=
    P.isEquivariant_smoothGreenOperator IG E F σE σF hσE hσF h k
      hInvariant kInvariant μ hμInvariant hPg A B hP Green hGreen hPG horth hunique
  let green : smoothSections (n := n) (r := F.rank) F.Fiber →ₗ[ℂ]
      smoothSections (n := n) (r := E.rank) E.Fiber := Green.toLinearMap
  let K := smoothOrthogonalProjection μ h W
  let Jn : PseudodifferentialOperator (n := n) (r := E.rank) (q := E.rank)
      E.Fiber E.Fiber μ 0 :=
    ⟨K, (isSmoothingOperator_smoothOrthogonalProjection μ h W).isPseudodifferentialOperator 0 K⟩
  have hgp (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      green (P.toLinearMap u) = u - K u := hGP u
  have hK (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      K u = u - green (P.toLinearMap u) := by
    rw [hgp]
    abel
  let actE := σE.smoothSectionRepresentation IG hσE
  let actF := σF.smoothSectionRepresentation IG hσF
  -- The exact Green identity makes the same kernel projection intertwine the original action.
  have hJn : Jn.IsEquivariant IG σE σE hσE hσE := by
    intro g
    apply LinearMap.ext
    intro u
    change K (actE g u) = actE g (K u)
    have hPeq : P.toLinearMap (actE g u) = actF g (P.toLinearMap u) :=
      LinearMap.congr_fun (hPg g) u
    have hReq : green (actF g (P.toLinearMap u)) = actE g (green (P.toLinearMap u)) :=
      LinearMap.congr_fun (hRn g) (P.toLinearMap u)
    rw [hK, hK, map_sub, hPeq, hReq]
  let R := Rn.toAtlasPseudodifferentialOperator
  let J := Jn.toAtlasPseudodifferentialOperator
  have hRg : R.IsEquivariant IG σF σE hAF hAE :=
    (Rn.isEquivariant_toAtlas_iff IG σF σE hσF hσE).mpr hRn
  have hJg : J.IsEquivariant IG σE σE hAE hAE :=
    (Jn.isEquivariant_toAtlas_iff IG σE σE hσE hσE).mpr hJn
  refine ⟨R, J, hRg, hJg, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · -- The projection lands in the actual full kernel before the original atlas transport.
    apply LinearMap.ext
    intro u
    change en'.symm (P.toLinearMap (en (en.symm (K (en u))))) = 0
    rw [en.apply_symm_apply]
    have hz : P.toLinearMap (K (en u)) = 0 := W.starProjection_apply_mem (en u)
    exact (congrArg en'.symm hz).trans en'.symm.map_zero
  · -- Conjugation by the same native section maps retains the complete Green identity.
    apply LinearMap.ext
    intro u
    change en.symm (green (en' (en'.symm (P.toLinearMap (en u))))) =
      u - en.symm (K (en u))
    rw [en'.apply_symm_apply, hgp, map_sub, en.symm_apply_apply]
  · -- The original two presentations realize these same bounded smooth maps on atlas H⁰.
    obtain ⟨R₀, hR₀⟩ := exists_nativeAtlasSobolevZeroRealization k h B A Green
    obtain ⟨J₀, hJ₀⟩ := exists_nativeAtlasSobolevZeroRealization h h A A W.starProjection
    exact ⟨R₀, hR₀, J₀, hJ₀⟩

end AtiyahSinger
