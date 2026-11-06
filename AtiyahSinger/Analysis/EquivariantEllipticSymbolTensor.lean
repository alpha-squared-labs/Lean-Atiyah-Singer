/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolIndexTensor
public import AtiyahSinger.Geometry.EquivariantNativeTensor
public import AtiyahSinger.Topology.EquivariantRepresentationNaturality

/-!
# Actual representation tensors of homogeneous elliptic symbols

Public module ID: M0505.

One tensor representative simultaneously realizes the representation-ring
action on the original equivariant support K class and multiplication of
the full analytic index. The native models, finite coordinate symbol, and
the original tensor triple use the same bundle comparisons throughout.
This is the geometric finite-coefficient step in SG III.9 and III.13;
virtual coefficients and arbitrary clopen families are handled by descent.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct BigOperators

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] trivialTopology isFiniteRank_trivial tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback t2Space_cotangent locallyCompactSpace_cotangent

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
-- One construction carries four native bundles and the original tensor boundary comparison.
/-- An actual representation tensor multiplies both the original K class and full index. -/
theorem EquivariantEllipticSymbolData.exists_tensor
    (a : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
    (ρ : FiniteContinuousRepresentation G) :
    ∃ b : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G),
      b.kClass = finiteRepresentationClass ρ • a.kClass ∧
        b.index = finiteRepresentationClass ρ * a.index := by
  classical
  let IG := 𝓘(ℝ, VG)
  let E₀ := a.source
  let F₀ := a.target
  let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  -- Retain the original representation tensor and the same two native comparisons.
  obtain ⟨E, _, σE, hσE, e, heg, hjE, hpE, hcE⟩ :=
    exists_equivariant_native_smooth_tensor ρ a.sourceAction a.source_smooth
  obtain ⟨F, _, σF, hσF, f, hfg, hjF, hpF, hcF⟩ :=
    exists_equivariant_native_smooth_tensor ρ a.targetAction a.target_smooth
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let c (x : M) := (e.linearEquiv x).symm.trans (finiteTensorCoordinates ρ.dimension (E₀.Fiber x))
  let d (x : M) := (f.linearEquiv x).symm.trans (finiteTensorCoordinates ρ.dimension (F₀.Fiber x))
  have hcg (g : G) (x : M) (v : E.Fiber x) (i : Fin ρ.dimension) :
      c (g • x) (σE.linearMap g x v) i = ∑ j,
        ρ.representation g (Pi.single j 1) i • a.sourceAction.linearMap g x (c x v j) :=
    hcE g x v i
  have hdg (g : G) (x : M) (v : F.Fiber x) (i : Fin ρ.dimension) :
      d (g • x) (σF.linearMap g x v) i = ∑ j,
        ρ.representation g (Pi.single j 1) i • a.targetAction.linearMap g x (d x v j) :=
    hcF g x v i
  -- Standard insertions are the inverses of precisely these finite tensor coordinates.
  have hinverse (A T : SmoothFiniteComplexBundle (n := n) M)
      (e : ∀ x, ((Fin ρ.dimension → ℂ) ⊗[ℂ] A.Fiber x) ≃ₗ[ℂ] T.Fiber x)
      (x : M) (i : Fin ρ.dimension) (v : A.Fiber x) :
      ((e x).symm.trans (finiteTensorCoordinates ρ.dimension (A.Fiber x))).symm
          (Pi.single i v) = e x (Pi.single i 1 ⊗ₜ[ℂ] v) := by
    apply ((e x).symm.trans (finiteTensorCoordinates ρ.dimension (A.Fiber x))).injective
    rw [LinearEquiv.apply_symm_apply]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      finiteTensorCoordinates, TensorProduct.comm_tmul, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    ext j
    by_cases h : j = i <;> simp [h]
  have hjc (i : Fin ρ.dimension) : IsSmoothBundleMap (n := n) (r := E₀.rank) (q := E.rank)
      (fun x ↦ (c x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)) := by
    convert hjE i using 1
    funext x
    apply LinearMap.ext
    intro v
    exact hinverse E₀ E e.linearEquiv x i v
  have hjd (i : Fin ρ.dimension) : IsSmoothBundleMap (n := n) (r := F₀.rank) (q := F.rank)
      (fun x ↦ (d x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)) := by
    convert hjF i using 1
    funext x
    apply LinearMap.ext
    intro v
    exact hinverse F₀ F f.linearEquiv x i v
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  choose α hα _ using fun i : Fin ρ.dimension ↦
    exists_homogeneousSymbol_smoothBundleMap (μ := μ)
      (fun x ↦ (LinearMap.proj i).comp (c x).toLinearMap) (hpE i)
  choose β hβ _ using fun i : Fin ρ.dimension ↦
    exists_homogeneousSymbol_smoothBundleMap (μ := μ)
      (fun x ↦ (d x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)) (hjd i)
  let t (i : Fin ρ.dimension) : homogeneousGlobalSymbolSpace (n := n)
      (r := E.rank) (q := F₀.rank) E.Fiber F₀.Fiber 0 :=
    ⟨globalSymbolComp a.symbol.val (α i).val,
      a.symbol.property.1.globalSymbolComp (α i).property.1,
      by simpa only [zero_add] using a.symbol.property.2.globalSymbolComp (α i).property.2⟩
  let s (i : Fin ρ.dimension) : homogeneousGlobalSymbolSpace (n := n)
      (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0 :=
    ⟨globalSymbolComp (β i).val (t i).val,
      (β i).property.1.globalSymbolComp (t i).property.1,
      by simpa only [zero_add] using (β i).property.2.globalSymbolComp (t i).property.2⟩
  let S := ∑ i, s i
  have hvalue (x : M) (ξ : CotangentFiber (n := n) x) (v : E.Fiber x)
      (i : Fin ρ.dimension) : d x (S.val x ξ v) i = a.symbol.val x ξ (c x v i) := by
    change d x ((∑ j, s j).val x ξ v) i = _
    simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply, map_sum]
    have hs (j : Fin ρ.dimension) :
        (s j).val x ξ v = (d x).symm (Pi.single j (a.symbol.val x ξ (c x v j))) := by
      change (β j).val x ξ (a.symbol.val x ξ ((α j).val x ξ v)) = _
      rw [hα, hβ]
      rfl
    simp_rw [hs, LinearEquiv.apply_symm_apply]
    simp
  have hi : IsEllipticGlobalSymbol E.Fiber F.Fiber S.val := by
    intro x ξ hξ
    let L := (c x).trans ((LinearEquiv.piCongrRight fun _ : Fin ρ.dimension ↦
      LinearEquiv.ofBijective (a.symbol.val x ξ).toLinearMap (a.elliptic x ξ hξ)).trans
        (d x).symm)
    have heq : ⇑(S.val x ξ) = L := by
      funext v
      apply (d x).injective
      funext i
      change d x (S.val x ξ v) i =
        d x ((d x).symm (fun j ↦ a.symbol.val x ξ (c x v j))) i
      rw [LinearEquiv.apply_symm_apply]
      exact hvalue x ξ v i
    rw [heq]
    exact L.bijective
  -- The finite-coordinate square intertwines the full original moving-fiber actions.
  have hcov := (equivariantGlobalSymbolLinearMap_eq_iff
    IG a.sourceAction a.targetAction a.symbol.val).mp a.equivariant
  have hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g S.val x ξ = S.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF S.val).mpr
    intro g x ξ hξ v
    apply (d (g • x)).injective
    funext i
    rw [hvalue, hcg, hdg]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hcov g x ξ hξ, hvalue]
  let b : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G) := {
    source := E
    target := F
    sourceAction := σE
    targetAction := σF
    source_smooth := hσE
    target_smooth := hσF
    symbol := S
    elliptic := hi
    equivariant := hs }
  refine ⟨b, ?_, ?_⟩
  · let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let πM := cotangentProjection (n := n) (M := M)
    let A := EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E₀.Fiber))
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F₀.Fiber))
      (ellipticSymbolTriple a.symbol.val a.symbol.property.1.continuous a.elliptic)
      (a.sourceAction.pullback πM (fun _ _ ↦ rfl))
      (a.targetAction.pullback πM (fun _ _ ↦ rfl))
      (ellipticSymbolTriple_isEquivariant IG a.sourceAction a.targetAction a.symbol.val
        a.symbol.property.1.continuous a.elliptic a.equivariant)
    let B := EquivariantSupportBundleTriple.ofBoundary
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ E.Fiber))
      (FiniteBundle.ofFamily ((πM : _ → M) *ᵖ F.Fiber))
      (ellipticSymbolTriple S.val S.property.1.continuous hi)
      (σE.pullback πM (fun _ _ ↦ rfl)) (σF.pullback πM (fun _ _ ↦ rfl))
      (ellipticSymbolTriple_isEquivariant IG σE σF S.val S.property.1.continuous hi hs)
    let u (J : FiniteBundle M) :=
      (pullbackTensorIso (E := (FiniteBundle.trivial M ρ.dimension).Fiber)
        (F := J.Fiber) πM).trans
        ((pullbackTrivialIso πM ρ.dimension).tensor (Iso.refl (J.pullback πM).Fiber))
    have hu (J : FiniteBundle M) (z : CotangentTotalSpace (n := n) (M := M))
        (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber z.proj) :
        (u J).linearEquiv z v = v := by
      have hl : ((u J).linearEquiv z).toLinearMap = LinearMap.id := by
        apply TensorProduct.ext'
        intro t w
        change (pullbackTrivialIso πM ρ.dimension).linearEquiv z t ⊗ₜ[ℂ] w = t ⊗ₜ[ℂ] w
        rw [pullbackTrivialIso_apply]
      exact DFunLike.congr_fun hl v
    let jE := (u (FiniteBundle.ofFamily E₀.Fiber)).symm.trans (e.pullback πM)
    let jF := (u (FiniteBundle.ofFamily F₀.Fiber)).symm.trans (f.pullback πM)
    have hjEval (J T : FiniteBundle M) (e : Iso
        (fun x ↦ (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber x) T.Fiber)
        (z : CotangentTotalSpace (n := n) (M := M))
        (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] J.Fiber z.proj) :
        ((u J).symm.trans (e.pullback πM)).linearEquiv z v = e.linearEquiv z.proj v := by
      change e.linearEquiv z.proj (((u J).linearEquiv z).symm v) = _
      have hv : ((u J).linearEquiv z).symm v = v := by
        apply ((u J).linearEquiv z).injective
        rw [LinearEquiv.apply_symm_apply, hu]
      rw [hv]
    have hjE (z : CotangentTotalSpace (n := n) (M := M)) (v) :
        jE.linearEquiv z v = e.linearEquiv z.proj v :=
      hjEval (FiniteBundle.ofFamily E₀.Fiber) (FiniteBundle.ofFamily E.Fiber) e z v
    have hjF (z : CotangentTotalSpace (n := n) (M := M)) (v) :
        jF.linearEquiv z v = f.linearEquiv z.proj v :=
      hjEval (FiniteBundle.ofFamily F₀.Fiber) (FiniteBundle.ofFamily F.Fiber) f z v
    -- The original tensor triple and this symbol share the same zero-section control.
    have hIso : (A.tensorRepresentation ρ).IsIsomorphic B := by
      refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet,
        B.2.isEquivariant.invariant_control, Set.Subset.rfl, Set.Subset.rfl,
        jE, jF, ?_, ?_, ?_⟩
      · intro g z v
        change jE.linearEquiv (g • z)
          (TensorProduct.map (ρ.representation g).toLinearMap
            (a.sourceAction.linearMap g z.proj) v) =
          σE.linearMap g z.proj (jE.linearEquiv z v)
        rw [hjE, hjE]
        exact heg g z.proj v
      · intro g z v
        change jF.linearEquiv (g • z)
          (TensorProduct.map (ρ.representation g).toLinearMap
            (a.targetAction.linearMap g z.proj) v) =
          σF.linearMap g z.proj (jF.linearEquiv z v)
        rw [hjF, hjF]
        exact hfg g z.proj v
      · intro z v
        simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
        change jF.linearEquiv z.val
          (((ellipticSymbolTriple a.symbol.val
            a.symbol.property.1.continuous a.elliptic).boundary.tensorLeft
              (FiniteBundle.trivial _ ρ.dimension).Fiber).linearEquiv z v) =
          (ellipticSymbolTriple S.val S.property.1.continuous hi).boundary.linearEquiv z
            (jE.linearEquiv z.val v)
        rw [hjF, hjE]
        induction v using TensorProduct.inductionOn with
        | tmul t w =>
          rw [RelativeTriple.tensorLeft_tmul, ellipticSymbolTriple_boundary_apply,
            ellipticSymbolTriple_boundary_apply]
          apply (d z.val.proj).injective
          funext i
          rw [hvalue]
          simp only [d, c, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
          have hpure (V : Type) [AddCommGroup V] [Module ℂ V]
              (u : Fin ρ.dimension → ℂ) (v : V) :
              finiteTensorCoordinates ρ.dimension V (u ⊗ₜ[ℂ] v) i = u i • v := by
            simp [finiteTensorCoordinates, TensorProduct.piScalarRight_apply,
              TensorProduct.piScalarRightHom_tmul]
          exact (hpure (F₀.Fiber z.val.proj) t (a.symbol.val z.val.proj z.val.snd w)).trans
            (((a.symbol.val z.val.proj z.val.snd).map_smul (t i) w).symm.trans
              (congrArg (a.symbol.val z.val.proj z.val.snd)
                (hpure (E₀.Fiber z.val.proj) t w).symm))
        | add v w hv hw => simp only [map_add, hv, hw]
    change B.kZeroClass = equivariantSupportRepresentationAction
      (finiteRepresentationClass ρ) A.kZeroClass
    rw [equivariantSupportRepresentationAction_finiteClass]
    exact (equivariantSupportTripleKZero_generator_relations.1 _ _ hIso).symm
  · exact EquivariantEllipticSymbolData.index_eq_mul_of_fiberEquiv ρ a b c d
      hpE hjc hpF hjd hcE hcF (fun x ξ _ v i ↦ hvalue x ξ v i)

end AtiyahSinger
