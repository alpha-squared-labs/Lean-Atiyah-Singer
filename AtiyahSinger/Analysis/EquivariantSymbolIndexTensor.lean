/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantEllipticSymbolData
public import AtiyahSinger.Analysis.EquivariantSmoothIndexFiniteTensor
public import AtiyahSinger.Analysis.EquivariantSmoothSymbolIndex
public import AtiyahSinger.Analysis.HomogeneousSymbolOperatorComposition
public import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol

/-!
# Tensor coordinates and the full symbol index

Public module ID: M0595.

A specified smooth finite-coordinate bundle equivalence gives an actual tensor
operator, with the original representation matrices mixing its coordinates.
Its principal symbol, section action, and kernel/cokernel comparison all use
that same operator. This is the finite coefficient step of representation-ring
linearity; arbitrary virtual coefficients and K classes are handled separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
-- One finite coordinate square retains four bundles and their actual PDO principal classes.
/-- Actual smooth tensor coordinates multiply the full homogeneous-symbol index. -/
theorem EquivariantEllipticSymbolData.index_eq_mul_of_fiberEquiv
    (ρ : FiniteContinuousRepresentation G)
    (a b : EquivariantEllipticSymbolData (n := n) (M := M) (VG := VG) (G := G))
    (e : ∀ x, b.source.Fiber x ≃ₗ[ℂ] (Fin ρ.dimension → a.source.Fiber x))
    (f : ∀ x, b.target.Fiber x ≃ₗ[ℂ] (Fin ρ.dimension → a.target.Fiber x))
    (he : ∀ i, IsSmoothBundleMap (n := n) (r := b.source.rank) (q := a.source.rank)
      (fun x ↦ (LinearMap.proj i).comp (e x).toLinearMap))
    (heInv : ∀ i, IsSmoothBundleMap (n := n) (r := a.source.rank) (q := b.source.rank)
      (fun x ↦ (e x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)))
    (hf : ∀ i, IsSmoothBundleMap (n := n) (r := b.target.rank) (q := a.target.rank)
      (fun x ↦ (LinearMap.proj i).comp (f x).toLinearMap))
    (hfInv : ∀ i, IsSmoothBundleMap (n := n) (r := a.target.rank) (q := b.target.rank)
      (fun x ↦ (f x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)))
    (heg : letI := modelTopology (EuclideanSpace ℂ (Fin b.source.rank)) b.source.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin a.source.rank)) a.source.Fiber
      ∀ g x v i, e (g • x) (b.sourceAction.linearMap g x v) i =
      ∑ j, ρ.representation g (Pi.single j 1) i •
        a.sourceAction.linearMap g x (e x v j))
    (hfg : letI := modelTopology (EuclideanSpace ℂ (Fin b.target.rank)) b.target.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin a.target.rank)) a.target.Fiber
      ∀ g x v i, f (g • x) (b.targetAction.linearMap g x v) i =
      ∑ j, ρ.representation g (Pi.single j 1) i •
        a.targetAction.linearMap g x (f x v j))
    (hsymbol : ∀ x ξ, ξ ≠ 0 → ∀ v i,
      f x (b.symbol.val x ξ v) i = a.symbol.val x ξ (e x v i)) :
    b.index = finiteRepresentationClass ρ * a.index := by
  classical
  let IG := 𝓘(ℝ, VG)
  let := modelTopology (EuclideanSpace ℂ (Fin b.source.rank)) b.source.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin a.source.rank)) a.source.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin b.target.rank)) b.target.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin a.target.rank)) a.target.Fiber
  -- Smooth projections and insertions give the genuine finite section equivalences.
  have sectionEquiv (A E : SmoothFiniteComplexBundle (n := n) M)
      (d : ∀ x, A.Fiber x ≃ₗ[ℂ] (Fin ρ.dimension → E.Fiber x))
      (hp : ∀ i, IsSmoothBundleMap (n := n) (r := A.rank) (q := E.rank)
        (fun x ↦ (LinearMap.proj i).comp (d x).toLinearMap))
      (hj : ∀ i, IsSmoothBundleMap (n := n) (r := E.rank) (q := A.rank)
        (fun x ↦ (d x).symm.toLinearMap.comp (LinearMap.single ℂ _ i))) :
      ∃ S : smoothSections (n := n) (r := A.rank) A.Fiber ≃ₗ[ℂ]
          (Fin ρ.dimension → smoothSections (n := n) (r := E.rank) E.Fiber),
        ∀ u i x, (S u i).val x = d x (u.val x) i := by
    let p (i : Fin ρ.dimension) :=
      smoothSectionMap (fun x ↦ (LinearMap.proj i).comp (d x).toLinearMap) (hp i)
    let j (i : Fin ρ.dimension) :=
      smoothSectionMap
        (fun x ↦ (d x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)) (hj i)
    let L := LinearMap.pi p
    have hL : Function.Bijective L := by
      constructor
      · intro u v h
        apply Subtype.ext
        funext x
        apply (d x).injective
        funext i
        exact congrArg (fun w ↦ (w i).val x) h
      · intro v
        refine ⟨∑ i, j i (v i), ?_⟩
        funext i
        apply Subtype.ext
        funext x
        change d x ((∑ k, j k (v k)).val x) i = (v i).val x
        simp only [Submodule.coe_sum, Finset.sum_apply]
        change d x (∑ k, (d x).symm (Pi.single k ((v k).val x))) i = _
        rw [← map_sum, LinearEquiv.apply_symm_apply]
        simp
    exact ⟨LinearEquiv.ofBijective L hL, fun _ _ _ ↦ rfl⟩
  obtain ⟨S, hSval⟩ := sectionEquiv b.source a.source e he heInv
  obtain ⟨T, hTval⟩ := sectionEquiv b.target a.target f hf hfInv
  have hS (g : G) (u : smoothSections (n := n) (r := b.source.rank) b.source.Fiber)
      (i : Fin ρ.dimension) :
      S (b.sourceAction.smoothSectionRepresentation IG b.source_smooth g u) i =
        ∑ j, ρ.representation g (Pi.single j 1) i •
          a.sourceAction.smoothSectionRepresentation IG a.source_smooth g (S u j) := by
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    rw [hSval]
    change e (g • y) (b.sourceAction.sectionLinearMap g u.val (g • y)) i = _
    rw [b.sourceAction.sectionLinearMap_smul, heg]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
      Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    change _ = _ • a.sourceAction.sectionLinearMap g (S u j).val (g • y)
    rw [a.sourceAction.sectionLinearMap_smul, hSval]
  have hT (g : G) (u : smoothSections (n := n) (r := b.target.rank) b.target.Fiber)
      (i : Fin ρ.dimension) :
      T (b.targetAction.smoothSectionRepresentation IG b.target_smooth g u) i =
        ∑ j, ρ.representation g (Pi.single j 1) i •
          a.targetAction.smoothSectionRepresentation IG a.target_smooth g (T u j) := by
    apply Subtype.ext
    funext x
    obtain ⟨y, rfl⟩ := MulAction.surjective g x
    rw [hTval]
    change f (g • y) (b.targetAction.sectionLinearMap g u.val (g • y)) i = _
    rw [b.targetAction.sectionLinearMap_smul, hfg]
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
      Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    change _ = _ • a.targetAction.sectionLinearMap g (T u j).val (g • y)
    rw [a.targetAction.sectionLinearMap_smul, hTval]
  -- Choose one original equivariant realization. Each tensor coordinate uses this same PDO.
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := a.source.rank) (q := a.target.rank)
    (E := a.source.Fiber) (F := a.target.Fiber)
  obtain ⟨P, hPg, hPclass⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG a.sourceAction a.targetAction a.source_smooth a.target_smooth 0
    (globalPrincipalSymbolClass a.source.Fiber a.target.Fiber 0
      (R.regularizedSymbol 0 a.symbol.val a.symbol.property.1 a.symbol.property.2))
    (fun g ↦ (R.equivariant_regularizedSymbol_class_eq_iff
      IG a.sourceAction a.targetAction a.source_smooth a.target_smooth R 0
        a.symbol a.symbol g).mpr (a.equivariant g))
  have hP : P.IsElliptic := ⟨_, hPclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 a.symbol.val
      a.symbol.property.1 a.symbol.property.2).mpr a.elliptic⟩
  let α (i : Fin ρ.dimension) := fun x ↦ (LinearMap.proj i).comp (e x).toLinearMap
  let β (i : Fin ρ.dimension) := fun x ↦
    (f x).symm.toLinearMap.comp (LinearMap.single ℂ _ i)
  let A (i : Fin ρ.dimension) := smoothBundleMapOperator (μ := μ) (α i) (he i)
  let B (i : Fin ρ.dimension) := smoothBundleMapOperator (μ := μ) (β i) (hfInv i)
  choose s hs hAclass using fun i ↦
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) (α i) (he i)
  choose t ht hBclass using fun i ↦
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) (β i) (hfInv i)
  obtain ⟨RA⟩ := nonempty_quantizationPresentation
    (n := n) (r := b.source.rank) (q := a.source.rank)
    (E := b.source.Fiber) (F := a.source.Fiber)
  obtain ⟨RB⟩ := nonempty_quantizationPresentation
    (n := n) (r := a.target.rank) (q := b.target.rank)
    (E := a.target.Fiber) (F := b.target.Fiber)
  obtain ⟨RU⟩ := nonempty_quantizationPresentation
    (n := n) (r := b.source.rank) (q := a.target.rank)
    (E := b.source.Fiber) (F := a.target.Fiber)
  obtain ⟨RQ⟩ := nonempty_quantizationPresentation
    (n := n) (r := b.source.rank) (q := b.target.rank)
    (E := b.source.Fiber) (F := b.target.Fiber)
  let u (i : Fin ρ.dimension) : homogeneousGlobalSymbolSpace (n := n)
      (r := b.source.rank) (q := a.target.rank) b.source.Fiber a.target.Fiber 0 :=
    ⟨globalSymbolComp a.symbol.val (s i).val,
      a.symbol.property.1.globalSymbolComp (s i).property.1,
      by simpa only [zero_add] using a.symbol.property.2.globalSymbolComp (s i).property.2⟩
  let c (i : Fin ρ.dimension) : homogeneousGlobalSymbolSpace (n := n)
      (r := b.source.rank) (q := b.target.rank) b.source.Fiber b.target.Fiber 0 :=
    ⟨globalSymbolComp (t i).val (u i).val,
      (t i).property.1.globalSymbolComp (u i).property.1,
      by simpa only [zero_add] using (t i).property.2.globalSymbolComp (u i).property.2⟩
  let U (i : Fin ρ.dimension) : PseudodifferentialOperator (n := n)
      (r := b.source.rank) (q := a.target.rank) b.source.Fiber a.target.Fiber μ 0 :=
    ⟨P.toLinearMap.comp (A i).toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (P.comp (A i)).isPseudodifferentialOperator⟩
  let Qc (i : Fin ρ.dimension) : PseudodifferentialOperator (n := n)
      (r := b.source.rank) (q := b.target.rank) b.source.Fiber b.target.Fiber μ 0 :=
    ⟨(B i).toLinearMap.comp (U i).toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        ((B i).comp (U i)).isPseudodifferentialOperator⟩
  have hQc (i : Fin ρ.dimension) : (Qc i).principalSymbol =
      globalPrincipalSymbolClass b.source.Fiber b.target.Fiber 0
        (RQ.regularizedSymbol 0 (c i).val (c i).property.1 (c i).property.2) := by
    have hU := PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
      RA R RU (s i) a.symbol (u i) (A i) P (U i) (hAclass i RA) hPclass rfl
        (fun _ _ _ ↦ rfl)
    exact PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp
      RU RB RQ (u i) (t i) (c i) (U i) (B i) (Qc i) hU (hBclass i RB) rfl
        (fun _ _ _ ↦ rfl)
  let Q := pseudodifferentialOperatorOfSpace (∑ i, (Qc i).toSpace)
  have hQclass : Q.principalSymbol =
      globalPrincipalSymbolClass b.source.Fiber b.target.Fiber 0
        (RQ.regularizedSymbol 0 b.symbol.val b.symbol.property.1 b.symbol.property.2) := by
    change principalSymbolLinearMap b.source.Fiber b.target.Fiber μ 0
      (∑ i, (Qc i).toSpace) = _
    rw [map_sum]
    change (∑ i, (Qc i).principalSymbol) = _
    simp_rw [hQc]
    rw [← map_sum]
    have hreg : (∑ i, RQ.regularizedSymbol 0 (c i).val
        (c i).property.1 (c i).property.2) = RQ.regularizedSymbol 0
          (∑ i, c i).val (∑ i, c i).property.1 (∑ i, c i).property.2 := by
      apply Subtype.ext
      funext x ξ
      simp only [Submodule.coe_sum, Finset.sum_apply,
        QuantizationPresentation.regularizedSymbol,
        QuantizationPresentation.regularizedSymbolFunction]
      simp only [Finset.smul_sum]
      exact Finset.sum_comm
    rw [hreg]
    apply (RQ.regularizedSymbol_class_eq_iff RQ 0 (∑ i, c i).val b.symbol.val
      (∑ i, c i).property.1 (∑ i, c i).property.2
      b.symbol.property.1 b.symbol.property.2).mpr
    intro x ξ hξ
    apply ContinuousLinearMap.ext
    intro v
    apply (f x).injective
    funext i
    simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply, map_sum]
    have hci (j : Fin ρ.dimension) :
        (c j).val x ξ v = (f x).symm (Pi.single j (a.symbol.val x ξ (e x v j))) := by
      change (t j).val x ξ (a.symbol.val x ξ ((s j).val x ξ v)) = _
      rw [hs, ht]
      rfl
    simp_rw [hci, LinearEquiv.apply_symm_apply]
    simp only [Finset.sum_pi_single, Finset.mem_univ, ite_true]
    exact (hsymbol x ξ hξ v i).symm
  have hQ : Q.IsElliptic := ⟨_, hQclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff RQ 0 b.symbol.val
      b.symbol.property.1 b.symbol.property.2).mpr b.elliptic⟩
  have hinter (v : smoothSections (n := n) (r := b.source.rank) b.source.Fiber)
      (i : Fin ρ.dimension) : P.toLinearMap (S v i) = T (Q.toLinearMap v) i := by
    apply Subtype.ext
    funext x
    rw [hTval]
    have hAv (j : Fin ρ.dimension) : (A j).toLinearMap v = S v j := by
      apply Subtype.ext
      funext y
      exact (hSval v j y).symm
    change (P.toLinearMap (S v i)).val x =
      f x (((∑ j, (Qc j).toSpace).val v).val x) i
    simp only [Submodule.coe_sum, LinearMap.sum_apply, Finset.sum_apply]
    change _ = f x (∑ j, (f x).symm
      (Pi.single j ((P.toLinearMap ((A j).toLinearMap v)).val x))) i
    rw [← map_sum, LinearEquiv.apply_symm_apply]
    simp only [Finset.sum_apply, Finset.sum_pi_single, Finset.mem_univ, ite_true]
    rw [hAv]
  -- Equivariance follows from this actual coordinate square, with the full mixing matrix.
  have hQg : Q.IsEquivariant IG b.sourceAction b.targetAction
      b.source_smooth b.target_smooth := by
    intro g
    apply LinearMap.ext
    intro v
    apply T.injective
    funext i
    simp only [LinearMap.comp_apply]
    rw [← hinter, hS, map_sum]
    simp only [map_smul]
    change (∑ j, _ • P.toLinearMap
      (a.sourceAction.smoothSectionRepresentation IG a.source_smooth g (S v j))) = _
    have hPgval (w : smoothSections (n := n) (r := a.source.rank) a.source.Fiber) :
        P.toLinearMap
          (a.sourceAction.smoothSectionRepresentation IG a.source_smooth g w) =
        a.targetAction.smoothSectionRepresentation IG a.target_smooth g (P.toLinearMap w) :=
      LinearMap.congr_fun (hPg g) w
    simp_rw [hPgval, hinter]
    exact (hT g (Q.toLinearMap v) i).symm
  -- Compare the same kernels and range quotients before returning to the symbol index.
  change equivariantHomogeneousAnalyticIndex IG b.sourceAction b.targetAction
    b.source_smooth b.target_smooth b.symbol b.elliptic b.equivariant = _
  rw [equivariantHomogeneousAnalyticIndex_eq_smooth IG b.sourceAction b.targetAction
    b.source_smooth b.target_smooth b.symbol b.elliptic b.equivariant μ RQ Q hQg hQ hQclass]
  rw [PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_mul_of_sectionEquiv
    IG b.source b.target
    a.source a.target b.sourceAction b.targetAction a.sourceAction a.targetAction
    b.source_smooth b.target_smooth a.source_smooth a.target_smooth
    ρ μ μ Q P hQg hQ hPg hP S T hS hT hinter]
  exact congrArg (fun z ↦ finiteRepresentationClass ρ * z)
    (equivariantHomogeneousAnalyticIndex_eq_smooth IG a.sourceAction a.targetAction
      a.source_smooth a.target_smooth a.symbol a.elliptic a.equivariant μ R P hPg hP
      hPclass).symm

end AtiyahSinger
