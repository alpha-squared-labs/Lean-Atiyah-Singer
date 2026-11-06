/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexDimension
public import AtiyahSinger.Analysis.EquivariantIndexProduct
public import AtiyahSinger.Geometry.CotangentProduct
public import AtiyahSinger.Geometry.OrthogonalGroupManifold
public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.TrivialEquivariantKTheory

/-!
# The ordinary analytic index of an external product

Public module ID: M0759.

The original compact-support K classes on two cotangent bundles have an
external product on the actual cotangent bundle of the product manifold. We
use the existing compact-support product and proper pullback through the
canonical cotangent splitting for the fixed concatenated Euclidean atlas.
The ordinary component analytic index of this class is the product of the
original two integer indices.

Source: SG III.13, Multiplicative Property 13.5, pp.249–250. Compact bases are
part of the source scope. No connectedness, nonempty base, positive dimension,
equal bundle ranks or fixed-rank representative of all classes is assumed.
Each of the three index maps uses a supplied positive smooth measure; they
need not be a product measure, by the existing density-independence theorem.
The ordinary formula is obtained by lifting the original classes for two
independent trivial compact Lie groups, applying full equivariant
multiplicativity, and using the actual support-product forgetful maps.
Its analytic comparison is supplied by the full equivariant product theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 30

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N] [T2Space N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The ordinary cotangent product is the original K product pulled back by the canonical split. -/
def cotangentKZeroExternalProduct :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+
      CompactSupportKZero (CotangentTotalSpace (n := m) (M := N)) →+
        CompactSupportKZero (CotangentTotalSpace (n := n + m) (M := M × N)) := by
  letI := euclideanProductChartedSpace (n := n) (m := m) M N
  letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let c := cotangentProductHomeomorph (n := n) (m := m) M N
  let p := compactSupportKZeroPullback ⟨c, c.continuous⟩ c.isProperMap
  let product := compactSupportKZeroExternalProduct
    (X := CotangentTotalSpace (n := n) (M := M))
    (Y := CotangentTotalSpace (n := m) (M := N))
  exact
    { toFun := fun u ↦ p.comp (product u)
      map_zero' := by
        apply AddMonoidHom.ext
        intro v
        simp
      map_add' := by
        intro u w
        apply AddMonoidHom.ext
        intro v
        simp }

variable [hSCM : SecondCountableTopology M] [hCM : CompactSpace M]
  [MeasurableSpace M] [hBM : BorelSpace M]
  [hSCN : SecondCountableTopology N] [hCN : CompactSpace N]
  [MeasurableSpace N] [hBN : BorelSpace N]

include hM hN hSCM hCM hBM hSCN hCN hBN in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Match the original factor actions, product action, and three native cotangent models.
/-- SG III.13.5: analytic indices multiply under the actual cotangent K external product. -/
theorem analyticIndexOfComponents_externalProduct
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν] :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    ∀ (ρ : Measure (M × N)) [IsSmoothPositiveMeasure (n := n + m) ρ]
      (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)))
      (v : CompactSupportKZero (CotangentTotalSpace (n := m) (M := N))),
      analyticIndexOfComponents (n := n + m) ρ (cotangentKZeroExternalProduct u v) =
        analyticIndexOfComponents (n := n) μ u * analyticIndexOfComponents (n := m) ν v := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  intro ρ hρ u v
  let G := Matrix.orthogonalGroup (Fin 0) ℝ
  let VG := OrthogonalGroupModel 0
  let := orthogonalGroupChartedSpace 0
  let := lieGroup_orthogonalGroup 0
  let := compactSpace_orthogonalGroup 0
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  -- Use genuine lifts of both original classes under two independent trivial actions.
  let : MulAction G M :=
    { smul := fun _ x ↦ x
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl }
  let : MulAction G N :=
    { smul := fun _ x ↦ x
      one_smul := fun _ ↦ rfl
      mul_smul := fun _ _ _ ↦ rfl }
  let : ContinuousSMul G M := ⟨continuous_snd⟩
  let : ContinuousSMul G N := ⟨continuous_snd⟩
  let : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M :=
    ⟨contMDiff_snd⟩
  let : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G N :=
    ⟨contMDiff_snd⟩
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := m) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := m) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := m) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, CotangentModel m)) ∞
  obtain ⟨u₀, hu₀⟩ := supportTripleKZeroToCompactSupport_surjective u
  obtain ⟨v₀, hv₀⟩ := supportTripleKZeroToCompactSupport_surjective v
  obtain ⟨a, ha⟩ :=
    (ComplexBundle.equivariantSupportTripleKZeroForget_bijective_of_subsingleton
      (G := G) (X := CotangentTotalSpace (n := n) (M := M))).surjective u₀
  obtain ⟨b, hb⟩ :=
    (ComplexBundle.equivariantSupportTripleKZeroForget_bijective_of_subsingleton
      (G := G) (X := CotangentTotalSpace (n := m) (M := N))).surjective v₀
  have haClass : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget a) = u := by rw [ha, hu₀]
  have hbClass : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget b) = v := by rw [hb, hv₀]
  let : ChartedSpace (VG × VG) (G × G) := prodChartedSpace VG G VG G
  let : LieGroup 𝓘(ℝ, VG × VG) ∞ (G × G) := by
    rw [modelWithCornersSelf_prod]
    exact Prod.instLieGroup (I := 𝓘(ℝ, VG)) (I' := 𝓘(ℝ, VG))
  let : MeasurableSpace (G × G) := borel (G × G)
  let : BorelSpace (G × G) := ⟨rfl⟩
  let : MulAction (G × G) M :=
    MulAction.compHom M (ContinuousMonoidHom.fst G G).toMonoidHom
  let : ContinuousSMul (G × G) M :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G G).continuous
  let : MulAction (G × G) N :=
    MulAction.compHom N (ContinuousMonoidHom.snd G G).toMonoidHom
  let : ContinuousSMul (G × G) N :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G G).continuous
  let := contMDiffSMul_euclideanProduct (n := n) (m := m)
    (VG := VG) (VH := VG) (G := G) (H := G) M N
  let := smoothCotangentMulAction (n := n + m) (G := G × G) (M := M × N) 𝓘(ℝ, VG × VG)
  let := contMDiffSMul_smoothCotangent
    (n := n + m) (G := G × G) (M := M × N) 𝓘(ℝ, VG × VG)
  let : ContinuousSMul (G × G) (CotangentTotalSpace (n := n + m) (M := M × N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG × VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + m))).prod 𝓘(ℝ, CotangentModel (n + m))) ∞
  let p := equivariantCotangentKZeroExternalProduct (n := n) (m := m)
    (VG := VG) (VH := VG) (G := G) (H := G) a b
  -- Apply full equivariant multiplicativity before applying the dimension augmentation.
  have hvalue := congrArg (representationDimension (G × G))
    (equivariantAnalyticIndexMap_externalProduct (n := n) (m := m)
      (VG := VG) (VH := VG) (G := G) (H := G) a b)
  have hdim (x y : RepresentationGrothendieckGroup G) :
      representationDimension (G × G) (representationExternalProduct x y) =
        representationDimension G x * representationDimension G y := by
    change representationDimension (G × G)
      (representationRestriction (ContinuousMonoidHom.fst G G) x *
        representationRestriction (ContinuousMonoidHom.snd G G) y) = _
    rw [(representationDimension_multiplicative (G × G)).1]
    exact congrArg₂ (· * ·)
      (DFunLike.congr_fun (representationDimension_restriction
        (ContinuousMonoidHom.fst G G)) x)
      (DFunLike.congr_fun (representationDimension_restriction
        (ContinuousMonoidHom.snd G G)) y)
  have hdimM := DFunLike.congr_fun
    (representationDimension_equivariantAnalyticIndexMap
      (n := n) (M := M) (VG := VG) (G := G) μ) a
  have hdimN := DFunLike.congr_fun
    (representationDimension_equivariantAnalyticIndexMap
      (n := m) (M := N) (VG := VG) (G := G) ν) b
  have hdimP := DFunLike.congr_fun
    (representationDimension_equivariantAnalyticIndexMap
      (n := n + m) (M := M × N) (VG := VG × VG) (G := G × G) ρ) p
  simp only [AddMonoidHom.comp_apply] at hdimM hdimN hdimP
  rw [haClass] at hdimM
  rw [hbClass] at hdimN
  rw [hdim, hdimM, hdimN] at hvalue
  change representationDimension (G × G)
    (equivariantAnalyticIndexMap (n := n + m) (VG := VG × VG) (G := G × G) p) = _ at hvalue
  rw [hdimP] at hvalue
  -- Forgetting the actual independent support product commutes with the same cotangent split.
  let : MulAction (G × G) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst G G).toMonoidHom
  let : ContinuousSMul (G × G) (CotangentTotalSpace (n := n) (M := M)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst G G).continuous
  let : MulAction (G × G) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd G G).toMonoidHom
  let : ContinuousSMul (G × G) (CotangentTotalSpace (n := m) (M := N)) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd G G).continuous
  let c := cotangentProductHomeomorph (n := n) (m := m) M N
  let cG := cotangentProductHomeomorph_equivariant (n := n) (m := m)
    (VG := VG) (VH := VG) (G := G) (H := G) M N
  let w := equivariantSupportKZeroDifferentGroupExternalProduct a b
  have hforget := DFunLike.congr_fun
    (equivariantSupportTripleKZeroForget_pullback ⟨c, c.continuous⟩ cG c.isProperMap) w
  have hpull := DFunLike.congr_fun
    (supportTripleKZeroToCompactSupport_pullback ⟨c, c.continuous⟩ c.isProperMap)
    (equivariantSupportTripleKZeroForget w)
  simp only [AddMonoidHom.comp_apply] at hforget hpull
  have hpClass : supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget p) = cotangentKZeroExternalProduct u v := by
    change supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget
      (equivariantSupportTripleKZeroPullback ⟨c, c.continuous⟩ cG c.isProperMap w)) = _
    rw [hforget, hpull]
    change compactSupportKZeroPullback ⟨c, c.continuous⟩ c.isProperMap
      (supportTripleKZeroToCompactSupport
        (equivariantSupportTripleKZeroForget
          (equivariantSupportKZeroDifferentGroupExternalProduct a b))) = _
    rw [equivariantSupportKZeroDifferentGroupExternalProduct_forget, haClass, hbClass]
    rfl
  rw [hpClass] at hvalue
  exact hvalue

end AtiyahSinger
