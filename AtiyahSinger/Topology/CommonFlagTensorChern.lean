/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CommonFlagChern
public import AtiyahSinger.Topology.ComplexLineTensorChern
public import AtiyahSinger.Topology.HermitianMetricComap
public import AtiyahSinger.Topology.HermitianMetricPullback

/-!
# Tensor Chern roots on one actual common flag space

Public module ID: M1633.

Two successive original flag bundles split the supplied factors. Their
actual tensor line coordinates detect the pulled-back tensor bundle; the
normalized line tensor formula identifies its roots with the pairwise sums
of the same two root families. All comparison maps use the specified tensor
Iso and the original total topologies, norms, and Hermitian metrics.

Source: SG III.11, Proposition 11.16, and the splitting principle in Hatcher,
Vector Bundles and K-Theory, Section 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

variable (s : ℕ)
  (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  (hF : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    ContinuousHermitianMetric F)
  (G : X → Type u) [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin (r * s))) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin (r * s))) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin (r * s))) G]
  (hG : letI := modelTopology (EuclideanSpace ℂ (Fin (r * s))) G
    ContinuousHermitianMetric G)

attribute [local instance] hermitianFlagTopology hermitianFlagLineTopology
  isFiniteRank_hermitianFlagLine hermitianProjectiveTopology tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback

set_option maxHeartbeats 1000000 in
-- The common native flags retain dependent original fiber norms through the tensor coordinates.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual tensor Iso gives pairwise sums of the same Chern roots on one common flag space. -/
theorem exists_commonFlag_chernClass_tensor
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin (r * s))) G
      letI := tensorTopology (E := E) (F := F)
      Iso G (fun z ↦ E z ⊗[ℂ] F z)) :
    ∃ (Y : TopCat.{u}) (f : C(Y, X))
      (x : Fin r → singularCohomology ℤ Y 2) (y : Fin s → singularCohomology ℤ Y 2),
      (∀ n, Function.Injective (singularCohomologyPullback ℤ f n)) ∧
      (∀ n, Function.Injective (singularCohomologyPullback ℚ f n)) ∧
      (∀ k, singularCohomologyPullback ℤ f (2 * k) (chernClass r E h k) =
        singularCohomologyElementarySymmetric ℤ Y (List.ofFn x) k) ∧
      (∀ k, singularCohomologyPullback ℤ f (2 * k) (chernClass s F hF k) =
        singularCohomologyElementarySymmetric ℤ Y (List.ofFn y) k) ∧
      (∀ k, singularCohomologyPullback ℤ f (2 * k) (chernClass (r * s) G hG k) =
        singularCohomologyElementarySymmetric ℤ Y (List.ofFn (fun i : Fin (r * s) ↦
          x (finProdFinEquiv.symm i).1 + y (finProdFinEquiv.symm i).2)) k) := by
  classical
  let vE := EuclideanSpace ℂ (Fin r)
  let vF := EuclideanSpace ℂ (Fin s)
  let := modelTopology vE E
  let := modelTopology vF F
  let := modelTopology (EuclideanSpace ℂ (Fin (r * s))) G
  let := isFiniteRank_model vE E
  let := isFiniteRank_model vF F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin (r * s))) G
  let := tensorTopology (E := E) (F := F)
  let P := HermitianFlagBundle r E h
  let p := hermitianFlagProjection r E h
  let FP := (p : P → X) *ᵖ F
  let hnormF : ∀ x, NormedAddCommGroup (F x) := inferInstance
  let hspaceF : ∀ x, NormedSpace ℂ (F x) := inferInstance
  let : ∀ z, NormedAddCommGroup (FP z) := fun z ↦ hnormF (p z)
  let : ∀ z, NormedSpace ℂ (FP z) := fun z ↦ hspaceF (p z)
  let : FiberBundle vF FP := FiberBundle.pullback (F := vF) (E := F) p
  let : VectorBundle ℂ vF FP := VectorBundle.pullback ℂ (F := vF) (E := F) p
  let hFP := hermitianProjectivePullbackMetric s F hF p
  let Q := HermitianFlagBundle s FP hFP
  let q := hermitianFlagProjection s FP hFP
  let f : C(Q, X) := p.comp q
  -- The first flag's lines are pulled back to the flag of the actual pulled-back second bundle.
  let hnormLE : ∀ i z, NormedAddCommGroup (HermitianFlagLine r E h i z) := inferInstance
  let hspaceLE : ∀ i z, NormedSpace ℂ (HermitianFlagLine r E h i z) := inferInstance
  let LE (i : Fin r) := (q : Q → P) *ᵖ (HermitianFlagLine r E h i)
  let LF := HermitianFlagLine s FP hFP
  let : ∀ i z, NormedAddCommGroup (LE i z) := fun i z ↦ hnormLE i (q z)
  let : ∀ i z, NormedSpace ℂ (LE i z) := fun i z ↦ hspaceLE i (q z)
  let : ∀ i, IsFiniteRank (LE i) := fun i ↦ isFiniteRank_pullback (E :=
    HermitianFlagLine r E h i) q
  let inclE (i : Fin r) : Hom (HermitianFlagLine r E h i) ((p : P → X) *ᵖ E) :=
    { linearMap z := (LinearMap.range (z.2.val i).toLinearMap).subtype
      continuous_total := continuous_induced_dom }
  let metricLE (i : Fin r) :=
    ((h.pullback p).comap (inclE i) (fun _ ↦ Subtype.val_injective)).pullback q
  let aE (i : Fin r) : Hom ((f : Q → X) *ᵖ E) (LE i) :=
    ((hermitianFlagCoordinateHom r E h i).pullback q).comp
      (pullbackCompIso (E := E) p q).symm.toHom
  let oldFTopology : TopologicalSpace (TotalSpace Unit FP) := inferInstance
  let := modelTopology vF FP
  let aFLinear (i : Fin s) := (hermitianFlagCoordinateHom s FP hFP i).linearMap
  have aFContinuous (i : Fin s) := (hermitianFlagCoordinateHom s FP hFP i).continuous_total
  have hFInject (z : Q) : Function.Injective (fun v : FP (q z) ↦
      fun i ↦ aFLinear i z v) := hermitianFlagCoordinates_injective s FP hFP z
  let inclF (i : Fin s) : Hom (LF i) ((q : Q → P) *ᵖ FP) :=
    { linearMap z := (LinearMap.range (z.2.val i).toLinearMap).subtype
      continuous_total := continuous_induced_dom }
  let metricLF (i : Fin s) :=
    (hFP.pullback q).comap (inclF i) (fun _ ↦ Subtype.val_injective)
  let := oldFTopology
  let aF₀ (i : Fin s) : Hom ((q : Q → P) *ᵖ FP) (LF i) :=
    { linearMap := aFLinear i
      continuous_total := by
        have hc := aFContinuous i
        have htop : oldFTopology = modelTopology vF FP :=
          (modelTopology_pullback vF F (p : P → X)).symm
        convert hc using 1
        exact congrArg (fun τ ↦ @Pullback.TotalSpace.topologicalSpace P Unit FP Q
          (q : Q → P) inferInstance τ) htop }
  let aF (i : Fin s) : Hom ((f : Q → X) *ᵖ F) (LF i) :=
    (aF₀ i).comp (pullbackCompIso (E := F) p q).symm.toHom
  have hcompE (z : Q) (v : E (f z)) :
      (pullbackCompIso (E := E) p q).symm.linearEquiv z v = v := by
    calc
      _ = (pullbackCompIso (E := E) p q).linearEquiv z
          ((pullbackCompIso (E := E) p q).symm.linearEquiv z v) :=
        (pullbackCompIso_apply (E := E) p q z _).symm
      _ = v := ((pullbackCompIso (E := E) p q).linearEquiv z).apply_symm_apply v
  have hcompF (z : Q) (v : F (f z)) :
      (pullbackCompIso (E := F) p q).symm.linearEquiv z v = v := by
    calc
      _ = (pullbackCompIso (E := F) p q).linearEquiv z
          ((pullbackCompIso (E := F) p q).symm.linearEquiv z v) :=
        (pullbackCompIso_apply (E := F) p q z _).symm
      _ = v := ((pullbackCompIso (E := F) p q).linearEquiv z).apply_symm_apply v
  have hdetectE (z : Q) (v : E (f z)) (hz : ∀ i, (aE i).linearMap z v = 0) : v = 0 := by
    apply hermitianFlagCoordinates_injective r E h (q z)
    funext i
    have hi := hz i
    change (hermitianFlagCoordinateHom r E h i).linearMap (q z)
      ((pullbackCompIso (E := E) p q).symm.linearEquiv z v) = 0 at hi
    rw [hcompE] at hi
    exact hi.trans (map_zero ((hermitianFlagCoordinateHom r E h i).linearMap (q z))).symm
  have hdetectF (z : Q) (v : F (f z)) (hz : ∀ i, (aF i).linearMap z v = 0) : v = 0 := by
    apply hFInject z
    funext i
    have hi := hz i
    change aFLinear i z
      ((pullbackCompIso (E := F) p q).symm.linearEquiv z v) = 0 at hi
    rw [hcompF] at hi
    exact hi.trans (map_zero (aFLinear i z)).symm
  have hLE (i : Fin r) (z : Q) : Module.finrank ℂ (LE i z) = 1 :=
    (q z).2.property.2.1 i
  have hLF (i : Fin s) (z : Q) : Module.finrank ℂ (LF i z) = 1 := z.2.property.2.1 i
  -- Tensor coordinates are genuine tensor maps between the original line factors.
  let : ∀ i z, FiniteDimensional ℂ (LE i z) := fun i z ↦ finite_fiber (E := LE i) z
  let : ∀ i z, FiniteDimensional ℂ (LF i z) := fun i z ↦ finite_fiber (E := LF i) z
  let T (ij : Fin r × Fin s) := fun z : Q ↦ LE ij.1 z ⊗[ℂ] LF ij.2 z
  have hT (ij : Fin r × Fin s) (z : Q) : Module.finrank ℂ (T ij z) = 1 := by
    rw [Module.finrank_tensorProduct, hLE, hLF, one_mul]
  let d (ij : Fin r × Fin s) (z : Q) : T ij z ≃ₗ[ℂ] ℂ :=
    LinearEquiv.ofFinrankEq (T ij z) ℂ ((hT ij z).trans (Module.finrank_self ℂ).symm)
  let : ∀ ij z, NormedAddCommGroup (T ij z) := fun ij z ↦
    NormedAddCommGroup.induced (T ij z) ℂ (d ij z).toAddMonoidHom (d ij z).injective
  let : ∀ ij z, NormedSpace ℂ (T ij z) := fun ij z ↦
    NormedSpace.induced ℂ (T ij z) ℂ (d ij z).toLinearMap
  let normT : ∀ ij z, NormedAddCommGroup (T ij z) := inferInstance
  let spaceT : ∀ ij z, NormedSpace ℂ (T ij z) := inferInstance
  let topologyT : ∀ ij, TopologicalSpace (TotalSpace Unit (T ij)) := inferInstance
  let finiteT : ∀ ij, IsFiniteRank (T ij) := inferInstance
  let L (i : Fin (r * s)) := T (finProdFinEquiv.symm i)
  let : ∀ i z, NormedAddCommGroup (L i z) := fun i ↦ normT (finProdFinEquiv.symm i)
  let : ∀ i z, NormedSpace ℂ (L i z) := fun i ↦ spaceT (finProdFinEquiv.symm i)
  let : ∀ i, TopologicalSpace (TotalSpace Unit (L i)) :=
    fun i ↦ topologyT (finProdFinEquiv.symm i)
  let : ∀ i, IsFiniteRank (L i) := fun i ↦ finiteT (finProdFinEquiv.symm i)
  let hL : ∀ i z, Module.finrank ℂ (L i z) = 1 := fun i ↦ hT (finProdFinEquiv.symm i)
  let a₀ (ij : Fin r × Fin s) : Hom ((f : Q → X) *ᵖ G) (T ij) :=
    ((aE ij.1).tensor (aF ij.2)).comp
      ((pullbackTensorIso (E := E) (F := F) f).toHom.comp (e.pullback f).toHom)
  let a (i : Fin (r * s)) : Hom ((f : Q → X) *ᵖ G) (L i) :=
    a₀ (finProdFinEquiv.symm i)
  have hdetect (z : Q) (v : G (f z)) (hz : ∀ i, (a i).linearMap z v = 0) : v = 0 := by
    let incE (i : Fin r) : LE i z →ₗ[ℂ] E (f z) :=
      (LinearMap.range ((q z).2.val i).toLinearMap).subtype
    let incF (i : Fin s) : LF i z →ₗ[ℂ] F (f z) :=
      (LinearMap.range (z.2.val i).toLinearMap).subtype
    have hrecE (w : E (f z)) : ∑ i : Fin r, incE i ((aE i).linearMap z w) = w := by
      change (∑ i : Fin r, (q z).2.val i
        ((pullbackCompIso (E := E) p q).symm.linearEquiv z w)) = w
      rw [hcompE]
      exact (hermitianFlagSplitting_properties r E h).2.1 (q z) w
    have hrecF (w : F (f z)) : ∑ i : Fin s, incF i ((aF i).linearMap z w) = w := by
      change (∑ i : Fin s, z.2.val i
        ((pullbackCompIso (E := F) p q).symm.linearEquiv z w)) = w
      rw [hcompF]
      exact (hermitianFlagSplitting_properties s FP hFP).2.1 z w
    -- Expand each pure tensor by the two original sum-of-projections identities.
    have hrec (w : E (f z) ⊗[ℂ] F (f z)) :
        (∑ i : Fin r, ∑ j : Fin s, TensorProduct.map (incE i) (incF j)
          (TensorProduct.map ((aE i).linearMap z) ((aF j).linearMap z) w)) = w := by
      induction w using TensorProduct.inductionOn with
      | tmul v w =>
          simp only [TensorProduct.map_tmul]
          simp_rw [← TensorProduct.tmul_sum]
          rw [← TensorProduct.sum_tmul, hrecE, hrecF]
      | add v w hv hw => simp only [map_add, Finset.sum_add_distrib, hv, hw]
    have hcoords (i : Fin r) (j : Fin s) :
        TensorProduct.map ((aE i).linearMap z) ((aF j).linearMap z)
          (e.linearEquiv (f z) v) = 0 := by
      have hc := hz (finProdFinEquiv (i, j))
      change (a₀ (finProdFinEquiv.symm (finProdFinEquiv (i, j)))).linearMap z v = 0 at hc
      rw [Equiv.symm_apply_apply] at hc
      exact hc
    apply (e.linearEquiv (f z)).injective
    have hw := hrec (e.linearEquiv (f z) v)
    simpa only [hcoords, map_zero, Finset.sum_const_zero] using hw.symm
  let x (i : Fin r) := firstChernClass (LE i) (hLE i)
  let y (i : Fin s) := firstChernClass (LF i) (hLF i)
  have hroots (ij : Fin r × Fin s) : firstChernClass (T ij) (hT ij) = x ij.1 + y ij.2 :=
    firstChernClass_eq_add_of_tensor (LE ij.1) (LF ij.2) (metricLE ij.1) (metricLF ij.2)
      (hLE ij.1) (hLF ij.2) (hT ij) (Iso.refl (T ij))
  refine ⟨TopCat.of Q, f, x, y, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hcomp : singularCohomologyPullback ℤ f n =
        singularCohomologyPullback ℤ p n ≫ singularCohomologyPullback ℤ q n := by
      change (singularCohomologyFunctor ℤ n).map ((TopCat.ofHom p).op ≫
        (TopCat.ofHom q).op) = _
      exact (singularCohomologyFunctor ℤ n).map_comp _ _
    rw [hcomp]
    exact (hermitianFlagProjection_cohomology_injective ℤ s FP hFP n).comp
      (hermitianFlagProjection_cohomology_injective ℤ r E h n)
  · intro n
    have hcomp : singularCohomologyPullback ℚ f n =
        singularCohomologyPullback ℚ p n ≫ singularCohomologyPullback ℚ q n := by
      change (singularCohomologyFunctor ℚ n).map ((TopCat.ofHom p).op ≫
        (TopCat.ofHom q).op) = _
      exact (singularCohomologyFunctor ℚ n).map_comp _ _
    rw [hcomp]
    exact (hermitianFlagProjection_cohomology_injective ℚ s FP hFP n).comp
      (hermitianFlagProjection_cohomology_injective ℚ r E h n)
  · exact chernClass_pullback_eq_elementarySymmetric_of_lineCoordinates r E h f
      LE aE hLE hdetectE
  · exact chernClass_pullback_eq_elementarySymmetric_of_lineCoordinates s F hF f
      LF aF hLF hdetectF
  · intro k
    have hc := chernClass_pullback_eq_elementarySymmetric_of_lineCoordinates
      (r * s) G hG f L a hL hdetect k
    have heq : (fun i ↦ firstChernClass (L i) (hL i)) =
        (fun i : Fin (r * s) ↦ x (finProdFinEquiv.symm i).1 +
          y (finProdFinEquiv.symm i).2) := by
      funext i
      exact hroots (finProdFinEquiv.symm i)
    rw [heq] at hc
    exact hc

end AtiyahSinger.ComplexBundle
