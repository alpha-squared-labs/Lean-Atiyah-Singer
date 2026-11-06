/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum
public import AtiyahSinger.Topology.ChernClass

/-!
# Chern classes on a common actual splitting space

Public module ID: M1632.

Line coordinates with joint kernel zero determine the original Chern classes
on a specified pullback. Applying this to two successive original flag bundles
compares a genuine direct sum on one common space, keeping the original bundle
norms and the independently supplied Hermitian metrics.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianFlagTopology hermitianFlagLineTopology
  isFiniteRank_hermitianFlagLine hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual detecting line coordinates give the elementary-symmetric formula on that pullback. -/
theorem chernClass_pullback_eq_elementarySymmetric_of_lineCoordinates
    {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
    (L : Fin r → Y → Type u) [∀ i y, NormedAddCommGroup (L i y)]
    [∀ i y, NormedSpace ℂ (L i y)] [∀ i, TopologicalSpace (TotalSpace Unit (L i))]
    [∀ i, IsFiniteRank (L i)]
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ i : Fin r, Hom ((f : Y → X) *ᵖ E) (L i))
    (hL : ∀ i y, Module.finrank ℂ (L i y) = 1)
    (hdetect : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (y : Y) (v : E (f y)), (∀ i, (a i).linearMap y v = 0) → v = 0)
    (k : ℕ) :
    singularCohomologyPullback ℤ f (2 * k) (chernClass r E h k) =
      singularCohomologyElementarySymmetric ℤ Y
        (List.ofFn (fun i ↦ firstChernClass (L i) (hL i))) k := by
  let F := (f : Y → X) *ᵖ E
  let hnorm : ∀ x, NormedAddCommGroup (E x) := inferInstance
  let hspace : ∀ x, NormedSpace ℂ (E x) := inferInstance
  let : ∀ p, NormedAddCommGroup (F p) := fun p ↦ hnorm (f p)
  let : ∀ p, NormedSpace ℂ (F p) := fun p ↦ hspace (f p)
  let : FiberBundle (EuclideanSpace ℂ (Fin r)) F :=
    FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  let : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F :=
    VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  have hb := hermitianProjectivePowerCombination_int_bijective r E h r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have hb' := hermitianProjectivePowerCombination_int_bijective r F
    (hermitianProjectivePullbackMetric r E h f) r (fun i ↦ Nat.le_of_lt i.isLt)
  -- The actual projective basis theorem discharges both coefficient comparison premises.
  rw [chernClass_eq_projectiveChernCoefficient r E h hb]
  exact hermitianProjectiveChernCoefficient_pullback_eq_elementarySymmetric r E h f
    hb hb' L a hL hdetect k

variable (s : ℕ)
  (F : X → Type u) [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  (hF : letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
    ContinuousHermitianMetric F)
  (G : X → Type u) [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin (r + s))) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin (r + s))) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin (r + s))) G]
  (hG : letI := modelTopology (EuclideanSpace ℂ (Fin (r + s))) G
    ContinuousHermitianMetric G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Successive actual flags give detecting cohomology and the concatenated roots of a direct sum. -/
theorem exists_commonFlag_chernClass_sum
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin s)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin (r + s))) G
      letI := sumTopology (E := E) (F := F)
      Iso G (E ×ᵇ F)) :
    ∃ (Y : TopCat.{u}) (f : C(Y, X))
      (x : Fin r → singularCohomology ℤ Y 2) (y : Fin s → singularCohomology ℤ Y 2),
      (∀ n, Function.Injective (singularCohomologyPullback ℤ f n)) ∧
      (∀ n, Function.Injective (singularCohomologyPullback ℚ f n)) ∧
      (∀ k, singularCohomologyPullback ℤ f (2 * k) (chernClass r E h k) =
        singularCohomologyElementarySymmetric ℤ Y (List.ofFn x) k) ∧
      (∀ k, singularCohomologyPullback ℤ f (2 * k) (chernClass s F hF k) =
        singularCohomologyElementarySymmetric ℤ Y (List.ofFn y) k) ∧
      (∀ k, singularCohomologyPullback ℤ f (2 * k) (chernClass (r + s) G hG k) =
        singularCohomologyElementarySymmetric ℤ Y (List.ofFn x ++ List.ofFn y) k) := by
  classical
  let vE := EuclideanSpace ℂ (Fin r)
  let vF := EuclideanSpace ℂ (Fin s)
  let := modelTopology vE E
  let := modelTopology vF F
  let := modelTopology (EuclideanSpace ℂ (Fin (r + s))) G
  let := sumTopology (E := E) (F := F)
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
  let aE (i : Fin r) : Hom ((f : Q → X) *ᵖ E) (LE i) :=
    ((hermitianFlagCoordinateHom r E h i).pullback q).comp
      (pullbackCompIso (E := E) p q).symm.toHom
  let oldFTopology : TopologicalSpace (TotalSpace Unit FP) := inferInstance
  let := modelTopology vF FP
  let aFLinear (i : Fin s) := (hermitianFlagCoordinateHom s FP hFP i).linearMap
  have aFContinuous (i : Fin s) := (hermitianFlagCoordinateHom s FP hFP i).continuous_total
  have hFInject (z : Q) : Function.Injective (fun v : FP (q z) ↦
      fun i ↦ aFLinear i z v) := hermitianFlagCoordinates_injective s FP hFP z
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
  let normLE : ∀ i z, NormedAddCommGroup (LE i z) := inferInstance
  let normLF : ∀ i z, NormedAddCommGroup (LF i z) := inferInstance
  let spaceLE : ∀ i z, NormedSpace ℂ (LE i z) := inferInstance
  let spaceLF : ∀ i z, NormedSpace ℂ (LF i z) := inferInstance
  let topologyLE : ∀ i, TopologicalSpace (TotalSpace Unit (LE i)) := inferInstance
  let topologyLF : ∀ i, TopologicalSpace (TotalSpace Unit (LF i)) := inferInstance
  let finiteLE : ∀ i, IsFiniteRank (LE i) := inferInstance
  let finiteLF : ∀ i, IsFiniteRank (LF i) := inferInstance
  let L₀ : Fin r ⊕ Fin s → Q → Type u := Sum.elim LE LF
  let normL₀ : ∀ i z, NormedAddCommGroup (L₀ i z) := Sum.rec normLE normLF
  let spaceL₀ : ∀ i z, NormedSpace ℂ (L₀ i z) := Sum.rec spaceLE spaceLF
  let topologyL₀ : ∀ i, TopologicalSpace (TotalSpace Unit (L₀ i)) :=
    Sum.rec topologyLE topologyLF
  let finiteL₀ : ∀ i, IsFiniteRank (L₀ i) := Sum.rec finiteLE finiteLF
  let hL₀ : ∀ i z, Module.finrank ℂ (L₀ i z) = 1 := Sum.rec hLE hLF
  let L (i : Fin (r + s)) := L₀ (finSumFinEquiv.symm i)
  let : ∀ i z, NormedAddCommGroup (L i z) := fun i ↦ normL₀ (finSumFinEquiv.symm i)
  let : ∀ i z, NormedSpace ℂ (L i z) := fun i ↦ spaceL₀ (finSumFinEquiv.symm i)
  let : ∀ i, TopologicalSpace (TotalSpace Unit (L i)) :=
    fun i ↦ topologyL₀ (finSumFinEquiv.symm i)
  let : ∀ i, IsFiniteRank (L i) := fun i ↦ finiteL₀ (finSumFinEquiv.symm i)
  let hL : ∀ i z, Module.finrank ℂ (L i z) = 1 := fun i ↦ hL₀ (finSumFinEquiv.symm i)
  -- Compose the genuine product projections with e before pulling them to this same space.
  let bE := ((sumFst (E := E) (F := F)).comp e.toHom).pullback f
  let bF := ((sumSnd (E := E) (F := F)).comp e.toHom).pullback f
  let a₀ : ∀ i, Hom ((f : Q → X) *ᵖ G) (L₀ i) :=
    Sum.rec (fun i ↦ (aE i).comp bE) (fun i ↦ (aF i).comp bF)
  let a (i : Fin (r + s)) : Hom ((f : Q → X) *ᵖ G) (L i) :=
    a₀ (finSumFinEquiv.symm i)
  have hdetect (z : Q) (v : G (f z)) (hz : ∀ i, (a i).linearMap z v = 0) : v = 0 := by
    have hleft : (e.linearEquiv (f z) v).1 = 0 := by
      apply hdetectE z
      intro i
      exact (congrArg (fun j ↦ (a₀ j).linearMap z v = 0)
        (finSumFinEquiv_symm_apply_castAdd i)).mp (hz (Fin.castAdd s i))
    have hright : (e.linearEquiv (f z) v).2 = 0 := by
      apply hdetectF z
      intro i
      exact (congrArg (fun j ↦ (a₀ j).linearMap z v = 0)
        (finSumFinEquiv_symm_apply_natAdd i)).mp (hz (Fin.natAdd r i))
    apply (e.linearEquiv (f z)).injective
    exact (Prod.ext hleft hright).trans (map_zero (e.linearEquiv (f z))).symm
  let x (i : Fin r) := firstChernClass (LE i) (hLE i)
  let y (i : Fin s) := firstChernClass (LF i) (hLF i)
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
      (r + s) G hG f L a hL hdetect k
    let c₀ (i : Fin r ⊕ Fin s) := firstChernClass (L₀ i) (hL₀ i)
    have hroots : (fun i ↦ firstChernClass (L i) (hL i)) = Fin.append x y := by
      funext i
      change c₀ (finSumFinEquiv.symm i) = Fin.append x y i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · rw [finSumFinEquiv_symm_apply_castAdd, Fin.append_left]
        rfl
      · rw [finSumFinEquiv_symm_apply_natAdd, Fin.append_right]
        rfl
    rw [hroots, List.ofFn_fin_append] at hc
    exact hc

end AtiyahSinger.ComplexBundle
