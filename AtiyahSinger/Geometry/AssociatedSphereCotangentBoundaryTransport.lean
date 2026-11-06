/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorTransport
public import AtiyahSinger.Geometry.AssociatedSphereCotangentTensorIso
public import AtiyahSinger.Topology.AssociatedEquivariantMaps

/-!
# The original associated cotangent coordinates and tensor boundary

Public module ID: M1070.

The paired image of the actual inverse cotangent realization has base covector
given by composition with the supplied horizontal lift. In every original
principal representative, its sphere covector is composition with the actual
fiber-inclusion derivative. These formulas connect the original associated
Hermitian product to the full tensor boundary on the native cotangent space.

All quotient, pullback and tensor topologies remain the original ones. No
native direct-sum model or compact-support class equality is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent verticalTangentTopology
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology isFiniteRank_associatedEquivariant
  tensorTopology isFiniteRank_tensor isFiniteRank_pullback sumTopology isFiniteRank_sum

/-- Internal pullback/sum reassociation, used at each original source and target sum. -/
private def pullbackSumIso {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]
    (a : C(U, V)) (E F : V → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)] :
    Iso (a *ᵖ (E ×ᵇ F)) ((a *ᵖ E) ×ᵇ (a *ᵖ F)) where
  linearEquiv x := LinearEquiv.refl ℂ (E (a x) × F (a x))
  continuous_total := by
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit E a).continuous_iff]
      exact (Pullback.continuous_proj Unit (E ×ᵇ F) a).prodMk
        (continuous_sum_fst.comp (Pullback.continuous_lift Unit (E ×ᵇ F) a))
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit F a).continuous_iff]
      exact (Pullback.continuous_proj Unit (E ×ᵇ F) a).prodMk
        (continuous_sum_snd.comp (Pullback.continuous_lift Unit (E ×ᵇ F) a))
  continuous_symm := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ F) a).continuous_iff]
    apply ((Pullback.continuous_proj Unit E a).comp continuous_sum_fst).prodMk
    apply continuous_induced_rng.mpr
    exact ((Pullback.continuous_lift Unit E a).comp continuous_sum_fst).prodMk
      ((Pullback.continuous_lift Unit F a).comp continuous_sum_snd)

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => CotangentTotalSpace (n := n) (M := B)
local notation "Y" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "f" => cotangentProjection (n := n) (M := B)
local notation "Q" => PrincipalBundlePullback f projection
local notation "W" => AssociatedBundle G Q Y
local notation "CotFiber" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ
local notation "NativeCot" => TotalSpace ((En × Er) →L[ℝ] ℝ) CotFiber

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- The two original cotangent factors retain the exact inclusion derivative and splitting.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual inverse cotangent realization retains both full original covector factors. -/
theorem associatedSphereCotangentHomeomorph_symm_paired_apply
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let e := associatedSphereCotangentHomeomorph S H
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let j := associatedBundlePullbackProdMap
      («G» := G) («Y» := Y) (projection := projection) f
    ∀ (z : NativeCot) (p : P) (y : OrthogonalSphere r),
      associatedBundleMk G P (OrthogonalSphere r) p y = z.proj →
      j (e.symm z) =
        ((⟨base z.proj, z.snd.comp (H.lift z.proj)⟩ : X),
          associatedBundleMk G P Y p
            ⟨y, z.snd.comp (mfderiv (𝓡 r) 𝓘(ℝ, En × Er)
              (associatedBundleMk G P (OrthogonalSphere r) p) y)⟩) := by
  classical
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  intro e base j z p y hz
  rcases z with ⟨z, ξ⟩
  change associatedBundleMk G P (OrthogonalSphere r) p y = z at hz
  subst z
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  let q := smoothAssociatedSphereProjection S
  let hq := associatedSphereProjection_isSubmersion S
  let := verticalTangentFiberBundle q hq
  let := verticalTangentVectorBundle q hq
  let := verticalTangentContMDiffVectorBundle q hq
  let split := H.cotangentSplitHomeomorph q hq
  let ξB := ξ.comp (H.lift z)
  let η : Y := ⟨y, ξ.comp (mfderiv (𝓡 r) 𝓘(ℝ, En × Er)
    (associatedBundleMk G P (OrthogonalSphere r) p) y)⟩
  let p₀ : Q := ⟨((⟨projection p, ξB⟩ : X), p), rfl⟩
  let w := associatedBundleMk G Q Y p₀ η
  -- The actual sphere derivative and its inverse identify the entire vertical covector.
  have hvertical : (associatedSphereCotangentRepresentative S p η).snd =
      verticalCotangentRestriction q z ξ := by
    apply ContinuousLinearMap.ext
    intro v
    let d := associatedSphereFiberTangentEquiv S p y
    change ξ (mfderiv (𝓡 r) 𝓘(ℝ, En × Er)
      (associatedBundleMk G P (OrthogonalSphere r) p) y (d.symm v)) = ξ v.val
    apply congrArg ξ
    have hd := (exists_associatedSphereFiberTangentEquiv S p y).choose_spec (d.symm v)
    change (d (d.symm v)).val = _ at hd
    rw [d.apply_symm_apply] at hd
    exact hd.symm
  -- The original quotient representative has exactly the same image under the chosen splitting.
  have hew : e w = (⟨z, ξ⟩ : NativeCot) := by
    apply split.injective
    have he := (exists_associatedSphereCotangentHomeomorph S H).choose_spec p₀ η
    change e w = split.symm _ at he
    rw [he, split.apply_symm_apply]
    have hs := (SmoothHorizontalLift.exists_cotangentSplitHomeomorph q hq H).choose_spec.1
      (⟨z, ξ⟩ : NativeCot)
    change split (⟨z, ξ⟩ : NativeCot) = _ at hs
    rw [hs]
    exact congrArg (fun v ↦ (⟨z, ξB, v⟩ :
      TotalSpace ((En →L[ℝ] ℝ) × (VerticalTangentModel (En × Er) En →L[ℝ] ℝ))
        (((q : Z → B) *ᵖ (fun b : B ↦ TangentSpace (𝓡 n) b →L[ℝ] ℝ)) ×ᵇ
          VerticalCotangentFiber (q : Z → B)))) hvertical
  -- Apply the actual inverse and then the unchanged paired quotient map.
  have hinverse : e.symm (⟨z, ξ⟩ : NativeCot) = w := by
    rw [← hew, e.symm_apply_apply]
  change j (e.symm (⟨z, ξ⟩ : NativeCot)) = _
  rw [hinverse]
  rfl


variable (E₀ : B → Type*) [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [TopologicalSpace (TotalSpace Unit E₀)] [IsFiniteRank E₀]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace Unit E₁)] [IsFiniteRank E₁]
  (F₀ F₁ : OrthogonalSphere r → Type)
  [∀ y, AddCommGroup (F₀ y)] [∀ y, Module ℂ (F₀ y)]
  [∀ y, AddCommGroup (F₁ y)] [∀ y, Module ℂ (F₁ y)]
  [TopologicalSpace (TotalSpace Unit F₀)] [IsFiniteRank F₀]
  [TopologicalSpace (TotalSpace Unit F₁)] [IsFiniteRank F₁]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- Four original tensor comparisons retain their native dependent pullback topologies.
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option cleanup.letToHave false in
/-- The original graded tensor isomorphisms retain the exact reciprocal boundary action. -/
theorem exists_associatedSphereCotangentGradedTensorIso
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (σ₀ : EquivariantStructure G F₀) (σ₁ : EquivariantStructure G F₁) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    let pY := cotangentProjection (n := r) (M := OrthogonalSphere r)
    let σY₀ := σ₀.pullback pY (fun _ _ ↦ rfl)
    let σY₁ := σ₁.pullback pY (fun _ _ ↦ rfl)
    let D₀ := AssociatedEquivariantFiber S.toIsPrincipalBundle σ₀
    let D₁ := AssociatedEquivariantFiber S.toIsPrincipalBundle σ₁
    let DY₀ := AssociatedEquivariantFiber S.toIsPrincipalBundle σY₀
    let DY₁ := AssociatedEquivariantFiber S.toIsPrincipalBundle σY₁
    letI (z : Z) : AddCommGroup (D₀ z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ₀ z
    letI (z : Z) : Module ℂ (D₀ z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ₀ z
    letI (z : Z) : AddCommGroup (D₁ z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ₁ z
    letI (z : Z) : Module ℂ (D₁ z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ₁ z
    letI (z : AssociatedBundle G P Y) : AddCommGroup (DY₀ z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σY₀ z
    letI (z : AssociatedBundle G P Y) : Module ℂ (DY₀ z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σY₀ z
    letI (z : AssociatedBundle G P Y) : AddCommGroup (DY₁ z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σY₁ z
    letI (z : AssociatedBundle G P Y) : Module ℂ (DY₁ z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σY₁ z
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let e := associatedSphereCotangentHomeomorph S H
    let inverse : C(NativeCot, W) := ⟨e.symm, e.symm.continuous⟩
    let proj : C(NativeCot, Z) := ⟨TotalSpace.proj,
      FiberBundle.continuous_proj ((En × Er) →L[ℝ] ℝ) CotFiber⟩
    let j := associatedBundlePullbackProdMap
      («G» := G) («Y» := Y) (projection := projection) f
    let A₀ := (ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ (f *ᵖ E₀)
    let A₁ := (ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ (f *ᵖ E₁)
    let B₀ := (ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ DY₀
    let B₁ := (ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ DY₁
    let P₀₀ := fun z ↦ A₀ z ⊗[ℂ] B₀ z
    let P₁₁ := fun z ↦ A₁ z ⊗[ℂ] B₁ z
    let P₁₀ := fun z ↦ A₁ z ⊗[ℂ] B₀ z
    let P₀₁ := fun z ↦ A₀ z ⊗[ℂ] B₁ z
    let T₀₀ := fun z : Z ↦ ((base : Z → B) *ᵖ E₀) z ⊗[ℂ] D₀ z
    let T₁₁ := fun z : Z ↦ ((base : Z → B) *ᵖ E₁) z ⊗[ℂ] D₁ z
    let T₁₀ := fun z : Z ↦ ((base : Z → B) *ᵖ E₁) z ⊗[ℂ] D₀ z
    let T₀₁ := fun z : Z ↦ ((base : Z → B) *ᵖ E₀) z ⊗[ℂ] D₁ z
    letI : TopologicalSpace (TotalSpace Unit P₀₀) := tensorTopology (E := A₀) (F := B₀)
    letI : TopologicalSpace (TotalSpace Unit P₁₁) := tensorTopology (E := A₁) (F := B₁)
    letI : TopologicalSpace (TotalSpace Unit P₁₀) := tensorTopology (E := A₁) (F := B₀)
    letI : TopologicalSpace (TotalSpace Unit P₀₁) := tensorTopology (E := A₀) (F := B₁)
    letI : TopologicalSpace (TotalSpace Unit T₀₀) :=
      tensorTopology (E := (base : Z → B) *ᵖ E₀) (F := D₀)
    letI : TopologicalSpace (TotalSpace Unit T₁₁) :=
      tensorTopology (E := (base : Z → B) *ᵖ E₁) (F := D₁)
    letI : TopologicalSpace (TotalSpace Unit T₁₀) :=
      tensorTopology (E := (base : Z → B) *ᵖ E₁) (F := D₀)
    letI : TopologicalSpace (TotalSpace Unit T₀₁) :=
      tensorTopology (E := (base : Z → B) *ᵖ E₀) (F := D₁)
    let Source := P₀₀ ×ᵇ P₁₁
    let Target := P₁₀ ×ᵇ P₀₁
    let NativeSource := T₀₀ ×ᵇ T₁₁
    let NativeTarget := T₁₀ ×ᵇ T₀₁
    letI : TopologicalSpace (TotalSpace Unit Source) := sumTopology (E := P₀₀) (F := P₁₁)
    letI : TopologicalSpace (TotalSpace Unit Target) := sumTopology (E := P₁₀) (F := P₀₁)
    letI : TopologicalSpace (TotalSpace Unit NativeSource) := sumTopology (E := T₀₀) (F := T₁₁)
    letI : TopologicalSpace (TotalSpace Unit NativeTarget) := sumTopology (E := T₁₀) (F := T₀₁)
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ Source)) := pullbackTopology Unit Source j
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ Target)) := pullbackTopology Unit Target j
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ Source))) :=
      pullbackTopology Unit (j *ᵖ Source) inverse
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ Target))) :=
      pullbackTopology Unit (j *ᵖ Target) inverse
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ P₀₀)) := pullbackTopology Unit P₀₀ j
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ P₀₀))) :=
      pullbackTopology Unit (j *ᵖ P₀₀) inverse
    letI : TopologicalSpace (TotalSpace Unit (proj *ᵖ T₀₀)) := pullbackTopology Unit T₀₀ proj
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ P₁₁)) := pullbackTopology Unit P₁₁ j
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ P₁₁))) :=
      pullbackTopology Unit (j *ᵖ P₁₁) inverse
    letI : TopologicalSpace (TotalSpace Unit (proj *ᵖ T₁₁)) := pullbackTopology Unit T₁₁ proj
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ P₁₀)) := pullbackTopology Unit P₁₀ j
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ P₁₀))) :=
      pullbackTopology Unit (j *ᵖ P₁₀) inverse
    letI : TopologicalSpace (TotalSpace Unit (proj *ᵖ T₁₀)) := pullbackTopology Unit T₁₀ proj
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ P₀₁)) := pullbackTopology Unit P₀₁ j
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ P₀₁))) :=
      pullbackTopology Unit (j *ᵖ P₀₁) inverse
    letI : TopologicalSpace (TotalSpace Unit (proj *ᵖ T₀₁)) := pullbackTopology Unit T₀₁ proj
    let data₀₀ := exists_associatedSphereCotangentTensorIso S H E₀ F₀ σ₀
    let data₁₁ := exists_associatedSphereCotangentTensorIso S H E₁ F₁ σ₁
    let data₁₀ := exists_associatedSphereCotangentTensorIso S H E₁ F₀ σ₀
    let data₀₁ := exists_associatedSphereCotangentTensorIso S H E₀ F₁ σ₁
    let a₀₀ := data₀₀.choose_spec.choose_spec.choose
    let a₁₁ := data₁₁.choose_spec.choose_spec.choose
    let a₁₀ := data₁₀.choose_spec.choose_spec.choose
    let a₀₁ := data₀₁.choose_spec.choose_spec.choose
    ∃ aS : Iso (inverse *ᵖ (j *ᵖ Source)) (proj *ᵖ NativeSource),
      ∃ aT : Iso (inverse *ᵖ (j *ᵖ Target)) (proj *ᵖ NativeTarget),
        (∀ z, aS.linearEquiv z = (a₀₀.linearEquiv z).prodCongr (a₁₁.linearEquiv z)) ∧
        (∀ z, aT.linearEquiv z = (a₁₀.linearEquiv z).prodCongr (a₀₁.linearEquiv z)) ∧
        ∀ (d : Hom (f *ᵖ E₀) (f *ᵖ E₁)) (d' : Hom (f *ᵖ E₁) (f *ᵖ E₀))
          (q : Hom (pY *ᵖ F₀) (pY *ᵖ F₁)) (q' : Hom (pY *ᵖ F₁) (pY *ᵖ F₀))
          (hq : q.IsEquivariant σY₀ σY₁) (hq' : q'.IsEquivariant σY₁ σY₀)
          (z : NativeCot) (p : P) (y : OrthogonalSphere r)
          (hz : associatedBundleMk G P (OrthogonalSphere r) p y = z.proj),
          let η : Y := ⟨y, z.snd.comp (mfderiv (𝓡 r) 𝓘(ℝ, En × Er)
            (associatedBundleMk G P (OrthogonalSphere r) p) y)⟩
          let hη := (congrArg Prod.snd
            (associatedSphereCotangentHomeomorph_symm_paired_apply S H z p y hz)).symm
          let hbase := data₀₀.choose z
          let ξ : X := ⟨base z.proj, z.snd.comp (H.lift z.proj)⟩
          ∀ (u₀ : E₀ (f (j (inverse z)).1)) (u₁ : E₁ (f (j (inverse z)).1))
            (v₀ : F₀ y) (v₁ : F₁ y),
            let w :=
              (u₀ ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY₀ p η hη v₀,
                u₁ ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY₁ p η hη v₁)
            aS.linearEquiv z w =
                (cast (congrArg E₀ hbase) u₀ ⊗ₜ[ℂ]
                    associatedEquivariantFiberMk S.toIsPrincipalBundle σ₀ p y hz v₀,
                  cast (congrArg E₁ hbase) u₁ ⊗ₜ[ℂ]
                    associatedEquivariantFiberMk S.toIsPrincipalBundle σ₁ p y hz v₁) ∧
              aT.linearEquiv z
                  (reciprocalTensorSymbol (d.linearMap (j (inverse z)).1)
                    (d'.linearMap (j (inverse z)).1)
                    ((associatedEquivariantHom S.toIsPrincipalBundle σY₀ σY₁ q hq).linearMap
                      (j (inverse z)).2)
                    ((associatedEquivariantHom S.toIsPrincipalBundle σY₁ σY₀ q' hq').linearMap
                      (j (inverse z)).2) w) =
                (Sub.sub (α := T₁₀ (proj z))
                  (d.linearMap ξ (cast (congrArg E₀ hbase) u₀) ⊗ₜ[ℂ]
                    associatedEquivariantFiberMk S.toIsPrincipalBundle σ₀ p y hz v₀)
                  (cast (congrArg E₁ hbase) u₁ ⊗ₜ[ℂ]
                    associatedEquivariantFiberMk S.toIsPrincipalBundle σ₀ p y hz
                      (q'.linearMap η v₁)),
                  Add.add (α := T₀₁ (proj z))
                  (cast (congrArg E₀ hbase) u₀ ⊗ₜ[ℂ]
                    associatedEquivariantFiberMk S.toIsPrincipalBundle σ₁ p y hz
                      (q.linearMap η v₀))
                  (d'.linearMap ξ (cast (congrArg E₁ hbase) u₁) ⊗ₜ[ℂ]
                    associatedEquivariantFiberMk S.toIsPrincipalBundle σ₁ p y hz v₁)) := by
  classical
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  intro pY σY₀ σY₁ D₀ D₁ DY₀ DY₁
  let (z : Z) : AddCommGroup (D₀ z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ₀ z
  let (z : Z) : Module ℂ (D₀ z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ₀ z
  let (z : Z) : AddCommGroup (D₁ z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ₁ z
  let (z : Z) : Module ℂ (D₁ z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ₁ z
  let (z : AssociatedBundle G P Y) : AddCommGroup (DY₀ z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σY₀ z
  let (z : AssociatedBundle G P Y) : Module ℂ (DY₀ z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σY₀ z
  let (z : AssociatedBundle G P Y) : AddCommGroup (DY₁ z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σY₁ z
  let (z : AssociatedBundle G P Y) : Module ℂ (DY₁ z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σY₁ z
  intro base e inverse proj j A₀ A₁ B₀ B₁ P₀₀ P₁₁ P₁₀ P₀₁ T₀₀ T₁₁ T₁₀ T₀₁
  let := tensorTopology (E := A₀) (F := B₀)
  let := tensorTopology (E := A₁) (F := B₁)
  let := tensorTopology (E := A₁) (F := B₀)
  let := tensorTopology (E := A₀) (F := B₁)
  let := tensorTopology (E := (base : Z → B) *ᵖ E₀) (F := D₀)
  let := tensorTopology (E := (base : Z → B) *ᵖ E₁) (F := D₁)
  let := tensorTopology (E := (base : Z → B) *ᵖ E₁) (F := D₀)
  let := tensorTopology (E := (base : Z → B) *ᵖ E₀) (F := D₁)
  intro Source Target NativeSource NativeTarget
  let := sumTopology (E := P₀₀) (F := P₁₁)
  let := sumTopology (E := P₁₀) (F := P₀₁)
  let := sumTopology (E := T₀₀) (F := T₁₁)
  let := sumTopology (E := T₁₀) (F := T₀₁)
  let := pullbackTopology Unit Source j
  let := pullbackTopology Unit Target j
  let := pullbackTopology Unit (j *ᵖ Source) inverse
  let := pullbackTopology Unit (j *ᵖ Target) inverse
  let := pullbackTopology Unit P₀₀ j
  let := pullbackTopology Unit (j *ᵖ P₀₀) inverse
  let := pullbackTopology Unit T₀₀ proj
  let := pullbackTopology Unit P₁₁ j
  let := pullbackTopology Unit (j *ᵖ P₁₁) inverse
  let := pullbackTopology Unit T₁₁ proj
  let := pullbackTopology Unit P₁₀ j
  let := pullbackTopology Unit (j *ᵖ P₁₀) inverse
  let := pullbackTopology Unit T₁₀ proj
  let := pullbackTopology Unit P₀₁ j
  let := pullbackTopology Unit (j *ᵖ P₀₁) inverse
  let := pullbackTopology Unit T₀₁ proj
  intro data₀₀ data₁₁ data₁₀ data₀₁ a₀₀ a₁₁ a₁₀ a₀₁
  -- Source and target use the same nested pullback/sum comparisons, in their prescribed order.
  let := sumTopology (E := j *ᵖ P₀₀) (F := j *ᵖ P₁₁)
  let := pullbackTopology Unit ((j *ᵖ P₀₀) ×ᵇ (j *ᵖ P₁₁)) inverse
  let := sumTopology (E := inverse *ᵖ (j *ᵖ P₀₀)) (F := inverse *ᵖ (j *ᵖ P₁₁))
  let := sumTopology (E := proj *ᵖ T₀₀) (F := proj *ᵖ T₁₁)
  let := sumTopology (E := j *ᵖ P₁₀) (F := j *ᵖ P₀₁)
  let := pullbackTopology Unit ((j *ᵖ P₁₀) ×ᵇ (j *ᵖ P₀₁)) inverse
  let := sumTopology (E := inverse *ᵖ (j *ᵖ P₁₀)) (F := inverse *ᵖ (j *ᵖ P₀₁))
  let := sumTopology (E := proj *ᵖ T₁₀) (F := proj *ᵖ T₀₁)
  let s₀ := ((pullbackSumIso j P₀₀ P₁₁).pullback inverse).trans
    (pullbackSumIso inverse (j *ᵖ P₀₀) (j *ᵖ P₁₁))
  let s₁ := ((pullbackSumIso j P₁₀ P₀₁).pullback inverse).trans
    (pullbackSumIso inverse (j *ᵖ P₁₀) (j *ᵖ P₀₁))
  let aS := s₀.trans ((a₀₀.sum a₁₁).trans (pullbackSumIso proj T₀₀ T₁₁).symm)
  let aT := s₁.trans ((a₁₀.sum a₀₁).trans (pullbackSumIso proj T₁₀ T₀₁).symm)
  refine ⟨aS, aT, fun _ ↦ rfl, (fun _ ↦ rfl), ?_⟩
  intro d d' q q' hq hq' z p y hz η hη hbase ξ u₀ u₁ v₀ v₁ w
  -- Each tensor corner retains its own selected iso and the same principal representative.
  have h₀₀ := data₀₀.choose_spec.choose_spec.choose_spec z p η hη
  have h₁₁ := data₁₁.choose_spec.choose_spec.choose_spec z p η hη
  have h₁₀ (u : E₁ (f (j (inverse z)).1)) (v : F₀ y) :
      a₁₀.linearEquiv z
          (u ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY₀ p η hη v) =
        cast (congrArg E₁ hbase) u ⊗ₜ[ℂ]
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ₀ p y hz v :=
    data₁₀.choose_spec.choose_spec.choose_spec z p η hη u v
  have h₀₁ (u : E₀ (f (j (inverse z)).1)) (v : F₁ y) :
      a₀₁.linearEquiv z
          (u ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σY₁ p η hη v) =
        cast (congrArg E₀ hbase) u ⊗ₜ[ℂ]
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ₁ p y hz v :=
    data₀₁.choose_spec.choose_spec.choose_spec z p η hη u v
  have hx : (j (inverse z)).1 = ξ :=
    congrArg Prod.fst
      (associatedSphereCotangentHomeomorph_symm_paired_apply S H z p y hz)
  -- Equality of the full base covectors transports both original horizontal maps.
  have hcast₀ (x x' : X) (h : x = x') (u : E₀ (f x)) :
      cast (congrArg E₁ (congrArg (fun t : X ↦ f t) h)) (d.linearMap x u) =
        d.linearMap x' (cast (congrArg E₀ (congrArg (fun t : X ↦ f t) h)) u) := by
    subst x'
    rfl
  have hcast₁ (x x' : X) (h : x = x') (u : E₁ (f x)) :
      cast (congrArg E₀ (congrArg (fun t : X ↦ f t) h)) (d'.linearMap x u) =
        d'.linearMap x' (cast (congrArg E₁ (congrArg (fun t : X ↦ f t) h)) u) := by
    subst x'
    rfl
  constructor
  · -- The even coordinates are precisely the two original diagonal pure tensors.
    exact Prod.ext (h₀₀ u₀ v₀) (h₁₁ u₁ v₁)
  · -- Descent evaluates the two sphere maps at the actual inclusion-derived covector.
    change ((a₁₀.linearEquiv z).prodCongr (a₀₁.linearEquiv z)) _ = _
    simp only [reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod, w,
      LinearMap.coprod_apply,
      LinearMap.neg_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.prodCongr_apply, associatedEquivariantHom_apply]
    erw [(a₁₀.linearEquiv z).map_add, (a₁₀.linearEquiv z).toLinearMap.map_neg,
      (a₀₁.linearEquiv z).map_add, h₁₀, h₁₀, h₀₁, h₀₁]
    erw [hcast₀ _ _ hx u₀, hcast₁ _ _ hx u₁]
    rfl

end AtiyahSinger
