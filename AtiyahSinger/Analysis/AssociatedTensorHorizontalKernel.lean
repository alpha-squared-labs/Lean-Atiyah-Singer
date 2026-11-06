/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCoefficientPseudodifferential
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalVerticalCommutation
public import AtiyahSinger.Analysis.AssociatedTensorVerticalKernelRealization
public import AtiyahSinger.Analysis.AtlasTensorCoefficientPiece
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential

/-!
# Horizontal intertwining with finite associated coefficients

Public module ID: M0168.

A supplied finite representation family and fiber evaluation map intertwine the
horizontal lift with the associated coefficient PDO. The proof compares
normalized principal coordinates, contracts finite coefficient frames, and
sums the same localized pieces. It retains the spatial cutoffs and complete
operator action.

Source: the kernel-coefficient application in SG III.13.6. The intertwining
theorem applies to any supplied family satisfying its evaluation equation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology tensorTopology continuousSMul_orthogonalSphere

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


variable (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "V" => Fin ρ.dimension → ℂ
local notation "C" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation

omit [IsManifold (𝓡 n) ∞ B] in
set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorEvaluation_principal_coordinates
    (s : V →ₗ[ℂ] A.smoothSections) (ev : Hom ((πS : Z → B) *ᵖ C) D)
    (hev : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y))
    (b : B) (p : P) (hp : projection p ∈ (S.trivialization b).baseSet)
    (hg : (S.trivialization b p).2 = 1)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (hpe : projection p ∈ e.baseSet) (y : OrthogonalSphere r)
    (l : F y →ₗ[ℂ] ℂ) (i : Fin a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    ∀ v : E (projection p) ⊗[ℂ] C (projection p),
      (e ⟨projection p, TensorProduct.lid ℂ (E (projection p))
        (TensorProduct.map l LinearMap.id
          (TensorProduct.comm ℂ (E (projection p)) (F y)
            ((associatedSphereTensorFiberEquiv S E σ p y).symm
              (TensorProduct.map LinearMap.id
                (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)) v))))⟩).2 i =
        l ((s (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨projection p, v⟩).2
          (finProdFinEquiv (i, k)))).val y) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let AK := associatedOrthogonalRepresentationAtlas S ρ
  let AC := tensorSmoothAtlas AE AK
  have hpc : projection p ∈ (AK.chart b).baseSet :=
    (associatedOrthogonalRepresentationChart_properties S ρ b).1.symm ▸ hp
  have hTC := (exists_tensor_trivialization (AE.chart ⟨e, he⟩) (AK.chart b)
    (AE.linear ⟨e, he⟩) (AK.linear b)).choose_spec
  have hpTC : projection p ∈ (AC.chart (⟨e, he⟩, b)).baseSet :=
    hTC.1.symm ▸ ⟨hpe, hpc⟩
  dsimp only
  intro v
  -- Pure coefficients use the same normalized principal representative on both sides.
  induction v using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨w₀, rfl⟩ := (associatedVectorFiberMk_bijective S.toIsPrincipalBundle
      ρ.representation p rfl).2 w
    have hrow : (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨projection p,
        v ⊗ₜ[ℂ] associatedVectorFiberMk S.toIsPrincipalBundle
          ρ.representation p rfl w₀⟩).2 (finProdFinEquiv (i, k))) =
          (e ⟨projection p, v⟩).2 i • w₀ := by
      funext k
      have hc := (associatedOrthogonalRepresentationChart_properties S ρ b).2
        p (projection p) rfl w₀ hp
      rw [hg] at hc
      simp only [map_one] at hc
      exact (hTC.2.2 (projection p) ⟨hpe, hpc⟩ v _ i k).trans
        (congrArg ((e ⟨projection p, v⟩).2 i * ·) (congrFun hc k))
    erw [hrow]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, hev]
    rw [show v ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl
        ((s w₀).val y) = associatedSphereTensorFiberEquiv S E σ p y
          (v ⊗ₜ[ℂ] (s w₀).val y) from rfl, LinearEquiv.symm_apply_apply]
    simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.lid_tmul, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h := congrArg (fun z : EuclideanSpace ℂ (Fin a) ↦ z i)
      ((e.linearEquivAt ℂ (projection p) hpe).map_smul (l ((s w₀).val y)) v)
    change (e ⟨projection p, l ((s w₀).val y) • v⟩).2 i =
      l ((s w₀).val y) * (e ⟨projection p, v⟩).2 i at h
    exact h.trans (mul_comm _ _)
  | add v w hv hw =>
    -- Linearity extends the identity to every coefficient tensor, including rank zero.
    have hc := (AC.linear (⟨e, he⟩, b) _ hpTC).map_add v w
    have hrow : (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨projection p, v + w⟩).2
        (finProdFinEquiv (i, k))) =
      (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨projection p, v⟩).2 (finProdFinEquiv (i, k))) +
      (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨projection p, w⟩).2 (finProdFinEquiv (i, k))) := by
      rw [hc]
      rfl
    erw [hrow]
    simp only [LinearMap.map_add, LinearEquiv.map_add, Submodule.coe_add, Pi.add_apply]
    have h := congrArg (fun z : EuclideanSpace ℂ (Fin a) ↦ z i)
      ((e.linearEquivAt ℂ (projection p) hpe).map_add
        (TensorProduct.lid ℂ (E (projection p))
          (TensorProduct.map l LinearMap.id (TensorProduct.comm ℂ _ _
            ((associatedSphereTensorFiberEquiv S E σ p y).symm
              (TensorProduct.map LinearMap.id (ev.linearMap _) v)))))
        (TensorProduct.lid ℂ (E (projection p))
          (TensorProduct.map l LinearMap.id (TensorProduct.comm ℂ _ _
            ((associatedSphereTensorFiberEquiv S E σ p y).symm
              (TensorProduct.map LinearMap.id (ev.linearMap _) w))))))
    apply Eq.trans h
    exact congrArg₂ (· + ·) hv hw

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cutoffBaseFamily_tensorEvaluation
    (s : V →ₗ[ℂ] A.smoothSections) (ev : Hom ((πS : Z → B) *ᵖ C) D)
    (hev : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y))
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B) (χ : B → ℝ)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (x : B) (hx : x ∈ (S.trivialization b).baseSet) (hxe : x ∈ e.baseSet)
    (y : OrthogonalSphere r) (l : F y →ₗ[ℂ] ℂ) (i : Fin a)
    (u : ∀ x, E x ⊗[ℂ] C x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
      (associatedOrthogonalRepresentationAtlas S ρ)
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections),
      (∀ z, w.val z = TensorProduct.map LinearMap.id (ev.linearMap z) (u (πS z))) →
      (e ⟨x, TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id
          (associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ y w x))⟩).2 i =
        (χ x : ℂ) * l ((s (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨x, u x⟩).2
          (finProdFinEquiv (i, k)))).val y) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AC := tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
    (associatedOrthogonalRepresentationAtlas S ρ)
  dsimp only
  intro w hw
  let transport : ∀ {x z : B}, x = z → E x ≃ₗ[ℂ] E z := fun {x z} h ↦ by
    subst z
    exact LinearEquiv.refl ℂ (E x)
  have hcoords (p₀ : P) (x₀ : B) (hpx : projection p₀ = x₀)
      (hp : projection p₀ ∈ (S.trivialization b).baseSet)
      (hg : (S.trivialization b p₀).2 = 1) (he₀ : x₀ ∈ e.baseSet) :
      (e ⟨x₀, TensorProduct.lid ℂ (E x₀)
        (TensorProduct.map l LinearMap.id (TensorProduct.comm ℂ (E x₀) (F y)
          (TensorProduct.map (transport hpx).toLinearMap LinearMap.id
            ((associatedSphereTensorFiberEquiv S E σ p₀ y).symm
              (w.val (associatedBundleMk G P (OrthogonalSphere r) p₀ y))))))⟩).2 i =
        l ((s (fun k ↦ (AC.chart (⟨e, he⟩, b) ⟨x₀, u x₀⟩).2
          (finProdFinEquiv (i, k)))).val y) := by
    subst x₀
    simp only [transport, LinearEquiv.refl_toLinearMap, TensorProduct.map_id, LinearMap.id_apply]
    change (e ⟨projection p₀, TensorProduct.lid ℂ (E (projection p₀))
      (TensorProduct.map l LinearMap.id (TensorProduct.comm ℂ (E (projection p₀)) (F y)
        ((associatedSphereTensorFiberEquiv S E σ p₀ y).symm
          (w.val (associatedBundleMk G P (OrthogonalSphere r) p₀ y)))))⟩).2 i = _
    erw [hw]
    exact tensorEvaluation_principal_coordinates S E A σ ρ s ev hev
      b p₀ hp hg e he he₀ y l i (u (projection p₀))
  -- Normalize only inside the original principal domain, then apply its exact base transport.
  let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
  have hp : projection p = x := (S.trivialization b).proj_symm_apply' hx
  have hg : (S.trivialization b p).2 = 1 :=
    congrArg Prod.snd ((S.trivialization b).apply_symm_apply' hx)
  let v := (associatedSphereTensorFiberEquiv S E σ p y).symm
    (w.val (associatedBundleMk G P (OrthogonalSphere r) p y))
  have hvalue : associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ y w x =
      (χ x : ℂ) • TensorProduct.comm ℂ (E x) (F y)
        (TensorProduct.map (transport hp).toLinearMap LinearMap.id v) := by
    simp only [associatedSphereTensorCutoffBaseFamily, LinearMap.pi_apply, dite_eq_left hx,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
      Submodule.subtype_apply]
    rfl
  rw [hvalue, map_smul, map_smul]
  have h := congrArg (fun z : EuclideanSpace ℂ (Fin a) ↦ z i)
    ((e.linearEquivAt ℂ x hxe).map_smul (χ x : ℂ)
      (TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id
        (TensorProduct.comm ℂ (E x) (F y)
          (TensorProduct.map (transport hp).toLinearMap LinearMap.id v)))))
  apply h.trans
  exact congrArg ((χ x : ℂ) * ·) (hcoords p x hp (hp.symm ▸ hx) hg hxe)

variable {a' : ℕ} [T2Space B]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localHorizontalLift_tensorCoefficient {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (s : V →ₗ[ℂ] A.smoothSections) (ev : Hom ((πS : Z → B) *ᵖ C) D)
    (hev : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y))
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AK := associatedOrthogonalRepresentationAtlas S ρ
    let R := L.toAtlasPseudodifferentialPiece.tensorCoefficient AK b
      (fun z hz ↦ (associatedOrthogonalRepresentationChart_properties S ρ b).1.symm ▸
        hinput ⟨z, hz, rfl⟩)
      (fun z hz ↦ (associatedOrthogonalRepresentationChart_properties S ρ b).1.symm ▸
        houtput ⟨z, hz, rfl⟩)
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
      (u : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        AK).smoothSections),
      (∀ z, w.val z = TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) →
      ∀ z, (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E'
        L hσ b χ hχ hχsupport houtput w).val z =
          TensorProduct.map LinearMap.id (ev.linearMap z) ((R.toLinearMap u).val (πS z)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let AE' := nativeSmoothComplexBundleAtlas (n := n) (r := a') E'
  let AK := associatedOrthogonalRepresentationAtlas S ρ
  let AC := tensorSmoothAtlas AE AK
  let AC' := tensorSmoothAtlas AE' AK
  let hin : tsupport L.input.cutoff ⊆ L.chart.symm ⁻¹' (AK.chart b).baseSet :=
    fun z hz ↦ (associatedOrthogonalRepresentationChart_properties S ρ b).1.symm ▸
      hinput ⟨z, hz, rfl⟩
  let hout : tsupport L.output.cutoff ⊆ L.chart.symm ⁻¹' (AK.chart b).baseSet :=
    fun z hz ↦ (associatedOrthogonalRepresentationChart_properties S ρ b).1.symm ▸
      houtput ⟨z, hz, rfl⟩
  let R := L.toAtlasPseudodifferentialPiece.tensorCoefficient AK b hin hout
  dsimp only
  intro w u hw
  let H := associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E'
    L hσ b χ hχ hχsupport houtput
  let g := R.input.localize R.chart_mem_atlas u
  -- The actual amplified operator acts on every fixed coefficient contraction.
  have hcolumn (j : Fin ρ.dimension) :=
    L.toAtlasPseudodifferentialPiece.tensorCoefficient_operator_column AK b hin hout j
  choose Δ hΔ hRΔ using hcolumn
  have hform (ℓ : V →ₗ[ℂ] ℂ) (v : V) :
      ℓ v = ∑ k, ℓ (Pi.single k 1) * v k := by
    have hv : v = ∑ k, v k • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    calc
      ℓ v = ℓ (∑ k, v k • Pi.single k 1) := congrArg ℓ hv
      _ = ∑ k, ℓ (Pi.single k 1) * v k := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have hoperator (ℓ : V →ₗ[ℂ] ℂ)
      (f : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin a)))
      (hf : ∀ x i, f x i = ℓ (fun k ↦ g x (finProdFinEquiv (i, k))))
      (x : EuclideanSpace ℝ (Fin n)) (i : Fin a') :
      L.operator f x i = ℓ (fun k ↦ R.operator g x (finProdFinEquiv (i, k))) := by
    have hsum : f = ∑ k, ℓ (Pi.single k 1) • Δ k g := by
      apply SchwartzMap.ext
      intro z
      apply PiLp.ext
      intro j
      simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_apply,
        PiLp.smul_apply, smul_eq_mul]
      rw [hf, hform]
      exact Finset.sum_congr rfl (fun k _ ↦ congrArg (ℓ (Pi.single k 1) * ·) (hΔ k g z j).symm)
    calc
      L.operator f x i = ∑ k, ℓ (Pi.single k 1) * L.operator (Δ k g) x i := by
        rw [hsum, map_sum]
        simp only [map_smul, sum_apply, smul_apply, WithLp.ofLp_sum,
          Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
      _ = ∑ k, ℓ (Pi.single k 1) * R.operator g x (finProdFinEquiv (i, k)) :=
        Finset.sum_congr rfl (fun k _ ↦ congrArg (ℓ (Pi.single k 1) * ·) (hRΔ k g x i).symm)
      _ = ℓ (fun k ↦ R.operator g x (finProdFinEquiv (i, k))) := (hform ℓ _).symm
  have hinputContract (y : OrthogonalSphere r) (l : F y →ₗ[ℂ] ℂ) :
      let B₀ := associatedSphereTensorCutoffBaseRestriction (a := a)
        S E A σ hσ b χ hχ hχsupport y w
      let f : smoothSections (n := n) (r := a) E :=
        ⟨fun x ↦ TensorProduct.lid ℂ (E x)
          (TensorProduct.map l LinearMap.id (B₀.val x)), B₀.property l⟩
      ∀ z i, L.input.localize L.chart_mem_atlas f z i =
        l ((s (fun k ↦ g z (finProdFinEquiv (i, k)))).val y) := by
    dsimp only
    intro z i
    by_cases hz : z ∈ tsupport L.input.cutoff
    · have hzt := (L.input.support_subset hz).1
      have hzf := (L.input.support_subset hz).2
      have hzb := hinput ⟨z, hz, rfl⟩
      have hv := cutoffBaseFamily_tensorEvaluation S E A σ ρ s ev hev hσ b χ
        L.input.frame L.input.frame_mem_atlas (L.chart.symm z) hzb hzf y l i u.val w hw
      have hone := hχone (L.chart.symm z) ⟨z, hz, rfl⟩
      rw [hone, Complex.ofReal_one, one_mul] at hv
      change (L.input.localizedFunction _ z) i = _
      simp only [BundleChartCutoff.localizedFunction, ite_eq_left hzt, sectionInChart,
        PiLp.smul_apply, smul_eq_mul]
      erw [hv]
      have hrow : (fun k ↦ g z (finProdFinEquiv (i, k))) =
          (L.input.cutoff z : ℂ) • (fun k ↦ (AC.chart (⟨L.input.frame,
            L.input.frame_mem_atlas⟩, b) ⟨L.chart.symm z, u.val (L.chart.symm z)⟩).2
              (finProdFinEquiv (i, k))) := by
        funext k
        change (R.input.localizedFunction u z) (finProdFinEquiv (i, k)) = _
        simp only [AtlasChartCutoff.localizedFunction, atlasSectionInChart]
        erw [ite_eq_left hzt]
        rfl
      erw [hrow]
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    · have hz0 := image_eq_zero_of_notMem_tsupport hz
      have hg0 : g z = 0 := by
        change R.input.localizedFunction u z = 0
        simp [AtlasChartCutoff.localizedFunction, show R.input.cutoff z = 0 from hz0]
      change (L.input.localizedFunction _ z) i = _
      simp only [BundleChartCutoff.localizedFunction, hz0, Complex.ofReal_zero, zero_smul,
        ite_self, PiLp.zero_apply, hg0]
      change 0 = l ((s 0).val y)
      rw [map_zero]
      exact (map_zero l).symm
  -- The original output cutoff and inverse frame recover the exact finite coefficient action.
  have hscalar (x : B) (hxc : x ∈ L.chart.source)
      (hxf : x ∈ L.output.frame.baseSet) (hxb : x ∈ (S.trivialization b).baseSet)
      (y : OrthogonalSphere r) (l : F y →ₗ[ℂ] ℂ) (i : Fin a') :
      (L.output.frame ⟨x, TensorProduct.lid ℂ (E' x)
        (TensorProduct.map l LinearMap.id ((associatedSphereTensorHorizontalFamily (a := a)
          S E A σ E' L hσ b χ hχ hχsupport y w).val x))⟩).2 i =
        l ((s (fun k ↦ (AC'.chart (⟨L.output.frame, L.output.frame_mem_atlas⟩, b)
          ⟨x, (R.toLinearMap u).val x⟩).2 (finProdFinEquiv (i, k)))).val y) := by
    let ℓ : V →ₗ[ℂ] ℂ := l.comp ((LinearMap.proj y).comp (A.smoothSections.subtype.comp s))
    let B₀ := associatedSphereTensorCutoffBaseRestriction (a := a)
      S E A σ hσ b χ hχ hχsupport y w
    let f : smoothSections (n := n) (r := a) E :=
      ⟨fun x ↦ TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id (B₀.val x)), B₀.property l⟩
    let ef := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
    let : FiniteDimensional ℂ (F y) := .of_injective ef.toLinearMap ef.injective
    have hcontract : TensorProduct.lid ℂ (E' x) (TensorProduct.map l LinearMap.id
        ((associatedSphereTensorHorizontalFamily (a := a)
          S E A σ E' L hσ b χ hχ hχsupport y w).val x)) = (L.toLinearMap f).val x :=
      congrFun (tensorSectionOperator_contract (F y)
        (smoothSections E) (smoothSections E') L.toLinearMap B₀ l) x
    have hleft := congrArg (fun v : EuclideanSpace ℂ (Fin a') ↦ v i)
      (L.toLinearMap_in_frame f x hxc hxf)
    change (L.output.frame ⟨x, (L.toLinearMap f).val x⟩).2 i =
      (L.output.cutoff (L.chart x) : ℂ) * quantize L.symbol
        (L.input.localize L.chart_mem_atlas f) (L.chart x) i at hleft
    rw [← L.operator_apply] at hleft
    have hf : ∀ z i, L.input.localize L.chart_mem_atlas f z i =
        ℓ (fun k ↦ g z (finProdFinEquiv (i, k))) := hinputContract y l
    have hop := hoperator ℓ (L.input.localize L.chart_mem_atlas f) hf (L.chart x) i
    have hpc : x ∈ (AK.chart b).baseSet :=
      (associatedOrthogonalRepresentationChart_properties S ρ b).1.symm ▸ hxb
    have hTC := (exists_tensor_trivialization
      (AE'.chart ⟨L.output.frame, L.output.frame_mem_atlas⟩) (AK.chart b)
      (AE'.linear ⟨L.output.frame, L.output.frame_mem_atlas⟩) (AK.linear b)).choose_spec
    have hpTC : x ∈ (AC'.chart (⟨L.output.frame, L.output.frame_mem_atlas⟩, b)).baseSet :=
      hTC.1.symm ▸ ⟨hxf, hpc⟩
    have hframe (v : 𝓢(EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℂ (Fin (a' * ρ.dimension)))) (i : Fin a') (k : Fin ρ.dimension) :
        (AC'.chart (⟨L.output.frame, L.output.frame_mem_atlas⟩, b)
          ⟨x, R.output.extendedFunction v x⟩).2 (finProdFinEquiv (i, k)) =
        (L.output.cutoff (L.chart x) : ℂ) * v (L.chart x) (finProdFinEquiv (i, k)) := by
      change (AC'.frameLinearEquiv (⟨L.output.frame, L.output.frame_mem_atlas⟩, b) x hpTC
        (R.output.extendedFunction v x)) (finProdFinEquiv (i, k)) = _
      simp only [AtlasChartCutoff.extendedFunction]
      erw [dite_eq_left (show x ∈ R.chart.source ∩
        (AC'.chart R.output.frameIndex).baseSet from ⟨hxc, hpTC⟩)]
      change (AC'.frameLinearEquiv (⟨L.output.frame, L.output.frame_mem_atlas⟩, b) x hpTC
        ((L.output.cutoff (L.chart x) : ℂ) •
          (AC'.frameLinearEquiv (⟨L.output.frame, L.output.frame_mem_atlas⟩, b) x hpTC).symm
            ((EuclideanSpace.equiv (Fin (a' * ρ.dimension)) ℂ) (v (L.chart x)))))
              (finProdFinEquiv (i, k)) = _
      rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
      rfl
    have hrow : (fun k ↦ (AC'.chart (⟨L.output.frame, L.output.frame_mem_atlas⟩, b)
        ⟨x, (R.toLinearMap u).val x⟩).2 (finProdFinEquiv (i, k))) =
        (L.output.cutoff (L.chart x) : ℂ) •
          (fun k ↦ R.operator g (L.chart x) (finProdFinEquiv (i, k))) := by
      funext k
      exact hframe (R.operator g) i k
    have hright := congrArg ℓ hrow
    rw [map_smul] at hright
    erw [hcontract]
    exact (hleft.trans (congrArg ((L.output.cutoff (L.chart x) : ℂ) * ·) hop)).trans
      hright.symm
  have hnormalized (p : P) (hp : projection p ∈ (S.trivialization b).baseSet)
      (hg : (S.trivialization b p).2 = 1) (hpc : projection p ∈ L.chart.source)
      (hpf : projection p ∈ L.output.frame.baseSet) (y : OrthogonalSphere r) :
      (H w).val (associatedBundleMk G P (OrthogonalSphere r) p y) =
        TensorProduct.map LinearMap.id
          (ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y))
          ((R.toLinearMap u).val (projection p)) := by
    let x := projection p
    let := L.output.frame_mem_atlas
    let e := L.output.frame.linearEquivAt ℂ x hpf
    let ef := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
    let et := (TensorProduct.congr (LinearEquiv.refl ℂ (E' x)) ef).trans
      (TensorProduct.piScalarRight ℂ ℂ (E' x) (Fin (A.rank (A.covers y).choose)))
    have hcoord (t : E' x ⊗[ℂ] F y) (k : Fin (A.rank (A.covers y).choose)) :
        et t k = TensorProduct.lid ℂ (E' x)
          (TensorProduct.map ((LinearMap.proj k).comp ef.toLinearMap) LinearMap.id
            (TensorProduct.comm ℂ (E' x) (F y) t)) := by
      induction t using TensorProduct.inductionOn with
      | tmul v w => simp [et]
      | add v w hv hw => simp only [map_add, Pi.add_apply, hv, hw]
    apply (associatedSphereTensorFiberEquiv S E' σ p y).symm.injective
    apply et.injective
    funext k
    rw [hcoord, hcoord]
    apply e.injective
    apply PiLp.ext
    intro i
    have hH : (associatedSphereTensorFiberEquiv S E' σ p y).symm
        ((H w).val (associatedBundleMk G P (OrthogonalSphere r) p y)) =
        TensorProduct.comm ℂ (F y) (E' x)
          ((associatedSphereTensorHorizontalFamily (a := a)
            S E A σ E' L hσ b χ hχ hχsupport y w).val x) := by
      apply (associatedSphereTensorFiberEquiv S E' σ p y).injective
      rw [LinearEquiv.apply_symm_apply, associatedSphereTensorLocalHorizontalLift_apply,
        associatedSphereTensorBaseExtension_apply_mk S E' σ b p y hp hg]
    rw [hH, ← TensorProduct.comm_symm ℂ (F y) (E' x), LinearEquiv.symm_apply_apply]
    exact (hscalar x hpc hpf hp y ((LinearMap.proj k).comp ef.toLinearMap) i).trans
      (tensorEvaluation_principal_coordinates S E' A σ ρ s ev hev b p hp hg
        L.output.frame L.output.frame_mem_atlas hpf y
        ((LinearMap.proj k).comp ef.toLinearMap) i ((R.toLinearMap u).val x)).symm
  intro z
  by_cases hzout : πS z ∈ L.chart.symm '' tsupport L.output.cutoff
  · have hx := houtput hzout
    let t := associatedSphereTrivialization S b
    have hbase : t.baseSet = (S.trivialization b).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.1
    have hz : z ∈ t.source := t.mem_source.mpr (hbase.symm ▸ hx)
    have hfst : (t z).1 = πS z := t.proj_toFun z hz
    let p := (S.trivialization b).toOpenPartialHomeomorph.symm (πS z, 1)
    have hp : projection p = πS z := (S.trivialization b).proj_symm_apply' hx
    have hg : (S.trivialization b p).2 = 1 :=
      congrArg Prod.snd ((S.trivialization b).apply_symm_apply' hx)
    have hrep : associatedBundleMk G P (OrthogonalSphere r) p (t z).2 = z := by
      have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.2.2 (πS z) (t z).2 hx
      have hpair : (πS z, (t z).2) = t z := Prod.ext hfst.symm rfl
      rw [hpair] at h
      exact h.symm.trans (t.left_inv hz)
    have hxc : πS z ∈ L.chart.source := by
      obtain ⟨z', hz', heq⟩ := hzout
      exact heq ▸ L.chart.map_target (L.output.support_subset hz').1
    have hxf : πS z ∈ L.output.frame.baseSet := by
      obtain ⟨z', hz', heq⟩ := hzout
      exact heq ▸ (L.output.support_subset hz').2
    have h := hnormalized p (hp.symm ▸ hx) hg (hp.symm ▸ hxc) (hp.symm ▸ hxf) (t z).2
    exact hrep ▸ h
  · -- Both complete local maps vanish off the original base output support.
    have hH := associatedSphereTensorLocalHorizontalLift_apply_eq_zero (a := a)
      S E A σ E' L hσ b χ hχ hχsupport houtput z hzout w
    have hR := R.toLinearMap_support_properties.1 u (πS z) hzout
    change (H w).val z = TensorProduct.map LinearMap.id (ev.linearMap z)
      ((R.toLinearMap u).val (πS z))
    rw [hH, hR, map_zero]

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : MeasureTheory.Measure B} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual horizontal map intertwines full-fiber evaluation with the same coefficient PDO. -/
theorem PrincipalPseudodifferentialLocalization.horizontalLift_coefficientOperator {m : ℝ}
    (C₀ : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m)
    (s : V →ₗ[ℂ] A.smoothSections) (ev : Hom ((πS : Z → B) *ᵖ C) D)
    (hev : ∀ (p : P) (y : OrthogonalSphere r) (v : V),
      ev.linearMap (associatedBundleMk G P (OrthogonalSphere r) p y)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p rfl v) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl ((s v).val y))
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ (w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections)
      (u : (tensorSmoothAtlas (nativeSmoothComplexBundleAtlas (n := n) (r := a) E)
        (associatedOrthogonalRepresentationAtlas S ρ)).smoothSections),
      (∀ z, w.val z = TensorProduct.map LinearMap.id (ev.linearMap z) (u.val (πS z))) →
      ∀ z, (C₀.horizontalLift S E A σ E' hσ w).val z =
        TensorProduct.map LinearMap.id (ev.linearMap z)
          (((C₀.coefficientOperator S E E' ρ).toLinearMap u).val (πS z)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro w u hw z
  -- The base-only plateaus are the stored ones; every local comparison uses the same evaluation.
  simp only [PrincipalPseudodifferentialLocalization.horizontalLift,
    PrincipalPseudodifferentialLocalization.coefficientOperator,
    LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact localHorizontalLift_tensorCoefficient S E A σ ρ E' (C₀.piece j) s ev hev hσ
    (C₀.center j) (fun _ hx ↦ C₀.piece_support j (by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, Or.inr hy, rfl⟩))
    (fun _ hx ↦ C₀.piece_support j (by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, Or.inl hy, rfl⟩))
    (C₀.inputCutoff j) (C₀.smooth_inputCutoff j) (C₀.inputCutoff_support j)
    (C₀.inputCutoff_eq_one j) w u hw z

end AtiyahSinger
