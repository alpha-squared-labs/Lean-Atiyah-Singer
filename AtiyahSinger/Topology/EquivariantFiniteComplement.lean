/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantHilbertEmbedding
public import AtiyahSinger.Topology.FiniteBundle

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Continuous projections and equivariant finite complements

Public module ID: M1783.

An injective bundle map into a finite trivial bundle has a continuous family
of projections onto its original image. The proof uses a fixed finite
presentation and an invertible Gram operator, so it also applies when the
fiber rank varies locally. Averaging the projection in a representation
bundle retains its specified image and its identity restriction there.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle MeasureTheory

open scoped Matrix

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

attribute [local instance] trivialTopology IdempotentMatrix.fiberTotalSpaceTopology
  IdempotentMatrix.isFiniteRank_fiber

/-- A fiberwise injection into a finite trivial bundle has a continuous
projection onto its actual image, with no constant-rank assumption. -/
theorem Hom.exists_continuous_projection_range {n : ℕ}
    (q : Hom E (Bundle.Trivial X (Fin n → ℂ)))
    (hq : ∀ x, Function.Injective (q.linearMap x)) :
    ∃ P : X → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ), Continuous P ∧
      (∀ (x : X) (v : E x), P x (q.linearMap x v) = q.linearMap x v) ∧
      ∀ (x : X) (w : Fin n → ℂ), ∃ v : E x, P x w = q.linearMap x v := by
  classical
  let p := idempotentPresentation (E := E)
  let e : Iso E (fun x ↦ p.fiber x) := presentationIso
  let D := EuclideanSpace ℂ (Fin p.size)
  let F := EuclideanSpace ℂ (Fin n)
  let a : D ≃L[ℂ] (Fin p.size → ℂ) := EuclideanSpace.equiv (Fin p.size) ℂ
  let b : F ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  let B (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  have hB : Continuous B :=
    continuous_pi fun i ↦ continuous_pi fun j ↦ (p.matrix i j).continuous
  have hfix (x : X) (v : p.fiber x) : B x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ : ∃ w, B x *ᵥ w = v.val := v.property
    rw [← hw, Matrix.mulVec_mulVec]
    exact congrArg (fun A ↦ A *ᵥ w)
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  let r (x : X) : D →ₗ[ℂ] E x := (e.linearEquiv x).symm.toLinearMap.comp ({
    toFun u := ⟨B x *ᵥ a u, ⟨a u, rfl⟩⟩
    map_add' u v := by apply Subtype.ext; simp [map_add, Matrix.mulVec_add]
    map_smul' c u := by apply Subtype.ext; simp [map_smul, Matrix.mulVec_smul] } :
      D →ₗ[ℂ] p.fiber x)
  have hr : Continuous (fun z : X × D ↦
      (⟨z.1, r z.1 z.2⟩ : TotalSpace Unit E)) := by
    have hc : Continuous (fun z : X × D ↦
        (⟨z.1, ⟨B z.1 *ᵥ a z.2, ⟨a z.2, rfl⟩⟩⟩ :
          TotalSpace Unit (fun x ↦ p.fiber x))) := by
      apply continuous_induced_rng.mpr
      exact continuous_fst.prodMk ((hB.comp continuous_fst).matrix_mulVec
        (a.continuous.comp continuous_snd))
    exact e.continuous_symm.comp hc
  let C (x : X) : D →L[ℂ] D :=
    (a.symm.toLinearMap.comp ((Matrix.toLin' (B x)).comp a.toLinearMap)).toContinuousLinearMap
  have hC : Continuous C := by
    apply continuous_clm_apply.mpr
    intro u
    exact a.symm.continuous.comp (hB.matrix_mulVec continuous_const)
  have hCr (x : X) (u : D) : C x u = a.symm (e.linearEquiv x (r x u)).val := by
    change a.symm (B x *ᵥ a u) = a.symm (e.linearEquiv x ((e.linearEquiv x).symm _)).val
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hre (x : X) (v : E x) : r x (a.symm (e.linearEquiv x v).val) = v := by
    change (e.linearEquiv x).symm _ = v
    apply (e.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change B x *ᵥ a (a.symm (e.linearEquiv x v).val) = (e.linearEquiv x v).val
    rw [a.apply_symm_apply, hfix]
  let A (x : X) : D →L[ℂ] F :=
    (b.symm.toLinearMap.comp ((q.linearMap x).comp (r x))).toContinuousLinearMap
  have hA : Continuous A := by
    apply continuous_clm_apply.mpr
    intro u
    exact b.symm.continuous.comp
      ((continuous_induced_rng.mp q.continuous_total).snd.comp
        (hr.comp (continuous_id.prodMk continuous_const)))
  let L (x : X) : D →L[ℂ] D := 1 - C x
  have hL : Continuous L := continuous_const.sub hC
  -- Adding the complementary Gram form makes the operator invertible on the
  -- whole fixed coordinate space, even where the original bundle has rank 0.
  let T (x : X) : D →L[ℂ] D := (A x).adjoint ∘L A x + (L x).adjoint ∘L L x
  have hT : Continuous T :=
    ((ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp hA).add
      ((ContinuousLinearMap.adjoint.continuous.comp hL).clm_comp hL)
  have hunit (x : X) : IsUnit (T x) := by
    have hinj : Function.Injective (T x) := by
      apply LinearMap.ker_eq_bot.mp
      apply (Submodule.eq_bot_iff _).mpr
      intro u hu
      have hnorm : ‖A x u‖ ^ 2 + ‖L x u‖ ^ 2 = 0 := by
        have h := congrArg (fun v : D ↦ (inner ℂ u v).re) (show T x u = 0 from hu)
        simp only [T, add_apply, ContinuousLinearMap.comp_apply,
          inner_add_right, Complex.add_re, ContinuousLinearMap.adjoint_inner_right,
          inner_zero_right, Complex.zero_re] at h
        change RCLike.re (inner ℂ (A x u) (A x u)) +
          RCLike.re (inner ℂ (L x u) (L x u)) = 0 at h
        simpa only [inner_self_eq_norm_sq] using h
      have hAu : A x u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (by
        nlinarith [sq_nonneg ‖L x u‖]))
      have hLu : L x u = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (by
        nlinarith [sq_nonneg ‖A x u‖]))
      have hru : r x u = 0 := hq x (by
        have h := congrArg b hAu
        simpa [A] using h)
      have hCu : C x u = 0 := by rw [hCr, hru]; simp
      have h : u - C x u = 0 := hLu
      simpa only [hCu, sub_zero] using h
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (T x).toLinearMap)).mp hinj⟩
  let U (x : X) : D →L[ℂ] D := Ring.inverse (T x)
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun x ↦ by
    have hi := NormedRing.inverse_continuousAt (hunit x).unit
    rw [(hunit x).unit_spec] at hi
    exact hi.comp (hT.continuousAt)
  have hUT (x : X) (u : D) : U x (T x u) = u := by
    exact DFunLike.congr_fun (Ring.inverse_mul_cancel (T x) (hunit x)) u
  let P (x : X) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    b.toContinuousLinearMap ∘L A x ∘L U x ∘L (A x).adjoint ∘L b.symm.toContinuousLinearMap
  refine ⟨P, ?_, ?_, ?_⟩
  · exact continuous_const.clm_comp (hA.clm_comp (hU.clm_comp
      ((ContinuousLinearMap.adjoint.continuous.comp hA).clm_comp continuous_const)))
  · -- On the specified image the complementary Gram term vanishes, so the
    -- inverse Gram operator recovers precisely the original coordinate vector.
    intro x v
    let u : D := a.symm (e.linearEquiv x v).val
    have hru : r x u = v := hre x v
    have hLu : L x u = 0 := by
      change u - C x u = 0
      rw [hCr, hru]
      exact sub_self u
    have hTu : T x u = (A x).adjoint (b.symm (q.linearMap x v)) := by
      change (A x).adjoint (A x u) + (L x).adjoint (L x u) = _
      rw [hLu, map_zero, add_zero]
      change (A x).adjoint (b.symm (q.linearMap x (r x u))) = _
      rw [hru]
    change b (A x (U x ((A x).adjoint (b.symm (q.linearMap x v))))) = q.linearMap x v
    rw [← hTu, hUT]
    change b (b.symm (q.linearMap x (r x u))) = q.linearMap x v
    rw [b.apply_symm_apply, hru]
  · intro x w
    refine ⟨r x (U x ((A x).adjoint (b.symm w))), ?_⟩
    exact b.apply_symm_apply _

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MulAction G X] [ContinuousSMul G X]

/-- Averaging projections in a finite representation bundle preserves the
original equivariant image and its identity restriction there. -/
theorem Hom.exists_equivariant_projection_range
    (σ : EquivariantStructure G E) (κ : FiniteContinuousRepresentation G)
    (q : Hom E (Bundle.Trivial X (Fin κ.dimension → ℂ)))
    (hq : ∀ x, Function.Injective (q.linearMap x))
    (heq : q.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation κ)) :
    ∃ P : X → (Fin κ.dimension → ℂ) →L[ℂ] (Fin κ.dimension → ℂ), Continuous P ∧
      (∀ (x : X) (v : E x), P x (q.linearMap x v) = q.linearMap x v) ∧
      (∀ (x : X) (w : Fin κ.dimension → ℂ), ∃ v : E x, P x w = q.linearMap x v) ∧
      ∀ (g : G) (x : X) (w : Fin κ.dimension → ℂ),
        P (g • x) (κ.representation g w) = κ.representation g (P x w) := by
  classical
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haar
  let μ : Measure G := (ν Set.univ)⁻¹ • ν
  let V := Fin κ.dimension → ℂ
  have hqequiv (g : G) (x : X) (v : E x) :
      q.linearMap (g • x) (σ.linearMap g x v) = κ.representation g (q.linearMap x v) :=
    heq g x v
  obtain ⟨P₀, hP₀, hfix, hrange⟩ := q.exists_continuous_projection_range hq
  have hκ : Continuous (fun g : G ↦ κ.representation g) :=
    continuous_clm_apply.mpr fun v ↦
      κ.continuous_action.comp (continuous_id.prodMk continuous_const)
  let R (x : X) (g : G) : V →L[ℂ] V :=
    κ.representation g ∘L P₀ (g⁻¹ • x) ∘L κ.representation g⁻¹
  have hR : Continuous (fun z : X × G ↦ R z.1 z.2) :=
    (hκ.comp continuous_snd).clm_comp
      ((hP₀.comp (continuous_snd.inv.smul continuous_fst)).clm_comp
        (hκ.comp continuous_snd.inv))
  have hRI (x : X) : Integrable (R x) μ :=
    (hR.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRvI (x : X) (v : V) : Integrable (fun g ↦ R x g v) μ :=
    ((hR.comp (continuous_const.prodMk continuous_id)).clm_apply
      continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P (x : X) : V →L[ℂ] V := ∫ g, R x g ∂μ
  have happly (x : X) (v : V) : P x v = ∫ g, R x g v ∂μ :=
    ContinuousLinearMap.integral_apply (hRI x) v
  have hcancel (g : G) (v : V) : κ.representation g (κ.representation g⁻¹ v) = v := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hcancel' (g : G) (v : V) : κ.representation g⁻¹ (κ.representation g v) = v := by
    simpa only [inv_inv] using hcancel g⁻¹ v
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · -- The compact group parameter gives continuity on the unchanged base.
    apply continuousOn_univ.mp
    exact continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
      hR.continuousOn (by simp)
  · intro x v
    rw [happly]
    have hv (g : G) : R x g (q.linearMap x v) = q.linearMap x v := by
      change κ.representation g (P₀ (g⁻¹ • x)
        (κ.representation g⁻¹ (q.linearMap x v))) = q.linearMap x v
      rw [← hqequiv g⁻¹ x v, hfix, hqequiv g⁻¹ x v, hcancel]
    simp [hv]
  · intro x w
    have hm : P x w ∈ (q.linearMap x).range := by
      rw [happly]
      have hconv : Convex ℝ ((q.linearMap x).range : Set V) :=
        ((q.linearMap x).range.restrictScalars ℝ).convex
      apply hconv.integral_mem
        (q.linearMap x).range.closed_of_finiteDimensional _ (hRvI x w)
      filter_upwards [] with g
      obtain ⟨u, hu⟩ := hrange (g⁻¹ • x) (κ.representation g⁻¹ w)
      obtain ⟨v, hv⟩ := (σ.linearMap_bijective g⁻¹ x).surjective u
      refine ⟨v, ?_⟩
      change q.linearMap x v = κ.representation g
        (P₀ (g⁻¹ • x) (κ.representation g⁻¹ w))
      rw [hu, ← hv, hqequiv g⁻¹ x v, hcancel]
    obtain ⟨v, hv⟩ := hm
    exact ⟨v, hv.symm⟩
  · -- A left translation of Haar measure yields covariance of the same
    -- averaged operator; no invariant measure on X is assumed.
    intro g x w
    rw [happly, happly, ← (κ.representation g).integral_comp_comm (hRvI x w)]
    calc
      _ = ∫ h, R (g • x) (g * h) (κ.representation g w) ∂μ :=
        (integral_mul_left_eq_self (μ := μ)
          (fun h ↦ R (g • x) h (κ.representation g w)) g).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with h
        simp only [R, ContinuousLinearMap.comp_apply, map_mul, mul_inv_rev,
          mul_apply_eq_comp, mul_smul, inv_smul_smul, hcancel']

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_trivial

/-- An actual equivariant finite-representation injection splits off an
equivariant complementary bundle, with the original injection as its first summand. -/
theorem Hom.exists_equivariant_complement
    (σ : EquivariantStructure G E) (κ : FiniteContinuousRepresentation G)
    (q : Hom E (Bundle.Trivial X (Fin κ.dimension → ℂ)))
    (hq : ∀ x, Function.Injective (q.linearMap x))
    (heq : q.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation κ)) :
    ∃ (F : FiniteBundle X) (τ : EquivariantStructure G F.Fiber),
      ∃ e : Iso (E ×ᵇ F.Fiber) (Bundle.Trivial X (Fin κ.dimension → ℂ)),
        e.IsEquivariant (σ.sum τ) (EquivariantStructure.ofFiniteRepresentation κ) := by
  classical
  obtain ⟨P, hP, hfix, hrange, hcov⟩ := q.exists_equivariant_projection_range σ κ hq heq
  have hPP (x : X) (v : Fin κ.dimension → ℂ) : P x (P x v) = P x v := by
    obtain ⟨u, hu⟩ := hrange x v
    rw [hu, hfix]
  -- Encode precisely this averaged projection as a continuous idempotent.
  -- Its complementary image is therefore a finite bundle with the original
  -- subspace topology; no choice of a constant complement rank is required.
  let A (x : X) : Matrix (Fin κ.dimension) (Fin κ.dimension) ℂ :=
    LinearMap.toMatrix' (P x).toLinearMap
  have hA (i j : Fin κ.dimension) : Continuous (fun x ↦ A x i j) :=
    (continuous_apply i).comp (hP.clm_apply continuous_const)
  have hAA (x : X) : A x * A x = A x := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact LinearMap.ext (hPP x)
  let p : IdempotentMatrix C(X, ℂ) := {
    size := κ.dimension
    matrix i j := ⟨fun x ↦ A x i j, hA i j⟩
    mul_self := by
      ext i j x
      change (∑ k : Fin κ.dimension,
        (⟨fun y ↦ A y i k, hA i k⟩ : C(X, ℂ)) *
          (⟨fun y ↦ A y k j, hA k j⟩ : C(X, ℂ))) x = A x i j
      simpa [Matrix.mul_apply] using congrFun (congrFun (hAA x) i) j }
  have hmat (x : X) (v : Fin κ.dimension → ℂ) :
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix *ᵥ v = P x v :=
    LinearMap.toMatrix'_mulVec (P x).toLinearMap v
  have hcmat (x : X) (v : Fin κ.dimension → ℂ) :
      (p.complement.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix *ᵥ v =
        v - P x v := by
    change (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix (1 - p.matrix) *ᵥ v =
      v - P x v
    rw [map_sub, map_one, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact congrArg (v - ·) (hmat x v)
  have hmem (x : X) (v : Fin κ.dimension → ℂ) :
      v ∈ p.complement.fiber x ↔ P x v = 0 := by
    constructor
    · intro hv
      obtain ⟨w, hw⟩ : ∃ w : Fin κ.dimension → ℂ,
          (p.complement.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix *ᵥ w = v := hv
      have hw' : w - P x w = v := (hcmat x w).symm.trans hw
      rw [← hw', map_sub, hPP, sub_self]
    · intro hv
      refine ⟨v, ?_⟩
      exact (hcmat x v).trans (by rw [hv, sub_zero])
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  have hcoords : Continuous (fun z : TotalSpace Unit F.Fiber ↦ (z.proj, z.snd.val)) :=
    continuous_induced_dom
  have hcoords_inj : Function.Injective
      (fun z : TotalSpace Unit F.Fiber ↦ (z.proj, z.snd.val)) := by
    rintro ⟨x, u⟩ ⟨y, v⟩ h
    obtain ⟨rfl, huv⟩ := Prod.mk.inj h
    exact congrArg (TotalSpace.mk x) (Subtype.ext huv)
  let τ : EquivariantStructure G F.Fiber := {
    linearMap g x := {
      toFun v := ⟨κ.representation g v.val, (hmem (g • x) _).mpr (by
        rw [hcov, (hmem x v.val).mp v.property, map_zero])⟩
      map_add' u v := by apply Subtype.ext; exact map_add (κ.representation g) u.val v.val
      map_smul' c v := by apply Subtype.ext; exact map_smul (κ.representation g) c v.val }
    one_map x v := by
      apply hcoords_inj
      change ((1 : G) • x, κ.representation 1 v.val) = (x, v.val)
      simp
    mul_map g h x v := by
      apply hcoords_inj
      change ((g * h) • x, κ.representation (g * h) v.val) =
        (g • (h • x), κ.representation g (κ.representation h v.val))
      simp [map_mul, mul_smul, mul_apply_eq_comp]
    continuous_action := continuous_induced_rng.mpr
      ((continuous_fst.smul (hcoords.fst.comp continuous_snd)).prodMk
        (κ.continuous_action.comp
          (continuous_fst.prodMk (hcoords.snd.comp continuous_snd)))) }
  let d : Hom (E ×ᵇ F.Fiber) (Bundle.Trivial X (Fin κ.dimension → ℂ)) := {
    linearMap x := (q.linearMap x).coprod (p.complement.fiber x).subtype
    continuous_total := by
      apply continuous_induced_rng.mpr
      exact (continuous_proj (E := E ×ᵇ F.Fiber)).prodMk
        (((continuous_induced_rng.mp q.continuous_total).snd.comp continuous_sum_fst).add
          (hcoords.snd.comp continuous_sum_snd)) }
  have hd (x : X) : Function.Bijective (d.linearMap x) := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply (Submodule.eq_bot_iff _).mpr
      rintro ⟨v, w⟩ hvw
      have hsum : q.linearMap x v + w.val = 0 := hvw
      have hqv : q.linearMap x v = 0 := by
        have h := congrArg (P x) hsum
        simpa only [map_add, hfix, (hmem x w.val).mp w.property, add_zero, map_zero] using h
      have hv : v = 0 := hq x (hqv.trans (q.linearMap x).map_zero.symm)
      have hw : w = 0 := Subtype.ext (by simpa [hqv] using hsum)
      exact Prod.ext hv hw
    · intro z
      obtain ⟨v, hv⟩ := hrange x z
      let w : F.Fiber x := ⟨z - P x z, (hmem x _).mpr (by
        rw [map_sub, hPP, sub_self])⟩
      refine ⟨(v, w), ?_⟩
      change q.linearMap x v + (z - P x z) = z
      rw [← hv]
      abel
  refine ⟨F, τ, d.toIso hd, ?_⟩
  intro g x v
  change q.linearMap (g • x) (σ.linearMap g x v.1) + κ.representation g v.2.val =
    κ.representation g (q.linearMap x v.1 + v.2.val)
  have h := heq g x v.1
  change q.linearMap (g • x) (σ.linearMap g x v.1) =
    κ.representation g (q.linearMap x v.1) at h
  rw [h, map_add]

end AtiyahSinger.ComplexBundle
