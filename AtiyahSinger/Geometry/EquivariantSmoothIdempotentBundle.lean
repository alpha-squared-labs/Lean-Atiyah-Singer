/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.SmoothIdempotentBundle
public import AtiyahSinger.Topology.EquivariantFiniteComplement
public import Mathlib.Geometry.Manifold.Algebra.SMul

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Smooth equivariant image-bundle atlases

Public module ID: M1207.

The explicit image-bundle atlas of a smooth idempotent admits a smooth
restricted action whenever the specified ambient finite representation is
jointly smooth. The local forward and reverse frames use the canonical
idempotent intertwiner. This strengthens the ordinary image-atlas existence
statement by retaining the ambient-frame information needed for equivariance.
-/

@[expose] public noncomputable section

universe u

namespace AtiyahSinger.IdempotentMatrix

open Bundle
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (p : IdempotentMatrix C(M, ℂ))

attribute [local instance] fiberTotalSpaceTopology

open Classical in
/-- The explicit smooth image atlas makes a specified smooth ambient action
smooth on the original image fibers, also when their ranks vary. -/
theorem exists_smoothAtlas_of_ambient_action
    (hp : ∀ i j, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x : M ↦ p.matrix i j x))
    (ρ : ContRepresentation ℂ G (Fin p.size → ℂ))
    (hρ : ContMDiff (IG.prod 𝓘(ℝ, Fin p.size → ℂ)) 𝓘(ℝ, Fin p.size → ℂ) ∞
      (fun z : G × (Fin p.size → ℂ) ↦ ρ z.1 z.2))
    (σ : ComplexBundle.EquivariantStructure G (fun x ↦ p.fiber x))
    (hσ : ∀ (g : G) (x : M) (v : p.fiber x), (σ.linearMap g x v).val = ρ g v.val) :
    ∃ B : SmoothComplexBundleAtlas.{u} (n := n) (fun x ↦ p.fiber x),
      ∀ (i j : B.Index) (k : Fin (B.rank i)),
        ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          𝓘(ℝ, Fin (B.rank j) → ℂ) ∞
          (fun z : G × M ↦ if hx : z.2 ∈ (B.chart i).baseSet then
            (B.chart j ⟨z.1 • z.2,
              σ.linearMap z.1 z.2 ((B.frameLinearEquiv i z.2 hx).symm
                (Pi.single k 1))⟩).2 else 0)
          {z : G × M | z.2 ∈ (B.chart i).baseSet ∧ z.1 • z.2 ∈ (B.chart j).baseSet} := by
  classical
  let matrix : (Fin p.size → Fin p.size → ℂ) →L[ℝ]
      Matrix (Fin p.size) (Fin p.size) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.id :
      (Fin p.size → Fin p.size → ℂ) →ₗ[ℝ] Matrix (Fin p.size) (Fin p.size) ℂ)
  let entry (i j : Fin p.size) : Matrix (Fin p.size) (Fin p.size) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun Q ↦ Q i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  let A (x : M) : Matrix (Fin p.size) (Fin p.size) ℂ :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  have hA : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Matrix (Fin p.size) (Fin p.size) ℂ) ∞ A := by
    exact matrix.contMDiff.comp
      (contMDiff_pi_space.mpr fun i ↦ contMDiff_pi_space.mpr fun j ↦ hp i j)
  have hAA (x : M) : A x * A x = A x :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  -- Near each chosen base point, the explicit intertwiner is a smooth invertible matrix.
  let T (x₀ x : M) := idempotentIntertwiner (A x) (A x₀)
  have hT (x₀ : M) : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Matrix (Fin p.size) (Fin p.size) ℂ) ∞ (T x₀) := by
    have hpol : ContDiff ℝ ∞ (fun Q : Matrix (Fin p.size) (Fin p.size) ℂ ↦
        1 - Q - A x₀ + 2 * Q * A x₀) :=
      ((contDiff_const.sub contDiff_id).sub contDiff_const).add
        ((contDiff_const.mul contDiff_id).mul contDiff_const)
    exact hpol.contMDiff.comp hA
  have hT₀ (x₀ : M) : T x₀ x₀ = 1 := by
    dsimp only [T, idempotentIntertwiner]
    noncomm_ring [hAA x₀]
  have hcomm (x₀ x : M) : T x₀ x * A x₀ = A x * T x₀ x :=
    idempotentIntertwiner_mul (A x) (A x₀) (hAA x) (hAA x₀)
  let U (x₀ : M) : Set M := {x | ‖T x₀ x - 1‖ < 1}
  have hopen (x₀ : M) : IsOpen (U x₀) :=
    isOpen_lt (((hT x₀).continuous.sub continuous_const).norm) continuous_const
  have hmem (x₀ : M) : x₀ ∈ U x₀ := by
    change ‖T x₀ x₀ - 1‖ < 1
    rw [hT₀, sub_self, norm_zero]
    exact zero_lt_one
  have hunit (x₀ x : M) (hx : x ∈ U x₀) : IsUnit (T x₀ x) :=
    isUnit_idempotentIntertwiner_of_norm_lt (A x) (A x₀) hx
  let L (x₀ x : M) := Ring.inverse (T x₀ x)
  have hLT (x₀ x : M) (hx : x ∈ U x₀) : L x₀ x * T x₀ x = 1 :=
    Ring.inverse_mul_cancel (T x₀ x) (hunit x₀ x hx)
  have hTL (x₀ x : M) (hx : x ∈ U x₀) : T x₀ x * L x₀ x = 1 :=
    Ring.mul_inverse_cancel (T x₀ x) (hunit x₀ x hx)
  have hL (x₀ : M) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Matrix (Fin p.size) (Fin p.size) ℂ) ∞ (L x₀) (U x₀) := by
    intro x hx
    obtain ⟨v, hv⟩ := hunit x₀ x hx
    have hi := contDiffAt_ringInverse ℝ (n := ∞) v
    rw [hv] at hi
    exact hi.contMDiffAt.comp_contMDiffWithinAt x ((hT x₀ x).contMDiffWithinAt)
  -- Both directions act on the original range subtypes, not abstract replacement fibers.
  let back (x₀ x : M) : (Fin p.size → ℂ) →ₗ[ℂ] p.fiber x₀ :=
    (A x₀).mulVecLin.rangeRestrict.comp (L x₀ x).mulVecLin
  let front (x₀ x : M) : p.fiber x₀ →ₗ[ℂ] p.fiber x :=
    (A x).mulVecLin.rangeRestrict.comp
      ((T x₀ x).mulVecLin.comp (p.fiber x₀).subtype)
  have hfix (x : M) (v : p.fiber x) : A x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ : ∃ w : Fin p.size → ℂ, A x *ᵥ w = v.val := v.property
    rw [← hw, Matrix.mulVec_mulVec, hAA]
  have hfrontback (x₀ x : M) (hx : x ∈ U x₀) (v : p.fiber x) :
      front x₀ x (back x₀ x v.val) = v := by
    apply Subtype.ext
    change A x *ᵥ (T x₀ x *ᵥ (A x₀ *ᵥ (L x₀ x *ᵥ v.val))) = v.val
    have hid : A x * T x₀ x * A x₀ * L x₀ x = A x := by
      calc
        _ = A x * (T x₀ x * A x₀) * L x₀ x := by noncomm_ring
        _ = A x * (A x * T x₀ x) * L x₀ x := by rw [hcomm]
        _ = (A x * A x) * (T x₀ x * L x₀ x) := by noncomm_ring
        _ = A x := by rw [hAA, hTL x₀ x hx, mul_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hid]
    exact hfix x v
  have hbackfront (x₀ x : M) (hx : x ∈ U x₀) (v : p.fiber x₀) :
      back x₀ x (front x₀ x v).val = v := by
    apply Subtype.ext
    change A x₀ *ᵥ (L x₀ x *ᵥ (A x *ᵥ (T x₀ x *ᵥ v.val))) = v.val
    have hid : A x₀ * L x₀ x * A x * T x₀ x = A x₀ := by
      calc
        _ = (A x₀ * L x₀ x) * (A x * T x₀ x) := by noncomm_ring
        _ = (A x₀ * L x₀ x) * (T x₀ x * A x₀) := by rw [← hcomm]
        _ = A x₀ * (L x₀ x * T x₀ x) * A x₀ := by noncomm_ring
        _ = A x₀ := by rw [hLT x₀ x hx, mul_one, hAA]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hid]
    exact hfix x₀ v
  have hpair : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
      (z.proj, z.snd.val)) := continuous_induced_dom
  have hbase := continuous_fst.comp hpair
  have hvec := continuous_snd.comp hpair
  let e (x₀ : M) : Trivialization (p.fiber x₀) (π Unit (fun x ↦ p.fiber x)) :=
    { toFun := fun z ↦ (z.proj, back x₀ z.proj z.snd.val)
      invFun := fun z ↦ ⟨z.1, front x₀ z.1 z.2⟩
      source := π Unit (fun x ↦ p.fiber x) ⁻¹' U x₀
      target := U x₀ ×ˢ Set.univ
      baseSet := U x₀
      open_source := (hopen x₀).preimage hbase
      open_target := (hopen x₀).prod isOpen_univ
      open_baseSet := hopen x₀
      map_source' := fun _ hx ↦ ⟨hx, Set.mem_univ _⟩
      map_target' := fun _ hx ↦ hx.1
      left_inv' := fun z hz ↦
        TotalSpace.ext rfl (heq_of_eq (hfrontback x₀ z.proj hz z.snd))
      right_inv' := fun z hz ↦ Prod.ext rfl (hbackfront x₀ z.1 hz.1 z.2)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl
      continuousOn_toFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        let base : (π Unit (fun x ↦ p.fiber x) ⁻¹' U x₀) → U x₀ :=
          fun z ↦ ⟨z.val.proj, z.property⟩
        have hbaseU : Continuous base := (hbase.comp continuous_subtype_val).subtype_mk _
        have hLc : Continuous (fun x : U x₀ ↦ L x₀ x.val) :=
          (continuousOn_iff_continuous_domRestrict.mp (hL x₀).continuousOn)
        apply (hbase.comp continuous_subtype_val).prodMk
        apply Continuous.subtype_mk
        exact continuous_const.matrix_mulVec
          ((hLc.comp hbaseU).matrix_mulVec (hvec.comp continuous_subtype_val))
      continuousOn_invFun := by
        apply Continuous.continuousOn
        apply continuous_induced_rng.mpr
        exact continuous_fst.prodMk
          ((hA.continuous.comp continuous_fst).matrix_mulVec
            (((hT x₀).continuous.comp continuous_fst).matrix_mulVec
              (continuous_subtype_val.comp continuous_snd))) }
  let c (x₀ : M) : p.fiber x₀ ≃L[ℂ]
      (Fin (Module.finrank ℂ (p.fiber x₀)) → ℂ) :=
    (Module.finBasis ℂ (p.fiber x₀)).equivFun.toContinuousLinearEquiv
  -- Fixed finite coordinates and smooth matrix inversion give every overlap column.
  let B : SmoothComplexBundleAtlas.{u} (n := n) (fun x ↦ p.fiber x) := by
    refine { Index := M
             rank := fun x₀ ↦ Module.finrank ℂ (p.fiber x₀)
             chart := fun x₀ ↦ (e x₀).transFiberHomeomorph (c x₀).toHomeomorph
             covers := fun x ↦ ⟨x, hmem x⟩
             linear := ?_
             contMDiffOn_coordChange := ?_ }
    · intro x₀ x _
      constructor
      · intro v w
        change c x₀ (back x₀ x (v.val + w.val)) =
          c x₀ (back x₀ x v.val) + c x₀ (back x₀ x w.val)
        rw [map_add, map_add]
      · intro a v
        change c x₀ (back x₀ x (a • v.val)) = a • c x₀ (back x₀ x v.val)
        rw [map_smul, map_smul]
    · intro i j a
      let v : Fin p.size → ℂ := ((c i).symm (Pi.single a 1)).val
      let R : (Fin p.size → ℂ) →L[ℝ] (Fin (Module.finrank ℂ (p.fiber j)) → ℂ) :=
        LinearMap.toContinuousLinearMap
          (((c j).toLinearMap.comp (A j).mulVecLin.rangeRestrict).restrictScalars ℝ)
      have hmul {s : Set M} (P : M → Matrix (Fin p.size) (Fin p.size) ℂ)
          (w : M → Fin p.size → ℂ)
          (hP : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, Matrix (Fin p.size) (Fin p.size) ℂ) ∞ P s)
          (hw : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, Fin p.size → ℂ) ∞ w s) :
          ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin p.size → ℂ) ∞
            (fun x ↦ P x *ᵥ w x) s := by
        apply contMDiffOn_pi_space.mpr
        intro k
        change ContMDiffOn _ _ ∞ (fun x ↦ ∑ l, P x k l * w x l) s
        apply contMDiffOn_finsetSum
        intro l _
        have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) :=
          contDiff_fst.mul contDiff_snd
        exact hm.contMDiff.comp_contMDiffOn
          (((entry k l).contMDiff.comp_contMDiffOn hP).prodMk_space
            (contMDiffOn_pi_space.mp hw l))
      have hv := hmul (s := U i ∩ U j) (T i) (fun _ ↦ v)
        (hT i).contMDiffOn contMDiffOn_const
      have hAv := hmul A _ hA.contMDiffOn hv
      have hLv := hmul (L j) _ ((hL j).mono Set.inter_subset_right) hAv
      apply (R.contMDiff.comp_contMDiffOn hLv).congr
      intro x _
      rfl
  refine ⟨B, ?_⟩
  intro i j k
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let s : Set (G × M) := {z | z.2 ∈ U i ∧ z.1 • z.2 ∈ U j}
  let v : Fin p.size → ℂ := ((c i).symm (Pi.single k 1)).val
  let R : (Fin p.size → ℂ) →L[ℝ] (Fin (Module.finrank ℂ (p.fiber j)) → ℂ) :=
    LinearMap.toContinuousLinearMap
      (((c j).toLinearMap.comp (A j).mulVecLin.rangeRestrict).restrictScalars ℝ)
  -- Moving action columns are finite products of smooth ambient matrices,
  -- the given ambient action, and the local inverse frame at the moved point.
  have hmul (P : G × M → Matrix (Fin p.size) (Fin p.size) ℂ)
      (w : G × M → Fin p.size → ℂ)
      (hP : ContMDiffOn (IG.prod I) 𝓘(ℝ, Matrix (Fin p.size) (Fin p.size) ℂ) ∞ P s)
      (hw : ContMDiffOn (IG.prod I) 𝓘(ℝ, Fin p.size → ℂ) ∞ w s) :
      ContMDiffOn (IG.prod I) 𝓘(ℝ, Fin p.size → ℂ) ∞
        (fun z ↦ P z *ᵥ w z) s := by
    apply contMDiffOn_pi_space.mpr
    intro a
    change ContMDiffOn _ _ ∞ (fun z ↦ ∑ b, P z a b * w z b) s
    apply contMDiffOn_finsetSum
    intro b _
    have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) :=
      contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp_contMDiffOn
      (((entry a b).contMDiff.comp_contMDiffOn hP).prodMk_space
        (contMDiffOn_pi_space.mp hw b))
  have hv := hmul (fun z ↦ T i z.2) (fun _ ↦ v)
    ((hT i).comp contMDiff_snd).contMDiffOn contMDiffOn_const
  have hAv := hmul (fun z ↦ A z.2) _
    (hA.comp contMDiff_snd).contMDiffOn hv
  have hact := hρ.comp_contMDiffOn (contMDiffOn_fst.prodMk hAv)
  have hLact := hmul (fun z ↦ L j (z.1 • z.2)) _
    ((hL j).comp (contMDiffOn_fst.smul contMDiffOn_snd) (fun _ hz ↦ hz.2)) hact
  apply (R.contMDiff.comp_contMDiffOn hLact).congr
  intro z hz
  have hframe : (B.frameLinearEquiv i z.2 hz.1).symm (Pi.single k 1) =
      front i z.2 ((c i).symm (Pi.single k 1)) := by
    apply (B.frameLinearEquiv i z.2 hz.1).injective
    rw [LinearEquiv.apply_symm_apply]
    change Pi.single k 1 = c i (back i z.2 (front i z.2 ((c i).symm _)).val)
    rw [hbackfront i z.2 hz.1, (c i).apply_symm_apply]
  have hz' : z.2 ∈ (B.chart i).baseSet := hz.1
  rw [dite_eq_left hz', hframe]
  change c j (back j (z.1 • z.2)
      (σ.linearMap z.1 z.2 (front i z.2 ((c i).symm _))).val) =
    R (L j (z.1 • z.2) *ᵥ ρ z.1 (A z.2 *ᵥ (T i z.2 *ᵥ v)))
  rw [hσ]
  rfl

end AtiyahSinger.IdempotentMatrix
