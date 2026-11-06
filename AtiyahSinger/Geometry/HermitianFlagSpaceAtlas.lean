/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianFlagFrameSlice
public import AtiyahSinger.Geometry.HermitianFlagMatrixFrames
public import AtiyahSinger.Geometry.HermitianFlagOrthonormalBasis
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Data.Finset.Prod
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# The embedded atlas on the original Hermitian projection flags

Public module ID: M1269.

The actual unitary frame slice supplies local parameters for projection flags.
The original projector subtype topology and the real dimension r(r-1) are kept.
The reference frame is chosen separately at each flag; no global phase section
is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise Topology

local notation "Pair" r:arg => {p : Fin r × Fin r // Prod.fst p < Prod.snd p}

/-- The strict triangular complex parameters have the original real flag model dimension. -/
def hermitianFlagParameterEquiv (r : ℕ) :
    (Pair r → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (r * (r - 1))) := by
  classical
  have hcard : Fintype.card (Pair r) = r.choose 2 := by
    rw [Fintype.card_subtype]
    simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r))))
  have hdim : Module.finrank ℝ (Pair r → ℂ) = r * (r - 1) := by
    rw [Module.finrank_pi_fintype]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hcard, Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
  let e : (Pair r → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (r * (r - 1))) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  exact e.toContinuousLinearEquiv

/-- Every original flag has a local chart with smooth ambient coordinates and smooth inverse.
The ambient formula supplies the differential left inverse for the subtype embedding. -/
theorem exists_hermitianFlagLocalChart (r : ℕ)
    (P : HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore) :
    ∃ c : OpenPartialHomeomorph
        (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
        (EuclideanSpace ℝ (Fin (r * (r - 1)))),
      P ∈ c.source ∧
        ∃ f : (Fin r → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) →
            EuclideanSpace ℝ (Fin (r * (r - 1))),
          (∀ Q, c Q = f Q.val) ∧ (∀ Q ∈ c.source, ContDiffAt ℝ ∞ f Q.val) ∧
            ContDiffOn ℝ ∞ (fun z ↦ (c.symm z).val) c.target := by
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let F := HermitianFlagSpace r V InnerProductSpace.toCore
  let L := Fin r → V →L[ℂ] V
  let Mat := Matrix (Fin r) (Fin r) ℂ
  let Z := EuclideanSpace ℝ (Fin (r * (r - 1)))
  let C := ((Fin r → ℂ) × (Pair r → ℂ)) × (Pair r → ℂ)
  obtain ⟨b, hb⟩ := P.exists_orthonormalBasis (by simp)
  obtain ⟨e, he1, he0, heSmooth, heInv, hePos, heGram, heLower⟩ :=
    exists_hermitianFlagFrameSlice r
  let a := hermitianFlagParameterEquiv r
  let lower : Mat → Pair r → ℂ := fun A p ↦ A p.val.2 p.val.1
  let ψ : Z → C := fun z ↦ (0, a.symm z)
  let f : L → Z := fun Q ↦ a (lower (hermitianFlagFrameMatrix b Q))
  let U : Set L := {Q | ∀ i : Fin r, Q i (b i) ≠ 0}
  let S : Set F := {Q | Q.val ∈ U ∧ hermitianFlagFrameMatrix b Q.val ∈ e.source}
  let W : Set Z := ψ ⁻¹' e.target
  have hlower : ContDiff ℝ ∞ lower := by dsimp [lower]; fun_prop
  have hψ : ContDiff ℝ ∞ ψ := contDiff_const.prodMk a.symm.contDiff
  have hf (Q : L) (hQ : Q ∈ U) : ContDiffAt ℝ ∞ f Q :=
    a.contDiff.contDiffAt.comp Q
      (hlower.contDiffAt.comp Q (hermitianFlagFrameMatrix_contDiffAt b Q hQ))
  -- On the original flag locus, the constrained coordinates vanish identically.
  have hcoords (Q : F) (hQ : Q.val ∈ U) :
      e (hermitianFlagFrameMatrix b Q.val) = ψ (f Q.val) := by
    obtain ⟨hgram, him, _, _⟩ := hermitianFlagFrameMatrix_properties b Q hQ
    apply Prod.ext
    · exact (heGram _).mpr ⟨hgram, him⟩
    · simpa only [ψ, f, a.symm_apply_apply] using heLower (hermitianFlagFrameMatrix b Q.val)
  -- The inverse Gram slice gives an actual flag, with precisely the same normalized frame.
  have hflag (z : Z) (hz : z ∈ W) :
      ∃ Q : F, Q.val = hermitianFlagMatrixProjections b (e.symm (ψ z)) ∧
        Q.val ∈ U ∧ hermitianFlagFrameMatrix b Q.val = e.symm (ψ z) := by
    have hzero : (e (e.symm (ψ z))).1 = 0 := by rw [e.right_inv hz]
    obtain ⟨hgram, him⟩ := (heGram _).mp hzero
    exact hermitianFlagMatrixProjections_flag b _ hgram him
      (hePos _ (e.map_target hz))
  let q : Z → F := fun z ↦ if hz : z ∈ W then (hflag z hz).choose else P
  have hq (z : Z) (hz : z ∈ W) :
      (q z).val = hermitianFlagMatrixProjections b (e.symm (ψ z)) ∧
        (q z).val ∈ U ∧ hermitianFlagFrameMatrix b (q z).val = e.symm (ψ z) := by
    simpa only [q, dite_eq_left hz] using (hflag z hz).choose_spec
  have hqS (z : Z) (hz : z ∈ W) : q z ∈ S := by
    refine ⟨(hq z hz).2.1, ?_⟩
    rw [(hq z hz).2.2]
    exact e.map_target hz
  have hmap (Q : F) (hQ : Q ∈ S) : f Q.val ∈ W := by
    change ψ (f Q.val) ∈ e.target
    rw [← hcoords Q hQ.1]
    exact e.map_source hQ.2
  have hleft (Q : F) (hQ : Q ∈ S) : q (f Q.val) = Q := by
    apply Subtype.ext
    rw [(hq _ (hmap Q hQ)).1, ← hcoords Q hQ.1, e.left_inv hQ.2]
    exact (hermitianFlagFrameMatrix_properties b Q hQ.1).2.2.2
  have hright (z : Z) (hz : z ∈ W) : f (q z).val = z := by
    have hc := congrArg Prod.snd (e.right_inv hz)
    rw [heLower] at hc
    change lower (e.symm (ψ z)) = a.symm z at hc
    change a (lower (hermitianFlagFrameMatrix b (q z).val)) = z
    rw [(hq z hz).2.2, hc, a.apply_symm_apply]
  -- Both open domains and both continuity certificates use the original subtype topology.
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun
      ((continuous_apply i).clm_apply continuous_const) continuous_const
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro Q hQ
    have hc : ContinuousAt (fun Q : F ↦ hermitianFlagFrameMatrix b Q.val) Q :=
      (hermitianFlagFrameMatrix_contDiffAt b Q.val hQ.1).continuousAt.comp
        continuous_subtype_val.continuousAt
    exact Filter.inter_mem ((hU.preimage continuous_subtype_val).mem_nhds hQ.1)
      (hc.preimage_mem_nhds (e.open_source.mem_nhds hQ.2))
  have hW : IsOpen W := e.open_target.preimage hψ.continuous
  have hg : ContDiffOn ℝ ∞
      (fun z : Z ↦ hermitianFlagMatrixProjections b (e.symm (ψ z))) W :=
    (hermitianFlagMatrixProjections_contDiff b).comp_contDiffOn
      (heInv.comp hψ.contDiffOn (fun _ hz ↦ hz))
  have hqCont : ContinuousOn q W := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact hg.continuousOn.congr (fun z hz ↦ (hq z hz).1)
  let c : OpenPartialHomeomorph F Z :=
    { toFun := fun Q ↦ f Q.val
      invFun := q
      source := S
      target := W
      map_source' := hmap
      map_target' := hqS
      left_inv' := hleft
      right_inv' := hright
      open_source := hS
      open_target := hW
      continuousOn_toFun := fun Q hQ ↦
        ((hf Q.val hQ.1).continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt
      continuousOn_invFun := hqCont }
  refine ⟨c, ?_, f, fun _ ↦ rfl, fun Q hQ ↦ hf Q.val hQ.1, ?_⟩
  · have hfixed (i : Fin r) : P.val i (b i) = b i := by
      rw [hb, b.inner_eq_one, one_smul]
    have hn (i : Fin r) : P.val i (b i) ≠ 0 := by
      rw [hfixed]
      exact b.toBasis.ne_zero i
    refine ⟨hn, ?_⟩
    have hp : hermitianFlagFrameMatrix b P.val = (1 : Mat) := by
      ext k i
      change hermitianFlagFrameMatrix b P.val k i = if k = i then 1 else 0
      simp [hermitianFlagFrameMatrix, hermitianFlagLocalFrame, hfixed, b.orthonormal.1]
    rw [hp]
    exact he1
  · apply hg.congr
    intro z hz
    exact (hq z hz).1

end AtiyahSinger.ComplexBundle
