/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBottConjugation
public import AtiyahSinger.Topology.ExteriorBottComparison

/-!
# Conjugation of the actual exterior Bott generator of the real sign line

Public module ID: M1981.

The vacuum and the unique exterior vector identify the original parity fibers
with the trivial and determinant lines. Conjugation of the boundary is compared
with the inverse determinant tensor triple outside one invariant compact ball.
The positive radial factor extends over the ball, giving a genuine global
equivariant bundle square. This generator calculation does not use the
surjectivity statement for the entire equivariant Bott group.

Source: Atiyah--Singer I, Lemma (2.8), with the project's original SG exterior
carrier and its specified real orthogonal action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  tensorTopology isFiniteRank_tensor trivialTopology isFiniteRank_trivial isFiniteRank_pullback

set_option maxHeartbeats 1200000 in

/-- Conjugation of the original sign-line Bott generator is its negative determinant twist. -/
theorem orthogonalLineConjugationPullback_bott :
    orthogonalComplexificationConjugationPullback 1
        (equivariantExteriorBottClass (orthogonalComplexification_unitary 1)) =
      -(finiteRepresentationClass (orthogonalDeterminantRepresentation 1) •
        equivariantExteriorBottClass (orthogonalComplexification_unitary 1)) := by
  classical
  let G := Matrix.orthogonalGroup (Fin 1) ℝ
  let V := EuclideanSpace ℂ (Fin 1)
  let P (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let := compactSpace_orthogonalGroup 1
  let := exteriorAlgebra_finiteDimensional (V := V)
  let (i : ZMod 2) := modelTopology (P i) (Bundle.Trivial V (P i))
  let (i : ZMod 2) := isFiniteRank_model (P i) (Bundle.Trivial V (P i))
  -- The actual parity basis is the vacuum and the unique original unit vector.
  let I₀ := {s : Finset (Fin 1) // (s.card : ZMod 2) = 0}
  let I₁ := {s : Finset (Fin 1) // (s.card : ZMod 2) = 1}
  let : Unique I₀ := { default := ⟨∅, by simp⟩, uniq := by decide }
  let : Unique I₁ := { default := ⟨{0}, by simp⟩, uniq := by decide }
  let b₀ : Module.Basis (Fin 1) ℂ (P 0) :=
    (complexSpinorParityBasis 1 0).reindex (Equiv.ofUnique I₀ (Fin 1))
  let b₁ : Module.Basis (Fin 1) ℂ (P 1) :=
    (complexSpinorParityBasis 1 1).reindex (Equiv.ofUnique I₁ (Fin 1))
  let d₀ := b₀.equivFun
  let d₁ := b₁.equivFun
  let v₀ : V := EuclideanSpace.single 0 1
  have hparity (i : ZMod 2) (t : {s : Finset (Fin 1) // (s.card : ZMod 2) = i}) :
      (complexSpinorParityBasis 1 i t : ExteriorAlgebra ℂ V) = complexSpinorBasis 1 t.val := by
    simp [complexSpinorParityBasis]
  have hb₀ : (b₀ 0 : ExteriorAlgebra ℂ V) = 1 := by
    have hi : (Equiv.ofUnique I₀ (Fin 1)).symm 0 = ⟨∅, by simp⟩ := Subsingleton.elim _ _
    simp only [b₀, Module.Basis.reindex_apply, hi]
    rw [hparity, complexSpinorBasis, ExteriorAlgebra.basis_apply]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  have hb₁ : (b₁ 0 : ExteriorAlgebra ℂ V) = ExteriorAlgebra.ι ℂ v₀ := by
    have hi : (Equiv.ofUnique I₁ (Fin 1)).symm 0 = ⟨{0}, by simp⟩ := Subsingleton.elim _ _
    simp only [b₁, Module.Basis.reindex_apply, hi]
    rw [hparity, complexSpinorBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton 0)]
    simp only [OrthonormalBasis.coe_toBasis, Fin.isValue, ExteriorAlgebra.ιMulti_succ_apply,
      Function.comp_apply, EuclideanSpace.basisFun_apply, ExteriorAlgebra.ιMulti_zero_apply,
      mul_one, ExteriorAlgebra.ι_inj]
    exact congrArg (fun k : Fin 1 ↦ EuclideanSpace.single k (1 : ℂ))
      (Subsingleton.elim _ _)
  have hd₀ (a : Fin 1 → ℂ) : (d₀.symm a : ExteriorAlgebra ℂ V) = a 0 • 1 := by
    simp [d₀, Module.Basis.equivFun_symm_apply, hb₀]
  have hd₁ (a : Fin 1 → ℂ) :
      (d₁.symm a : ExteriorAlgebra ℂ V) = a 0 • ExteriorAlgebra.ι ℂ v₀ := by
    simp [d₁, Module.Basis.equivFun_symm_apply, hb₁]
  have hvector (z : V) : z = z 0 • v₀ := by
    ext k
    fin_cases k
    change z 0 = z 0 * 1
    exact (mul_one _).symm
  have hsymbol (z : V) (a : Fin 1 → ℂ) :
      cliffordSymbolParity z 0 (d₀.symm a) = d₁.symm (z 0 • a) := by
    apply Subtype.ext
    change cliffordSymbol z (d₀.symm a : ExteriorAlgebra ℂ V) = _
    rw [hd₀, hd₁, map_smul]
    have hvacuum : cliffordSymbol z 1 = ExteriorAlgebra.ι ℂ z := by
      simp [cliffordSymbol, exteriorMultiplication, contraction]
    rw [hvacuum]
    have hι := congrArg (ExteriorAlgebra.ι ℂ) (hvector z)
    rw [map_smul] at hι
    rw [hι]
    simp [smul_smul, mul_comm]
  -- The even action is trivial and the odd action is the original determinant character.
  have haction (A : G) (z : V) : A • z = (A.val.det : ℂ) • z := by
    ext k
    fin_cases k
    change (∑ j : Fin 1, (A.val 0 j : ℂ) * z j) = (A.val.det : ℂ) * z 0
    simp only [Fin.sum_univ_one, Matrix.det_fin_one]
  have hact₀ (A : G) (a : Fin 1 → ℂ) :
      exteriorParityAction A 0 (d₀.symm a) = d₀.symm a := by
    apply Subtype.ext
    change ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V A)
      (d₀.symm a : ExteriorAlgebra ℂ V) = _
    rw [hd₀, map_smul, map_one]
  have hact₁ (A : G) (a : Fin 1 → ℂ) :
      exteriorParityAction A 1 (d₁.symm a) = d₁.symm ((A.val.det : ℂ) • a) := by
    apply Subtype.ext
    change ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V A)
      (d₁.symm a : ExteriorAlgebra ℂ V) = _
    rw [hd₁, hd₁, map_smul, ExteriorAlgebra.map_apply_ι]
    change a 0 • ExteriorAlgebra.ι ℂ (A • v₀) = _
    rw [haction, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]
  have hdet (A : G) : (A.val.det : ℂ) * (A.val.det : ℂ) = 1 := by
    have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff' (Fin 1) ℝ).mp A.property)
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact_mod_cast h
  have hnorm (A : G) (z : V) : ‖A • z‖ = ‖z‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      orthogonalComplexification_unitary]
  -- Extend the radial square positively across the invariant unit ball.
  let α : C(V, ℂ) := ⟨fun z ↦ (max 1 (‖z‖ ^ 2) : ℝ),
    Complex.continuous_ofReal.comp (continuous_const.max (continuous_norm.pow 2))⟩
  have hα (z : V) : α z ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hαeq (A : G) (z : V) : α (A • z) = α z := by
    change ((max 1 (‖A • z‖ ^ 2) : ℝ) : ℂ) = ((max 1 (‖z‖ ^ 2) : ℝ) : ℂ)
    rw [hnorm]
  let f := orthogonalComplexificationConjugation 1
  let a := equivariantExteriorBottTriple (orthogonalComplexification_unitary 1)
  let ρ := orthogonalDeterminantRepresentation 1
  let b := a.pullback f (orthogonalComplexificationConjugation_equivariant 1)
    (orthogonalComplexificationConjugation_isProperMap 1)
  let c := a.tensorRepresentation ρ
  let J (i : ZMod 2) := FiniteBundle.ofFamily (Bundle.Trivial V (P i))
  -- The original tensor topology makes insertion of a fixed scalar coefficient continuous.
  have hpure (i : ZMod 2) : Continuous (fun z : TotalSpace Unit (J i).Fiber ↦
      (⟨z.proj, (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] z.snd⟩ :
        TotalSpace Unit ((FiniteBundle.trivial V 1).tensor (J i)).Fiber)) := by
    let D := TotalSpace Unit (fun x : V ↦
      (Fin 1 → Fin 1 → ℂ) × (Fin 1 → (J i).Fiber x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun k ↦ (⟨z.proj, z.snd.1 k⟩ : TotalSpace Unit (FiniteBundle.trivial V 1).Fiber)),
        (fun k ↦ (⟨z.proj, z.snd.2 k⟩ : TotalSpace Unit (J i).Fiber)))) inferInstance
    have hg : Continuous (fun z : D ↦
        (⟨z.proj, ∑ k : Fin 1, z.snd.1 k ⊗ₜ[ℂ] z.snd.2 k⟩ :
          TotalSpace Unit ((FiniteBundle.trivial V 1).tensor (J i)).Fiber)) :=
      continuous_iSup_rng (i := 1) continuous_coinduced_rng
    let q (z : TotalSpace Unit (J i).Fiber) : D :=
      ⟨z.proj, fun _ ↦ 1, fun _ ↦ z.snd⟩
    have hq : Continuous q := by
      apply continuous_induced_rng.mpr
      refine (continuous_proj (E := (J i).Fiber)).prodMk
        ((continuous_pi ?_).prodMk (continuous_pi (fun _ ↦ continuous_id)))
      intro _
      exact continuous_induced_rng.mpr
        ((continuous_proj (E := (J i).Fiber)).prodMk continuous_const)
    apply (hg.comp hq).congr
    intro z
    simp only [Function.comp_apply, q, Fin.sum_univ_one]
  let hmodel (i : ZMod 2) : TotalSpace Unit (J i).Fiber ≃ₜ V × P i :=
    (unitTotalHomeomorph (P i) (Bundle.Trivial V (P i))).trans
      (Bundle.Trivial.homeomorphProd V (P i))
  let tensorUnit (i : ZMod 2) : P i ≃ₗ[ℂ] ((Fin 1 → ℂ) ⊗[ℂ] P i) :=
    ((TensorProduct.congr (LinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))
      (LinearEquiv.refl ℂ (P i))).trans (TensorProduct.lid ℂ (P i))).symm
  have hunit (i : ZMod 2) (v : P i) : tensorUnit i v = (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v := by
    rfl
  let makeIso (i j : ZMod 2) (d : P i ≃ₗ[ℂ] P j) (β : C(V, ℂ))
      (hβ : ∀ z, β z ≠ 0) :
      Iso ((J i).pullback f).Fiber ((FiniteBundle.trivial V 1).tensor (J j)).Fiber := by
    let l (z : V) := (d.trans (LinearEquiv.smulOfNeZero ℂ (P j) (β z) (hβ z))).trans
      (tensorUnit j)
    let L : Hom ((J i).pullback f).Fiber
        ((FiniteBundle.trivial V 1).tensor (J j)).Fiber :=
      { linearMap z := (l z).toLinearMap
        continuous_total := by
          have hs := (hmodel i).continuous.comp (Pullback.continuous_lift Unit (J i).Fiber f)
          have hb := Pullback.continuous_proj Unit (J i).Fiber f
          have hm := (hmodel j).symm.continuous.comp
            (hb.prodMk ((β.continuous.comp hb).smul
              (d.continuous_of_finiteDimensional.comp hs.snd)))
          apply ((hpure j).comp hm).congr
          intro z
          rfl }
    exact L.toIso (fun z ↦ (l z).bijective)
  let u := makeIso 0 1 (d₀.trans d₁.symm) α hα
  let v := makeIso 1 0 (d₁.trans d₀.symm) 1 (fun _ ↦ one_ne_zero)
  have hu (z : V) (w : P 0) :
      u.linearEquiv z w = (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] (α z • d₁.symm (d₀ w)) := rfl
  have hv (z : V) (w : P 1) :
      v.linearEquiv z w = (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] d₀.symm (d₁ w) := by
    change (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] ((1 : ℂ) • d₀.symm (d₁ w)) = _
    rw [one_smul]
  have hueq : u.IsEquivariant b.2.sourceAction c.inverse.2.sourceAction := by
    intro A z w
    obtain ⟨t, rfl⟩ := d₀.symm.surjective w
    change u.linearEquiv (A • z) (exteriorParityAction A 0 (d₀.symm t)) = _
    rw [hact₀, hu, LinearEquiv.apply_symm_apply]
    change _ = (c.inverse.2.sourceAction.linearMap A z) (u.linearEquiv z (d₀.symm t))
    rw [hu, LinearEquiv.apply_symm_apply]
    change (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] (α (A • z) • d₁.symm t) =
      ((A.val.det : ℂ) • (1 : Fin 1 → ℂ)) ⊗ₜ[ℂ]
        exteriorParityAction A 1 (α z • d₁.symm t)
    rw [hαeq, (exteriorParityAction A 1).map_smul, hact₁, d₁.symm.map_smul,
      TensorProduct.smul_tmul]
    rw [smul_comm (A.val.det : ℂ) (α z)]
    simp only [smul_smul, hdet, mul_one]
  have hveq : v.IsEquivariant b.2.targetAction c.inverse.2.targetAction := by
    intro A z w
    obtain ⟨t, rfl⟩ := d₁.symm.surjective w
    change v.linearEquiv (A • z) (exteriorParityAction A 1 (d₁.symm t)) = _
    rw [hact₁, hv, LinearEquiv.apply_symm_apply]
    change _ = (c.inverse.2.targetAction.linearMap A z) (v.linearEquiv z (d₁.symm t))
    rw [hv, LinearEquiv.apply_symm_apply]
    change (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] d₀.symm ((A.val.det : ℂ) • t) =
      ((A.val.det : ℂ) • (1 : Fin 1 → ℂ)) ⊗ₜ[ℂ]
        exteriorParityAction A 0 (d₀.symm t)
    rw [hact₀, d₀.symm.map_smul, TensorProduct.smul_tmul]
  let K : Set V := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall _ _
  have hInv (A : G) (z : V) : A • z ∈ K ↔ z ∈ K := by
    simp only [K, Metric.mem_closedBall, dist_zero_right, hnorm]
  have hbK : b.1.datum.control ⊆ K := by
    intro z hz
    change f z ∈ ({0} : Set V) at hz
    have hz0 : z = 0 := by
      ext i
      have h := congrArg (fun w : V ↦ star (w i)) (Set.mem_singleton_iff.mp hz)
      simpa only [f, orthogonalComplexificationConjugation, ContinuousMap.coe_mk,
        PiLp.toLp_apply, star_star, PiLp.zero_apply, star_zero] using h
    simp only [hz0, K, Metric.mem_closedBall, dist_self, zero_le_one]
  have hcK : c.inverse.1.datum.control ⊆ K := by
    intro z hz
    change z ∈ ({0} : Set V) at hz
    rw [Set.mem_singleton_iff] at hz
    simp only [hz, K, Metric.mem_closedBall, dist_self, zero_le_one]
  have hproduct (z : V) : z 0 * star (z 0) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = inner ℂ z z := by
        have hi := PiLp.inner_apply (𝕜 := ℂ) z z
        rw [hi]
        simp only [Fin.sum_univ_one, RCLike.inner_apply]
        rfl
      _ = (‖z‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K z
      _ = _ := (Complex.ofReal_pow ‖z‖ 2).symm
  -- At infinity the two original boundaries commute through these exact global maps.
  have hiso : b.IsIsomorphic c.inverse := by
    refine ⟨K, hK, hInv, hbK, hcK, u, v, hueq, hveq, ?_⟩
    intro x w
    obtain ⟨t, rfl⟩ := d₀.symm.surjective w
    have hx : 1 < ‖x.val‖ := by
      simpa only [K, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
        not_le] using x.property
    have hαx : α x.val = x.val 0 * star (x.val 0) := by
      rw [hproduct]
      change ((max 1 (‖x.val‖ ^ 2) : ℝ) : ℂ) = _
      rw [max_eq_right (by nlinarith)]
    have hbval : (b.1.datum.enlarge K hK hbK).boundary.linearEquiv x (d₀.symm t) =
        cliffordSymbolParity (f x.val) 0 (d₀.symm t) := by
      exact (b.1.datum.enlarge_apply K hK hbK x (d₀.symm t)).trans
        (a.1.datum.boundary.pullback_apply f _ (d₀.symm t))
    erw [hbval, hsymbol, hv, LinearEquiv.apply_symm_apply, hu,
      LinearEquiv.apply_symm_apply]
    apply ((c.inverse.1.datum.enlarge K hK hcK).boundary.linearEquiv x).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    let y : (c.1.datum.controlᶜ : Set V) := ⟨x.val, fun h ↦ x.property (hcK h)⟩
    have hcval : (c.inverse.1.datum.enlarge K hK hcK).boundary.linearEquiv x =
        (c.1.datum.boundary.linearEquiv y).symm := by
      apply LinearEquiv.ext
      intro q
      exact c.inverse.1.datum.enlarge_apply K hK hcK x q
    erw [hcval, LinearEquiv.symm_symm]
    erw [RelativeTriple.tensorLeft_tmul]
    change (1 : Fin 1 → ℂ) ⊗ₜ[ℂ]
      cliffordSymbolParity x.val 0 (d₀.symm ((f x.val) 0 • t)) = _
    rw [hsymbol, smul_smul, map_smul, hαx]
    rfl
  -- The original quotient relations supply the sign of the inverse, retaining the character.
  change equivariantSupportTripleKZeroPullback f
    (orthogonalComplexificationConjugation_equivariant 1)
    (orthogonalComplexificationConjugation_isProperMap 1) a.kZeroClass =
      -(finiteRepresentationClass ρ • a.kZeroClass)
  rw [equivariantSupportTripleKZeroPullback_apply]
  calc
    b.kZeroClass = c.inverse.kZeroClass :=
      equivariantSupportTripleKZero_generator_relations.1 b c.inverse hiso
    _ = -c.kZeroClass := c.kZeroClass_inverse
    _ = -(finiteRepresentationClass ρ • a.kZeroClass) := by
      congr 1
      exact (equivariantSupportRepresentationAction_finiteClass ρ a).symm

end AtiyahSinger
