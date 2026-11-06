/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.EndomorphismIntertwiner
public import AtiyahSinger.Algebra.RealSpinor
public import AtiyahSinger.Algebra.SpinorChirality

/-!
# Bilinear duality of the actual complex spinor representation

Public module ID: M0068.

The negative transpose of each original complex Clifford generator defines an
action on the algebraic dual. Matrix-algebra module uniqueness supplies an
intertwining linear equivalence with the original exterior spinor space. The
resulting nondegenerate complex bilinear pairing is contravariant for Clifford
conjugation, hence invariant under the same native Spin group.

Clifford conjugation fixes complex scalars here. This is a bilinear duality;
it must not be confused with the separately constructed Hermitian metric.

Source: the standard contragredient Clifford-module construction, SG I.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The original complex Clifford generators act on the algebraic dual by negative transpose. -/
def complexSpinorDualRepresentation (m : ℕ) :
    CliffordAlgebra (complexSpinorQuadraticForm m) →ₐ[ℂ]
      Module.End ℂ (Module.Dual ℂ (ComplexSpinor m)) :=
  CliffordAlgebra.lift (complexSpinorQuadraticForm m)
    ⟨(-Module.Dual.transpose).comp (complexSpinorGenerator m), by
      intro v
      apply LinearMap.ext
      intro l
      apply LinearMap.ext
      intro s
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, Module.End.mul_apply,
        Module.Dual.transpose_apply, map_neg, neg_neg, Module.algebraMap_end_apply,
        LinearMap.smul_apply]
      change l (complexSpinorGenerator m v (complexSpinorGenerator m v s)) =
        complexSpinorQuadraticForm m v * l s
      have h := congrArg (fun A : Module.End ℂ (ComplexSpinor m) ↦ l (A s))
        (complexSpinorGenerator_sq m v)
      simpa only [Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
        smul_eq_mul] using h⟩

/-- The original spinor space has a nondegenerate bilinear duality for Clifford conjugation. -/
theorem exists_complexSpinor_invariantDuality (m : ℕ) :
    ∃ e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m),
      ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
        e (complexSpinorRepresentation m a s) t =
          e s (complexSpinorRepresentation m (star a) t) := by
  classical
  let : FiniteDimensional ℂ (ComplexSpinor m) :=
    Module.Finite.of_basis (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
  let ρ := (complexSpinorDualRepresentation m).comp (complexSpinorEquiv m).symm.toAlgHom
  obtain ⟨e, he⟩ := exists_linearEquiv_intertwining_algHom ℂ (ComplexSpinor m)
    (Module.Dual ℂ (ComplexSpinor m)) (Subspace.dual_finrank_eq.symm) ρ
  -- The dual action transposes Clifford conjugation; vector generators give negative transposes.
  have htranspose (a : CliffordAlgebra (complexSpinorQuadraticForm m))
      (l : Module.Dual ℂ (ComplexSpinor m)) (t : ComplexSpinor m) :
      complexSpinorDualRepresentation m a l t = l (complexSpinorRepresentation m (star a) t) := by
    induction a using CliffordAlgebra.induction generalizing l t with
    | algebraMap z =>
      simp only [AlgHom.commutes, CliffordAlgebra.star_algebraMap,
        Module.algebraMap_end_apply, LinearMap.smul_apply, map_smul, smul_eq_mul]
    | ι v =>
      simp only [complexSpinorDualRepresentation, CliffordAlgebra.lift_ι_apply,
        LinearMap.comp_apply, LinearMap.neg_apply, CliffordAlgebra.star_ι, map_neg,
        complexSpinorRepresentation, LinearMap.neg_apply, map_neg]
      rfl
    | mul a b ha hb =>
      rw [map_mul, Module.End.mul_apply, ha, hb, star_mul, map_mul, Module.End.mul_apply]
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply, ha, hb, star_add]
  refine ⟨e, ?_⟩
  intro a s t
  have h := he (complexSpinorRepresentation m a) s
  have hroundtrip : (complexSpinorEquiv m).symm (complexSpinorRepresentation m a) = a :=
    (complexSpinorEquiv m).symm_apply_apply a
  change e (complexSpinorRepresentation m a s) =
    complexSpinorDualRepresentation m
      ((complexSpinorEquiv m).symm (complexSpinorRepresentation m a)) (e s) at h
  rw [hroundtrip] at h
  exact (congrArg (fun l : Module.Dual ℂ (ComplexSpinor m) ↦ l t) h).trans
    (htranspose a (e s) t)

/-- Clifford conjugation has the prescribed sign on the original interleaved complex volume. -/
theorem star_complexSpinorVolume (m : ℕ) :
    star (complexSpinorVolume m) = (-1 : ℂ) ^ m • complexSpinorVolume m := by
  classical
  let Q := complexSpinorQuadraticForm m
  let a (i : Fin m) := CliffordAlgebra.ι Q (EuclideanSpace.single i (1 : ℂ), 0)
  let b (i : Fin m) := CliffordAlgebra.ι Q (0, EuclideanSpace.single i (1 : ℂ))
  let J (i : Fin m) := a i * b i
  have hzero (i : Fin m) : EuclideanSpace.single i (0 : ℂ) = 0 := by
    ext j
    simp
  -- Orthogonality gives the anticommutation relations on these exact coordinate generators.
  have hab (i : Fin m) : b i * a i = -(a i * b i) := by
    apply CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    apply QuadraticMap.isOrtho_polarBilin.mp
    simp [Q, complexSpinorQuadraticForm, QuadraticMap.polar]
  have hcross (i j : Fin m) (hij : i ≠ j) (α β γ δ : ℂ) :
      CliffordAlgebra.ι Q (EuclideanSpace.single i α, EuclideanSpace.single i β) *
        CliffordAlgebra.ι Q (EuclideanSpace.single j γ, EuclideanSpace.single j δ) =
      -(CliffordAlgebra.ι Q (EuclideanSpace.single j γ, EuclideanSpace.single j δ) *
        CliffordAlgebra.ι Q (EuclideanSpace.single i α, EuclideanSpace.single i β)) := by
    apply CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
    apply QuadraticMap.isOrtho_polarBilin.mp
    simp [Q, complexSpinorQuadraticForm, QuadraticMap.polar, add_mul, mul_add,
      Finset.sum_add_distrib, mul_ite, ite_mul, hij, Ne.symm hij]
    ring
  have hcomm (i j : Fin m) : Commute (J i) (J j) := by
    by_cases hij : i = j
    · subst j
      exact Commute.refl _
    have hp (γ δ : ℂ) : Commute (J i)
        (CliffordAlgebra.ι Q (EuclideanSpace.single j γ, EuclideanSpace.single j δ)) := by
      let c := CliffordAlgebra.ι Q (EuclideanSpace.single j γ, EuclideanSpace.single j δ)
      have hac : a i * c = -(c * a i) := by simpa [a, c, hzero] using hcross i j hij 1 0 γ δ
      have hbc : b i * c = -(c * b i) := by simpa [b, c, hzero] using hcross i j hij 0 1 γ δ
      change a i * b i * c = c * (a i * b i)
      calc
        a i * b i * c = a i * (b i * c) := mul_assoc _ _ _
        _ = a i * -(c * b i) := by rw [hbc]
        _ = -(a i * c) * b i := by noncomm_ring
        _ = -(-(c * a i)) * b i := by rw [hac]
        _ = c * (a i * b i) := by noncomm_ring
    simpa [J, a, b, hzero] using (hp 1 0).mul_right (hp 0 1)
  have hstar (i : Fin m) : star (J i) = -J i := by
    simpa only [J, a, b, star_mul, CliffordAlgebra.star_ι, neg_mul_neg] using hab i
  -- Reversal contributes one minus sign per plane; the actual plane bivectors commute.
  have hprod (l : List (Fin m)) : star (l.map J).prod =
      (-1 : ℂ) ^ l.length • (l.map J).prod := by
    induction l with
    | nil => simp
    | cons i l ih =>
      have hc : Commute (J i) (l.map J).prod := by
        apply Commute.list_prod_right
        intro c hc
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
        exact hcomm i j
      simp only [List.map_cons, List.prod_cons, star_mul, ih, hstar, List.length_cons,
        mul_neg, smul_mul_assoc, ← hc.eq, pow_succ, mul_smul, neg_smul, one_smul]
  change star (Complex.I ^ m • ((List.ofFn J).prod)) =
    (-1 : ℂ) ^ m • (Complex.I ^ m • ((List.ofFn J).prod))
  rw [CliffordAlgebra.star_smul, List.ofFn_eq_map, hprod, List.length_finRange,
    smul_smul, smul_smul, mul_comm (Complex.I ^ m)]

/-- The original nondegenerate duality pairs half-spin parity with the shift by m modulo two. -/
theorem complexSpinor_invariantDuality_chirality (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (s t : ComplexSpinor m) :
    e (complexSpinorChirality m s) t = (-1 : ℂ) ^ m * e s (complexSpinorChirality m t) := by
  -- The coefficient involution is trivial on ℂ here; the sole sign is the original volume reversal.
  change e (complexSpinorRepresentation m (complexSpinorVolume m) s) t = _
  rw [he, star_complexSpinorVolume, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rfl

/-- The same duality restricts to the original real Clifford action on the same exterior spinors. -/
theorem complexSpinor_invariantDuality_realClifford (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (a : CliffordAlgebra (realSpinorQuadraticForm m)) (s t : ComplexSpinor m) :
    e (realSpinorRepresentation m a s) t = e s (realSpinorRepresentation m (star a) t) := by
  -- Check the original real/imaginary embedding on vectors, then extend by the Clifford algebra.
  induction a using CliffordAlgebra.induction generalizing s t with
  | algebraMap r =>
    simp only [AlgHom.commutes, CliffordAlgebra.star_algebraMap, Module.algebraMap_end_apply]
    rw [LinearMapClass.map_smul_of_tower e, LinearMap.smul_apply,
      LinearMap.map_smul_of_tower]
  | ι v =>
    have h := he (CliffordAlgebra.ι (complexSpinorQuadraticForm m)
      (complexSpinorRealEmbedding m v)) s t
    simpa only [realSpinorRepresentation, complexSpinorRepresentation,
      CliffordAlgebra.lift_ι_apply, CliffordAlgebra.star_ι, map_neg, LinearMap.neg_apply,
      realSpinorGenerator, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_apply, ha, hb, star_mul, map_mul, Module.End.mul_apply]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb, star_add]

/-- The same nondegenerate bilinear pairing is invariant under the native Spin action. -/
theorem complexSpinor_invariantDuality_spin (m : ℕ)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (g : spinGroup (realSpinorQuadraticForm m)) (s t : ComplexSpinor m) :
    e (complexSpinRepresentation m g s) (complexSpinRepresentation m g t) = e s t := by
  -- Membership of this very g identifies its inverse with the original Clifford conjugate.
  change e (realSpinorRepresentation m g.val s) (realSpinorRepresentation m g.val t) = e s t
  rw [complexSpinor_invariantDuality_realClifford m e he,
    ← Module.End.mul_apply, ← map_mul, spinGroup.star_mul_self_of_mem g.property,
    map_one, Module.End.one_apply]

end AtiyahSinger
