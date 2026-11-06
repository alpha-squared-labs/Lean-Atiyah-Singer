/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.SmoothSpinorBundle

/-!
# The original Fock metric on the associated half-spin bundles

Public module ID: M1465.

The original ordered exterior monomials are orthonormal. Their coefficient
pairing fixes the full-spin Hermitian form before restricting to either
original parity subspace. It descends through the original spin action and
quotient representatives. Both halves use this same pairing, including the
even line and odd zero space at m=0. Their smooth metrics use the very
associated atlases selected from the supplied principal atlas.

Sources: Spin Geometry I.5 and II.3--5. Creation and contraction are adjoint
in this monomial pairing, hence their difference is skew-adjoint. Clifford
conjugation is the adjoint in this form; the Spin norm identity gives
unitarity and descent under the original Spin action. The auxiliary exterior
norm used for continuity is not identified with the canonical Hermitian norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff ComplexConjugate

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

/-- The standard Fock pairing makes the original ordered exterior monomials orthonormal. -/
def spinorFockPairing (m : ℕ) (u v : ComplexSpinor m) : ℂ :=
  let c := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra.equivFun
  ∑ a : Finset (Fin m), conj (c u a) * c v a

set_option maxHeartbeats 2000000 in
-- The original exterior-basis creation and contraction adjoint identities use this budget.
/-- Clifford multiplication is skew for the canonical Fock pairing on the original exterior algebra.
This identity gives both Spin invariance of the metric and the half-spin adjoint law. -/
theorem spinorFockPairing_cliffordSymbol (m : ℕ) (a : EuclideanSpace ℂ (Fin m))
    (u v : ComplexSpinor m) :
    spinorFockPairing m (cliffordSymbol a u) v =
      -spinorFockPairing m u (cliffordSymbol a v) := by
  classical
  -- First use the original exterior basis to establish the exact adjoint identities.
  have fock_basis (m : ℕ) :
      let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
      ∀ s t : Finset (Fin m), spinorFockPairing m (b s) (b t) = if s = t then 1 else 0 := by
    classical
    intro b s t
    simp [spinorFockPairing, b]
  have creation_basis (m : ℕ) :
      let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
      ∀ (i : Fin m) (s : Finset (Fin m)), i ∉ s →
        exteriorMultiplication (EuclideanSpace.single i (1 : ℂ)) (b s) = b (insert i s) ∨
        exteriorMultiplication (EuclideanSpace.single i (1 : ℂ)) (b s) = -b (insert i s) := by
    classical
    intro b i s hi
    let u : Set.powersetCard (Fin m) 1 := Set.powersetCard.ofCard
      (s := {i}) (by simp)
    let v : Set.powersetCard (Fin m) s.card := Set.powersetCard.ofCard
      (s := s) rfl
    have hd : Disjoint u.val v.val := by simpa [u, v] using hi
    have hprod := ExteriorAlgebra.basis_mul_of_disjoint
      (EuclideanSpace.basisFun (Fin m) ℂ).toBasis u v hd
    have hu : b u.val = ExteriorAlgebra.ι ℂ (EuclideanSpace.single i (1 : ℂ)) := by
      change (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra {i} = _
      rw [ExteriorAlgebra.basis_apply_ofCard _ (n := 1) (by simp)]
      simp only [OrthonormalBasis.coe_toBasis, ExteriorAlgebra.ιMulti_succ_apply,
        Fin.isValue, Function.comp_apply, EuclideanSpace.basisFun_apply,
        ExteriorAlgebra.ιMulti_zero_apply, mul_one, ExteriorAlgebra.ι_inj]
      congr 1
      apply Finset.mem_singleton.mp
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem u _).mp ⟨(0 : Fin 1), rfl⟩
    have huv : (Set.powersetCard.disjUnion hd).val = insert i s := by
      simp [Set.powersetCard.disjUnion, u, v]
    have hprod' : exteriorMultiplication (EuclideanSpace.single i (1 : ℂ)) (b s) =
        (Set.powersetCard.permOfDisjoint hd).sign • b (insert i s) := by
      change ExteriorAlgebra.ι ℂ (EuclideanSpace.single i (1 : ℂ)) * b v.val = _
      rw [← hu]
      simpa only [huv] using hprod
    rcases Int.units_eq_one_or (Set.powersetCard.permOfDisjoint hd).sign with h | h
    · left
      simpa only [h, one_smul] using hprod'
    · right
      simpa only [h, Units.neg_smul, one_smul] using hprod'
  have fock_adjoint (m : ℕ) (i : Fin m) (u v : ComplexSpinor m) :
      spinorFockPairing m
          (exteriorMultiplication (EuclideanSpace.single i (1 : ℂ)) u) v =
        spinorFockPairing m u (contraction (EuclideanSpace.single i (1 : ℂ)) v) := by
    classical
    let S := ComplexSpinor m
    let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
    let e (j : Fin m) : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single j (1 : ℂ)
    let w : Module.End ℂ S := exteriorMultiplication (e i)
    let c : Module.End ℂ S := contraction (e i)
    let Q := spinorFockPairing m
    let E : S ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
      b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
    have hQ (a d : S) : Q a d = inner ℂ (E a) (E d) := by
      -- Read the same Fock coefficients without unfolding the exterior-basis construction.
      rw [PiLp.inner_apply]
      change (∑ q : Finset (Fin m), conj (b.equivFun a q) * b.equivFun d q) =
        ∑ q : Finset (Fin m), inner ℂ (b.equivFun a q) (b.equivFun d q)
      simp only [RCLike.inner_apply']
    have hQzeroL (a : S) : Q 0 a = 0 := by rw [hQ, map_zero, inner_zero_left]
    have hQzeroR (a : S) : Q a 0 = 0 := by rw [hQ, map_zero, inner_zero_right]
    have hQnegL (a d : S) : Q (-a) d = -Q a d := by rw [hQ, hQ, map_neg, inner_neg_left]
    have hQnegR (a d : S) : Q a (-d) = -Q a d := by rw [hQ, hQ, map_neg, inner_neg_right]
    have hgram (s t : Finset (Fin m)) : Q (b s) (b t) = if s = t then 1 else 0 :=
      fock_basis m s t
    have hcW (a : S) : c (w a) = a - w (c a) := by
      change CliffordAlgebra.contractLeft (innerₛₗ ℂ (e i))
          (ExteriorAlgebra.ι ℂ (e i) * a) = _
      rw [CliffordAlgebra.contractLeft_ι_mul]
      change inner ℂ (e i) (e i) • a - w (c a) = _
      simp [e]
    have hwW (a : S) : w (w a) = 0 := by
      change ExteriorAlgebra.ι ℂ (e i) * (ExteriorAlgebra.ι ℂ (e i) * a) = 0
      rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
    -- The contraction annihilates every original monomial which omits its index.
    let z (j : Fin m) : S := ExteriorAlgebra.ι ℂ (e j)
    let mon (l : List (Fin m)) : S := (l.map z).prod
    have hcmon (l : List (Fin m)) (hi : i ∉ l) : c (mon l) = 0 := by
      induction l with
      | nil => exact CliffordAlgebra.contractLeft_one _ _
      | cons j l ih =>
        have hij : i ≠ j := fun h ↦ hi (List.mem_cons.mpr (Or.inl h))
        change CliffordAlgebra.contractLeft (innerₛₗ ℂ (e i))
          (ExteriorAlgebra.ι ℂ (e j) * mon l) = 0
        rw [CliffordAlgebra.contractLeft_ι_mul]
        change inner ℂ (e i) (e j) • mon l - z j * c (mon l) = 0
        rw [EuclideanSpace.inner_single_left]
        simp [e, hij, ih (fun h ↦ hi (List.mem_cons_of_mem _ h))]
    let seq (s : Finset (Fin m)) : List (Fin m) :=
      List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))
    have hseq (s : Finset (Fin m)) : i ∈ seq s ↔ i ∈ s :=
      (List.mem_ofFn' _ _).trans
        (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _)
    have hb (s : Finset (Fin m)) : b s = mon (seq s) := by
      rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
      simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
        Function.comp_def, mon, seq, List.map_ofFn]
      congr 2
      funext j
      simp [z, e]
    have hc0 (s : Finset (Fin m)) (hi : i ∉ s) : c (b s) = 0 := by
      rw [hb]
      exact hcmon _ (fun h ↦ hi ((hseq s).mp h))
    have hcreate (s : Finset (Fin m)) (hi : i ∉ s) :
        w (b s) = b (insert i s) ∨ w (b s) = -b (insert i s) :=
      creation_basis m i s hi
    have hw0 (s : Finset (Fin m)) (hi : i ∈ s) : w (b s) = 0 := by
      have his : i ∉ s.erase i := Finset.notMem_erase i s
      rcases hcreate (s.erase i) his with hs | hs
      · rw [Finset.insert_erase hi] at hs
        rw [← hs, hwW]
      · rw [Finset.insert_erase hi] at hs
        have hs' : b s = -w (b (s.erase i)) := by rw [hs, neg_neg]
        rw [hs', map_neg, hwW, neg_zero]
    -- Creation carries the monomial subspace omitting i isometrically onto its image.
    have hisometry (s t : Finset (Fin m)) (hs : i ∉ s) (ht : i ∉ t) :
        Q (w (b s)) (w (b t)) = Q (b s) (b t) := by
      have hinj : insert i s = insert i t ↔ s = t := by
        constructor
        · intro h
          have := congrArg (fun q : Finset (Fin m) ↦ q.erase i) h
          simpa [hs, ht] using this
        · exact congrArg (insert i)
      by_cases hst : s = t
      · subst t
        rcases hcreate s hs with h | h
        · rw [h, hgram, hgram]
          simp
        · rw [h, hQnegL, hQnegR, hgram, hgram]
          simp
      · have hneq : insert i s ≠ insert i t := fun h ↦ hst (hinj.mp h)
        rcases hcreate s hs with h | h <;> rcases hcreate t ht with h' | h'
        all_goals
          simp only [h, h', hQnegL, hQnegR, hgram, ite_eq_right hneq,
            ite_eq_right hst, neg_zero]
    -- Verify the adjoint formula on the original ordered monomials.
    have hadjoint (s t : Finset (Fin m)) : Q (w (b s)) (b t) = Q (b s) (c (b t)) := by
      by_cases ht : i ∈ t
      · have hit : i ∉ t.erase i := Finset.notMem_erase i t
        rcases hcreate (t.erase i) hit with h | h
        · rw [Finset.insert_erase ht] at h
          rw [← h, hcW, hc0 _ hit, map_zero, sub_zero]
          by_cases hs : i ∈ s
          · have hne : s ≠ t.erase i := by
              intro heq
              exact hit (heq ▸ hs)
            rw [hw0 s hs, hQzeroL, hgram, ite_eq_right hne]
          · exact hisometry s (t.erase i) hs hit
        · rw [Finset.insert_erase ht] at h
          have h' : b t = -w (b (t.erase i)) := by rw [h, neg_neg]
          rw [h', hQnegR, map_neg, hcW, hc0 _ hit, map_zero, sub_zero, hQnegR]
          by_cases hs : i ∈ s
          · have hne : s ≠ t.erase i := by
              intro heq
              exact hit (heq ▸ hs)
            rw [hw0 s hs, hQzeroL, hgram, ite_eq_right hne]
          · rw [hisometry s (t.erase i) hs hit]
      · rw [hc0 t ht, hQzeroR]
        by_cases hs : i ∈ s
        · rw [hw0 s hs, hQzeroL]
        · have hne : insert i s ≠ t := by
            intro heq
            exact ht (heq ▸ Finset.mem_insert_self i s)
          rcases hcreate s hs with h | h
          · rw [h, hgram, ite_eq_right hne]
          · rw [h, hQnegL, hgram, ite_eq_right hne, neg_zero]
    have hadjointE (s t : Finset (Fin m)) :
        inner ℂ (E (w (b s))) (E (b t)) = inner ℂ (E (b s)) (E (c (b t))) := by
      simpa only [hQ] using hadjoint s t
    change Q (w u) v = Q u (c v)
    rw [hQ, hQ, ← b.sum_repr u, ← b.sum_repr v]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      hadjointE]
  -- Sesquilinearity extends the coordinate adjoint formula to every vector.
  have fock_adjoint_all (m : ℕ) (a : EuclideanSpace ℂ (Fin m))
      (u v : ComplexSpinor m) :
      spinorFockPairing m (exteriorMultiplication a u) v =
        spinorFockPairing m u (contraction a v) := by
    classical
    let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
    let E : ComplexSpinor m ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
      b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
    have hQ (s t : ComplexSpinor m) : spinorFockPairing m s t = inner ℂ (E s) (E t) := by
      -- Read the same Fock coefficients without unfolding the exterior-basis construction.
      rw [PiLp.inner_apply]
      change (∑ q : Finset (Fin m), conj (b.equivFun s q) * b.equivFun t q) =
        ∑ q : Finset (Fin m), inner ℂ (b.equivFun s q) (b.equivFun t q)
      simp only [RCLike.inner_apply']
    have ha : a = ∑ j : Fin m, a j • EuclideanSpace.single j (1 : ℂ) := by
      ext j
      simp [EuclideanSpace.single, Pi.single_apply]
    rw [ha]
    simp only [exteriorMultiplication, contraction, map_sum, map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, RingHom.id_apply]
    rw [hQ, hQ]
    simp only [map_sum, map_smul, sum_inner, inner_smul_left, inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simpa only [exteriorMultiplication, contraction, hQ] using fock_adjoint m j u v
  have fock_skew (m : ℕ) (a : EuclideanSpace ℂ (Fin m)) (u v : ComplexSpinor m) :
      spinorFockPairing m (cliffordSymbol a u) v =
        -spinorFockPairing m u (cliffordSymbol a v) := by
    classical
    let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
    let E : ComplexSpinor m ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
      b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
    have hQ (s t : ComplexSpinor m) : spinorFockPairing m s t = inner ℂ (E s) (E t) := by
      -- Read the same Fock coefficients without unfolding the exterior-basis construction.
      rw [PiLp.inner_apply]
      change (∑ q : Finset (Fin m), conj (b.equivFun s q) * b.equivFun t q) =
        ∑ q : Finset (Fin m), inner ℂ (b.equivFun s q) (b.equivFun t q)
      simp only [RCLike.inner_apply']
    have hadj (s t : ComplexSpinor m) :
        inner ℂ (E (exteriorMultiplication a s)) (E t) =
          inner ℂ (E s) (E (contraction a t)) := by
      simpa only [hQ] using fock_adjoint_all m a s t
    have hadj' : inner ℂ (E (contraction a u)) (E v) =
        inner ℂ (E u) (E (exteriorMultiplication a v)) := by
      have h := congrArg conj (hadj v u)
      simpa only [inner_conj_symm] using h.symm
    simp only [cliffordSymbol, LinearMap.sub_apply, hQ, map_sub, inner_sub_left,
      inner_sub_right, hadj, hadj', neg_sub]
  exact fock_skew m a u v

variable (m : ℕ) {n : ℕ} {P M : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)
  (A : SmoothSpinPrincipalAtlas m 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) projection)

set_option maxHeartbeats 2000000 in
-- Descent of the original Fock form and the same half-spin metric uses this budget.
-- Retain the declared manifold hypothesis in the metric construction.
set_option linter.unusedSectionVars false in
/-- The fixed Fock form descends uniquely to a smooth metric on each original half-spin bundle. -/
theorem existsUnique_halfSpinorHermitianMetric (i : ZMod 2) :
    ∃! h : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP i),
      (halfSpinorBundleSmoothAtlas m hP A i).IsSmoothHermitianMetric h ∧
        ∀ (p : P) (x : M) (hp : projection p = x)
          (u v : CliffordAlgebra.evenOdd
            (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i),
          (h.toCore x).inner
              (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp u)
              (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp v) =
            spinorFockPairing m u.val v.val := by
  /- Stage 1: the exterior basis coefficient sum is positive definite and
  sesquilinear. Exterior multiplication and contraction are adjoint for
  this exact form, so Clifford multiplication by a real vector is skew.
  Induction on the Clifford algebra identifies Clifford conjugation
  with the adjoint in this form. The Spin norm identity then proves
  unitarity of the original Spin action.
  Stage 2: restrict the same full form to each invariant parity space.
  Its unitarity makes the displayed formula independent of the common
  principal representative, so it defines a positive form on the original
  quotient fibers. In the actual associated charts its matrix is the
  constant Fock matrix transported by fixed linear coordinates; hence the
  form is continuous and smooth in the specified selected atlas.
  Stage 3: every fiber vector has a representative at any principal point
  over its base. The displayed formula therefore determines the metric
  uniquely. Neither a new spinor carrier nor a different parity convention
  enters the construction; the zero odd space at m=0 causes no exception. -/
  classical
  -- Reuse the same Fock adjoint identity needed by the geometric Clifford symbol.
  have fock_skew := spinorFockPairing_cliffordSymbol
  -- Clifford conjugation packages the unit-generator argument for the native Spin group.
  have fock_spin_invariant (m : ℕ) (g : spinGroup (realSpinorQuadraticForm m))
      (u v : ComplexSpinor m) :
      spinorFockPairing m (complexSpinRepresentation m g u) (complexSpinRepresentation m g v) =
        spinorFockPairing m u v := by
    classical
    let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
    let E : ComplexSpinor m ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
      b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
    let Q := spinorFockPairing m
    let R := realSpinorRepresentation m
    have hQ (s t : ComplexSpinor m) : Q s t = inner ℂ (E s) (E t) := by
      simp [Q, spinorFockPairing, E, b, PiLp.inner_apply, mul_comm]
    -- Native Clifford conjugation is the adjoint in this exact Fock pairing.
    have hadjoint (a : CliffordAlgebra (realSpinorQuadraticForm m)) :
        ∀ s t : ComplexSpinor m, Q (R a s) t = Q s (R (star a) t) := by
      induction a using CliffordAlgebra.induction with
      | algebraMap r =>
        intro s t
        simp only [CliffordAlgebra.star_algebraMap, AlgHom.commutes]
        rw [hQ, hQ]
        change inner ℂ (E ((r : ℂ) • s)) (E t) = inner ℂ (E s) (E ((r : ℂ) • t))
        rw [map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      | add a a' ha ha' =>
        intro s t
        simp only [map_add, LinearMap.add_apply, star_add, hQ, inner_add_left,
          inner_add_right]
        rw [← hQ, ← hQ, ← hQ, ← hQ, ha, ha']
      | ι a =>
        intro s t
        change Q (realSpinorRepresentation m (CliffordAlgebra.ι _ a) s) t =
          Q s (realSpinorRepresentation m (star (CliffordAlgebra.ι _ a)) t)
        rw [CliffordAlgebra.star_ι, map_neg, LinearMap.neg_apply,
          realSpinorRepresentation_ι]
        have hs : Q (cliffordSymbol a s) t = -Q s (cliffordSymbol a t) :=
          fock_skew m a s t
        rw [hs, hQ, hQ, map_neg, inner_neg_right]
      | mul a a' ha ha' =>
        intro s t
        simp only [map_mul, Module.End.mul_apply, star_mul]
        rw [ha, ha']
    change Q (R (g : CliffordAlgebra (realSpinorQuadraticForm m)) u)
        (R (g : CliffordAlgebra (realSpinorQuadraticForm m)) v) = Q u v
    rw [hadjoint, ← Module.End.mul_apply, ← map_mul,
      spinGroup.star_mul_self_of_mem g.property, map_one]
    rfl
  -- Spin invariance descends the prescribed form to the original quotient fibers.
  have metric_core_descent (i : ZMod 2) :
      ∃ core : ∀ x : M, InnerProductSpace.Core ℂ (HalfSpinorBundle m hP i x),
        ∀ (p : P) (x : M) (hp : projection p = x)
          (u v : CliffordAlgebra.evenOdd
            (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i),
          (core x).inner
              (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp u)
              (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp v) =
            spinorFockPairing m u.val v.val := by
    classical
    let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
    let ρ := complexSpinParityContRepresentation m i
    let : MulAction (spinGroup (realSpinorQuadraticForm m)) W := associatedRepresentationAction ρ
    let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
    let E : ComplexSpinor m ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
      b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
        (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
    have hQ (s t : ComplexSpinor m) : spinorFockPairing m s t = inner ℂ (E s) (E t) := by
      simp [spinorFockPairing, E, b, PiLp.inner_apply, mul_comm]
    let L (x : M) : HalfSpinorBundle m hP i x →ₗ[ℂ] ComplexSpinor m :=
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i).subtype.comp
        (associatedVectorFiberLinearEquiv hP ρ x).toLinearMap
    let C (x : M) : HalfSpinorBundle m hP i x →ₗ[ℂ]
        EuclideanSpace ℂ (Finset (Fin m)) := E.toLinearMap.comp (L x)
    have hC (x : M) : Function.Injective (C x) := by
      intro u v h
      apply (associatedVectorFiberLinearEquiv hP ρ x).injective
      apply Subtype.val_injective
      exact E.injective h
    let core (x : M) : InnerProductSpace.Core ℂ (HalfSpinorBundle m hP i x) := {
      inner u v := inner ℂ (C x u) (C x v)
      conj_inner_symm u v := inner_conj_symm _ _
      re_inner_nonneg u := inner_self_nonneg
      add_left u v w := by rw [map_add, inner_add_left]
      smul_left u v c := by rw [map_smul, inner_smul_left]
      definite u hu := hC x (by simpa only [map_zero] using inner_self_eq_zero.mp hu) }
    refine ⟨core, ?_⟩
    intro p x hp u v
    let p₀ : P := (hP.projection_properties.2.2 x).choose
    have hp₀ : projection p₀ = x := (hP.projection_properties.2.2 x).choose_spec
    obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p₀ p (hp₀.trans hp.symm)
    let e₀ := associatedVectorFiberLinearEquiv hP ρ x
    have hcoord (w : W) : associatedVectorFiberMk hP ρ p hp w = e₀.symm (ρ g w) := by
      apply Subtype.ext
      change associatedBundleMk _ P W p w = associatedBundleMk _ P W p₀ (ρ g w)
      rw [← hg]
      exact associatedBundleMk_smul p₀ g w
    change inner ℂ (C x (associatedVectorFiberMk hP ρ p hp u))
        (C x (associatedVectorFiberMk hP ρ p hp v)) = _
    rw [hcoord u, hcoord v]
    simp only [C, L, e₀, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      LinearEquiv.apply_symm_apply]
    rw [← hQ]
    exact fock_spin_invariant m g u.val v.val
  have metric_localization (i : ZMod 2)
      (core : ∀ x : M, InnerProductSpace.Core ℂ (HalfSpinorBundle m hP i x))
      (hcore : ∀ (p : P) (x : M) (hp : projection p = x)
        (u v : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i),
        (core x).inner
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp u)
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp v) =
          spinorFockPairing m u.val v.val) :
      let B := halfSpinorBundleSmoothAtlas m hP A i
      ∀ x₀ : M, ∃ (j : B.Index)
        (c : (CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) ≃ₗ[ℂ] (Fin (B.rank j) → ℂ)),
        x₀ ∈ (B.chart j).baseSet ∧
          ∀ (x : M), x ∈ (B.chart j).baseSet → ∀ u v : HalfSpinorBundle m hP i x,
            (core x).inner u v =
              spinorFockPairing m (c.symm ((B.chart j ⟨x, u⟩).2)).val
                (c.symm ((B.chart j ⟨x, v⟩).2)).val := by
    classical
    intro B x₀
    let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
    let ρ := complexSpinParityContRepresentation m i
    let : MulAction (spinGroup (realSpinorQuadraticForm m)) W := associatedRepresentationAction ρ
    obtain ⟨j, c, hbase, hrep⟩ := (spinorBundleSmoothAtlases_compatibility m hP A).2.1 i x₀
    refine ⟨j, c, hbase.symm ▸ A.mem_baseSet x₀, ?_⟩
    intro x hx u v
    have hx' : x ∈ (A.trivialization x₀).baseSet := hbase ▸ hx
    let p : P := (A.trivialization x₀).toPartialEquiv.symm (x, 1)
    have hp : projection p = x := (A.trivialization x₀).proj_symm_apply' hx'
    obtain ⟨u', rfl⟩ := (associatedVectorFiberMk_bijective hP ρ p hp).surjective u
    obtain ⟨v', rfl⟩ := (associatedVectorFiberMk_bijective hP ρ p hp).surjective v
    have hchart (w : W) :
        (B.chart j ⟨x, associatedVectorFiberMk hP ρ p hp w⟩).2 = c w := by
      rw [hrep p x hp hx' w]
      dsimp only [p]
      erw [(A.trivialization x₀).apply_symm_apply' (x := (1 : spinGroup
        (realSpinorQuadraticForm m))) hx']
      simp
    rw [hcore p x hp, hchart u', hchart v', LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  let F := HalfSpinorBundle m hP i
  let B := halfSpinorBundleSmoothAtlas m hP A i
  let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let ρ := complexSpinParityContRepresentation m i
  let : MulAction (spinGroup (realSpinorQuadraticForm m)) W := associatedRepresentationAction ρ
  let : ComplexBundle.IsFiniteRank F := B.isFiniteRank
  let : TopologicalSpace (TotalSpace Unit (F ×ᵇ F)) := ComplexBundle.sumTopology
  let b := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
  let E : ComplexSpinor m ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
    b.equivFun.trans (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Finset (Fin m) ↦ ℂ)).symm.toLinearEquiv
  have hQ (s t : ComplexSpinor m) : spinorFockPairing m s t = inner ℂ (E s) (E t) := by
    simp [spinorFockPairing, E, b, PiLp.inner_apply, mul_comm]
  obtain ⟨core, hcore⟩ := metric_core_descent i
  have hlocal := metric_localization i core hcore
  -- The prescribed Fock matrix is constant in the actual associated chart coordinates.
  let T (j : B.Index) (c : W ≃ₗ[ℂ] (Fin (B.rank j) → ℂ)) :
      (Fin (B.rank j) → ℂ) →L[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
    (E.toLinearMap.comp (W.subtype.comp c.symm.toLinearMap)).toContinuousLinearMap
  have hcontinuous : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦
      (core z.proj).inner z.snd.1 z.snd.2) := by
    have hfst : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦
        (⟨z.proj, z.snd.1⟩ : TotalSpace Unit F)) := ComplexBundle.continuous_sum_fst
    have hsnd : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F)) := ComplexBundle.continuous_sum_snd
    have hbase : Continuous (π Unit (F ×ᵇ F)) :=
      (ComplexBundle.continuous_proj (E := F)).comp hfst
    rw [continuous_iff_continuousAt]
    intro z
    obtain ⟨j, c, hz, hform⟩ := hlocal z.proj
    have hvec₁ : ContinuousOn (fun w : TotalSpace Unit (F ×ᵇ F) ↦
        T j c ((B.chart j ⟨w.proj, w.snd.1⟩).2))
        (π Unit (F ×ᵇ F) ⁻¹' (B.chart j).baseSet) :=
      (T j c).continuous.comp_continuousOn
        (continuous_snd.comp_continuousOn
          ((B.chart j).toOpenPartialHomeomorph.continuousOn.comp hfst.continuousOn
            (fun w hw ↦ (B.chart j).mem_source.mpr hw)))
    have hvec₂ : ContinuousOn (fun w : TotalSpace Unit (F ×ᵇ F) ↦
        T j c ((B.chart j ⟨w.proj, w.snd.2⟩).2))
        (π Unit (F ×ᵇ F) ⁻¹' (B.chart j).baseSet) :=
      (T j c).continuous.comp_continuousOn
        (continuous_snd.comp_continuousOn
          ((B.chart j).toOpenPartialHomeomorph.continuousOn.comp hsnd.continuousOn
            (fun w hw ↦ (B.chart j).mem_source.mpr hw)))
    have hopen := (B.chart j).open_baseSet.preimage hbase
    apply ((hvec₁.inner hvec₂).continuousAt (hopen.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hz] with w hw
    rw [hform w.proj hw w.snd.1 w.snd.2, hQ]
    rfl
  let h : ComplexBundle.ContinuousHermitianMetric F := {
    toCore := core
    continuous_pairing := hcontinuous
    isFiniteRank := B.isFiniteRank }
  -- In every selected frame, its true transition columns transport the same Fock form.
  have hsmooth : B.IsSmoothHermitianMetric h := by
    intro k a d x hx
    obtain ⟨j, c, hxi, hform⟩ := hlocal x
    let inv (v : Fin (B.rank k) → ℂ) (y : M) : F y :=
      if hy : y ∈ (B.chart k).baseSet then (B.frameLinearEquiv k y hy).symm v else 0
    have hpoint (v : Fin (B.rank k) → ℂ) (y : M)
        (hy : y ∈ (B.chart k).baseSet) :
        (⟨y, inv v y⟩ : TotalSpace Unit F) = (B.chart k).toPartialEquiv.symm (y, v) := by
      dsimp only [inv]
      rw [dite_eq_left hy]
      exact TotalSpace.mk_cast (F := Unit) (E := F) ((B.chart k).proj_symm_apply' hy) _
    have hvec (v : Fin (B.rank k)) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Finset (Fin m))) ∞
          (fun y ↦ T j c ((B.chart j ⟨y, inv (Pi.single v 1) y⟩).2))
          ((B.chart k).baseSet ∩ (B.chart j).baseSet) := by
      have hcol := ((T j c).restrictScalars ℝ).contDiff.contMDiff.comp_contMDiffOn
        (B.contMDiffOn_coordChange k j v)
      apply hcol.congr
      intro y hy
      rw [hpoint (Pi.single v 1) y hy.1]
      rfl
    have hpair := (contDiff_inner (𝕜 := ℂ)).contMDiff.comp_contMDiffOn
      ((hvec a).prodMk_space (hvec d))
    have hpairAt := hpair.contMDiffAt
      (((B.chart k).open_baseSet.inter (B.chart j).open_baseSet).mem_nhds ⟨hx, hxi⟩)
    apply hpairAt.contMDiffWithinAt.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((B.chart j).open_baseSet.mem_nhds hxi)] with y hy hyj
      rw [dite_eq_left hy]
      change (core y).inner ((B.frameLinearEquiv k y hy).symm (Pi.single a 1))
          ((B.frameLinearEquiv k y hy).symm (Pi.single d 1)) = _
      rw [hform y hyj, hQ]
      simp only [Function.comp_apply, inv, dite_eq_left hy]
      rfl
    · rw [dite_eq_left hx]
      change (core x).inner ((B.frameLinearEquiv k x hx).symm (Pi.single a 1))
          ((B.frameLinearEquiv k x hx).symm (Pi.single d 1)) = _
      rw [hform x hxi, hQ]
      simp only [Function.comp_apply, inv, dite_eq_left hx]
      rfl
  refine ⟨h, ⟨hsmooth, hcore⟩, ?_⟩
  -- Representatives at one common principal point determine every original fiber pairing.
  intro h' hh'
  have hcore_ext (x : M) (a d : InnerProductSpace.Core ℂ (F x))
      (had : a.inner = d.inner) : a = d := by
    rcases a with ⟨⟨⟨f⟩, hs, hp, ha, hm⟩, hd⟩
    rcases d with ⟨⟨⟨g⟩, hs', hp', ha', hm'⟩, hd'⟩
    change f = g at had
    cases had
    rfl
  have hext (a d : ComplexBundle.ContinuousHermitianMetric F)
      (had : ∀ x (u v : F x), (a.toCore x).inner u v = (d.toCore x).inner u v) : a = d := by
    cases a with
    | mk ca ha _ =>
      cases d with
      | mk cd hd _ =>
        congr 1
        funext x
        exact hcore_ext x (ca x) (cd x) (funext fun u ↦ funext fun v ↦ had x u v)
  apply hext
  intro x u v
  obtain ⟨p, hp⟩ := hP.projection_properties.2.2 x
  obtain ⟨u', rfl⟩ := (associatedVectorFiberMk_bijective hP ρ p hp).surjective u
  obtain ⟨v', rfl⟩ := (associatedVectorFiberMk_bijective hP ρ p hp).surjective v
  exact (hh'.2 p x hp u' v').trans (hcore p x hp u' v').symm

/-- The canonical Fock metric on the specified original half-spin bundle. -/
def halfSpinorHermitianMetric (i : ZMod 2) :
    ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP i) :=
  (existsUnique_halfSpinorHermitianMetric m hP A i).exists.choose

set_option linter.defProp false in
/-- The selected metric retains both the original Fock formula and the same smooth atlas. -/
def halfSpinorHermitianMetric_properties (i : ZMod 2) :
    (halfSpinorBundleSmoothAtlas m hP A i).IsSmoothHermitianMetric
        (halfSpinorHermitianMetric m hP A i) ∧
      ∀ (p : P) (x : M) (hp : projection p = x)
        (u v : CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i),
        ((halfSpinorHermitianMetric m hP A i).toCore x).inner
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp u)
            (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp v) =
          spinorFockPairing m u.val v.val :=
  (existsUnique_halfSpinorHermitianMetric m hP A i).exists.choose_spec

end AtiyahSinger
