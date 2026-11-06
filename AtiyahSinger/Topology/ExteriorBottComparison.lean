/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorWeights
public import AtiyahSinger.Topology.BottEuclidean
public import AtiyahSinger.Topology.ExteriorBott
public import Mathlib.Analysis.InnerProductSpace.PiL2

import AtiyahSinger.Topology.EquivariantBottProduct
import Mathlib.Algebra.Module.PUnit

/-!
# The exterior-symbol class and the specified Bott generator

Public module ID: M1838.

Compare the actual even-to-odd exterior triple with the previously fixed
iterated multiplication-by-z class. Euclidean coordinates use the standard
`PiLp.homeomorph`; the comparison does not select an unspecified generator of ℤ.

Sources: SG Appendix C.3, Karoubi II.5.21--5.22, IV.1.4--1.7 and the point
calculation in the proof of IV.1.9. The multiplicativity theorem is the vector-space specialization
of Proposition IV.1.7. The actual graded tensor argument interpolates reciprocal
cutoffs and changes the odd-odd source sign to compare the product with the SG
negative-contraction symbol. The general bundle Thom theorem IV.1.9 is not
used as an input to Bott periodicity.

The coordinate comparison, Bott bijectivity, and the positive integer normalization
are proved in every dimension. General Thom classes over noncompact bases require
a separate fiberwise-support construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The actual exterior-symbol class expressed in the standard finite complex coordinates. -/
def exteriorBottEuclideanClass (n : ℕ) : CompactSupportKZero (Fin n → ℂ) :=
  compactSupportKZeroHomeomorph (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℂ))
    (exteriorBottClass (EuclideanSpace ℂ (Fin n)))

/-- In dimension zero, the exterior triple is the positive rank-one point class. -/
theorem exteriorBottEuclideanClass_zero :
    exteriorBottEuclideanClass 0 = bottEuclideanClass 0 := by
  /- Stage 1: the exterior algebra of the zero vector space is ℂ, entirely
  even, and its odd subspace is zero. Identify these actual spaces by the
  algebra unit and the unique zero-space map, using their finite-dimensional
  topologies. The complement of {0} in the base is empty, so the boundary
  imposes no isomorphism between the unequal even and odd ranks at zero.
  Stage 2: the resulting compact-support triple on the point has absolute
  class [ℂ]-[0], exactly the original positive rank-one identity class.
  The compact-to-absolute comparison and the same unique point homeomorphism
  identify it with the defining zero case of bottEuclideanClass. -/
  classical
  let V := EuclideanSpace ℂ (Fin 0)
  let P (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let := exteriorAlgebra_finiteDimensional (V := V)
  let := exteriorAlgebraNormedAddCommGroup (V := V)
  let := exteriorAlgebraNormedSpace (V := V)
  let := FiniteDimensional.proper ℂ V
  let : CompactSpace V := inferInstance
  let (i : ZMod 2) := ComplexBundle.modelTopology (P i) (Bundle.Trivial V (P i))
  let (i : ZMod 2) := ComplexBundle.isFiniteRank_model (P i) (Bundle.Trivial V (P i))
  let (k : ℕ) := ComplexBundle.trivialTopology (X := V) k
  let (k : ℕ) := ComplexBundle.isFiniteRank_trivial (X := V) k
  -- The empty exterior monomial supplies the positive line, and the odd basis is empty.
  let I := {s : Finset (Fin 0) // (s.card : ZMod 2) = 0}
  let : Unique I :=
    { default := ⟨∅, by simp⟩
      uniq := fun s ↦ Subtype.ext (Subsingleton.elim _ _) }
  let d₀ : P 0 ≃ₗ[ℂ] (Fin 1 → ℂ) := (complexSpinorParityBasis 0 0).equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 1 ↦ ℂ) (Equiv.ofUnique I (Fin 1)))
  let J := {s : Finset (Fin 0) // (s.card : ZMod 2) = 1}
  let : IsEmpty J := ⟨fun s ↦ by
    have hs : s.val = ∅ := Subsingleton.elim _ _
    have h := s.property
    simp [hs] at h⟩
  let d₁ : P 1 ≃ₗ[ℂ] (Fin 0 → ℂ) := (complexSpinorParityBasis 0 1).equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 0 ↦ ℂ) (Equiv.equivOfIsEmpty J (Fin 0)))
  -- These fixed coordinates define genuine continuous maps for the original model topologies.
  have hiso (i : ZMod 2) (k : ℕ) (d : P i ≃ₗ[ℂ] (Fin k → ℂ)) :
      Nonempty (ComplexBundle.Iso (Bundle.Trivial V (P i))
        (Bundle.Trivial V (Fin k → ℂ))) := by
    let h := (ComplexBundle.unitTotalHomeomorph (P i) (Bundle.Trivial V (P i))).trans
      (Bundle.Trivial.homeomorphProd V (P i))
    let A : ComplexBundle.Hom (Bundle.Trivial V (P i)) (Bundle.Trivial V (Fin k → ℂ)) :=
      { linearMap := fun _ ↦ d.toLinearMap
        continuous_total := by
          apply continuous_induced_rng.mpr
          exact h.continuous.fst.prodMk
            (d.continuous_of_finiteDimensional.comp h.continuous.snd) }
    exact ⟨A.toIso (fun _ ↦ d.bijective)⟩
  have h₀ := ComplexBundle.kZeroClass_eq_of_iso (hiso 0 1 d₀).some
  have h₁ := ComplexBundle.kZeroClass_eq_of_iso (hiso 1 0 d₁).some
  have habsolute : compactSupportKZeroToAbsolute (exteriorBottClass V) =
      kZeroClass C(V, ℂ) (IdempotentMatrix.identity C(V, ℂ) 1) := by
    change compactSupportKZeroToAbsolute
      (exteriorBottTriple V).toSupportBundleTriple.compactSupportClass = _
    rw [ComplexBundle.SupportBundleTriple.compactSupportClass_toAbsolute]
    change ComplexBundle.kZeroClass (ComplexBundle.smallBundle
        (Bundle.Trivial V (P 0))).Fiber -
      ComplexBundle.kZeroClass (ComplexBundle.smallBundle (Bundle.Trivial V (P 1))).Fiber = _
    rw [← ComplexBundle.kZeroClass_eq_of_iso (ComplexBundle.smallBundleIso
      (Bundle.Trivial V (P 0))), ← ComplexBundle.kZeroClass_eq_of_iso
        (ComplexBundle.smallBundleIso (Bundle.Trivial V (P 1)))]
    rw [h₀, h₁, ComplexBundle.kZeroClass_trivial, ComplexBundle.kZeroClass_trivial_zero,
      sub_zero]
  -- Forgetting support commutes with the very same inverse base map used by transport.
  have hfinite {A B : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
      [CompactSpace A] [CompactSpace B]
      (f : C(B, A)) (hf : IsProperMap f) (a : CompactSupportKZero A) :
      compactSupportKZeroToAbsolute (compactSupportKZeroPullback f hf a) =
        complexKZeroPullback f (compactSupportKZeroToAbsolute a) := by
    change complexKZeroPullback
        ⟨((↑) : B → OnePoint B), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap f hf) a.val) =
      complexKZeroPullback f (complexKZeroPullback
        ⟨((↑) : A → OnePoint A), OnePoint.continuous_coe⟩ a.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hunit {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
      [CompactSpace A] [T2Space A] [CompactSpace B] [T2Space B] (f : C(B, A)) :
      complexKZeroPullback f (kZeroClass C(A, ℂ) (IdempotentMatrix.identity C(A, ℂ) 1)) =
        kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1) := by
    change kZeroMap _ (kZeroClass _ _) = _
    rw [kZeroMap_class]
    congr 1
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom.mapMatrix.map_one
  have hpoint : compactSupportKZeroToAbsolute compactSupportKZeroPointOne =
      kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1) :=
    (compactSupportKZeroCompactEquiv PUnit.{1}).apply_symm_apply _
  -- Both specified point transports now have the identical positive absolute class.
  apply compactSupportKZeroToAbsolute_bijective.1
  change compactSupportKZeroToAbsolute (compactSupportKZeroHomeomorph
      (PiLp.homeomorph 2 (fun _ : Fin 0 ↦ ℂ)) (exteriorBottClass V)) =
    compactSupportKZeroToAbsolute (compactSupportKZeroHomeomorph
      (Homeomorph.homeomorphOfUnique PUnit.{1} (Fin 0 → ℂ)) compactSupportKZeroPointOne)
  unfold compactSupportKZeroHomeomorph
  rw [hfinite, hfinite, habsolute, hpoint, hunit, hunit]

set_option maxHeartbeats 800000 in

open Bundle ComplexBundle in
/-- The one-dimensional exterior symbol is the original multiplication-by-z line class. -/
theorem exteriorBottEuclideanClass_one :
    compactSupportKZeroHomeomorph (Homeomorph.funUnique (Fin 1) ℂ)
      (exteriorBottEuclideanClass 1) = bottLineClass := by
  /- Stage 1: use the even basis 1 and odd basis given by the unique unit
  coordinate vector of EuclideanSpace ℂ (Fin 1). The Clifford formula in
  dimension one has even-to-odd block z and odd-to-even block -conj(z).
  Stage 2: these finite-dimensional linear coordinate maps are continuous
  bundle isomorphisms. On the punctured line the transported boundary is
  precisely multiplication by the original z, with the same control {0}.
  Invariance of the raw-triple class under those isomorphisms gives the
  original bottLineTriple class, not a class determined only up to sign. -/
  classical
  let V := EuclideanSpace ℂ (Fin 1)
  let P (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let := exteriorAlgebra_finiteDimensional (V := V)
  let := exteriorAlgebraNormedAddCommGroup (V := V)
  let := exteriorAlgebraNormedSpace (V := V)
  let := FiniteDimensional.proper ℂ V
  let (i : ZMod 2) := modelTopology (P i) (Bundle.Trivial V (P i))
  let (i : ZMod 2) := isFiniteRank_model (P i) (Bundle.Trivial V (P i))
  let := trivialTopology (X := ℂ) 1
  let := isFiniteRank_trivial (X := ℂ) 1
  -- The original even and odd exterior bases are the vacuum and the unique vector.
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
  let e := (PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℂ)).trans
    (Homeomorph.funUnique (Fin 1) ℂ)
  let f : C(ℂ, V) := ⟨e.symm, e.symm.continuous⟩
  have hf : IsProperMap f := e.symm.isProperMap
  have hvector (z : ℂ) : f z = z • v₀ := by
    ext k
    fin_cases k
    change z = z * 1
    exact (mul_one z).symm
  have hsymbol (z : ℂ) (a : Fin 1 → ℂ) :
      cliffordSymbol (f z) (d₀.symm a : ExteriorAlgebra ℂ V) =
        (d₁.symm (z • a) : ExteriorAlgebra ℂ V) := by
    rw [hd₀, hd₁, map_smul]
    have hvacuum : cliffordSymbol (f z) 1 = ExteriorAlgebra.ι ℂ (f z) := by
      simp [cliffordSymbol, exteriorMultiplication, contraction]
    rw [hvacuum, hvector, map_smul]
    simp [smul_smul, mul_comm]
  -- Fixed parity coordinates define continuous bundle isomorphisms after the actual base change.
  let j (i : ZMod 2) (d : P i ≃ₗ[ℂ] (Fin 1 → ℂ)) :
      Iso ((f : ℂ → V) *ᵖ (Bundle.Trivial V (P i)))
        (Bundle.Trivial ℂ (Fin 1 → ℂ)) := by
    let hV : TotalSpace Unit (Bundle.Trivial V (P i)) ≃ₜ V × P i :=
      (unitTotalHomeomorph (P i) (Bundle.Trivial V (P i))).trans
        (Bundle.Trivial.homeomorphProd V (P i))
    refine { linearEquiv := fun _ ↦ d, continuous_total := ?_, continuous_symm := ?_ }
    · have hsource := hV.continuous.comp
        (Pullback.continuous_lift Unit (Bundle.Trivial V (P i)) f)
      have hbase := Pullback.continuous_proj Unit (Bundle.Trivial V (P i)) f
      apply continuous_induced_rng.mpr
      exact hbase.prodMk (d.continuous_of_finiteDimensional.comp hsource.snd)
    · rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial V (P i))
        f).continuous_iff]
      have hW : Continuous (fun z : TotalSpace Unit
          (Bundle.Trivial ℂ (Fin 1 → ℂ)) ↦ (z.proj, z.snd)) := continuous_induced_dom
      exact hW.fst.prodMk (hV.symm.continuous.comp
        ((f.continuous.comp hW.fst).prodMk
          (d.symm.continuous_of_finiteDimensional.comp hW.snd)))
  let : IsFiniteRank ((f : ℂ → V) *ᵖ (Bundle.Trivial V (P 0))) := isFiniteRank_pullback f
  let : IsFiniteRank ((f : ℂ → V) *ᵖ (Bundle.Trivial V (P 1))) := isFiniteRank_pullback f
  let a := exteriorBottTriple V
  let b := bottLineTriple
  let d := (a.pullback f hf).congr (j 0 d₀) (j 1 d₁)
  have hd : d.control ⊆ ({0} : Set ℂ) := by
    intro z hz
    change f z = 0 at hz
    have h := congrArg e hz
    change z = 0 at h
    exact h
  have hb : b.control ⊆ ({0} : Set ℂ) := Set.Subset.refl _
  have hboundary (z : (d.controlᶜ : Set ℂ)) (v : Fin 1 → ℂ) :
      d.boundary.linearEquiv z v = z.val • v := by
    have hc := (a.pullback f hf).congr_apply (j 0 d₀) (j 1 d₁) z v
    change d.boundary.linearEquiv z v =
      d₁ ((a.boundary.pullback f).linearEquiv z (d₀.symm v)) at hc
    refine hc.trans ?_
    have hp := congrArg d₁ (a.boundary.pullback_apply f z (d₀.symm v))
    refine hp.trans ?_
    apply d₁.symm.injective
    exact (d₁.symm_apply_apply _).trans (Subtype.ext (hsymbol z.val v))
  -- Both enlarged triples have the same zero control and the same multiplication-by-z boundary.
  have hsame : (d.enlarge {0} isCompact_singleton hd).boundary =
      (b.enlarge {0} isCompact_singleton hb).boundary := by
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    have hleft : (d.enlarge {0} isCompact_singleton hd).boundary.linearEquiv z v =
        z.val • (v : Fin 1 → ℂ) :=
      (d.enlarge_apply {0} isCompact_singleton hd z v).trans (hboundary _ _)
    have hright : (b.enlarge {0} isCompact_singleton hb).boundary.linearEquiv z v =
        z.val • (v : Fin 1 → ℂ) := b.enlarge_apply {0} isCompact_singleton hb z v
    exact hleft.trans hright.symm
  have hhom : d.Homotopic b := by
    refine ⟨{0}, isCompact_singleton, hd, hb, ?_⟩
    rw [hsame]
    exact IsoHomotopy.nonempty_refl _
  have htransport : compactSupportKZeroHomeomorph (Homeomorph.funUnique (Fin 1) ℂ)
      (exteriorBottEuclideanClass 1) = compactSupportKZeroHomeomorph e (exteriorBottClass V) := by
    change compactSupportKZeroPullback
        ⟨(Homeomorph.funUnique (Fin 1) ℂ).symm, _⟩ _
        (compactSupportKZeroPullback
          ⟨(PiLp.homeomorph 2 (fun _ : Fin 1 ↦ ℂ)).symm, _⟩ _ (exteriorBottClass V)) = _
    exact (DFunLike.congr_fun (compactSupportKZeroPullback_comp _ _ _ _)
      (exteriorBottClass V)).symm
  calc
    _ = compactSupportKZeroHomeomorph e (exteriorBottClass V) := htransport
    _ = (a.pullback f hf).compactSupportClass := (a.compactSupportClass_pullback f hf).symm
    _ = d.compactSupportClass :=
      ((a.pullback f hf).compactSupportClass_congr (j 0 d₀) (j 1 d₁)).symm
    _ = bottLineClass := d.compactSupportClass_eq_of_homotopic b hhom

/-- KA IV.1.7 on vector spaces: the actual exterior class multiplies under ordered direct sum. -/
theorem exteriorBottEuclideanClass_add (m n : ℕ) :
    compactSupportKZeroHomeomorph (Fin.appendHomeomorph (X := ℂ) m n)
      (compactSupportKZeroExternalProduct
        (exteriorBottEuclideanClass m) (exteriorBottEuclideanClass n)) =
      exteriorBottEuclideanClass (m + n) := by
  /- Stage 1: apply equivariantExteriorBottClass_prod to the trivial one-point
  group. Its graded tensor comparison interpolates reciprocal cutoffs on one
  product control, changes the odd-odd source sign, and uses ordered exterior
  multiplication to identify the SG parity symbols.
  Stage 2: forget this same equivariant equality. The existing proper-pullback
  and external-product forgetful laws, followed by the original support-group
  comparison, identify the ordinary compact-support classes on the Hilbert sum.
  Stage 3: the ordered Hilbert-sum isometry has precisely the coordinate map
  Fin.appendHomeomorph m n. Product naturality and unitary exterior naturality
  transport the same equality to the displayed finite coordinates. The argument
  retains negative contraction throughout, includes either zero-dimensional
  summand and does not invoke the general bundle Thom theorem. -/
  classical
  let V := EuclideanSpace ℂ (Fin m)
  let W := EuclideanSpace ℂ (Fin n)
  let S := WithLp 2 (V × W)
  let U := EuclideanSpace ℂ (Fin (m + n))
  let := FiniteDimensional.proper ℂ V
  let := FiniteDimensional.proper ℂ W
  let := FiniteDimensional.proper ℂ S
  let := FiniteDimensional.proper ℂ U
  let : ContinuousSMul PUnit.{1} V := ⟨continuous_snd⟩
  let : ContinuousSMul PUnit.{1} W := ⟨continuous_snd⟩
  let : ContinuousSMul PUnit.{1} S := ⟨continuous_snd⟩
  have hV (g : PUnit.{1}) (x y : V) : inner ℂ (g • x) (g • y) = inner ℂ x y := rfl
  have hW (g : PUnit.{1}) (x y : W) : inner ℂ (g • x) (g • y) = inner ℂ x y := rfl
  let h := (WithLp.prodContinuousLinearEquiv 2 ℂ V W).toHomeomorph
  -- Forget only after the equivariant homotopy has compared the original products.
  have hproduct := equivariantExteriorBottClass_prod hV hW
  have hforgot := congrArg (fun a ↦ ComplexBundle.supportTripleKZeroToCompactSupport
    (ComplexBundle.equivariantSupportTripleKZeroForget a)) hproduct
  rw [ComplexBundle.equivariantSupportKZeroExternalProduct_forget,
    equivariantExteriorBottClass_forget, equivariantExteriorBottClass_forget] at hforgot
  have hpull (a : ComplexBundle.EquivariantSupportTripleKZero PUnit.{1} S) :=
    DFunLike.congr_fun
    (ComplexBundle.equivariantSupportTripleKZeroForget_pullback (G := PUnit.{1})
      (⟨h.symm, h.symm.continuous⟩ : C(V × W, S)) (fun _ _ ↦ rfl)
      h.symm.isProperMap) a
  simp only [AddMonoidHom.comp_apply] at hpull
  erw [hpull] at hforgot
  have hcompact (a : ComplexBundle.SupportTripleKZero S) := DFunLike.congr_fun
    (ComplexBundle.supportTripleKZeroToCompactSupport_pullback
      (⟨h.symm, h.symm.continuous⟩ : C(V × W, S)) h.symm.isProperMap) a
  simp only [AddMonoidHom.comp_apply] at hcompact
  erw [hcompact, equivariantExteriorBottClass_forget] at hforgot
  change compactSupportKZeroHomeomorph h (exteriorBottClass S) =
    compactSupportKZeroExternalProduct (exteriorBottClass V) (exteriorBottClass W) at hforgot
  -- The ordered Hilbert sum isometry induces exactly the prescribed append coordinates.
  let k : S ≃ₗᵢ[ℂ] U :=
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2 (fun _ : Fin m ⊕ Fin n ↦ ℂ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ finSumFinEquiv.symm).symm
  let v := PiLp.homeomorph 2 (fun _ : Fin m ↦ ℂ)
  let w := PiLp.homeomorph 2 (fun _ : Fin n ↦ ℂ)
  let u := PiLp.homeomorph 2 (fun _ : Fin (m + n) ↦ ℂ)
  have hcoords : h.trans ((v.prodCongr w).trans (Fin.appendHomeomorph m n)) =
      k.toHomeomorph.trans u := by
    ext z i
    simp only [k, LinearIsometryEquiv.piLpCongrLeft_symm, Equiv.symm_symm]
    change Fin.append (fun j ↦ (WithLp.ofLp z).1 j) (fun j ↦ (WithLp.ofLp z).2 j) i =
      Sum.elim (fun j ↦ (WithLp.ofLp z).1 j) (fun j ↦ (WithLp.ofLp z).2 j)
        (finSumFinEquiv.symm i)
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  have hcomp {A B C : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
      [TopologicalSpace C] [LocallyCompactSpace C] [T2Space C]
      (e : A ≃ₜ B) (f : B ≃ₜ C) (a : CompactSupportKZero A) :
      compactSupportKZeroHomeomorph f (compactSupportKZeroHomeomorph e a) =
        compactSupportKZeroHomeomorph (e.trans f) a := by
    unfold compactSupportKZeroHomeomorph
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  change compactSupportKZeroHomeomorph (Fin.appendHomeomorph m n)
    (compactSupportKZeroExternalProduct
      (compactSupportKZeroHomeomorph v (exteriorBottClass V))
      (compactSupportKZeroHomeomorph w (exteriorBottClass W))) =
    compactSupportKZeroHomeomorph u (exteriorBottClass U)
  rw [← compactSupportKZeroExternalProduct_homeomorph, ← hforgot, hcomp, hcomp,
    hcoords, ← hcomp, exteriorBottClass_natural]

/-- The actual exterior-symbol class equals the specified finite external power of the line class.
-/
theorem exteriorBottEuclideanClass_eq_bottEuclideanClass (n : ℕ) :
    exteriorBottEuclideanClass n = bottEuclideanClass n := by
  /- Induct on n. The base case is the actual rank-one point normalization.
  For the successor apply the direct-sum formula with second block of length
  one. Its one-dimensional factor becomes the original line class under
  the specified coordinate evaluation. Product naturality then identifies
  the block-append map with complexFinSuccHomeomorph n, exactly the map in
  the recursive definition of bottEuclideanClass. Substitute the induction
  hypothesis and obtain equality of the concrete classes, without relying
  on cyclicity of Kc(ℂⁿ) or choosing the sign of a generator. -/
  have hcomp {A B C : Type} [TopologicalSpace A] [LocallyCompactSpace A] [T2Space A]
      [TopologicalSpace B] [LocallyCompactSpace B] [T2Space B]
      [TopologicalSpace C] [LocallyCompactSpace C] [T2Space C]
      (e : A ≃ₜ B) (f : B ≃ₜ C) (a : CompactSupportKZero A) :
      compactSupportKZeroHomeomorph f (compactSupportKZeroHomeomorph e a) =
        compactSupportKZeroHomeomorph (e.trans f) a := by
    unfold compactSupportKZeroHomeomorph
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    rfl
  induction n with
  | zero => exact exteriorBottEuclideanClass_zero
  | succ n ih =>
    -- Insert the same one-dimensional coordinate evaluation into the original product.
    let e := Homeomorph.funUnique (Fin 1) ℂ
    have hp := compactSupportKZeroExternalProduct_homeomorph
      (Homeomorph.refl (Fin n → ℂ)) e (exteriorBottEuclideanClass n)
      (exteriorBottEuclideanClass 1)
    have hid : compactSupportKZeroHomeomorph (Homeomorph.refl (Fin n → ℂ))
        (exteriorBottEuclideanClass n) = exteriorBottEuclideanClass n := by
      change compactSupportKZeroPullback (ContinuousMap.id _) isProperMap_id _ = _
      rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
    rw [hid, exteriorBottEuclideanClass_one, ih] at hp
    -- Evaluation followed by the recursive successor map is the original block append map.
    have hcoords : ((Homeomorph.refl (Fin n → ℂ)).prodCongr e).trans
        (complexFinSuccHomeomorph n) = Fin.appendHomeomorph (X := ℂ) n 1 := by
      ext z i
      change Fin.append z.1 (e.symm (e z.2)) i = Fin.append z.1 z.2 i
      rw [e.symm_apply_apply]
    calc
      exteriorBottEuclideanClass (n + 1) =
          compactSupportKZeroHomeomorph (Fin.appendHomeomorph n 1)
            (compactSupportKZeroExternalProduct
              (exteriorBottEuclideanClass n) (exteriorBottEuclideanClass 1)) :=
        (exteriorBottEuclideanClass_add n 1).symm
      _ = compactSupportKZeroHomeomorph (complexFinSuccHomeomorph n)
          (compactSupportKZeroExternalProduct (bottEuclideanClass n) bottLineClass) := by
        rw [← hp, hcomp, hcoords, ih]
      _ = bottEuclideanClass (n + 1) := rfl

/-- The actual exterior triple has positive coordinate under the pre-existing integer normalization.
-/
theorem bottEuclideanClassEquivInt_exteriorBottEuclideanClass (n : ℕ) :
    bottEuclideanClassEquivInt n (exteriorBottEuclideanClass n) = 1 := by
  /- Substitute the concrete class comparison into the already fixed
  integer coordinate. The original iterated line class maps to +1 by its
  normalization theorem. This is a consequence of the geometric comparison;
  it is not a normalization used to define or select the exterior class. -/
  rw [exteriorBottEuclideanClass_eq_bottEuclideanClass,
    bottEuclideanClassEquivInt_bottEuclideanClass]

/-- Complex Bott periodicity for external product with the actual finite Hermitian exterior class.
-/
theorem exteriorBottExternalProduct_bijective (X V : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] :
    letI := FiniteDimensional.proper ℂ V
    Function.Bijective (compactSupportKZeroExternalProduct.flip (exteriorBottClass V) :
      CompactSupportKZero X →+ CompactSupportKZero (X × V)) := by
  /- Stage 1: an orthonormal basis gives a complex linear isometry from V
  to EuclideanSpace ℂ (Fin (finrank ℂ V)). Unitary naturality of the actual
  exterior triple transports its class along that same isometry.
  Stage 2: pass to the actual finite-coordinate homeomorphism and apply the
  exterior/iterated-class comparison. Existing finite-dimensional Bott
  periodicity gives bijectivity of external product with that class.
  Stage 3: product naturality under the specified base homeomorphism
  identifies this map with the displayed external product after transport
  by id_X times the coordinate map. Transport is an equivalence, so the
  displayed map itself is bijective. Finite-dimensional V is locally
  compact, and X is arbitrary LCH, including empty or disconnected bases.
  The argument includes V=0 and assumes no global bundle Thom theorem. -/
  let := FiniteDimensional.proper ℂ V
  let n := Module.finrank ℂ V
  let q : V ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) := (stdOrthonormalBasis ℂ V).repr
  let f := PiLp.homeomorph 2 (fun _ : Fin n ↦ ℂ)
  let e := q.toHomeomorph.trans f
  -- The very same unitary exterior symbol becomes the existing finite-coordinate class.
  have hclass : compactSupportKZeroHomeomorph e (exteriorBottClass V) =
      bottEuclideanClass n := by
    have hcomp : compactSupportKZeroHomeomorph e (exteriorBottClass V) =
        compactSupportKZeroHomeomorph f
          (compactSupportKZeroHomeomorph q.toHomeomorph (exteriorBottClass V)) := by
      exact DFunLike.congr_fun (compactSupportKZeroPullback_comp
        ⟨f.symm, f.symm.continuous⟩
        ⟨q.toHomeomorph.symm, q.toHomeomorph.symm.continuous⟩
        f.symm.isProperMap q.toHomeomorph.symm.isProperMap) (exteriorBottClass V)
    rw [hcomp, exteriorBottClass_natural]
    exact exteriorBottEuclideanClass_eq_bottEuclideanClass n
  let E := compactSupportKZeroHomeomorphEquiv ((Homeomorph.refl X).prodCongr e)
  have hsquare (a : CompactSupportKZero X) :
      E (compactSupportKZeroExternalProduct a (exteriorBottClass V)) =
        bottEuclideanExternalProduct n a := by
    have h := compactSupportKZeroExternalProduct_homeomorph (Homeomorph.refl X) e
      a (exteriorBottClass V)
    rw [hclass] at h
    have hid : compactSupportKZeroHomeomorph (Homeomorph.refl X) a = a := by
      change compactSupportKZeroPullback (ContinuousMap.id X) isProperMap_id a = a
      rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
    rw [hid] at h
    exact h
  have hB := bottEuclideanExternalProduct_bijective X n
  constructor
  · -- The fixed coordinate equivalence and finite Bott injectivity detect equality.
    intro a b hab
    apply hB.injective
    exact (hsquare a).symm.trans ((congrArg E hab).trans (hsquare b))
  · intro b
    obtain ⟨a, ha⟩ := hB.surjective (E b)
    refine ⟨a, E.injective ?_⟩
    exact (hsquare a).trans ha

/-- The Bott equivalence keeps external product with the actual exterior triple as forward map. -/
def exteriorBottEquiv (X V : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] :
    letI := FiniteDimensional.proper ℂ V
    CompactSupportKZero X ≃+ CompactSupportKZero (X × V) :=
  letI := FiniteDimensional.proper ℂ V
  AddEquiv.ofBijective (compactSupportKZeroExternalProduct.flip (exteriorBottClass V))
    (exteriorBottExternalProduct_bijective X V)

end AtiyahSinger
