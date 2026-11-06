/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import AtiyahSinger.Topology.EquivariantKExternalProduct
public import AtiyahSinger.Topology.EquivariantRepresentationNaturality
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod

/-!
# Ordered direct sums and the actual equivariant Bott external product

Public module ID: M1758.

ASI I, p.494, equation (2.6), uses the ordered graded exterior identification
for V followed by W. The map below is literally multiplication of the two
exterior inclusion maps, on the original tensor carrier. Its target is the
native Hilbert direct sum `WithLp 2 (V × W)`, not the maximum-norm product.

The Bott comparison pulls this exact sum's original SG class back along the
standard continuous complex-linear identification from V times W. The other
side is the existing equivariant support external product with its reciprocal
cutoffs. The proof records their common-control normalization and the sign on
the odd-odd source summand; it does not equate positive reciprocal matrices
with SG's negative-square graded matrix without that comparison.

The forward Bott-map formula retains the full representation-ring product.
Compactness of the group is inherited from the existing external-product API;
neither a Lie atlas nor Bott bijectivity is needed. Both representation spaces
may have dimension zero. The ordered exterior tensor identification and its full
equivariant graded symbol formula are proved below. The support-class product
comparison and its full-coefficient consequence are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle
open scoped TensorProduct

set_option maxSynthPendingDepth 25

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]
  [DistribMulAction G W] [SMulCommClass G ℂ W] [ContinuousSMul G W]

/-- The native diagonal action is continuous in the actual Hilbert direct-sum topology. -/
instance equivariantWithLpProdContinuousSMul : ContinuousSMul G (WithLp 2 (V × W)) where
  continuous_smul := by
    let e := WithLp.prodContinuousLinearEquiv 2 ℂ V W
    have h : Continuous (fun z : G × WithLp 2 (V × W) ↦ z.1 • e z.2) :=
      continuous_fst.smul (e.continuous.comp continuous_snd)
    exact (e.symm.continuous.comp h).congr (fun z ↦ by rfl)

/-- The ordered exterior tensor map multiplies the actual two inclusion maps, V before W. -/
def exteriorTensorToSum :
    ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W →ₗ[ℂ]
      ExteriorAlgebra ℂ (WithLp 2 (V × W)) :=
  let e := (WithLp.linearEquiv 2 ℂ (V × W)).symm
  TensorProduct.lift ((LinearMap.mul ℂ (ExteriorAlgebra ℂ (WithLp 2 (V × W)))).compl₁₂
    (ExteriorAlgebra.map (e.toLinearMap.comp (LinearMap.inl ℂ V W))).toLinearMap
    (ExteriorAlgebra.map (e.toLinearMap.comp (LinearMap.inr ℂ V W))).toLinearMap)

-- Keep the original section hypotheses although this algebraic proof needs fewer.
set_option linter.unusedSectionVars false in
/-- The actual exterior tensor map is an equivariant graded isomorphism intertwining SG symbols. -/
theorem exteriorTensorToSum_properties :
    Function.Bijective (exteriorTensorToSum (V := V) (W := W)) ∧
    (∀ (g : G) (a : ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W),
      exteriorTensorToSum
        (TensorProduct.map
          (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)).toLinearMap
          (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ W g)).toLinearMap a) =
        ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ (WithLp 2 (V × W)) g)
          (exteriorTensorToSum a)) ∧
    (∀ (i j : ZMod 2) (a : ExteriorAlgebra ℂ V) (b : ExteriorAlgebra ℂ W),
      a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i →
      b ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) j →
      exteriorTensorToSum (a ⊗ₜ[ℂ] b) ∈
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (WithLp 2 (V × W))) (i + j)) ∧
    (∀ (v : V) (w : W) (a : ExteriorAlgebra ℂ V) (b : ExteriorAlgebra ℂ W),
      cliffordSymbol (WithLp.toLp 2 (v, w)) (exteriorTensorToSum (a ⊗ₜ[ℂ] b)) =
        exteriorTensorToSum
          ((cliffordSymbol v a) ⊗ₜ[ℂ] b +
            (CliffordAlgebra.involute (Q := (0 : QuadraticForm ℂ V)) a) ⊗ₜ[ℂ]
              (cliffordSymbol w b))) := by
  /- Stage 1: the displayed map sends a tensor b to exterior_inl(a) wedge
  exterior_inr(b), in that order. The standard exterior basis of the sum is
  obtained by first taking the ordered V vectors and then the W vectors.
  Hence this specified map is bijective. Equivalently specialize mathlib's
  graded Clifford prodEquiv to the two zero forms, then use the actual
  WithLp linear identification. No arbitrary equal-dimensional equivalence
  is selected and no ungraded algebra-product assertion is being made.
  Stage 2: both inclusion maps commute with the original diagonal action.
  Functoriality of ExteriorAlgebra.map gives exactly the stated equivariance
  on pure tensors and then on all tensors. Multiplication adds exterior
  degrees, proving the same parity statement in the fixed evenOdd submodules.
  Stage 3: wedge by (v,w) is wedge(v) tensor one plus the first-factor
  grading involution tensor wedge(w). Because the WithLp inner product is
  the orthogonal sum of the original two metrics, contraction satisfies the
  identical graded Leibniz formula. Subtract contraction from wedge in both
  factors. This gives the displayed exact SG intertwining identity, with
  its negative square and its actual involute sign, in both parities. -/
  classical
  let S := WithLp 2 (V × W)
  let e : (V × W) ≃ₗ[ℂ] S := (WithLp.linearEquiv 2 ℂ (V × W)).symm
  let f : V →ₗ[ℂ] S := e.toLinearMap.comp (LinearMap.inl ℂ V W)
  let k : W →ₗ[ℂ] S := e.toLinearMap.comp (LinearMap.inr ℂ V W)
  let F := ExteriorAlgebra.map f
  let K := ExteriorAlgebra.map k
  have happly (a : ExteriorAlgebra ℂ V) (b : ExteriorAlgebra ℂ W) :
      exteriorTensorToSum (a ⊗ₜ[ℂ] b) = F a * K b := rfl
  -- The specified multiplication map is the underlying map of the graded Clifford equivalence.
  let q : ((0 : QuadraticForm ℂ V).prod (0 : QuadraticForm ℂ W)).IsometryEquiv
      (0 : QuadraticForm ℂ S) :=
    { e with map_app' := fun x ↦ by simp [QuadraticMap.prod_apply] }
  let B : ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W ≃ₗ[ℂ] ExteriorAlgebra ℂ S :=
    (GradedTensorProduct.of ℂ (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W))).trans
      ((CliffordAlgebra.prodEquiv (0 : QuadraticForm ℂ V)
        (0 : QuadraticForm ℂ W)).symm.toLinearEquiv.trans
          (CliffordAlgebra.equivOfIsometry q).toLinearEquiv)
  have hF : (CliffordAlgebra.map q.toIsometry).comp
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl (0 : QuadraticForm ℂ V)
        (0 : QuadraticForm ℂ W))) = F := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [F, f, q, e]
    rfl
  have hK : (CliffordAlgebra.map q.toIsometry).comp
      (CliffordAlgebra.map (QuadraticMap.Isometry.inr (0 : QuadraticForm ℂ V)
        (0 : QuadraticForm ℂ W))) = K := by
    apply ExteriorAlgebra.hom_ext
    ext w
    simp [K, k, q, e]
    rfl
  have hB : B.toLinearMap = exteriorTensorToSum (V := V) (W := W) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change CliffordAlgebra.map q.toIsometry
      (CliffordAlgebra.toProd (0 : QuadraticForm ℂ V) (0 : QuadraticForm ℂ W)
        (a ᵍ⊗ₜ b)) = F a * K b
    simp only [CliffordAlgebra.toProd, GradedTensorProduct.lift_tmul, map_mul]
    exact congrArg₂ (· * ·) (AlgHom.congr_fun hF a) (AlgHom.congr_fun hK b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hB]
    exact B.bijective
  · intro g a
    have hFcomm : (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ S g)).comp F =
        F.comp (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)) := by
      apply ExteriorAlgebra.hom_ext
      ext v
      simp only [F, AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.coe_toLinearMap,
        Function.comp_apply, ExteriorAlgebra.map_apply_ι, DistribSMul.toLinearMap_apply]
      congr 1
      apply WithLp.ofLp_injective 2
      change (g • v, g • (0 : W)) = (g • v, 0)
      rw [smul_zero]
    have hKcomm : (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ S g)).comp K =
        K.comp (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ W g)) := by
      apply ExteriorAlgebra.hom_ext
      ext w
      simp only [K, AlgHom.comp_toLinearMap, LinearMap.coe_comp, AlgHom.coe_toLinearMap,
        Function.comp_apply, ExteriorAlgebra.map_apply_ι, DistribSMul.toLinearMap_apply]
      congr 1
      apply WithLp.ofLp_injective 2
      change (g • (0 : V), g • w) = (0, g • w)
      rw [smul_zero]
    -- Naturality holds on pure tensors and then on their linear span.
    induction a using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [TensorProduct.map_tmul, happly, map_mul]
      exact congrArg₂ (· * ·) (AlgHom.congr_fun hFcomm a).symm
        (AlgHom.congr_fun hKcomm b).symm
  · intro i j a b ha hb
    -- Each inclusion preserves degree, and multiplication adds the original parities.
    have hgraded {M N : Type} [AddCommGroup M] [Module ℂ M]
        [AddCommGroup N] [Module ℂ N] (l : M →ₗ[ℂ] N)
        (s : ZMod 2) (x : ExteriorAlgebra ℂ M)
        (hx : x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ M) s) :
        ExteriorAlgebra.map l x ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ N) s := by
      have hrange : (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ M))).map
          (ExteriorAlgebra.map l).toLinearMap ≤
            LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ N)) := by
        rintro _ ⟨y, ⟨v, rfl⟩, rfl⟩
        exact ⟨l v, (ExteriorAlgebra.map_apply_ι l v).symm⟩
      have hparity : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ M) s).map
          (ExteriorAlgebra.map l).toLinearMap ≤
            CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ N) s := by
        simp only [CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
        exact iSup_mono (fun n ↦ pow_le_pow_left' hrange n.val)
      exact (Submodule.map_le_iff_le_comap.mp hparity) hx
    rw [happly]
    exact SetLike.mul_mem_graded (hgraded f i a ha) (hgraded k j b hb)
  · intro v w a b
    -- Contraction is natural for the pulled covector, before identifying the two metrics.
    have hcontractMap {M N : Type} [AddCommGroup M] [Module ℂ M]
        [AddCommGroup N] [Module ℂ N] (l : M →ₗ[ℂ] N)
        (d : Module.Dual ℂ N) (x : ExteriorAlgebra ℂ M) :
        CliffordAlgebra.contractLeft d (ExteriorAlgebra.map l x) =
          ExteriorAlgebra.map l (CliffordAlgebra.contractLeft (d.comp l) x) := by
      induction x using CliffordAlgebra.left_induction with
      | algebraMap r => simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap,
          map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | ι_mul x m hx =>
        rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
          CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
          ExteriorAlgebra.map_apply_ι, hx]
        rfl
    -- The graded Leibniz rule comes from the original contraction recurrence on vectors.
    have hcontractMul (d : Module.Dual ℂ S) (x y : ExteriorAlgebra ℂ S) :
        CliffordAlgebra.contractLeft d (x * y) =
          CliffordAlgebra.contractLeft d x * y +
            CliffordAlgebra.involute x * CliffordAlgebra.contractLeft d y := by
      induction x using CliffordAlgebra.left_induction with
      | algebraMap r =>
        simp only [CliffordAlgebra.contractLeft_algebraMap, zero_mul, zero_add,
          AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap_mul]
      | add x z hx hz =>
        simp only [add_mul, map_add, hx, hz]
        abel
      | ι_mul x m hx =>
        rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
          CliffordAlgebra.contractLeft_ι_mul, map_mul CliffordAlgebra.involute,
          CliffordAlgebra.involute_ι, hx]
        simp only [sub_mul, smul_mul_assoc, mul_add, neg_mul, mul_assoc]
        abel
    have hinvolute : CliffordAlgebra.involute.comp F =
        F.comp CliffordAlgebra.involute := by
      apply ExteriorAlgebra.hom_ext
      ext x
      simp [F]
    have hinvolute_apply : CliffordAlgebra.involute (F a) =
        F (CliffordAlgebra.involute a) := AlgHom.congr_fun hinvolute a
    -- Moving a vector past a multivector introduces exactly the parity involution.
    have hcomm (x : S) (y : ExteriorAlgebra ℂ S) :
        ExteriorAlgebra.ι ℂ x * y = CliffordAlgebra.involute y * ExteriorAlgebra.ι ℂ x := by
      induction y using CliffordAlgebra.left_induction with
      | algebraMap r =>
        rw [AlgHom.commutes]
        exact (Algebra.commutes r (ExteriorAlgebra.ι ℂ x)).symm
      | add y z hy hz => simp only [mul_add, map_add, add_mul, hy, hz]
      | ι_mul y z hy =>
        have hanti := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) x z)
        rw [← mul_assoc, hanti, neg_mul, mul_assoc, hy, map_mul,
          CliffordAlgebra.involute_ι]
        simp only [neg_mul, mul_assoc]
    let s : S := WithLp.toLp 2 (v, w)
    have hsplit : s = f v + k w := by
      apply WithLp.ofLp_injective 2
      change (v, w) = (v + 0, 0 + w)
      simp
    have hleft : (innerₛₗ ℂ s).comp f = innerₛₗ ℂ v := by
      ext x
      change inner ℂ v x + inner ℂ w 0 = inner ℂ v x
      simp
    have hright : (innerₛₗ ℂ s).comp k = innerₛₗ ℂ w := by
      ext y
      change inner ℂ v 0 + inner ℂ w y = inner ℂ w y
      simp
    have hcontractF : contraction s (F a) = F (contraction v a) := by
      exact (hcontractMap f (innerₛₗ ℂ s) a).trans (congrArg F (by rw [hleft]; rfl))
    have hcontractK : contraction s (K b) = K (contraction w b) := by
      exact (hcontractMap k (innerₛₗ ℂ s) b).trans (congrArg K (by rw [hright]; rfl))
    have hwedge : ExteriorAlgebra.ι ℂ s * (F a * K b) =
        F (exteriorMultiplication v a) * K b +
          F (CliffordAlgebra.involute a) * K (exteriorMultiplication w b) := by
      change ExteriorAlgebra.ι ℂ s * (F a * K b) =
        F (ExteriorAlgebra.ι ℂ v * a) * K b +
          F (CliffordAlgebra.involute a) * K (ExteriorAlgebra.ι ℂ w * b)
      rw [hsplit, map_add, add_mul, ← mul_assoc (ExteriorAlgebra.ι ℂ (k w)), hcomm (k w) (F a),
        hinvolute_apply, map_mul F, map_mul K,
        ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
      simp only [mul_assoc]
    -- Subtract the two graded identities, retaining SG's wedge-minus-contraction convention.
    rw [map_add, happly, happly, happly]
    change exteriorMultiplication s (F a * K b) - contraction s (F a * K b) =
      F (exteriorMultiplication v a - contraction v a) * K b +
        F (CliffordAlgebra.involute a) * K (exteriorMultiplication w b - contraction w b)
    change ExteriorAlgebra.ι ℂ s * (F a * K b) -
      CliffordAlgebra.contractLeft (innerₛₗ ℂ s) (F a * K b) = _
    rw [hwedge, hcontractMul]
    change _ - (contraction s (F a) * K b +
      CliffordAlgebra.involute (F a) * contraction s (K b)) = _
    rw [hcontractF, hcontractK, hinvolute_apply, map_sub F, map_sub K]
    noncomm_ring

variable (hV : ∀ (g : G) (u v : V), inner ℂ (g • u) (g • v) = inner ℂ u v)
  (hW : ∀ (g : G) (u v : W), inner ℂ (g • u) (g • v) = inner ℂ u v)
  [CompactSpace G]

attribute [local instance] ComplexBundle.sumTopology ComplexBundle.isFiniteRank_sum
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  ComplexBundle.isFiniteRank_pullback ComplexBundle.sectionModule
  exteriorAlgebra_finiteDimensional in
open Bundle in
open scoped unitInterval in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
-- The original tensor, pullback and model bundle topologies are retained throughout.
/-- The original Bott class of the orthogonal sum is the specified equivariant external product. -/
theorem equivariantExteriorBottClass_prod :
    letI := FiniteDimensional.proper ℂ V
    letI := FiniteDimensional.proper ℂ W
    let hsum : ∀ (g : G) (u v : WithLp 2 (V × W)),
        inner ℂ (g • u) (g • v) = inner ℂ u v := fun g u v ↦ by
      exact congrArg₂ (fun a b : ℂ ↦ a + b)
        (hV g (WithLp.ofLp u).1 (WithLp.ofLp v).1)
        (hW g (WithLp.ofLp u).2 (WithLp.ofLp v).2)
    let e := (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm
    equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩
        (fun _ _ ↦ rfl) e.toHomeomorph.isProperMap
        (equivariantExteriorBottClass hsum) =
      equivariantSupportKZeroExternalProduct
        (equivariantExteriorBottClass hV) (equivariantExteriorBottClass hW) := by
  /- Stage 1: choose invariant radial cutoffs rho and tau that vanish on
  neighborhoods of zero and equal one off closed balls L and M. Evaluate
  the existing equivariant external product on these exact original Bott
  triples and cutoffs. Its control is L times M; it is not reduced to zero
  before constructing a common-control homotopy.
  Stage 2: write f and g for the forward and reverse SG blocks in V, so
  gf=fg=-norm(v)^2. The reciprocal cutoff maps are rho*f and
  -rho/norm(v)^2*g, with the quotient extended by zero near zero. Interpolate
  their two scalar coefficients to one: a_t=(1-t)rho+t and
  b_t=(1-t)rho/norm(v)^2+t. The resulting pair is a_t*f and -b_t*g.
  Their composite scalar is a_t*b_t*norm(v)^2, nonnegative everywhere
  and positive off L. Treat W identically. The original reciprocal block
  therefore stays invertible off L times M, with the same continuous
  reciprocal-denominator inverse and the same group actions for all t.
  Stage 3: at the endpoint the pairs are (f_V,-g_V) and (f_W,-g_W).
  Precompose the even source by +1 on even-even and -1 on odd-odd. Its
  resulting even-to-odd matrix has blocks f_V, -g_W, f_W, g_V, exactly
  the SG graded sum from exteriorTensorToSum_properties. This constant
  equivariant bundle isomorphism is the necessary sign comparison between
  the reciprocal positive-square presentation and the negative-square SG
  presentation. Their raw displayed matrices are not asserted equal.
  Stage 4: restrict the actual ordered exterior tensor identification to
  the two parity sums. Its action, boundary and topology comparisons give
  the original exterior Bott triple of WithLp 2 (V times W), pulled back
  by precisely e. That homeomorphism sends (v,w) to its original Hilbert
  sum vector and zero to zero. Enlarge its zero control to L times M.
  The same equivariant homotopy and isomorphism relations prove the claimed
  equality in the original support group, without forgetting the action,
  using Bott bijectivity, or assuming either rank positive. -/
  classical
  have hParityTensor :
      let PV := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
      let PW := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
      let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (WithLp 2 (V × W)))
      ∃ L₀ : ((PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) ≃ₗ[ℂ] PS 0,
        ∃ L₁ : ((PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) ≃ₗ[ℂ] PS 1,
          (∀ z, (L₀ z).val = exteriorTensorToSum
            (TensorProduct.map (PV 0).subtype (PW 0).subtype z.1 +
              TensorProduct.map (PV 1).subtype (PW 1).subtype z.2)) ∧
          ∀ z, (L₁ z).val = exteriorTensorToSum
            (TensorProduct.map (PV 1).subtype (PW 0).subtype z.1 +
              TensorProduct.map (PV 0).subtype (PW 1).subtype z.2) := by
    classical
    let PV := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
    let PW := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
    let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (WithLp 2 (V × W)))
    let T (i j : ZMod 2) : (PV i ⊗[ℂ] PW j) →ₗ[ℂ]
        ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W :=
      TensorProduct.map (PV i).subtype (PW j).subtype
    let F := exteriorTensorToSum (V := V) (W := W)
    let _ : ContinuousSMul PUnit.{1} V :=
      ⟨by simpa using (continuous_snd : Continuous (Prod.snd : PUnit.{1} × V → V))⟩
    let _ : ContinuousSMul PUnit.{1} W :=
      ⟨by simpa using (continuous_snd : Continuous (Prod.snd : PUnit.{1} × W → W))⟩
    have hF := exteriorTensorToSum_properties (G := PUnit.{1}) (V := V) (W := W)
    have hgrade (i j : ZMod 2) (z : PV i ⊗[ℂ] PW j) :
        F (T i j z) ∈ PS (i + j) := by
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' =>
        simpa only [map_add] using (PS (i + j)).add_mem hz hz'
      | tmul a b => exact hF.2.2.1 i j a.val b.val a.property b.property
    let M₀ := F.comp ((T 0 0).coprod (T 1 1))
    let M₁ := F.comp ((T 1 0).coprod (T 0 1))
    have hM₀ (z : (PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) : M₀ z ∈ PS 0 := by
      simpa only [M₀, LinearMap.comp_apply, LinearMap.coprod_apply, map_add] using
        (PS 0).add_mem (hgrade 0 0 z.1) (hgrade 1 1 z.2)
    have hM₁ (z : (PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) : M₁ z ∈ PS 1 := by
      simpa only [M₁, LinearMap.comp_apply, LinearMap.coprod_apply, map_add] using
        (PS 1).add_mem (hgrade 1 0 z.1) (hgrade 0 1 z.2)
    let J₀ := M₀.codRestrict (PS 0) hM₀
    let J₁ := M₁.codRestrict (PS 1) hM₁
    -- Decompose both original factors, distribute their tensor product, and retain its order.
    let dV : (PV 0 × PV 1) ≃ₗ[ℂ] ExteriorAlgebra ℂ V :=
      Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
    let dW : (PW 0 × PW 1) ≃ₗ[ℂ] ExteriorAlgebra ℂ W :=
      Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
    let dS : (PS 0 × PS 1) ≃ₗ[ℂ] ExteriorAlgebra ℂ (WithLp 2 (V × W)) :=
      Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
    let R : (((PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) ×
        ((PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1))) ≃ₗ[ℂ]
          (((PV 0 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) ×
            ((PV 1 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1))) :=
      { toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
        invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    let D := R.trans
      (((TensorProduct.prodRight ℂ ℂ (PV 0) (PW 0) (PW 1)).symm.prodCongr
          (TensorProduct.prodRight ℂ ℂ (PV 1) (PW 0) (PW 1)).symm).trans
        ((TensorProduct.prodLeft ℂ ℂ (PV 0) (PV 1) (PW 0 × PW 1)).symm.trans
          (TensorProduct.congr dV dW)))
    let B := LinearEquiv.ofBijective F hF.1
    have hwhole : dS.toLinearMap.comp (J₀.prodMap J₁) = B.toLinearMap.comp D.toLinearMap := by
      apply LinearMap.prod_ext <;> apply LinearMap.prod_ext <;>
        apply TensorProduct.ext' <;> intro x y
      all_goals
        simp [J₀, J₁, M₀, M₁, T, B, D, R, dV, dW, dS,
          TensorProduct.prodRight, TensorProduct.prodLeft]
    have hjoint : Function.Bijective (J₀.prodMap J₁) := by
      have hcomp := B.bijective.comp D.bijective
      change Function.Bijective (B.toLinearMap.comp D.toLinearMap) at hcomp
      rw [← hwhole] at hcomp
      exact (Function.Bijective.of_comp_iff' dS.bijective (J₀.prodMap J₁)).mp hcomp
    -- The full graded equivalence is block diagonal, so each actual parity map is bijective.
    have h₀ : Function.Bijective J₀ := by
      constructor
      · intro x y h
        have heq : J₀.prodMap J₁ (x, 0) = J₀.prodMap J₁ (y, 0) := Prod.ext h rfl
        exact congrArg Prod.fst (hjoint.injective heq)
      · intro z
        obtain ⟨x, hx⟩ := hjoint.surjective (z, 0)
        exact ⟨x.1, congrArg Prod.fst hx⟩
    have h₁ : Function.Bijective J₁ := by
      constructor
      · intro x y h
        have heq : J₀.prodMap J₁ (0, x) = J₀.prodMap J₁ (0, y) := Prod.ext rfl h
        exact congrArg Prod.snd (hjoint.injective heq)
      · intro z
        obtain ⟨x, hx⟩ := hjoint.surjective (0, z)
        exact ⟨x.2, congrArg Prod.snd hx⟩
    exact ⟨LinearEquiv.ofBijective J₀ h₀, LinearEquiv.ofBijective J₁ h₁,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hWeightedBlock (v : V) (w : W) (a b t : I)
      (hoff : (2 < ‖v‖ ∧ a = 1) ∨ (2 < ‖w‖ ∧ b = 1)) :
      let av : ℝ := (1 - (t : ℝ)) * a + t
      let bv : ℝ := (1 - (t : ℝ)) * a / ‖v‖ ^ 2 + t
      let aw : ℝ := (1 - (t : ℝ)) * b + t
      let bw : ℝ := (1 - (t : ℝ)) * b / ‖w‖ ^ 2 + t
      Function.Bijective (reciprocalTensorSymbol
        ((av : ℂ) • cliffordSymbolParity v 0)
        (-(bv : ℂ) • cliffordSymbolParity v 1)
        ((aw : ℂ) • cliffordSymbolParity w 0)
        (-(bw : ℂ) • cliffordSymbolParity w 1)) := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    dsimp only
    -- The two original SG squares supply the scalar products in either direction.
    have pairSquare {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
        (z : E) (α β : ℝ) :
        (-(β : ℂ) • cliffordSymbolParity z 1).comp
            ((α : ℂ) • cliffordSymbolParity z 0) =
          ((α * β * ‖z‖ ^ 2 : ℝ) : ℂ) • LinearMap.id ∧
        ((α : ℂ) • cliffordSymbolParity z 0).comp
            (-(β : ℂ) • cliffordSymbolParity z 1) =
          ((α * β * ‖z‖ ^ 2 : ℝ) : ℂ) • LinearMap.id := by
      have h₀ (x : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ E) 0) :
          cliffordSymbolParity z 1 (cliffordSymbolParity z 0 x) =
            -(‖z‖ ^ 2 : ℂ) • x := by
        apply Subtype.ext
        exact LinearMap.congr_fun (cliffordSymbol_sq z) x.val
      have h₁ (x : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ E) 1) :
          cliffordSymbolParity z 0 (cliffordSymbolParity z 1 x) =
            -(‖z‖ ^ 2 : ℂ) • x := by
        apply Subtype.ext
        exact LinearMap.congr_fun (cliffordSymbol_sq z) x.val
      constructor <;> apply LinearMap.ext <;> intro x
      · simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
          map_smul, h₀, smul_smul]
        congr 1
        push_cast
        ring
      · simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
          map_smul, h₁, smul_smul]
        congr 1
        push_cast
        ring
    let A (c : I) : ℝ := (1 - (t : ℝ)) * c + t
    let B (c : I) (r : ℝ) : ℝ := (1 - (t : ℝ)) * c / r ^ 2 + t
    let R (c : I) (r : ℝ) : ℝ := A c * B c r * r ^ 2
    have hA (c : I) : 0 ≤ A c :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) c.property.1) t.property.1
    have hB (c : I) (r : ℝ) : 0 ≤ B c r :=
      add_nonneg (div_nonneg
        (mul_nonneg (sub_nonneg.mpr t.property.2) c.property.1) (sq_nonneg r)) t.property.1
    have hR (c : I) (r : ℝ) : 0 ≤ R c r :=
      mul_nonneg (mul_nonneg (hA c) (hB c r)) (sq_nonneg r)
    -- Off a radius-two ball its cutoff is one, so its summand is strictly positive at all times.
    have hpositive (r : ℝ) (hr : 2 < r) : 0 < R 1 r := by
      have hrpos : 0 < r ^ 2 := sq_pos_of_pos (lt_trans (by norm_num) hr)
      have ha : A 1 = 1 := by simp [A]
      dsimp only [R]
      rw [ha, one_mul]
      apply mul_pos _ hrpos
      by_cases ht : (t : ℝ) = 0
      · simp [B, ht, hrpos]
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        exact add_pos_of_nonneg_of_pos
          (div_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (by simp)) hrpos.le) htpos
    have hsum : 0 < R a ‖v‖ + R b ‖w‖ := by
      rcases hoff with ⟨hv, rfl⟩ | ⟨hw, rfl⟩
      · exact add_pos_of_pos_of_nonneg (hpositive ‖v‖ hv) (hR b ‖w‖)
      · exact add_pos_of_nonneg_of_pos (hR a ‖v‖) (hpositive ‖w‖ hw)
    have hne : (R a ‖v‖ : ℂ) + (R b ‖w‖ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hsum)
    exact (reciprocalTensorSymbolEquiv _ _ _ _ (R a ‖v‖) (R b ‖w‖)
      (pairSquare v (A a) (B a ‖v‖)).1 (pairSquare v (A a) (B a ‖v‖)).2
      (pairSquare w (A b) (B b ‖w‖)).1 (pairSquare w (A b) (B b ‖w‖)).2 hne).bijective
  let constantTensorHom {X Y Z E F H : Type}
      [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
      [NormedAddCommGroup H] [NormedSpace ℂ H]
      (f : C(X × Y, Z)) (L : E ⊗[ℂ] F →ₗ[ℂ] H) :
      letI := modelTopology E (Bundle.Trivial X E)
      letI := modelTopology F (Bundle.Trivial Y F)
      letI := modelTopology H (Bundle.Trivial Z H)
      Hom (fun z : X × Y ↦ ((ContinuousMap.fst : C(X × Y, X)) *ᵖ (Bundle.Trivial X E)) z
        ⊗[ℂ] ((ContinuousMap.snd : C(X × Y, Y)) *ᵖ (Bundle.Trivial Y F)) z)
        (f *ᵖ (Bundle.Trivial Z H)) := by
    let := modelTopology E (Bundle.Trivial X E)
    let := modelTopology F (Bundle.Trivial Y F)
    let := modelTopology H (Bundle.Trivial Z H)
    let A := ((ContinuousMap.fst : C(X × Y, X)) *ᵖ (Bundle.Trivial X E))
    let B := ((ContinuousMap.snd : C(X × Y, Y)) *ᵖ (Bundle.Trivial Y F))
    let eE := (unitTotalHomeomorph E (Bundle.Trivial X E)).trans
      (Bundle.Trivial.homeomorphProd X E)
    let eF := (unitTotalHomeomorph F (Bundle.Trivial Y F)).trans
      (Bundle.Trivial.homeomorphProd Y F)
    let eH := (unitTotalHomeomorph H (Bundle.Trivial Z H)).trans
      (Bundle.Trivial.homeomorphProd Z H)
    have hE : Continuous (fun z : TotalSpace Unit A ↦ (z.snd : E)) :=
      eE.continuous.snd.comp
        (Pullback.continuous_lift Unit (Bundle.Trivial X E) ContinuousMap.fst)
    have hF : Continuous (fun z : TotalSpace Unit B ↦ (z.snd : F)) :=
      eF.continuous.snd.comp
        (Pullback.continuous_lift Unit (Bundle.Trivial Y F) ContinuousMap.snd)
    let l : E →ₗ[ℂ] F →L[ℂ] H :=
      LinearMap.toContinuousLinearMap.toLinearMap.comp (TensorProduct.curry L)
    have hl : Continuous (fun z : E × F ↦ L (z.1 ⊗ₜ[ℂ] z.2)) :=
      (l.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
    refine { linearMap _ := L, continuous_total := ?_ }
    -- The tensor topology is final for its finite-sum maps, including the empty sum.
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun z : X × Y ↦ (Fin m → A z) × (Fin m → B z))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) inferInstance
    have hc : Continuous (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) := continuous_induced_dom
    have hs : Continuous (fun z : D ↦ ∑ i : Fin m, L (z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)) := by
      apply continuous_finsetSum
      intro i _
      exact hl.comp ((hE.comp ((continuous_apply i).comp hc.snd.fst)).prodMk
        (hF.comp ((continuous_apply i).comp hc.snd.snd)))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial Z H) f).continuous_iff]
    have hout := hc.fst.prodMk (eH.symm.continuous.comp
      ((f.continuous.comp hc.fst).prodMk hs))
    apply hout.congr
    intro z
    change (z.proj, eH.symm (f z.proj, ∑ i, L (z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i))) =
      (z.proj, eH.symm (f z.proj, L (∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)))
    rw [map_sum]
  have hParitySymbol :
      let PV := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
      let PW := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
      let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (WithLp 2 (V × W)))
      ∀ (L₀ : ((PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) ≃ₗ[ℂ] PS 0)
        (L₁ : ((PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) ≃ₗ[ℂ] PS 1),
        (∀ z, (L₀ z).val = exteriorTensorToSum
          (TensorProduct.map (PV 0).subtype (PW 0).subtype z.1 +
            TensorProduct.map (PV 1).subtype (PW 1).subtype z.2)) →
        (∀ z, (L₁ z).val = exteriorTensorToSum
          (TensorProduct.map (PV 1).subtype (PW 0).subtype z.1 +
            TensorProduct.map (PV 0).subtype (PW 1).subtype z.2)) →
        ∀ (v : V) (w : W) z,
          L₁ (reciprocalTensorSymbol (cliffordSymbolParity v 0) (-cliffordSymbolParity v 1)
            (cliffordSymbolParity w 0) (-cliffordSymbolParity w 1) z) =
          cliffordSymbolParity (WithLp.toLp 2 (v, w)) 0 (L₀ (z.1, -z.2)) := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    intro PV PW PS L₀ L₁ h₀ h₁ v w
    let _ : ContinuousSMul PUnit.{1} V :=
      ⟨by simpa using (continuous_snd : Continuous (Prod.snd : PUnit.{1} × V → V))⟩
    let _ : ContinuousSMul PUnit.{1} W :=
      ⟨by simpa using (continuous_snd : Continuous (Prod.snd : PUnit.{1} × W → W))⟩
    have hF := (exteriorTensorToSum_properties (G := PUnit.{1}) (V := V) (W := W)).2.2.2
    have hv (i : ZMod 2) (x : PV i) : (cliffordSymbolParity v i x).val =
        cliffordSymbol v x.val := rfl
    have hw (i : ZMod 2) (x : PW i) : (cliffordSymbolParity w i x).val =
        cliffordSymbol w x.val := rfl
    have hmap : L₁.toLinearMap.comp
        (reciprocalTensorSymbol (cliffordSymbolParity v 0) (-cliffordSymbolParity v 1)
          (cliffordSymbolParity w 0) (-cliffordSymbolParity w 1)) =
        (cliffordSymbolParity (WithLp.toLp 2 (v, w)) 0).comp
          (L₀.toLinearMap.comp ((LinearMap.id).prodMap (-LinearMap.id))) := by
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro x y
      · apply Subtype.ext
        change (L₁ _).val = cliffordSymbol _ (L₀ _).val
        rw [h₁, h₀]
        simpa only [reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
          LinearMap.coprod_apply, LinearMap.inl_apply, LinearMap.id_apply,
          LinearMap.prodMap_apply, LinearMap.neg_apply, map_zero, map_add,
          TensorProduct.map_tmul, Submodule.subtype_apply, hv, hw, neg_zero, add_zero, zero_add,
          CliffordAlgebra.involute_eq_of_mem_even x.property] using (hF v w x.val y.val).symm
      · apply Subtype.ext
        change (L₁ _).val = cliffordSymbol _ (L₀ _).val
        rw [h₁, h₀]
        have h := congrArg Neg.neg (hF v w x.val y.val)
        simp only [reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
          LinearMap.coprod_apply, LinearMap.inr_apply, LinearMap.id_apply,
          LinearMap.prodMap_apply, LinearMap.neg_apply, map_zero, map_add, map_neg,
          TensorProduct.map_tmul, Submodule.subtype_apply, hv, hw, zero_add,
          TensorProduct.tmul_neg, TensorProduct.neg_tmul, neg_add, neg_neg,
          CliffordAlgebra.involute_eq_of_mem_odd x.property] at h ⊢
        exact (add_comm _ _).trans h.symm
    intro z
    exact LinearMap.congr_fun hmap z
  let combineHom {X : Type} [TopologicalSpace X] (E F : FiniteBundle X)
      (f g : Hom E.Fiber F.Fiber) (r s : C(X, ℂ)) : Hom E.Fiber F.Fiber := by
    let p : C(TotalSpace Unit E.Fiber, X) := ⟨fun z ↦ z.proj, continuous_proj⟩
    let := isFiniteRank_pullback (E := F.Fiber) p
    have hf : Continuous (fun z : TotalSpace Unit E.Fiber ↦
        (⟨z, f.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ F.Fiber))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber p).continuous_iff]
      exact continuous_id.prodMk f.continuous_total
    have hg : Continuous (fun z : TotalSpace Unit E.Fiber ↦
        (⟨z, g.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ F.Fiber))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber p).continuous_iff]
      exact continuous_id.prodMk g.continuous_total
    refine { linearMap z := r z • f.linearMap z + s z • g.linearMap z
             continuous_total := ?_ }
    exact (Pullback.continuous_lift Unit F.Fiber p).comp
      (continuous_add_section (p *ᵖ F.Fiber) _ _
        (continuous_smul_section _ (r.comp p) _ hf)
        (continuous_smul_section _ (s.comp p) _ hg))
  let blockHom {X : Type} [TopologicalSpace X] (E₀ E₁ F₀ F₁ : FiniteBundle X)
      (d : Hom E₀.Fiber E₁.Fiber) (d' : Hom E₁.Fiber E₀.Fiber)
      (e : Hom F₀.Fiber F₁.Fiber) (e' : Hom F₁.Fiber F₀.Fiber) :
      Hom ((E₀.tensor F₀).sum (E₁.tensor F₁)).Fiber
        ((E₁.tensor F₀).sum (E₀.tensor F₁)).Fiber := by
    let source := (E₀.tensor F₀).sum (E₁.tensor F₁)
    let upper := combineHom source (E₁.tensor F₀)
      ((d.tensor (Hom.id _)).comp sumFst) (((Hom.id _).tensor e').comp sumSnd)
      (ContinuousMap.const _ 1) (ContinuousMap.const _ (-1))
    let lower := combineHom source (E₀.tensor F₁)
      (((Hom.id _).tensor e).comp sumFst) ((d'.tensor (Hom.id _)).comp sumSnd)
      (ContinuousMap.const _ 1) (ContinuousMap.const _ 1)
    refine { linearMap z := reciprocalTensorSymbol
                (d.linearMap z) (d'.linearMap z) (e.linearMap z) (e'.linearMap z)
             continuous_total := ?_ }
    apply continuous_induced_rng.mpr
    apply (upper.continuous_total.prodMk lower.continuous_total).congr
    intro z
    apply Prod.ext <;> apply congrArg (TotalSpace.mk z.proj)
    · simp only [upper, combineHom, ContinuousMap.const_apply, one_smul, neg_one_smul]
      rfl
    · simp only [lower, combineHom, ContinuousMap.const_apply, one_smul]
      rfl
  let cliffordParityHom (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (α : ℂ) (i : ZMod 2) :
      letI := exteriorAlgebraNormedAddCommGroup V
      letI := exteriorAlgebraNormedSpace V
      let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
      letI := modelTopology (P i) (Bundle.Trivial V (P i))
      letI := modelTopology (P (i + 1)) (Bundle.Trivial V (P (i + 1)))
      Hom (Bundle.Trivial V (P i)) (Bundle.Trivial V (P (i + 1))) := by
    let := exteriorAlgebraNormedAddCommGroup V
    let := exteriorAlgebraNormedSpace V
    let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
    let := modelTopology (P i) (Bundle.Trivial V (P i))
    let := modelTopology (P (i + 1)) (Bundle.Trivial V (P (i + 1)))
    let u := (unitTotalHomeomorph (P i) (Bundle.Trivial V (P i))).trans
      (Bundle.Trivial.homeomorphProd V (P i))
    let v := (unitTotalHomeomorph (P (i + 1)) (Bundle.Trivial V (P (i + 1)))).trans
      (Bundle.Trivial.homeomorphProd V (P (i + 1)))
    have h := (continuous_const (y := α)).smul
      ((continuous_cliffordSymbolParity i).comp u.continuous)
    exact { linearMap z := α • cliffordSymbolParity z i
            continuous_total := v.symm.continuous.comp (u.continuous.fst.prodMk h) }
  have hExteriorCutoff (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : C(V, I)) (hzero : ρ 0 = 0) :
      letI := exteriorAlgebraNormedAddCommGroup V
      letI := exteriorAlgebraNormedSpace V
      let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
      letI := modelTopology (P 0) (Bundle.Trivial V (P 0))
      letI := modelTopology (P 1) (Bundle.Trivial V (P 1))
      ∀ v : V,
        (exteriorBottTriple V).cutoffLinearMap ρ v = (ρ v : ℂ) • cliffordSymbolParity v 0 ∧
        (exteriorBottTriple V).inverse.cutoffLinearMap ρ v =
          -((ρ v : ℝ) / ‖v‖ ^ 2 : ℂ) • cliffordSymbolParity v 1 := by
    let := exteriorAlgebraNormedAddCommGroup V
    let := exteriorAlgebraNormedSpace V
    let P := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
    let := modelTopology (P 0) (Bundle.Trivial V (P 0))
    let := modelTopology (P 1) (Bundle.Trivial V (P 1))
    dsimp only
    intro v
    by_cases hv : v = 0
    · subst v
      simp [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        exteriorBottTriple, hzero]
    · constructor
      · dsimp only [CompactSupportTriple.cutoffLinearMap]
        rw [dite_eq_right (show v ∉ (exteriorBottTriple V).control by
          simpa only [exteriorBottTriple, Set.mem_singleton_iff] using hv)]
        rfl
      · dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse]
        rw [dite_eq_right (show v ∉ (exteriorBottTriple V).control by
          simpa only [exteriorBottTriple, Set.mem_singleton_iff] using hv)]
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change (ρ v : ℂ) •
          ((cliffordSymbolParityEquiv v hv 0).symm x : ExteriorAlgebra ℂ V) =
            (-((ρ v : ℝ) / ‖v‖ ^ 2 : ℂ)) • cliffordSymbol v x.val
        rw [cliffordSymbolParityEquiv_symm_apply]
        simp only [smul_smul, div_eq_mul_inv, mul_neg]
  have hAlgebraMix {A₀ A₁ B₀ B₁ : Type}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      (d₀ d₁ : A₀ →ₗ[ℂ] A₁) (d₀' d₁' : A₁ →ₗ[ℂ] A₀)
      (e₀ e₁ : B₀ →ₗ[ℂ] B₁) (e₀' e₁' : B₁ →ₗ[ℂ] B₀) (r s : ℂ) :
      reciprocalTensorSymbol (r • d₀ + s • d₁) (r • d₀' + s • d₁')
          (r • e₀ + s • e₁) (r • e₀' + s • e₁') =
        r • reciprocalTensorSymbol d₀ d₀' e₀ e₀' +
          s • reciprocalTensorSymbol d₁ d₁' e₁ e₁' := by
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro u v <;> apply Prod.ext <;>
      simp [reciprocalTensorSymbol, TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    all_goals abel
  have hTensorSquare {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : Type}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]
      [AddCommGroup D₀] [Module ℂ D₀] [AddCommGroup D₁] [Module ℂ D₁]
      (d : A₀ →ₗ[ℂ] A₁) (d' : A₁ →ₗ[ℂ] A₀)
      (e : B₀ →ₗ[ℂ] B₁) (e' : B₁ →ₗ[ℂ] B₀)
      (δ : C₀ →ₗ[ℂ] C₁) (δ' : C₁ →ₗ[ℂ] C₀)
      (ε : D₀ →ₗ[ℂ] D₁) (ε' : D₁ →ₗ[ℂ] D₀)
      (u : A₀ →ₗ[ℂ] C₀) (v : A₁ →ₗ[ℂ] C₁)
      (w : B₀ →ₗ[ℂ] D₀) (z : B₁ →ₗ[ℂ] D₁)
      (hD : ∀ a, v (d a) = δ (u a)) (hD' : ∀ a, u (d' a) = δ' (v a))
      (hE : ∀ b, z (e b) = ε (w b)) (hE' : ∀ b, w (e' b) = ε' (z b)) :
      ((TensorProduct.map v w).prodMap (TensorProduct.map u z)).comp
          (reciprocalTensorSymbol d d' e e') =
        (reciprocalTensorSymbol δ δ' ε ε').comp
          ((TensorProduct.map u w).prodMap (TensorProduct.map v z)) := by
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro a b <;> apply Prod.ext <;>
      simp [reciprocalTensorSymbol, hD, hD', hE, hE']
  let := exteriorAlgebraNormedAddCommGroup V
  let := exteriorAlgebraNormedSpace V
  let := exteriorAlgebraNormedAddCommGroup W
  let := exteriorAlgebraNormedSpace W
  let := exteriorAlgebraNormedAddCommGroup (WithLp 2 (V × W))
  let := exteriorAlgebraNormedSpace (WithLp 2 (V × W))
  let := FiniteDimensional.proper ℂ V
  let := FiniteDimensional.proper ℂ W
  let S := WithLp 2 (V × W)
  let hsum : ∀ (g : G) (u v : S), inner ℂ (g • u) (g • v) = inner ℂ u v :=
    fun g u v ↦ congrArg₂ (fun a b : ℂ ↦ a + b)
      (hV g (WithLp.ofLp u).1 (WithLp.ofLp v).1)
      (hW g (WithLp.ofLp u).2 (WithLp.ofLp v).2)
  let a := equivariantExteriorBottTriple hV
  let b := equivariantExteriorBottTriple hW
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm
  let p : C(V × W, S) := ⟨e, e.continuous⟩
  let c := (equivariantExteriorBottTriple hsum).pullback p
    (fun _ _ ↦ rfl) e.toHomeomorph.isProperMap
  let PV := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
  let PW := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
  let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ S)
  let (j : ZMod 2) := modelTopology (PV j) (Bundle.Trivial V (PV j))
  let (j : ZMod 2) := modelTopology (PW j) (Bundle.Trivial W (PW j))
  let (j : ZMod 2) := modelTopology (PS j) (Bundle.Trivial S (PS j))
  have normInvariant {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [DistribMulAction G E]
      (hu : ∀ (g : G) (u v : E), inner ℂ (g • u) (g • v) = inner ℂ u v)
      (g : G) (v : E) : ‖g • v‖ = ‖v‖ := by
    have h := congrArg Complex.re (hu g v v)
    have h₁ : (inner ℂ (g • v) (g • v)).re = ‖g • v‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) _
    have h₂ : (inner ℂ v v).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    rw [h₁, h₂] at h
    nlinarith [norm_nonneg (g • v), norm_nonneg v]
  let ρ : C(V, I) := ⟨fun v ↦ Set.projIcc 0 1 zero_le_one (‖v‖ - 1),
    continuous_projIcc.comp (continuous_norm.sub continuous_const)⟩
  let τ : C(W, I) := ⟨fun w ↦ Set.projIcc 0 1 zero_le_one (‖w‖ - 1),
    continuous_projIcc.comp (continuous_norm.sub continuous_const)⟩
  have hρzero (v : V) (hv : v ∈ Metric.ball 0 1) : ρ v = 0 := by
    apply projIcc_eq_zero.mpr
    have hv' : ‖v‖ < 1 := by simpa using hv
    linarith
  have hτzero (w : W) (hw : w ∈ Metric.ball 0 1) : τ w = 0 := by
    apply projIcc_eq_zero.mpr
    have hw' : ‖w‖ < 1 := by simpa using hw
    linarith
  let L : Set V := Metric.closedBall 0 2
  let M : Set W := Metric.closedBall 0 2
  have hL : IsCompact L := isCompact_closedBall 0 2
  have hM : IsCompact M := isCompact_closedBall 0 2
  have hρone (v : V) (hv : v ∉ L) : ρ v = 1 := by
    apply projIcc_eq_one.mpr
    have hv' : 2 < ‖v‖ := by simpa [L] using hv
    linarith
  have hτone (w : W) (hw : w ∉ M) : τ w = 1 := by
    apply projIcc_eq_one.mpr
    have hw' : 2 < ‖w‖ := by simpa [M] using hw
    linarith
  have hρinv (g : G) (v : V) : ρ (g • v) = ρ v := by
    change Set.projIcc 0 1 zero_le_one (‖g • v‖ - 1) = _
    rw [normInvariant hV]
    rfl
  have hτinv (g : G) (w : W) : τ (g • w) = τ w := by
    change Set.projIcc 0 1 zero_le_one (‖g • w‖ - 1) = _
    rw [normInvariant hW]
    rfl
  have hLinv (g : G) (v : V) : g • v ∈ L ↔ v ∈ L := by
    simp only [L, Metric.mem_closedBall, dist_zero_right, normInvariant hV]
  have hMinv (g : G) (w : W) : g • w ∈ M ↔ w ∈ M := by
    simp only [M, Metric.mem_closedBall, dist_zero_right, normInvariant hW]
  have ha : a.1.datum.control ⊆ Metric.ball 0 1 := by
    change ({0} : Set V) ⊆ _
    simp
  have hb : b.1.datum.control ⊆ Metric.ball 0 1 := by
    change ({0} : Set W) ⊆ _
    simp
  let A₀ := supportedEquivariantExternalProductTriple a b
    ρ (Metric.ball 0 1) Metric.isOpen_ball ha hρzero L hL hρone
    τ (Metric.ball 0 1) Metric.isOpen_ball hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv
  let E₀ := a.1.externalProductSource b.1
  let E₁ := a.1.externalProductTarget b.1
  let q₀ := blockHom
    (a.1.source.pullback ContinuousMap.fst) (a.1.target.pullback ContinuousMap.fst)
    (b.1.source.pullback ContinuousMap.snd) (b.1.target.pullback ContinuousMap.snd)
    ((a.1.datum.cutoffHom ρ _ Metric.isOpen_ball ha hρzero).pullback ContinuousMap.fst)
    ((a.1.datum.inverse.cutoffHom ρ _ Metric.isOpen_ball ha hρzero).pullback ContinuousMap.fst)
    ((b.1.datum.cutoffHom τ _ Metric.isOpen_ball hb hτzero).pullback ContinuousMap.snd)
    ((b.1.datum.inverse.cutoffHom τ _ Metric.isOpen_ball hb hτzero).pullback ContinuousMap.snd)
  let q₁ := blockHom
    (a.1.source.pullback ContinuousMap.fst) (a.1.target.pullback ContinuousMap.fst)
    (b.1.source.pullback ContinuousMap.snd) (b.1.target.pullback ContinuousMap.snd)
    ((cliffordParityHom V 1 0).pullback ContinuousMap.fst)
    ((cliffordParityHom V (-1) 1).pullback ContinuousMap.fst)
    ((cliffordParityHom W 1 0).pullback ContinuousMap.snd)
    ((cliffordParityHom W (-1) 1).pullback ContinuousMap.snd)
  have hq₀ (z : V × W) : q₀.linearMap z = reciprocalTensorSymbol
      ((ρ z.1 : ℂ) • cliffordSymbolParity z.1 0)
      (-((ρ z.1 : ℝ) / ‖z.1‖ ^ 2 : ℂ) • cliffordSymbolParity z.1 1)
      ((τ z.2 : ℂ) • cliffordSymbolParity z.2 0)
      (-((τ z.2 : ℝ) / ‖z.2‖ ^ 2 : ℂ) • cliffordSymbolParity z.2 1) := by
    change reciprocalTensorSymbol ((exteriorBottTriple V).cutoffLinearMap ρ z.1)
      ((exteriorBottTriple V).inverse.cutoffLinearMap ρ z.1)
      ((exteriorBottTriple W).cutoffLinearMap τ z.2)
      ((exteriorBottTriple W).inverse.cutoffLinearMap τ z.2) = _
    rw [(hExteriorCutoff V ρ (hρzero 0 (by simp)) z.1).1,
      (hExteriorCutoff V ρ (hρzero 0 (by simp)) z.1).2,
      (hExteriorCutoff W τ (hτzero 0 (by simp)) z.2).1,
      (hExteriorCutoff W τ (hτzero 0 (by simp)) z.2).2]
  have hq₁ (z : V × W) : q₁.linearMap z = reciprocalTensorSymbol
      (cliffordSymbolParity z.1 0) (-cliffordSymbolParity z.1 1)
      (cliffordSymbolParity z.2 0) (-cliffordSymbolParity z.2 1) := by
    dsimp only [q₁, blockHom, Hom.pullback, cliffordParityHom]
    simp only [one_smul, neg_one_smul]
    rfl
  let K : Set (V × W) := Set.prod L M
  have hK : IsCompact K := hL.prod hM
  have hKinv (g : G) (z : V × W) : g • z ∈ K ↔ z ∈ K :=
    and_congr (hLinv g z.1) (hMinv g z.2)
  have hoff (z : (Kᶜ : Set (V × W))) :
      (2 < ‖z.val.1‖ ∧ ρ z.val.1 = 1) ∨ (2 < ‖z.val.2‖ ∧ τ z.val.2 = 1) := by
    by_cases hv : z.val.1 ∈ L
    · have hw : z.val.2 ∉ M := fun hw ↦ z.property ⟨hv, hw⟩
      exact Or.inr ⟨by simpa [M] using hw, hτone _ hw⟩
    · exact Or.inl ⟨by simpa [L] using hv, hρone _ hv⟩
  let i : C((Kᶜ : Set (V × W)), V × W) := ⟨Subtype.val, continuous_subtype_val⟩
  let pr : C(I × (Kᶜ : Set (V × W)), (Kᶜ : Set (V × W))) := ContinuousMap.snd
  let r : C(I × (Kᶜ : Set (V × W)), ℂ) :=
    ⟨fun z ↦ ((1 - (z.1 : ℝ) : ℝ) : ℂ), Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))⟩
  let s : C(I × (Kᶜ : Set (V × W)), ℂ) :=
    ⟨fun z ↦ ((z.1 : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)⟩
  let q := combineHom ((E₀.pullback i).pullback pr) ((E₁.pullback i).pullback pr)
    ((q₀.pullback i).pullback pr) ((q₁.pullback i).pullback pr) r s
  have hmix (z : I × (Kᶜ : Set (V × W))) : q.linearMap z =
      reciprocalTensorSymbol
        ((((1 - (z.1 : ℝ)) * ρ z.2.val.1 + z.1 : ℝ) : ℂ) •
          cliffordSymbolParity z.2.val.1 0)
        (-(((1 - (z.1 : ℝ)) * ρ z.2.val.1 / ‖z.2.val.1‖ ^ 2 + z.1 : ℝ) : ℂ) •
          cliffordSymbolParity z.2.val.1 1)
        ((((1 - (z.1 : ℝ)) * τ z.2.val.2 + z.1 : ℝ) : ℂ) •
          cliffordSymbolParity z.2.val.2 0)
        (-(((1 - (z.1 : ℝ)) * τ z.2.val.2 / ‖z.2.val.2‖ ^ 2 + z.1 : ℝ) : ℂ) •
          cliffordSymbolParity z.2.val.2 1) := by
    change r z • q₀.linearMap z.2.val + s z • q₁.linearMap z.2.val = _
    rw [hq₀, hq₁, ← hAlgebraMix]
    congr 1 <;>
      simp only [r, s, ContinuousMap.coe_mk, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
        add_smul, smul_smul, smul_neg, neg_smul, neg_add_rev, mul_div_assoc] <;> module
  have hqbij (z : I × (Kᶜ : Set (V × W))) : Function.Bijective (q.linearMap z) := by
    rw [hmix]
    exact hWeightedBlock z.2.val.1 z.2.val.2
      (ρ z.2.val.1) (τ z.2.val.2) z.1 (hoff z.2)
  let qIso := q.toIso hqbij
  have hqIso (z : I × (Kᶜ : Set (V × W))) (u : E₀.Fiber z.2.val) :
      qIso.linearEquiv z u = ((1 - (z.1 : ℝ) : ℝ) : ℂ) • q₀.linearMap z.2.val u +
        ((z.1 : ℝ) : ℂ) • q₁.linearMap z.2.val u := rfl
  have hq₁bij (z : (Kᶜ : Set (V × W))) :
      Function.Bijective ((q₁.pullback i).linearMap z) := by
    have h := hqbij (1, z)
    change Function.Bijective ((r (1, z)) • q₀.linearMap z.val +
      (s (1, z)) • q₁.linearMap z.val) at h
    simp only [r, s, ContinuousMap.coe_mk, Set.Icc.coe_one, sub_self,
      Complex.ofReal_zero, Complex.ofReal_one, zero_smul, one_smul, zero_add] at h
    exact h
  have hq₁eqv (g : G) (z : V × W) (u : E₀.Fiber z) :
      q₁.linearMap (g • z) ((a.externalProductSourceAction b).linearMap g z u) =
        (a.externalProductTargetAction b).linearMap g z (q₁.linearMap z u) := by
    have hD (j : ZMod 2) (v : PV j) :
        cliffordSymbolParity (g • z.1) j (exteriorParityAction g j v) =
          exteriorParityAction g (j + 1) (cliffordSymbolParity z.1 j v) :=
      LinearMap.congr_fun (cliffordSymbolParity_equivariant hV g z.1 j) v
    have hE (j : ZMod 2) (w : PW j) :
        cliffordSymbolParity (g • z.2) j (exteriorParityAction g j w) =
          exteriorParityAction g (j + 1) (cliffordSymbolParity z.2 j w) :=
      LinearMap.congr_fun (cliffordSymbolParity_equivariant hW g z.2 j) w
    have hblock : (reciprocalTensorSymbol (cliffordSymbolParity (g • z.1) 0)
          (-cliffordSymbolParity (g • z.1) 1) (cliffordSymbolParity (g • z.2) 0)
          (-cliffordSymbolParity (g • z.2) 1)).comp
        ((TensorProduct.map (exteriorParityAction g 0) (exteriorParityAction g 0)).prodMap
          (TensorProduct.map (exteriorParityAction g 1) (exteriorParityAction g 1))) =
        ((TensorProduct.map (exteriorParityAction g 1) (exteriorParityAction g 0)).prodMap
          (TensorProduct.map (exteriorParityAction g 0) (exteriorParityAction g 1))).comp
            (reciprocalTensorSymbol (cliffordSymbolParity z.1 0)
              (-cliffordSymbolParity z.1 1) (cliffordSymbolParity z.2 0)
              (-cliffordSymbolParity z.2 1)) := by
      symm
      apply hTensorSquare
      · intro x
        exact (hD 0 x).symm
      · intro x
        have h := congrArg Neg.neg (hD 1 x).symm
        change -(exteriorParityAction g 0) (cliffordSymbolParity z.1 1 x) =
          -(cliffordSymbolParity (g • z.1) 1) (exteriorParityAction g 1 x) at h
        exact (map_neg (exteriorParityAction g 0) (cliffordSymbolParity z.1 1 x)).trans h
      · intro x
        exact (hE 0 x).symm
      · intro x
        have h := congrArg Neg.neg (hE 1 x).symm
        change -(exteriorParityAction g 0) (cliffordSymbolParity z.2 1 x) =
          -(cliffordSymbolParity (g • z.2) 1) (exteriorParityAction g 1 x) at h
        exact (map_neg (exteriorParityAction g 0) (cliffordSymbolParity z.2 1 x)).trans h
    rw [hq₁, hq₁]
    exact LinearMap.congr_fun hblock u
  let A₁datum : CompactSupportTriple E₀.Fiber E₁.Fiber :=
    { control := K
      isCompact_control := hK
      boundary := (q₁.pullback i).toIso hq₁bij }
  have hA₁ : A₁datum.IsEquivariant (a.externalProductSourceAction b)
      (a.externalProductTargetAction b) := by
    refine ⟨hKinv, ?_⟩
    intro g z u
    exact hq₁eqv g z.val u
  let A₁ := EquivariantSupportBundleTriple.ofBoundary E₀ E₁ A₁datum
    (a.externalProductSourceAction b) (a.externalProductTargetAction b) hA₁
  have hq₀boundary (z : (Kᶜ : Set (V × W))) (u : E₀.Fiber z.val) :
      A₀.1.datum.boundary.linearEquiv z u = q₀.linearMap z.val u := rfl
  have hq₀eqv (g : G) (z : (Kᶜ : Set (V × W))) (u : E₀.Fiber z.val) :
      q₀.linearMap (g • z.val)
          ((a.externalProductSourceAction b).linearMap g z.val u) =
        (a.externalProductTargetAction b).linearMap g z.val (q₀.linearMap z.val u) := by
    exact A₀.2.isEquivariant.boundary_intertwines g z u
  let H : CompactSupportTriple.EquivariantHomotopy
      (a.externalProductSourceAction b) (a.externalProductTargetAction b)
      A₀.1.datum A₁datum :=
    { control := K
      isCompact_control := hK
      invariant_control := hKinv
      left_control := Set.Subset.refl _
      right_control := Set.Subset.refl _
      homotopy :=
        { iso := qIso
          map_zero := by
            intro z u
            refine (hqIso (0, z) u).trans ?_
            simp only [Set.Icc.coe_zero, sub_zero, Complex.ofReal_one, one_smul,
              Complex.ofReal_zero, zero_smul, add_zero]
            rw [Iso.restrictTo_apply]
            exact (hq₀boundary z u).symm
          map_one := by
            intro z u
            refine (hqIso (1, z) u).trans ?_
            simp only [Set.Icc.coe_one, sub_self, Complex.ofReal_zero, zero_smul,
              Complex.ofReal_one, one_smul, zero_add]
            rw [Iso.restrictTo_apply]
            rfl }
      intertwines := by
        intro t g z u
        change qIso.linearEquiv (t, ⟨g • z.val, _⟩)
          ((a.externalProductSourceAction b).linearMap g z.val u) =
            (a.externalProductTargetAction b).linearMap g z.val
              (qIso.linearEquiv (t, z) u)
        rw [hqIso, hqIso, hq₀eqv, hq₁eqv, map_add, map_smul, map_smul] }
  have hA₀A₁ : A₀.kZeroClass = A₁.kZeroClass :=
    equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic E₀ E₁
      (a.externalProductSourceAction b) (a.externalProductTargetAction b)
      A₀.1.datum A₁datum A₀.2.isEquivariant hA₁ ⟨H⟩
  -- The ordered tensor identification has a negative odd-odd source coordinate.
  obtain ⟨L₀, L₁, hL₀, hL₁⟩ := hParityTensor
  let fu := combineHom E₀ c.1.source
    ((constantTensorHom p (L₀.toLinearMap.comp (LinearMap.inl ℂ _ _))).comp sumFst)
    ((constantTensorHom p (L₀.toLinearMap.comp (LinearMap.inr ℂ _ _))).comp sumSnd)
    (ContinuousMap.const _ 1) (ContinuousMap.const _ (-1))
  let fv := combineHom E₁ c.1.target
    ((constantTensorHom p (L₁.toLinearMap.comp (LinearMap.inl ℂ _ _))).comp sumFst)
    ((constantTensorHom p (L₁.toLinearMap.comp (LinearMap.inr ℂ _ _))).comp sumSnd)
    (ContinuousMap.const _ 1) (ContinuousMap.const _ 1)
  have hfu (z : V × W) (w : E₀.Fiber z) : fu.linearMap z w = L₀ (w.1, -w.2) := by
    change (1 : ℂ) • L₀ (w.1, 0) + (-1 : ℂ) • L₀ (0, w.2) = L₀ (w.1, -w.2)
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
    calc
      _ = L₀ ((w.1, 0) - (0, w.2)) := (map_sub L₀ (w.1, 0) (0, w.2)).symm
      _ = _ := congrArg L₀ (by ext <;> simp)
  have hfv (z : V × W) (w : E₁.Fiber z) : fv.linearMap z w = L₁ w := by
    change (1 : ℂ) • L₁ (w.1, 0) + (1 : ℂ) • L₁ (0, w.2) = L₁ w
    rw [one_smul, one_smul, ← map_add]
    congr 1
    ext <;> simp
  have hfubij (z : V × W) : Function.Bijective (fu.linearMap z) := by
    have hsign : Function.Involutive
        (fun w : (PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1) ↦ (w.1, -w.2)) := by
      intro w
      simp
    have hfun : (fun w ↦ fu.linearMap z w) = fun w ↦ L₀ (w.1, -w.2) := funext (hfu z)
    rw [show (fu.linearMap z : E₀.Fiber z → c.1.source.Fiber z) =
      (fun w ↦ L₀ (w.1, -w.2)) from hfun]
    exact L₀.bijective.comp hsign.bijective
  have hfvbij (z : V × W) : Function.Bijective (fv.linearMap z) := by
    rw [show (fv.linearMap z : E₁.Fiber z → c.1.target.Fiber z) =
      (fun w ↦ L₁ w) from funext (hfv z)]
    exact L₁.bijective
  let u := fu.toIso hfubij
  let v := fv.toIso hfvbij
  -- Naturality of the same tensor map proves the equivariance of both global isomorphisms.
  have hTin (g : G) (j k : ZMod 2) (w : PV j ⊗[ℂ] PW k) :
      TensorProduct.map (PV j).subtype (PW k).subtype
          (TensorProduct.map (exteriorParityAction g j) (exteriorParityAction g k) w) =
        TensorProduct.map
          (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)).toLinearMap
          (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ W g)).toLinearMap
            (TensorProduct.map (PV j).subtype (PW k).subtype w) := by
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul x y => rfl
  have hL₀eqv (g : G) (w : (PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) :
      L₀ (TensorProduct.map (exteriorParityAction g 0) (exteriorParityAction g 0) w.1,
        TensorProduct.map (exteriorParityAction g 1) (exteriorParityAction g 1) w.2) =
          exteriorParityAction g 0 (L₀ w) := by
    apply Subtype.ext
    rw [hL₀]
    change _ = ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ S g) (L₀ w).val
    rw [hL₀, hTin, hTin, ← map_add]
    exact (exteriorTensorToSum_properties (G := G) (V := V) (W := W)).2.1 g _
  have hL₁eqv (g : G) (w : (PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) :
      L₁ (TensorProduct.map (exteriorParityAction g 1) (exteriorParityAction g 0) w.1,
        TensorProduct.map (exteriorParityAction g 0) (exteriorParityAction g 1) w.2) =
          exteriorParityAction g 1 (L₁ w) := by
    apply Subtype.ext
    rw [hL₁]
    change _ = ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ S g) (L₁ w).val
    rw [hL₁, hTin, hTin, ← map_add]
    exact (exteriorTensorToSum_properties (G := G) (V := V) (W := W)).2.1 g _
  have hueqv : u.IsEquivariant A₁.2.sourceAction c.2.sourceAction := by
    intro g z w
    change fu.linearMap (g • z) ((a.externalProductSourceAction b).linearMap g z w) =
      exteriorParityAction g 0 (fu.linearMap z w)
    rw [hfu, hfu]
    change L₀ (TensorProduct.map (exteriorParityAction g 0) (exteriorParityAction g 0) w.1,
      -(TensorProduct.map (exteriorParityAction g 1) (exteriorParityAction g 1) w.2)) = _
    rw [← map_neg]
    exact hL₀eqv g (w.1, -w.2)
  have hveqv : v.IsEquivariant A₁.2.targetAction c.2.targetAction := by
    intro g z w
    change fv.linearMap (g • z) ((a.externalProductTargetAction b).linearMap g z w) =
      exteriorParityAction g 1 (fv.linearMap z w)
    rw [hfv, hfv]
    exact hL₁eqv g w
  have hcK : c.1.datum.control ⊆ K := by
    intro z hz
    change p z ∈ ({0} : Set S) at hz
    have hz0 : z = 0 := e.injective (by simpa only [p, ContinuousMap.coe_mk,
      Set.mem_singleton_iff, map_zero] using hz)
    subst z
    change (0 : V) ∈ L ∧ (0 : W) ∈ M
    simp [L, M]
  have hA₁c : A₁.IsIsomorphic c := by
    refine ⟨K, hK, hKinv, Set.Subset.refl _, hcK, u, v, hueqv, hveqv, ?_⟩
    intro z w
    rw [CompactSupportTriple.enlarge_apply, CompactSupportTriple.enlarge_apply]
    change fv.linearMap z.val (q₁.linearMap z.val w) =
      c.1.datum.boundary.linearEquiv ⟨z.val, _⟩ (fu.linearMap z.val w)
    rw [hfv, hfu, hq₁]
    change _ = ((exteriorBottTriple S).boundary.pullback p).linearEquiv _ _
    rw [RelativeTriple.pullback_apply]
    change L₁ (reciprocalTensorSymbol (cliffordSymbolParity z.val.1 0)
      (-cliffordSymbolParity z.val.1 1) (cliffordSymbolParity z.val.2 0)
      (-cliffordSymbolParity z.val.2 1) w) =
        cliffordSymbolParity (WithLp.toLp 2 z.val) 0 (L₀ (w.1, -w.2))
    exact hParitySymbol L₀ L₁ hL₀ hL₁ z.val.1 z.val.2 w
  -- Descend the same fixed-control homotopy and global square through the presentation.
  change equivariantSupportTripleKZeroPullback p (fun _ _ ↦ rfl)
    e.toHomeomorph.isProperMap (equivariantExteriorBottTriple hsum).kZeroClass =
      equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass
  rw [equivariantSupportTripleKZeroPullback_apply]
  have hproduct := equivariantSupportKZeroExternalProduct_class a b
    ρ (Metric.ball 0 1) Metric.isOpen_ball ha hρzero L hL hρone
    τ (Metric.ball 0 1) Metric.isOpen_ball hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv
  exact (equivariantSupportTripleKZero_generator_relations.1 A₁ c hA₁c).symm.trans
    (hA₀A₁.symm.trans hproduct.symm)

/-- The same ordered direct-sum comparison multiplies the original full Bott coefficients. -/
theorem equivariantBottLinearMap_prod (r s : RepresentationGrothendieckGroup G) :
    letI := FiniteDimensional.proper ℂ V
    letI := FiniteDimensional.proper ℂ W
    let hsum : ∀ (g : G) (u v : WithLp 2 (V × W)),
        inner ℂ (g • u) (g • v) = inner ℂ u v := fun g u v ↦ by
      exact congrArg₂ (fun a b : ℂ ↦ a + b)
        (hV g (WithLp.ofLp u).1 (WithLp.ofLp v).1)
        (hW g (WithLp.ofLp u).2 (WithLp.ofLp v).2)
    let e := (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm
    equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩
        (fun _ _ ↦ rfl) e.toHomeomorph.isProperMap
        (equivariantBottLinearMap hsum (r * s)) =
      equivariantSupportKZeroExternalProduct
        (equivariantBottLinearMap hV r) (equivariantBottLinearMap hW s) := by
  /- Expand each existing Bott forward map as multiplication by its
  specified exterior class. Proper equivariant pullback preserves the
  actual representation-ring action. Apply the preceding direct-sum class
  comparison and the established balancing laws of the same external
  product in its first and second variables. The two full coefficients
  combine as r*s; integer dimension or character evaluation never replaces
  either coefficient. Both routes use the same e, original unitary actions,
  parity convention and compact-control comparison. -/
  let := FiniteDimensional.proper ℂ V
  let := FiniteDimensional.proper ℂ W
  let hsum : ∀ (g : G) (u v : WithLp 2 (V × W)),
      inner ℂ (g • u) (g • v) = inner ℂ u v := fun g u v ↦
    congrArg₂ (fun a b : ℂ ↦ a + b)
      (hV g (WithLp.ofLp u).1 (WithLp.ofLp v).1)
      (hW g (WithLp.ofLp u).2 (WithLp.ofLp v).2)
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm
  change equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩
    (fun _ _ ↦ rfl) e.toHomeomorph.isProperMap
      ((r * s) • equivariantExteriorBottClass hsum) =
        equivariantSupportKZeroExternalProduct
          (r • equivariantExteriorBottClass hV) (s • equivariantExteriorBottClass hW)
  -- Proper pullback and the specified product retain both full representation coefficients.
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  rw [equivariantSupportTripleKZeroPullback_smul,
    equivariantExteriorBottClass_prod hV hW,
    equivariantSupportKZeroExternalProduct_smul_left,
    equivariantSupportKZeroExternalProduct_smul_right, mul_smul]

end AtiyahSinger
