/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorTopology
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The original exterior symbol under a unitary group action

Public module ID: M0014.

The exterior action is the restriction of mathlib's exterior algebra map induced
by the given complex-linear action on the original vector space. Both parity
carriers and their finite-dimensional topology are the previously fixed ones.
The action laws and joint continuity certify this same map; they do not select
an unrelated representation with the same dimension.

A unitary action intertwines the actual wedge-minus-contraction symbol. This is
the representation model underlying ASI I section 2, pp.494--496, and the exterior
Thom construction in SG Appendix C / Karoubi IV.1.5. Equivariance uses the supplied
Hermitian invariance equation. Compactness of the group is unnecessary here;
the independent equivariant Bott theorem has additional hypotheses elsewhere.
The proofs certify these original actions and their actual Clifford intertwining identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [DistribMulAction G V] [SMulCommClass G ℂ V] [ContinuousSMul G V]

-- Preserve the original section assumptions although this algebraic proof needs fewer.
set_option linter.unusedSectionVars false in
/-- The actual induced exterior map preserves the original parity submodules. -/
theorem exteriorAction_mem_evenOdd (g : G) (i : ZMod 2) (a : ExteriorAlgebra ℂ V)
    (ha : a ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i) :
    ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g) a ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
  /- The exterior map sends each product of k original vectors to the product
  of their k images, retaining its degree and hence parity. Extend this identity
  over the standard span defining the existing evenOdd submodule. This argument
  uses complex linearity, not preservation of a chosen Hermitian metric. -/
  -- Preserve vector generators first, then their powers and the existing parity supremum.
  let f : V →ₗ[ℂ] V := DistribSMul.toLinearMap ℂ V g
  let F : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V := ExteriorAlgebra.map f
  have hrange : (LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ V))).map
      F.toLinearMap ≤ LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm ℂ V)) := by
    rintro _ ⟨x, ⟨v, rfl⟩, rfl⟩
    exact ⟨f v, (ExteriorAlgebra.map_apply_ι f v).symm⟩
  have hparity : (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i).map
      F.toLinearMap ≤ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i := by
    simp only [CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
    exact iSup_mono (fun n ↦ pow_le_pow_left' hrange n.val)
  exact (Submodule.map_le_iff_le_comap.mp hparity) ha

/-- The original exterior action restricted to one of its actual parity subspaces. -/
def exteriorParityAction (g : G) (i : ZMod 2) :
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i →ₗ[ℂ]
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i :=
  (ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)).toLinearMap.restrict
    (fun a ha ↦ exteriorAction_mem_evenOdd g i a ha)

/-- The induced parity maps form a jointly continuous action on the original finite spaces. -/
theorem exteriorParityAction_properties (i : ZMod 2) :
    exteriorParityAction (V := V) (1 : G) i = LinearMap.id ∧
    (∀ g h : G, exteriorParityAction (V := V) (g * h) i =
      (exteriorParityAction g i).comp (exteriorParityAction h i)) ∧
    Continuous (fun p : G × CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i ↦
      exteriorParityAction p.1 i p.2) := by
  /- Functoriality on vector generators proves the identity and composition laws.
  Algebra induction gives continuity of each orbit in the actual exterior algebra.
  In finite dimension, continuity on each vector gives continuity of the operator
  family, and evaluation is jointly continuous. Restrict to the original parity
  carrier with its inherited topology; no chosen matrix minors are needed. -/
  let F (g : G) : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V :=
    ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)
  -- These equalities use the original maps on vector generators.
  have hFone : F 1 = AlgHom.id ℂ (ExteriorAlgebra ℂ V) := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [F]
  have hFmul (g h : G) : F (g * h) = (F g).comp (F h) := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [F, mul_smul]
  -- Multiplication is continuous for the already fixed finite-dimensional coordinate topology.
  let : IsModuleTopology ℂ (ExteriorAlgebra ℂ V) := isModuleTopologyOfFiniteDimensional
  let : IsTopologicalRing (ExteriorAlgebra ℂ V) :=
    IsModuleTopology.isTopologicalRing ℂ (ExteriorAlgebra ℂ V)
  have horbit (a : ExteriorAlgebra ℂ V) : Continuous (fun g : G ↦ F g a) := by
    induction a using ExteriorAlgebra.induction with
    | algebraMap c =>
      simpa using continuous_const (y := algebraMap ℂ (ExteriorAlgebra ℂ V) c)
    | ι v =>
      simpa [F, Function.comp_def, Pi.smul_apply] using
        (ExteriorAlgebra.ι ℂ (M := V)).continuous_of_finiteDimensional.comp
          (continuous_id.smul (continuous_const (y := v)))
    | mul a b ha hb => simpa only [map_mul] using ha.fun_mul hb
    | add a b ha hb => simpa only [map_add] using ha.fun_add hb
  have hfamily :
      Continuous (fun g : G ↦ (exteriorParityAction (V := V) g i).toContinuousLinearMap) := by
    apply continuous_clm_apply.mpr
    intro a
    exact (horbit a.val).subtype_mk _
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact AlgHom.congr_fun hFone a.val
  · intro g h
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact AlgHom.congr_fun (hFmul g h) a.val
  · -- Evaluate the same continuous family on the varying parity vector.
    exact (hfamily.comp continuous_fst).clm_apply continuous_snd

/-- A unitary group action intertwines the specified negative-square Clifford symbol. -/
theorem cliffordSymbolParity_equivariant
    (hunitary : ∀ (g : G) (u v : V), inner ℂ (g • u) (g • v) = inner ℂ u v)
    (g : G) (v : V) (i : ZMod 2) :
    (cliffordSymbolParity (g • v) i).comp (exteriorParityAction g i) =
      (exteriorParityAction g (i + 1)).comp (cliffordSymbolParity v i) := by
  /- Stage 1: functoriality intertwines wedge multiplication by v with wedge
  multiplication by g v. Expand contraction on a decomposable exterior vector;
  hunitary identifies each Hermitian coefficient before and after applying g.
  Thus the original contraction also intertwines with the same exterior map.
  Stage 2: subtract the two identities, preserving SG's minus convention.
  Restrict to parity i and i+1 using their actual inclusions. The equality holds
  also at v=0; off zero it supplies the boundary square for the Bott triple. -/
  let F : ExteriorAlgebra ℂ V →ₐ[ℂ] ExteriorAlgebra ℂ V :=
    ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V g)
  -- The contraction rule is natural because the original Hermitian coefficients are invariant.
  have hcontract (a : ExteriorAlgebra ℂ V) :
      contraction (g • v) (F a) = F (contraction v a) := by
    induction a using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp [contraction, CliffordAlgebra.contractLeft_algebraMap]
    | add a b ha hb =>
      simp only [map_add, ha, hb]
    | ι_mul a w ha =>
      have hw : F (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w) =
          CliffordAlgebra.ι (0 : QuadraticForm ℂ V) (g • w) :=
        ExteriorAlgebra.map_apply_ι (DistribSMul.toLinearMap ℂ V g) w
      change CliffordAlgebra.contractLeft (innerₛₗ ℂ (g • v))
        (F (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w * a)) =
          F (CliffordAlgebra.contractLeft (innerₛₗ ℂ v)
            (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) w * a))
      rw [map_mul, hw, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul F, map_mul, hw]
      change inner ℂ (g • v) (g • w) • F a -
        CliffordAlgebra.ι (0 : QuadraticForm ℂ V) (g • w) * contraction (g • v) (F a) =
          inner ℂ v w • F a -
            CliffordAlgebra.ι (0 : QuadraticForm ℂ V) (g • w) * F (contraction v a)
      rw [hunitary, ha]
  -- Wedge multiplication is functorial; subtract contraction with the unchanged minus sign.
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change cliffordSymbol (g • v) (F a.val) = F (cliffordSymbol v a.val)
  change ExteriorAlgebra.ι ℂ (g • v) * F a.val - contraction (g • v) (F a.val) =
    F (ExteriorAlgebra.ι ℂ v * a.val - contraction v a.val)
  rw [map_sub, map_mul, hcontract]
  rw [show F (ExteriorAlgebra.ι ℂ v) = ExteriorAlgebra.ι ℂ (g • v) from
    ExteriorAlgebra.map_apply_ι (DistribSMul.toLinearMap ℂ V g) v]

end AtiyahSinger
