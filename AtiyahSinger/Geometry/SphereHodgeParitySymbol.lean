/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PositiveHodgeNativeRealization
public import AtiyahSinger.Geometry.ComplexifiedTangentExteriorOperators
public import AtiyahSinger.Geometry.ComplexifiedTangentParityForms
public import AtiyahSinger.Geometry.SphereExteriorFormMetric
public import AtiyahSinger.Topology.SphereDeRhamClass
public import AtiyahSinger.Topology.SphereHodgeSymbolComparison

/-!
# The original sphere symbol in finite Hodge form coordinates

Public module ID: M1434.

The metric exterior identification sends the homogeneous components of wedge
minus contraction to the actual adjacent-degree Hodge symbol components. The
original exterior phase then gives the precise square for the sphere de Rham
symbol, using its original round Hermitian metric and the finite form grading.

Source: Lawson--Michelsohn, Spin Geometry, II.5 and III.13; the exact finite
coordinate square is the implementation of the standard exterior comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators DirectSum Manifold ContDiff TensorProduct

attribute [local instance] sphereComplexifiedTangentTopology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option maxHeartbeats 1200000 in
-- Homogeneous projection retains exactly the two adjacent degrees of the same symbol.
set_option backward.isDefEq.respectTransparency false in
/-- The homogeneous exterior symbol becomes the original Hodge principal component. -/
theorem complexifiedTangentExteriorEquiv_hodgeSymbolComponent
    (g : SmoothTangentMetric (n := n) (M := M)) (p q : ℕ) (x : M)
    (v : EuclideanSpace ℝ (Fin n))
    (d : Module.Dual ℂ (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hd : ∀ z, d z = complexifiedTangentCovectorMap g x z v)
    (a : ⋀[ℂ]^p (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)) :
    complexifiedTangentExteriorEquiv g q x
        (DirectSum.decompose (fun k : ℕ ↦
          ⋀[ℂ]^k (ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
            (Complex.I • (ExteriorAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] v) * a.val -
              CliffordAlgebra.contractLeft d a.val)) q) =
      differentialFormHodgeSymbolComponent g p q x v
        (complexifiedTangentExteriorEquiv g p x a) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let C := ℂ ⊗[ℝ] V
  let grade (k : ℕ) : Submodule ℂ (ExteriorAlgebra ℂ C) := ⋀[ℂ]^k C
  let T (k : ℕ) : grade k ≃ₗ[ℂ] (V [⋀^Fin k]→L[ℝ] ℂ) :=
    complexifiedTangentExteriorEquiv g k x
  let P (k : ℕ) : ExteriorAlgebra ℂ C →ₗ[ℂ] grade k :=
    (DirectSum.component ℂ ℕ (fun k ↦ grade k) k).comp
      (DirectSum.decomposeLinearEquiv grade).toLinearMap
  have hsame (k : ℕ) (b : grade k) : P k b.val = b := by
    change DirectSum.decompose grade b.val k = b
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
  have hzero (k j : ℕ) (b : grade k) (hjk : j ≠ k) : P j b.val = 0 := by
    change DirectSum.decompose grade b.val j = 0
    rw [DirectSum.decompose_coe, DirectSum.of_eq_of_ne _ _ _ hjk]
  let w : grade (p + 1) :=
    ⟨ExteriorAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] v) * a.val, by
      change _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ)) ^ (p + 1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) a.property⟩
  have hw : T (p + 1) w = ContinuousAlternatingMap.alternatizeUncurryFin
      ((g.inner x v).smulRight (T p a)) :=
    complexifiedTangentExteriorEquiv_wedge g p x v a w rfl
  -- In degree zero the contraction vanishes on the original scalar submodule.
  cases p with
  | zero =>
      have hc : CliffordAlgebra.contractLeft d a.val = 0 := by
        have ha := a.property
        change a.val ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ)) ^ 0 at ha
        rw [pow_zero] at ha
        obtain ⟨c, hc⟩ := Submodule.mem_one.mp ha
        rw [← hc, CliffordAlgebra.contractLeft_algebraMap]
      change T q (P q (Complex.I • (w.val - CliffordAlgebra.contractLeft d a.val))) = _
      rw [hc, sub_zero, map_smul, map_smul]
      by_cases hq : q = 1
      · subst q
        rw [hsame, hw]
        rfl
      · rw [hzero 1 q w hq, map_zero, smul_zero]
        simp [differentialFormHodgeSymbolComponent, hq]
  | succ p =>
      -- For positive degree, the actual contraction is homogeneous one degree lower.
      let c : grade p := ⟨CliffordAlgebra.contractLeft d a.val,
        exteriorContractLeft_mem_exteriorPower d p a.val a.property⟩
      have hc : T p c = (T (p + 1) a).curryLeft v :=
        complexifiedTangentExteriorEquiv_contractLeft g p x v d hd a c rfl
      change T q (P q (Complex.I • (w.val - c.val))) = _
      simp only [map_smul, map_sub]
      by_cases hraise : q = p + 1 + 1
      · subst q
        rw [hsame, hzero p (p + 1 + 1) c (by omega), map_zero, sub_zero, hw]
        simp only [differentialFormHodgeSymbolComponent]
        rfl
      · by_cases hlower : q = p
        · subst q
          rw [hzero (p + 1 + 1) p w (by omega), hsame, map_zero, zero_sub, hc]
          simp only [differentialFormHodgeSymbolComponent,
            dite_eq_right hraise, smul_neg, neg_smul]
          rfl
        · rw [hzero (p + 1 + 1) q w hraise, hzero p q c hlower, map_zero,
            sub_self, smul_zero]
          have hne : p + 1 ≠ q + 1 := by omega
          simp only [differentialFormHodgeSymbolComponent,
            dite_eq_right hraise, dite_eq_right hne]

set_option maxHeartbeats 1200000 in
-- Keep the phase, the finite form coordinates and the original round contraction together.
set_option backward.isDefEq.respectTransparency false in
/-- The original sphere de Rham symbol is the finite Hodge symbol in the phased form coordinates. -/
theorem sphereDeRhamSymbol_hodge_components (r : ℕ)
    (z : TangentBundle (𝓡 r) (OrthogonalSphere r))
    (a : (sphereDeRhamParityBundle r 0).Fiber z) :
    let core := (sphereComplexifiedRoundMetric r).toCore z.proj
    letI : NormedAddCommGroup (SphereComplexifiedTangent r z.proj) :=
      core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (SphereComplexifiedTangent r z.proj) :=
      InnerProductSpace.ofCore core.toCore
    complexifiedTangentOddFormEquiv (orthogonalSphereRoundMetric r) z.proj
        (exteriorHodgePhaseEquiv (SphereComplexifiedTangent r z.proj) 1
          (sphereDeRhamSymbol r 0 z a)) =
      fun q ↦ ∑ p, differentialFormHodgeSymbolComponent (orthogonalSphereRoundMetric r)
        p.val.val q.val.val z.proj z.snd
        (complexifiedTangentEvenFormEquiv (orthogonalSphereRoundMetric r) z.proj
          (exteriorHodgePhaseEquiv (SphereComplexifiedTangent r z.proj) 0 a) p) := by
  classical
  let C := SphereComplexifiedTangent r z.proj
  let core := (sphereComplexifiedRoundMetric r).toCore z.proj
  let : NormedAddCommGroup C := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ C := InnerProductSpace.ofCore core.toCore
  let g := orthogonalSphereRoundMetric r
  let v : C := (1 : ℂ) ⊗ₜ[ℝ] z.snd
  let d : Module.Dual ℂ C := innerₛₗ ℂ v
  have hd (w : C) : d w = complexifiedTangentCovectorMap g z.proj w z.snd :=
    sphereComplexifiedRoundMetric_inner_one_tmul r z.proj z.snd w
  let b := exteriorHodgePhaseEquiv C 0 a
  let u := complexifiedTangentEvenFormEquiv g z.proj b
  let T (k : ℕ) : (⋀[ℂ]^k C) ≃ₗ[ℂ] DifferentialFormFiber (n := r) k z.proj :=
    complexifiedTangentExteriorEquiv g k z.proj
  -- The original zero-parameter vector and the phase lemma fix both adjacent signs.
  have hvector : sphereDeRhamVector r 0 z = v := by
    simp only [sphereDeRhamVector, Complex.ofReal_zero, zero_mul,
      TensorProduct.zero_tmul, sub_zero, v]
  have hphase : exteriorHodgePhaseEquiv C 1 (sphereDeRhamSymbol r 0 z a) =
      Complex.I • cliffordSymbolParity v 0 b := by
    change exteriorHodgePhaseEquiv C (0 + 1)
      (koszulSymbolParity (sphereDeRhamVector r 0 z) 0 a) = _
    rw [exteriorHodgePhaseEquiv_koszulSymbolParity, hvector]
  -- Reconstruct the same phased even vector from all of its original finite degrees.
  have hb : b.val = ∑ p : {p : Fin (r + 1) // Even p.val}, ((T p.val.val).symm (u p)).val := by
    calc
      b.val = ((complexifiedTangentEvenFormEquiv g z.proj).symm u).val :=
        congrArg Subtype.val ((complexifiedTangentEvenFormEquiv g z.proj).symm_apply_apply b).symm
      _ = _ := complexifiedTangentEvenFormEquiv_symm_coe g z.proj u
  change complexifiedTangentOddFormEquiv g z.proj
      (exteriorHodgePhaseEquiv C 1 (sphereDeRhamSymbol r 0 z a)) =
    fun q ↦ ∑ p, differentialFormHodgeSymbolComponent g p.val.val q.val.val z.proj z.snd (u p)
  rw [hphase]
  funext q
  rw [complexifiedTangentOddFormEquiv_apply]
  let grade (k : ℕ) : Submodule ℂ (ExteriorAlgebra ℂ C) := ⋀[ℂ]^k C
  let H : ExteriorAlgebra ℂ C →ₗ[ℂ] DifferentialFormFiber (n := r) q.val.val z.proj :=
    (T q.val.val).toLinearMap.comp
      ((DirectSum.component ℂ ℕ (fun k ↦ grade k) q.val.val).comp
        (DirectSum.decomposeLinearEquiv grade).toLinearMap)
  change H (Complex.I • (ExteriorAlgebra.ι ℂ v * b.val -
    CliffordAlgebra.contractLeft d b.val)) = _
  rw [hb, Finset.mul_sum, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum, map_sum]
  -- Each homogeneous summand contributes precisely its already established Hodge block.
  apply Finset.sum_congr rfl
  intro p _
  have h := complexifiedTangentExteriorEquiv_hodgeSymbolComponent g p.val.val q.val.val
    z.proj z.snd d hd ((T p.val.val).symm (u p))
  exact h.trans (congrArg
    (differentialFormHodgeSymbolComponent g p.val.val q.val.val z.proj z.snd)
      ((T p.val.val).apply_symm_apply (u p)))

end AtiyahSinger
