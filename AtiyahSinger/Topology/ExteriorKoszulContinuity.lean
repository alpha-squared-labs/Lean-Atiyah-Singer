/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorTopology
public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.ExteriorBundle

/-!
# Continuity of the exterior Koszul operator in a Hermitian bundle

Public module ID: M1844.

Both the positive exterior Koszul operator and the wedge-minus-contraction Clifford
operator are jointly continuous on the original finite-rank bundle and its exterior
algebra bundle. The metric is supplied as continuous Hermitian-form data; its norm
adapter only expresses the already defined fiber operator. Neither total-space topology changes.

The proof uses native linear bundle charts and their exterior charts. The
transformed contraction covector has continuous coefficients obtained by pairing
with the same inverse-chart frame. No orthonormal frame, constant rank, compact
base, positive rank or auxiliary separation hypothesis is required.

Sources: Lawson--Michelsohn, Spin Geometry, Appendix C, for the exterior-symbol
construction; Karoubi, K-Theory, IV.1.4--1.6. The explicit native-topology continuity
argument is a project supplement shared by sphere-symbol boundaries and their
parameter homotopies. A fixed complex phase also gives the Clifford convention used
by the compact and supported Thom boundaries. No Thom isomorphism or K descent is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology exteriorTopology isFiniteRank_exterior
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E)

/-- The positive exterior Koszul operator is continuous for the original bundle topologies. -/
theorem continuous_exteriorMultiplication_add_contraction :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (E x))) ↦
      let core := h.toCore z.proj
      letI : NormedAddCommGroup (E z.proj) := core.toNormedAddCommGroup
      letI : InnerProductSpace ℂ (E z.proj) := InnerProductSpace.ofCore core.toCore
      (⟨z.proj, exteriorMultiplication z.snd.1 z.snd.2 +
        contraction z.snd.1 z.snd.2⟩ :
          TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
  classical
  -- Keep the actual exterior fibers and express contraction by the supplied form.
  let A := fun x ↦ ExteriorAlgebra ℂ (E x)
  let D := TotalSpace Unit (E ×ᵇ A)
  let T := TotalSpace Unit A
  let ell (x : X) (v : E x) : E x →ₗ[ℂ] ℂ :=
    let core := h.toCore x
    letI : NormedAddCommGroup (E x) := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ (E x) := InnerProductSpace.ofCore core.toCore
    innerₛₗ ℂ v
  let F (z : D) : T :=
    ⟨z.proj, ExteriorAlgebra.ι ℂ z.snd.1 * z.snd.2 +
      CliffordAlgebra.contractLeft (ell z.proj z.snd.1) z.snd.2⟩
  change Continuous F
  have hv : Continuous (fun z : D ↦ (⟨z.proj, z.snd.1⟩ : TotalSpace Unit E)) :=
    continuous_sum_fst
  have ha : Continuous (fun z : D ↦ (⟨z.proj, z.snd.2⟩ : T)) := continuous_sum_snd
  have hp : Continuous (fun z : D ↦ z.proj) := (continuous_proj (E := E)).comp hv
  apply continuous_iff_continuousAt.mpr
  intro z
  -- Work over one original linear chart and its specified exterior-algebra chart.
  obtain ⟨n, e, hz, he⟩ := IsFiniteRank.exists_linear_trivialization (E := E) z.proj
  obtain ⟨t, htbase, htlin, htformula⟩ := exists_exterior_trivialization e he
  let V := Fin n → ℂ
  let B := ExteriorAlgebra ℂ V
  let b := (Pi.basisFun ℂ (Fin n)).ExteriorAlgebra.reindex
    (Fintype.equivFin (Finset (Fin n)))
  let c := b.equivFun
  let R : Set D := {w | w.proj ∈ e.baseSet}
  have hR : IsOpen R := e.open_baseSet.preimage hp
  let q (w : R) : X := w.val.proj
  let el (w : R) : E (q w) ≃ₗ[ℂ] V :=
    { toFun := fun v ↦ (e ⟨q w, v⟩).2
      invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' w.property))
        (e.toOpenPartialHomeomorph.symm (q w, v)).snd
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun u : TotalSpace Unit E ↦ u.snd)
          (e.symm_apply_mk_proj (x := ⟨q w, v⟩) (e.mem_source.mpr w.property))
      right_inv := by
        intro v
        have heq := TotalSpace.mk_cast (F := Unit) (E := E)
          (e.proj_symm_apply' (x := v) w.property)
          (e.toOpenPartialHomeomorph.symm (q w, v)).snd
        exact (congrArg (fun u : TotalSpace Unit E ↦ (e u).2) heq).trans
          (congrArg Prod.snd (e.apply_symm_apply' w.property))
      map_add' := (he (q w) w.property).map_add
      map_smul' := (he (q w) w.property).map_smul }
  have hq : Continuous q := hp.comp continuous_subtype_val
  have hvcoord : Continuous (fun w : R ↦ el w w.val.snd.1) := by
    exact (e.toOpenPartialHomeomorph.continuousOn.comp_continuous (hv.comp continuous_subtype_val)
      (fun w ↦ e.mem_source.mpr w.property)).snd
  have hacoord : Continuous (fun w : R ↦ (t ⟨q w, w.val.snd.2⟩).2) := by
    exact (t.toOpenPartialHomeomorph.continuousOn.comp_continuous (ha.comp continuous_subtype_val)
      (fun w ↦ t.mem_source.mpr (htbase.symm ▸ w.property))).snd
  -- Pair with this same inverse-chart frame to obtain continuous dual coefficients.
  have hframe (i : Fin n) : Continuous (fun w : R ↦
      (⟨q w, (el w).symm (Pi.basisFun ℂ (Fin n) i)⟩ : TotalSpace Unit E)) := by
    have hc := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (hq.prodMk (continuous_const (y := Pi.basisFun ℂ (Fin n) i)))
      (fun w ↦ e.mem_target.mpr w.property)
    apply hc.congr
    intro w
    exact (TotalSpace.mk_cast (F := Unit) (E := E)
      (e.proj_symm_apply' w.property) _).symm
  have hcoeff (i : Fin n) : Continuous (fun w : R ↦
      ell (q w) w.val.snd.1 ((el w).symm (Pi.basisFun ℂ (Fin n) i))) := by
    change Continuous (fun w : R ↦ (h.toCore (q w)).inner w.val.snd.1
      ((el w).symm (Pi.basisFun ℂ (Fin n) i)))
    have hc : Continuous (fun w : R ↦
        (⟨q w, (w.val.snd.1, (el w).symm (Pi.basisFun ℂ (Fin n) i))⟩ :
          TotalSpace Unit (E ×ᵇ E))) := by
      apply continuous_induced_rng.mpr
      exact (hv.comp continuous_subtype_val).prodMk (hframe i)
    exact h.continuous_pairing.comp hc
  let d (w : R) : V →L[ℂ] ℂ :=
    ∑ i : Fin n, ell (q w) w.val.snd.1 ((el w).symm (Pi.basisFun ℂ (Fin n) i)) •
      ContinuousLinearMap.proj i
  have hd : Continuous d := by
    apply continuous_finsetSum
    intro i _
    exact (hcoeff i).smul continuous_const
  have hd_eq (w : R) : (d w).toLinearMap =
      (ell (q w) w.val.snd.1).comp (el w).symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    change (∑ i : Fin n, ell (q w) w.val.snd.1 ((el w).symm (Pi.basisFun ℂ (Fin n) i)) •
      ContinuousLinearMap.proj i) v = _
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hv := (Pi.basisFun ℂ (Fin n)).sum_repr v
    conv_rhs => rw [← hv, map_sum, map_sum]
    simp only [map_smul, Pi.basisFun_repr, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  -- On the fixed coordinate space, both operator families are finite-dimensional linear maps.
  let wedge : V →ₗ[ℂ] B →L[ℂ] B :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((Algebra.lmul ℂ B).toLinearMap.comp (ExteriorAlgebra.ι ℂ))
  let contract : (V →L[ℂ] ℂ) →ₗ[ℂ] B →L[ℂ] B :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      (CliffordAlgebra.contractLeft.comp (ContinuousLinearMap.coeLM ℂ))
  have hvec : Continuous (fun w : R ↦ c.symm (t ⟨q w, w.val.snd.2⟩).2) :=
    c.symm.continuous_of_finiteDimensional.comp hacoord
  have hoperator : Continuous (fun w : R ↦
      c (wedge (el w w.val.snd.1) (c.symm (t ⟨q w, w.val.snd.2⟩).2) +
        contract (d w) (c.symm (t ⟨q w, w.val.snd.2⟩).2))) :=
    c.continuous_of_finiteDimensional.comp
      (((wedge.continuous_of_finiteDimensional.comp hvcoord).clm_apply hvec).add
        ((contract.continuous_of_finiteDimensional.comp hd).clm_apply hvec))
  -- Contraction transports by the dual inverse, even when the frame is not isometric.
  have hnatural (w : R) (f : E (q w) →ₗ[ℂ] ℂ) (a : A (q w)) :
      ExteriorAlgebra.map (el w).toLinearMap (CliffordAlgebra.contractLeft f a) =
        CliffordAlgebra.contractLeft (f.comp (el w).symm.toLinearMap)
          (ExteriorAlgebra.map (el w).toLinearMap a) := by
    induction a using CliffordAlgebra.left_induction with
    | algebraMap c => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | ι_mul a v ha =>
      simp only [map_mul, ExteriorAlgebra.map_apply_ι]
      rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul]
      simp only [CliffordAlgebra.contractLeft_ι_mul, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      simp only [map_mul, ExteriorAlgebra.map_apply_ι, ha]
      rfl
  have hext (w : R) (a : A (q w)) :
      (t ⟨q w, a⟩).2 = c (ExteriorAlgebra.map (el w).toLinearMap a) :=
    htformula (q w) w.property a
  -- Identify the coordinate formula with the original operator and glue continuity locally.
  have hFcoord : Continuous (fun w : R ↦ (t (F w.val)).2) := by
    apply hoperator.congr
    intro w
    rw [hext, c.symm_apply_apply]
    rw [hext]
    apply congrArg c
    change ExteriorAlgebra.ι ℂ (el w w.val.snd.1) *
      ExteriorAlgebra.map (el w).toLinearMap w.val.snd.2 +
      CliffordAlgebra.contractLeft (d w).toLinearMap
        (ExteriorAlgebra.map (el w).toLinearMap w.val.snd.2) =
      ExteriorAlgebra.map (el w).toLinearMap
        (ExteriorAlgebra.ι ℂ w.val.snd.1 * w.val.snd.2 +
          CliffordAlgebra.contractLeft (ell (q w) w.val.snd.1) w.val.snd.2)
    rw [map_add, map_mul, ExteriorAlgebra.map_apply_ι, hnatural, hd_eq]
    rfl
  have hlocal : ContinuousOn (fun w : D ↦ (t (F w)).2) R := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hFcoord
  apply t.continuousAt_of_comp_left (f := F) hp.continuousAt (htbase.symm ▸ hz)
  have hpfirst : ∀ᶠ w in nhds z, (t (F w)).1 = w.proj := by
    filter_upwards [hR.mem_nhds hz] with w hw
    exact t.proj_toFun _ (t.mem_source.mpr (htbase.symm ▸ hw))
  have htfirst := hp.continuousAt.congr_of_eventuallyEq hpfirst
  exact htfirst.prodMk (hlocal.continuousAt (hR.mem_nhds hz))

/-- The negative-contraction Clifford operator is continuous in the original bundle topology. -/
theorem continuous_cliffordSymbol
    (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2)) :
    Continuous (fun z : TotalSpace Unit (E ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (E x))) ↦
      (⟨z.proj, cliffordSymbol z.snd.1 z.snd.2⟩ :
        TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
  let A := fun x ↦ ExteriorAlgebra ℂ (E x)
  let D := TotalSpace Unit (E ×ᵇ A)
  -- Scalar multiplication is continuous for each original finite-rank total topology.
  have hscale (F : X → Type _) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F] (c : ℂ) :
      Continuous (fun z : TotalSpace Unit F ↦
        (⟨z.proj, c • z.snd⟩ : TotalSpace Unit F)) := by
    let p : C(TotalSpace Unit F, X) := ⟨π Unit F, continuous_proj⟩
    let : IsFiniteRank ((p : TotalSpace Unit F → X) *ᵖ F) := isFiniteRank_pullback p
    have hv : Continuous (fun z : TotalSpace Unit F ↦
        (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit F → X) *ᵖ F))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact continuous_id.prodMk continuous_id
    exact (Pullback.continuous_lift Unit F p).comp
      (continuous_smul_section _ (ContinuousMap.const _ c) _ hv)
  -- A fixed complex phase changes the positive Koszul symbol into the original
  -- wedge-minus-contraction symbol, using the very same Hermitian form.
  have hpositive := continuous_exteriorMultiplication_add_contraction E
    (ContinuousHermitianMetric.ofInnerProduct E hinner)
  have hrotate : Continuous (fun z : D ↦
      (⟨z.proj, (Complex.I • z.snd.1, z.snd.2)⟩ : D)) := by
    apply continuous_induced_rng.mpr
    exact ((hscale E Complex.I).comp continuous_sum_fst).prodMk continuous_sum_snd
  apply ((hscale A (-Complex.I)).comp (hpositive.comp hrotate)).congr
  intro z
  simp [exteriorMultiplication, contraction, cliffordSymbol, innerₛₗ, map_smul,
    smul_add, smul_smul, sub_eq_add_neg]
  abel

end AtiyahSinger.ComplexBundle
