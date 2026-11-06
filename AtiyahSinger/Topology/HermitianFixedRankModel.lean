/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFlagBundle

/-!
# Native fixed-rank models on the original Hermitian bundle

Public module ID: M1881.

On a constant-rank piece of an original locally finite-rank complex bundle,
the supplied continuous positive Hermitian form gives fiber norms. Retyping the
same total-space points and vectors gives the native fixed-model topology.
The native local charts are chosen only after their existence has been proved
for that exact topology and those exact fibers. Their continuous linear
transitions supply the native vector-bundle certificate.

This adapter chooses no replacement bundle or flag. Its purpose is to apply the
existing flag construction on actual clopen rank strata. It does not claim that
a chosen continuous chart atlas is compatible with a separate smooth atlas.
Sources: Husemoller III.9.2/9.5 for Hermitian metrics and local orthonormal frames;
SG III.11.1 and Hatcher VBKT 3.3 for the subsequent flag construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- Retype the original total-space topology without changing any base point or fiber vector. -/
@[reducible]
def nativeModelTopology (V : Type*) : TopologicalSpace (TotalSpace V E) :=
  TopologicalSpace.induced
    (fun z : TotalSpace V E ↦ (⟨z.proj, z.snd⟩ : TotalSpace Unit E)) inferInstance

/-- The actual identity-on-vectors homeomorphism to the original Unit total space. -/
def nativeModelTotalHomeomorph (V : Type*) :
    letI := nativeModelTopology E V
    TotalSpace V E ≃ₜ TotalSpace Unit E :=
  letI := nativeModelTopology E V
  Equiv.toHomeomorphOfIsInducing
    { toFun := fun z ↦ ⟨z.proj, z.snd⟩
      invFun := fun z ↦ ⟨z.proj, z.snd⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    ⟨rfl⟩

namespace ContinuousHermitianMetric

variable {E} (h : ContinuousHermitianMetric E)

/-- The normed additive structure determined by the supplied original positive form. -/
@[reducible]
def fiberNormedAddCommGroup (x : X) : NormedAddCommGroup (E x) :=
  (h.toCore x).toNormedAddCommGroup

/-- The original complex form gives the inner product for its own induced fiber norm. -/
@[reducible]
def fiberInnerProductSpace (x : X) :
    letI := h.fiberNormedAddCommGroup x
    InnerProductSpace ℂ (E x) :=
  letI := h.fiberNormedAddCommGroup x
  InnerProductSpace.ofCore (h.toCore x).toCore

/-- Local linear frames give a native vector-bundle atlas on the unchanged total topology. -/
theorem exists_nativeFiberBundle [IsFiniteRank E] (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    ∃ b : FiberBundle (EuclideanSpace ℂ (Fin r)) E,
      letI := b
      VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E := by
  /- Stage 1: choose an original finite linear trivialization near each base
  point. Its coordinate dimension is r by hr. Reindex these finite coordinates
  into the fixed Euclidean model, and retype only the total-space phantom model.
  The forward and inverse maps still act on precisely the original vectors.
  Stage 2: in each fiber, the chosen coordinate linear bijection is continuous
  for the h-induced norm by finite dimension. Its inverse is continuous as well.
  Compare this same linear homeomorphism with the chart's homeomorphism from
  the original topological fiber to the model. The fiber inclusion is inducing
  for exactly the h-induced norm; no additional local norm estimates or
  replacement fiber topology are needed.
  Stage 3: use all complex-linear charts on this native topology as the atlas,
  choosing the charts from Stage 1 to cover the base. On overlaps the original
  chart composition is continuous at every fixed model vector. Finite dimension
  promotes this to continuous-linear-map-valued continuity. This is
  the native VectorBundle condition. The construction includes rank zero and
  an empty base, and needs neither a global frame nor a global rank bound on
  unrelated bundles. It selects chart data, not a new bundle topology. -/
  classical
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let V := EuclideanSpace ℂ (Fin r)
  let := nativeModelTopology E V
  -- Retype original charts and their fixed coordinates, keeping every underlying vector.
  have hcharts (x : X) : ∃ e : Trivialization V (π V E),
      x ∈ e.baseSet ∧ e.IsLinear ℂ := by
    obtain ⟨n, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
    let l : E x ≃ₗ[ℂ] (Fin n → ℂ) :=
      { toFun := fun v ↦ (e ⟨x, v⟩).2
        invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hx))
          (e.toOpenPartialHomeomorph.symm (x, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
            (e.symm_apply_mk_proj (x := ⟨x, v⟩) (e.mem_source.mpr hx))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E)
            (e.proj_symm_apply' (x := v) hx) (e.toOpenPartialHomeomorph.symm (x, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
            (congrArg Prod.snd (e.apply_symm_apply' hx))
        map_add' := (hlinear x hx).map_add
        map_smul' := (hlinear x hx).map_smul }
    have hdim : Module.finrank ℂ (E x) = n := by simpa using l.finrank_eq
    have hn : n = r := hdim.symm.trans (hr x)
    clear hdim
    subst n
    let c : (Fin r → ℂ) ≃L[ℂ] V := (EuclideanSpace.equiv (Fin r) ℂ).symm
    let e' : Trivialization V (π V E) :=
      (e.transFiberHomeomorph c.toHomeomorph).compHomeomorph (nativeModelTotalHomeomorph E V)
    refine ⟨e', hx, ⟨?_⟩⟩
    intro y hy
    constructor
    · intro v w
      change c (e ⟨y, v + w⟩).2 = c (e ⟨y, v⟩).2 + c (e ⟨y, w⟩).2
      rw [(hlinear y hy).map_add, map_add]
    · intro a v
      change c (e ⟨y, a • v⟩).2 = a • c (e ⟨y, v⟩).2
      rw [(hlinear y hy).map_smul, map_smul]
  choose chart hchart hlinear using hcharts
  -- The metric norm gives precisely the topology of each original fiber inclusion.
  have hmk (x : X) : Topology.IsInducing (@TotalSpace.mk X V E x) := by
    let := hlinear x
    let c : E x ≃L[ℂ] V :=
      ((chart x).linearEquivAt ℂ x (hchart x)).toContinuousLinearEquiv
    let f : E x → ((π V E) ⁻¹' ({x} : Set X)) := fun v ↦ ⟨⟨x, v⟩, rfl⟩
    have hf : Topology.IsInducing f := by
      apply ((chart x).preimageSingletonHomeomorph (hchart x)).isInducing.of_comp_iff.mp
      exact c.toHomeomorph.isInducing
    exact Topology.IsInducing.subtypeVal.comp hf
  let b : FiberBundle V E :=
    { totalSpaceMk_isInducing' := hmk
      trivializationAtlas' := {e | e.IsLinear ℂ}
      trivializationAt' := chart
      mem_baseSet_trivializationAt' := hchart
      trivialization_mem_atlas' := hlinear }
  refine ⟨b, ?_⟩
  let := b
  refine { trivialization_linear' := fun e he ↦ he.out, continuousOn_coordChange' := ?_ }
  intro e e' he he'
  let : e.IsLinear ℂ := he.out
  let : e'.IsLinear ℂ := he'.out
  -- In the finite-dimensional model, continuous operator families are detected on vectors.
  apply continuousOn_clm_apply.mpr
  intro v
  have hin : ContinuousOn (fun y : X ↦ (y, v)) (e.baseSet ∩ e'.baseSet) :=
    continuousOn_id.prodMk continuousOn_const
  have hback := e.continuousOn_symm.comp hin fun y hy ↦ ⟨hy.1, Set.mem_univ v⟩
  have hout := e'.continuousOn.comp hback fun y hy ↦ by
    apply e'.mem_source.mpr
    exact hy.2
  apply hout.snd.congr
  intro y hy
  exact e.coordChangeL_apply e' hy v

/-- Choose native chart data only from existence on the fixed original topology. -/
@[reducible]
def nativeFiberBundle [IsFiniteRank E] (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    FiberBundle (EuclideanSpace ℂ (Fin r)) E :=
  (h.exists_nativeFiberBundle r hr).choose

set_option linter.defProp false in
/-- The chosen original native atlas has the specified complex-linear transitions. -/
@[reducible]
def nativeVectorBundle [IsFiniteRank E] (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    letI := h.nativeFiberBundle r hr
    VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E :=
  (h.exists_nativeFiberBundle r hr).choose_spec

set_option linter.unusedSectionVars false in
/-- Going to the native phantom model and back recovers the exact original total topology. -/
theorem modelTopology_nativeModelTopology (r : ℕ) :
    let t := (inferInstance : TopologicalSpace (TotalSpace Unit E))
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    modelTopology (EuclideanSpace ℂ (Fin r)) E = t := by
  /- Both induced topologies use the inverse identity-on-vectors retypings.
  Composition of induced topologies is induction along the composite map,
  and their composite is the literal identity on the original Unit total space.
  Thus the equality is of the full original topology, not only of continuous
  section predicates or an unspecified homeomorphic replacement. -/
  dsimp only [modelTopology, nativeModelTopology]
  rw [induced_compose]
  exact induced_id

/-- The original pairing stays continuous after the two inverse phantom-model retypings. -/
theorem continuous_nativeModel_pairing (r : ℕ) :
    let form := h.toCore
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := sumTopology (E := E) (F := E)
    Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦
      (form z.proj).inner z.snd.1 z.snd.2) := by
  /- The two inverse identity-on-vectors retypings recover the full original
  total topology by modelTopology_nativeModelTopology. After substituting
  this equality, the same-base sum topology and pairing are the original
  ones, so h.continuous_pairing gives the displayed continuity directly. -/
  have ht := modelTopology_nativeModelTopology (E := E) r
  dsimp only at ht ⊢
  rw [ht]
  exact h.continuous_pairing

/-- The original Hermitian form, retyped for the native flag constructor. -/
def nativeModelMetric (r : ℕ) :
    letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E :=
  let form := h.toCore
  let hc := h.continuous_nativeModel_pairing r
  let ht := modelTopology_nativeModelTopology (E := E) r
  let hfinite := h.isFiniteRank
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  { toCore := form
    continuous_pairing := hc
    isFiniteRank := by
      -- Transport local linear triviality along the equality of the original total topologies.
      dsimp only at ht
      exact Eq.mpr
        (congrArg (fun t : TopologicalSpace (TotalSpace Unit E) ↦
          @IsFiniteRank X _ E _ _ t) ht) hfinite }

end ContinuousHermitianMetric

end AtiyahSinger.ComplexBundle
