/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KZeroFunctor
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Continuous sections and the topological Serre-Swan theorem

Public module ID: M2114.

The standard finite-rank bundle condition is expressed using
mathlib's actual local trivializations, permitting the model dimension to vary with
the base point. The phantom parameter `Unit` in `Bundle.TotalSpace` fixes one total
space while local trivializations use different finite-dimensional complex fibers.
It is not the dimension or the fiber of the bundle.

On a compact Hausdorff base, the section construction is fully faithful and
identifies finite-rank bundles with finite projective modules, realized by
idempotent image bundles. The bundle condition is local linear triviality;
finite projectivity and the equivalence follow from the finite dual-frame
and idempotent-image constructions below.

Sources: Karoubi I.6 and Wikipedia, Serre-Swan theorem, Topology.
No connectedness, smoothness, metric, or constant global rank is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

namespace ComplexBundle

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- A finite-rank continuous complex vector bundle, allowing locally varying rank.
Each point has an open linear trivialization with some finite-dimensional complex fiber. -/
class IsFiniteRank : Prop where
  /-- Local linear trivializations cover the base; their ranks need not agree globally. -/
  exists_linear_trivialization :
    ∀ x : X, ∃ (r : ℕ) (e : Trivialization (Fin r → ℂ) (π Unit E)),
      x ∈ e.baseSet ∧ ∀ y ∈ e.baseSet,
        IsLinearMap ℂ (fun v : E y ↦ (e ⟨y, v⟩).2)

/-- Scalar action on a fiber by evaluating a continuous scalar function at its base point. -/
@[instance_reducible]
def sectionModule (x : X) : Module C(X, ℂ) (E x) :=
  Module.compHom (E x) (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom

attribute [local instance] sectionModule

variable [IsFiniteRank E]

/-- Local linear triviality makes the zero section continuous. -/
theorem continuous_zero_section :
    Continuous (fun x : X ↦ (⟨x, 0⟩ : TotalSpace Unit E)) := by
  /- In each linear trivialization this section is x ↦ (x,0), which is continuous.
  The open base sets cover X, so continuity follows locally at every point. -/
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  -- The original linear chart takes the zero section to the zero coordinate vector.
  apply e.continuousAt_of_comp_left
    (f := fun y ↦ (⟨y, 0⟩ : TotalSpace Unit E)) continuousAt_id hx
  apply (continuousAt_id.prodMk (continuousAt_const (y := (0 : Fin r → ℂ)))).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact Prod.ext (e.proj_toFun ⟨y, 0⟩ (e.mem_source.mpr hy)) (hlinear y hy).map_zero

/-- The sum of two continuous sections is continuous. -/
theorem continuous_add_section (s t : ∀ x, E x)
    (hs : Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E)))
    (ht : Continuous (fun x ↦ (⟨x, t x⟩ : TotalSpace Unit E))) :
    Continuous (fun x ↦ (⟨x, s x + t x⟩ : TotalSpace Unit E)) := by
  /- Around any base point choose one linear trivialization. The fiber coordinate
  of s+t is the sum of the coordinates of s and t. Addition in ℂ^r is continuous;
  transport through the inverse chart and use the open cover. -/
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  -- Both sections use the same chart and therefore the same coordinate addition.
  have hs' := (e.continuousAt (e.mem_source.mpr hx)).comp hs.continuousAt
  have ht' := (e.continuousAt (e.mem_source.mpr hx)).comp ht.continuousAt
  apply e.continuousAt_of_comp_left
    (f := fun y ↦ (⟨y, s y + t y⟩ : TotalSpace Unit E)) continuousAt_id hx
  apply (continuousAt_id.prodMk (hs'.snd.add ht'.snd)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact Prod.ext (e.proj_toFun ⟨y, s y + t y⟩ (e.mem_source.mpr hy))
    ((hlinear y hy).map_add (s y) (t y))

/-- Multiplying a continuous section by a continuous scalar function is continuous. -/
theorem continuous_smul_section (c : C(X, ℂ)) (s : ∀ x, E x)
    (hs : Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E))) :
    Continuous (fun x ↦ (⟨x, c x • s x⟩ : TotalSpace Unit E)) := by
  /- In a linear trivialization the fiber coordinate is c(x) times the coordinate
  of s(x). Joint continuity of complex scalar multiplication gives the assertion
  locally, and the trivializing neighborhoods cover X. -/
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨r, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  have hs' := (e.continuousAt (e.mem_source.mpr hx)).comp hs.continuousAt
  -- Linearity is over the actual complex fibers; the scalar is evaluated at this base point.
  apply e.continuousAt_of_comp_left
    (f := fun y ↦ (⟨y, c y • s y⟩ : TotalSpace Unit E)) continuousAt_id hx
  apply (continuousAt_id.prodMk (c.continuous.continuousAt.smul hs'.snd)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  exact Prod.ext (e.proj_toFun ⟨y, c y • s y⟩ (e.mem_source.mpr hy))
    ((hlinear y hy).map_smul (c y) (s y))

/-- The actual C(X,ℂ)-module of continuous sections, as a submodule of all sections. -/
def continuousSections : Submodule C(X, ℂ) (∀ x, E x) where
  carrier := {s | Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E))}
  zero_mem' := continuous_zero_section E
  add_mem' := fun hs ht ↦ continuous_add_section E _ _ hs ht
  smul_mem' := fun c _ hs ↦ continuous_smul_section E c _ hs

variable [CompactSpace X] [T2Space X]

/-- A finite continuous dual frame reconstructs every vector in its original fiber.
This standard partition-of-unity construction supplies the shared finite dual-basis
criterion for the three Serre-Swan statements below. Both weights are square roots
of the same partition function; no metric or global constant rank is chosen. -/
private theorem exists_finite_dual_frame :
    ∃ (n : ℕ) (s : Fin n → continuousSections E)
      (l : ∀ (_i : Fin n) (x : X), E x →ₗ[ℂ] ℂ),
      (∀ i, Continuous (fun z : TotalSpace Unit E ↦ l i z.proj z.snd)) ∧
      ∀ (x : X) (v : E x), ∑ i, l i x v • (s i).val x = v := by
  classical
  -- Choose a finite subcover of the original linear charts, retaining their individual ranks.
  choose r e he hlinear using (IsFiniteRank.exists_linear_trivialization (E := E))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, he x⟩)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : t ↦ (e i.val).baseSet) (fun i ↦ (e i.val).open_baseSet) (by
      intro x _
      obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩)
  have hbase : Continuous (π Unit E) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (e z.proj).continuousAt_proj ((e z.proj).mem_source.mpr (he z.proj))
  -- The inverse coordinate maps retain the transport supplied by each actual chart.
  let coord (i : t) (x : X) (hx : x ∈ (e i.val).baseSet) :
      E x ≃ₗ[ℂ] (Fin (r i.val) → ℂ) :=
    { toFun := fun v ↦ ((e i.val) ⟨x, v⟩).2
      invFun := fun w ↦ cast (congrArg E ((e i.val).proj_symm_apply' hx))
        ((e i.val).toOpenPartialHomeomorph.symm (x, w)).2
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.2)
          ((e i.val).symm_apply_mk_proj (x := ⟨x, v⟩) ((e i.val).mem_source.mpr hx))
      right_inv := by
        intro w
        have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
          ((e i.val).proj_symm_apply' (x := w) hx)
          ((e i.val).toOpenPartialHomeomorph.symm (x, w)).2
        exact (congrArg (fun z : TotalSpace Unit E ↦ ((e i.val) z).2) hpoint).trans
          (congrArg Prod.snd ((e i.val).apply_symm_apply' hx))
      map_add' := (hlinear i.val x hx).map_add
      map_smul' := (hlinear i.val x hx).map_smul }
  let w (i : t) : C(X, ℂ) :=
    ⟨fun x ↦ (Real.sqrt (ρ i x) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (ρ i).continuous)⟩
  have hwzero (i : t) (x : X) (hx : x ∉ tsupport (ρ i)) : w i x = 0 := by
    simp only [w, ContinuousMap.coe_mk, image_eq_zero_of_notMem_tsupport hx,
      Real.sqrt_zero, Complex.ofReal_zero]
  have hwsq (i : t) (x : X) : w i x * w i x = (ρ i x : ℂ) := by
    change (Real.sqrt (ρ i x) : ℂ) * (Real.sqrt (ρ i x) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ρ.nonneg i x)]
  let I := (i : t) × Fin (r i.val)
  let sval (a : I) (x : X) : E x :=
    if hx : x ∈ (e a.1.val).baseSet then
      (coord a.1 x hx).symm (w a.1 x • Pi.single a.2 (1 : ℂ)) else 0
  have hs (a : I) : Continuous (fun x ↦ (⟨x, sval a x⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ (e a.1.val).baseSet
    · -- Inside the original chart the weighted basis vector is an ordinary continuous vector.
      apply (e a.1.val).continuousAt_of_comp_left
        (f := fun y ↦ (⟨y, sval a y⟩ : TotalSpace Unit E)) continuousAt_id hx
      have hweight : ContinuousAt
          (fun y ↦ w a.1 y • Pi.single a.2 (1 : ℂ)) x :=
        (w a.1).continuous.continuousAt.smul continuousAt_const
      apply (continuousAt_id.prodMk hweight).congr_of_eventuallyEq
      filter_upwards [(e a.1.val).open_baseSet.mem_nhds hx] with y hy
      refine Prod.ext ((e a.1.val).proj_toFun ⟨y, sval a y⟩
        ((e a.1.val).mem_source.mpr hy)) ?_
      change coord a.1 y hy (sval a y) = _
      simp only [sval, dite_eq_left hy, LinearEquiv.apply_symm_apply]
    · -- Closed support containment makes the zero extension locally identically zero.
      have hxs : x ∉ tsupport (ρ a.1) := fun h ↦ hx (hρ a.1 h)
      apply (continuous_zero_section E).continuousAt.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (ρ a.1)).isOpen_compl.mem_nhds hxs] with y hy
      change (⟨y, sval a y⟩ : TotalSpace Unit E) = ⟨y, 0⟩
      congr 1
      simp only [sval, hwzero a.1 y hy, zero_smul, map_zero, dite_eq_ite, ite_self]
  let s (a : I) : continuousSections E := ⟨sval a, hs a⟩
  let l (a : I) (x : X) : E x →ₗ[ℂ] ℂ :=
    if hx : x ∈ (e a.1.val).baseSet then
      w a.1 x • ((LinearMap.proj a.2).comp (coord a.1 x hx).toLinearMap) else 0
  have hl (a : I) : Continuous (fun z : TotalSpace Unit E ↦ l a z.proj z.snd) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z.proj ∈ (e a.1.val).baseSet
    · have hcoord := (continuous_apply a.2).continuousAt.comp
        (((e a.1.val).continuousAt ((e a.1.val).mem_source.mpr hz)).snd)
      have hweight : ContinuousAt (fun y : TotalSpace Unit E ↦ w a.1 y.proj) z :=
        ((w a.1).continuous.comp hbase).continuousAt
      apply (hweight.mul hcoord).congr_of_eventuallyEq
      filter_upwards [hbase.continuousAt.preimage_mem_nhds
        ((e a.1.val).open_baseSet.mem_nhds hz)] with y hy
      change y.proj ∈ (e a.1.val).baseSet at hy
      simp only [l, dite_eq_left hy, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearMap.proj_apply, smul_eq_mul]
      rfl
    · have hzs : z.proj ∉ tsupport (ρ a.1) := fun h ↦ hz (hρ a.1 h)
      apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hbase.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport (ρ a.1)).isOpen_compl.mem_nhds hzs)] with y hy
      simp only [l, hwzero a.1 y.proj hy, zero_smul, dite_eq_ite, ite_self,
        LinearMap.zero_apply]
  have hreconstruct (x : X) (v : E x) : ∑ a : I, l a x v • (s a).val x = v := by
    -- The two square-root weights multiply to the original partition weight.
    have hblock (i : t) :
        ∑ j : Fin (r i.val), l ⟨i, j⟩ x v • (s ⟨i, j⟩).val x = (ρ i x : ℂ) • v := by
      by_cases hx : x ∈ (e i.val).baseSet
      · have hcoordinates :
            ∑ j : Fin (r i.val), (coord i x hx v) j • Pi.single j (1 : ℂ) =
              coord i x hx v := by
          ext j
          simp [Pi.single_apply]
        calc
          _ = (coord i x hx).symm
              (∑ j : Fin (r i.val), (w i x * w i x) •
                ((coord i x hx v) j • Pi.single j (1 : ℂ))) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp only [l, s, sval, dite_eq_left hx, LinearMap.smul_apply,
              LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.proj_apply,
              map_smul, smul_smul, smul_eq_mul]
            congr 1
            ring
          _ = (coord i x hx).symm ((ρ i x : ℂ) • coord i x hx v) := by
            rw [hwsq, ← Finset.smul_sum, hcoordinates]
          _ = (ρ i x : ℂ) • v := by rw [map_smul, LinearEquiv.symm_apply_apply]
      · have hzero : ρ i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ i h))
        simp only [l, s, sval, dite_eq_right hx, LinearMap.zero_apply, zero_smul,
          Finset.sum_const_zero, hzero, Complex.ofReal_zero]
    rw [Fintype.sum_sigma]
    simp_rw [hblock]
    rw [← Finset.sum_smul]
    have hsum : ∑ i : t, ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_smul]
  -- Reindex the finite disjoint union of the local coordinate sets by a single Fin n.
  let index := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i ↦ s (index i), fun i ↦ l (index i),
    fun i ↦ hl (index i), ?_⟩
  intro x v
  exact (index.sum_comp (fun a ↦ l a x v • (s a).val x)).trans (hreconstruct x v)

/-- Serre-Swan, finite generation of continuous sections on a compact Hausdorff base. -/
theorem finite_continuousSections : Module.Finite C(X, ℂ) (continuousSections E) := by
  /- A finite continuous dual frame gives global sections s_i and continuous
  fiberwise linear functionals l_i with v = sum_i l_i(v) s_i at each base point.
  Applying the same functionals to a continuous section gives continuous scalar
  coefficients, so every section lies in the image of one finite free module.
  This explicit reconstruction proves generation without selecting a metric. -/
  classical
  obtain ⟨n, s, l, hl, hreconstruct⟩ := exists_finite_dual_frame E
  -- The finite global frame gives a map from the original finite free section module.
  let assemble := Fintype.linearCombination C(X, ℂ) s
  apply Module.Finite.of_surjective assemble
  intro a
  let c (i : Fin n) : C(X, ℂ) :=
    ⟨fun x ↦ l i x (a.val x), (hl i).comp a.property⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext x
  change (∑ i, c i • s i).val x = a.val x
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  exact hreconstruct x (a.val x)

/-- Serre-Swan, projectivity of continuous sections on a compact Hausdorff base. -/
theorem projective_continuousSections : Module.Projective C(X, ℂ) (continuousSections E) := by
  /- Use the same finite dual-frame construction as for finite generation.
  Its coordinate functionals give a C(X,ℂ)-linear map from sections to a finite
  free module. Reconstruction from the global frame is a left inverse to that
  coordinate map. The section module is therefore a direct summand of a finite
  free module. The original locally varying ranks require no uniform rank choice. -/
  classical
  obtain ⟨n, s, l, hl, hreconstruct⟩ := exists_finite_dual_frame E
  -- The continuous dual coordinates define a module-linear section of finite reconstruction.
  let coordinates : continuousSections E →ₗ[C(X, ℂ)] (Fin n → C(X, ℂ)) :=
    { toFun := fun a i ↦ ⟨fun x ↦ l i x (a.val x), (hl i).comp a.property⟩
      map_add' := by
        intro a b
        ext i x
        exact (l i x).map_add (a.val x) (b.val x)
      map_smul' := by
        intro c a
        ext i x
        exact (l i x).map_smul (c x) (a.val x) }
  let assemble := Fintype.linearCombination C(X, ℂ) s
  apply Module.Projective.of_split coordinates assemble
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext x
  change (∑ i, coordinates a i • s i).val x = a.val x
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  exact hreconstruct x (a.val x)

variable (F : X → Type*) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- Serre-Swan, full faithfulness in explicit fiber-map form.
Every module homomorphism is induced by a unique continuous fiberwise complex-linear map. -/
theorem existsUnique_bundleMap_of_sectionMap
    (Φ : continuousSections E →ₗ[C(X, ℂ)] continuousSections F) :
    ∃! τ : ∀ x, E x →ₗ[ℂ] F x,
      Continuous (fun z : TotalSpace Unit E ↦
        (⟨z.proj, τ z.proj z.snd⟩ : TotalSpace Unit F)) ∧
      ∀ (s : continuousSections E) (x : X), τ x (s.val x) = (Φ s).val x := by
  /- Choose a finite continuous dual frame (s_i,l_i) for the original source
  bundle. Define the fiber map by v mapped to sum_i l_i(v) Φ(s_i). In an original
  target chart this finite sum is continuous on the source total space. The exact
  global section reconstruction and C(X,ℂ)-linearity of Φ prove that this map
  induces Φ. Fiber reconstruction also forces uniqueness. No topology or
  boundedness condition on the module homomorphism is added. -/
  classical
  obtain ⟨n, s, l, hl, hreconstruct⟩ := exists_finite_dual_frame E
  -- Apply the given module map to the same finite frame used for fiber reconstruction.
  let τ (x : X) : E x →ₗ[ℂ] F x :=
    ∑ i, (l i x).smulRight ((Φ (s i)).val x)
  have hτ (x : X) (v : E x) :
      τ x v = ∑ i, l i x v • (Φ (s i)).val x := by
    simp only [τ, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hbase : Continuous (π Unit E) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨r, e, hz, _⟩ := IsFiniteRank.exists_linear_trivialization (E := E) z.proj
    exact e.continuousAt_proj (e.mem_source.mpr hz)
  have hcontinuous : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, τ z.proj z.snd⟩ : TotalSpace Unit F)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨r, e, hz, hlinear⟩ :=
      IsFiniteRank.exists_linear_trivialization (E := F) z.proj
    -- In one original target chart, this is a finite sum of continuous scalar-vector products.
    have hcoords : ContinuousAt (fun y : TotalSpace Unit E ↦
        ∑ i, l i y.proj y.snd • (e ⟨y.proj, (Φ (s i)).val y.proj⟩).2) z := by
      apply tendsto_finsetSum
      intro i _
      have hsection := (Φ (s i)).property.comp hbase
      have hchart := (e.continuousAt (e.mem_source.mpr hz)).comp hsection.continuousAt
      exact (hl i).continuousAt.smul hchart.snd
    apply e.continuousAt_of_comp_left
      (f := fun y : TotalSpace Unit E ↦ (⟨y.proj, τ y.proj y.snd⟩ : TotalSpace Unit F))
      hbase.continuousAt hz
    apply (hbase.continuousAt.prodMk hcoords).congr_of_eventuallyEq
    filter_upwards [hbase.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hz)] with y hy
    change y.proj ∈ e.baseSet at hy
    refine Prod.ext (e.proj_toFun ⟨y.proj, τ y.proj y.snd⟩ (e.mem_source.mpr hy)) ?_
    let eLin : F y.proj →ₗ[ℂ] (Fin r → ℂ) :=
      { toFun := fun v ↦ (e ⟨y.proj, v⟩).2
        map_add' := (hlinear y.proj hy).map_add
        map_smul' := (hlinear y.proj hy).map_smul }
    change eLin (τ y.proj y.snd) = _
    rw [hτ, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact eLin.map_smul _ _
  have himplements (a : continuousSections E) (x : X) :
      τ x (a.val x) = (Φ a).val x := by
    let c (i : Fin n) : C(X, ℂ) :=
      ⟨fun y ↦ l i y (a.val y), (hl i).comp a.property⟩
    have ha : ∑ i, c i • s i = a := by
      apply Subtype.ext
      funext y
      simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
      exact hreconstruct y (a.val y)
    -- Module linearity transports the exact section identity, so no boundedness is assumed for Φ.
    have hΦ := congrArg (fun b : continuousSections F ↦ b.val x) (congrArg Φ ha)
    simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply] at hΦ
    exact (hτ x (a.val x)).trans hΦ
  refine ⟨τ, ⟨hcontinuous, himplements⟩, ?_⟩
  intro σ hσ
  funext x
  apply LinearMap.ext
  intro v
  -- Every original fiber vector has the same finite frame expansion, which forces uniqueness.
  calc
    σ x v = σ x (∑ i, l i x v • (s i).val x) := by rw [hreconstruct]
    _ = ∑ i, l i x v • σ x ((s i).val x) := by simp only [map_sum, map_smul]
    _ = ∑ i, l i x v • (Φ (s i)).val x := by simp only [hσ.2]
    _ = τ x v := (hτ x v).symm

end ComplexBundle

namespace IdempotentMatrix

variable {X : Type*} [TopologicalSpace X] (p : IdempotentMatrix C(X, ℂ))

/-- The fiber of a continuous idempotent image bundle. -/
def fiber (x : X) : Submodule ℂ (Fin p.size → ℂ) :=
  (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).image

/-- The image bundle inherits its topology from X × ℂ^N, not a disjoint-union topology. -/
@[instance_reducible]
def fiberTotalSpaceTopology : TopologicalSpace (TotalSpace Unit (fun x ↦ p.fiber x)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦ (z.proj, z.snd.val)) inferInstance

attribute [local instance] fiberTotalSpaceTopology

open scoped Matrix Matrix.Norms.Operator in
/-- A continuous idempotent has a locally trivial finite-rank image bundle. -/
theorem isFiniteRank_fiber : ComplexBundle.IsFiniteRank (fun x ↦ p.fiber x) := by
  /- At a fixed base point choose a basis for im p(x₀). For y near x₀, the explicit
  intertwiner 1-p(y)-p(x₀)+2p(y)p(x₀) is invertible and identifies im p(x₀) with im p(y).
  These continuous identifications and their inverses give a local linear trivialization
  in the subspace topology. Its rank is dim im p(x₀), and no global rank is prescribed. -/
  classical
  constructor
  intro x₀
  let A (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  have hA : Continuous A := continuous_pi fun i ↦
    continuous_pi fun j ↦ (p.matrix i j).continuous
  have hAA (x : X) : A x * A x = A x :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  -- The same polynomial intertwines the original moving and fixed projections.
  let T (x : X) := idempotentIntertwiner (A x) (A x₀)
  have hT : Continuous T := by
    unfold T idempotentIntertwiner
    fun_prop
  have hT₀ : T x₀ = 1 := by
    dsimp only [T, idempotentIntertwiner]
    noncomm_ring [hAA x₀]
  have hcomm (x : X) : T x * A x₀ = A x * T x :=
    idempotentIntertwiner_mul (A x) (A x₀) (hAA x) (hAA x₀)
  let U : Set X := {x | ‖T x - 1‖ < 1}
  have hopen : IsOpen U := isOpen_lt ((hT.sub continuous_const).norm) continuous_const
  have hx₀ : x₀ ∈ U := by
    change ‖T x₀ - 1‖ < 1
    rw [hT₀, sub_self, norm_zero]
    exact zero_lt_one
  have hunit (x : X) (hx : x ∈ U) : IsUnit (T x) :=
    isUnit_idempotentIntertwiner_of_norm_lt (A x) (A x₀) hx
  let L (x : X) := Ring.inverse (T x)
  have hLT (x : X) (hx : x ∈ U) : L x * T x = 1 :=
    Ring.inverse_mul_cancel (T x) (hunit x hx)
  have hTL (x : X) (hx : x ∈ U) : T x * L x = 1 :=
    Ring.mul_inverse_cancel (T x) (hunit x hx)
  have hL : Continuous (fun x : U ↦ L x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    obtain ⟨u, hu⟩ := hunit x.val x.property
    have hinverse := NormedRing.inverse_continuousAt u
    rw [hu] at hinverse
    exact hinverse.comp_of_eq ((hT.comp continuous_subtype_val).continuousAt) rfl
  -- Use the fixed image as an intermediate model, keeping every actual fiber as a subtype.
  let back (x : X) : (Fin p.size → ℂ) →ₗ[ℂ] p.fiber x₀ :=
    (A x₀).mulVecLin.rangeRestrict.comp (L x).mulVecLin
  let front (x : X) : p.fiber x₀ →ₗ[ℂ] p.fiber x :=
    (A x).mulVecLin.rangeRestrict.comp
      ((T x).mulVecLin.comp (p.fiber x₀).subtype)
  have hfix (x : X) (v : p.fiber x) : A x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ : ∃ w : Fin p.size → ℂ, A x *ᵥ w = v.val := v.property
    rw [← hw, Matrix.mulVec_mulVec, hAA]
  have hfrontback (x : X) (hx : x ∈ U) (v : p.fiber x) :
      front x (back x v.val) = v := by
    apply Subtype.ext
    change A x *ᵥ (T x *ᵥ (A x₀ *ᵥ (L x *ᵥ v.val))) = v.val
    have hid : A x * T x * A x₀ * L x = A x := by
      calc
        _ = A x * (T x * A x₀) * L x := by noncomm_ring
        _ = A x * (A x * T x) * L x := by rw [hcomm]
        _ = (A x * A x) * (T x * L x) := by noncomm_ring
        _ = A x := by rw [hAA, hTL x hx, mul_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hid]
    exact hfix x v
  have hbackfront (x : X) (hx : x ∈ U) (v : p.fiber x₀) :
      back x (front x v).val = v := by
    apply Subtype.ext
    change A x₀ *ᵥ (L x *ᵥ (A x *ᵥ (T x *ᵥ v.val))) = v.val
    have hid : A x₀ * L x * A x * T x = A x₀ := by
      calc
        _ = (A x₀ * L x) * (A x * T x) := by noncomm_ring
        _ = (A x₀ * L x) * (T x * A x₀) := by rw [← hcomm]
        _ = A x₀ * (L x * T x) * A x₀ := by noncomm_ring
        _ = A x₀ := by rw [hLT x hx, mul_one, hAA]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hid]
    exact hfix x₀ v
  -- Continuity is tested in the original induced total-space topology.
  have hpair : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
      (z.proj, z.snd.val)) := continuous_induced_dom
  have hbase := continuous_fst.comp hpair
  have hvec := continuous_snd.comp hpair
  let e : Trivialization (p.fiber x₀) (π Unit (fun x ↦ p.fiber x)) :=
    { toFun := fun z ↦ (z.proj, back z.proj z.snd.val)
      invFun := fun z ↦ ⟨z.1, front z.1 z.2⟩
      source := π Unit (fun x ↦ p.fiber x) ⁻¹' U
      target := U ×ˢ Set.univ
      baseSet := U
      open_source := hopen.preimage hbase
      open_target := hopen.prod isOpen_univ
      open_baseSet := hopen
      map_source' := fun _ hx ↦ ⟨hx, Set.mem_univ _⟩
      map_target' := fun _ hx ↦ hx.1
      left_inv' := fun z hz ↦ TotalSpace.ext rfl (heq_of_eq (hfrontback z.proj hz z.snd))
      right_inv' := fun z hz ↦ Prod.ext rfl (hbackfront z.1 hz.1 z.2)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl
      continuousOn_toFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        let base : (π Unit (fun x ↦ p.fiber x) ⁻¹' U) → U :=
          fun z ↦ ⟨z.val.proj, z.property⟩
        have hbaseU : Continuous base := (hbase.comp continuous_subtype_val).subtype_mk _
        apply (hbase.comp continuous_subtype_val).prodMk
        apply Continuous.subtype_mk
        exact continuous_const.matrix_mulVec
          ((hL.comp hbaseU).matrix_mulVec (hvec.comp continuous_subtype_val))
      continuousOn_invFun := by
        apply Continuous.continuousOn
        apply continuous_induced_rng.mpr
        exact continuous_fst.prodMk
          ((hA.comp continuous_fst).matrix_mulVec
            ((hT.comp continuous_fst).matrix_mulVec
              (continuous_subtype_val.comp continuous_snd))) }
  -- Finite coordinates only re-express the fixed image model, with no global rank choice.
  let c : p.fiber x₀ ≃L[ℂ] (Fin (Module.finrank ℂ (p.fiber x₀)) → ℂ) :=
    (Module.finBasis ℂ (p.fiber x₀)).equivFun.toContinuousLinearEquiv
  refine ⟨Module.finrank ℂ (p.fiber x₀), e.transFiberHomeomorph c.toHomeomorph, hx₀, ?_⟩
  intro x hx
  constructor
  · intro v w
    change c (back x (v.val + w.val)) = c (back x v.val) + c (back x w.val)
    rw [map_add, map_add]
  · intro a v
    change c (back x (a • v.val)) = a • c (back x v.val)
    rw [map_smul, map_smul]

/-- Sections of the image bundle are exactly the image module of the original matrix. -/
theorem nonempty_image_equiv_continuousSections :
    letI := p.isFiniteRank_fiber
    Nonempty (p.image ≃ₗ[C(X, ℂ)]
      ComplexBundle.continuousSections (fun x ↦ p.fiber x)) := by
  /- A vector of continuous scalar functions in im p is fixed by p, so evaluation
  gives a continuous section of im p(x). Conversely, the induced total-space topology
  makes the ambient coordinates of a continuous section continuous. Pointwise
  idempotence says p s=s, hence the resulting vector belongs to im p. These constructions
  are inverse and commute with multiplication by continuous scalar functions. -/
  classical
  let := p.isFiniteRank_fiber
  -- Evaluation of a vector in the original image gives a vector in the same fiber image.
  have hmem (v : p.image) (x : X) : (fun i ↦ v.val i x) ∈ p.fiber x := by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨fun i ↦ w i x, ?_⟩
    change (fun i : Fin p.size ↦ ∑ j, p.matrix i j x * w j x) = (fun i ↦ v.val i x)
    funext i
    have hi := congrArg (fun a : C(X, ℂ) ↦ a x) (congrFun hw i)
    change (∑ j, p.matrix i j * w j) x = v.val i x at hi
    simpa using hi
  let forward (v : p.image) : ComplexBundle.continuousSections (fun x ↦ p.fiber x) :=
    ⟨fun x ↦ ⟨fun i ↦ v.val i x, hmem v x⟩, by
      apply continuous_induced_rng.mpr
      exact continuous_id.prodMk (continuous_pi fun i ↦ (v.val i).continuous)⟩
  -- A section supplies continuous coordinate functions; its image condition says p fixes them.
  have hfixed (x : X) (v : p.fiber x) :
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix.mulVecLin v.val = v.val := by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul,
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self]
  let backward (s : ComplexBundle.continuousSections (fun x ↦ p.fiber x)) : p.image := by
    have hcoords : Continuous (fun x ↦ (s.val x).val) :=
      continuous_snd.comp (continuous_induced_rng.mp s.property)
    let v (i : Fin p.size) : C(X, ℂ) :=
      ⟨fun x ↦ (s.val x).val i, (continuous_apply i).comp hcoords⟩
    refine ⟨v, ⟨v, ?_⟩⟩
    funext i
    apply ContinuousMap.ext
    intro x
    have hi := congrFun (hfixed x (s.val x)) i
    change ∑ j, p.matrix i j x * (s.val x).val j = (s.val x).val i at hi
    change (∑ j, p.matrix i j * v j) x = v i x
    simpa [v] using hi
  refine ⟨{
    toFun := forward
    invFun := backward
    left_inv := by
      intro v
      apply Subtype.ext
      funext i
      apply ContinuousMap.ext
      intro x
      rfl
    right_inv := by
      intro s
      apply Subtype.ext
      funext x
      apply Subtype.ext
      rfl
    map_add' := by
      intro v w
      apply Subtype.ext
      funext x
      apply Subtype.ext
      funext i
      rfl
    map_smul' := by
      intro a v
      apply Subtype.ext
      funext x
      apply Subtype.ext
      funext i
      rfl }⟩

end IdempotentMatrix

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

set_option linter.unusedSectionVars false in
/-- Serre-Swan, essential surjectivity with an actual idempotent image bundle. -/
theorem exists_imageBundle_of_finite_projective (P : Type*) [AddCommGroup P]
    [Module C(X, ℂ) P] [Module.Finite C(X, ℂ) P] [Module.Projective C(X, ℂ) P] :
    ∃ p : IdempotentMatrix C(X, ℂ),
      letI := p.fiberTotalSpaceTopology
      letI := p.isFiniteRank_fiber
      Nonempty (ComplexBundle.continuousSections (fun x ↦ p.fiber x) ≃ₗ[C(X, ℂ)] P) := by
  /- Present P as the image of a finite idempotent matrix over C(X,ℂ), using finite
  generation and projectivity. The fiberwise image is locally trivial by the explicit
  intertwiner construction. Its continuous section module is the algebraic image
  of that same matrix. Compose this identification with the presentation of P. -/
  -- Use one algebraic idempotent presentation throughout the geometric realization.
  obtain ⟨p, ⟨e⟩⟩ := exists_idempotentMatrix_of_finite_projective C(X, ℂ) P
  refine ⟨p, ?_⟩
  let := p.fiberTotalSpaceTopology
  let := p.isFiniteRank_fiber
  obtain ⟨sections⟩ := p.nonempty_image_equiv_continuousSections
  exact ⟨sections.symm.trans e⟩

end AtiyahSinger
