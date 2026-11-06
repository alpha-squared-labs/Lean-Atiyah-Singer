/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.InverseAhat

/-!
# Pullback of the original Pontryagin and inverse A-hat classes

Public module ID: M1994.

Continuous pullback preserves the original local real-linear charts, including
locally varying rank. The tensor complexification of that same pulled-back
bundle has exactly the native topology of the pulled-back complexification.
Its integral Pontryagin classes and the original finite inverse A-hat
polynomials therefore commute with the same cohomology pullback.

The two auxiliary Hermitian metrics are specified independently on their
original complexification topologies. Chern-class metric independence makes
their equality unnecessary. No compactness, separation, properness, orientation
or global rank bound is imposed. The even family retains its actual parity
test and degree transport, including the zero components.

Sources: Milnor--Stasheff, section 15, for Pontryagin classes of the actual
complexification; Spin Geometry III.11, Example 11.13 and Proposition 11.24,
for the fixed A-hat series and its inverse. The native-topology and finite
polynomial comparisons expand the standard naturality argument in the
project's existing models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle CategoryTheory
open scoped TensorProduct

universe u v


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Type u} [TopologicalSpace X]
  (G : Type*) (V : X → Type v) [hAdd : ∀ x, AddCommGroup (V x)]
  [hModule : ∀ x, Module ℝ (V x)] [TopologicalSpace (TotalSpace G V)]
  [hV : IsFiniteRank G V]

include hV in
/-- Native continuous pullback preserves local finite real rank, allowing ranks to vary. -/
theorem isFiniteRank_pullback {Y : Type*} [TopologicalSpace Y] (f : C(Y, X)) :
    letI : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
    letI : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
    IsFiniteRank G ((f : Y → X) *ᵖ V) := by
  classical
  let : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
  let : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
  constructor
  intro y
  obtain ⟨r, e, he, hlinear⟩ := hV.exists_linear_trivialization (f y)
  -- The inverse chart retains the old fiber vector and only changes its base coordinate.
  let g : Y × (Fin r → ℝ) → TotalSpace G ((f : Y → X) *ᵖ V) :=
    fun z ↦ if hz : f z.1 ∈ e.baseSet then
      ⟨z.1, cast (congrArg V (e.proj_symm_apply' hz))
        (e.toPartialEquiv.symm (f z.1, z.2)).snd⟩
    else ⟨z.1, 0⟩
  have hgproj (z : Y × (Fin r → ℝ)) : (g z).proj = z.1 := by
    dsimp [g]
    split_ifs <;> rfl
  have hglift (z : Y × (Fin r → ℝ)) (hz : f z.1 ∈ e.baseSet) :
      Pullback.lift f (g z) = e.toPartialEquiv.symm (f z.1, z.2) := by
    dsimp only [g]
    rw [dite_eq_left hz]
    exact TotalSpace.mk_cast (F := G) (E := V) (e.proj_symm_apply' hz) _
  -- The native induced topology makes the original finite chart a pullback chart.
  let t : Trivialization (Fin r → ℝ) (π G ((f : Y → X) *ᵖ V)) :=
    { toFun := fun z ↦ (z.proj, (e (Pullback.lift f z)).2)
      invFun := g
      source := Pullback.lift f ⁻¹' e.source
      baseSet := f ⁻¹' e.baseSet
      target := (f ⁻¹' e.baseSet) ×ˢ Set.univ
      map_source' := by
        intro z hz
        simp only [e.source_eq, Set.mem_preimage, Pullback.lift_proj] at hz
        exact ⟨hz, Set.mem_univ _⟩
      map_target' := by
        intro z hz
        simp only [e.source_eq, Set.mem_preimage, Pullback.lift_proj, hgproj]
        exact hz.1
      left_inv' := by
        intro z hz
        have hbase : f z.proj ∈ e.baseSet := e.mem_source.mp hz
        apply TotalSpace.ext (hgproj _)
        have hpoint := (hglift (z.proj, (e (Pullback.lift f z)).2) hbase).trans
          (e.symm_apply_mk_proj hz)
        exact congr_arg_heq (fun w : TotalSpace G V ↦ w.snd) hpoint
      right_inv' := by
        intro z hz
        apply Prod.ext
        · exact hgproj z
        · change (e (Pullback.lift f (g z))).2 = z.2
          rw [hglift z hz.1]
          exact congrArg (fun w : X × (Fin r → ℝ) ↦ w.2)
            (e.apply_symm_apply' (x := z.2) hz.1)
      open_source := by
        rw [e.source_eq]
        exact e.open_baseSet.preimage
          (f.continuous.comp (Pullback.continuous_proj G V f))
      open_target := (e.open_baseSet.preimage f.continuous).prod isOpen_univ
      open_baseSet := e.open_baseSet.preimage f.continuous
      continuousOn_toFun :=
        (Pullback.continuous_proj G V f).continuousOn.prodMk
          (continuous_snd.comp_continuousOn
            (e.toOpenPartialHomeomorph.continuousOn.comp
              (Pullback.continuous_lift G V f).continuousOn Set.Subset.rfl))
      continuousOn_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding G V f).continuousOn_iff]
        refine (continuousOn_fst.prodMk
          (e.toOpenPartialHomeomorph.continuousOn_symm.comp
            (f.continuous.prodMap continuous_id).continuousOn
            (fun z hz ↦ e.mem_target.mpr hz.1))).congr ?_
        intro z hz
        exact Prod.ext (hgproj z) (hglift z hz.1)
      source_eq := by rw [e.source_eq]; rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  refine ⟨r, t, he, ?_⟩
  intro z hz
  exact hlinear (f z) hz

variable
  (h : letI := ComplexBundle.complexificationTopology G V
    ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] V x))
  {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
  (hY : letI : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
    letI : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
    letI := ComplexBundle.complexificationTopology G ((f : Y → X) *ᵖ V)
    ComplexBundle.ContinuousHermitianMetric (fun y ↦ ℂ ⊗[ℝ] ((f : Y → X) *ᵖ V) y))

/-- The original integral Pontryagin classes commute with native continuous pullback. -/
theorem pontryaginClass_pullback (k : ℕ) :
    letI : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
    letI : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
    letI := isFiniteRank_pullback G V f
    singularCohomologyPullback ℤ f (2 * (2 * k)) (pontryaginClass G V h k) =
      pontryaginClass G ((f : Y → X) *ᵖ V) hY k := by
  let : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
  let : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
  let := isFiniteRank_pullback G V f
  let := ComplexBundle.complexificationTopology G V
  let := isFiniteRank_complexification G V
  let C : X → Type _ := fun x ↦ ℂ ⊗[ℝ] V x
  let D : Y → Type _ := (f : Y → X) *ᵖ C
  let tOriginal : TopologicalSpace (TotalSpace Unit D) :=
    ComplexBundle.complexificationTopology G ((f : Y → X) *ᵖ V)
  let tPullback : TopologicalSpace (TotalSpace Unit D) :=
    Pullback.TotalSpace.topologicalSpace Unit C (f : Y → X)
  have htop : tOriginal = tPullback :=
    ComplexBundle.complexificationTopology_pullback G V f
  -- Make the actual topology explicit before identifying the same tensor fibers.
  let Statement (t : TopologicalSpace (TotalSpace Unit D)) : Prop :=
    letI := t
    ∀ hFin : ComplexBundle.IsFiniteRank D,
      letI := hFin
      ∀ hD : ComplexBundle.ContinuousHermitianMetric D,
        singularCohomologyPullback ℤ f (2 * (2 * k))
            ((-1 : ℤ) ^ k • ComplexBundle.globalChernClass C h (2 * k)) =
          (-1 : ℤ) ^ k • ComplexBundle.globalChernClass D hD (2 * k)
  have hpull : Statement tPullback := by
    let := tPullback
    intro hFin hD
    let := hFin
    -- Chern naturality permits the specified target metric on the identical native pullback.
    rw [map_zsmul]
    exact congrArg (fun c ↦ (-1 : ℤ) ^ k • c)
      (ComplexBundle.globalChernClass_pullback C h f D hD
        (ComplexBundle.Iso.refl D) (2 * k)).symm
  rw [← htop] at hpull
  exact hpull (isFiniteRank_complexification G ((f : Y → X) *ᵖ V)) hY

/-- The original inverse A-hat polynomial in each degree commutes with continuous pullback. -/
theorem inverseAHatClassComponent_pullback (k : ℕ) :
    letI : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
    letI : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
    letI := isFiniteRank_pullback G V f
    singularCohomologyPullback ℚ f (2 * (2 * k)) (inverseAHatClassComponent G V h k) =
      inverseAHatClassComponent G ((f : Y → X) *ᵖ V) hY k := by
  let : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
  let : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
  let := isFiniteRank_pullback G V f
  -- The finite evaluator retains the same inverse series and doubled cohomological weights.
  unfold inverseAHatClassComponent
  rw [singularCohomologyWeightedPolynomial_pullback]
  congr 1
  funext i
  -- Rationalization and integral Pontryagin naturality identify every original input.
  rw [← singularCohomologyRationalization_naturality]
  congr 1
  exact pontryaginClass_pullback G V h f hY (i.val + 1)

/-- The full original even inverse A-hat family is natural, including its zero components. -/
theorem inverseAHatEvenComponent_pullback (k : ℕ) :
    letI : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
    letI : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
    letI := isFiniteRank_pullback G V f
    singularCohomologyPullback ℚ f (2 * k) (inverseAHatEvenComponent G V h k) =
      inverseAHatEvenComponent G ((f : Y → X) *ᵖ V) hY k := by
  classical
  let : ∀ y, AddCommGroup (((f : Y → X) *ᵖ V) y) := fun y ↦ hAdd (f y)
  let : ∀ y, Module ℝ (((f : Y → X) *ᵖ V) y) := fun y ↦ hModule (f y)
  let := isFiniteRank_pullback G V f
  -- The same degree equality is used in both cohomology functors.
  have ht {i j : ℕ} (hij : i = j) (b : singularCohomology ℚ X i) :
      singularCohomologyPullback ℚ f j
          ((eqToIso (congrArg (singularCohomology ℚ X) hij)).hom b) =
        (eqToIso (congrArg (singularCohomology ℚ Y) hij)).hom
          (singularCohomologyPullback ℚ f i b) := by
    subst j
    rfl
  unfold inverseAHatEvenComponent
  split_ifs with hk
  · have hdegree : 2 * (2 * (k / 2)) = 2 * k := by
      rcases hk with ⟨j, hj⟩
      omega
    rw [ht hdegree, inverseAHatClassComponent_pullback G V h f hY (k / 2)]
  · -- Outside the fourfold degrees, both original components are zero.
    exact map_zero _

end AtiyahSinger.RealBundle
