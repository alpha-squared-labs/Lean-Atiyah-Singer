/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorBaseSections
public import AtiyahSinger.Analysis.AssociatedTensorFiberSmoothness

/-!
# The original compactly localized whole-fiber input family

Public module ID: M0183.

Localize the actual normalized principal-fiber restriction in the supplied
base chart and base frame. The entire sphere section is retained. The same
compact base support controls every coordinate, and dual contraction recovers
exactly the original input localization used by the horizontal PDO.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

variable [T2Space B]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual base localization is a compactly supported smooth family of whole sphere sections. -/
theorem exists_associatedSphereTensorLocalizedFiberFamily
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (b : B) {c : OpenPartialHomeomorph B X}
    (input : BundleChartCutoff (r := a) E c) (hc : c ∈ atlas X B)
    (hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ c.symm '' tsupport input.cutoff, χ x = 1) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      ∃ u : Xp → Fin a → A.smoothSections,
        (∀ (z : Xp) (i : Fin a), u z i =
          (input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
            associatedSphereTensorLocalFiberCoordinates S E A b input.frame
              input.frame_mem_atlas i
              (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
              (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z))) ∧
        (∀ (i : Fin a) (j : A.Index),
          ContMDiffOn ((𝓘(ℝ, Xp)).prod (𝓡 r)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
            (fun z : Xp × OrthogonalSphere r ↦ (A.chart j ⟨z.2, (u z.1 i).val z.2⟩).2)
            (Set.univ ×ˢ (A.chart j).baseSet)) ∧
        (∀ z ∉ (EuclideanSpace.equiv (Fin n) ℝ) '' tsupport input.cutoff, ∀ i, u z i = 0) ∧
        ∀ (y : OrthogonalSphere r) (l : F y →ₗ[ℂ] ℂ) (z : Xp) (i : Fin a),
          let R := associatedSphereTensorCutoffBaseRestriction (a := a)
            S E A σ hσ b χ hχ hχsupport y w
          let s : smoothSections (n := n) (r := a) E :=
            ⟨fun x ↦ TensorProduct.lid ℂ (E x)
              (TensorProduct.map l LinearMap.id (R.val x)), R.property l⟩
          input.localize hc s ((EuclideanSpace.equiv (Fin n) ℝ).symm z) i =
            l ((u z i).val y) := by
  classical
  let := input.frame_mem_atlas
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro w
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  let v := associatedSphereTensorLocalFiberCoordinates S E A b input.frame input.frame_mem_atlas
    (u := fun p ↦ R p w)
  let ex := EuclideanSpace.equiv (Fin n) ℝ
  let u (z : Xp) (i : Fin a) : A.smoothSections :=
    (input.cutoff (ex.symm z) : ℂ) • v i (c.symm (ex.symm z))
  have hfamily := (isSmoothSection_associatedSphereTensor_iff_jointFiberCoordinates (a := a)
    S E A σ hσ w.val (fun p ↦ R p w)
    (fun p y ↦ (associatedSphereTensorFiberRestriction_apply (a := a)
      S E A σ hσ p w y).symm)).mp w.property
  have hzero (z : Xp) (hz : ex.symm z ∉ tsupport input.cutoff) (i : Fin a) : u z i = 0 := by
    simp only [u, image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_smul]
  refine ⟨u, fun _ _ ↦ rfl, ?_, ?_, ?_⟩
  · intro i j z hz
    by_cases hs : ex.symm z.1 ∈ tsupport input.cutoff
    · have htarget := (input.support_subset hs).1
      have hframe := (input.support_subset hs).2
      have hprincipal := hinput ⟨ex.symm z.1, hs, rfl⟩
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) hc) htarget
      have hparam : ContMDiffAt ((𝓘(ℝ, Xp)).prod (𝓡 r)) ((𝓡 n).prod (𝓡 r)) ∞
          (fun z : Xp × OrthogonalSphere r ↦ (c.symm (ex.symm z.1), z.2)) z :=
        (hchart.comp z (ex.symm.contDiff.contDiffAt.contMDiffAt.comp z
          contMDiffAt_fst)).prodMk contMDiffAt_snd
      have hdom : (c.symm (ex.symm z.1), z.2) ∈
          ((S.trivialization b).baseSet ∩ input.frame.baseSet) ×ˢ (A.chart j).baseSet :=
        ⟨⟨hprincipal, hframe⟩, hz.2⟩
      have hopen := ((S.trivialization b).open_baseSet.inter input.frame.open_baseSet).prod
        (A.chart j).open_baseSet
      have hcoords := ((hfamily b input.frame input.frame_mem_atlas i j).contMDiffAt
        (hopen.mem_nhds hdom)).comp z hparam
      have hcut := Complex.ofRealCLM.contDiff.comp
        (input.smooth_cutoff.comp ex.symm.contDiff)
      have hcutoff : ContMDiffAt ((𝓘(ℝ, Xp)).prod (𝓡 r)) 𝓘(ℝ, ℂ) ∞
          (fun z : Xp × OrthogonalSphere r ↦ (input.cutoff (ex.symm z.1) : ℂ)) z :=
        hcut.contDiffAt.contMDiffAt.comp z contMDiffAt_fst
      have hmul : ContDiff ℝ ∞ (fun p : ℂ × (Fin (A.rank j) → ℂ) ↦ p.1 • p.2) :=
        contDiff_smul
      apply ((hmul.comp_contMDiffAt (hcutoff.prodMk_space hcoords)).congr_of_eventuallyEq
        ?_).contMDiffWithinAt
      filter_upwards [continuous_snd.continuousAt ((A.chart j).open_baseSet.mem_nhds hz.2)]
        with z hz'
      change (A.chart j ⟨z.2, (input.cutoff (ex.symm z.1) : ℂ) •
        (v i (c.symm (ex.symm z.1))).val z.2⟩).2 = _
      exact (A.linear j z.2 hz').map_smul _ _
    · have hzeroEvent : ∀ᶠ z' : Xp × OrthogonalSphere r in nhds z,
          (A.chart j ⟨z'.2, (u z'.1 i).val z'.2⟩).2 = 0 := by
        filter_upwards [(ex.symm.continuous.comp continuous_fst).continuousAt
          ((isClosed_tsupport input.cutoff).isOpen_compl.mem_nhds hs),
          continuous_snd.continuousAt ((A.chart j).open_baseSet.mem_nhds hz.2)] with z' hz' hy
        rw [hzero z'.1 hz' i]
        exact (A.linear j z'.2 hy).map_zero
      exact (contMDiffAt_const.congr_of_eventuallyEq hzeroEvent).contMDiffWithinAt
  · intro z hz i
    apply hzero z _ i
    intro h
    exact hz ⟨ex.symm z, h, ex.apply_symm_apply z⟩
  · intro y l z i
    dsimp only
    let RB := associatedSphereTensorCutoffBaseRestriction (a := a)
      S E A σ hσ b χ hχ hχsupport y w
    let s : smoothSections (n := n) (r := a) E :=
      ⟨fun x ↦ TensorProduct.lid ℂ (E x)
        (TensorProduct.map l LinearMap.id (RB.val x)), RB.property l⟩
    change input.localize hc s (ex.symm z) i = l ((u z i).val y)
    by_cases hs : ex.symm z ∈ tsupport input.cutoff
    · have hzchart := (input.support_subset hs).1
      have hzframe := (input.support_subset hs).2
      let x := c.symm (ex.symm z)
      have hx : x ∈ (S.trivialization b).baseSet := hinput ⟨ex.symm z, hs, rfl⟩
      have hχx : χ x = 1 := hχone x ⟨ex.symm z, hs, rfl⟩
      let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
      have hpx : projection p = x := (S.trivialization b).proj_symm_apply' hx
      let e := input.frame.linearEquivAt ℂ x hzframe
      let cE := LinearEquiv.cast (R := ℂ) (M := E) hpx
      let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj i).comp
        ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
          (e.toLinearMap.comp cE.toLinearMap))
      have hcontract (v : E (projection p) ⊗[ℂ] F y) :
          e (TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id
            (TensorProduct.comm ℂ (E x) (F y)
              (TensorProduct.map cE.toLinearMap LinearMap.id v)))) i =
          l (TensorProduct.lid ℂ (F y) (TensorProduct.map φ LinearMap.id v)) := by
        induction v using TensorProduct.inductionOn with
        | tmul v t =>
          simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul,
            TensorProduct.lid_tmul, map_smul]
          change l t * e (cE v) i = e (cE v) i * l t
          exact mul_comm _ _
        | add v t hv ht =>
          simpa only [map_add, PiLp.add_apply] using congrArg₂ (· + ·) hv ht
      have hR : (associatedSphereTensorFiberEquiv S E σ p y).symm
          (w.val (associatedBundleMk G P (OrthogonalSphere r) p y)) = (R p w).val y := by
        rw [← associatedSphereTensorFiberRestriction_apply]
        exact (associatedSphereTensorFiberEquiv S E σ p y).symm_apply_apply _
      have hbase : RB.val x = TensorProduct.comm ℂ (E x) (F y)
          (TensorProduct.map cE.toLinearMap LinearMap.id ((R p w).val y)) := by
        change associatedSphereTensorCutoffBaseFamily (a := a) S E A σ hσ b χ y w x = _
        simp only [associatedSphereTensorCutoffBaseFamily, LinearMap.pi_apply,
          dite_eq_left hx, LinearMap.smul_apply, LinearMap.comp_apply,
          LinearEquiv.coe_coe, LinearMap.proj_apply, Submodule.subtype_apply]
        rw [hχx, Complex.ofReal_one, one_smul]
        let transport : ∀ {x z : B}, x = z → E x ≃ₗ[ℂ] E z := fun {x z} h ↦ by
          subst z
          exact LinearEquiv.refl ℂ (E x)
        have htransport {x z : B} (h : x = z) : transport h =
            LinearEquiv.cast (R := ℂ) (M := E) h := by
          subst z
          rfl
        change TensorProduct.comm ℂ (E x) (F y)
          (TensorProduct.map (transport hpx).toLinearMap LinearMap.id
            ((associatedSphereTensorFiberEquiv S E σ p y).symm
              (w.val (associatedBundleMk G P (OrthogonalSphere r) p y)))) = _
        rw [htransport, hR]
      have hu : (u z i).val y = (input.cutoff (ex.symm z) : ℂ) •
          TensorProduct.lid ℂ (F y) (TensorProduct.map φ LinearMap.id ((R p w).val y)) := by
        have hmem : x ∈ (S.trivialization b).baseSet ∩ input.frame.baseSet := ⟨hx, hzframe⟩
        change (input.cutoff (ex.symm z) : ℂ) •
          (associatedSphereTensorLocalFiberCoordinates S E A b input.frame
            input.frame_mem_atlas i (fun p ↦ R p w) x).val y = _
        simp only [associatedSphereTensorLocalFiberCoordinates, dite_eq_left hmem]
        rfl
      change input.localizedFunction s (ex.symm z) i = _
      simp only [BundleChartCutoff.localizedFunction, ite_eq_left hzchart, sectionInChart]
      change (input.cutoff (ex.symm z) : ℂ) * e (s.val x) i = _
      change (input.cutoff (ex.symm z) : ℂ) *
        e (TensorProduct.lid ℂ (E x) (TensorProduct.map l LinearMap.id (RB.val x))) i = _
      rw [hbase, hcontract, hu, map_smul]
      rfl
    · have hloc : input.localize hc s (ex.symm z) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hs (input.tsupport_localizedFunction_subset s h))
      rw [hloc, hzero z hs i]
      exact (map_zero l).symm

end AtiyahSinger
