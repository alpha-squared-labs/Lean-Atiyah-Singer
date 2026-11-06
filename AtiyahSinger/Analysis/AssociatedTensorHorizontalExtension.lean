/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalJointCutoff
public import AtiyahSinger.Analysis.AssociatedTensorLocalHorizontalProperties

/-!
# Returning the original horizontal Fourier output to the associated bundle

Public module ID: M0164.

The specified output plateaus return the exact full joint Fourier output to
the same associated tensor bundle. The result is the original local horizontal
lift multiplied by the supplied sphere cutoff. The proof keeps the original
output support and normalized principal coordinates, including every case
outside the principal, manifold, sphere or bundle-frame chart.

This is the output identity needed before summing a finite sphere partition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
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
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space B]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)
local notation "V₁" => EuclideanSpace ℂ (Fin a')

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Classical in
/-- Returning the full Fourier output gives the sphere-localized original horizontal lift. -/
theorem exists_associatedSphereTensorHorizontalCutoff_extension
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (c : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hc : c ∈ atlas Y (OrthogonalSphere r)) (C : AtlasChartCutoff A c)
    (Co : BundleChartCutoff (r := a') E' L.chart) (hCoFrame : Co.frame = L.output.frame)
    (hCo : L.chart.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (hCoOne : ∀ x ∈ tsupport L.output.cutoff, Co.cutoff x = 1)
    (κ : Y → ℝ) (hκ : ContDiff ℝ ∞ κ) (hκK : HasCompactSupport κ)
    (hκsupport : tsupport κ ⊆ c.target ∩ c.symm ⁻¹' (A.chart C.frameIndex).baseSet)
    (hκone : ∀ y ∈ tsupport C.cutoff, κ y = 1)
    (ρ : Y → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρK : HasCompactSupport ρ)
    (hρone : ∀ y ∈ tsupport C.cutoff, ρ y = 1) :
    letI := modelTopology V₀ E
    letI := modelTopology V₁ E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let Kout : AtlasChartCutoff A c := ⟨C.frameIndex, κ, hκ, hκK, hκsupport⟩
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b L.chart L.input hinput c C
    let Dout := associatedSphereTensorChartCutoff S E' A σ hσ b L.chart Co hCo c Kout
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    ∀ I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank C.frameIndex))),
      (∀ w z, I w z = Din.localizedFunction w z) →
      ∀ w : AT.smoothSections,
        ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a' * A.rank C.frameIndex))),
          (∀ z, quantize (liftedProductSymbol
            (fun x ξ ↦ tensorIdentitySymbolMap a a' (A.rank C.frameIndex) (α x ξ)) ρ)
              (I w) z = v z) ∧
          ∀ z : Z, Dout.extendedFunction v z =
            ((if (associatedSphereTrivialization S b z).2 ∈ c.source then
              C.cutoff (c (associatedSphereTrivialization S b z).2) else 0 : ℝ) : ℂ) •
              (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
                hχ hχsupport houtput w).val z := by
  classical
  let := L.output.frame_mem_atlas
  let := modelTopology V₀ E
  let := modelTopology V₁ E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a') S E' A σ hσ
  let t := associatedSphereTrivialization S b
  let CP := associatedSphereProductChart S b L.chart c
  let Kout : AtlasChartCutoff A c := ⟨C.frameIndex, κ, hκ, hκK, hκsupport⟩
  let Dout : AtlasChartCutoff AT' CP :=
    associatedSphereTensorChartCutoff S E' A σ hσ b L.chart Co hCo c Kout
  dsimp only
  intro I hI w
  let H := associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
    hχ hχsupport houtput w
  obtain ⟨v, hv, hvsupport, hcolumns⟩ := exists_associatedSphereTensorHorizontalJointCutoff
    (a := a) S E A σ E' L hσ b hinput χ hχ hχsupport hχone c hc C ρ hρ hρK hρone I hI w
  refine ⟨v, hv, ?_⟩
  have hparts (z : Z) (hz : z ∈ CP.source) :
      z ∈ t.source ∧ (t z).1 ∈ L.chart.source ∧ (t z).2 ∈ c.source :=
    ⟨hz.1.1, hz.1.2.1, hz.1.2.2⟩
  have hcoordinate (z : Z) (hz : z ∈ CP.source) :
      CP z = e.symm (L.chart (πS z), c (t z).2) := by
    change e.symm (L.chart (t z).1, c (t z).2) = _
    have hprojection : (t z).1 = πS z := t.proj_toFun z (hparts z hz).1
    rw [hprojection]
  have hnonzero (z : Z) (hz : z ∈ CP.source) (hn : v (CP z) ≠ 0) :
      πS z ∈ L.chart.symm '' tsupport L.output.cutoff ∧
        c (t z).2 ∈ tsupport C.cutoff := by
    obtain ⟨p, hp, hpoint⟩ := hvsupport (subset_tsupport v hn)
    have hp' : p = (L.chart (πS z), c (t z).2) := by
      have heq := congrArg e hpoint
      rw [e.apply_symm_apply, hcoordinate z hz, e.apply_symm_apply] at heq
      exact heq
    rw [hp'] at hp
    have hx : πS z ∈ L.chart.source := by
      have hprojection : (t z).1 = πS z := t.proj_toFun z (hparts z hz).1
      exact hprojection ▸ (hparts z hz).2.1
    exact ⟨⟨L.chart (πS z), hp.1, L.chart.left_inv hx⟩, hp.2⟩
  have hzeroExtension (z : Z) (hzero : v (CP z) = 0) : Dout.extendedFunction v z = 0 := by
    by_cases hz : z ∈ CP.source ∩ (AT'.chart Dout.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hz]
      change (Dout.cutoff (CP z) : ℂ) •
        (AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm
          ((EuclideanSpace.equiv (Fin (a' * A.rank C.frameIndex)) ℂ) (v (CP z))) = 0
      rw [hzero, (EuclideanSpace.equiv (Fin (a' * A.rank C.frameIndex)) ℂ).map_zero,
        (AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm.map_zero, smul_zero]
    · simp only [AtlasChartCutoff.extendedFunction, dite_eq_right hz]
  intro z
  change Dout.extendedFunction v z =
    ((if (t z).2 ∈ c.source then C.cutoff (c (t z).2) else 0 : ℝ) : ℂ) • H.val z
  -- Outside the original base output support, both the original lift and its return vanish.
  by_cases hzbase : πS z ∈ L.chart.symm '' tsupport L.output.cutoff
  · obtain ⟨x, hxout, hxbase⟩ := hzbase
    have hxt : x ∈ L.chart.target := (L.output.support_subset hxout).1
    have hx : πS z ∈ L.chart.source := hxbase ▸ L.chart.map_target hxt
    have hxcoord : L.chart (πS z) = x := by rw [← hxbase, L.chart.right_inv hxt]
    have hxframe : πS z ∈ L.output.frame.baseSet :=
      hxbase ▸ (L.output.support_subset hxout).2
    have htbase : t.baseSet = (S.trivialization b).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.1
    have hzt : z ∈ t.source := t.mem_source.mpr
      (htbase.symm ▸ houtput ⟨x, hxout, hxbase⟩)
    by_cases hy : (t z).2 ∈ c.source
    · by_cases hycut : c (t z).2 ∈ tsupport C.cutoff
      · -- Both plateau cutoffs equal one on the supplied base and sphere output supports.
        have hzCP : z ∈ CP.source := by
          refine ⟨⟨hzt, ?_⟩, Set.mem_univ _⟩
          exact ⟨(t.proj_toFun z hzt).symm ▸ hx, hy⟩
        have hcut : Dout.cutoff (CP z) = 1 := by
          change Co.cutoff (e (CP z)).1 * κ (e (CP z)).2 = 1
          rw [hcoordinate z hzCP, e.apply_symm_apply, hxcoord,
            hCoOne x hxout, hκone _ hycut, mul_one]
        have hzcut : CP z ∈ tsupport Dout.cutoff := by
          apply subset_tsupport
          change Dout.cutoff (CP z) ≠ 0
          rw [hcut]
          exact one_ne_zero
        have hzframe : z ∈ (AT'.chart Dout.frameIndex).baseSet := by
          have hf := (Dout.support_subset hzcut).2
          change CP.symm (CP z) ∈ (AT'.chart Dout.frameIndex).baseSet at hf
          rwa [CP.left_inv hzCP] at hf
        simp only [ite_eq_left hy, AtlasChartCutoff.extendedFunction,
          dite_eq_left (show z ∈ CP.source ∩ (AT'.chart Dout.frameIndex).baseSet from
            ⟨hzCP, hzframe⟩), hcut, Complex.ofReal_one, one_smul]
        let frame : T' z ≃ₗ[ℂ] (Fin (a' * A.rank C.frameIndex) → ℂ) :=
          AT'.frameLinearEquiv Dout.frameIndex z hzframe
        apply frame.injective
        change frame (frame.symm
          ((EuclideanSpace.equiv (Fin (a' * A.rank C.frameIndex)) ℂ) (v (CP z)))) =
            frame ((C.cutoff (c (t z).2) : ℂ) • H.val z)
        rw [frame.apply_symm_apply, frame.map_smul]
        funext l
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective l
        change v (CP z) (finProdFinEquiv (i, j)) =
          (C.cutoff (c (t z).2) : ℂ) *
            (AT'.chart Dout.frameIndex ⟨z, H.val z⟩).2 (finProdFinEquiv (i, j))
        have hyframe : (t z).2 ∈ (A.chart C.frameIndex).baseSet := by
          have hf := (C.support_subset hycut).2
          change c.symm (c (t z).2) ∈ (A.chart C.frameIndex).baseSet at hf
          rwa [c.left_inv hy] at hf
        have hreturn := associatedSphereTensorBaseExtension_coordinate (a := a')
          S E' A σ hσ b L.output.frame L.output.frame_mem_atlas C.frameIndex
          z hzt hxframe hyframe i j
          (fun y x ↦ (associatedSphereTensorHorizontalFamily (a := a) S E A σ E'
            L hσ b χ hχ hχsupport y w).val x)
        have hreturn' : (AT'.chart Dout.frameIndex ⟨z, H.val z⟩).2
            (finProdFinEquiv (i, j)) =
            (L.output.frame ⟨πS z, TensorProduct.lid ℂ (E' (πS z))
              (TensorProduct.map ((LinearMap.proj j).comp
                (A.frameLinearEquiv C.frameIndex (t z).2 hyframe).toLinearMap) LinearMap.id
                  ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
                    hχ hχsupport (t z).2 w).val (πS z)))⟩).2 i := by
          change (AT'.chart (⟨Co.frame, Co.frame_mem_atlas⟩, (b, C.frameIndex))
            ⟨z, H.val z⟩).2 (finProdFinEquiv (i, j)) = _
          have hindex : (⟨Co.frame, Co.frame_mem_atlas⟩ :
              (nativeSmoothComplexBundleAtlas (n := n) (r := a') E').Index) =
              ⟨L.output.frame, L.output.frame_mem_atlas⟩ := Subtype.ext hCoFrame
          have hframeeq := congrArg (fun q :
              (nativeSmoothComplexBundleAtlas (n := n) (r := a') E').Index ↦
              (AT'.chart (q, (b, C.frameIndex)) ⟨z, H.val z⟩).2
                (finProdFinEquiv (i, j))) hindex
          apply hframeeq.trans
          change (AT'.chart (⟨L.output.frame, L.output.frame_mem_atlas⟩, (b, C.frameIndex))
            ⟨z, (associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' L hσ b χ
              hχ hχsupport houtput w).val z⟩).2 (finProdFinEquiv (i, j)) = _
          rw [associatedSphereTensorLocalHorizontalLift_apply]
          exact hreturn
        rw [hcoordinate z hzCP, hreturn']
        have hcol := hcolumns (c (t z).2) hycut (πS z) hx hxframe j i
        dsimp only at hcol
        rw [hcol, TensorProduct.map_smul_left, LinearMap.smul_apply, map_smul]
        change ((L.output.frame.linearEquivAt ℂ (πS z) hxframe) (_ • _)) i = _
        rw [map_smul]
        let value (y : OrthogonalSphere r) (hy : y ∈ (A.chart C.frameIndex).baseSet) : ℂ :=
          (L.output.frame ⟨πS z, TensorProduct.lid ℂ (E' (πS z))
            (TensorProduct.map ((LinearMap.proj j).comp
              (A.frameLinearEquiv C.frameIndex y hy).toLinearMap) LinearMap.id
                ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
                  hχ hχsupport y w).val (πS z)))⟩).2 i
        have hyframe' : c.symm (c (t z).2) ∈ (A.chart C.frameIndex).baseSet :=
          (C.support_subset hycut).2
        have hvalue : value (c.symm (c (t z).2)) hyframe' = value (t z).2 hyframe := by
          congr 1
          exact c.left_inv hy
        change (C.cutoff (c (t z).2) : ℂ) * value (c.symm (c (t z).2)) hyframe' =
          (C.cutoff (c (t z).2) : ℂ) * value (t z).2 hyframe
        exact congrArg ((C.cutoff (c (t z).2) : ℂ) * ·) hvalue
      · have hzero : Dout.extendedFunction v z = 0 := by
          by_cases hzCP : z ∈ CP.source
          · apply hzeroExtension
            by_contra hn
            exact hycut (hnonzero z hzCP hn).2
          · simp [AtlasChartCutoff.extendedFunction, hzCP]
        rw [hzero, ite_eq_left hy, image_eq_zero_of_notMem_tsupport hycut]
        simp
    · have hzCP : z ∉ CP.source := fun hz ↦ hy (hparts z hz).2.2
      simp [AtlasChartCutoff.extendedFunction, hzCP, hy]
  · have hHzero : H.val z = 0 := associatedSphereTensorLocalHorizontalLift_apply_eq_zero
      (a := a) S E A σ E' L hσ b χ hχ hχsupport houtput z hzbase w
    rw [hHzero, smul_zero]
    by_cases hzCP : z ∈ CP.source
    · apply hzeroExtension
      by_contra hn
      exact hzbase (hnonzero z hzCP hn).1
    · simp [AtlasChartCutoff.extendedFunction, hzCP]

end AtiyahSinger

