/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalCutoffCoordinates
public import AtiyahSinger.Analysis.AtlasChartSchwartzFamily
public import AtiyahSinger.Analysis.ProductCompactSchwartz

/-!
# Controlled approximation of associated horizontal coordinates

Public module ID: M0160.

The supplied principal chart and sphere cutoff give joint Schwartz
coordinates of the horizontal family. The output cutoff is absorbed
into its compact complete symbol. A bounded lift and its positive
product-frequency cutoffs act uniformly on all smooth sections and
sphere-frame columns, with one operator-norm constant.

This is the local analytic comparison in SG III.13.5--13.6.
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

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One controlled coordinate limit realizes every column of the original horizontal family. -/
theorem exists_associatedSphereTensorHorizontalCutoff
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (c : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hc : c ∈ atlas Y (OrthogonalSphere r)) (C : AtlasChartCutoff A c)
    (ρ : Y → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρK : HasCompactSupport ρ)
    (hρone : ∀ y ∈ tsupport C.cutoff, ρ y = 1) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    let hα := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 L.output.cutoff
      L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _) L.symbol L.isSymbol
    let hαK := hasCompactSupport_zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
      L.output.compact_support
    ∃ R : Lp V₀ 2 (volume : Measure XY) →L[ℂ] Lp V₁ 2 (volume : Measure XY),
      (∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
        ∃ u : Xp → Fin a → A.smoothSections,
          (∀ (z : Xp) (i : Fin a), u z i =
            (L.input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
              associatedSphereTensorLocalFiberCoordinates S E A b L.input.frame
                L.input.frame_mem_atlas i
                (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
                (L.chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z))) ∧
          ∃ (f : Fin (A.rank C.frameIndex) → 𝓢(XY, V₀))
            (g : Fin (A.rank C.frameIndex) → 𝓢(XY, V₁)),
            (∀ x y i j, f j (EuclideanSpace.finAddEquivProd.symm (x, y)) i =
              C.localize hc (u ((EuclideanSpace.equiv (Fin n) ℝ) x) i) y j) ∧
            (∀ j, HasCompactSupport (f j)) ∧
            (∀ j z, quantize (liftedProductSymbol α ρ) (f j) z = g j z) ∧
            (∀ j, R (schwartzSobolevCoordinate 1 (f j)) = schwartzSobolevCoordinate 0 (g j)) ∧
            ∀ (y : Y) (hy : y ∈ tsupport C.cutoff) (x : B)
              (_hx : x ∈ L.chart.source) (_hf : x ∈ L.output.frame.baseSet)
              (j : Fin (A.rank C.frameIndex)),
              let l := (C.cutoff y : ℂ) • (LinearMap.proj j).comp
                (A.frameLinearEquiv C.frameIndex (c.symm y) (C.support_subset hy).2).toLinearMap
              g j (EuclideanSpace.finAddEquivProd.symm (L.chart x, y)) =
                (L.output.frame ⟨x, TensorProduct.lid ℂ (E' x)
                  (TensorProduct.map l LinearMap.id
                    ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
                      hχ hχsupport (c.symm y) w).val x))⟩).2) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
        ‖productCutoffSobolevOperator α hα hαK ρ hρ hρK ε hε - R‖ ≤ K * ε := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  let hα := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 L.output.cutoff
    L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _) L.symbol L.isSymbol
  let hαK := hasCompactSupport_zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    L.output.compact_support
  -- One bounded limit is selected before the original section and every sphere-frame column.
  obtain ⟨R, hR, K, hK, hbound⟩ :=
    exists_liftedProductSobolev_approximation_schwartz α hα hαK ρ hρ hρK
  refine ⟨R, ?_, K, hK, hbound⟩
  intro w
  obtain ⟨u, hu, huSmooth, huSupport, huDual⟩ :=
    exists_associatedSphereTensorHorizontalCutoffCoordinates (a := a)
      S E A σ E' L hσ b hinput χ hχ hχsupport hχone w
  refine ⟨u, hu, ?_⟩
  let ex := EuclideanSpace.equiv (Fin n) ℝ
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let uX (x : X) (i : Fin a) := u (ex x) i
  have huX (i : Fin a) (j : A.Index) :
      ContMDiffOn ((𝓡 n).prod (𝓡 r)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun p : X × OrthogonalSphere r ↦ (A.chart j ⟨p.2, (uX p.1 i).val p.2⟩).2)
        (Set.univ ×ˢ (A.chart j).baseSet) := by
    have hm : ContMDiff ((𝓡 n).prod (𝓡 r)) ((𝓘(ℝ, Xp)).prod (𝓡 r)) ∞
        (fun p : X × OrthogonalSphere r ↦ (ex p.1, p.2)) :=
      (ex.toContinuousLinearMap.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    exact (huSmooth i j).comp hm.contMDiffOn (fun _ h ↦ ⟨Set.mem_univ _, h.2⟩)
  have huXsupport (x : X) (hx : x ∉ tsupport L.input.cutoff) (i : Fin a) : uX x i = 0 := by
    apply huSupport (ex x) ?_ i
    rintro ⟨z, hz, heq⟩
    exact hx ((ex.injective heq) ▸ hz)
  -- Localize the same whole-fiber family, in the supplied sphere chart and original frame.
  obtain ⟨W, hW, hWsupport⟩ := exists_jointSchwartz_atlasChartCutoff_localize A c hc C
    uX huX (tsupport L.input.cutoff) L.input.compact_support huXsupport
  let col (j : Fin (A.rank C.frameIndex)) :
      EuclideanSpace ℂ (Fin (a * A.rank C.frameIndex)) →L[ℂ] V₀ :=
    LinearMap.toContinuousLinearMap {
      toFun z := WithLp.toLp 2 (fun i ↦ z (finProdFinEquiv (i, j)))
      map_add' z z' := by ext i; rfl
      map_smul' z z' := by ext i; rfl }
  let f (j : Fin (A.rank C.frameIndex)) := SchwartzMap.postcompCLM (col j) W
  have hfvalue (x : X) (y : Y) (i : Fin a) (j : Fin (A.rank C.frameIndex)) :
      f j (e.symm (x, y)) i = C.localize hc (u (ex x) i) y j := hW x y i j
  have hfK (j : Fin (A.rank C.frameIndex)) : HasCompactSupport (f j) := by
    have hcompact := (L.input.compact_support.prod C.compact_support).image e.symm.continuous
    apply hcompact.of_isClosed_subset (isClosed_tsupport _)
    exact (tsupport_comp_subset (map_zero (col j)) W).trans hWsupport
  have hgExists (j : Fin (A.rank C.frameIndex)) :=
    exists_schwartz_quantize_liftedProductSymbol_of_hasCompactSupport
      α hα hαK ρ hρ hρK (f j) (hfK j)
  choose g hg _hgSupport using hgExists
  refine ⟨f, g, hfvalue, hfK, hg, fun j ↦ hR (f j) (g j) (hg j), ?_⟩
  intro y hy x hx hf j
  let l := (C.cutoff y : ℂ) • (LinearMap.proj j).comp
    (A.frameLinearEquiv C.frameIndex (c.symm y) (C.support_subset hy).2).toLinearMap
  obtain ⟨f₀, hf₀, hH⟩ := huDual (c.symm y) l
  -- The actual sphere-frame column is precisely the original dual-contracted input slice.
  have hslice (t : X) : f₀ t = f j (e.symm (t, y)) := by
    apply PiLp.ext
    intro i
    rw [hf₀, hfvalue]
    change l ((u (ex t) i).val (c.symm y)) =
      C.localizedFunction (u (ex t) i) y j
    have hyt : y ∈ c.target := (C.support_subset hy).1
    simp only [AtlasChartCutoff.localizedFunction, ite_eq_left hyt, atlasSectionInChart]
    rfl
  have hαquant (v : 𝓢(X, V₀)) (t : X) :
      quantize α v t = (L.output.cutoff t : ℂ) • quantize L.symbol v t := by
    simp only [α, zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, quantize, smul_apply]
    simp_rw [smul_comm (Complex.exp _) (L.output.cutoff t : ℂ)]
    rw [integral_smul, smul_comm]
  -- The original output cutoff occurs exactly once, inside the compact complete symbol.
  rw [← hg j _, quantize_liftedProductSymbol_eq_slice α hα hαK ρ (f j) y f₀ hslice,
    hρone y hy, Complex.ofReal_one, one_smul, hαquant]
  exact (hH x hx hf).symm

end AtiyahSinger

