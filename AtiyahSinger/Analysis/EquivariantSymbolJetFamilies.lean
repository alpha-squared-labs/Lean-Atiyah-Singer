/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantFrameFamilies
public import AtiyahSinger.Analysis.EquivariantSymbolCoordinateFamilies
public import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Continuous mixed jets of the original transported symbol

Public module ID: M0597.

Use fixed original charts and frames near each moving point. Two independent
smooth group parameters describe the forward and backward transport; only after
spatial and frequency differentiation do we restrict to the continuous inverse
graph. This keeps the original topological-group assumptions and never assumes
smooth inversion or continuity in a stronger symbol topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold Manifold Set Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

universe u

private theorem contMDiffAt_parameter_jets {V HG Y : Type*} {X F : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace HG]
    (I : ModelWithCorners ℝ V HG) [TopologicalSpace Y] [ChartedSpace HG Y]
    [IsManifold I ∞ Y] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Y × X → F} {p : Y × X}
    (hf : ContMDiffAt (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, F) ∞ f p) (k : ℕ) :
    ContMDiffAt (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, X [×k]→L[ℝ] F) ∞
      (fun q ↦ iteratedFDeriv ℝ k (fun x ↦ f (q.1, x)) q.2) p := by
  have hpartial {A : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
      {g : Y × X → A}
      (hg : ContMDiffAt (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, A) ∞ g p) :
      ContMDiffAt (I.prod 𝓘(ℝ, X)) 𝓘(ℝ, X →L[ℝ] A) ∞
        (fun q ↦ fderiv ℝ (fun x ↦ g (q.1, x)) q.2) p := by
    have hcomp : ContMDiffAt ((I.prod 𝓘(ℝ, X)).prod 𝓘(ℝ, X)) 𝓘(ℝ, A) ∞
        (fun q : (Y × X) × X ↦ g (q.1.1, q.2)) (p, p.2) :=
      hg.comp_of_eq (contMDiffAt_fst.fst.prodMk contMDiffAt_snd) rfl
    have hd := hcomp.mfderiv (m := ∞) (fun q : Y × X ↦ fun x : X ↦ g (q.1, x))
      (fun q : Y × X ↦ q.2) contMDiffAt_snd (by simp)
    have heq : inTangentCoordinates 𝓘(ℝ, X) 𝓘(ℝ, A)
        (fun q : Y × X ↦ q.2) (fun q ↦ g (q.1, q.2))
        (fun q ↦ mfderiv 𝓘(ℝ, X) 𝓘(ℝ, A) (fun x ↦ g (q.1, x)) q.2) p =
        (fun q : Y × X ↦ fderiv ℝ (fun x ↦ g (q.1, x)) q.2) := by
      funext q
      simp only [mfderiv_eq_fderiv]
      unfold inTangentCoordinates
      erw [inCoordinates_tangent_bundle_core_model_space]
      rfl
    rwa [heq] at hd
  induction k with
  | zero =>
    exact (((continuousMultilinearCurryFin0 ℝ X F).symm :
      F →L[ℝ] X [×0]→L[ℝ] F).contMDiffAt).comp p hf
  | succ k ih =>
    have hd := hpartial ih
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) F).symm
    rw [show (fun q : Y × X ↦ iteratedFDeriv ℝ (k + 1) (fun x ↦ f (q.1, x)) q.2) =
        fun q ↦ L (fderiv ℝ (fun x ↦ iteratedFDeriv ℝ k (fun y ↦ f (q.1, y)) x) q.2) from by
      funext q
      exact congrFun (iteratedFDeriv_succ_eq_comp_left (𝕜 := ℝ)
        (f := fun x ↦ f (q.1, x))) q.2]
    exact (L : (X →L[ℝ] X [×k]→L[ℝ] F) →L[ℝ] X [×(k + 1)]→L[ℝ] F).contMDiffAt.comp p hd

private theorem contMDiffAt_mixed_parameter_jets {V HG Y : Type*} {X F : Type u}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace HG]
    (I : ModelWithCorners ℝ V HG) [TopologicalSpace Y] [ChartedSpace HG Y]
    [IsManifold I ∞ Y] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Y × (X × X) → F} {p : Y × (X × X)}
    (hf : ContMDiffAt (I.prod 𝓘(ℝ, X × X)) 𝓘(ℝ, F) ∞ f p) (i j : ℕ) :
    ContMDiffAt (I.prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X [×i]→L[ℝ] X [×j]→L[ℝ] F) ∞
      (fun q ↦ iteratedFDeriv ℝ i
        (fun x ↦ iteratedFDeriv ℝ j (fun ξ ↦ f (q.1, (x, ξ))) q.2.2) q.2.1) p := by
  have hx : ContMDiffAt (I.prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X) ∞
      (fun q : Y × (X × X) ↦ q.2.1) p :=
    (ContinuousLinearMap.fst ℝ X X).contMDiffAt.comp p contMDiffAt_snd
  have hξ : ContMDiffAt (I.prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X) ∞
      (fun q : Y × (X × X) ↦ q.2.2) p :=
    (ContinuousLinearMap.snd ℝ X X).contMDiffAt.comp p contMDiffAt_snd
  have hf₁ : ContMDiffAt ((I.prod 𝓘(ℝ, X)).prod 𝓘(ℝ, X)) 𝓘(ℝ, F) ∞
      (fun q : (Y × X) × X ↦ f (q.1.1, (q.1.2, q.2))) ((p.1, p.2.1), p.2.2) :=
    hf.comp_of_eq (contMDiffAt_fst.fst.prodMk
      (contMDiffAt_fst.snd.prodMk_space contMDiffAt_snd)) rfl
  have hj := contMDiffAt_parameter_jets (I.prod 𝓘(ℝ, X)) hf₁ j
  have hback : ContMDiffAt (I.prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X [×j]→L[ℝ] F) ∞
      (fun q : Y × (X × X) ↦ iteratedFDeriv ℝ j
        (fun ξ ↦ f (q.1, (q.2.1, ξ))) q.2.2) p :=
    hj.comp_of_eq ((contMDiffAt_fst.prodMk hx).prodMk hξ) rfl
  have hf₂ : ContMDiffAt ((I.prod 𝓘(ℝ, X)).prod 𝓘(ℝ, X))
      𝓘(ℝ, X [×j]→L[ℝ] F) ∞ (fun q : (Y × X) × X ↦
        iteratedFDeriv ℝ j (fun ξ ↦ f (q.1.1, (q.2, ξ))) q.1.2)
        ((p.1, p.2.2), p.2.1) :=
    hback.comp_of_eq (contMDiffAt_fst.fst.prodMk
      (contMDiffAt_snd.prodMk_space contMDiffAt_fst.snd)) rfl
  have hi := contMDiffAt_parameter_jets (I.prod 𝓘(ℝ, X)) hf₂ i
  exact hi.comp_of_eq ((contMDiffAt_fst.prodMk hξ).prodMk hx) rfl

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

variable [hG : IsManifold IG ∞ G]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)

include hG hM hσ hτ in
-- The same geometric local model gives both mixed and full jets at a valid point.
private theorem continuousAt_equivariantGlobalSymbol_jets
    {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e'] [MemTrivializationAtlas f'] (i j k : ℕ)
    (a : G × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (ha : a.2.1 ∈ symbolChartDomain E F d e' f') :
    ContinuousAt (fun z : G ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        symbolDerivative
          (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ z.1 p.val)
            d e' f') i j z.2.1 z.2.2) a ∧
    ContinuousAt (fun z : G ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (Function.uncurry
          (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ z.1 p.val)
            d e' f')) z.2) a := by
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℂ (Fin r)
  let Q := EuclideanSpace ℂ (Fin q)
  let H := R →L[ℂ] Q
  let I := 𝓘(ℝ, X)
  let U := symbolChartDomain E F d e' f'
  have hU : IsOpen U := isOpen_symbolChartDomain E F d e' f'
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  let y₀ : M := a.1⁻¹ • d.symm a.2.1
  let c := chartAt X y₀
  let e := trivializationAt R E y₀
  let f := trivializationAt Q F y₀
  have hc : c ∈ atlas X M := chart_mem_atlas X y₀
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hyc : y₀ ∈ c.source := mem_chart_source X y₀
  have hye : y₀ ∈ e.baseSet := mem_baseSet_trivializationAt R E y₀
  have hyf : y₀ ∈ f.baseSet := mem_baseSet_trivializationAt Q F y₀
  let b : (G × G) × (X × X) := ((a.1, a.1⁻¹), a.2)
  let old (z : (G × G) × (X × X)) : M := z.1.2 • d.symm z.2.1
  let φ (z : (G × G) × (X × X)) : X := c (old z)
  let fw (z : G × X) : X := d (z.1 • c.symm z.2)
  let A (z : (G × G) × (X × X)) : Q →L[ℂ] Q :=
    (f'.continuousLinearMapAt ℂ (z.1.1 • old z)).comp
      ((τ.linearMap z.1.1 (old z)).toContinuousLinearMap.comp (f.symmL ℂ (old z)))
  let B (z : (G × G) × (X × X)) : R →L[ℂ] R :=
    (e.continuousLinearMapAt ℂ (old z)).comp
      ((σ.linearMap z.1.2 (d.symm z.2.1)).toContinuousLinearMap.comp
        (e'.symmL ℂ (d.symm z.2.1)))
  let Θ (z : (G × G) × (X × X)) : X →L[ℝ] X :=
    (fderiv ℝ (fun w ↦ fw (z.1.1, w)) (φ z)).adjoint
  let model (z : (G × G) × (X × X)) : H :=
    (A z).comp ((globalSymbolInChart E F p.val c e f (φ z) (Θ z z.2.2)).comp (B z))
  -- Smoothness is first proved with independent forward and backward group parameters.
  have hx : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) I ∞
      (fun z : (G × G) × (X × X) ↦ z.2.1) b :=
    (ContinuousLinearMap.fst ℝ X X).contMDiffAt.comp b contMDiffAt_snd
  have hξ : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) I ∞
      (fun z : (G × G) × (X × X) ↦ z.2.2) b :=
    (ContinuousLinearMap.snd ℝ X X).contMDiffAt.comp b contMDiffAt_snd
  have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hdM ha.1.1).comp b hx
  have hold : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) I ∞ old b :=
    contMDiffAt_fst.snd.smul hbase
  have hφ : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) I ∞ φ b :=
    (contMDiffAt_of_mem_maximalAtlas hcM hyc).comp b hold
  have hfw : ContMDiffAt (IG.prod I) I ∞ fw (a.1, c y₀) := by
    have hc' : ContMDiffAt (IG.prod I) I ∞
        (fun z : G × X ↦ c.symm z.2) (a.1, c y₀) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hcM
        (c.map_source hyc)).comp (a.1, c y₀) contMDiffAt_snd
    have hmove : ContMDiffAt (IG.prod I) I ∞
        (fun z : G × X ↦ z.1 • c.symm z.2) (a.1, c y₀) :=
      contMDiffAt_fst.smul hc'
    have hreturn : a.1 • c.symm (c y₀) = d.symm a.2.1 := by
      rw [c.left_inv hyc]
      exact smul_inv_smul a.1 (d.symm a.2.1)
    have htarget : a.1 • c.symm (c y₀) ∈ d.source := by
      rw [hreturn]
      exact d.map_target ha.1.1
    exact (contMDiffAt_of_mem_maximalAtlas hdM htarget).comp (a.1, c y₀) hmove
  have hdfw : ContMDiffAt (IG.prod I) 𝓘(ℝ, X →L[ℝ] X) ∞
      (fun z : G × X ↦ fderiv ℝ (fun w ↦ fw (z.1, w)) z.2) (a.1, c y₀) := by
    have h := ((continuousMultilinearCurryFin1 ℝ X X) :
      (X [×1]→L[ℝ] X) →L[ℝ] X →L[ℝ] X).contMDiffAt.comp
        (a.1, c y₀) (contMDiffAt_parameter_jets IG hfw 1)
    convert h using 1
    ext z v
    simp
  let J : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ]
      (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro t L; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hΘ : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, X →L[ℝ] X) ∞ Θ b :=
    (J : (X →L[ℝ] X) →L[ℝ] X →L[ℝ] X).contMDiffAt.comp b
      (hdfw.comp_of_eq (contMDiffAt_fst.fst.prodMk hφ) rfl)
  have hA : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, Q →L[ℂ] Q) ∞ A b := by
    have hopen : IsOpen {z : G × M | z.2 ∈ f.baseSet ∧ z.1 • z.2 ∈ f'.baseSet} :=
      (f.open_baseSet.preimage continuous_snd).inter
        (f'.open_baseSet.preimage (continuous_fst.smul continuous_snd))
    have hb : (a.1, y₀) ∈ {z : G × M |
        z.2 ∈ f.baseSet ∧ z.1 • z.2 ∈ f'.baseSet} := by
      refine ⟨hyf, ?_⟩
      change a.1 • (a.1⁻¹ • d.symm a.2.1) ∈ f'.baseSet
      rw [smul_inv_smul]
      exact ha.2
    exact ((τ.contMDiffOn_frameMap IG hτ f f').contMDiffAt (hopen.mem_nhds hb)).comp_of_eq
      (contMDiffAt_fst.fst.prodMk hold) rfl
  have hB : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, R →L[ℂ] R) ∞ B b := by
    have hopen : IsOpen {z : G × M | z.2 ∈ e'.baseSet ∧ z.1 • z.2 ∈ e.baseSet} :=
      (e'.open_baseSet.preimage continuous_snd).inter
        (e.open_baseSet.preimage (continuous_fst.smul continuous_snd))
    have hb : (a.1⁻¹, d.symm a.2.1) ∈ {z : G × M |
        z.2 ∈ e'.baseSet ∧ z.1 • z.2 ∈ e.baseSet} := ⟨ha.1.2, hye⟩
    exact ((σ.contMDiffOn_frameMap IG hσ e' e).contMDiffAt (hopen.mem_nhds hb)).comp_of_eq
      (contMDiffAt_fst.snd.prodMk hbase) rfl
  have hpchart : ContDiffAt ℝ ∞
      (Function.uncurry (globalSymbolInChart E F p.val c e f)) (φ b, Θ b b.2.2) := by
    apply (p.property c hc e f).1.contDiffAt
    apply ((isOpen_symbolChartDomain E F c e f).prod isOpen_univ).mem_nhds
    refine ⟨⟨⟨c.map_source hyc, ?_⟩, ?_⟩, mem_univ _⟩
    · change c.symm (c y₀) ∈ e.baseSet
      rwa [c.left_inv hyc]
    · change c.symm (c y₀) ∈ f.baseSet
      rwa [c.left_inv hyc]
  have hpull : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, H) ∞
      (fun z ↦ globalSymbolInChart E F p.val c e f (φ z) (Θ z z.2.2)) b :=
    hpchart.contMDiffAt.comp b (hφ.prodMk_space (hΘ.clm_apply hξ))
  have hcomp : ContDiff ℝ ∞ (fun z : (Q →L[ℂ] Q) × H ↦ z.1.comp z.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
  have hcomp' : ContDiff ℝ ∞ (fun z : H × (R →L[ℂ] R) ↦ z.1.comp z.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
  have hmodel : ContMDiffAt ((IG.prod IG).prod 𝓘(ℝ, X × X)) 𝓘(ℝ, H) ∞ model b :=
    hcomp.comp_contMDiffAt (hA.prodMk_space
      (hcomp'.comp_contMDiffAt (hpull.prodMk_space hB)))
  have hjets := (contMDiffAt_mixed_parameter_jets (IG.prod IG) hmodel i j).continuousAt
  have hfull := (contMDiffAt_parameter_jets (IG.prod IG) hmodel k).continuousAt
  have hinverse : Continuous (fun z : G × (X × X) ↦ ((z.1, z.1⁻¹), z.2)) :=
    (continuous_fst.prodMk continuous_fst.inv).prodMk continuous_snd
  have hrestricted := hjets.comp_of_eq hinverse.continuousAt rfl
  have hfullRestricted := hfull.comp_of_eq hinverse.continuousAt rfl
  -- Fixed charts agree on an open moving overlap, so all original mixed germs agree there.
  let old' (z : G × X) := z.1⁻¹ • d.symm z.2
  let S := c.source ∩ e.baseSet ∩ f.baseSet
  let W : Set (G × X) := (univ ×ˢ U) ∩ old' ⁻¹' S
  have hold' : ContinuousOn old' (univ ×ˢ U) :=
    continuous_fst.inv.continuousOn.smul (d.continuousOn_symm.comp
      continuous_snd.continuousOn (fun z hz ↦ hz.2.1.1))
  have hW : IsOpen W := hold'.isOpen_inter_preimage
    (isOpen_univ.prod hU) ((c.open_source.inter e.open_baseSet).inter f.open_baseSet)
  have haW : (a.1, a.2.1) ∈ W := ⟨⟨mem_univ _, ha⟩, ⟨⟨hyc, hye⟩, hyf⟩⟩
  have hformula (g : G) (z : X) (hz : (g, z) ∈ W) (ξ : X) :
      globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ g p.val)
        d e' f' z ξ = model ((g, g⁻¹), (z, ξ)) := by
    exact equivariantGlobalSymbolInChart_eq IG σ τ g p.val c d hc hd e e' f f'
      z hz.1.2 hz.2 ξ
  constructor
  · apply hrestricted.congr_of_eventuallyEq
    filter_upwards [(hW.preimage (continuous_fst.prodMk continuous_snd.fst)).mem_nhds haW]
      with z hz
    have hnear : (fun x ↦ iteratedFDeriv ℝ j
        (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ z.1 p.val)
          d e' f' x) z.2.2) =ᶠ[nhds z.2.1]
        (fun x ↦ iteratedFDeriv ℝ j (fun ξ ↦ model ((z.1, z.1⁻¹), (x, ξ))) z.2.2) := by
      filter_upwards [(hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz]
        with x hxW
      rw [funext (hformula z.1 x hxW)]
    exact (hnear.iteratedFDeriv ℝ i).eq_of_nhds
  · apply hfullRestricted.congr_of_eventuallyEq
    filter_upwards [(hW.preimage (continuous_fst.prodMk continuous_snd.fst)).mem_nhds haW]
      with z hz
    have hnear : Function.uncurry
        (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ z.1 p.val)
          d e' f') =ᶠ[nhds z.2] (fun w ↦ model ((z.1, z.1⁻¹), w)) := by
      filter_upwards [(hW.preimage (continuous_const.prodMk continuous_fst)).mem_nhds hz]
        with w hw
      exact hformula z.1 w.1 hw w.2
    exact (hnear.iteratedFDeriv ℝ k).eq_of_nhds

include hG hM hσ hτ in
/-- Every measured mixed jet of the original transported symbol is jointly continuous. -/
theorem continuousOn_symbolDerivative_equivariantGlobalSymbol
    {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e'] [MemTrivializationAtlas f'] (i j : ℕ) :
    ContinuousOn (fun a : G × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
      symbolDerivative
        (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ a.1 p.val)
          d e' f') i j a.2.1 a.2.2)
      {a | a.2.1 ∈ symbolChartDomain E F d e' f'} := by
  intro a ha
  exact (continuousAt_equivariantGlobalSymbol_jets IG σ τ hσ hτ
    p d hd e' f' i j 0 a ha).1.continuousWithinAt

include hG hM hσ hτ in
/-- All full spatial and frequency jets of the original transported symbol are jointly
continuous with the group parameter; inversion is used only as a continuous map. -/
theorem continuousOn_iteratedFDeriv_equivariantGlobalSymbol
    {m : ℝ} (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e'] [MemTrivializationAtlas f'] (k : ℕ) :
    ContinuousOn (fun a : G ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (Function.uncurry
          (globalSymbolInChart E F (equivariantGlobalSymbolLinearMap IG σ τ a.1 p.val)
            d e' f')) a.2)
      {a | a.2.1 ∈ symbolChartDomain E F d e' f'} := by
  intro a ha
  exact (continuousAt_equivariantGlobalSymbol_jets IG σ τ hσ hτ
    p d hd e' f' 0 0 k a ha).2.continuousWithinAt

/-- The original coordinate, cotangent, output-frame and input-frame transport data.
This tuple is an implementation interface for their common compact-family estimates. -/
def equivariantSymbolCoordinateData
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f']
    (g : G) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × ((EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) × ((EuclideanSpace ℂ (Fin q) →L[ℂ]
      EuclideanSpace ℂ (Fin q)) × (EuclideanSpace ℂ (Fin r) →L[ℂ]
      EuclideanSpace ℂ (Fin r)))) := by
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let old := g⁻¹ • d.symm x
  exact (c old, ((fderiv ℝ (fun w ↦ d (g • c.symm w)) (c old)).adjoint,
    ((f'.continuousLinearMapAt ℂ (g • old)).comp
      ((τ.linearMap g old).toContinuousLinearMap.comp (f.symmL ℂ old)),
      (e.continuousLinearMapAt ℂ old).comp
        ((σ.linearMap g⁻¹ (d.symm x)).toContinuousLinearMap.comp (e'.symmL ℂ (d.symm x))))))

include hG hM hσ hτ in
/-- All spatial jets of the same coordinate and frame tuple are jointly continuous. -/
theorem continuousOn_iteratedFDeriv_equivariantSymbolCoordinateData
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f'] (k : ℕ) :
    ContinuousOn (fun a : G × EuclideanSpace ℝ (Fin n) ↦
      iteratedFDeriv ℝ k (equivariantSymbolCoordinateData σ τ c d e e' f f' a.1) a.2)
      {a | a.2 ∈ symbolChartDomain E F d e' f' ∧
        a.1⁻¹ • d.symm a.2 ∈ c.source ∩ e.baseSet ∩ f.baseSet} := by
  classical
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℂ (Fin r)
  let Q := EuclideanSpace ℂ (Fin q)
  let I := 𝓘(ℝ, X)
  let H := X × ((X →L[ℝ] X) × ((Q →L[ℂ] Q) × (R →L[ℂ] R)))
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  intro a ha
  have ht := ha.1
  have hs := ha.2
  let y₀ : M := a.1⁻¹ • d.symm a.2
  let b : (G × G) × X := ((a.1, a.1⁻¹), a.2)
  let old (z : (G × G) × X) : M := z.1.2 • d.symm z.2
  let φ (z : (G × G) × X) : X := c (old z)
  let fw (z : G × X) : X := d (z.1 • c.symm z.2)
  let A (z : (G × G) × X) : Q →L[ℂ] Q :=
    (f'.continuousLinearMapAt ℂ (z.1.1 • old z)).comp
      ((τ.linearMap z.1.1 (old z)).toContinuousLinearMap.comp (f.symmL ℂ (old z)))
  let B (z : (G × G) × X) : R →L[ℂ] R :=
    (e.continuousLinearMapAt ℂ (old z)).comp
      ((σ.linearMap z.1.2 (d.symm z.2)).toContinuousLinearMap.comp
        (e'.symmL ℂ (d.symm z.2)))
  let Θ (z : (G × G) × X) : X →L[ℝ] X :=
    (fderiv ℝ (fun w ↦ fw (z.1.1, w)) (φ z)).adjoint
  let model (z : (G × G) × X) : H := (φ z, (Θ z, (A z, B z)))
  -- Work with two independent smooth parameters until all spatial derivatives are taken.
  have hx : ContMDiffAt ((IG.prod IG).prod I) I ∞
      (fun z : (G × G) × X ↦ z.2) b := contMDiffAt_snd
  have hbase := (contMDiffAt_symm_of_mem_maximalAtlas hdM ht.1.1).comp b hx
  have hold : ContMDiffAt ((IG.prod IG).prod I) I ∞ old b :=
    contMDiffAt_fst.snd.smul hbase
  have hφ : ContMDiffAt ((IG.prod IG).prod I) I ∞ φ b :=
    (contMDiffAt_of_mem_maximalAtlas hcM hs.1.1).comp b hold
  have hfw : ContMDiffAt (IG.prod I) I ∞ fw (a.1, c y₀) := by
    have hc' : ContMDiffAt (IG.prod I) I ∞
        (fun z : G × X ↦ c.symm z.2) (a.1, c y₀) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hcM
        (c.map_source hs.1.1)).comp (a.1, c y₀) contMDiffAt_snd
    have hmove : ContMDiffAt (IG.prod I) I ∞
        (fun z : G × X ↦ z.1 • c.symm z.2) (a.1, c y₀) :=
      contMDiffAt_fst.smul hc'
    have hreturn : a.1 • c.symm (c y₀) = d.symm a.2 := by
      rw [c.left_inv hs.1.1]
      exact smul_inv_smul a.1 (d.symm a.2)
    have htarget : a.1 • c.symm (c y₀) ∈ d.source := by
      rw [hreturn]
      exact d.map_target ht.1.1
    exact (contMDiffAt_of_mem_maximalAtlas hdM htarget).comp (a.1, c y₀) hmove
  have hdfw : ContMDiffAt (IG.prod I) 𝓘(ℝ, X →L[ℝ] X) ∞
      (fun z : G × X ↦ fderiv ℝ (fun w ↦ fw (z.1, w)) z.2) (a.1, c y₀) := by
    have h := ((continuousMultilinearCurryFin1 ℝ X X) :
      (X [×1]→L[ℝ] X) →L[ℝ] X →L[ℝ] X).contMDiffAt.comp
        (a.1, c y₀) (contMDiffAt_parameter_jets IG hfw 1)
    convert h using 1
    ext z v
    simp
  let J : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ]
      (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro t L; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hΘ : ContMDiffAt ((IG.prod IG).prod I) 𝓘(ℝ, X →L[ℝ] X) ∞ Θ b :=
    (J : (X →L[ℝ] X) →L[ℝ] X →L[ℝ] X).contMDiffAt.comp b
      (hdfw.comp_of_eq (contMDiffAt_fst.fst.prodMk hφ) rfl)
  have hA : ContMDiffAt ((IG.prod IG).prod I) 𝓘(ℝ, Q →L[ℂ] Q) ∞ A b := by
    have hopen : IsOpen {z : G × M | z.2 ∈ f.baseSet ∧ z.1 • z.2 ∈ f'.baseSet} :=
      (f.open_baseSet.preimage continuous_snd).inter
        (f'.open_baseSet.preimage (continuous_fst.smul continuous_snd))
    have hb : (a.1, y₀) ∈ {z : G × M |
        z.2 ∈ f.baseSet ∧ z.1 • z.2 ∈ f'.baseSet} := by
      refine ⟨hs.2, ?_⟩
      change a.1 • (a.1⁻¹ • d.symm a.2) ∈ f'.baseSet
      rw [smul_inv_smul]
      exact ht.2
    exact ((τ.contMDiffOn_frameMap IG hτ f f').contMDiffAt (hopen.mem_nhds hb)).comp_of_eq
      (contMDiffAt_fst.fst.prodMk hold) rfl
  have hB : ContMDiffAt ((IG.prod IG).prod I) 𝓘(ℝ, R →L[ℂ] R) ∞ B b := by
    have hopen : IsOpen {z : G × M | z.2 ∈ e'.baseSet ∧ z.1 • z.2 ∈ e.baseSet} :=
      (e'.open_baseSet.preimage continuous_snd).inter
        (e.open_baseSet.preimage (continuous_fst.smul continuous_snd))
    have hb : (a.1⁻¹, d.symm a.2) ∈ {z : G × M |
        z.2 ∈ e'.baseSet ∧ z.1 • z.2 ∈ e.baseSet} := ⟨ht.1.2, hs.1.2⟩
    exact ((σ.contMDiffOn_frameMap IG hσ e' e).contMDiffAt (hopen.mem_nhds hb)).comp_of_eq
      (contMDiffAt_fst.snd.prodMk hbase) rfl
  have hmodel : ContMDiffAt ((IG.prod IG).prod I) 𝓘(ℝ, H) ∞ model b :=
    hφ.prodMk_space (hΘ.prodMk_space (hA.prodMk_space hB))
  have hjets := (contMDiffAt_parameter_jets (IG.prod IG) hmodel k).continuousAt
  have hinverse : Continuous (fun z : G × X ↦ ((z.1, z.1⁻¹), z.2)) :=
    (continuous_fst.prodMk continuous_fst.inv).prodMk continuous_snd
  exact (hjets.comp_of_eq hinverse.continuousAt rfl).continuousWithinAt

end AtiyahSinger
