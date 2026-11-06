/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.VariableRankDifferentialOperator

import AtiyahSinger.Geometry.AtlasChartLocalization

/-!
# Principal symbols without a global rank choice

Public module ID: M0276.

D03: the highest-order coordinate polynomials of an AtlasDifferentialOperator
glue to a unique map on the original fibers. Its symbol is selected from that
existence theorem rather than supplied as an assumption on the operator.
Ellipticity uses the selected map and imposes invertibility only away from
the zero cotangent vectors. In particular, no equal-rank assumption or
positive-dimensional-base assumption is built into the definition.

Sources: Spin Geometry III.1.1-1.3, pp.167-168. The full real-scaling formula
is the polynomial formulation of degree-m homogeneity and includes order
zero and scaling by zero. Hausdorffness and second countability support the
bump localization used to identify the symbol from global smooth sections.
Compactness and a uniform rank bound are not required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hS : SecondCountableTopology M]

include hM hT hS

namespace AtlasDifferentialOperator

variable {m : ℕ}


set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
open scoped Topology SchwartzMap in
/-- The leading coordinate polynomials determine a unique symbol on the original fibers. -/
theorem existsUnique_principalSymbol (P : AtlasDifferentialOperator A B m) :
    ∃! σ : ∀ x : M,
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) → (E x →ₗ[ℂ] F x),
      HasAtlasPrincipalSymbol A B m P.toLinearMap σ := by
  /- The proof compares coordinate expressions using the same global test
  sections. First, the scalar power jet formula shows that applying an order-m
  expression to φ^m s, with φ vanishing at the base point, detects only its
  leading polynomial, multiplied by a nonzero factorial and power of -i.
  Smooth cutoffs then realize any specified covector as dφ and any input
  fiber vector as the value of s. Evaluating the same global section in two
  expressions forces their transported principal maps to agree.
  Finally, covering reference charts select an original-fiber map at each
  point; the test identity proves its specification and uniqueness. Source
  and target local ranks remain independent. No finite cover, global rank
  bound or compactness is used. -/
  classical
  -- Stage 1: the Faà di Bruno expansion identifies the jets of a vanishing scalar power.
  have eq_atomic {n : ℕ} (c : OrderedFinpartition n) (h : c.length = n) :
      c = OrderedFinpartition.atomic n := by
    have hsum : ∑ i, c.partSize i = c.length := by
      have hh := Fintype.card_congr c.equivSigma
      simpa [Fintype.card_sigma, h] using hh
    have hparts (i : Fin c.length) : c.partSize i = 1 := by
      have hsum' : ∑ j : Fin c.length, 1 = ∑ j, c.partSize j := by
        simpa using hsum.symm
      exact ((Finset.sum_eq_sum_iff_of_le (fun j _ ↦ c.partSize_pos j)).mp hsum' i
        (Finset.mem_univ i)).symm
    rcases c with ⟨length, partSize, hpos, emb, hmono, horder, hdisjoint, hcover⟩
    dsimp only at h hparts
    subst length
    obtain rfl : partSize = fun _ ↦ 1 := funext hparts
    have hemb : (fun i : Fin n ↦ emb i 0) = id := horder.eq_id
    apply OrderedFinpartition.ext
    · rfl
    · rfl
    · apply heq_of_eq
      funext i j
      have hj : j = 0 := Subsingleton.elim _ _
      rw [hj]
      exact congrFun hemb i
  have power_jet_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ ∞ f x) (hx : f x = 0)
      (m k : ℕ) (hk : k < m) :
      iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m) x = 0 := by
    classical
    have hcomp := iteratedFDeriv_comp
      (f := f) (g := fun t : ℝ ↦ t ^ m) (n := ∞)
      (by fun_prop) hf (show (k : ℕ∞ω) ≤ ∞ by simp)
    change iteratedFDeriv ℝ k ((fun t : ℝ ↦ t ^ m) ∘ f) x = 0
    rw [hcomp]
    simp only [FormalMultilinearSeries.taylorComp]
    apply Finset.sum_eq_zero
    intro c _
    ext v
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      ftaylorSeries, hx, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      iteratedDeriv_fun_pow_zero,
      ite_eq_right (Nat.ne_of_lt (lt_of_le_of_lt c.length_le hk)), zero_apply]
    simp
  have power_jet_top {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : E → ℝ) (x : E) (hf : ContDiffAt ℝ ∞ f x) (hx : f x = 0)
      (m : ℕ) (v : Fin m → E) :
      iteratedFDeriv ℝ m (fun y ↦ (f y) ^ m) x v =
        (m.factorial : ℝ) * ∏ j, fderiv ℝ f x (v j) := by
    classical
    change iteratedFDeriv ℝ m ((fun t : ℝ ↦ t ^ m) ∘ f) x v = _
    rw [iteratedFDeriv_comp (n := ∞) (by fun_prop) hf (by simp)]
    simp only [FormalMultilinearSeries.taylorComp, _root_.sum_apply]
    rw [Finset.sum_eq_single (OrderedFinpartition.atomic m)]
    · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hx,
        iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_fun_pow_zero,
        OrderedFinpartition.atomic_length, ite_true]
      change (∏ i : Fin m, iteratedFDeriv ℝ 1 f x (fun _ ↦ v i)) •
        (m.factorial : ℝ) = _
      have hval (i : Fin m) : iteratedFDeriv ℝ 1 f x (fun _ ↦ v i) =
          fderiv ℝ f x (v i) := iteratedFDeriv_one_apply _
      simp only [hval, smul_eq_mul, mul_comm]
    · intro c _ hc
      have hc' : c.length < m := lt_of_le_of_ne c.length_le (fun h ↦ hc (eq_atomic c h))
      simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hx,
        iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_fun_pow_zero,
        ite_eq_right (Nat.ne_of_lt hc')]
      simp
    · simp
  -- Stage 2: multiplying by a changing frame vector keeps only its value at the base point.
  have power_smul_jet {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → ℝ) (g : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x)
      (hg : ContDiffAt ℝ ∞ g x) (hx : f x = 0) (m k : ℕ) (hk : k ≤ m) :
      iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • g y) x =
        iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • g x) x := by
    classical
    have hpower := hf.pow m
    have hdiff := hg.sub (contDiffAt_const (c := g x))
    obtain ⟨u, hu, hxu, hfu⟩ := hpower.contDiffOn' (m := (k : ℕ∞ω)) (by simp) (by simp)
    obtain ⟨v, hv, hxv, hgv⟩ := hdiff.contDiffOn' (m := (k : ℕ∞ω)) (by simp) (by simp)
    simp only [Set.insert_eq_of_mem (Set.mem_univ x), Set.univ_inter] at hfu hgv
    let s := u ∩ v
    have hs : UniqueDiffOn ℝ s := (hu.inter hv).uniqueDiffOn
    have hxs : x ∈ s := ⟨hxu, hxv⟩
    have hzero : iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • (g y - g x)) x = 0 := by
      have hbound := norm_iteratedFDerivWithin_smul_le
        (hfu.mono Set.inter_subset_left) (hgv.mono Set.inter_subset_right) hs hxs
        (show (k : ℕ∞ω) ≤ k from le_rfl)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := k)
        (f := fun y ↦ (f y) ^ m • (g y - g x)) hs
        ((hpower.smul hdiff).of_le (by simp)) hxs] at hbound
      have hsum : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun y ↦ (f y) ^ m) s x‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun y ↦ g y - g x) s x‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        by_cases him : i < m
        · rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := i) hs
            (hpower.of_le (by simp)) hxs,
            power_jet_zero f x hf hx m i him]
          simp
        · have hki : k - i = 0 := by omega
          rw [hki, norm_iteratedFDerivWithin_zero, sub_self, norm_zero, mul_zero]
      rw [hsum] at hbound
      exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
    have hsub : (fun y ↦ (f y) ^ m • (g y - g x)) =
        (fun y ↦ (f y) ^ m • g y) - (fun y ↦ (f y) ^ m • g x) := by
      funext y
      exact smul_sub _ _ _
    rw [hsub, iteratedFDeriv_sub_apply (i := k)
      (f := fun y ↦ (f y) ^ m • g y) (g := fun y ↦ (f y) ^ m • g x)
      ((hpower.smul hg).of_le (by simp))
      ((hpower.smul (contDiffAt_const (c := g x))).of_le (by simp))] at hzero
    exact sub_eq_zero.mp hzero
  -- Stage 3: the original finite expression detects exactly its highest-order symbol.
  have coordinate_apply_power {n r q m : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
      (Q : AtiyahSinger.CoordinateDifferentialOperator n r q m U)
      (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℂ (Fin r))
      (x : EuclideanSpace ℝ (Fin n)) (hf : ContDiffAt ℝ ∞ f x)
      (hg : ContDiffAt ℝ ∞ g x) (hx : f x = 0) :
      Q.apply (fun y ↦ (f y) ^ m • g y) x =
        ((-Complex.I) ^ m * (m.factorial : ℂ)) •
          Q.principalSymbol x
            (WithLp.toLp 2 fun j ↦ fderiv ℝ f x (EuclideanSpace.single j 1)) (g x) := by
    classical
    have hjet (k : ℕ) (hk : k ≤ m) := power_smul_jet f g x hf hg hx m k hk
    have hzero (k : ℕ) (hk : k < m) :
        iteratedFDeriv ℝ k (fun y ↦ (f y) ^ m • g y) x = 0 := by
      rw [hjet k (Nat.le_of_lt hk),
        iteratedFDeriv_smul_const_apply ((hf.pow m).of_le (by simp)),
        power_jet_zero f x hf hx m k hk]
      ext v
      simp
    have htop (α : Fin m → Fin n) :
        iteratedFDeriv ℝ m (fun y ↦ (f y) ^ m • g y) x
          (fun j ↦ EuclideanSpace.single (α j) 1) =
        (m.factorial : ℝ) • (∏ j, fderiv ℝ f x (EuclideanSpace.single (α j) 1)) • g x := by
      rw [hjet m le_rfl, iteratedFDeriv_smul_const_apply ((hf.pow m).of_le (by simp))]
      change (iteratedFDeriv ℝ m (fun y ↦ (f y) ^ m) x
        (fun j ↦ EuclideanSpace.single (α j) 1)) • g x = _
      rw [power_jet_top f x hf hx m, mul_smul]
    unfold AtiyahSinger.CoordinateDifferentialOperator.apply
    rw [Finset.sum_eq_single (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))]
    · simp only [htop]
      simp only [AtiyahSinger.CoordinateDifferentialOperator.principalSymbol,
        _root_.sum_apply, smul_apply, ← Complex.coe_smul, Complex.ofReal_natCast,
        map_smul, mul_smul, Finset.smul_sum]
    · intro k _ hk
      have hkm : k.val < m := lt_of_le_of_ne (Nat.le_of_lt_succ k.isLt)
        (fun h ↦ hk (Fin.ext h))
      apply Finset.sum_eq_zero
      intro α _
      simp [hzero k.val hkm]
    · simp
  -- Stage 4: smooth cutoffs realize the same covector and input vector globally.
  have exists_scalar_jet (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      ∃ φ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ ∧
        φ x = 0 ∧ mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let b : SmoothBumpFunction I x := Classical.choice inferInstance
    let ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      ξ.comp (mfderiv I I c.symm (c x))
    let φ : M → ℝ := fun y ↦ b y * ℓ (c y - c x)
    have hc := contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) (chart_mem_atlas _ x))
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ :=
      b.contMDiff_smul (ℓ.contMDiff.comp_contMDiffOn (hc.sub contMDiffOn_const))
    have heq : φ =ᶠ[𝓝 x] (fun y ↦ ℓ (c y - c x)) := by
      filter_upwards [b.eventuallyEq_one] with y hy
      simp [φ, hy]
    refine ⟨φ, hs, ?_, ?_⟩
    · simp [φ]
    · rw [heq.mfderiv_eq]
      have hchart := mdifferentiable_of_mem_atlas (I := I) (chart_mem_atlas _ x)
      have hcx := hchart.mdifferentiableAt (mem_chart_source _ x)
      change mfderiv I 𝓘(ℝ, ℝ) (ℓ ∘ (fun y ↦ c y - c x)) x = ξ
      erw [mfderiv_comp x (ℓ.contMDiff (n := ∞) |>.contMDiffAt.mdifferentiableAt (by simp))
        (hcx.sub (mdifferentiableAt_const (c := c x))), mfderiv_eq_fderiv, ℓ.fderiv,
        mfderiv_sub hcx (mdifferentiableAt_const (c := c x)), mfderiv_const, sub_zero]
      dsimp only [ℓ]
      change (ξ.comp (mfderiv I I c.symm (c x))).comp (mfderiv I I c x) = ξ
      erw [ContinuousLinearMap.comp_assoc, hchart.symm_comp_deriv (mem_chart_source _ x)]
      exact ContinuousLinearMap.comp_id ξ
  have exists_section_value (x : M) (v : E x) :
      ∃ s : A.smoothSections, s.val x = v := by
    classical
    let H := EuclideanSpace ℝ (Fin n)
    let c := chartAt H x
    obtain ⟨i, hxi⟩ := A.covers x
    have hcx : c x ∈ c.target ∩ c.symm ⁻¹' (A.chart i).baseSet := by
      exact ⟨c.map_source (mem_chart_source H x), by simpa [c] using hxi⟩
    have hU : IsOpen (c.target ∩ c.symm ⁻¹' (A.chart i).baseSet) :=
      c.isOpen_inter_preimage_symm (A.chart i).open_baseSet
    obtain ⟨b, _, hb⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, H)) (c x)).mem_iff.mp
        (hU.mem_nhds hcx)
    let L : AtlasChartCutoff A c := {
      frameIndex := i
      cutoff := b
      smooth_cutoff := b.contMDiff.contDiff
      compact_support := b.hasCompactSupport
      support_subset := hb }
    let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
    let a := e.symm (A.frameLinearEquiv i x hxi v)
    have hcompact : HasCompactSupport (fun z : H ↦ b z • a) :=
      b.hasCompactSupport.smul_right
    have hsmooth : ContDiff ℝ ∞ (fun z : H ↦ b z • a) :=
      b.contMDiff.contDiff.smul contDiff_const
    let f : 𝓢(H, EuclideanSpace ℂ (Fin (A.rank i))) := hcompact.toSchwartzMap hsmooth
    refine ⟨L.extend (chart_mem_atlas H x) f, ?_⟩
    -- Both original cutoffs have value one, so the specified frame inverse recovers v.
    have hvalid : x ∈ c.source ∩ (A.chart i).baseSet := ⟨mem_chart_source H x, hxi⟩
    change L.extendedFunction f x = v
    simp only [AtlasChartCutoff.extendedFunction, L, dite_eq_left hvalid]
    change (b (c x) : ℂ) • (A.frameLinearEquiv i x hxi).symm (e (b (c x) • a)) = v
    rw [b.eq_one, Complex.ofReal_one, one_smul, one_smul]
    rw [show e a = A.frameLinearEquiv i x hxi v from e.apply_symm_apply _]
    exact (A.frameLinearEquiv i x hxi).symm_apply_apply v
  -- Stage 5: compare every chart expression on one actual global test section.
  have exists_power_section (φ : M → ℝ)
      (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (s : A.smoothSections) :
      ∃ t : A.smoothSections, ∀ y, t.val y = ((φ y) ^ m : ℂ) • s.val y := by
    refine ⟨⟨fun y ↦ ((φ y) ^ m : ℂ) • s.val y, ?_⟩, fun _ ↦ rfl⟩
    intro i
    have hpower : ContDiff ℝ ∞ (fun t : ℝ ↦ (t ^ m : ℂ)) :=
      Complex.ofRealCLM.contDiff.pow m
    have hscalar := hpower.comp_contMDiff hφ
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × (Fin (A.rank i) → ℂ) ↦ p.1 • p.2) := contDiff_smul
    apply (hmul.contMDiff.comp_contMDiffOn
      (hscalar.contMDiffOn.prodMk_space (s.property i))).congr
    intro y hy
    exact (A.linear i y hy).map_smul ((φ y) ^ m : ℂ) (s.val y)
  have test_evaluation
      (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
      (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ φ)
      (hφx : φ x = 0) (hφd : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) φ x = ξ)
      (s t : A.smoothSections) (ht : ∀ y, t.val y = ((φ y) ^ m : ℂ) • s.val y)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index)
      (U : Set M) (Q : CoordinateDifferentialOperator n (A.rank i) (B.rank j) m (c '' U))
      (hQ : HasAtlasCoordinateExpression A B m P.toLinearMap c i j U Q) (hxU : x ∈ U) :
      (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
          ((B.chart j ⟨x, (P.toLinearMap t).val x⟩).2) =
        ((-Complex.I) ^ m * (m.factorial : ℂ)) •
          Q.principalSymbol (c x) (covectorInChart c x ξ)
            ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
              ((A.chart i ⟨x, s.val x⟩).2)) := by
    have hx := hQ.1 hxU
    let ψ : EuclideanSpace ℝ (Fin n) → ℝ := φ ∘ c.symm
    let g := atlasSectionInChart A c i s.val
    have hcsm := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (n := ∞) hc) (c.map_source hx.1.1)
    have hψ : ContDiffAt ℝ ∞ ψ (c x) :=
      (hφ.contMDiffAt.comp (c x) hcsm).contDiffAt
    have hg : ContDiffAt ℝ ∞ g (c x) := by
      have hsection := (s.property i).contMDiffAt
        ((A.chart i).open_baseSet.mem_nhds (show c.symm (c x) ∈ (A.chart i).baseSet by
          simpa [c.left_inv hx.1.1] using hx.1.2))
      let e := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
      exact ((e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp (c x)
        (hsection.comp (c x) hcsm)).contDiffAt
    have hψx : ψ (c x) = 0 := by simp [ψ, c.left_inv hx.1.1, hφx]
    have hcoords : atlasSectionInChart A c i t.val =ᶠ[𝓝 (c x)]
        (fun z ↦ (ψ z) ^ m • g z) := by
      filter_upwards [(c.tendsto_symm hx.1.1).eventually
        ((A.chart i).open_baseSet.mem_nhds hx.1.2)] with z hz
      dsimp only [atlasSectionInChart, ψ, g, Function.comp_apply]
      rw [ht, (A.linear i (c.symm z) hz).map_smul, map_smul,
        ← Complex.ofReal_pow, Complex.coe_smul]
    have happly : Q.apply (atlasSectionInChart A c i t.val) (c x) =
        Q.apply (fun z ↦ (ψ z) ^ m • g z) (c x) := by
      simp only [CoordinateDifferentialOperator.apply]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro α _
      rw [(hcoords.iteratedFDeriv ℝ k.val).eq_of_nhds]
    have hdψ : fderiv ℝ ψ (c x) =
        ξ.comp (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm (c x)) := by
      have hchain := mfderiv_comp (c x) (hφ.contMDiffAt.mdifferentiableAt (by simp))
        (hcsm.mdifferentiableAt (by simp))
      dsimp only [ψ]
      have hleft : c.symm (c x) = x := c.left_inv hx.1.1
      erw [hleft, hφd] at hchain
      rw [mfderiv_eq_fderiv] at hchain
      exact hchain
    have hcov : (WithLp.toLp 2 fun j ↦ fderiv ℝ ψ (c x)
        (EuclideanSpace.single j 1)) = covectorInChart c x ξ := by
      rw [hdψ]
      rfl
    rw [hQ.2 t x hxU, happly, coordinate_apply_power Q ψ g (c x) hψ hg hψx, hcov]
    congr 1
    dsimp only [g, atlasSectionInChart]
    rw [c.left_inv hx.1.1]
  -- Stage 6: use covering reference charts, with their original independent local ranks.
  let c (x : M) := chartAt (EuclideanSpace ℝ (Fin n)) x
  choose i hi using A.covers
  choose j hj using B.covers
  let e (x : M) : E x ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (A.rank (i x))) :=
    (A.frameLinearEquiv (i x) x (hi x)).trans
      (EuclideanSpace.equiv (Fin (A.rank (i x))) ℂ).symm.toLinearEquiv
  let f (x : M) : F x ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (B.rank (j x))) :=
    (B.frameLinearEquiv (j x) x (hj x)).trans
      (EuclideanSpace.equiv (Fin (B.rank (j x))) ℂ).symm.toLinearEquiv
  have hlocal (x : M) := P.isAtlasDifferentialOperator (c x) (chart_mem_atlas _ x)
    (i x) (j x) x ⟨⟨mem_chart_source _ x, hi x⟩, hj x⟩
  choose U hU hxU Q hQ using hlocal
  let σ (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
      E x →ₗ[ℂ] F x :=
    (f x).symm.toLinearMap.comp
      (((Q x).principalSymbol (c x x) (covectorInChart (c x) x ξ)).toLinearMap.comp
        (e x).toLinearMap)
  let C : ℂ := (-Complex.I) ^ m * (m.factorial : ℂ)
  have hC : C ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (by exact_mod_cast Nat.factorial_ne_zero m)
  have hσ : HasAtlasPrincipalSymbol A B m P.toLinearMap σ := by
    intro c' hc' i' j' V _ R hR x hx ξ v
    -- Both expressions act on the same original global section, so their symbols agree.
    obtain ⟨φ, hφ, hφx, hφd⟩ := exists_scalar_jet x ξ
    obtain ⟨s, hs⟩ := exists_section_value x v
    obtain ⟨t, ht⟩ := exists_power_section φ hφ s
    have htest0 := test_evaluation x ξ φ hφ hφx hφd s t ht
      (c x) (chart_mem_atlas _ x) (i x) (j x) (U x) (Q x) (hQ x) (hxU x)
    have htest : (P.toLinearMap t).val x = C • σ x ξ v := by
      apply (f x).injective
      rw [map_smul]
      change f x ((P.toLinearMap t).val x) = C •
        f x ((f x).symm ((Q x).principalSymbol (c x x)
          (covectorInChart (c x) x ξ) (e x v)))
      rw [(f x).apply_symm_apply]
      simpa [f, e, C, SmoothComplexBundleAtlas.frameLinearEquiv, hs] using htest0
    have htest1 := test_evaluation x ξ φ hφ hφx hφd s t ht c' hc' i' j' V R hR hx
    rw [htest, (B.linear j' x (hR.1 hx).2).map_smul, map_smul, hs] at htest1
    exact smul_right_injective _ hC htest1
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  funext x ξ
  apply LinearMap.ext
  intro v
  have hτx := hτ (c x) (chart_mem_atlas _ x) (i x) (j x)
    (U x) (hU x) (Q x) (hQ x) x (hxU x) ξ v
  have hσx := hσ (c x) (chart_mem_atlas _ x) (i x) (j x)
    (U x) (hU x) (Q x) (hQ x) x (hxU x) ξ v
  apply (f x).injective
  exact hτx.trans hσx.symm

/-- The original-fiber symbol selected from its unique local polynomial specification. -/
def principalSymbol (P : AtlasDifferentialOperator A B m) :
    ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) →
      (E x →ₗ[ℂ] F x) :=
  Classical.choose P.existsUnique_principalSymbol.exists

/-- The selected symbol agrees with every local expression of the given section operator. -/
theorem hasAtlasPrincipalSymbol (P : AtlasDifferentialOperator A B m) :
    HasAtlasPrincipalSymbol A B m P.toLinearMap P.principalSymbol := by
  /- Use the specification of the witness chosen from existsUnique_principalSymbol.
  Its quantifiers retain the actual atlas charts, the same section action and
  every representing coordinate expression; no new local symbol is selected. -/
  exact Classical.choose_spec P.existsUnique_principalSymbol.exists

/-- The principal symbol is homogeneous of degree m under every real cotangent scaling. -/
theorem principalSymbol_smul (P : AtlasDifferentialOperator A B m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) (t : ℝ) :
    P.principalSymbol x (t • ξ) = (t : ℂ) ^ m • P.principalSymbol x ξ := by
  /- Fix covering charts and a local expression of P. The inverse-chart derivative
  is linear on covectors, and every top-degree monomial contains precisely m
  covector coordinates. Its scaling factor is therefore t^m. Apply the symbol
  specification and the linearity and injectivity of the same fiber charts to
  transport the identity to the original fibers. The finite polynomial identity
  also applies when t = 0, m = 0, or all top-order coefficients vanish. -/
  classical
  -- Use one representing polynomial for both original cotangent vectors.
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨i, hi⟩ := A.covers x
  obtain ⟨j, hj⟩ := B.covers x
  obtain ⟨U, hU, hxU, Q, hQ⟩ :=
    P.isAtlasDifferentialOperator c (chart_mem_atlas _ x) i j x
      ⟨⟨mem_chart_source _ x, hi⟩, hj⟩
  have hscale : covectorInChart c x (t • ξ) = t • covectorInChart c x ξ := by
    ext a
    rfl
  have hpoly : Q.principalSymbol (c x) (t • covectorInChart c x ξ) =
      (t : ℂ) ^ m • Q.principalSymbol (c x) (covectorInChart c x ξ) := by
    simp only [CoordinateDifferentialOperator.principalSymbol, PiLp.smul_apply,
      smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.smul_sum, ← Complex.coe_smul, smul_smul,
      Complex.ofReal_mul, Complex.ofReal_pow]
  apply LinearMap.ext
  intro v
  have h₁ := P.hasAtlasPrincipalSymbol c (chart_mem_atlas _ x) i j U hU Q hQ x hxU (t • ξ) v
  have h₂ := P.hasAtlasPrincipalSymbol c (chart_mem_atlas _ x) i j U hU Q hQ x hxU ξ v
  rw [hscale, hpoly, smul_apply] at h₁
  have hout := h₁.trans (congrArg (fun w ↦ (t : ℂ) ^ m • w) h₂.symm)
  -- The actual output frame is injective even when its rank differs from the input rank.
  apply (B.frameLinearEquiv j x hj).injective
  apply (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.injective
  change _ = (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
    ((B.chart j ⟨x, ((t : ℂ) ^ m • P.principalSymbol x ξ) v⟩).2)
  rw [LinearMap.smul_apply, (B.linear j x hj).map_smul, map_smul]
  exact hout

/-- Ellipticity is bijectivity of the actual principal symbol at every nonzero covector. -/
def IsElliptic (P : AtlasDifferentialOperator A B m) : Prop :=
  ∀ (x : M) (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ), ξ ≠ 0 →
    Function.Bijective (P.principalSymbol x ξ)

end AtlasDifferentialOperator

end AtiyahSinger
