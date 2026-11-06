/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialLocalFunctional
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.SchwartzPairingFubini

/-!
# Distributional parameter pairings commute with the original atlas PDO

Public module ID: M0292.

A compactly supported smooth family of actual sections may be paired with
one continuous Schwartz functional in its independent parameter. Applying
the original whole PDO commutes with this pairing, including its smoothing
remainder. Pointwise fiber duals specify the two paired sections, without
replacing a full family by an algebraic finite tensor span.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff SchwartzMap Topology

variable {n k d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

local notation "Y" => Fin k → ℝ
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

set_option maxHeartbeats 1200000 in

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same whole PDO commutes with compactly supported distributional parameter pairing. -/
theorem AtlasPseudodifferentialOperator.apply_schwartz_parameter_pairing {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m)
    (T : 𝓢(Y, EuclideanSpace ℂ (Fin d)) →L[ℂ] ℂ)
    (u : Y → Fin d → A.smoothSections)
    (hu : ∀ (l : Fin d) (i : A.Index),
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : Y × M ↦ (A.chart i ⟨p.2, (u p.1 l).val p.2⟩).2)
        (Set.univ ×ˢ (A.chart i).baseSet))
    (C : Set Y) (hC : IsCompact C) (hc : ∀ y ∉ C, ∀ i, u y i = 0)
    (s : A.smoothSections) (t : B.smoothSections)
    (hs : ∀ (x : M) (l : E x →ₗ[ℂ] ℂ), ∃ f : 𝓢(Y, EuclideanSpace ℂ (Fin d)),
      (∀ y i, f y i = l ((u y i).val x)) ∧ l (s.val x) = T f)
    (ht : ∀ (x : M) (l : F x →ₗ[ℂ] ℂ), ∃ f : 𝓢(Y, EuclideanSpace ℂ (Fin d)),
      (∀ y i, f y i = l ((P.toLinearMap (u y i)).val x)) ∧ l (t.val x) = T f) :
    P.toLinearMap s = t := by
  classical
  obtain ⟨L⟩ := nonempty_atlasBundlePresentation A
  obtain ⟨K⟩ := nonempty_atlasBundlePresentation B
  let U (j : Fin L.size) :=
    (L.chart j).target ∩ (L.chart j).symm ⁻¹' (A.chart (L.frameIndex j)).baseSet
  let H (j : Fin L.size) := (L.chart j) '' tsupport (L.cutoff j)
  have hU (j : Fin L.size) : IsOpen (U j) :=
    (L.chart j).isOpen_inter_preimage_symm (A.chart (L.frameIndex j)).open_baseSet
  have hH (j : Fin L.size) : IsCompact (H j) :=
    (L.compact_support j).image_of_continuousOn
      ((L.chart j).continuousOn.mono (fun x hx ↦ (L.support_subset j hx).1))
  have hHU (j : Fin L.size) : H j ⊆ U j := by
    rintro _ ⟨x, hx, rfl⟩
    have hs := (L.support_subset j hx).1
    refine ⟨(L.chart j).map_source hs, ?_⟩
    change (L.chart j).symm ((L.chart j) x) ∈ (A.chart (L.frameIndex j)).baseSet
    rw [(L.chart j).left_inv hs]
    exact (L.support_subset j hx).2
  -- Original compact input supports receive plateaus only for exact reconstruction.
  have hplateau (j : Fin L.size) : ∃ η : X → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ U j ∧
        ∀ z ∈ H j, η z = 1 := by
    obtain ⟨η, hη, hcη, hsη, honeη⟩ := exists_compact_cutoff_one_near
      (H j) (U j) (hH j) (hU j) (hHU j)
    refine ⟨η, hη, hcη, hsη, fun z hz ↦ ?_⟩
    exact (show z ∈ {x | η x = 1} from interior_subset (honeη hz))
  choose η hη hcη hsη honeη using hplateau
  let D (j : Fin L.size) : AtlasChartCutoff A (L.chart j) :=
    { frameIndex := L.frameIndex j
      cutoff := η j
      smooth_cutoff := hη j
      compact_support := hcη j
      support_subset := hsη j }
  have hpiece (j : Fin L.size) (s : A.smoothSections) (x : M) :
      ((D j).extend (L.chart_mem_atlas j) (L.localize j s)).val x =
        (L.cutoff j x : ℂ) • s.val x := by
    change (D j).extendedFunction (L.localize j s) x = _
    by_cases hx : x ∈ (L.chart j).source ∩ (A.chart (L.frameIndex j)).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, D, dite_eq_left hx]
      change (η j ((L.chart j) x) : ℂ) • (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
        ((EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ)
          (L.localizedFunction j s ((L.chart j) x))) = _
      simp only [AtlasBundlePresentation.localizedFunction,
        ite_eq_left ((L.chart j).map_source hx.1), atlasSectionInChart]
      rw [(L.chart j).left_inv hx.1, map_smul,
        ContinuousLinearEquiv.apply_symm_apply, map_smul]
      change _ • ((L.cutoff j x : ℂ) •
        (A.frameLinearEquiv (L.frameIndex j) x hx.2).symm
          ((A.frameLinearEquiv (L.frameIndex j) x hx.2) (s.val x))) = _
      rw [LinearEquiv.symm_apply_apply]
      by_cases hχ : L.cutoff j x = 0
      · simp [hχ]
      · rw [honeη j _ ⟨x, subset_tsupport _ hχ, rfl⟩, Complex.ofReal_one, one_smul]
    · have hχ : L.cutoff j x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hx (L.support_subset j h))
      simp [AtlasChartCutoff.extendedFunction, D, hx, hχ]
  have hreconstruct (s : A.smoothSections) :
      (∑ j, (D j).extend (L.chart_mem_atlas j) (L.localize j s)) = s := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply, hpiece]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, L.sum_cutoff, Complex.ofReal_one, one_smul]
  -- Each actual localized input is jointly smooth with its original fixed compact support.
  let f (j : Fin L.size) (l : Fin d) (y : Y) := L.localize j (u y l)
  have hf (j : Fin L.size) (l : Fin d) : ContDiff ℝ ∞ (fun p : Y × X ↦ f j l p.1 p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.2 ∈ H j
    · have hpt := (hHU j hp).1
      have hpf := (hHU j hp).2
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, X)) (n := ∞) (L.chart_mem_atlas j)) hpt
      have hpair : ContMDiffAt 𝓘(ℝ, Y × X) ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) ∞
          (fun z : Y × X ↦ (z.1, (L.chart j).symm z.2)) p :=
        contDiffAt_fst.contMDiffAt.prodMk (hchart.comp p contDiffAt_snd.contMDiffAt)
      have hsection : ContMDiffAt ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X))
          𝓘(ℝ, Fin (A.rank (L.frameIndex j)) → ℂ) ∞
          (fun z : Y × M ↦ (A.chart (L.frameIndex j) ⟨z.2, (u z.1 l).val z.2⟩).2)
          (p.1, (L.chart j).symm p.2) := (hu l (L.frameIndex j)).contMDiffAt
        ((isOpen_univ.prod (A.chart (L.frameIndex j)).open_baseSet).mem_nhds
          ⟨Set.mem_univ _, hpf⟩)
      let e := EuclideanSpace.equiv (Fin (A.rank (L.frameIndex j))) ℂ
      have hcoords := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp p
        (hsection.comp p hpair)
      have hcutoff := Complex.ofRealCLM.contMDiffAt.comp p
        ((L.smooth_cutoff j).contMDiffAt.comp p (hchart.comp p contDiffAt_snd.contMDiffAt))
      apply (hcutoff.contDiffAt.smul hcoords.contDiffAt).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt ((L.chart j).open_target.mem_nhds hpt)]
        with z hz
      change L.localizedFunction j (u z.1 l) z.2 = _
      have hz' : z.2 ∈ (L.chart j).target := hz
      simp [AtlasBundlePresentation.localizedFunction, atlasSectionInChart, hz', e]
    · apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ
        (Fin (A.rank (L.frameIndex j)))))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt ((hH j).isClosed.isOpen_compl.mem_nhds hp)]
        with z hz
      exact image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz ((L.localizedFunction_properties j (u z.1 l)).2.1 h))
  -- The same localized coordinates now have compact support in both variables.
  let ex := EuclideanSpace.equiv (Fin n) ℝ
  let Hp (j : Fin L.size) := ex '' H j
  have hHp (j : Fin L.size) : IsCompact (Hp j) := (hH j).image ex.continuous
  have hfc (j : Fin L.size) (l : Fin d) : ContDiff ℝ ∞
      (fun z : Y × Xp ↦ f j l z.1 (ex.symm z.2)) :=
    (hf j l).comp (contDiff_fst.prodMk (ex.symm.contDiff.comp contDiff_snd))
  have hsupport (j : Fin L.size) (l : Fin d) (i : Fin (A.rank (L.frameIndex j))) :
      tsupport (fun z : Y × Xp ↦ f j l z.1 (ex.symm z.2) i) ⊆ C ×ˢ Hp j := by
    apply closure_minimal ?_ (hC.isClosed.prod (hHp j).isClosed)
    intro z hz
    have hy : z.1 ∈ C := by
      by_contra h
      have hzero := hc z.1 h l
      have hloc : f j l z.1 = 0 := by
        change L.localizeLinearMap j (u z.1 l) = 0
        rw [hzero, map_zero]
      exact hz (by simp only [hloc, zero_apply, PiLp.zero_apply])
    have hx : ex.symm z.2 ∈ H j := by
      apply (L.localizedFunction_properties j (u z.1 l)).2.1
      apply subset_tsupport
      intro h
      apply hz
      exact congrArg (fun v ↦ v i) h
    exact ⟨hy, ex.apply_symm_apply z.2 ▸ ⟨ex.symm z.2, hx, rfl⟩⟩
  let test (j : Fin L.size) (l : Fin d) (i : Fin (A.rank (L.frameIndex j))) : 𝓢(Y × Xp, ℂ) :=
    HasCompactSupport.toSchwartzMap
      ((hC.prod (hHp j)).of_isClosed_subset (isClosed_tsupport _) (hsupport j l i))
      ((contDiff_piLp (𝕜 := ℝ) (p := 2)).mp (hfc j l) i)
  have hplateauPi {d : ℕ} (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
      ∃ φ : 𝓢(Fin d → ℝ, ℂ), HasCompactSupport φ ∧ ∀ x ∈ K, φ x = 1 := by
    let e := EuclideanSpace.equiv (Fin d) ℝ
    obtain ⟨ψ, hψ, hcψ, _, honeψ⟩ := exists_compact_cutoff_one_near
      (e.symm '' K) Set.univ (hK.image e.symm.continuous) isOpen_univ (Set.subset_univ _)
    have hcompact : HasCompactSupport (fun x ↦ (ψ (e.symm x) : ℂ)) :=
      (hcψ.comp_homeomorph e.symm.toHomeomorph).comp_left Complex.ofReal_zero
    let φ : 𝓢(Fin d → ℝ, ℂ) := HasCompactSupport.toSchwartzMap hcompact
      (Complex.ofRealCLM.contDiff.comp (hψ.comp e.symm.contDiff))
    refine ⟨φ, hcompact, ?_⟩
    intro x hx
    change (ψ (e.symm x) : ℂ) = 1
    rw [show ψ (e.symm x) = 1 from
      (show e.symm x ∈ {z | ψ z = 1} from interior_subset (honeψ ⟨x, hx, rfl⟩))]
    rfl
  -- Scalar Fubini is applied to each coordinate of the same compact matrix input.
  have hpair (j : Fin L.size) (l : Fin d) (i : Fin (A.rank (L.frameIndex j)))
      (T0 : 𝓢(Y, ℂ) →L[ℂ] ℂ) (R : 𝓢(Xp, ℂ) →L[ℂ] ℂ) :
      ∃ (a : 𝓢(Y, ℂ)) (b : 𝓢(Xp, ℂ)),
        (∀ y, a y = R (schwartzSliceCLM y (test j l i))) ∧
        (∀ x, b x = T0 (schwartzSliceCLM x
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (ContinuousLinearEquiv.prodComm ℝ Xp Y) (test j l i)))) ∧ T0 a = R b := by
    obtain ⟨φS, hφS, honeφ⟩ := hplateauPi C hC
    obtain ⟨ψS, hψS, honeψ⟩ := hplateauPi (Hp j) (hHp j)
    obtain ⟨aa, bb, haa, hbb, hab⟩ := exists_schwartzLocalizedPairings_commute
      φS hφS ψS hψS T0 R
    have hweight : (fun z : Y × Xp ↦ φS z.1 * ψS z.2).HasTemperateGrowth :=
      (φS.hasTemperateGrowth.comp (ContinuousLinearMap.fst ℝ Y Xp).hasTemperateGrowth).mul
        (ψS.hasTemperateGrowth.comp (ContinuousLinearMap.snd ℝ Y Xp).hasTemperateGrowth)
    have hsame : SchwartzMap.smulLeftCLM ℂ (fun z : Y × Xp ↦ φS z.1 * ψS z.2)
        (test j l i) = test j l i := by
      ext z
      rw [SchwartzMap.smulLeftCLM_apply_apply hweight]
      by_cases hz : z ∈ C ×ˢ Hp j
      · rw [honeφ z.1 hz.1, honeψ z.2 hz.2, one_mul, one_smul]
      · have hzero : test j l i z = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hz (hsupport j l i h))
        simp only [hzero, smul_zero]
    refine ⟨aa (test j l i), bb (test j l i), ?_, ?_, ?_⟩
    · intro y
      simpa only [hsame] using haa (test j l i) y
    · intro x
      simpa only [hsame] using hbb (test j l i) x
    · exact congrArg (fun f : 𝓢(Y × Xp, ℂ) →L[ℂ] ℂ ↦ f (test j l i)) hab
  -- Recover each actual output fiber through its dual, after exact finite reconstruction.
  apply Subtype.ext
  funext x
  let frame := B.frameLinearEquiv (B.covers x).choose x (B.covers x).choose_spec
  apply frame.injective
  funext coordinate
  let l : F x →ₗ[ℂ] ℂ := (LinearMap.proj coordinate).comp frame.toLinearMap
  change l ((P.toLinearMap s).val x) = l (t.val x)
  choose R hR using fun j : Fin L.size ↦
    P.exists_localActionFunctional L K (D j) (L.chart_mem_atlas j) x l
  let J (j : Fin L.size) (i : Fin (A.rank (L.frameIndex j))) :
      𝓢(Xp, ℂ) →L[ℂ] 𝓢(X, EuclideanSpace ℂ (Fin (A.rank (L.frameIndex j)))) :=
    (SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
      (EuclideanSpace.single i 1))).comp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ex)
  let I (l : Fin d) : 𝓢(Y, ℂ) →L[ℂ] 𝓢(Y, EuclideanSpace ℂ (Fin d)) :=
    SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight
      (EuclideanSpace.single l 1))
  have hI (v : Fin d → 𝓢(Y, ℂ)) (y : Y) (l : Fin d) :
      (∑ i, I i (v i)) y l = v l y := by
    simp [I, Pi.single_apply]
  choose a b ha hb hab using fun (j : Fin L.size) (l : Fin d)
    (i : Fin (A.rank (L.frameIndex j))) ↦
      hpair j l i (T.comp (I l)) ((R j).comp (J j i))
  have hlocal (j : Fin L.size) :
      L.localize j s = ∑ i, J j i (∑ l, b j l i) := by
    have hbvalue (z : Xp) (i : Fin (A.rank (L.frameIndex j))) :
        (∑ l, b j l i) z = L.localize j s (ex.symm z) i := by
      have hbT : (∑ l, b j l i) z = T (∑ l, I l (schwartzSliceCLM z
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (ContinuousLinearEquiv.prodComm ℝ Xp Y) (test j l i)))) := by
        simp only [sum_apply, hb, ContinuousLinearMap.comp_apply, map_sum]
      rw [hbT]
      by_cases hz : ex.symm z ∈ H j
      · have hzt := (hHU j hz).1
        have hzf := (hHU j hz).2
        let y := (L.chart j).symm (ex.symm z)
        let e := A.frameLinearEquiv (L.frameIndex j) y hzf
        let q : E y →ₗ[ℂ] ℂ := (L.cutoff j y : ℂ) •
          ((LinearMap.proj i).comp e.toLinearMap)
        have hcoord (w : A.smoothSections) : L.localize j w (ex.symm z) i = q (w.val y) := by
          change L.localizedFunction j w (ex.symm z) i = _
          simp only [AtlasBundlePresentation.localizedFunction, ite_eq_left hzt,
            atlasSectionInChart]
          rfl
        obtain ⟨g, hg, hsg⟩ := hs y q
        rw [hcoord, hsg]
        congr 1
        ext v l
        rw [hI]
        change f j l v (ex.symm z) i = g v l
        rw [hg]
        exact hcoord (u v l)
      · have hzero (w : A.smoothSections) : L.localize j w (ex.symm z) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun h ↦ hz ((L.localizedFunction_properties j w).2.1 h))
        have hslice (l : Fin d) : schwartzSliceCLM z
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (ContinuousLinearEquiv.prodComm ℝ Xp Y) (test j l i)) = 0 := by
          ext v
          change f j l v (ex.symm z) i = 0
          rw [show f j l v = L.localize j (u v l) from rfl, hzero]
          rfl
        simp only [hslice, map_zero, Finset.sum_const_zero, hzero]
        rfl
    apply SchwartzMap.ext
    intro z
    calc
      L.localize j s z = ∑ i, (L.localize j s z i) • EuclideanSpace.single i 1 := by
        symm
        simpa only [OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply] using
          (EuclideanSpace.basisFun (Fin (A.rank (L.frameIndex j))) ℂ).toBasis.sum_repr
            (L.localize j s z)
      _ = ∑ i, (∑ l, b j l i) (ex z) • EuclideanSpace.single i 1 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hbvalue, ex.symm_apply_apply]
      _ = (∑ i, J j i (∑ l, b j l i)) z := by
        simp only [sum_apply, J, ContinuousLinearMap.comp_apply,
          SchwartzMap.postcompCLM_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
          Function.comp_apply]
  -- The same finite reconstruction evaluates the entire original P, including its remainder.
  have hsum (w : A.smoothSections) :
      l ((P.toLinearMap w).val x) = ∑ j, R j (L.localize j w) := by
    have h := congrArg (fun w : A.smoothSections ↦ l ((P.toLinearMap w).val x))
      (hreconstruct w).symm
    simpa only [map_sum, Submodule.coe_sum, Finset.sum_apply, hR] using h
  obtain ⟨g, hg, htg⟩ := ht x l
  rw [hsum, htg]
  have hterm (j : Fin L.size) : R j (L.localize j s) = T (∑ l, I l (∑ i, a j l i)) := by
    rw [hlocal, map_sum]
    simp only [map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro i _
    exact (hab j l i).symm
  simp only [hterm]
  rw [← map_sum]
  congr 1
  apply SchwartzMap.ext
  intro y
  apply PiLp.ext
  intro coordinate
  change (∑ j, ∑ l, I l (∑ i, a j l i)) y coordinate = g y coordinate
  rw [hg]
  have hleft : (∑ j, ∑ l, I l (∑ i, a j l i)) y coordinate =
      ∑ j, ∑ i, a j coordinate i y := by
    have heval (v : Fin L.size → EuclideanSpace ℂ (Fin d)) :
        (∑ j, v j) coordinate = ∑ j, v j coordinate :=
      map_sum ((LinearMap.proj coordinate).comp
        (EuclideanSpace.equiv (Fin d) ℂ).toLinearMap) v Finset.univ
    rw [sum_apply, heval]
    apply Finset.sum_congr rfl
    intro j _
    rw [hI]
    exact sum_apply _ _ _
  rw [hleft]
  simp only [ha, ContinuousLinearMap.comp_apply]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← map_sum]
  congr 1
  apply SchwartzMap.ext
  intro z
  have hin (i : Fin (A.rank (L.frameIndex j))) :
      J j i (schwartzSliceCLM y (test j coordinate i)) z =
        f j coordinate y z i • EuclideanSpace.single i 1 := by
    change test j coordinate i (y, ex z) • EuclideanSpace.single i 1 = _
    change f j coordinate y (ex.symm (ex z)) i • EuclideanSpace.single i 1 = _
    rw [ex.symm_apply_apply]
  change (∑ i : Fin (A.rank (L.frameIndex j)),
    J j i (schwartzSliceCLM y (test j coordinate i))) z = f j coordinate y z
  simp only [sum_apply, hin]
  simpa only [OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] using
    (EuclideanSpace.basisFun (Fin (A.rank (L.frameIndex j))) ℂ).toBasis.sum_repr
      (f j coordinate y z)

end AtiyahSinger
