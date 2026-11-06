/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorH1Coordinates
public import AtiyahSinger.Analysis.SobolevLocalization
public import AtiyahSinger.Geometry.ExternalTensorChartCutoff

/-!
# Pure smooth tensor sections are dense in geometric H1

Public module ID: M0611.

Bounded extension from the original Euclidean H1 graph transports separated
coordinate approximation through actual product cutoff frames. A product
partition of unity reconstructs every smooth section, and the original smooth
inclusion is dense in each specified Sobolev presentation.

The proof uses the native tensor bundle, the fixed Euclidean concatenation,
and the exact factor extension formulas. It does not assert that a factorwise
pseudodifferential operator is an isotropic product pseudodifferential operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct SchwartzMap

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {n m r s : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := m) (r := s) F]

variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
  [CompactSpace M] [CompactSpace N]

/-- The original pure smooth tensor sections span densely in every geometric H1 presentation. -/
theorem dense_span_externalTensorH1 :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    ∀ L : SmoothBundlePresentation (n := n + m) (r := r * s) (externalTensorFiber E F),
      Dense (Submodule.span ℂ (Set.range fun p :
        smoothSections (n := n) (r := r) E × smoothSections (n := m) (r := s) F ↦
        L.smoothToSobolev 1 (externalTensorSection E F p.1 p.2)) :
          Set (L.SobolevSpace 1)) := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  intro L
  let S := Submodule.span ℂ (Set.range fun p :
    smoothSections (n := n) (r := r) E × smoothSections (n := m) (r := s) F ↦
    L.smoothToSobolev 1 (externalTensorSection E F p.1 p.2))
  let C := S.topologicalClosure
  -- Bounded product cutoff extensions carry local H1 density into the original geometric space.
  have hlocal {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
      {d : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m))}
      (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := s) F d)
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (hd : d ∈ atlas (EuclideanSpace ℝ (Fin m)) N)
      (hp : ((c.prod d).trans (EuclideanSpace.finAddEquivProd
        (𝕜 := ℝ) (n := n) (m := m)).symm.toHomeomorph.toOpenPartialHomeomorph) ∈
          atlas (EuclideanSpace ℝ (Fin (n + m))) (M × N))
      (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s)))) :
      L.smoothToSobolev 1 ((externalTensorChartCutoff A B).extend hp w) ∈ C := by
    let X := EuclideanSpace ℝ (Fin n)
    let Y := EuclideanSpace ℝ (Fin m)
    let Z := EuclideanSpace ℝ (Fin (n + m))
    let V := EuclideanSpace ℂ (Fin (r * s))
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let G := externalTensorChartCutoff A B
    let F₀ : 𝓢(Z, V) →ₗ[ℂ] L.SobolevSpace 1 :=
      (L.smoothToSobolev 1).comp (G.extendLinearMap hp)
    have hbound : ∃ C : ℝ, ∀ u : 𝓢(Z, V),
        ‖F₀ u‖ ≤ C * ‖schwartzToH1Graph (n + m) (r * s) u‖ := by
      obtain ⟨C, _, hC⟩ := G.exists_norm_extend_sobolev_le hp L 1
      refine ⟨C, fun u ↦ ?_⟩
      change ‖L.smoothToSobolev 1 (G.extend hp u)‖ ≤
        C * ‖schwartzH1Jet (n + m) (r * s) u‖
      rw [norm_schwartzH1Jet]
      exact hC u
    let T := F₀.extendOfNorm (schwartzToH1Graph (n + m) (r * s))
    have hT (u : 𝓢(Z, V)) : T (schwartzToH1Graph (n + m) (r * s) u) = F₀ u :=
      F₀.extendOfNorm_eq (denseRange_schwartzToH1Graph (n + m) (r * s)) hbound u
    have hseparated (g : 𝓢(Z, V)) (a : 𝓢(X, ℂ)) (b : 𝓢(Y, ℂ)) (v : V)
        (hg : ∀ z : Z, g z = (a (e z).1 * b (e z).2) • v) : F₀ g ∈ C := by
      by_cases hv : v = 0
      · have hg0 : g = 0 := by ext z; simp [hg, hv]
        simpa only [hg0, map_zero] using C.zero_mem
      obtain ⟨l, hl⟩ : ∃ l : Fin (r * s), v l ≠ 0 := by
        by_contra! hall
        apply hv
        apply PiLp.ext
        intro l
        exact hall l
      let scalar : 𝓢(Z, ℂ) := (v l)⁻¹ •
        SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) l) g
      have hscalar (z : Z) : scalar z = a (e z).1 * b (e z).2 := by
        change (v l)⁻¹ * ((EuclideanSpace.proj (𝕜 := ℂ) l) (g z)) = _
        rw [hg z]
        change (v l)⁻¹ * ((a (e z).1 * b (e z).2) * v l) = _
        field_simp
      let part (k : Fin (r * s)) : 𝓢(Z, V) :=
        SchwartzMap.postcompCLM
          ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single k 1)) scalar
      have hpart (k : Fin (r * s)) (z : Z) : part k z = scalar z • EuclideanSpace.single k 1 := rfl
      have hsum : g = ∑ k : Fin (r * s), v k • part k := by
        apply SchwartzMap.ext
        intro z
        simp only [sum_apply, smul_apply, hpart, hscalar, hg z]
        have hbasis : ∑ k : Fin (r * s), v k • EuclideanSpace.single k 1 = v := by
          simpa only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
            (EuclideanSpace.basisFun (Fin (r * s)) ℂ).sum_repr v
        conv_lhs => rw [← hbasis]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro k _
        exact smul_comm _ _ _
      have hparts (k : Fin (r * s)) : F₀ (part k) ∈ S := by
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        let φ : 𝓢(X, EuclideanSpace ℂ (Fin r)) :=
          SchwartzMap.postcompCLM
            ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i 1)) a
        let ψ : 𝓢(Y, EuclideanSpace ℂ (Fin s)) :=
          SchwartzMap.postcompCLM
            ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single j 1)) b
        have hφ (z : X) : φ z = a z • EuclideanSpace.single i 1 := rfl
        have hψ (z : Y) : ψ z = b z • EuclideanSpace.single j 1 := rfl
        have hcoord (z : X × Y) (i' : Fin r) (j' : Fin s) :
            part (finProdFinEquiv (i, j)) (e.symm z) (finProdFinEquiv (i', j')) =
              φ z.1 i' * ψ z.2 j' := by
          rw [hpart, hscalar, e.apply_symm_apply, hφ, hψ]
          change (a z.1 * b z.2) *
            (EuclideanSpace.single (finProdFinEquiv (i, j)) (1 : ℂ))
              (finProdFinEquiv (i', j')) =
            (a z.1 * (EuclideanSpace.single i (1 : ℂ)) i') *
              (b z.2 * (EuclideanSpace.single j (1 : ℂ)) j')
          simp only [PiLp.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
          by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]
        have hsection : G.extend hp (part (finProdFinEquiv (i, j))) =
            externalTensorSection E F (A.extend hc φ) (B.extend hd ψ) := by
          apply Subtype.ext
          funext z
          exact externalTensorChartCutoff_extendedFunction A B φ ψ
            (part (finProdFinEquiv (i, j))) hcoord z.1 z.2
        change L.smoothToSobolev 1 (G.extend hp (part (finProdFinEquiv (i, j)))) ∈ S
        rw [hsection]
        exact Submodule.subset_span ⟨(_, _), rfl⟩
      rw [hsum, map_sum]
      exact C.sum_mem (fun k _ ↦ by
        rw [map_smul]
        exact C.smul_mem (v k) (S.le_topologicalClosure (hparts k)))
    let D := Submodule.span ℂ ((schwartzToH1Graph (n + m) (r * s)) ''
      {u : 𝓢(Z, V) | ∃ a : 𝓢(X, ℂ), ∃ b : 𝓢(Y, ℂ), ∃ v : V,
        ∀ z : Z, u z = (a (e z).1 * b (e z).2) • v})
    have hD : Dense (D : Set (EuclideanH1Graph (n + m) (r * s))) :=
      dense_span_schwartz_products_h1Graph n m (r * s)
    have hall (z : EuclideanH1Graph (n + m) (r * s)) : T z ∈ C := by
      refine hD.induction (P := fun z ↦ T z ∈ C) ?_
        (S.isClosed_topologicalClosure.preimage T.continuous) z
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨g, ⟨a, b, v, hg⟩, rfl⟩ := hz
        rw [hT]
        exact hseparated g a b v hg
      | zero => simpa only [map_zero] using C.zero_mem
      | add z w hz hw hzi hwi => simpa only [map_add] using C.add_mem hzi hwi
      | smul a z hz hzi => simpa only [map_smul] using C.smul_mem a hzi
    have hresult := hall (schwartzToH1Graph (n + m) (r * s) w)
    rwa [hT] at hresult
  -- Select plateaus inside the original factor chart/frame domains.
  let P := Classical.choice (nonempty_smoothBundlePresentation (n := n) (r := r) E)
  let Q := Classical.choice (nonempty_smoothBundlePresentation (n := m) (r := s) F)
  let R := externalTensorPresentation P Q
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  have plateau {d : ℕ} (K U : Set (EuclideanSpace ℝ (Fin d)))
      (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∃ η : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        tsupport η ⊆ U ∧ ∀ z ∈ K, η z = 1 := by
    obtain ⟨O, hO, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨η, hη, _, hsη, honeη⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO hK.isClosed hKO
    have hs : tsupport η = closure O := congrArg closure hsη
    refine ⟨η, hη, by simpa [HasCompactSupport, hs] using hOc, by rwa [hs], ?_⟩
    exact fun z hz ↦ (honeη z).mp hz
  have pP (i : Fin P.size) : ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        tsupport η ⊆ (P.chart i).target ∩ (P.chart i).symm ⁻¹' (P.frame i).baseSet ∧
          ∀ x ∈ tsupport (P.cutoff i), η ((P.chart i) x) = 1 := by
    let K := (P.chart i) '' tsupport (P.cutoff i)
    let U := (P.chart i).target ∩ (P.chart i).symm ⁻¹' (P.frame i).baseSet
    have hK : IsCompact K := (P.compact_support i).image_of_continuousOn
      ((P.chart i).continuousOn.mono (fun _ hx ↦ (P.support_subset i hx).1))
    have hU : IsOpen U := (P.chart i).continuousOn_symm.isOpen_inter_preimage
      (P.chart i).open_target (P.frame i).open_baseSet
    have hKU : K ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hs := (P.support_subset i hx).1
      refine ⟨(P.chart i).map_source hs, ?_⟩
      change (P.chart i).symm ((P.chart i) x) ∈ (P.frame i).baseSet
      rw [(P.chart i).left_inv hs]
      exact (P.support_subset i hx).2
    obtain ⟨η, hη, hcη, hsη, honeη⟩ := plateau K U hK hU hKU
    exact ⟨η, hη, hcη, hsη, fun x hx ↦ honeη _ ⟨x, hx, rfl⟩⟩
  have pQ (j : Fin Q.size) : ∃ η : EuclideanSpace ℝ (Fin m) → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
        tsupport η ⊆ (Q.chart j).target ∩ (Q.chart j).symm ⁻¹' (Q.frame j).baseSet ∧
          ∀ y ∈ tsupport (Q.cutoff j), η ((Q.chart j) y) = 1 := by
    let K := (Q.chart j) '' tsupport (Q.cutoff j)
    let U := (Q.chart j).target ∩ (Q.chart j).symm ⁻¹' (Q.frame j).baseSet
    have hK : IsCompact K := (Q.compact_support j).image_of_continuousOn
      ((Q.chart j).continuousOn.mono (fun _ hx ↦ (Q.support_subset j hx).1))
    have hU : IsOpen U := (Q.chart j).continuousOn_symm.isOpen_inter_preimage
      (Q.chart j).open_target (Q.frame j).open_baseSet
    have hKU : K ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      have hs := (Q.support_subset j hx).1
      refine ⟨(Q.chart j).map_source hs, ?_⟩
      change (Q.chart j).symm ((Q.chart j) x) ∈ (Q.frame j).baseSet
      rw [(Q.chart j).left_inv hs]
      exact (Q.support_subset j hx).2
    obtain ⟨η, hη, hcη, hsη, honeη⟩ := plateau K U hK hU hKU
    exact ⟨η, hη, hcη, hsη, fun x hx ↦ honeη _ ⟨x, hx, rfl⟩⟩
  choose ηP hηP hcηP hsηP honeP using pP
  choose ηQ hηQ hcηQ hsηQ honeQ using pQ
  let GP (i : Fin P.size) : BundleChartCutoff (r := r) E (P.chart i) := {
    frame := P.frame i
    frame_mem_atlas := P.frame_mem_atlas i
    cutoff := ηP i
    smooth_cutoff := hηP i
    compact_support := hcηP i
    support_subset := hsηP i }
  let GQ (j : Fin Q.size) : BundleChartCutoff (r := s) F (Q.chart j) := {
    frame := Q.frame j
    frame_mem_atlas := Q.frame_mem_atlas j
    cutoff := ηQ j
    smooth_cutoff := hηQ j
    compact_support := hcηQ j
    support_subset := hsηQ j }
  let cprod (i : Fin P.size) (j : Fin Q.size) :=
    ((P.chart i).prod (Q.chart j)).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
  have cprod_mem (i : Fin P.size) (j : Fin Q.size) :
      cprod i j ∈ atlas (EuclideanSpace ℝ (Fin (n + m))) (M × N) := by
    refine ⟨(P.chart i).prod (Q.chart j), ?_,
      e.symm.toHomeomorph.toOpenPartialHomeomorph, Set.mem_singleton _, rfl⟩
    exact ⟨P.chart i, P.chart_mem_atlas i, Q.chart j, Q.chart_mem_atlas j, rfl⟩
  let G (i : Fin P.size) (j : Fin Q.size) := externalTensorChartCutoff (GP i) (GQ j)
  -- Each plateau extension exactly undoes its corresponding original product localization.
  have hterm (i : Fin P.size) (j : Fin Q.size)
      (w : smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F)) (z : M × N) :
      ((G i j).extend (cprod_mem i j) (R.localize (finProdFinEquiv (i, j)) w)).val z =
        ((P.cutoff i z.1 * Q.cutoff j z.2 : ℝ) : ℂ) • w.val z := by
    let k : Fin R.size := finProdFinEquiv (i, j)
    let := (G i j).frame_mem_atlas
    let := R.frame_mem_atlas k
    have hchart : R.chart k = cprod i j := by
      simp only [R, k, externalTensorPresentation, Equiv.symm_apply_apply]
      rfl
    have hcut (x : M × N) : R.cutoff k x = P.cutoff i x.1 * Q.cutoff j x.2 := by
      simp only [R, k, externalTensorPresentation, Equiv.symm_apply_apply]
    have hsymmL : (G i j).frame.symmL ℂ z = (R.frame k).symmL ℂ z := by
      simp only [G, GP, GQ, R, k, externalTensorChartCutoff,
        externalTensorPresentation, Equiv.symm_apply_apply]
    have hcutG : (G i j).cutoff (cprod i j z) =
        ηP i ((P.chart i) z.1) * ηQ j ((Q.chart j) z.2) := by
      change ηP i (e (e.symm ((P.chart i z.1), (Q.chart j z.2)))).1 *
        ηQ j (e (e.symm ((P.chart i z.1), (Q.chart j z.2)))).2 = _
      rw [e.apply_symm_apply]
    change (G i j).extendedFunction (R.localize k w) z = _
    have hext : (G i j).extendedFunction (R.localize k w) z =
        if z ∈ (cprod i j).source then
          ((G i j).cutoff (cprod i j z) : ℂ) • (G i j).frame.symmL ℂ z
            (R.localize k w (cprod i j z)) else 0 := rfl
    rw [hext, ← hcut z]
    by_cases hz : z ∈ (cprod i j).source
    · rw [ite_eq_left hz]
      have hloc : R.localize k w (cprod i j z) =
          (R.cutoff k z : ℂ) • (R.frame k ⟨z, w.val z⟩).2 := by
        change R.localizedFunction k w (cprod i j z) = _
        simp only [SmoothBundlePresentation.localizedFunction, hchart]
        rw [ite_eq_left ((cprod i j).map_source hz)]
        simp only [sectionInChart, (cprod i j).left_inv hz]
        exact congrArg (fun y : M × N ↦
          (R.cutoff k z : ℂ) • (R.frame k ⟨y, w.val y⟩).2) ((cprod i j).left_inv hz)
      rw [hloc]
      by_cases hzero : R.cutoff k z = 0
      · simp [hzero]
      have hsupport := subset_tsupport (R.cutoff k) hzero
      have hf := (R.support_subset k hsupport).2
      have hfactor : P.cutoff i z.1 ≠ 0 ∧ Q.cutoff j z.2 ≠ 0 := by
        rw [hcut] at hzero
        exact mul_ne_zero_iff.mp hzero
      rw [hcutG, honeP i z.1 (subset_tsupport _ hfactor.1),
        honeQ j z.2 (subset_tsupport _ hfactor.2), one_mul, Complex.ofReal_one,
        one_smul, map_smul, hsymmL]
      rw [← (R.frame k).continuousLinearMapAt_apply_of_mem ℂ hf,
        (R.frame k).symmL_continuousLinearMapAt hf]
    · have hzero : R.cutoff k z = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦
        hz (by simpa only [hchart] using (R.support_subset k hs).1))
      simp [hz, hzero]
  have hpartition (w : smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F)) :
      (∑ i : Fin P.size, ∑ j : Fin Q.size,
        (G i j).extend (cprod_mem i j) (R.localize (finProdFinEquiv (i, j)) w)) = w := by
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sum, Finset.sum_apply]
    simp_rw [hterm, ← Finset.sum_smul, ← Complex.ofReal_sum]
    have hsum : (∑ i : Fin P.size, ∑ j : Fin Q.size, P.cutoff i z.1 * Q.cutoff j z.2) = 1 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, P.sum_cutoff, Q.sum_cutoff, one_mul]
    rw [hsum, Complex.ofReal_one, one_smul]
  have hsmooth (w : smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F)) :
      L.smoothToSobolev 1 w ∈ C := by
    rw [← hpartition w, map_sum]
    apply C.sum_mem
    intro i _
    rw [map_sum]
    apply C.sum_mem
    intro j _
    exact hlocal (GP i) (GQ j) (P.chart_mem_atlas i) (Q.chart_mem_atlas j)
      (cprod_mem i j) (R.localize (finProdFinEquiv (i, j)) w)
  -- Smooth sections are dense in this exact presentation's completion.
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro u _
  refine (L.denseRange_smoothToSobolev 1).induction ?_ S.isClosed_topologicalClosure u
  rintro _ ⟨w, rfl⟩
  exact hsmooth w

end AtiyahSinger
