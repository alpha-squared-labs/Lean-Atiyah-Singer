/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.HermitianMetricDifferentialAdjoint
public import AtiyahSinger.Analysis.PrincipalSymbolAdjoint

/-!
# Real-order PDO adjoints for explicit metrics

Public module ID: M0727.

D02/D05/A02/A07: globalize SG III.3.11 with smooth Gram and density weights,
then retain the principal class from (3.17)–(3.19). The integral relation and
bilinear transpose determine the same actual map. The formulas below are
project bridges; they do not assert fiber adjunction of a complete symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate SchwartzMap Matrix.Norms.Elementwise

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

set_option maxHeartbeats 800000 in
-- Normalize metric duality in the original kernel and its integral pairing identity.
/-- A specified metric adjoint of a smooth-kernel map is again a smooth-kernel map.
This map-level result also applies to the two actual parametrix residuals. -/
theorem IsMetricFormalAdjoint.isSmoothingOperator
    {P : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F}
    {Q : smoothSections (n := n) (r := q) F →ₗ[ℂ] smoothSections (n := n) (r := r) E}
    (hPQ : IsMetricFormalAdjoint h k μ P Q) (hP : IsSmoothingOperator μ P) :
    IsSmoothingOperator μ Q := by
  -- Construct the swapped kernel in the original norms, using the two supplied metric dualities.
  have hkernel (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
      ∃ J : SmoothKernel (n := n) (r := q) (q := r) F E,
        (∀ (x y : M) (u : E x) (v : F y),
          k.pairing y (K.toFun y x u) v = h.pairing x u (J.toFun x y v)) ∧
        ∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := n) (r := q) F),
          k.sectionPairing μ (K.toLinearMap μ u) v =
            h.sectionPairing μ u (J.toLinearMap μ v) := by
    classical
    let (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let (x : M) : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let (x : M) : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
    -- Compose metric duality with dual precomposition, using the original fiber norms.
    let A₀ (x y : M) : F y →ₗ[ℂ] E x := {
      toFun := fun v ↦ (h.dualEquiv x).symm ((k.dual y v).comp (K.toFun y x))
      map_add' := by
        intro v w
        rw [k.dual_add, ContinuousLinearMap.add_comp, map_add]
      map_smul' := by
        intro c v
        rw [k.dual_smul, ContinuousLinearMap.smul_comp, map_smulₛₗ]
        simp }
    let A (x y : M) : F y →L[ℂ] E x := (A₀ x y).toContinuousLinearMap
    have hpair (x y : M) (u : E x) (v : F y) :
        h.pairing x u (A x y v) = k.pairing y (K.toFun y x u) v := by
      have hs : h.pairing x (A x y v) u = k.pairing y v (K.toFun y x u) :=
        (h.pairing_dualEquiv_symm x ((k.dual y v).comp (K.toFun y x)) u).trans
          (k.dual_apply y v (K.toFun y x u))
      have hc := congrArg (starRingEnd ℂ) hs
      simpa only [SmoothHermitianMetric.pairing, (h.toCore x).conj_inner_symm,
        (k.toCore y).conj_inner_symm] using hc
    have hA : IsSmoothKernel (n := n) (r := q) (q := r) F E A := by
      intro f e hf he
      let toOpE : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ]
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
      let matrixOpE : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        LinearMap.toContinuousLinearMap (toOpE.restrictScalars ℝ)
      let GE (x : M) := matrixOpE (h.gramMatrix e x)
      have gramSmoothE : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          GE e.baseSet := by
        apply matrixOpE.contDiff.contMDiff.comp_contMDiffOn
        apply contMDiffOn_pi_space.mpr
        intro i
        apply contMDiffOn_pi_space.mpr
        intro j
        exact h.contMDiffOn_gram e i j
      have gramInvertibleE (x : M) (hx : x ∈ e.baseSet) : (GE x).IsInvertible := by
        have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
          (h.isUnit_det_gramMatrix e x hx)
        let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
          ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
            Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
        let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
        refine ⟨Q.trans (L.trans Q.symm), ?_⟩
        ext v i
        rfl
      have gramPairingE (x : M) (hx : x ∈ e.baseSet)
          (u v : EuclideanSpace ℂ (Fin r)) :
          inner ℂ u (GE x v) = h.pairing x (e.symmL ℂ x u) (e.symmL ℂ x v) := by
        rw [h.pairing_eq_gramMatrix e x hx]
        have hcoord (w : EuclideanSpace ℂ (Fin r)) :
            (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact e.continuousLinearMapAt_symmL hx w
        rw [hcoord, hcoord]
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        change (∑ i, (∑ j, h.gramMatrix e x i j * v j) * star (u i)) = _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [starRingEnd_apply]
        ring
      let toOpF : Matrix (Fin q) (Fin q) ℂ →ₗ[ℂ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
        LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
      let matrixOpF : Matrix (Fin q) (Fin q) ℂ →L[ℝ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
        LinearMap.toContinuousLinearMap (toOpF.restrictScalars ℝ)
      let GF (x : M) := matrixOpF (k.gramMatrix f x)
      have gramSmoothF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          GF f.baseSet := by
        apply matrixOpF.contDiff.contMDiff.comp_contMDiffOn
        apply contMDiffOn_pi_space.mpr
        intro i
        apply contMDiffOn_pi_space.mpr
        intro j
        exact k.contMDiffOn_gram f i j
      have gramPairingF (x : M) (hx : x ∈ f.baseSet)
          (u v : EuclideanSpace ℂ (Fin q)) :
          inner ℂ u (GF x v) = k.pairing x (f.symmL ℂ x u) (f.symmL ℂ x v) := by
        rw [k.pairing_eq_gramMatrix f x hx]
        have hcoord (w : EuclideanSpace ℂ (Fin q)) :
            (f ⟨x, f.symmL ℂ x w⟩).2 = w := by
          rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact f.continuousLinearMapAt_symmL hx w
        rw [hcoord, hcoord]
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        change (∑ i, (∑ j, k.gramMatrix f x i j * v j) * star (u i)) = _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [starRingEnd_apply]
        ring
      have hGEi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          (fun x ↦ (GE x).inverse) e.baseSet := by
        intro x hx
        exact ((gramInvertibleE x hx).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ
          |>.comp_contMDiffWithinAt (gramSmoothE x hx)
      let adj : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        { toFun := fun c ↦ c.adjoint
          map_add' := fun c d ↦ map_add _ c d
          map_smul' := by
            intro a c
            simp only [RingHom.id_apply, ← Complex.coe_smul, map_smulₛₗ,
              Complex.conj_ofReal]
          cont := ContinuousLinearMap.adjoint.continuous }
      -- The inverse source Gram is at x; the original target Gram is at y.
      have hleft := hGEi.comp (contMDiffOn_fst (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.1)
      have hright := gramSmoothF.comp (contMDiffOn_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.2)
      have hswap := (K.isSmooth e f).comp (contMDiffOn_snd.prodMk contMDiffOn_fst)
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ ⟨hz.2, hz.1⟩)
      have hmiddle := adj.contMDiff.comp_contMDiffOn hswap
      have hcompose {a b c : ℕ} : ContDiff ℝ ∞ (fun z :
          (EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)) ×
            (EuclideanSpace ℂ (Fin a) →L[ℂ] EuclideanSpace ℂ (Fin b)) ↦ z.1.comp z.2) :=
        (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
      have hweighted := hcompose.contMDiff.comp_contMDiffOn
        (hleft.prodMk_space (hcompose.contMDiff.comp_contMDiffOn
          (hmiddle.prodMk_space hright)))
      apply hweighted.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro v
      have heq : GE z.1 (kernelInFrames F E A f e z v) =
          (kernelInFrames E F K.toFun e f (z.2, z.1)).adjoint (GF z.2 v) := by
        apply ext_inner_left ℂ
        intro u
        rw [ContinuousLinearMap.adjoint_inner_right, gramPairingE _ hz.1,
          gramPairingF _ hz.2]
        change h.pairing z.1 (e.symmL ℂ z.1 u)
          (e.symmL ℂ z.1 (e.continuousLinearMapAt ℂ z.1
            (A z.1 z.2 (f.symmL ℂ z.2 v)))) =
          k.pairing z.2 (f.symmL ℂ z.2 (f.continuousLinearMapAt ℂ z.2
            (K.toFun z.2 z.1 (e.symmL ℂ z.1 u)))) (f.symmL ℂ z.2 v)
        rw [e.symmL_continuousLinearMapAt hz.1, hpair,
          f.symmL_continuousLinearMapAt hz.2]
      exact ((gramInvertibleE z.1 hz.1).inverse_apply_self _).symm.trans
        (congrArg (GE z.1).inverse heq)
    let J : SmoothKernel (n := n) (r := q) (q := r) F E := ⟨A, hA⟩
    refine ⟨J, ?_, ?_⟩
    · intro x y u v
      exact (hpair x y u v).symm
    · intro u v
      -- The proven bilinear transpose formula supplies Fubini for the actual kernels.
      let α := dualSectionsEquiv F (k.dualSectionsEquiv v)
      have hrow (x : M) :
          h.pairing x (u.val x) ((J.toLinearMap μ v).val x) =
            conj ((K.transpose.toLinearMap μ α).val x (u.val x)) := by
        have hJ := J.dual_apply μ v x (h.dual x (u.val x))
        have hT := K.transpose.dual_apply μ α x (ContinuousLinearMap.apply ℂ ℂ (u.val x))
        change h.dual x (u.val x) ((J.toLinearMap μ v).val x) =
          ∫ y, h.dual x (u.val x) (A x y (v.val y)) ∂μ at hJ
        simp only [h.dual_apply] at hJ
        change (K.transpose.toLinearMap μ α).val x (u.val x) =
          ∫ y, α.val y (K.toFun y x (u.val x)) ∂μ at hT
        rw [hJ, hT, ← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        change h.pairing x (u.val x) (A x y (v.val y)) =
          conj ((k.dualSectionsEquiv v).val y (K.toFun y x (u.val x)))
        rw [hpair, k.dualSectionsEquiv_apply]
        exact ((k.toCore y).conj_inner_symm _ _).symm
      have ht := K.isFormalTranspose_toLinearMap (μ := μ) α u
      change (∫ x, (K.transpose.toLinearMap μ α).val x (u.val x) ∂μ) =
        ∫ x, (k.dualSectionsEquiv v).val x ((K.toLinearMap μ u).val x) ∂μ at ht
      simp only [k.dualSectionsEquiv_apply] at ht
      change (∫ x, k.pairing x ((K.toLinearMap μ u).val x) (v.val x) ∂μ) =
        ∫ x, h.pairing x (u.val x) ((J.toLinearMap μ v).val x) ∂μ
      simp_rw [hrow]
      rw [integral_conj, ht, ← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((k.toCore x).conj_inner_symm _ _).symm
  obtain ⟨K, rfl⟩ := hP
  obtain ⟨J, _, hJ⟩ := hkernel K
  -- Uniqueness identifies the specified section map with this actual kernel integral.
  exact ⟨J, (hPQ.unique hJ).symm⟩

set_option maxHeartbeats 3000000 in
-- Normalize local Gram weights, density conjugation and the smoothing residual.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- A single local adjoint representation retains its map and its Hermitian principal class. -/
private theorem PseudodifferentialPiece.exists_representation_metricFormalAdjoint {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (T : smoothSections (n := n) (r := q) F →ₗ[ℂ]
      smoothSections (n := n) (r := r) E)
    (hT : ∀ u v, k.sectionPairing μ (L.toLinearMap u) v =
      h.sectionPairing μ u (T v)) :
    ∃ (N : ℕ) (L' : Fin N → PseudodifferentialPiece (n := n) (r := q) (q := r) F E m),
      IsSmoothingOperator μ (T - ∑ j, (L' j).toLinearMap) ∧
        globalPrincipalSymbolClass F E m (∑ j, (L' j).globalSymbol) =
          h.principalSymbolAdjoint k (globalPrincipalSymbolClass E F m L.globalSymbol) := by
  classical
  let TModel := EuclideanSpace ℝ (Fin n)
  let SourceModel := EuclideanSpace ℂ (Fin r)
  let TargetModel := EuclideanSpace ℂ (Fin q)
  -- The specified metrics give smooth invertible Gram weights in the chosen frames.
  have hgramE (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization SourceModel (π SourceModel E)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (SourceModel →L[ℂ] SourceModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : SourceModel,
            h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (SourceModel →L[ℂ] SourceModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : SourceModel →L[ℂ] SourceModel := toOp (h.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((h.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : SourceModel) :
        h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : SourceModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [h.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * h.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, h.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (h.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  have hgramF (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization TargetModel (π TargetModel F)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (TargetModel →L[ℂ] TargetModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : TargetModel,
            k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin q) (Fin q) ℂ →L[ℝ] (TargetModel →L[ℂ] TargetModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : TargetModel →L[ℂ] TargetModel := toOp (k.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((k.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : TargetModel) :
        k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : TargetModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [k.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * k.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, k.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (k.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  have hchartIntegral (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (μ : Measure M)
      (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
      (hpos : ∀ z ∈ c.target, 0 ≤ w z)
      (hmap : Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
      (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
      (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
    classical
    -- Extend the target test by zero outside the prescribed chart target.
    let g : EuclideanSpace ℝ (Fin n) → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
    have hg : Measurable g :=
      (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
        continuousOn_const c.open_target.measurableSet
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
        |>.aemeasurable c.open_target.measurableSet
    calc
      (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
        simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
          hg.aestronglyMeasurable).symm
      _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
        rw [hmap]
        exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
      _ = ∫ z in c.target, w z • f (c.symm z) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]
  -- A reversed piece uses the same chart and frames, with the prescribed density weights.
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
  let c := L.chart
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  -- A common plateau lies strictly inside the original chart and both original frames.
  let K := tsupport L.input.cutoff ∪ tsupport L.output.cutoff
  let U := c.target ∩ c.symm ⁻¹' (L.input.frame.baseSet ∩ L.output.frame.baseSet)
  have hK : IsCompact K := L.input.compact_support.union L.output.compact_support
  have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    (L.input.frame.open_baseSet.inter L.output.frame.open_baseSet)
  have hKU : K ⊆ U := by
    rintro z (hz | hz)
    · exact ⟨(L.input.support_subset hz).1, (L.input.support_subset hz).2,
        L.input_support_in_output_frame hz⟩
    · exact ⟨(L.output.support_subset hz).1, L.output_support_in_input_frame hz,
        (L.output.support_subset hz).2⟩
  have hcutoff (S O : Set V) (hS : IsCompact S) (hO : IsOpen O) (hSO : S ⊆ O) :
      ∃ β : V → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ O ∧
        S ⊆ interior {z | β z = 1} := by
    obtain ⟨W, hW, hSW, hWO, hWcompact⟩ :=
      exists_open_between_and_isCompact_closure hS hO hSO
    obtain ⟨D, hD, hWD, hDO, hDcompact⟩ :=
      exists_open_between_and_isCompact_closure hWcompact hO hWO
    obtain ⟨β, hβ, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hD isClosed_closure hWD
    have hts : tsupport β = closure D := congrArg closure hsupp
    refine ⟨β, hβ, ?_, ?_, ?_⟩
    · change IsCompact (tsupport β)
      rwa [hts]
    · rwa [hts]
    · apply hSW.trans
      apply interior_maximal ?_ hW
      intro z hz
      exact (hone z).mp (subset_closure hz)
  obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff K U hK hU hKU
  have hβK (z : V) (hz : z ∈ K) : β z = 1 :=
    (interior_subset (s := {z : V | β z = 1})) (honeβ hz)
  obtain ⟨χ, hχ, hcχ, _, honeχ⟩ :=
    hcutoff (tsupport β) Set.univ hcβ isOpen_univ (Set.subset_univ _)
  -- Compactify the original Schwartz operator before transposing it.
  let p₀ := cutoffSymbol β β L.symbol
  have hp₀ : IsSymbol Set.univ m p₀ :=
    isSymbol_cutoffSymbol m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
  let P₀ := amplitudeOperator m (cutoffAmplitude β β L.symbol)
    (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
    (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ)
  have hP₀ (v : 𝓢(V, H r)) (z : V) : P₀ v z = quantize p₀ v z := by
    rw [show P₀ v z = amplitudeApply (cutoffAmplitude β β L.symbol) v z from
      amplitudeOperator_apply m _ _ _ v z]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
      (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ) v) z).symm
  have hP₀support : HasOperatorSupport (tsupport β) P₀ := by
    simpa only [Set.union_self] using
      hasOperatorSupport_cutoff m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
  have hp₀compact : HasCompactSupport p₀ :=
    hcβ.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ P₀ hP₀
        (tsupport β) (isClosed_tsupport β) hP₀support)
  let Q := localFormalAdjoint m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
  let q₀ := adjointSymbol χ p₀
  have hq₀ : IsSymbol Set.univ m q₀ :=
    isSymbol_adjointSymbol m p₀ hp₀ hp₀compact χ hχ hcχ
  have hQ (v : 𝓢(V, H q)) (z : V) : Q v z = quantize q₀ v z :=
    localFormalAdjoint_apply m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
      χ hχ hcχ honeχ v z
  have hQpair : IsSchwartzFormalAdjoint P₀ Q :=
    isSchwartzFormalAdjoint_localFormalAdjoint m p₀ hp₀ P₀ hP₀
      (tsupport β) hcβ hP₀support
  -- The density and its inverse need smoothness only on this chart target.
  obtain ⟨ρ, hρ, hρpos, hρmap⟩ := hμ.exists_smooth_density c L.chart_mem_atlas
  have hβtarget : tsupport β ⊆ c.target := fun z hz ↦ (hsβ hz).1
  obtain ⟨GE, hGE, hGEinv, hGEpair⟩ := hgramE c L.chart_mem_atlas L.input.frame
  obtain ⟨GF, hGF, _, hGFpair⟩ := hgramF c L.chart_mem_atlas L.output.frame
  have hUE : U ⊆ c.target ∩ c.symm ⁻¹' L.input.frame.baseSet :=
    fun z hz ↦ ⟨hz.1, hz.2.1⟩
  have hUF : U ⊆ c.target ∩ c.symm ⁻¹' L.output.frame.baseSet :=
    fun z hz ↦ ⟨hz.1, hz.2.2⟩
  let A : V → H r →L[ℂ] H r := cutoffMatrix β (fun z ↦ (ρ z)⁻¹ • (GE z).inverse)
  let B : V → H q →L[ℂ] H q := cutoffMatrix β (fun z ↦ ρ z • GF z)
  have hA : ContDiff ℝ ∞ A := contDiff_cutoffMatrix U hU _
    (((hρ.mono (fun z hz ↦ hz.1)).inv
      (fun z hz ↦ ne_of_gt (hρpos z hz.1))).smul (hGEinv.mono hUE)) β hβ hsβ
  have hB : ContDiff ℝ ∞ B := contDiff_cutoffMatrix U hU _
    ((hρ.mono (fun z hz ↦ hz.1)).smul (hGF.mono hUF)) β hβ hsβ
  have hcA : HasCompactSupport A := hasCompactSupport_cutoffMatrix β _ hcβ
  have hcB : HasCompactSupport B := hasCompactSupport_cutoffMatrix β _ hcβ
  let W := (matrixMultiplierCLM A hA hcA).comp
    (Q.comp (matrixMultiplierCLM B hB hcB))
  let w := amplitudeSymbol (matrixAmplitude A B q₀)
  have hw : IsSymbol Set.univ m w :=
    isSymbol_amplitudeSymbol m _ (isAmplitude_matrixAmplitude m q₀ hq₀ A B hA hB)
      (hasCompactSupport_matrixAmplitude A B q₀ hcA hcB)
  have hW (v : 𝓢(V, H q)) (z : V) : W v z = quantize w v z := by
    change matrixMultiplierCLM A hA hcA (Q (matrixMultiplierCLM B hB hcB v)) z = _
    rw [matrixMultiplierCLM_apply, hQ]
    exact (quantize_matrixAmplitude m q₀ hq₀ A B hA hcA hB hcB v z).symm
  let LT : PseudodifferentialPiece (n := n) (r := q) (q := r) F E m :=
    { chart := c
      chart_mem_atlas := L.chart_mem_atlas
      input := L.output
      output := L.input
      input_support_in_output_frame := L.output_support_in_input_frame
      output_support_in_input_frame := L.input_support_in_output_frame
      operator := W
      symbol := w
      isSymbol := hw
      operator_apply := hW }
  have hpair : IsMetricFormalAdjoint h k μ L.toLinearMap LT.toLinearMap := by
    intro u v
    let u₀ := L.input.localize L.chart_mem_atlas u
    let v₀ := L.output.localize L.chart_mem_atlas v
    let b := matrixMultiplierCLM B hB hcB v₀
    have hu₀zero (z : V) (hz : z ∉ tsupport L.input.cutoff) : u₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.input.tsupport_localizedFunction_subset u hz'))
    have hv₀zero (z : V) (hz : z ∉ tsupport L.output.cutoff) : v₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.output.tsupport_localizedFunction_subset v hz'))
    have hβgrowth : (fun z : V ↦ (β z : ℂ)).HasTemperateGrowth :=
      (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hβ)
    have hβu : SchwartzMap.smulLeftCLM (H r) (fun z ↦ (β z : ℂ)) u₀ = u₀ := by
      ext z : 1
      rw [SchwartzMap.smulLeftCLM_apply_apply hβgrowth]
      by_cases hz : z ∈ tsupport L.input.cutoff
      · rw [hβK z (Or.inl hz), Complex.ofReal_one, one_smul]
      · rw [hu₀zero z hz, smul_zero]
    have hP₀apply (z : V) : P₀ u₀ z = β z • L.operator u₀ z := by
      rw [show P₀ u₀ z = amplitudeApply (cutoffAmplitude β β L.symbol) u₀ z from
        amplitudeOperator_apply m _ _ _ u₀ z]
      rw [amplitudeApply_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ hcβ hcβ,
        hβu, ← L.operator_apply]
    have hb (z : V) : b z = ρ z • GF z (v₀ z) := by
      rw [show b z = B z (v₀ z) from matrixMultiplierCLM_apply B hB hcB v₀ z]
      change β z • (ρ z • GF z (v₀ z)) = _
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · rw [hv₀zero z hz, map_zero, smul_zero, smul_zero]
    have hWapply (z : V) :
        W v₀ z = β z • ((ρ z)⁻¹ • (GE z).inverse (Q b z)) :=
      matrixMultiplierCLM_apply A hA hcA (Q b) z
    -- Move each global pairing into this single original chart using its prescribed density.
    have hleftChart : k.sectionPairing μ
        (L.output.extend L.chart_mem_atlas (L.operator u₀)) v =
        ∫ z, inner ℂ (L.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      let A := L.output
      let G := GF
      let hc := L.chart_mem_atlas
      let u := v
      let v := L.operator u₀
      let h := k
      have hG : ∀ z ∈ tsupport A.cutoff, ∀ a b : H q,
          h.pairing (L.chart.symm z) (A.frame.symmL ℂ (L.chart.symm z) a)
            (A.frame.symmL ℂ (L.chart.symm z) b) = inner ℂ a (G z b) := by
        intro z hz a b
        exact (hGFpair z (L.output.support_subset hz)).2 a b
      rw [SmoothHermitianMetric.sectionPairing]
      rw [hchartIntegral L.chart μ ρ hρ.continuousOn
        (fun z hz ↦ (hρpos z hz).le) hρmap _
        (h.contMDiff_pairing (A.extend hc v) u).continuous (by
          intro x hx
          by_contra hxc
          apply hx
          change h.pairing x (A.extendedFunction v x) (u.val x) = 0
          rw [show A.extendedFunction v x = 0 by
            simp [BundleChartCutoff.extendedFunction, hxc]]
          let : InnerProductSpace.Core ℂ (F x) := h.toCore x
          exact InnerProductSpace.Core.inner_zero_left _)]
      calc
        _ = ∫ z in L.chart.target, inner ℂ (v z) (ρ z • G z (A.localize hc u z)) := by
          apply setIntegral_congr_fun L.chart.open_target.measurableSet
          intro z hz
          change ρ z • h.pairing (L.chart.symm z) (A.extendedFunction v (L.chart.symm z))
            (u.val (L.chart.symm z)) = inner ℂ (v z) (ρ z • G z (A.localizedFunction u z))
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            L.chart.map_target hz, ite_true, L.chart.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hu : u.val (L.chart.symm z) =
                A.frame.symmL ℂ (L.chart.symm z) (sectionInChart F L.chart A.frame u.val z) := by
              symm
              rw [sectionInChart, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
                A.frame.symmL_continuousLinearMapAt he]
            have hsmul : h.pairing (L.chart.symm z)
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z))
                (u.val (L.chart.symm z)) =
                  (A.cutoff z : ℂ) * h.pairing (L.chart.symm z)
                    (A.frame.symmL ℂ (L.chart.symm z) (v z)) (u.val (L.chart.symm z)) := by
              let : InnerProductSpace.Core ℂ (F (L.chart.symm z)) := h.toCore (L.chart.symm z)
              change (h.toCore (L.chart.symm z)).inner
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z))
                (u.val (L.chart.symm z)) =
                  (A.cutoff z : ℂ) * (h.toCore (L.chart.symm z)).inner
                    (A.frame.symmL ℂ (L.chart.symm z) (v z)) (u.val (L.chart.symm z))
              rw [InnerProductSpace.Core.inner_smul_left, Complex.conj_ofReal]
            rw [hsmul, hu, hG z hb, map_smul]
            simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
              smul_eq_mul]
          · rw [image_eq_zero_of_notMem_tsupport hb]
            simp only [Complex.ofReal_zero, zero_smul, map_zero]
            have hzero : h.pairing (L.chart.symm z) 0 (u.val (L.chart.symm z)) = 0 := by
              let : InnerProductSpace.Core ℂ (F (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_zero_left _
            rw [hzero, smul_zero, smul_zero, inner_zero_right]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change inner ℂ (v z) (ρ z • G z (A.localizedFunction u z)) = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hrightChart : h.sectionPairing μ u
        (L.input.extend L.chart_mem_atlas (W v₀)) =
        ∫ z, inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) := by
      let A := L.input
      let G := GE
      let hc := L.chart_mem_atlas
      let v := W v₀
      have hG : ∀ z ∈ tsupport A.cutoff, ∀ a b : H r,
          h.pairing (L.chart.symm z) (A.frame.symmL ℂ (L.chart.symm z) a)
            (A.frame.symmL ℂ (L.chart.symm z) b) = inner ℂ a (G z b) := by
        intro z hz a b
        exact (hGEpair z (L.input.support_subset hz)).2 a b
      rw [SmoothHermitianMetric.sectionPairing]
      rw [hchartIntegral L.chart μ ρ hρ.continuousOn
        (fun z hz ↦ (hρpos z hz).le) hρmap _
        (h.contMDiff_pairing u (A.extend hc v)).continuous (by
          intro x hx
          by_contra hxc
          apply hx
          change h.pairing x (u.val x) (A.extendedFunction v x) = 0
          rw [show A.extendedFunction v x = 0 by
            simp [BundleChartCutoff.extendedFunction, hxc]]
          let : InnerProductSpace.Core ℂ (E x) := h.toCore x
          exact InnerProductSpace.Core.inner_zero_right _)]
      calc
        _ = ∫ z in L.chart.target, inner ℂ (A.localize hc u z) (ρ z • G z (v z)) := by
          apply setIntegral_congr_fun L.chart.open_target.measurableSet
          intro z hz
          change ρ z • h.pairing (L.chart.symm z) (u.val (L.chart.symm z))
            (A.extendedFunction v (L.chart.symm z)) =
              inner ℂ (A.localizedFunction u z) (ρ z • G z (v z))
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            L.chart.map_target hz, ite_true, L.chart.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hu : u.val (L.chart.symm z) =
                A.frame.symmL ℂ (L.chart.symm z) (sectionInChart E L.chart A.frame u.val z) := by
              symm
              rw [sectionInChart, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
                A.frame.symmL_continuousLinearMapAt he]
            have hsmul : h.pairing (L.chart.symm z) (u.val (L.chart.symm z))
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z)) =
                  (A.cutoff z : ℂ) * h.pairing (L.chart.symm z)
                    (u.val (L.chart.symm z)) (A.frame.symmL ℂ (L.chart.symm z) (v z)) := by
              let : InnerProductSpace.Core ℂ (E (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_smul_right _ _
            rw [hsmul, hu, hG z hb]
            simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
              inner_smul_right, Complex.conj_ofReal, smul_eq_mul]
          · rw [image_eq_zero_of_notMem_tsupport hb]
            simp only [Complex.ofReal_zero, zero_smul, inner_zero_left]
            have hzero : h.pairing (L.chart.symm z) (u.val (L.chart.symm z)) 0 = 0 := by
              let : InnerProductSpace.Core ℂ (E (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_zero_right _
            rw [hzero, smul_zero]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change inner ℂ (A.localizedFunction u z) (ρ z • G z (v z)) = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hleft (z : V) : inner ℂ (P₀ u₀ z) (b z) =
        inner ℂ (L.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      rw [hP₀apply, hb]
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · simp [hv₀zero z hz]
    have hright (z : V) : inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) =
        inner ℂ (u₀ z) (Q b z) := by
      by_cases hz : z ∈ tsupport L.input.cutoff
      · have hzE := L.input.support_subset hz
        obtain ⟨J, hJ⟩ := (hGEpair z hzE).1
        have hGI (a : H r) : GE z ((GE z).inverse a) = a := by
          rw [← hJ, ContinuousLinearMap.inverse_equiv]
          exact J.apply_symm_apply a
        rw [hWapply, hβK z (Or.inl hz), one_smul, ContinuousLinearMap.map_smul_of_tower, hGI,
          smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos z hzE.1)), one_smul]
      · simp [hu₀zero z hz]
    change k.sectionPairing μ (L.output.extend L.chart_mem_atlas (L.operator u₀)) v =
      h.sectionPairing μ u (L.input.extend L.chart_mem_atlas (W v₀))
    rw [hleftChart, hrightChart]
    calc
      _ = ∫ z, inner ℂ (P₀ u₀ z) (b z) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hleft z).symm))
      _ = ∫ z, inner ℂ (u₀ z) (Q b z) := hQpair u₀ b
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hright z).symm))
  have adjointOrder {s t : ℕ} (U : Set TModel) (m : ℝ)
      (a : SymbolFunction n s t) (ha : IsSymbol U m a) :
      IsSymbol U m (fun x ξ ↦ (a x ξ).adjoint) := by
    let V := EuclideanSpace ℂ (Fin s) →L[ℂ] EuclideanSpace ℂ (Fin t)
    let W := EuclideanSpace ℂ (Fin t) →L[ℂ] EuclideanSpace ℂ (Fin s)
    let J : V ≃ₗᵢ[ℝ] W := {
      toEquiv := (ContinuousLinearMap.adjoint : V ≃ₗᵢ⋆[ℂ] W).toEquiv
      map_add' := map_add ContinuousLinearMap.adjoint
      map_smul' := by
        intro t A
        change (t • A).adjoint = t • A.adjoint
        rw [← Complex.coe_smul t A, map_smulₛₗ]
        simp
      norm_map' := ContinuousLinearMap.adjoint.norm_map }
    refine ⟨J.contDiff.comp_contDiffOn ha.1, ?_⟩
    intro K hK hcompact i j
    obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    let Jj : (TModel [×j]→L[ℝ] V) ≃ₗᵢ[ℝ] (TModel [×j]→L[ℝ] W) := {
      toLinearEquiv := (J.toContinuousLinearEquiv.continuousMultilinearMapCongrRight
        (fun _ : Fin j ↦ TModel)).toLinearEquiv
      norm_map' := fun f ↦ J.toLinearIsometry.norm_compContinuousMultilinearMap f }
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a y η).adjoint) ξ) =
        Jj ∘ (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) := by
      funext y
      exact J.toContinuousLinearEquiv.iteratedFDeriv_comp_left
    change ‖iteratedFDeriv ℝ i
      (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ (a y η).adjoint) ξ) x‖ ≤ _
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hbound x hx ξ
  -- The original pairing identifies the supplied map with this very same local piece.
  have hmap : T = LT.toLinearMap :=
    (show IsMetricFormalAdjoint h k μ L.toLinearMap T from hT).unique hpair
  refine ⟨1, fun _ ↦ LT, ?_, ?_⟩
  · rw [hmap, Fin.sum_univ_one, sub_self]
    let K₀ : SmoothKernel (n := n) (r := q) (q := r) F E :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro e f _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames F E (fun _ _ ↦ 0) e f z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K₀, ?_⟩
    ext u x
    simp [SmoothKernel.toLinearMap, SmoothKernel.apply, K₀]
  rw [Fin.sum_univ_one, h.principalSymbolAdjoint_class]
  apply (globalPrincipalSymbolClass_eq_iff F E m _ _).mpr
  -- Retain all three first-order remainders before canceling the density weights.
  let a : SymbolFunction n r q := fun z ξ ↦ cutoffAmplitude β β L.symbol z z ξ
  have hpLow : IsSymbol Set.univ (m - 1) (p₀ - a) := by
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol β β hβ hβ hcβ hcβ 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] using h
  have hqLow : IsSymbol Set.univ (m - 1) (q₀ - symbolAdjoint p₀) :=
    isSymbol_adjointSymbol_sub m p₀ hp₀ hp₀compact χ hχ hcχ (by
      intro z hz
      apply interior_subset (honeχ _)
      exact tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ P₀ hP₀
        (tsupport β) (isClosed_tsupport β) hP₀support hz)
  have htSub (p p' : SymbolFunction n r q) :
      symbolAdjoint (p - p') = symbolAdjoint p - symbolAdjoint p' := by
    funext z ξ
    exact map_sub ContinuousLinearMap.adjoint (p z ξ) (p' z ξ)
  let d : SymbolFunction n q r := w - matrixSymbol A B (symbolAdjoint a)
  have hd : IsSymbol Set.univ (m - 1) d := by
    have h₁ := isSymbol_amplitudeSymbol_matrixAmplitude_sub m q₀ hq₀ A B hA hcA hB hcB
    have h₂ := isSymbol_matrixSymbol Set.univ isOpen_univ (m - 1)
      (q₀ - symbolAdjoint p₀) hqLow A B hA.contDiffOn hB.contDiffOn
    have h₃ := isSymbol_matrixSymbol Set.univ isOpen_univ (m - 1)
      (symbolAdjoint (p₀ - a))
      (adjointOrder Set.univ (m - 1) _ hpLow)
      A B hA.contDiffOn hB.contDiffOn
    have heq : d = (w - matrixSymbol A B q₀) +
        matrixSymbol A B (q₀ - symbolAdjoint p₀) +
        matrixSymbol A B (symbolAdjoint (p₀ - a)) := by
      rw [htSub]
      ext z ξ v
      simp only [d, matrixSymbol, Pi.sub_apply, Pi.add_apply,
        sub_apply, add_apply,
        ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [heq]
    exact (h₁.add isOpen_univ h₂).add isOpen_univ h₃
  -- A final compact plateau packages that lower-order difference as a genuine global symbol.
  let b := zeroExtendedSymbol Set.univ β d
  have hb : IsSymbol Set.univ (m - 1) b :=
    isSymbol_zeroExtendedSymbol Set.univ isOpen_univ (m - 1) β hβ hcβ
      (Set.subset_univ _) d hd
  have hbc : HasCompactSupport b :=
    hasCompactSupport_zeroExtendedSymbol Set.univ β d hcβ
  let R : PseudodifferentialPiece (n := n) (r := q) (q := r)
      F E (m - 1) :=
    { chart := c
      chart_mem_atlas := L.chart_mem_atlas
      input := L.output
      output := L.input
      input_support_in_output_frame := LT.input_support_in_output_frame
      output_support_in_input_frame := LT.output_support_in_input_frame
      operator := quantizeSchwartz (m - 1) b hb hbc
      symbol := b
      isSymbol := hb
      operator_apply := quantizeSchwartz_apply (m - 1) b hb hbc }
  have heq : LT.globalSymbolFunction -
      h.symbolAdjoint k L.globalSymbolFunction =
      R.globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ c.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
    · have hz : c x ∈ symbolChartDomain E F c L.input.frame L.output.frame :=
        ⟨⟨c.map_source hx.1.1,
          by simpa only [Set.mem_preimage, c.left_inv hx.1.1] using hx.1.2⟩,
          by simpa only [Set.mem_preimage, c.left_inv hx.1.1] using hx.2⟩
      have hz' : c x ∈ symbolChartDomain F E c L.output.frame L.input.frame :=
        ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩
      have hformula (η : V) :
          globalSymbolInChart F E (h.symbolAdjoint k L.globalSymbolFunction)
              c L.output.frame L.input.frame (c x) η =
            (GE (c x)).inverse.comp
              ((globalSymbolInChart E F L.globalSymbolFunction
                c L.input.frame L.output.frame (c x) η).adjoint.comp (GF (c x))) := by
        let y := c.symm (c x)
        let A := globalSymbolInChart E F L.globalSymbolFunction
          c L.input.frame L.output.frame (c x) η
        let B := globalSymbolInChart F E (h.symbolAdjoint k L.globalSymbolFunction)
          c L.output.frame L.input.frame (c x) η
        apply ContinuousLinearMap.ext
        intro v
        have hw : GE (c x) (B v) = A.adjoint (GF (c x) v) := by
          apply ext_inner_left ℂ
          intro u
          rw [← (hGEpair (c x) ⟨hz.1.1, hz.1.2⟩).2,
            ContinuousLinearMap.adjoint_inner_right,
            ← (hGFpair (c x) ⟨hz.1.1, hz.2⟩).2]
          change h.pairing y (L.input.frame.symmL ℂ y u)
              (L.input.frame.symmL ℂ y (L.input.frame.continuousLinearMapAt ℂ y
                (h.adjoint k y (L.globalSymbolFunction y (covectorFromChart c y η))
                  (L.output.frame.symmL ℂ y v)))) =
            k.pairing y (L.output.frame.symmL ℂ y
              (L.output.frame.continuousLinearMapAt ℂ y
                (L.globalSymbolFunction y (covectorFromChart c y η)
                  (L.input.frame.symmL ℂ y u)))) (L.output.frame.symmL ℂ y v)
          rw [L.input.frame.symmL_continuousLinearMapAt hz.1.2, h.pairing_adjoint,
            L.output.frame.symmL_continuousLinearMapAt hz.2]
        obtain ⟨J, hJ⟩ := (hGEpair (c x) ⟨hz.1.1, hz.1.2⟩).1
        have hinverse : (GE (c x)).inverse (GE (c x) (B v)) = B v := by
          rw [← hJ, ContinuousLinearMap.inverse_equiv]
          exact J.symm_apply_apply _
        exact hinverse.symm.trans (congrArg (GE (c x)).inverse hw)
      let t : SymbolFunction n q r :=
        matrixSymbol (fun z ↦ (GE z).inverse) GF (symbolAdjoint L.symbol)
      have hcoord :
          globalSymbolInChart F E LT.globalSymbolFunction c L.output.frame L.input.frame
              (c x) (covectorInChart c x ξ) -
            globalSymbolInChart F E
              (h.symbolAdjoint k L.globalSymbolFunction)
              c L.output.frame L.input.frame (c x) (covectorInChart c x ξ) =
          globalSymbolInChart F E R.globalSymbolFunction c L.output.frame L.input.frame
              (c x) (covectorInChart c x ξ) := by
        rw [LT.globalSymbolInChart_globalSymbolFunction _ _ hz',
          R.globalSymbolInChart_globalSymbolFunction _ _ hz']
        change ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) •
            w (c x) (covectorInChart c x ξ) -
            globalSymbolInChart F E
              (h.symbolAdjoint k L.globalSymbolFunction)
              c L.output.frame L.input.frame (c x) (covectorInChart c x ξ) =
          ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) •
            b (c x) (covectorInChart c x ξ)
        rw [hformula, L.globalSymbolInChart_globalSymbolFunction _ _ hz]
        have htrans (η : V) :
            (GE (c x)).inverse.comp
              ((((L.output.cutoff (c x) * L.input.cutoff (c x) : ℝ) : ℂ) •
                L.symbol (c x) η).adjoint.comp (GF (c x))) =
              ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) • t (c x) η := by
          ext v : 1
          change (GE (c x)).inverse
            (((((L.output.cutoff (c x) * L.input.cutoff (c x) : ℝ) : ℂ) •
              L.symbol (c x) η).adjoint) (GF (c x) v)) =
            ((L.input.cutoff (c x) * L.output.cutoff (c x) : ℝ) : ℂ) •
              (GE (c x)).inverse ((L.symbol (c x) η).adjoint (GF (c x) v))
          simp only [map_smulₛₗ, Complex.conj_ofReal, smul_apply, RingHom.id_apply,
            mul_comm (L.output.cutoff (c x))]
        rw [htrans]
        by_cases hin : L.input.cutoff (c x) = 0
        · simp [hin]
        have hone : β (c x) = 1 := hβK _ (Or.inl (subset_tsupport _ hin))
        have ha (η : V) : symbolAdjoint a (c x) η = symbolAdjoint L.symbol (c x) η := by
          simp [symbolAdjoint, a, cutoffAmplitude, hone]
        have hdiag (η : V) : matrixSymbol A B (symbolAdjoint a) (c x) η = t (c x) η := by
          change (A (c x)).comp ((symbolAdjoint a (c x) η).comp (B (c x))) = _
          rw [ha]
          ext v : 1
          change β (c x) • ((ρ (c x))⁻¹ • (GE (c x)).inverse
            (symbolAdjoint L.symbol (c x) η (β (c x) • (ρ (c x) • GF (c x) v)))) =
              (GE (c x)).inverse (symbolAdjoint L.symbol (c x) η (GF (c x) v))
          simp only [hone, ContinuousLinearMap.map_smul_of_tower, smul_smul, one_mul,
            inv_mul_cancel₀ (ne_of_gt (hρpos _ (c.map_source hx.1.1))), one_smul]
        simp only [b, zeroExtendedSymbol, Set.mem_univ, ite_true, hone,
          Complex.ofReal_one, one_smul, d, Pi.sub_apply, hdiag, smul_sub]
      -- The Gram operators belong to the two specified metrics on these exact frames.
      rw [globalSymbolInChart_covectorInChart _ _ _ c L.chart_mem_atlas
          L.output.frame L.input.frame x hx.1.1 ξ,
        globalSymbolInChart_covectorInChart _ _ _ c L.chart_mem_atlas
          L.output.frame L.input.frame x hx.1.1 ξ,
        globalSymbolInChart_covectorInChart _ _ _ c L.chart_mem_atlas
          L.output.frame L.input.frame x hx.1.1 ξ] at hcoord
      ext v : 1
      have hv := congrArg (fun D : H q →L[ℂ] H r ↦
        L.input.frame.symmL ℂ x (D (L.output.frame.continuousLinearMapAt ℂ x v))) hcoord
      change L.input.frame.symmL ℂ x
        (L.input.frame.continuousLinearMapAt ℂ x (LT.globalSymbolFunction x ξ
            (L.output.frame.symmL ℂ x (L.output.frame.continuousLinearMapAt ℂ x v))) -
          L.input.frame.continuousLinearMapAt ℂ x
            (h.symbolAdjoint k L.globalSymbolFunction x ξ
              (L.output.frame.symmL ℂ x (L.output.frame.continuousLinearMapAt ℂ x v)))) =
        L.input.frame.symmL ℂ x (L.input.frame.continuousLinearMapAt ℂ x
          (R.globalSymbolFunction x ξ
            (L.output.frame.symmL ℂ x (L.output.frame.continuousLinearMapAt ℂ x v)))) at hv
      simpa only [Pi.sub_apply, sub_apply, map_sub,
        L.output.frame.symmL_continuousLinearMapAt hx.2,
        L.input.frame.symmL_continuousLinearMapAt hx.1.2] using hv
    · have hx' : x ∉ c.source ∩ L.output.frame.baseSet ∩ L.input.frame.baseSet := by
        simpa only [Set.inter_right_comm] using hx
      have hxL : x ∉ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet := hx
      have hzero : L.globalSymbolFunction x ξ = 0 := by
        simp only [PseudodifferentialPiece.globalSymbolFunction, ite_eq_right hxL]
      have hzeroAdj : h.symbolAdjoint k L.globalSymbolFunction x ξ = 0 := by
        simp only [SmoothHermitianMetric.symbolAdjoint, hzero, h.adjoint_zero]
      simp only [Pi.sub_apply, hzeroAdj, sub_zero,
        PseudodifferentialPiece.globalSymbolFunction, LT, R, ite_eq_right hx']
  change IsGlobalSymbol F E (m - 1)
    (LT.globalSymbolFunction - h.symbolAdjoint k L.globalSymbolFunction)
  rw [heq]
  exact R.isGlobalSymbol_globalSymbolFunction

omit hT2 hSC hC hBorel hE hF hμ [MeasurableSpace M] in
/-- The actual weighted fiber adjoint preserves the compact-local inverse bound.
The two Gram factors are frequency independent and retain the original norms. -/
private theorem SmoothHermitianMetric.isEllipticFullGlobalSymbol_symbolAdjoint {m : ℝ}
    (p : GlobalSymbolFunction (n := n) E F)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m p) :
    IsEllipticFullGlobalSymbol (r := q) (q := r) F E m (h.symbolAdjoint k p) := by
  classical
  let P := EuclideanSpace ℝ (Fin n)
  intro c hc f e hf he
  let U := symbolChartDomain E F c e f
  have hswap : symbolChartDomain F E c f e = U := by
    ext z
    simp only [symbolChartDomain, U, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [hswap]
  -- Each supplied metric gives a smooth invertible Gram operator in its original frame.
  let toOpE : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let matrixOpE : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap (toOpE.restrictScalars ℝ)
  let GE (x : M) := matrixOpE (h.gramMatrix e x)
  have gramSmoothE : ContMDiffOn 𝓘(ℝ, P)
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      GE e.baseSet := by
    apply matrixOpE.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact h.contMDiffOn_gram e i j
  have gramInvertibleE (x : M) (hx : x ∈ e.baseSet) : (GE x).IsInvertible := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
      (h.isUnit_det_gramMatrix e x hx)
    let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
    refine ⟨Q.trans (L.trans Q.symm), ?_⟩
    ext v i
    rfl
  have gramPairingE (x : M) (hx : x ∈ e.baseSet)
      (u v : EuclideanSpace ℂ (Fin r)) :
      inner ℂ u (GE x v) = h.pairing x (e.symmL ℂ x u) (e.symmL ℂ x v) := by
    rw [h.pairing_eq_gramMatrix e x hx]
    have hcoord (w : EuclideanSpace ℂ (Fin r)) :
        (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact e.continuousLinearMapAt_symmL hx w
    rw [hcoord, hcoord]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, (∑ j, h.gramMatrix e x i j * v j) * star (u i)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  have hGE : ContDiffOn ℝ ∞ (fun z ↦ GE (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := gramSmoothE.contMDiffAt (e.open_baseSet.mem_nhds hz.1.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  let toOpF : Matrix (Fin q) (Fin q) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let matrixOpF : Matrix (Fin q) (Fin q) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
    LinearMap.toContinuousLinearMap (toOpF.restrictScalars ℝ)
  let GF (x : M) := matrixOpF (k.gramMatrix f x)
  have gramSmoothF : ContMDiffOn 𝓘(ℝ, P)
      𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
      GF f.baseSet := by
    apply matrixOpF.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact k.contMDiffOn_gram f i j
  have gramInvertibleF (x : M) (hx : x ∈ f.baseSet) : (GF x).IsInvertible := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
      (k.isUnit_det_gramMatrix f x hx)
    let L := (LinearEquiv.ofBijective (k.gramMatrix f x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin q ↦ ℂ)
    refine ⟨Q.trans (L.trans Q.symm), ?_⟩
    ext v i
    rfl
  have gramPairingF (x : M) (hx : x ∈ f.baseSet)
      (u v : EuclideanSpace ℂ (Fin q)) :
      inner ℂ u (GF x v) = k.pairing x (f.symmL ℂ x u) (f.symmL ℂ x v) := by
    rw [k.pairing_eq_gramMatrix f x hx]
    have hcoord (w : EuclideanSpace ℂ (Fin q)) :
        (f ⟨x, f.symmL ℂ x w⟩).2 = w := by
      rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact f.continuousLinearMapAt_symmL hx w
    rw [hcoord, hcoord]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i, (∑ j, k.gramMatrix f x i j * v j) * star (u i)) = _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [starRingEnd_apply]
    ring
  have hGF : ContDiffOn ℝ ∞ (fun z ↦ GF (c.symm z)) U := by
    intro z hz
    have hbase := contMDiffAt_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, P)) (n := ∞) (IsManifold.subset_maximalAtlas hc) hz.1.1
    have hg := gramSmoothF.contMDiffAt (f.open_baseSet.mem_nhds hz.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hg.comp z hbase)).contDiffWithinAt
  -- Pairing with all source vectors fixes the two-sided Gram order at the same covector.
  have hformula (z η : P) (hz : z ∈ U) :
      globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η =
        (GE (c.symm z)).inverse.comp
          ((globalSymbolInChart E F p c e f z η).adjoint.comp (GF (c.symm z))) := by
    let x := c.symm z
    let T := p x (covectorFromChart c x η)
    let A := globalSymbolInChart E F p c e f z η
    let B := globalSymbolInChart F E (h.symbolAdjoint k p) c f e z η
    apply ContinuousLinearMap.ext
    intro v
    have hw : GE x (B v) = A.adjoint (GF x v) := by
      apply ext_inner_left ℂ
      intro u
      rw [gramPairingE x hz.1.2, ContinuousLinearMap.adjoint_inner_right,
        gramPairingF x hz.2]
      change h.pairing x (e.symmL ℂ x u)
          (e.symmL ℂ x (e.continuousLinearMapAt ℂ x
            (h.adjoint k x T (f.symmL ℂ x v)))) =
        k.pairing x (f.symmL ℂ x
          (f.continuousLinearMapAt ℂ x (T (e.symmL ℂ x u)))) (f.symmL ℂ x v)
      rw [e.symmL_continuousLinearMapAt hz.1.2, h.pairing_adjoint,
        f.symmL_continuousLinearMapAt hz.2]
    exact ((gramInvertibleE x hz.1.2).inverse_apply_self (B v)).symm.trans
      (congrArg (GE x).inverse hw)
  -- The inverse adjoint matrix has the reversed bounded Gram factors.
  have hGFinv : ContDiffOn ℝ ∞ (fun z ↦ (GF (c.symm z)).inverse) U := by
    intro z hz
    have hi := (gramInvertibleF (c.symm z) hz.2).contDiffAt_map_inverse (n := ∞)
    exact (hi.restrict_scalars ℝ).comp_contDiffWithinAt z (hGF z hz)
  intro K hKU hK
  obtain ⟨R, C, hR, hC, hbound⟩ := ha c hc e f K hKU hK
  obtain ⟨CE, hCE⟩ := (hK.image_of_continuousOn
    (hGE.continuousOn.norm.mono hKU)).bddAbove
  obtain ⟨CF, hCF⟩ := (hK.image_of_continuousOn
    (hGFinv.continuousOn.norm.mono hKU)).bddAbove
  let B := max CE 0
  let D := max CF 0
  have hB : 0 ≤ B := le_max_right _ _
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨R, D * C * B, hR, mul_nonneg (mul_nonneg hD hC) hB, ?_⟩
  intro z hz η hη
  have hzU := hKU hz
  obtain ⟨hA, hAnorm⟩ := hbound z hz η hη
  let A := globalSymbolInChart E F p c e f z η
  have hAA : A.adjoint.comp A.inverse.adjoint = ContinuousLinearMap.id ℂ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hA.inverse_comp_self,
      ContinuousLinearMap.adjoint_id]
  have hAA' : A.inverse.adjoint.comp A.adjoint = ContinuousLinearMap.id ℂ _ := by
    rw [← ContinuousLinearMap.adjoint_comp, hA.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]
  have hAi : A.adjoint.IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse hAA hAA'
  have hAinv : A.adjoint.inverse = A.inverse.adjoint :=
    ContinuousLinearMap.inverse_eq hAA hAA'
  rw [hformula z η hzU]
  have hE := gramInvertibleE (c.symm z) hzU.1.2
  have hF := gramInvertibleF (c.symm z) hzU.2
  refine ⟨hE.inverse.comp (hAi.comp hF), ?_⟩
  rw [hE.inverse.inverse_comp_of_left, hAi.inverse_comp_of_left,
    hE.inverse_inverse, hAinv]
  have hb : ‖GE (c.symm z)‖ ≤ B :=
    (hCE ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  have hd : ‖(GF (c.symm z)).inverse‖ ≤ D :=
    (hCF ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  calc
    ‖((GF (c.symm z)).inverse.comp A.inverse.adjoint).comp (GE (c.symm z))‖ ≤
        (‖(GF (c.symm z)).inverse‖ * ‖A.inverse.adjoint‖) * ‖GE (c.symm z)‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (D * (C * (1 + ‖η‖) ^ (-m))) * B := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul (mul_le_mul hd hAnorm (norm_nonneg _) hD) hb
        (norm_nonneg _) (mul_nonneg hD (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)))
    _ = (D * C * B) * (1 + ‖η‖) ^ (-m) := by ring

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

set_option maxHeartbeats 2500000 in
-- Assemble local metric adjoints with the original cutoff sums and prove uniqueness.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Weighted local adjunction produces the unique global PDO of the same real order. -/
theorem existsUnique_metricFormalAdjoint :
    ∃! Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m,
      IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap := by
  classical
  let TModel := EuclideanSpace ℝ (Fin n)
  let SourceModel := EuclideanSpace ℂ (Fin r)
  let TargetModel := EuclideanSpace ℂ (Fin q)
  -- The specified metrics give smooth invertible Gram weights in the chosen frames.
  have hgramE (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization SourceModel (π SourceModel E)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (SourceModel →L[ℂ] SourceModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : SourceModel,
            h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (SourceModel →L[ℂ] SourceModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : SourceModel →L[ℂ] SourceModel := toOp (h.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((h.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : SourceModel) :
        h.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : SourceModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [h.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * h.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, h.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : SourceModel ≃L[ℂ] SourceModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (h.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  have hgramF (c : OpenPartialHomeomorph M TModel) (hc : c ∈ atlas TModel M)
      (e : Trivialization TargetModel (π TargetModel F)) [MemTrivializationAtlas e] :
      ∃ G : TModel → (TargetModel →L[ℂ] TargetModel),
        ContDiffOn ℝ ∞ G (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ContDiffOn ℝ ∞ (fun z ↦ (G z).inverse) (c.target ∩ c.symm ⁻¹' e.baseSet) ∧
        ∀ z ∈ c.target ∩ c.symm ⁻¹' e.baseSet,
          (∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z) ∧
          (∀ u v : TargetModel,
            k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
              inner ℂ u (G z v)) := by
    classical
    let toOp : Matrix (Fin q) (Fin q) ℂ →L[ℝ] (TargetModel →L[ℂ] TargetModel) :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap.toLinearMap.comp
          Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
    let G (z : TModel) : TargetModel →L[ℂ] TargetModel := toOp (k.gramMatrix e (c.symm z))
    have hG (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) : ContDiffAt ℝ ∞ G z := by
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, TModel)) (n := ∞) hc) hz.1
      apply toOp.contDiff.contDiffAt.comp z
      apply contDiffAt_pi.mpr
      intro i
      apply contDiffAt_pi.mpr
      intro j
      exact (((k.contMDiffOn_gram e i j).contMDiffAt
        (e.open_baseSet.mem_nhds hz.2)).comp z hchart).contDiffAt
    have hpair (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) (u v : TargetModel) :
        k.pairing (c.symm z) (e.symmL ℂ (c.symm z) u) (e.symmL ℂ (c.symm z) v) =
          inner ℂ u (G z v) := by
      have hcoords (a : TargetModel) : (e ⟨c.symm z, e.symmL ℂ (c.symm z) a⟩).2 = a := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hz.2]
        exact e.continuousLinearMapAt_symmL hz.2 a
      rw [k.pairing_eq_gramMatrix e _ hz.2, hcoords u, hcoords v, PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ j, conj (u i) * k.gramMatrix e (c.symm z) i j * v j) =
        (∑ j, k.gramMatrix e (c.symm z) i j * v j) * conj (u i)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hequiv (z : TModel) (hz : z ∈ c.target ∩ c.symm ⁻¹' e.baseSet) :
        ∃ L : TargetModel ≃L[ℂ] TargetModel, L.toContinuousLinearMap = G z := by
      have hinj : Function.Injective (G z) := by
        intro u v huv
        have hzG : G z (u - v) = 0 := by rw [map_sub, huv, sub_self]
        have hzpair := hpair z hz (u - v) (u - v)
        rw [hzG, inner_zero_right] at hzpair
        have hzvec : e.symmL ℂ (c.symm z) (u - v) = 0 :=
          (k.toCore _).definite _ hzpair
        have hzcoords := congrArg (e.continuousLinearMapAt ℂ (c.symm z)) hzvec
        rw [e.continuousLinearMapAt_symmL hz.2, map_zero] at hzcoords
        exact sub_eq_zero.mp hzcoords
      exact ⟨(LinearEquiv.ofBijective (G z).toLinearMap
        ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩
    refine ⟨G, fun z hz ↦ (hG z hz).contDiffWithinAt, ?_, ?_⟩
    · intro z hz
      obtain ⟨L, hL⟩ := hequiv z hz
      have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G z) := by
        rw [← hL]
        exact (contDiffAt_map_inverse L).restrict_scalars ℝ
      exact (hi.comp z (hG z hz)).contDiffWithinAt
    · intro z hz
      exact ⟨hequiv z hz, hpair z hz⟩
  have hchartIntegral (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (μ : Measure M)
      (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContinuousOn w c.target)
      (hpos : ∀ z ∈ c.target, 0 ≤ w z)
      (hmap : Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z)))
      (f : M → ℂ) (hf : Continuous f) (hsupp : Function.support f ⊆ c.source) :
      (∫ x, f x ∂μ) = ∫ z in c.target, w z • f (c.symm z) := by
    classical
    -- Extend the target test by zero outside the prescribed chart target.
    let g : EuclideanSpace ℝ (Fin n) → ℂ := c.target.piecewise (fun z ↦ f (c.symm z)) (fun _ ↦ 0)
    have hg : Measurable g :=
      (hf.comp_continuousOn c.continuousOn_symm).measurable_piecewise
        continuousOn_const c.open_target.measurableSet
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w z)) (volume.restrict c.target) :=
      ENNReal.continuous_ofReal.continuousOn.comp hw (Set.mapsTo_univ _ _)
        |>.aemeasurable c.open_target.measurableSet
    calc
      (∫ x, f x ∂μ) = ∫ x in c.source, f x ∂μ := by
        symm
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ Function.notMem_support.mp (fun h ↦ hx (hsupp h)))
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
        simp [g, Set.piecewise_eq_of_mem, c.map_source hx, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet)
          hg.aestronglyMeasurable).symm
      _ = ∫ z in c.target, (ENNReal.ofReal (w z)).toReal • g z := by
        rw [hmap]
        exact integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)) g
      _ = ∫ z in c.target, w z • f (c.symm z) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        simp [g, Set.piecewise_eq_of_mem, hz, ENNReal.toReal_ofReal (hpos z hz)]
  -- A reversed piece uses the same chart and frames, with the prescribed density weights.
  have hpiece (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m) :
      ∃ T : smoothSections (n := n) (r := q) F →ₗ[ℂ]
          smoothSections (n := n) (r := r) E,
        IsMetricFormalAdjoint h k μ L.toLinearMap T ∧
          IsPseudodifferentialOperator F E μ m T := by
    classical
    let V := EuclideanSpace ℝ (Fin n)
    let H (s : ℕ) := EuclideanSpace ℂ (Fin s)
    let c := L.chart
    let := L.input.frame_mem_atlas
    let := L.output.frame_mem_atlas
    -- A common plateau lies strictly inside the original chart and both original frames.
    let K := tsupport L.input.cutoff ∪ tsupport L.output.cutoff
    let U := c.target ∩ c.symm ⁻¹' (L.input.frame.baseSet ∩ L.output.frame.baseSet)
    have hK : IsCompact K := L.input.compact_support.union L.output.compact_support
    have hU : IsOpen U := c.continuousOn_symm.isOpen_inter_preimage c.open_target
      (L.input.frame.open_baseSet.inter L.output.frame.open_baseSet)
    have hKU : K ⊆ U := by
      rintro z (hz | hz)
      · exact ⟨(L.input.support_subset hz).1, (L.input.support_subset hz).2,
          L.input_support_in_output_frame hz⟩
      · exact ⟨(L.output.support_subset hz).1, L.output_support_in_input_frame hz,
          (L.output.support_subset hz).2⟩
    have hcutoff (S O : Set V) (hS : IsCompact S) (hO : IsOpen O) (hSO : S ⊆ O) :
        ∃ β : V → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ O ∧
          S ⊆ interior {z | β z = 1} := by
      obtain ⟨W, hW, hSW, hWO, hWcompact⟩ :=
        exists_open_between_and_isCompact_closure hS hO hSO
      obtain ⟨D, hD, hWD, hDO, hDcompact⟩ :=
        exists_open_between_and_isCompact_closure hWcompact hO hWO
      obtain ⟨β, hβ, _, hsupp, hone⟩ :=
        exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hD isClosed_closure hWD
      have hts : tsupport β = closure D := congrArg closure hsupp
      refine ⟨β, hβ, ?_, ?_, ?_⟩
      · change IsCompact (tsupport β)
        rwa [hts]
      · rwa [hts]
      · apply hSW.trans
        apply interior_maximal ?_ hW
        intro z hz
        exact (hone z).mp (subset_closure hz)
    obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff K U hK hU hKU
    have hβK (z : V) (hz : z ∈ K) : β z = 1 :=
      (interior_subset (s := {z : V | β z = 1})) (honeβ hz)
    obtain ⟨χ, hχ, hcχ, _, honeχ⟩ :=
      hcutoff (tsupport β) Set.univ hcβ isOpen_univ (Set.subset_univ _)
    -- Compactify the original Schwartz operator before transposing it.
    let p₀ := cutoffSymbol β β L.symbol
    have hp₀ : IsSymbol Set.univ m p₀ :=
      isSymbol_cutoffSymbol m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
    let P₀ := amplitudeOperator m (cutoffAmplitude β β L.symbol)
      (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
      (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ)
    have hP₀ (v : 𝓢(V, H r)) (z : V) : P₀ v z = quantize p₀ v z := by
      rw [show P₀ v z = amplitudeApply (cutoffAmplitude β β L.symbol) v z from
        amplitudeOperator_apply m _ _ _ v z]
      exact (congrFun (quantize_amplitudeSymbol m _
        (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ)
        (hasCompactSupport_cutoffAmplitude L.symbol β β hcβ hcβ) v) z).symm
    have hP₀support : HasOperatorSupport (tsupport β) P₀ := by
      simpa only [Set.union_self] using
        hasOperatorSupport_cutoff m L.symbol L.isSymbol β β hβ hβ hcβ hcβ
    have hp₀compact : HasCompactSupport p₀ :=
      hcβ.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_symbol_subset_of_hasOperatorSupport m p₀ hp₀ P₀ hP₀
          (tsupport β) (isClosed_tsupport β) hP₀support)
    let Q := localFormalAdjoint m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
    let q₀ := adjointSymbol χ p₀
    have hq₀ : IsSymbol Set.univ m q₀ :=
      isSymbol_adjointSymbol m p₀ hp₀ hp₀compact χ hχ hcχ
    have hQ (v : 𝓢(V, H q)) (z : V) : Q v z = quantize q₀ v z :=
      localFormalAdjoint_apply m p₀ hp₀ P₀ hP₀ (tsupport β) hcβ hP₀support
        χ hχ hcχ honeχ v z
    have hQpair : IsSchwartzFormalAdjoint P₀ Q :=
      isSchwartzFormalAdjoint_localFormalAdjoint m p₀ hp₀ P₀ hP₀
        (tsupport β) hcβ hP₀support
    -- The density and its inverse need smoothness only on this chart target.
    obtain ⟨ρ, hρ, hρpos, hρmap⟩ := hμ.exists_smooth_density c L.chart_mem_atlas
    have hβtarget : tsupport β ⊆ c.target := fun z hz ↦ (hsβ hz).1
    obtain ⟨GE, hGE, hGEinv, hGEpair⟩ := hgramE c L.chart_mem_atlas L.input.frame
    obtain ⟨GF, hGF, _, hGFpair⟩ := hgramF c L.chart_mem_atlas L.output.frame
    have hUE : U ⊆ c.target ∩ c.symm ⁻¹' L.input.frame.baseSet :=
      fun z hz ↦ ⟨hz.1, hz.2.1⟩
    have hUF : U ⊆ c.target ∩ c.symm ⁻¹' L.output.frame.baseSet :=
      fun z hz ↦ ⟨hz.1, hz.2.2⟩
    let A : V → H r →L[ℂ] H r := cutoffMatrix β (fun z ↦ (ρ z)⁻¹ • (GE z).inverse)
    let B : V → H q →L[ℂ] H q := cutoffMatrix β (fun z ↦ ρ z • GF z)
    have hA : ContDiff ℝ ∞ A := contDiff_cutoffMatrix U hU _
      (((hρ.mono (fun z hz ↦ hz.1)).inv
        (fun z hz ↦ ne_of_gt (hρpos z hz.1))).smul (hGEinv.mono hUE)) β hβ hsβ
    have hB : ContDiff ℝ ∞ B := contDiff_cutoffMatrix U hU _
      ((hρ.mono (fun z hz ↦ hz.1)).smul (hGF.mono hUF)) β hβ hsβ
    have hcA : HasCompactSupport A := hasCompactSupport_cutoffMatrix β _ hcβ
    have hcB : HasCompactSupport B := hasCompactSupport_cutoffMatrix β _ hcβ
    let W := (matrixMultiplierCLM A hA hcA).comp
      (Q.comp (matrixMultiplierCLM B hB hcB))
    let w := amplitudeSymbol (matrixAmplitude A B q₀)
    have hw : IsSymbol Set.univ m w :=
      isSymbol_amplitudeSymbol m _ (isAmplitude_matrixAmplitude m q₀ hq₀ A B hA hB)
        (hasCompactSupport_matrixAmplitude A B q₀ hcA hcB)
    have hW (v : 𝓢(V, H q)) (z : V) : W v z = quantize w v z := by
      change matrixMultiplierCLM A hA hcA (Q (matrixMultiplierCLM B hB hcB v)) z = _
      rw [matrixMultiplierCLM_apply, hQ]
      exact (quantize_matrixAmplitude m q₀ hq₀ A B hA hcA hB hcB v z).symm
    let LT : PseudodifferentialPiece (n := n) (r := q) (q := r) F E m :=
      { chart := c
        chart_mem_atlas := L.chart_mem_atlas
        input := L.output
        output := L.input
        input_support_in_output_frame := L.output_support_in_input_frame
        output_support_in_input_frame := L.input_support_in_output_frame
        operator := W
        symbol := w
        isSymbol := hw
        operator_apply := hW }
    refine ⟨LT.toLinearMap, ?_, LT.isPseudodifferentialOperator m⟩
    intro u v
    let u₀ := L.input.localize L.chart_mem_atlas u
    let v₀ := L.output.localize L.chart_mem_atlas v
    let b := matrixMultiplierCLM B hB hcB v₀
    have hu₀zero (z : V) (hz : z ∉ tsupport L.input.cutoff) : u₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.input.tsupport_localizedFunction_subset u hz'))
    have hv₀zero (z : V) (hz : z ∉ tsupport L.output.cutoff) : v₀ z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hz' ↦ hz (L.output.tsupport_localizedFunction_subset v hz'))
    have hβgrowth : (fun z : V ↦ (β z : ℂ)).HasTemperateGrowth :=
      (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hβ)
    have hβu : SchwartzMap.smulLeftCLM (H r) (fun z ↦ (β z : ℂ)) u₀ = u₀ := by
      ext z : 1
      rw [SchwartzMap.smulLeftCLM_apply_apply hβgrowth]
      by_cases hz : z ∈ tsupport L.input.cutoff
      · rw [hβK z (Or.inl hz), Complex.ofReal_one, one_smul]
      · rw [hu₀zero z hz, smul_zero]
    have hP₀apply (z : V) : P₀ u₀ z = β z • L.operator u₀ z := by
      rw [show P₀ u₀ z = amplitudeApply (cutoffAmplitude β β L.symbol) u₀ z from
        amplitudeOperator_apply m _ _ _ u₀ z]
      rw [amplitudeApply_cutoffAmplitude m L.symbol L.isSymbol β β hβ hβ hcβ hcβ,
        hβu, ← L.operator_apply]
    have hb (z : V) : b z = ρ z • GF z (v₀ z) := by
      rw [show b z = B z (v₀ z) from matrixMultiplierCLM_apply B hB hcB v₀ z]
      change β z • (ρ z • GF z (v₀ z)) = _
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · rw [hv₀zero z hz, map_zero, smul_zero, smul_zero]
    have hWapply (z : V) :
        W v₀ z = β z • ((ρ z)⁻¹ • (GE z).inverse (Q b z)) :=
      matrixMultiplierCLM_apply A hA hcA (Q b) z
    -- Move each global pairing into this single original chart using its prescribed density.
    have hleftChart : k.sectionPairing μ
        (L.output.extend L.chart_mem_atlas (L.operator u₀)) v =
        ∫ z, inner ℂ (L.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      let A := L.output
      let G := GF
      let hc := L.chart_mem_atlas
      let u := v
      let v := L.operator u₀
      let h := k
      have hG : ∀ z ∈ tsupport A.cutoff, ∀ a b : H q,
          h.pairing (L.chart.symm z) (A.frame.symmL ℂ (L.chart.symm z) a)
            (A.frame.symmL ℂ (L.chart.symm z) b) = inner ℂ a (G z b) := by
        intro z hz a b
        exact (hGFpair z (L.output.support_subset hz)).2 a b
      rw [SmoothHermitianMetric.sectionPairing]
      rw [hchartIntegral L.chart μ ρ hρ.continuousOn
        (fun z hz ↦ (hρpos z hz).le) hρmap _
        (h.contMDiff_pairing (A.extend hc v) u).continuous (by
          intro x hx
          by_contra hxc
          apply hx
          change h.pairing x (A.extendedFunction v x) (u.val x) = 0
          rw [show A.extendedFunction v x = 0 by
            simp [BundleChartCutoff.extendedFunction, hxc]]
          let : InnerProductSpace.Core ℂ (F x) := h.toCore x
          exact InnerProductSpace.Core.inner_zero_left _)]
      calc
        _ = ∫ z in L.chart.target, inner ℂ (v z) (ρ z • G z (A.localize hc u z)) := by
          apply setIntegral_congr_fun L.chart.open_target.measurableSet
          intro z hz
          change ρ z • h.pairing (L.chart.symm z) (A.extendedFunction v (L.chart.symm z))
            (u.val (L.chart.symm z)) = inner ℂ (v z) (ρ z • G z (A.localizedFunction u z))
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            L.chart.map_target hz, ite_true, L.chart.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hu : u.val (L.chart.symm z) =
                A.frame.symmL ℂ (L.chart.symm z) (sectionInChart F L.chart A.frame u.val z) := by
              symm
              rw [sectionInChart, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
                A.frame.symmL_continuousLinearMapAt he]
            have hsmul : h.pairing (L.chart.symm z)
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z))
                (u.val (L.chart.symm z)) =
                  (A.cutoff z : ℂ) * h.pairing (L.chart.symm z)
                    (A.frame.symmL ℂ (L.chart.symm z) (v z)) (u.val (L.chart.symm z)) := by
              let : InnerProductSpace.Core ℂ (F (L.chart.symm z)) := h.toCore (L.chart.symm z)
              change (h.toCore (L.chart.symm z)).inner
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z))
                (u.val (L.chart.symm z)) =
                  (A.cutoff z : ℂ) * (h.toCore (L.chart.symm z)).inner
                    (A.frame.symmL ℂ (L.chart.symm z) (v z)) (u.val (L.chart.symm z))
              rw [InnerProductSpace.Core.inner_smul_left, Complex.conj_ofReal]
            rw [hsmul, hu, hG z hb, map_smul]
            simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
              smul_eq_mul]
          · rw [image_eq_zero_of_notMem_tsupport hb]
            simp only [Complex.ofReal_zero, zero_smul, map_zero]
            have hzero : h.pairing (L.chart.symm z) 0 (u.val (L.chart.symm z)) = 0 := by
              let : InnerProductSpace.Core ℂ (F (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_zero_left _
            rw [hzero, smul_zero, smul_zero, inner_zero_right]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change inner ℂ (v z) (ρ z • G z (A.localizedFunction u z)) = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hrightChart : h.sectionPairing μ u
        (L.input.extend L.chart_mem_atlas (W v₀)) =
        ∫ z, inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) := by
      let A := L.input
      let G := GE
      let hc := L.chart_mem_atlas
      let v := W v₀
      have hG : ∀ z ∈ tsupport A.cutoff, ∀ a b : H r,
          h.pairing (L.chart.symm z) (A.frame.symmL ℂ (L.chart.symm z) a)
            (A.frame.symmL ℂ (L.chart.symm z) b) = inner ℂ a (G z b) := by
        intro z hz a b
        exact (hGEpair z (L.input.support_subset hz)).2 a b
      rw [SmoothHermitianMetric.sectionPairing]
      rw [hchartIntegral L.chart μ ρ hρ.continuousOn
        (fun z hz ↦ (hρpos z hz).le) hρmap _
        (h.contMDiff_pairing u (A.extend hc v)).continuous (by
          intro x hx
          by_contra hxc
          apply hx
          change h.pairing x (u.val x) (A.extendedFunction v x) = 0
          rw [show A.extendedFunction v x = 0 by
            simp [BundleChartCutoff.extendedFunction, hxc]]
          let : InnerProductSpace.Core ℂ (E x) := h.toCore x
          exact InnerProductSpace.Core.inner_zero_right _)]
      calc
        _ = ∫ z in L.chart.target, inner ℂ (A.localize hc u z) (ρ z • G z (v z)) := by
          apply setIntegral_congr_fun L.chart.open_target.measurableSet
          intro z hz
          change ρ z • h.pairing (L.chart.symm z) (u.val (L.chart.symm z))
            (A.extendedFunction v (L.chart.symm z)) =
              inner ℂ (A.localizedFunction u z) (ρ z • G z (v z))
          simp only [BundleChartCutoff.extendedFunction, BundleChartCutoff.localizedFunction,
            L.chart.map_target hz, ite_true, L.chart.right_inv hz, hz]
          by_cases hb : z ∈ tsupport A.cutoff
          · have he := (A.support_subset hb).2
            have hu : u.val (L.chart.symm z) =
                A.frame.symmL ℂ (L.chart.symm z) (sectionInChart E L.chart A.frame u.val z) := by
              symm
              rw [sectionInChart, ← A.frame.continuousLinearMapAt_apply_of_mem ℂ he,
                A.frame.symmL_continuousLinearMapAt he]
            have hsmul : h.pairing (L.chart.symm z) (u.val (L.chart.symm z))
                ((A.cutoff z : ℂ) • A.frame.symmL ℂ (L.chart.symm z) (v z)) =
                  (A.cutoff z : ℂ) * h.pairing (L.chart.symm z)
                    (u.val (L.chart.symm z)) (A.frame.symmL ℂ (L.chart.symm z) (v z)) := by
              let : InnerProductSpace.Core ℂ (E (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_smul_right _ _
            rw [hsmul, hu, hG z hb]
            simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
              inner_smul_right, Complex.conj_ofReal, smul_eq_mul]
          · rw [image_eq_zero_of_notMem_tsupport hb]
            simp only [Complex.ofReal_zero, zero_smul, inner_zero_left]
            have hzero : h.pairing (L.chart.symm z) (u.val (L.chart.symm z)) 0 = 0 := by
              let : InnerProductSpace.Core ℂ (E (L.chart.symm z)) := h.toCore (L.chart.symm z)
              exact InnerProductSpace.Core.inner_zero_right _
            rw [hzero, smul_zero]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (by
          intro z hz
          change inner ℂ (A.localizedFunction u z) (ρ z • G z (v z)) = 0
          simp [BundleChartCutoff.localizedFunction, hz])
    have hleft (z : V) : inner ℂ (P₀ u₀ z) (b z) =
        inner ℂ (L.operator u₀ z) (ρ z • GF z (v₀ z)) := by
      rw [hP₀apply, hb]
      by_cases hz : z ∈ tsupport L.output.cutoff
      · rw [hβK z (Or.inr hz), one_smul]
      · simp [hv₀zero z hz]
    have hright (z : V) : inner ℂ (u₀ z) (ρ z • GE z (W v₀ z)) =
        inner ℂ (u₀ z) (Q b z) := by
      by_cases hz : z ∈ tsupport L.input.cutoff
      · have hzE := L.input.support_subset hz
        obtain ⟨J, hJ⟩ := (hGEpair z hzE).1
        have hGI (a : H r) : GE z ((GE z).inverse a) = a := by
          rw [← hJ, ContinuousLinearMap.inverse_equiv]
          exact J.apply_symm_apply a
        rw [hWapply, hβK z (Or.inl hz), one_smul, ContinuousLinearMap.map_smul_of_tower, hGI,
          smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos z hzE.1)), one_smul]
      · simp [hu₀zero z hz]
    change k.sectionPairing μ (L.output.extend L.chart_mem_atlas (L.operator u₀)) v =
      h.sectionPairing μ u (L.input.extend L.chart_mem_atlas (W v₀))
    rw [hleftChart, hrightChart]
    calc
      _ = ∫ z, inner ℂ (P₀ u₀ z) (b z) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hleft z).symm))
      _ = ∫ z, inner ℂ (u₀ z) (Q b z) := hQpair u₀ b
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ (hright z).symm))
  -- The remainder is adjointed between its two original fibers, with explicit forms.
  have hkernelRaw (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
      ∃ J : SmoothKernel (n := n) (r := q) (q := r) F E,
        (∀ (x y : M) (u : E x) (v : F y),
          k.pairing y (K.toFun y x u) v = h.pairing x u (J.toFun x y v)) ∧
        ∀ (u : smoothSections (n := n) (r := r) E)
          (v : smoothSections (n := n) (r := q) F),
          k.sectionPairing μ (K.toLinearMap μ u) v =
            h.sectionPairing μ u (J.toLinearMap μ v) := by
    classical
    let (x : M) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let (x : M) : FiniteDimensional ℂ (F x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
    let (x : M) : CompleteSpace (E x) := FiniteDimensional.complete ℂ (E x)
    let (x : M) : CompleteSpace (F x) := FiniteDimensional.complete ℂ (F x)
    -- Compose metric duality with dual precomposition, using the original fiber norms.
    let A₀ (x y : M) : F y →ₗ[ℂ] E x := {
      toFun := fun v ↦ (h.dualEquiv x).symm ((k.dual y v).comp (K.toFun y x))
      map_add' := by
        intro v w
        rw [k.dual_add, ContinuousLinearMap.add_comp, map_add]
      map_smul' := by
        intro c v
        rw [k.dual_smul, ContinuousLinearMap.smul_comp, map_smulₛₗ]
        simp }
    let A (x y : M) : F y →L[ℂ] E x := (A₀ x y).toContinuousLinearMap
    have hpair (x y : M) (u : E x) (v : F y) :
        h.pairing x u (A x y v) = k.pairing y (K.toFun y x u) v := by
      have hs : h.pairing x (A x y v) u = k.pairing y v (K.toFun y x u) :=
        (h.pairing_dualEquiv_symm x ((k.dual y v).comp (K.toFun y x)) u).trans
          (k.dual_apply y v (K.toFun y x u))
      have hc := congrArg (starRingEnd ℂ) hs
      simpa only [SmoothHermitianMetric.pairing, (h.toCore x).conj_inner_symm,
        (k.toCore y).conj_inner_symm] using hc
    have hA : IsSmoothKernel (n := n) (r := q) (q := r) F E A := by
      intro f e hf he
      let toOpE : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ]
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
      let matrixOpE : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        LinearMap.toContinuousLinearMap (toOpE.restrictScalars ℝ)
      let GE (x : M) := matrixOpE (h.gramMatrix e x)
      have gramSmoothE : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          GE e.baseSet := by
        apply matrixOpE.contDiff.contMDiff.comp_contMDiffOn
        apply contMDiffOn_pi_space.mpr
        intro i
        apply contMDiffOn_pi_space.mpr
        intro j
        exact h.contMDiffOn_gram e i j
      have gramInvertibleE (x : M) (hx : x ∈ e.baseSet) : (GE x).IsInvertible := by
        have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr
          (h.isUnit_det_gramMatrix e x hx)
        let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
          ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
            Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
        let Q := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
        refine ⟨Q.trans (L.trans Q.symm), ?_⟩
        ext v i
        rfl
      have gramPairingE (x : M) (hx : x ∈ e.baseSet)
          (u v : EuclideanSpace ℂ (Fin r)) :
          inner ℂ u (GE x v) = h.pairing x (e.symmL ℂ x u) (e.symmL ℂ x v) := by
        rw [h.pairing_eq_gramMatrix e x hx]
        have hcoord (w : EuclideanSpace ℂ (Fin r)) :
            (e ⟨x, e.symmL ℂ x w⟩).2 = w := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact e.continuousLinearMapAt_symmL hx w
        rw [hcoord, hcoord]
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        change (∑ i, (∑ j, h.gramMatrix e x i j * v j) * star (u i)) = _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [starRingEnd_apply]
        ring
      let toOpF : Matrix (Fin q) (Fin q) ℂ →ₗ[ℂ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
        LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
      let matrixOpF : Matrix (Fin q) (Fin q) ℂ →L[ℝ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
        LinearMap.toContinuousLinearMap (toOpF.restrictScalars ℝ)
      let GF (x : M) := matrixOpF (k.gramMatrix f x)
      have gramSmoothF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          GF f.baseSet := by
        apply matrixOpF.contDiff.contMDiff.comp_contMDiffOn
        apply contMDiffOn_pi_space.mpr
        intro i
        apply contMDiffOn_pi_space.mpr
        intro j
        exact k.contMDiffOn_gram f i j
      have gramPairingF (x : M) (hx : x ∈ f.baseSet)
          (u v : EuclideanSpace ℂ (Fin q)) :
          inner ℂ u (GF x v) = k.pairing x (f.symmL ℂ x u) (f.symmL ℂ x v) := by
        rw [k.pairing_eq_gramMatrix f x hx]
        have hcoord (w : EuclideanSpace ℂ (Fin q)) :
            (f ⟨x, f.symmL ℂ x w⟩).2 = w := by
          rw [← f.continuousLinearMapAt_apply_of_mem ℂ hx]
          exact f.continuousLinearMapAt_symmL hx w
        rw [hcoord, hcoord]
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        change (∑ i, (∑ j, k.gramMatrix f x i j * v j) * star (u i)) = _
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [starRingEnd_apply]
        ring
      have hGEi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          (fun x ↦ (GE x).inverse) e.baseSet := by
        intro x hx
        exact ((gramInvertibleE x hx).contDiffAt_map_inverse (n := ∞)).restrict_scalars ℝ
          |>.comp_contMDiffWithinAt (gramSmoothE x hx)
      let adj : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℝ]
          (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
        { toFun := fun c ↦ c.adjoint
          map_add' := fun c d ↦ map_add _ c d
          map_smul' := by
            intro a c
            simp only [RingHom.id_apply, ← Complex.coe_smul, map_smulₛₗ,
              Complex.conj_ofReal]
          cont := ContinuousLinearMap.adjoint.continuous }
      -- The inverse source Gram is at x; the original target Gram is at y.
      have hleft := hGEi.comp (contMDiffOn_fst (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.1)
      have hright := gramSmoothF.comp (contMDiffOn_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ hz.2)
      have hswap := (K.isSmooth e f).comp (contMDiffOn_snd.prodMk contMDiffOn_fst)
        (s := e.baseSet ×ˢ f.baseSet) (fun z hz ↦ ⟨hz.2, hz.1⟩)
      have hmiddle := adj.contMDiff.comp_contMDiffOn hswap
      have hcompose {a b c : ℕ} : ContDiff ℝ ∞ (fun z :
          (EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)) ×
            (EuclideanSpace ℂ (Fin a) →L[ℂ] EuclideanSpace ℂ (Fin b)) ↦ z.1.comp z.2) :=
        (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
      have hweighted := hcompose.contMDiff.comp_contMDiffOn
        (hleft.prodMk_space (hcompose.contMDiff.comp_contMDiffOn
          (hmiddle.prodMk_space hright)))
      apply hweighted.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro v
      have heq : GE z.1 (kernelInFrames F E A f e z v) =
          (kernelInFrames E F K.toFun e f (z.2, z.1)).adjoint (GF z.2 v) := by
        apply ext_inner_left ℂ
        intro u
        rw [ContinuousLinearMap.adjoint_inner_right, gramPairingE _ hz.1,
          gramPairingF _ hz.2]
        change h.pairing z.1 (e.symmL ℂ z.1 u)
          (e.symmL ℂ z.1 (e.continuousLinearMapAt ℂ z.1
            (A z.1 z.2 (f.symmL ℂ z.2 v)))) =
          k.pairing z.2 (f.symmL ℂ z.2 (f.continuousLinearMapAt ℂ z.2
            (K.toFun z.2 z.1 (e.symmL ℂ z.1 u)))) (f.symmL ℂ z.2 v)
        rw [e.symmL_continuousLinearMapAt hz.1, hpair,
          f.symmL_continuousLinearMapAt hz.2]
      exact ((gramInvertibleE z.1 hz.1).inverse_apply_self _).symm.trans
        (congrArg (GE z.1).inverse heq)
    let J : SmoothKernel (n := n) (r := q) (q := r) F E := ⟨A, hA⟩
    refine ⟨J, ?_, ?_⟩
    · intro x y u v
      exact (hpair x y u v).symm
    · intro u v
      -- The proven bilinear transpose formula supplies Fubini for the actual kernels.
      let α := dualSectionsEquiv F (k.dualSectionsEquiv v)
      have hrow (x : M) :
          h.pairing x (u.val x) ((J.toLinearMap μ v).val x) =
            conj ((K.transpose.toLinearMap μ α).val x (u.val x)) := by
        have hJ := J.dual_apply μ v x (h.dual x (u.val x))
        have hT := K.transpose.dual_apply μ α x (ContinuousLinearMap.apply ℂ ℂ (u.val x))
        change h.dual x (u.val x) ((J.toLinearMap μ v).val x) =
          ∫ y, h.dual x (u.val x) (A x y (v.val y)) ∂μ at hJ
        simp only [h.dual_apply] at hJ
        change (K.transpose.toLinearMap μ α).val x (u.val x) =
          ∫ y, α.val y (K.toFun y x (u.val x)) ∂μ at hT
        rw [hJ, hT, ← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        change h.pairing x (u.val x) (A x y (v.val y)) =
          conj ((k.dualSectionsEquiv v).val y (K.toFun y x (u.val x)))
        rw [hpair, k.dualSectionsEquiv_apply]
        exact ((k.toCore y).conj_inner_symm _ _).symm
      have ht := K.isFormalTranspose_toLinearMap (μ := μ) α u
      change (∫ x, (K.transpose.toLinearMap μ α).val x (u.val x) ∂μ) =
        ∫ x, (k.dualSectionsEquiv v).val x ((K.toLinearMap μ u).val x) ∂μ at ht
      simp only [k.dualSectionsEquiv_apply] at ht
      change (∫ x, k.pairing x ((K.toLinearMap μ u).val x) (v.val x) ∂μ) =
        ∫ x, h.pairing x (u.val x) ((J.toLinearMap μ v).val x) ∂μ
      simp_rw [hrow]
      rw [integral_conj, ht, ← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((k.toCore x).conj_inner_symm _ _).symm
  have hkernel (K : SmoothKernel (n := n) (r := r) (q := q) E F) :
      ∃ K' : SmoothKernel (n := n) (r := q) (q := r) F E,
        IsMetricFormalAdjoint h k μ (K.toLinearMap μ) (K'.toLinearMap μ) := by
    obtain ⟨J, _, hJ⟩ := hkernelRaw K
    exact ⟨J, hJ⟩
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  choose T hT horder using fun j : Fin N ↦ hpiece (L j)
  obtain ⟨K', hK'⟩ := hkernel K
  have hsum (s : Finset (Fin N)) :
      IsMetricFormalAdjoint h k μ
          ((∑ j ∈ s, (L j).toLinearMap) + K.toLinearMap μ)
          ((∑ j ∈ s, T j) + K'.toLinearMap μ) ∧
        IsPseudodifferentialOperator F E μ m ((∑ j ∈ s, T j) + K'.toLinearMap μ) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty, zero_add] using
        And.intro hK' (IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨K', rfl⟩)
    | @insert j s hjs ih =>
      simpa only [Finset.sum_insert hjs, add_assoc] using
        And.intro ((hT j).add ih.1)
          (IsPseudodifferentialOperator.add m _ _ (horder j) ih.2)
  let Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m :=
    ⟨(∑ j, T j) + K'.toLinearMap μ, (hsum Finset.univ).2⟩
  have hdecomp : P.toLinearMap = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    rw [hK]
    abel
  have hQ : IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap := by
    rw [hdecomp]
    exact (hsum Finset.univ).1
  refine ⟨Q, hQ, ?_⟩
  -- Positive definiteness determines the full section map, hence the original PDO structure.
  intro R hR
  have hmaps : R.toLinearMap = Q.toLinearMap :=
    hR.unique hQ
  have hext (R S : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m)
      (heq : R.toLinearMap = S.toLinearMap) : R = S := by
    cases R
    cases S
    cases heq
    rfl
  exact hext R Q hmaps

/-- The actual same-order PDO adjoint for the specified two metrics. -/
def metricFormalAdjoint :
    PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m :=
  Classical.choose (P.existsUnique_metricFormalAdjoint h k).exists

/-- The selected PDO satisfies its defining integral identity. -/
theorem isMetricFormalAdjoint_metricFormalAdjoint :
    IsMetricFormalAdjoint h k μ P.toLinearMap (P.metricFormalAdjoint h k).toLinearMap := by
  -- The selected witness keeps exactly the given metrics, density and section map.
  exact (P.existsUnique_metricFormalAdjoint h k).exists.choose_spec

/-- A PDO with the same integral identity equals the chosen adjoint. -/
theorem metricFormalAdjoint_eq
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ m)
    (hQ : IsMetricFormalAdjoint h k μ P.toLinearMap Q.toLinearMap) :
    P.metricFormalAdjoint h k = Q := by
  -- Both same-order PDOs satisfy the same unique integral characterization.
  exact (P.existsUnique_metricFormalAdjoint h k).unique
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k) hQ

/-- Double adjunction preserves the entire PDO, including the smoothing remainder. -/
theorem metricFormalAdjoint_metricFormalAdjoint :
    (P.metricFormalAdjoint h k).metricFormalAdjoint k h = P := by
  -- Hermitian symmetry reverses the original relation with the two specified metrics.
  exact (P.metricFormalAdjoint h k).metricFormalAdjoint_eq k h P
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k).symm

/-- Both metric changes appear in the exact full section-map formula. -/
theorem metricFormalAdjoint_change (h' : SmoothHermitianMetric (n := n) (r := r) E)
    (k' : SmoothHermitianMetric (n := n) (r := q) F) :
    (P.metricFormalAdjoint h' k').toLinearMap =
      (h'.changeSections h).toLinearMap.comp
        ((P.metricFormalAdjoint h k).toLinearMap.comp (k.changeSections k').toLinearMap) := by
  -- Apply the general metric-change law to the actual old adjoint map.
  exact (P.isMetricFormalAdjoint_metricFormalAdjoint h' k').unique
    ((P.isMetricFormalAdjoint_metricFormalAdjoint h k).change h' k')

/-- The bilinear transpose is intertwined by the actual conjugate-linear metric duals. -/
theorem formalTranspose_metric (v : smoothSections (n := n) (r := q) F) :
    P.formalTranspose.toLinearMap (AtiyahSinger.dualSectionsEquiv F (k.dualSectionsEquiv v)) =
      AtiyahSinger.dualSectionsEquiv E
        (h.dualSectionsEquiv ((P.metricFormalAdjoint h k).toLinearMap v)) := by
  -- The two conjugate-linear metric identifications give a complex-linear transpose.
  let e := h.dualSectionsEquiv.trans (AtiyahSinger.dualSectionsEquiv E)
  let f := k.dualSectionsEquiv.trans (AtiyahSinger.dualSectionsEquiv F)
  let T : smoothSections (n := n) (r := q) (DualBundle F) →ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E) :=
    e.toLinearMap.comp ((P.metricFormalAdjoint h k).toLinearMap.comp f.symm.toLinearMap)
  have hT : IsFormalTranspose μ P.toLinearMap T := by
    intro α u
    obtain ⟨w, rfl⟩ := f.surjective α
    change smoothDualSectionPairing E μ
      ((AtiyahSinger.dualSectionsEquiv E).symm (T (f w))) u =
      smoothDualSectionPairing F μ
        ((AtiyahSinger.dualSectionsEquiv F).symm (f w)) (P.toLinearMap u)
    have hTw : T (f w) = e ((P.metricFormalAdjoint h k).toLinearMap w) := by simp [T]
    rw [hTw]
    change smoothDualSectionPairing E μ
      (h.dualSectionsEquiv ((P.metricFormalAdjoint h k).toLinearMap w)) u =
      smoothDualSectionPairing F μ (k.dualSectionsEquiv w) (P.toLinearMap u)
    rw [h.dualSectionPairing_dualSectionsEquiv, k.dualSectionPairing_dualSectionsEquiv]
    exact (P.isMetricFormalAdjoint_metricFormalAdjoint h k).symm w u
  -- Separation by smooth primal tests identifies the exact global transpose.
  have hmaps : P.formalTranspose.toLinearMap = T :=
    IsFormalTranspose.unique P.toLinearMap _ _ P.isFormalTranspose_formalTransposeLinearMap hT
  change P.formalTranspose.toLinearMap (f v) = e ((P.metricFormalAdjoint h k).toLinearMap v)
  rw [hmaps]
  simp [T]

/-- The principal quotient of the actual PDO adjoint is the fiber adjoint class. -/
theorem principalSymbol_metricFormalAdjoint :
    (P.metricFormalAdjoint h k).principalSymbol = h.principalSymbolAdjoint k P.principalSymbol := by
  /- Retain each weighted local principal term, then assemble the actual adjoint
  section maps. The density cancels before passage to the quotient; the same
  specified metrics supply the source and target Gram factors throughout. -/
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  let A (j : Fin N) : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m :=
    ⟨(L j).toLinearMap, (L j).isPseudodifferentialOperator m⟩
  let Q (j : Fin N) : pseudodifferentialSpace (n := n) (r := q) (q := r) F E μ m :=
    ((A j).metricFormalAdjoint h k).toSpace
  have hT (j : Fin N) : IsMetricFormalAdjoint h k μ (L j).toLinearMap (Q j).val :=
    (A j).isMetricFormalAdjoint_metricFormalAdjoint h k
  -- The actual adjoint of the smooth remainder is itself represented by a smooth kernel.
  let K₀ : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m :=
    ⟨K.toLinearMap μ, IsSmoothingOperator.isPseudodifferentialOperator m _ ⟨K, rfl⟩⟩
  let R := (K₀.metricFormalAdjoint h k).toSpace
  have hR : IsMetricFormalAdjoint h k μ (K.toLinearMap μ) R.val :=
    K₀.isMetricFormalAdjoint_metricFormalAdjoint h k
  have hRs : IsSmoothingOperator μ R.val := hR.isSmoothingOperator h k ⟨K, rfl⟩
  let S := pseudodifferentialOperatorOfSpace ((∑ j, Q j) + R)
  have hsum (s : Finset (Fin N)) :
      IsMetricFormalAdjoint h k μ ((∑ j ∈ s, (L j).toLinearMap) + K.toLinearMap μ)
        ((∑ j ∈ s, (Q j).val) + R.val) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, zero_add] using hR
    | @insert j s hj ih =>
      simpa only [Finset.sum_insert hj, add_assoc] using (hT j).add ih
  have hrepr : P.toLinearMap = (∑ j, (L j).toLinearMap) + K.toLinearMap μ := by
    rw [hK]
    abel
  have hS : IsMetricFormalAdjoint h k μ P.toLinearMap S.toLinearMap := by
    rw [hrepr]
    simpa only [S, pseudodifferentialOperatorOfSpace, Submodule.coe_add,
      Submodule.coe_sum] using hsum Finset.univ
  have heq : (P.metricFormalAdjoint h k).toLinearMap = S.toLinearMap :=
    (P.isMetricFormalAdjoint_metricFormalAdjoint h k).unique hS
  rw [(P.metricFormalAdjoint h k).principalSymbol_eq_of_toLinearMap_eq μ S heq]
  -- The local representation and its principal comparison concern each same chosen map.
  let σ := principalSymbolLinearMap (n := n) (r := q) (q := r) F E μ m
  have hpiece (j : Fin N) : σ (Q j) =
      h.principalSymbolAdjoint k (globalPrincipalSymbolClass E F m (L j).globalSymbol) := by
    obtain ⟨N', L', hrem, hclass⟩ :=
      (L j).exists_representation_metricFormalAdjoint h k (Q j).val (hT j)
    exact ((pseudodifferentialOperatorOfSpace (Q j)).principalSymbol_eq_of_representation
      N' L' hrem).trans hclass
  have hkernel : σ R = 0 :=
    (pseudodifferentialOperatorOfSpace R).principalSymbol_eq_zero_of_isSmoothingOperator hRs
  change σ ((∑ j, Q j) + R) = _
  rw [map_add, map_sum, hkernel, add_zero]
  simp_rw [hpiece]
  rw [P.principalSymbol_eq_of_representation N L ⟨K, hK⟩, map_sum]
  have hfinite (s : Finset (Fin N)) :
      h.principalSymbolAdjoint k
          (∑ j ∈ s, globalPrincipalSymbolClass E F m (L j).globalSymbol) =
        ∑ j ∈ s, h.principalSymbolAdjoint k
          (globalPrincipalSymbolClass E F m (L j).globalSymbol) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, h.principalSymbolAdjoint_zero]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, h.principalSymbolAdjoint_add, ih]
  exact (hfinite Finset.univ).symm

/-- Quantitative full-symbol ellipticity is preserved by metric adjunction. -/
theorem isElliptic_metricFormalAdjoint_iff :
    (P.metricFormalAdjoint h k).IsElliptic ↔ P.IsElliptic := by
  -- One elliptic representative gives the explicit adjoint representative and its inverse bound.
  have forward {m : ℝ}
      (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
      (hP : P.IsElliptic) : (P.metricFormalAdjoint h k).IsElliptic := by
    obtain ⟨a, hPa, ha⟩ := hP
    refine ⟨h.symbolSpaceAdjoint k a, ?_, ?_⟩
    · rw [P.principalSymbol_metricFormalAdjoint, hPa, h.principalSymbolAdjoint_class]
    · exact h.isEllipticFullGlobalSymbol_symbolAdjoint k a.val ha
  constructor
  · intro hP
    obtain ⟨a, ha, he⟩ := hP
    have hclass : P.principalSymbol =
        globalPrincipalSymbolClass E F m (k.symbolSpaceAdjoint h a) := by
      rw [← P.metricFormalAdjoint_metricFormalAdjoint h k,
        principalSymbol_metricFormalAdjoint, ha, k.principalSymbolAdjoint_class]
    exact ⟨k.symbolSpaceAdjoint h a, hclass,
      k.isEllipticFullGlobalSymbol_symbolAdjoint h a.val he⟩
  · exact forward P

/-- The smooth kernel is the annihilator of the original smooth range. -/
theorem metricFormalAdjoint_apply_eq_zero_iff (v : smoothSections (n := n) (r := q) F) :
    (P.metricFormalAdjoint h k).toLinearMap v = 0 ↔
      ∀ u, k.sectionPairing μ (P.toLinearMap u) v = 0 := by
  constructor
  · intro hz u
    rw [P.isMetricFormalAdjoint_metricFormalAdjoint h k u v, hz]
    unfold SmoothHermitianMetric.sectionPairing
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    let : InnerProductSpace.Core ℂ (E x) := h.toCore x
    exact InnerProductSpace.Core.inner_zero_right _
  · -- Test orthogonality with the actual adjoint output in the original positive pairing.
    intro hz
    apply (h.sectionPairing_self_eq_zero_iff μ _).mp
    rw [← P.isMetricFormalAdjoint_metricFormalAdjoint h k]
    exact hz _

/-- Smooth-kernel operators remain smoothing under explicit metric adjunction. -/
theorem isSmoothingOperator_metricFormalAdjoint_iff :
    IsSmoothingOperator μ (P.metricFormalAdjoint h k).toLinearMap ↔
      IsSmoothingOperator μ P.toLinearMap := by
  /- A smooth kernel K(x,y) becomes its metric adjoint K(y,x)†. In local
  frames smooth positive Gram matrices and their inverses preserve smoothness.
  This proves one implication; double adjunction proves the other. -/
  have hP := P.isMetricFormalAdjoint_metricFormalAdjoint h k
  exact ⟨fun hQ ↦ hP.symm.isSmoothingOperator k h hQ,
    fun hQ ↦ hP.isSmoothingOperator h k hQ⟩

/-- Adjunction reverses a two-sided parametrix with the correct bundle directions. -/
theorem isParametrix_metricFormalAdjoint
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
    (hQ : IsParametrix μ P.toLinearMap Q.toLinearMap) :
    IsParametrix μ (P.metricFormalAdjoint h k).toLinearMap
      (Q.metricFormalAdjoint k h).toLinearMap := by
  /- Adjoint both parametrix identities. Composition reverses, identity
  is self-adjoint, and each smooth kernel remains smoothing under the swapped
  weighted adjoint. The two original error directions exchange roles. -/
  have hP' := P.isMetricFormalAdjoint_metricFormalAdjoint h k
  have hQ' := Q.isMetricFormalAdjoint_metricFormalAdjoint k h
  -- Reverse each actual composite, retaining the same middle metric.
  have hPQ := IsMetricFormalAdjoint.comp k h μ k hQ' hP'
  have hQP := IsMetricFormalAdjoint.comp h k μ h hP' hQ'
  have hnegE := (isMetricFormalAdjoint_id h μ).smul (-1)
  have hnegF := (isMetricFormalAdjoint_id k μ).smul (-1)
  have herrorF : IsMetricFormalAdjoint k k μ
      (P.toLinearMap.comp Q.toLinearMap - LinearMap.id)
      ((Q.metricFormalAdjoint k h).toLinearMap.comp
        (P.metricFormalAdjoint h k).toLinearMap - LinearMap.id) := by
    simpa only [map_neg, map_one, neg_one_smul, sub_eq_add_neg] using hPQ.add hnegF
  have herrorE : IsMetricFormalAdjoint h h μ
      (Q.toLinearMap.comp P.toLinearMap - LinearMap.id)
      ((P.metricFormalAdjoint h k).toLinearMap.comp
        (Q.metricFormalAdjoint k h).toLinearMap - LinearMap.id) := by
    simpa only [map_neg, map_one, neg_one_smul, sub_eq_add_neg] using hQP.add hnegE
  -- The original smoothing witnesses transfer to the reversed residuals in the required order.
  exact ⟨herrorF.isSmoothingOperator k k hQ.2, herrorE.isSmoothingOperator h h hQ.1⟩

/-- Adjunction sends the zero PDO to zero. -/
theorem metricFormalAdjoint_toLinearMap_eq_zero (hP : P.toLinearMap = 0) :
    (P.metricFormalAdjoint h k).toLinearMap = 0 := by
  -- The zero map has the same adjoint relation once the original map is zero.
  have hQ := P.isMetricFormalAdjoint_metricFormalAdjoint h k
  rw [hP] at hQ
  exact hQ.unique (isMetricFormalAdjoint_zero h k μ)

/-- Adjunction preserves addition of PDOs of a fixed order. -/
theorem metricFormalAdjoint_add
    (R : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    (P.add R).metricFormalAdjoint h k =
      (P.metricFormalAdjoint h k).add (R.metricFormalAdjoint h k) := by
  -- Add the same-density identities; the existing PDO sum keeps the actual summed map.
  apply (P.add R).metricFormalAdjoint_eq
  exact (P.isMetricFormalAdjoint_metricFormalAdjoint h k).add
    (R.isMetricFormalAdjoint_metricFormalAdjoint h k)

/-- Adjunction conjugates the complex scalar multiplying a PDO. -/
theorem metricFormalAdjoint_smul (c : ℂ) :
    (P.smul c).metricFormalAdjoint h k = (P.metricFormalAdjoint h k).smul (conj c) := by
  -- Conjugation of the scalar is forced by the first slot of the target metric.
  apply (P.smul c).metricFormalAdjoint_eq
  exact (P.isMetricFormalAdjoint_metricFormalAdjoint h k).smul c

end PseudodifferentialOperator

/-- Differential and PDO adjoints agree on the same original section map. -/
theorem DifferentialOperator.metricFormalAdjoint_eq_of_toLinearMap_eq {d : ℕ}
    (D : DifferentialOperator (n := n) (r := r) (q := q) E F d)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ (d : ℝ))
    (hP : P.toLinearMap = D.toLinearMap) :
    (P.metricFormalAdjoint h k).toLinearMap = (D.metricFormalAdjoint (μ := μ) h k).toLinearMap := by
  -- The original section-map equality makes both adjoints satisfy the same characterization.
  have hQ := P.isMetricFormalAdjoint_metricFormalAdjoint h k
  rw [hP] at hQ
  exact hQ.unique (D.isMetricFormalAdjoint_metricFormalAdjoint h k)

end AtiyahSinger
