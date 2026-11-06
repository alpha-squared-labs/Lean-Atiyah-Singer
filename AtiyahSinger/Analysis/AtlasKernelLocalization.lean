/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFormalAdjoint
public import AtiyahSinger.Analysis.AtlasFullSymbolEllipticity
public import AtiyahSinger.Analysis.AtlasPieceKernel
public import AtiyahSinger.Analysis.AtlasRelativeQuantization

/-!
# Relative elliptic representatives with genuine two-variable kernel control

Public module ID: M0257.

UL03, SG III.13.4, pp.248--249, and ASI section 8, (8.1), p.523.
The given exterior identity is the original specified bundle identification b.
It need not extend to a global bundle isomorphism. A smooth global multiplier
c agrees with b outside a larger compact region and may degenerate inside it.
The actual representative P is c plus finitely many original atlas Fourier
order-zero pieces; its principal quotient is the regularized class of the
given degree-zero homogeneous symbol a.

Both P and its actual formal adjoint Q have genuine local distribution kernels
for independent input/output charts, with their original metric/density test
actions. Only the residual kernels P-M_c and Q-M_(c-adjoint) have compact
support in L×L. The full multiplier delta kernel generally has a noncompact
diagonal. The adjoint is defined by the same hE, hF and measure, and its
exterior multiplier is b-adjoint, which equals b-inverse only when b is unitary.

All dimensions, locally varying finite ranks and noncompact bases are retained.
The two-environment excision and index comparisons are downstream P02, not
additional premises or conclusions of this localization assertion. The
construction uses actual continuous Schwartz kernels and the same compact
residual support in the original metric and density conventions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option backward.isDefEq.respectTransparency false in
/-- UL03: the original exterior symbol has an elliptic representative with both residual kernels. -/
theorem exists_atlas_relative_kernel_localization
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol 0 a)
    (hi : IsEllipticAtlasSymbol a)
    (K : Set M) (hK : IsCompact K) (U : Set M) (hU : IsOpen U) (hKU : K ⊆ U)
    (b : ∀ x : M, E x →ₗ[ℂ] F x) (hb : IsSmoothAtlasBundleMapOn A B Kᶜ b)
    (hbiso : ∀ x : M, x ∉ K → Function.Bijective (b x))
    (ha : ∀ x : M, x ∉ K → ∀ ξ, ξ ≠ 0 → a x ξ = b x)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hE : ComplexBundle.ContinuousHermitianMetric E) (hhE : A.IsSmoothHermitianMetric hE)
    (hF : ComplexBundle.ContinuousHermitianMetric F) (hhF : B.IsSmoothHermitianMetric hF)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ] :
    ∃ L : Set M, IsCompact L ∧ K ⊆ L ∧ L ⊆ U ∧
      ∃ (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c),
        (∀ x : M, x ∉ L → c x = b x) ∧
        ∃ (N : ℕ) (T : Fin N → AtlasPseudodifferentialPiece A B 0),
          let P := atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap
          let d := fun x ↦ atlasFiberAdjoint A B hE hF x (c x)
          let hd := (atlasFiberAdjoint_properties A B hE hF hhE hhF c hc).1
          atlasGlobalPrincipalSymbolClass A B 0
              (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol) =
            atlasGlobalPrincipalSymbolClass A B 0 (atlasRegularizedSymbol A B g 0 a hs hh) ∧
          IsEllipticFullAtlasSymbol A B 0
            (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol).val ∧
          (∀ j, (T j).chart.symm ''
            (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ L) ∧
          ∃ (Q : B.smoothSections →ₗ[ℂ] A.smoothSections)
            (κ κR : AtlasSchwartzKernel A B),
            IsAtlasFormalAdjoint A B hE hF μ P Q ∧
            IsAtlasSchwartzKernel A B hF μ P κ ∧
            IsAtlasSchwartzKernel B A hE μ Q (atlasSchwartzKernelAdjoint A B κ) ∧
            IsAtlasSchwartzKernel A B hF μ (P - atlasSmoothSectionMap A B c hc) κR ∧
            IsAtlasSchwartzKernel B A hE μ (Q - atlasSmoothSectionMap B A d hd)
              (atlasSchwartzKernelAdjoint A B κR) ∧
            atlasSchwartzKernelSupport A B κR ⊆ L ×ˢ L ∧
            atlasSchwartzKernelSupport B A (atlasSchwartzKernelAdjoint A B κR) ⊆ L ×ˢ L ∧
            (∀ (u : A.smoothSections) (x : M), x ∉ L → (P u).val x = b x (u.val x)) ∧
            (∀ (v : B.smoothSections) (x : M), x ∉ L →
              (Q v).val x = atlasFiberAdjoint A B hE hF x (b x) (v.val x)) ∧
            (∀ x : M, x ∉ L → Function.Bijective (b x) ∧
              Function.Bijective (atlasFiberAdjoint A B hE hF x (b x))) := by
  classical
  -- Enlarge the exceptional compact set before quantizing the actual correction a - c.
  obtain ⟨K₀, hK₀, hKK₀, hK₀U, c, hc, hcb₀⟩ :=
    exists_atlasZeroOrder_extension_of_exterior A B K hK U hU hKU b hb
  have ha₀ (x : M) (hx : x ∉ K₀) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      a x ξ = c x := by
    rw [hcb₀ x hx]
    exact ha x (fun hxK ↦ hx (interior_subset (hKK₀ hxK))) ξ hξ
  obtain ⟨N, T, _, hprincipal, L, hL, hK₀L, hLU, hTL, hRSupport, hPout⟩ :=
    exists_atlas_relative_quantization A B a hs hh c hc K₀ hK₀ ha₀ U hU hK₀U g
  have hcb (x : M) (hx : x ∉ L) : c x = b x := hcb₀ x (fun hxK ↦ hx (hK₀L hxK))
  let P := atlasSmoothSectionMap A B c hc + ∑ j, (T j).toLinearMap
  let d := fun x ↦ atlasFiberAdjoint A B hE hF x (c x)
  let hd := (atlasFiberAdjoint_properties A B hE hF hhE hhF c hc).1
  let Mc := atlasSmoothSectionMap A B c hc
  let Md := atlasSmoothSectionMap B A d hd
  have helliptic : IsEllipticFullAtlasSymbol A B 0
      (atlasZeroOrderSymbol A B c hc + ∑ j, (T j).globalSymbol).val :=
    (isEllipticFullAtlasSymbol_iff_of_class_eq A B _ _ hprincipal).mpr
      ((isEllipticFullAtlasSymbol_atlasRegularizedSymbol_iff A B g 0 a hs hh).mpr hi)
  -- The adjoint and kernels are constructed for this same c and this same finite family T.
  obtain ⟨Q, hPQ, hQSupport, hQout⟩ :=
    exists_atlasRelative_formalAdjoint A B hE hF μ hhE hhF c hc N T L hL hTL
  obtain ⟨⟨κ, hκ, _⟩, ⟨κR, hκR, _⟩⟩ :=
    exists_atlasSchwartzKernels_of_pieces A B hF hhF μ c hc N T
  have hκQ : IsAtlasSchwartzKernel B A hE μ Q (atlasSchwartzKernelAdjoint A B κ) :=
    isAtlasSchwartzKernel_adjoint A B hE hF μ P Q κ hκ (fun u v hu _ ↦ hPQ u hu v)
  -- For residual adjunction, compactness of either test supplies every needed integral.
  let : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  have hIntA (u v : A.smoothSections) (hu : IsCompact (closure {x | u.val x ≠ 0})) :
      Integrable (fun x ↦ (hE.toCore x).inner (u.val x) (v.val x)) μ := by
    apply (A.contMDiff_pairing hE hhE u v).continuous.integrable_of_hasCompactSupport
    apply hu.of_isClosed_subset isClosed_closure (closure_mono ?_)
    intro x hx hz
    apply hx
    change (hE.toCore x).inner (u.val x) (v.val x) = 0
    rw [hz]
    let : InnerProductSpace.Core ℂ (E x) := hE.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  have hIntB (u v : B.smoothSections) (hv : IsCompact (closure {x | v.val x ≠ 0})) :
      Integrable (fun x ↦ (hF.toCore x).inner (u.val x) (v.val x)) μ := by
    apply (B.contMDiff_pairing hF hhF u v).continuous.integrable_of_hasCompactSupport
    apply hv.of_isClosed_subset isClosed_closure (closure_mono ?_)
    intro x hx hz
    apply hx
    change (hF.toCore x).inner (u.val x) (v.val x) = 0
    rw [hz]
    let : InnerProductSpace.Core ℂ (F x) := hF.toCore x
    exact InnerProductSpace.Core.inner_zero_right _
  have hRAdjoint (u : A.smoothSections) (v : B.smoothSections)
      (hu : IsCompact (closure {x | u.val x ≠ 0}))
      (hv : IsCompact (closure {x | v.val x ≠ 0})) :
      (∫ x, (hF.toCore x).inner (((P - Mc) u).val x) (v.val x) ∂μ) =
        ∫ x, (hE.toCore x).inner (u.val x) (((Q - Md) v).val x) ∂μ := by
    have hmult : (∫ x, (hF.toCore x).inner ((Mc u).val x) (v.val x) ∂μ) =
        ∫ x, (hE.toCore x).inner (u.val x) ((Md v).val x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x ↦
        (atlasFiberAdjoint_properties A B hE hF hhE hhF c hc).2.1 x (u.val x) (v.val x)))
    have hPu := hIntB (P u) v hv
    have hMcu := hIntB (Mc u) v hv
    have hQv := hIntA u (Q v) hu
    have hMdv := hIntA u (Md v) hu
    have hsubF := integral_sub hPu hMcu
    have hsubE := integral_sub hQv hMdv
    calc
      _ = ∫ x, ((hF.toCore x).inner ((P u).val x) (v.val x) -
          (hF.toCore x).inner ((Mc u).val x) (v.val x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        let : InnerProductSpace.Core ℂ (F x) := hF.toCore x
        exact InnerProductSpace.Core.inner_sub_left _ _ _
      _ = (∫ x, (hF.toCore x).inner ((P u).val x) (v.val x) ∂μ) -
          ∫ x, (hF.toCore x).inner ((Mc u).val x) (v.val x) ∂μ :=
        hsubF
      _ = (∫ x, (hE.toCore x).inner (u.val x) ((Q v).val x) ∂μ) -
          ∫ x, (hE.toCore x).inner (u.val x) ((Md v).val x) ∂μ := by rw [hPQ u hu v, hmult]
      _ = ∫ x, ((hE.toCore x).inner (u.val x) ((Q v).val x) -
          (hE.toCore x).inner (u.val x) ((Md v).val x)) ∂μ :=
        hsubE.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        let : InnerProductSpace.Core ℂ (E x) := hE.toCore x
        exact (InnerProductSpace.Core.inner_sub_right _ _ _).symm
  have hκRQ : IsAtlasSchwartzKernel B A hE μ (Q - Md)
      (atlasSchwartzKernelAdjoint A B κR) :=
    isAtlasSchwartzKernel_adjoint A B hE hF μ (P - Mc) (Q - Md) κR hκR hRAdjoint
  have hRSupport' : HasAtlasSectionOperatorSupport A B L (P - Mc) := by
    simpa only [P, Mc, add_sub_cancel_left] using hRSupport
  have hsupport := IsAtlasSchwartzKernel.support_subset A B hF μ (P - Mc) κR hκR
    L hL.isClosed hRSupport'
  have hsupportQ := IsAtlasSchwartzKernel.support_subset B A hE μ (Q - Md)
    (atlasSchwartzKernelAdjoint A B κR) hκRQ L hL.isClosed hQSupport
  refine ⟨L, hL, (fun x hx ↦ hK₀L (interior_subset (hKK₀ hx))), hLU,
    c, hc, hcb, N, T, hprincipal, helliptic, hTL, Q, κ, κR,
    hPQ, hκ, hκQ, hκR, hκRQ, hsupport, hsupportQ, ?_, ?_, ?_⟩
  · intro u x hx
    rw [hPout u x hx, hcb x hx]
  · intro v x hx
    rw [hQout v x hx, hcb x hx]
  · intro x hx
    have hb' := hbiso x (fun hxK ↦ hx (hK₀L (interior_subset (hKK₀ hxK))))
    refine ⟨hb', ?_⟩
    have hbij := (atlasFiberAdjoint_properties A B hE hF hhE hhF c hc).2.2 x
    rw [hcb x hx] at hbij
    exact hbij.mpr hb'

end AtiyahSinger
