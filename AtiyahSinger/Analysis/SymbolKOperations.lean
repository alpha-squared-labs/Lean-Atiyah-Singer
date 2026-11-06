/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SymbolKClass

/-!
# Elementary operations on symbol K classes

Public module ID: M1025.

The identity and composition formulas are those of the original support triples.
Complex scalar invariance uses a nonvanishing scalar path; an arbitrary affine
path between elliptic symbols need not stay elliptic. These are project bridges
from SG I.9 triple operations to the symbol convention in SG III.1 and III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- The fiberwise identity symbol is a continuous off-zero Hom section. -/
theorem isContinuousOffZeroGlobalSymbol_id :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := r) (globalSymbolId (n := n) E) := by
  /- In matching local frames the identity section is the constant identity matrix. These
  expressions patch into the original Hom total-space identity section and remain continuous
  when pulled to the nonzero cotangent space. -/
  change Continuous (puncturedSymbolTotal (r := r) (q := r) (globalSymbolId (n := n) E))
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.val.proj
  have hbase : Continuous (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
      z.val.proj) := (FiberBundle.continuous_proj _ _).comp continuous_subtype_val
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase.continuousAt, ?_⟩
  -- On this one valid frame, the original fiber identity has constant identity coordinates.
  apply (continuousAt_const (y := ContinuousLinearMap.id ℂ
    (EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
  filter_upwards [hbase.continuousAt.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _))] with z hz
  change (e.continuousLinearMapAt ℂ z.val.proj).comp
    ((ContinuousLinearMap.id ℂ (E z.val.proj)).comp (e.symmL ℂ z.val.proj)) = _
  apply ContinuousLinearMap.ext
  intro v
  exact e.continuousLinearMapAt_symmL (R := ℂ) hz v

/-- The identity symbol is elliptic in every dimension. -/
theorem isEllipticGlobalSymbol_id : IsEllipticGlobalSymbol E E (globalSymbolId (n := n) E) := by
  /- At each nonzero covector the symbol is the identity continuous linear map on its original
  fiber. Its forward and inverse functions are both identity, hence bijective. -/
  let _ := hM
  intro x ξ hξ
  exact Function.bijective_id

/-- A nonzero complex scalar preserves ellipticity. -/
theorem IsEllipticGlobalSymbol.smul {a : GlobalSymbolFunction (n := n) E F}
    (hi : IsEllipticGlobalSymbol E F a) (c : ℂ) (hc : c ≠ 0) :
    IsEllipticGlobalSymbol E F (c • a) := by
  /- At a nonzero covector compose the bijective original symbol with scalar multiplication by
  c on the target. Multiplication by c inverse gives the inverse scalar operation. -/
  let _ := hM
  intro x ξ hξ
  exact (LinearEquiv.smulOfNeZero ℂ (F x) c hc).bijective.comp (hi x ξ hξ)

variable {k : ℕ}
  {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin k)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin k)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]

/-- Composition of jointly continuous Hom sections is continuous off zero. -/
theorem IsContinuousOffZeroGlobalSymbol.comp
    {a : GlobalSymbolFunction (n := n) E F} {b : GlobalSymbolFunction (n := n) F G}
    (hb : IsContinuousOffZeroGlobalSymbol (r := q) (q := k) b)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := k) (globalSymbolComp b a) := by
  /- Use three compatible local bundle frames. Matrix multiplication is jointly continuous, and
  both Hom sections use the same base point. The local product is the coordinate expression
  of the original fiberwise composition. -/
  change Continuous (puncturedSymbolTotal (r := r) (q := k) (globalSymbolComp b a))
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.val.proj
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z₀.val.proj
  let g := trivializationAt (EuclideanSpace ℂ (Fin k)) G z₀.val.proj
  have hA := (continuousAt_hom_bundle (RingHom.id ℂ)
    (puncturedSymbolTotal (r := r) (q := q) a) (x₀ := z₀)).mp ha.continuousAt
  have hB := (continuousAt_hom_bundle (RingHom.id ℂ)
    (puncturedSymbolTotal (r := q) (q := k) b) (x₀ := z₀)).mp hb.continuousAt
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hA.1, (hB.2.clm_comp hA.2).congr_of_eventuallyEq ?_⟩
  -- Cancel only the same middle frame; no identification of different model ranks is needed.
  filter_upwards [hA.1.eventually (f.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ _))] with z hz
  apply ContinuousLinearMap.ext
  intro v
  change g.continuousLinearMapAt ℂ z.val.proj
    (b z.val.proj z.val.snd (a z.val.proj z.val.snd (e.symmL ℂ z.val.proj v))) =
      g.continuousLinearMapAt ℂ z.val.proj (b z.val.proj z.val.snd
        (f.symmL ℂ z.val.proj (f.continuousLinearMapAt ℂ z.val.proj
          (a z.val.proj z.val.snd (e.symmL ℂ z.val.proj v)))))
  exact (congrArg (fun w ↦ g.continuousLinearMapAt ℂ z.val.proj
    (b z.val.proj z.val.snd w)) (f.symmL_continuousLinearMapAt (R := ℂ) hz _)).symm

/-- Composition of elliptic symbols is elliptic. -/
theorem IsEllipticGlobalSymbol.comp
    {a : GlobalSymbolFunction (n := n) E F} {b : GlobalSymbolFunction (n := n) F G}
    (hb : IsEllipticGlobalSymbol F G b) (ha : IsEllipticGlobalSymbol E F a) :
    IsEllipticGlobalSymbol E G (globalSymbolComp b a) := by
  /- At every nonzero covector compose the two bijective fiber functions. The original
  composition order is a first and b second, so their inverse maps compose in the reverse
  order. -/
  let _ := hM
  intro x ξ hξ
  exact (hb x ξ hξ).comp (ha x ξ hξ)

variable [CompactSpace M] [T2Space M]

/-- The identity symbol class vanishes. -/
theorem symbolKClass_id :
    symbolKClass (globalSymbolId (n := n) E)
      (isContinuousOffZeroGlobalSymbol_id (r := r)) isEllipticGlobalSymbol_id = 0 := by
  /- The exterior map is the restriction of the global identity on the pulled-back bundle. The
  extension criterion makes its compact-support class zero, including in dimension zero
  where source and target coincide. -/
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  apply symbolKClass_eq_zero_of_extension
  refine ⟨ComplexBundle.Iso.refl _, ?_⟩
  apply ComplexBundle.Iso.ext
  intro z
  apply LinearEquiv.ext
  intro v
  exact (ellipticSymbolBoundary_apply (globalSymbolId (n := n) E)
    isContinuousOffZeroGlobalSymbol_id isEllipticGlobalSymbol_id z v).symm

/-- Composition of elliptic symbols adds their compact-support classes. -/
theorem symbolKClass_comp
    (a : GlobalSymbolFunction (n := n) E F) (b : GlobalSymbolFunction (n := n) F G)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hb : IsContinuousOffZeroGlobalSymbol (r := q) (q := k) b)
    (hi : IsEllipticGlobalSymbol E F a) (hj : IsEllipticGlobalSymbol F G b) :
    symbolKClass (globalSymbolComp b a) (hb.comp ha) (hj.comp hi) =
      symbolKClass a ha hi + symbolKClass b hb hj := by
  /- The actual exterior maps compose in the same order as the original symbols. Both triples
  use the zero section, and the union of these identical controls is the same control. Apply
  the raw support-triple composition formula, using the same resizing of the middle bundle. -/
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin k)) G
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := ComplexBundle.isFiniteRank_model (EuclideanSpace ℂ (Fin k)) G
  let := ComplexBundle.isFiniteRank_pullback (E := E)
    (cotangentProjection (n := n) (M := M))
  let := ComplexBundle.isFiniteRank_pullback (E := F)
    (cotangentProjection (n := n) (M := M))
  let := ComplexBundle.isFiniteRank_pullback (E := G)
    (cotangentProjection (n := n) (M := M))
  let u := ellipticSymbolTriple a ha hi
  let v := ellipticSymbolTriple b hb hj
  let d := ellipticSymbolTriple (globalSymbolComp b a) (hb.comp ha) (hj.comp hi)
  let K := cotangentZeroSet (n := n) (M := M) ∪ cotangentZeroSet
  have hK : IsCompact K := isCompact_cotangentZeroSet.union isCompact_cotangentZeroSet
  have hd : d.control ⊆ K := Set.subset_union_left
  have hcompose : u.compose v = d.enlarge K hK hd := by
    change ComplexBundle.CompactSupportTriple.mk K hK _ =
      ComplexBundle.CompactSupportTriple.mk K hK _
    congr 1
    apply ComplexBundle.Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    let z' : PuncturedCotangentBundle (n := n) (M := M) :=
      ⟨z, fun hz ↦ z.property (Or.inl hz)⟩
    -- Compare the same original vectors on the exterior of the common union control.
    have hu := (u.enlarge_apply K hK Set.subset_union_left z w).trans
      (ellipticSymbolTriple_boundary_apply a ha hi z' w)
    let uw := (u.enlarge K hK Set.subset_union_left).boundary.linearEquiv z w
    have hv := (v.enlarge_apply K hK Set.subset_union_right z uw).trans
      (ellipticSymbolTriple_boundary_apply b hb hj z' uw)
    have hleft := hv.trans (congrArg (b z'.val.proj z'.val.snd) hu)
    have hright := (d.enlarge_apply K hK hd z w).trans
      (ellipticSymbolTriple_boundary_apply (globalSymbolComp b a) (hb.comp ha)
        (hj.comp hi) z' w)
    exact hleft.trans hright.symm
  change d.compactSupportClass = u.compactSupportClass + v.compactSupportClass
  calc
    d.compactSupportClass = (d.enlarge K hK hd).compactSupportClass :=
      (d.compactSupportClass_enlarge K hK hd).symm
    _ = (u.compose v).compactSupportClass :=
      congrArg ComplexBundle.CompactSupportTriple.compactSupportClass hcompose.symm
    _ = u.compactSupportClass + v.compactSupportClass := u.compactSupportClass_compose v

/-- Multiplication by a nonzero complex scalar leaves the symbol class unchanged. -/
theorem symbolKClass_smul (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hi : IsEllipticGlobalSymbol E F a) (c : ℂ) (hc : c ≠ 0) :
    symbolKClass (c • a) (ha.smul c) (hi.smul c hc) = symbolKClass a ha hi := by
  /- Choose one complex logarithm of c and use the exponential path from one to c. This scalar
  path never vanishes. Multiplying the original Hom section by it gives a jointly continuous
  elliptic family with one zero-section control. An affine scalar interpolation would not
  suffice when it passes through zero. -/
  let s : unitInterval → ℂ := fun t ↦ Complex.exp (((t : ℝ) : ℂ) * Complex.log c)
  have hs : Continuous s := Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
  have hs0 : s 0 = 1 := by simp [s]
  have hs1 : s 1 = c := by simpa [s] using Complex.exp_log hc
  let H : unitInterval → GlobalSymbolFunction (n := n) E F := fun t ↦ s t • a
  have hI (t : unitInterval) : IsEllipticGlobalSymbol E F (H t) :=
    hi.smul (s t) (Complex.exp_ne_zero _)
  -- Joint continuity uses the original Hom bundle, with one local frame on the cylinder.
  have hpre : Continuous (fun p : unitInterval × PuncturedCotangentBundle (n := n) (M := M) ↦
      puncturedSymbolTotal (r := r) (q := q) a p.2) := Continuous.comp ha continuous_snd
  have hH : IsContinuousOffZeroSymbolFamily (r := r) (q := q) H := by
    unfold IsContinuousOffZeroSymbolFamily
    apply continuous_iff_continuousAt.mpr
    intro p
    let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let B := fun x ↦ E x →L[ℂ] F x
    let e := trivializationAt V B p.2.val.proj
    have h₁ := (FiberBundle.continuousAt_totalSpace V _).mp (hpre.continuousAt (x := p))
    apply (FiberBundle.continuousAt_totalSpace V _).mpr
    refine ⟨h₁.1, (((hs.comp continuous_fst).continuousAt).smul h₁.2).congr_of_eventuallyEq ?_⟩
    filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V B p.2.val.proj))] with y hy
    exact (e.linear ℂ hy).2 (s y.1) (a y.2.val.proj y.2.val.snd)
  have h0 : H 0 = a := by
    change s 0 • a = a
    rw [hs0, one_smul]
  have h1 : H 1 = c • a := by
    change s 1 • a = c • a
    rw [hs1]
  exact (symbolKClass_eq_of_family a ha hi (c • a) (ha.smul c) (hi.smul c hc)
    H hH hI h0 h1).symm

/-- Negating an elliptic symbol leaves its class unchanged. -/
theorem symbolKClass_neg (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hi : IsEllipticGlobalSymbol E F a) :
    symbolKClass ((-1 : ℂ) • a) (ha.smul (-1)) (hi.smul (-1) (neg_ne_zero.mpr one_ne_zero)) =
      symbolKClass a ha hi := by
  /- Apply complex scalar invariance to minus one, which is nonzero. This concerns changing the
  boundary map by a complex phase; exchanging source and target instead produces the
  additive inverse class. -/
  exact symbolKClass_smul a ha hi (-1) (neg_ne_zero.mpr one_ne_zero)

end AtiyahSinger
