/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologyCup
public import AtiyahSinger.Topology.SingularCapProduct

/-!
# Cap product for a relative cochain and a relative chain of the same pair

Public module ID: M2058.

Hatcher, Algebraic Topology, section 3.3, pp.240--241 and 245. The original
Alexander--Whitney formula gives H^p(X,A;R) x H_(p+q)(X,A;R) -> H_q(X;R).
The target is absolute: a relative cochain kills every front face of a
simplex in A, so the chain operation kills C_*(A) before taking a quotient.
The boundary identity then gives absolute cycles and absolute boundaries.

Both descents use the existing cokernel projection and the original
cycle/boundary quotients. No pairing is chosen independently of the
front/back formula. The subset A is arbitrary, with no compactness or
excision hypothesis. This same-pair pairing is the one needed for
compact supports and local fundamental classes. Different-pair cap
products involving unions require additional excision data and are not
asserted here. The support-inclusion identity uses the same ambient
space and the already defined relative maps in both arguments.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- A relative cochain caps every chain lying in A to zero as an absolute chain. -/
theorem singularCochainCap_comp_subspace_eq_zero (A : Set X) (p q : ℕ)
    (φ : (relativeSingularCochains R A).X p) :
    (singularSubspaceChains R A).f (p + q) ≫
      ModuleCat.ofHom (singularCochainCap R X p q
        (relativeSingularCochainEquiv R A p φ).val) = 0 := by
  /- Each original simplex in A has its front face in A. The given
  relative cochain vanishes on this front face because it factors
  through the original chain cokernel. Its cap coefficient is zero,
  so the actual back-face chain is zero. Original coproduct generators
  span the chain module, proving the displayed morphism equality.
  The output is zero before any quotient in the target. -/
  -- Restriction evaluates on the included simplex, and its front face still lies in A.
  let f := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
  let P := (singularCochainDualFunctor R).map (singularSubspaceChains R A).op
  have heval (k : ℕ) (χ : (singularCochains R X).X k)
      (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋k⦌)) :
      singularCochainEquiv R A k (P.f k χ) σ =
        singularCochainEquiv R X k χ (f.app (op ⦋k⦌) σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
      (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
        (SSet.chainComplexMap f (singularCoefficient R)).f k) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  have hgen (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋p + q⦌)) :
      singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val
        ((singularSubspaceChains R A).f (p + q)
          ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
            (R := singularCoefficient R) σ (ULift.up 1))) = 0 := by
    change singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val
      (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
        (SSet.chainComplexMap f (singularCoefficient R)).f (p + q)) (ULift.up 1)) = 0
    rw [SSet.ι_chainComplexMap_f, singularCochainCap_simplex]
    have hvanish := congrArg
      (fun χ : (singularCochains R A).X p ↦ singularCochainEquiv R A p χ
        ((TopCat.toSSet.obj (TopCat.of A)).map (singularCupFrontFace p q).op σ))
      (relativeSingularCochainEquiv R A p φ).property
    rw [heval] at hvanish
    have hface := congrArg (fun g ↦ g σ) (f.naturality (singularCupFrontFace p q).op)
    change f.app (op ⦋p⦌) ((TopCat.toSSet.obj (TopCat.of A)).map
      (singularCupFrontFace p q).op σ) =
        (TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op
          (f.app (op ⦋p + q⦌) σ) at hface
    rw [← hface, hvanish]
    simp
    rfl
  -- Extend the coefficient-one computation to every original coproduct summand.
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  have hr : r = r.down • (ULift.up (1 : R) : ULift.{u} R) := by
    apply ULift.ext
    simp
  rw [hr, map_smul]
  change r.down • singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val
    ((singularSubspaceChains R A).f (p + q)
      ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
        (R := singularCoefficient R) σ (ULift.up 1))) = 0
  rw [hgen, smul_zero]

/-- The original cap formula descends to relative chains, with an absolute chain target. -/
def relativeSingularCochainCap (A : Set X) (p q : ℕ) :
    (relativeSingularCochains R A).X p →ₗ[R]
      (relativeSingularChains R A).X (p + q) →ₗ[R] (singularChains R X).X q := by
  -- Evaluation preserves the existing chain cokernel in the required degree.
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) (p + q))
    (singularSubspaceChains R A)
  -- Descend precisely the original front/back operator along its quotient projection.
  let lift (φ : (relativeSingularCochains R A).X p) :=
    CokernelCofork.IsColimit.desc' Q
      (ModuleCat.ofHom (singularCochainCap R X p q
        (relativeSingularCochainEquiv R A p φ).val))
      (singularCochainCap_comp_subspace_eq_zero R A p q φ)
  exact
    { toFun := fun φ ↦ (lift φ).val.hom
      map_add' := by
        intro φ ψ
        change (lift (φ + ψ)).val.hom = ((lift φ).val + (lift ψ).val).hom
        apply congrArg ModuleCat.Hom.hom
        apply Cofork.IsColimit.hom_ext Q
        rw [Preadditive.comp_add, (lift (φ + ψ)).property,
          (lift φ).property, (lift ψ).property]
        apply ModuleCat.hom_ext
        change singularCochainCap R X p q
            (relativeSingularCochainEquiv R A p (φ + ψ)).val = _
        simp only [map_add, Submodule.coe_add]
        rfl
      map_smul' := by
        intro a φ
        change (lift (a • φ)).val.hom = (a • (lift φ).val).hom
        apply congrArg ModuleCat.Hom.hom
        apply Cofork.IsColimit.hom_ext Q
        rw [Linear.comp_smul, (lift (a • φ)).property, (lift φ).property]
        apply ModuleCat.hom_ext
        change singularCochainCap R X p q
            (relativeSingularCochainEquiv R A p (a • φ)).val = _
        simp only [map_smul, Submodule.coe_smul]
        rfl }

/-- On a projected original chain the descended operation is the original cap formula. -/
theorem relativeSingularCochainCap_projection (A : Set X) (p q : ℕ)
    (φ : (relativeSingularCochains R A).X p) (c : (singularChains R X).X (p + q)) :
    relativeSingularCochainCap R A p q φ ((relativeSingularChainsProjection R A).f (p + q) c) =
      singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val c := by
  /- This is the specifying equation of the original cokernel descent,
  evaluated on c. Its source, projection and output are exactly those
  in relativeSingularCochainCap; no representative choice is involved. -/
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) (p + q))
    (singularSubspaceChains R A)
  let lift := CokernelCofork.IsColimit.desc' Q
    (ModuleCat.ofHom (singularCochainCap R X p q
      (relativeSingularCochainEquiv R A p φ).val))
    (singularCochainCap_comp_subspace_eq_zero R A p q φ)
  exact congrArg (fun f : (singularChains R X).X (p + q) ⟶ (singularChains R X).X q ↦ f c)
    lift.property

/-- The cycle kernel of the actual relative singular chain complex. -/
abbrev relativeSingularCycles (A : Set X) (n : ℕ) : ModuleCat.{u} R :=
  ((relativeSingularChains R A).sc n).moduleCatLeftHomologyData.K

/-- The incoming-boundary image inside that same relative cycle kernel. -/
abbrev relativeSingularBoundaries (A : Set X) (n : ℕ) :
    Submodule R (relativeSingularCycles R A n) :=
  ((relativeSingularChains R A).sc n).moduleCatToCycles.range

/-- The class of a relative cycle in the already defined relative singular homology. -/
def relativeSingularCycleClass (A : Set X) (n : ℕ) :
    relativeSingularCycles R A n →ₗ[R] relativeSingularHomology R A n :=
  (((relativeSingularChains R A).sc n).moduleCatHomologyIso.inv.hom).comp
    (relativeSingularBoundaries R A n).mkQ

/-- A relative cocycle capping a relative cycle of the same pair is an absolute cycle. -/
theorem relativeSingularCochainCap_mem_cycles (A : Set X) (p q : ℕ)
    (φ : relativeSingularCocycles R A p) (c : relativeSingularCycles R A (p + q)) :
    ((singularChains R X).sc q).g (relativeSingularCochainCap R A p q φ.val c.val) = 0 := by
  /- Lift c to an original chain using the original cokernel projection.
  Its boundary lies in chains on A. In positive output degree apply
  the cap boundary formula: the cochain differential vanishes, and
  the remaining term vanishes because the same relative cochain kills
  chains in A. Thus the result is an absolute cycle. In degree zero
  the original outgoing chain differential is zero. The argument
  uses neither compactness nor injectivity of a cohomology comparison. -/
  -- The kernel witness uses dFrom; the canonical next-degree map recovers the actual boundary.
  have hclosed {shape : ComplexShape ℕ} (D : HomologicalComplex (ModuleCat.{u} R) shape)
      (i j : ℕ) (hij : shape.Rel i j)
      (a : (D.sc i).moduleCatLeftHomologyData.K) : D.d i j a.val = 0 := by
    let v : D.X i := a.val
    have h : D.dFrom i v = 0 := a.property
    have h' := congrArg (D.xNextIso hij).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  -- Descend the original cap boundary identity along the same degreewise cokernel projection.
  have hcap_boundary (p q : ℕ)
      (φ : (relativeSingularCochains R A).X p)
      (c : (relativeSingularChains R A).X (p + (q + 1))) :
      (singularChains R X).d (q + 1) q (relativeSingularCochainCap R A p (q + 1) φ c) =
        (-1 : R) ^ p •
          (relativeSingularCochainCap R A p q φ
              ((relativeSingularChains R A).d (p + (q + 1)) (p + q) c) -
            relativeSingularCochainCap R A (p + 1) q
              ((relativeSingularCochains R A).d p (p + 1) φ)
              (((relativeSingularChains R A).XIsoOfEq
                ((Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1))).hom c)) := by
    let π := relativeSingularChainsProjection R A
    let J := (singularCochainDualFunctor R).map π.op
    have hd (i j : ℕ) (z : (singularChains R X).X i) :
        π.f j ((singularChains R X).d i j z) =
          (relativeSingularChains R A).d i j (π.f i z) :=
      (congrArg (fun f ↦ f z) (π.comm i j)).symm
    have hdual (i j : ℕ) (χ : (relativeSingularCochains R A).X i) :
        J.f j ((relativeSingularCochains R A).d i j χ) =
          (singularCochains R X).d i j (J.f i χ) :=
      (congrArg (fun f ↦ f χ) (J.comm i j)).symm
    have ht {i j : ℕ} (h : i = j) (z : (singularChains R X).X i) :
        π.f j (((singularChains R X).XIsoOfEq h).hom z) =
          ((relativeSingularChains R A).XIsoOfEq h).hom (π.f i z) := by
      subst j
      rfl
    -- Every relative chain is the image of an original chain; no representative is added as data.
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (π.f (p + (q + 1)))).mp inferInstance c
    rw [relativeSingularCochainCap_projection, singularCochainCap_boundary, ← hd, ← ht,
      relativeSingularCochainCap_projection, relativeSingularCochainCap_projection]
    rw [show (relativeSingularCochainEquiv R A (p + 1)
      ((relativeSingularCochains R A).d p (p + 1) φ)).val =
        (singularCochains R X).d p (p + 1) (relativeSingularCochainEquiv R A p φ).val
      from hdual p (p + 1) φ]
  -- At degree zero the outgoing chain differential vanishes; positive degrees use the formula.
  cases q with
  | zero =>
    have hd : (singularChains R X).dFrom 0 = 0 :=
      (singularChains R X).shape _ _ (by change ¬ _ + 1 = 0; omega)
    change (singularChains R X).dFrom 0 _ = 0
    rw [hd]
    rfl
  | succ k =>
    have hφ := hclosed (relativeSingularCochains R A) p (p + 1) rfl φ
    have hc := hclosed (relativeSingularChains R A) (p + (k + 1)) (p + k)
      (by change p + k + 1 = p + (k + 1); omega) c
    have hcap := hcap_boundary p k φ.val c.val
    rw [hφ, hc] at hcap
    simp only [map_zero, LinearMap.zero_apply, sub_zero, smul_zero] at hcap
    change (singularChains R X).dFrom (k + 1) _ = 0
    rw [HomologicalComplex.dFrom_eq (r := show (ComplexShape.down ℕ).Rel (k + 1) k
      from rfl), ModuleCat.comp_apply, hcap, map_zero]

/-- The actual relative cap formula restricted to cocycles and cycles, with absolute output. -/
def relativeSingularCycleCap (A : Set X) (p q : ℕ) :
    relativeSingularCocycles R A p →ₗ[R] relativeSingularCycles R A (p + q) →ₗ[R]
      singularCycles R X q where
  toFun φ :=
    { toFun := fun c ↦ ⟨relativeSingularCochainCap R A p q φ.val c.val,
        relativeSingularCochainCap_mem_cycles R A p q φ c⟩
      map_add' := by
        intro c d
        apply Subtype.ext
        exact (relativeSingularCochainCap R A p q φ.val).map_add c.val d.val
      map_smul' := by
        intro a c
        apply Subtype.ext
        exact (relativeSingularCochainCap R A p q φ.val).map_smul a c.val }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f ↦ f c.val)
      ((relativeSingularCochainCap R A p q).map_add φ.val ψ.val)
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f ↦ f c.val)
      ((relativeSingularCochainCap R A p q).map_smul a φ.val)

/-- A coboundary or a boundary in the two inputs gives an actual absolute boundary. -/
theorem relativeSingularCycleCap_mem_boundaries (A : Set X) (p q : ℕ)
    (φ : relativeSingularCocycles R A p) (c : relativeSingularCycles R A (p + q))
    (h : φ ∈ relativeSingularCoboundaries R A p ∨
      c ∈ relativeSingularBoundaries R A (p + q)) :
    relativeSingularCycleCap R A p q φ c ∈ singularBoundaries R X q := by
  /- For a relative coboundary choose its actual relative cochain
  primitive. In positive degree the cap boundary formula supplies
  an absolute chain primitive, with the indicated (-1)^p correction;
  the cap with the boundary of the lifted relative cycle vanishes
  on A. In cochain degree zero the incoming cochain differential is
  zero, so that factor is zero. For a relative boundary choose its
  actual relative chain primitive. The closed cochain kills its A
  correction, and the same boundary formula gives an absolute
  primitive. Thus the output lies in the original boundary image,
  not merely in a relative boundary image. -/
  let O := singularChains R X
  let C := relativeSingularChains R A
  let D := relativeSingularCochains R A
  -- The kernel witness uses dFrom; the canonical next-degree map recovers the actual boundary.
  have hclosed {shape : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{u} R) shape)
      (i j : ℕ) (hij : shape.Rel i j)
      (a : (K.sc i).moduleCatLeftHomologyData.K) : K.d i j a.val = 0 := by
    let v : K.X i := a.val
    have h : K.dFrom i v = 0 := a.property
    have h' := congrArg (K.xNextIso hij).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  -- Boundary membership supplies a primitive in the same complex, via its incoming-degree map.
  have hprimitive {shape : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{u} R) shape)
      (i j : ℕ) (hij : shape.Rel i j) (a : (K.sc j).moduleCatLeftHomologyData.K)
      (ha : a ∈ (K.sc j).moduleCatToCycles.range) :
      ∃ b : K.X i, K.d i j b = a.val := by
    obtain ⟨b, hb⟩ := ha
    have hval := congrArg Subtype.val hb
    change K.dTo j b = a.val at hval
    refine ⟨(K.xPrevIso hij).hom b, ?_⟩
    have hcomp := congrArg (fun f : K.xPrev j ⟶ K.X j ↦ f b) (K.dTo_eq hij)
    exact hcomp.symm.trans hval
  have hboundary (a : singularCycles R X q) (b : O.X (q + 1))
      (hb : O.d (q + 1) q b = a.val) : a ∈ singularBoundaries R X q := by
    have hrel : (ComplexShape.down ℕ).Rel (q + 1) q := rfl
    refine ⟨(O.xPrevIso hrel).inv b, ?_⟩
    apply Subtype.ext
    change O.dTo q ((O.xPrevIso hrel).inv b) = a.val
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo]
    exact hb
  -- Descend the original cap boundary identity along the same degreewise cokernel projection.
  have hcap_boundary (p q : ℕ)
      (φ : (relativeSingularCochains R A).X p)
      (c : (relativeSingularChains R A).X (p + (q + 1))) :
      (singularChains R X).d (q + 1) q (relativeSingularCochainCap R A p (q + 1) φ c) =
        (-1 : R) ^ p •
          (relativeSingularCochainCap R A p q φ
              ((relativeSingularChains R A).d (p + (q + 1)) (p + q) c) -
            relativeSingularCochainCap R A (p + 1) q
              ((relativeSingularCochains R A).d p (p + 1) φ)
              (((relativeSingularChains R A).XIsoOfEq
                ((Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1))).hom c)) := by
    let π := relativeSingularChainsProjection R A
    let J := (singularCochainDualFunctor R).map π.op
    have hd (i j : ℕ) (z : (singularChains R X).X i) :
        π.f j ((singularChains R X).d i j z) =
          (relativeSingularChains R A).d i j (π.f i z) :=
      (congrArg (fun f ↦ f z) (π.comm i j)).symm
    have hdual (i j : ℕ) (χ : (relativeSingularCochains R A).X i) :
        J.f j ((relativeSingularCochains R A).d i j χ) =
          (singularCochains R X).d i j (J.f i χ) :=
      (congrArg (fun f ↦ f χ) (J.comm i j)).symm
    have ht {i j : ℕ} (h : i = j) (z : (singularChains R X).X i) :
        π.f j (((singularChains R X).XIsoOfEq h).hom z) =
          ((relativeSingularChains R A).XIsoOfEq h).hom (π.f i z) := by
      subst j
      rfl
    -- Every relative chain is the image of an original chain; no representative is added as data.
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (π.f (p + (q + 1)))).mp inferInstance c
    rw [relativeSingularCochainCap_projection, singularCochainCap_boundary, ← hd, ← ht,
      relativeSingularCochainCap_projection, relativeSingularCochainCap_projection]
    rw [show (relativeSingularCochainEquiv R A (p + 1)
      ((relativeSingularCochains R A).d p (p + 1) φ)).val =
        (singularCochains R X).d p (p + 1) (relativeSingularCochainEquiv R A p φ).val
      from hdual p (p + 1) φ]
  -- A cochain coboundary and a chain boundary require their respective actual primitives.
  rcases h with hφ | hc
  · cases p with
    | zero =>
      obtain ⟨α, hα⟩ := hφ
      have hval := congrArg Subtype.val hα
      change D.dTo 0 α = φ.val at hval
      have hd : D.dTo 0 = 0 := D.shape _ _ (by
        change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
        omega)
      rw [hd] at hval
      have hφzero : φ = 0 := Subtype.ext hval.symm
      rw [hφzero]
      simp
    | succ k =>
      -- Reassociate the same relative cycle, then correct the primitive by the parity sign.
      obtain ⟨α, hα⟩ := hprimitive D k (k + 1) rfl φ hφ
      have hdeg : k + (q + 1) = (k + 1) + q := by omega
      let c₀ : C.X (k + (q + 1)) := (C.XIsoOfEq hdeg.symm).hom c.val
      have hcast : (C.XIsoOfEq hdeg).hom c₀ = c.val := by
        change ((C.XIsoOfEq hdeg.symm).hom ≫ (C.XIsoOfEq hdeg).hom) c.val = c.val
        simp
        rfl
      have hclosedc := hclosed C ((k + 1) + q) (k + q)
        (by change k + q + 1 = k + 1 + q; omega) c
      have hc₀ : C.d (k + (q + 1)) (k + q) c₀ = 0 := by
        change ((C.XIsoOfEq hdeg.symm).hom ≫ C.d _ _) c.val = 0
        rw [HomologicalComplex.XIsoOfEq_hom_comp_d]
        exact hclosedc
      have hcap := hcap_boundary k q α c₀
      change O.d (q + 1) q _ = _ at hcap
      rw [hα, hcast, hc₀, map_zero] at hcap
      apply hboundary (relativeSingularCycleCap R A (k + 1) q φ c)
        (-((-1 : R) ^ k) • relativeSingularCochainCap R A k (q + 1) α c₀)
      change O.d (q + 1) q (-((-1 : R) ^ k) •
        relativeSingularCochainCap R A k (q + 1) α c₀) =
          relativeSingularCochainCap R A (k + 1) q φ.val c.val
      rw [map_smul, hcap, smul_smul, neg_mul, ← pow_add, ← two_mul, pow_mul]
      simp
  · -- A closed cochain caps a relative chain primitive to an absolute primitive.
    obtain ⟨b, hb⟩ := hprimitive C (p + (q + 1)) (p + q)
      (by change p + q + 1 = p + (q + 1); omega) c hc
    have hφ := hclosed D p (p + 1) rfl φ
    have hcap := hcap_boundary p q φ.val b
    change O.d (q + 1) q _ = _ at hcap
    rw [hφ, hb] at hcap
    simp only [map_zero, LinearMap.zero_apply, sub_zero] at hcap
    apply hboundary (relativeSingularCycleCap R A p q φ c)
      ((-1 : R) ^ p • relativeSingularCochainCap R A p (q + 1) φ.val b)
    change O.d (q + 1) q ((-1 : R) ^ p •
      relativeSingularCochainCap R A p (q + 1) φ.val b) =
        relativeSingularCochainCap R A p q φ.val c.val
    rw [map_smul, hcap, smul_smul, ← pow_add, ← two_mul, pow_mul]
    simp

/-- The Alexander--Whitney cap pairing of the same relative pair into absolute homology. -/
def relativeSingularCapProduct (A : Set X) (p q : ℕ) :
    relativeSingularCohomology R A p →ₗ[R]
      relativeSingularHomology R A (p + q) →ₗ[R] singularHomology R X q := by
  -- Form the original absolute cycle class and kill the two original boundary submodules.
  let product := (relativeSingularCycleCap R A p q).compr₂ (singularBoundaries R X q).mkQ
  have hLeft : relativeSingularCoboundaries R A p ≤ product.ker := by
    intro a ha
    apply LinearMap.ext
    intro c
    change (singularBoundaries R X q).mkQ (relativeSingularCycleCap R A p q a c) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCycleCap_mem_boundaries R A p q a c (Or.inl ha))
  have hRight : relativeSingularBoundaries R A (p + q) ≤ product.flip.ker := by
    intro c hc
    apply LinearMap.ext
    intro a
    change (singularBoundaries R X q).mkQ (relativeSingularCycleCap R A p q a c) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCycleCap_mem_boundaries R A p q a c (Or.inr hc))
  -- Descend both original quotients, then apply their canonical categorical comparisons.
  let descended := product.liftQ₂
    (relativeSingularCoboundaries R A p) (relativeSingularBoundaries R A (p + q)) hLeft hRight
  let comparison := descended.compr₂ ((singularChains R X).sc q).moduleCatHomologyIso.inv.hom
  exact
    (comparison.compl₂ ((relativeSingularChains R A).sc (p + q)).moduleCatHomologyIso.hom.hom).comp
      ((relativeSingularCochains R A).sc p).moduleCatHomologyIso.hom.hom

/-- The pairing on the specified original classes is represented by their original cap chain. -/
theorem relativeSingularCapProduct_cycleClass (A : Set X) (p q : ℕ)
    (φ : relativeSingularCocycles R A p) (c : relativeSingularCycles R A (p + q)) :
    relativeSingularCapProduct R A p q (relativeSingularCocycleClass R A p φ)
        (relativeSingularCycleClass R A (p + q) c) =
      singularCycleClass R X q (relativeSingularCycleCap R A p q φ c) := by
  /- Cancel the canonical homology comparison maps. The two quotient
  lifts evaluated at these representatives give precisely the class
  of their original cap cycle. The absolute target comparison is
  the one used in singularCycleClass. -/
  let product := (relativeSingularCycleCap R A p q).compr₂ (singularBoundaries R X q).mkQ
  have hLeft : relativeSingularCoboundaries R A p ≤ product.ker := by
    intro a ha
    apply LinearMap.ext
    intro c
    change (singularBoundaries R X q).mkQ (relativeSingularCycleCap R A p q a c) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCycleCap_mem_boundaries R A p q a c (Or.inl ha))
  have hRight : relativeSingularBoundaries R A (p + q) ≤ product.flip.ker := by
    intro c hc
    apply LinearMap.ext
    intro a
    change (singularBoundaries R X q).mkQ (relativeSingularCycleCap R A p q a c) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (relativeSingularCycleCap_mem_boundaries R A p q a c (Or.inr hc))
  let descended := product.liftQ₂
    (relativeSingularCoboundaries R A p) (relativeSingularBoundaries R A (p + q)) hLeft hRight
  let I := ((relativeSingularCochains R A).sc p).moduleCatHomologyIso
  let J := ((relativeSingularChains R A).sc (p + q)).moduleCatHomologyIso
  let K := ((singularChains R X).sc q).moduleCatHomologyIso
  change K.inv (descended (I.hom (I.inv ((relativeSingularCoboundaries R A p).mkQ φ)))
    (J.hom (J.inv ((relativeSingularBoundaries R A (p + q)).mkQ c)))) =
      K.inv ((singularBoundaries R X q).mkQ (relativeSingularCycleCap R A p q φ c))
  have hI : I.hom (I.inv ((relativeSingularCoboundaries R A p).mkQ φ)) =
      (relativeSingularCoboundaries R A p).mkQ φ :=
    congrArg (fun f ↦ f ((relativeSingularCoboundaries R A p).mkQ φ)) I.inv_hom_id
  have hJ : J.hom (J.inv ((relativeSingularBoundaries R A (p + q)).mkQ c)) =
      (relativeSingularBoundaries R A (p + q)).mkQ c :=
    congrArg (fun f ↦ f ((relativeSingularBoundaries R A (p + q)).mkQ c)) J.inv_hom_id
  rw [hI, hJ]
  rfl

/-- Enlarging the relative subspace gives the support compatibility of the same cap pairing. -/
theorem relativeSingularCapProduct_inclusion (A B : Set X) (h : A ⊆ B) (p q : ℕ)
    (a : relativeSingularCohomology R B p) (z : relativeSingularHomology R A (p + q)) :
    relativeSingularCapProduct R A p q (relativeSingularCohomologyRestriction R A B h p a) z =
      relativeSingularCapProduct R B p q a
        (relativeSingularHomologyInclusion R A B h (p + q) z) := by
  /- The two cochains pull back to the same ordinary cochain on X.
  The inclusion map on relative chains is induced by the identity
  on the same ordinary chains, so both cap constructions give the
  same absolute chain on every projected generator. Descend first
  through the actual cokernels and then through the original cycle
  quotients. This identity supplies compact-support compatibility
  by taking A to be the complement of a larger compact set and B
  the complement of the smaller one. No compactness is used here. -/
  -- Choose actual quotient representatives in either of the original homological complexes.
  have hrep {shape : ComplexShape ℕ} (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  -- Naturality of the fixed homology comparisons computes classes under the specified maps.
  have hclass {shape : ComplexShape ℕ}
      (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) shape n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap]
    change (D.sc n).moduleCatHomologyIso.inv
      (G.φH ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))) = _
    have hcancel : (C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc n).moduleCatToCycles.range.mkQ a :=
      congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
        (C.sc n).moduleCatHomologyIso.inv_hom_id
    rw [hcancel, hquot]
  -- The same chain or cochain map sends the original outgoing kernel into its counterpart.
  have hcycles {shape : ComplexShape ℕ}
      (C D : HomologicalComplex (ModuleCat.{u} R) shape) (F : C ⟶ D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  -- Both support maps arise from the identity on the same ambient chains.
  let F := relativeSingularChainsMap R (ContinuousMap.id X) (fun _ hx ↦ h hx)
  let G := (singularCochainDualFunctor R).map F.op
  let JA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  have hchain : relativeSingularChainsProjection R A ≫ F =
      relativeSingularChainsProjection R B := by
    simp [F, relativeSingularChainsProjection, relativeSingularChainsMap]
  have hdual : G ≫ JA = JB := by
    change (singularCochainDualFunctor R).map _ ≫ (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp]
    change (singularCochainDualFunctor R).map
      (relativeSingularChainsProjection R A ≫ F).op = _
    rw [hchain]
  -- Their cochain restrictions agree before quotienting, hence so do their absolute cap chains.
  have hcap (α : (relativeSingularCochains R B).X p)
      (c : (relativeSingularChains R A).X (p + q)) :
      relativeSingularCochainCap R A p q (G.f p α) c =
        relativeSingularCochainCap R B p q α (F.f (p + q) c) := by
    obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((relativeSingularChainsProjection R A).f (p + q))).mp inferInstance c
    have hchainval := congrArg (fun f ↦ f.f (p + q) v) hchain
    change F.f (p + q) ((relativeSingularChainsProjection R A).f (p + q) v) =
      (relativeSingularChainsProjection R B).f (p + q) v at hchainval
    rw [hchainval, relativeSingularCochainCap_projection, relativeSingularCochainCap_projection]
    have hdualval := congrArg (fun f ↦ f.f p α) hdual
    change (relativeSingularCochainEquiv R A p (G.f p α)).val =
      (relativeSingularCochainEquiv R B p α).val at hdualval
    rw [hdualval]
  -- Pass this equality through the two original quotients using the same representatives.
  obtain ⟨α, hα⟩ := hrep (relativeSingularCochains R B) p a
  obtain ⟨c, hc⟩ := hrep (relativeSingularChains R A) (p + q) z
  change relativeSingularCocycleClass R B p α = a at hα
  change relativeSingularCycleClass R A (p + q) c = z at hc
  obtain ⟨α', hα'⟩ := hcycles (relativeSingularCochains R B)
    (relativeSingularCochains R A) G p α
  obtain ⟨c', hc'⟩ := hcycles (relativeSingularChains R A)
    (relativeSingularChains R B) F (p + q) c
  have ha := hclass (relativeSingularCochains R B) (relativeSingularCochains R A)
    G p α α' hα'.symm
  have hz := hclass (relativeSingularChains R A) (relativeSingularChains R B)
    F (p + q) c c' hc'.symm
  change relativeSingularCohomologyRestriction R A B h p
    (relativeSingularCocycleClass R B p α) = relativeSingularCocycleClass R A p α' at ha
  change relativeSingularHomologyInclusion R A B h (p + q)
    (relativeSingularCycleClass R A (p + q) c) = relativeSingularCycleClass R B (p + q) c' at hz
  rw [← hα, ← hc, ha, hz, relativeSingularCapProduct_cycleClass,
    relativeSingularCapProduct_cycleClass]
  congr 1
  apply Subtype.ext
  change relativeSingularCochainCap R A p q α'.val c.val =
    relativeSingularCochainCap R B p q α.val c'.val
  rw [hα', hc']
  exact hcap α.val c.val

end AtiyahSinger
