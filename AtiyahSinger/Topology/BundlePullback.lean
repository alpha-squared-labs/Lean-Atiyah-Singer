/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIso

/-!
# Pullbacks with the existing mathlib total-space topology

Public module ID: M1590.

D07/K01. Use Bundle.Pullback and its induced topology, with phantom model Unit.
Local finite rank is pulled back along continuous maps, without compactness.
The identity and composition comparisons retain the same underlying fiber vector.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {E : Y → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : Y → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- The additive group on a pulled-back fiber is exactly the original fiber group. -/
instance pullbackAddCommGroup (f : X → Y) (x : X) : AddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (AddCommGroup (E (f x)))

variable (f : C(X, Y))

/-- Continuous pullback preserves local finite complex rank. -/
theorem isFiniteRank_pullback [IsFiniteRank E] : IsFiniteRank ((f : X → Y) *ᵖ E) := by
  /- Pull each local linear trivialization back along f. Its open base set is the
  inverse image of the original base set. The induced total-space topology gives
  a homeomorphism to that open set times the same finite coordinate space. -/
  classical
  constructor
  intro x
  obtain ⟨r, e, he, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) (f x)
  -- Keep the original total-space point when transporting the inverse fiber vector.
  let g : X × (Fin r → ℂ) → TotalSpace Unit ((f : X → Y) *ᵖ E) :=
    fun y ↦ if hy : f y.1 ∈ e.baseSet then
      ⟨y.1, cast (congrArg E (e.proj_symm_apply' hy))
        (e.toPartialEquiv.symm (f y.1, y.2)).snd⟩
    else ⟨y.1, 0⟩
  have hgproj (y : X × (Fin r → ℂ)) : (g y).proj = y.1 := by
    dsimp [g]
    split_ifs <;> rfl
  have hglift (y : X × (Fin r → ℂ)) (hy : f y.1 ∈ e.baseSet) :
      Pullback.lift f (g y) = e.toPartialEquiv.symm (f y.1, y.2) := by
    dsimp only [g]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  -- Construct the usual pullback chart in the original Unit-phantom total topology.
  let t : Trivialization (Fin r → ℂ) (π Unit ((f : X → Y) *ᵖ E)) :=
    { toFun := fun z ↦ (z.proj, (e (Pullback.lift f z)).2)
      invFun := g
      source := Pullback.lift f ⁻¹' e.source
      baseSet := f ⁻¹' e.baseSet
      target := (f ⁻¹' e.baseSet) ×ˢ Set.univ
      map_source' := by
        intro x hx
        simp only [e.source_eq, Set.mem_preimage, Pullback.lift_proj] at hx
        exact ⟨hx, Set.mem_univ _⟩
      map_target' := by
        intro y hy
        simp only [e.source_eq, Set.mem_preimage, Pullback.lift_proj, hgproj]
        exact hy.1
      left_inv' := by
        intro x hx
        have hbase : f x.proj ∈ e.baseSet := e.mem_source.mp hx
        apply TotalSpace.ext (hgproj _)
        have hpoint := (hglift (x.proj, (e (Pullback.lift f x)).2) hbase).trans
          (e.symm_apply_mk_proj hx)
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd) hpoint
      right_inv' := by
        intro y hy
        apply Prod.ext
        · exact hgproj y
        · change (e (Pullback.lift f (g y))).2 = y.2
          rw [hglift y hy.1]
          exact congrArg (fun p : Y × (Fin r → ℂ) ↦ p.2)
            (e.apply_symm_apply' (x := y.2) hy.1)
      open_source := by
        rw [e.source_eq]
        exact e.open_baseSet.preimage
          (f.continuous.comp (Pullback.continuous_proj Unit E f))
      open_target := (e.open_baseSet.preimage f.continuous).prod isOpen_univ
      open_baseSet := e.open_baseSet.preimage f.continuous
      continuousOn_toFun :=
        (Pullback.continuous_proj Unit E f).continuousOn.prodMk
          (continuous_snd.comp_continuousOn
            (e.toOpenPartialHomeomorph.continuousOn.comp
              (Pullback.continuous_lift Unit E f).continuousOn Set.Subset.rfl))
      continuousOn_invFun := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuousOn_iff]
        refine (continuousOn_fst.prodMk
          (e.toOpenPartialHomeomorph.continuousOn_symm.comp
            (f.continuous.prodMap continuous_id).continuousOn
            (fun y hy ↦ e.mem_target.mpr hy.1))).congr ?_
        intro y hy
        exact Prod.ext (hgproj y) (hglift y hy.1)
      source_eq := by rw [e.source_eq]; rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  refine ⟨r, t, he, ?_⟩
  intro y hy
  exact hlinear (f y) hy

attribute [local instance] isFiniteRank_pullback

/-- The fiberwise pulled-back map is continuous in the induced total topology. -/
theorem Hom.continuous_pullback (a : Hom E F) :
    Continuous (fun z : TotalSpace Unit ((f : X → Y) *ᵖ E) ↦
      (⟨z.proj, a.linearMap (f z.proj) z.snd⟩ :
        TotalSpace Unit ((f : X → Y) *ᵖ F))) := by
  /- A map into a pullback total space is continuous if its base projection and
  its lift to the old total space are continuous. The former is unchanged, and
  the latter is the composite of the original lift with the total map of a. -/
  -- Continuity into the original pullback is tested by projection and original lift.
  rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
  exact (Pullback.continuous_proj Unit E f).prodMk
    (a.continuous_total.comp (Pullback.continuous_lift Unit E f))

/-- Pull a bundle map back by applying its fiber map at f(x). -/
def Hom.pullback (a : Hom E F) : Hom ((f : X → Y) *ᵖ E) ((f : X → Y) *ᵖ F) where
  linearMap x := a.linearMap (f x)
  continuous_total := a.continuous_pullback f

/-- Pullback of a bundle isomorphism, with both directions specified. -/
def Iso.pullback (e : Iso E F) : Iso ((f : X → Y) *ᵖ E) ((f : X → Y) *ᵖ F) where
  linearEquiv x := e.linearEquiv (f x)
  continuous_total := e.toHom.continuous_pullback f
  continuous_symm := e.symm.toHom.continuous_pullback f

/-- Pullback keeps the original map on the fiber at the image point. -/
theorem Hom.pullback_apply (a : Hom E F) (x : X) (v : E (f x)) :
    (a.pullback f).linearMap x v = a.linearMap (f x) v := by
  /- Unfold the pulled-back family of linear maps. Evaluation uses precisely f(x),
  with the same vector v in the original fiber, and introduces no chosen trivialization. -/
  rfl

/-- Pullback preserves identity bundle maps. -/
theorem Hom.pullback_id : (Hom.id E).pullback f = Hom.id ((f : X → Y) *ᵖ E) := by
  /- Use extensionality on the pulled-back fibers. Both sides are the identity map
  on E(f(x)), so the two bundle structures differ only in proof-irrelevant certificates. -/
  apply Hom.ext
  intro x
  rfl

variable {G : Y → Type*} [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- Pullback preserves composition of bundle maps. -/
theorem Hom.pullback_comp (a : Hom E F) (b : Hom F G) :
    (b.comp a).pullback f = (b.pullback f).comp (a.pullback f) := by
  /- At x both maps are the composite of a and b on the fiber over f(x).
  Apply extensionality of bundle maps and the defining composition of linear maps. -/
  apply Hom.ext
  intro x
  rfl

attribute [local instance] sectionModule

/-- A section pulled back by evaluation at f(x) is continuous. -/
theorem continuous_pullback_section [IsFiniteRank E] (s : continuousSections E) :
    Continuous (fun x ↦ (⟨x, s.val (f x)⟩ : TotalSpace Unit ((f : X → Y) *ᵖ E))) := by
  /- Use the defining induced topology: the base component is the identity on X,
  and the lift to E is the composite of the continuous section s with f. These
  two continuous components prove continuity into the pullback total space. -/
  -- The lifted section is the old section composed with the original base map.
  rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
  exact continuous_id.prodMk (s.property.comp f.continuous)

/-- Pullback of an actual section, retaining its values in the original fibers. -/
def pullbackSection [IsFiniteRank E] (s : continuousSections E) :
    continuousSections ((f : X → Y) *ᵖ E) :=
  ⟨fun x ↦ s.val (f x), continuous_pullback_section f s⟩

/-- Section pullback is semilinear over precomposition of scalar functions. -/
theorem pullbackSection_smul [IsFiniteRank E] (c : C(Y, ℂ)) (s : continuousSections E) :
    pullbackSection f (c • s) = c.comp f • pullbackSection f s := by
  /- Evaluate each section at x. The left side is c(f(x)) times s(f(x)), and the
  right side is the same expression by the evaluated scalar module action. The
  scalar ring changes from C(Y,ℂ) to C(X,ℂ), so this is not a same-ring linear map. -/
  apply Subtype.ext
  funext x
  rfl

/-- Section pullback commutes with the specified bundle map. -/
theorem pullbackSection_natural [IsFiniteRank E] [IsFiniteRank F]
    (a : Hom E F) (s : continuousSections E) :
    pullbackSection f (a.sectionMap s) = (a.pullback f).sectionMap (pullbackSection f s) := by
  /- At each x both sides apply a on the fiber over f(x) to the value s(f(x)).
  Extensionality of sections gives naturality without any scalar-extension identification. -/
  apply Subtype.ext
  funext x
  rfl

variable [hE : IsFiniteRank E]

include hE

/-- The identity pullback admits the canonical vector-preserving isomorphism. -/
theorem exists_pullback_id_iso :
    ∃ e : Iso (((ContinuousMap.id Y : C(Y, Y)) : Y → Y) *ᵖ E) E,
      ∀ y v, e.linearEquiv y v = v := by
  /- The fiber map is the identity. Its forward total map is the canonical lift;
  the inverse sends (y,v) to the same pair in the pullback. Continuity of the inverse
  uses continuity of the original projection, obtained from local triviality. -/
  -- Both fiber maps are the actual identity; the induced pullback controls continuity.
  let e : Iso (((ContinuousMap.id Y : C(Y, Y)) : Y → Y) *ᵖ E) E :=
    { linearEquiv := fun y ↦ LinearEquiv.refl ℂ (E y)
      continuous_total := Pullback.continuous_lift Unit E (ContinuousMap.id Y)
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E (ContinuousMap.id Y)).continuous_iff]
        exact (continuous_proj (E := E)).prodMk continuous_id }
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- Canonical identity comparison, chosen only from the vector-preserving theorem. -/
def pullbackIdIso : Iso (((ContinuousMap.id Y : C(Y, Y)) : Y → Y) *ᵖ E) E :=
  (exists_pullback_id_iso (E := E)).choose

/-- The chosen identity comparison acts as identity on each fiber. -/
theorem pullbackIdIso_apply (y : Y) (v : E y) :
    (pullbackIdIso (E := E)).linearEquiv y v = v := by
  /- Use the characterization carried by the existence theorem used to choose the
  identity comparison. The choice selects a certificate, not an arbitrary fiber automorphism. -/
  exact (exists_pullback_id_iso (E := E)).choose_spec y v

omit hE in
/-- Iterated and composite pullbacks have a vector-preserving isomorphism. -/
theorem exists_pullback_comp_iso (g : C(Z, X)) :
    ∃ e : Iso ((g : Z → X) *ᵖ ((f : X → Y) *ᵖ E))
      (((f.comp g : C(Z, Y)) : Z → Y) *ᵖ E),
      ∀ z v, e.linearEquiv z v = v := by
  /- Both fibers are E(f(g(z))). The total topologies are induced by the base and
  the lift into E; the intermediate X component is g of the Z component and is
  therefore continuous. The identity fiber maps are continuous in both directions. -/
  -- The forward lift forgets the intermediate base point, which is already g(z).
  let e : Iso ((g : Z → X) *ᵖ ((f : X → Y) *ᵖ E))
      (((f.comp g : C(Z, Y)) : Z → Y) *ᵖ E) :=
    { linearEquiv := fun z ↦ LinearEquiv.refl ℂ (E (f (g z)))
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E (f.comp g)).continuous_iff]
        exact (Pullback.continuous_proj Unit ((f : X → Y) *ᵖ E) g).prodMk
          ((Pullback.continuous_lift Unit E f).comp
            (Pullback.continuous_lift Unit ((f : X → Y) *ᵖ E) g))
      continuous_symm := by
        -- Recover the intermediate base as g of the original Z base projection.
        rw [(inducing_pullbackTotalSpaceEmbedding Unit ((f : X → Y) *ᵖ E) g).continuous_iff]
        apply (Pullback.continuous_proj Unit E (f.comp g)).prodMk
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
        exact (g.continuous.comp (Pullback.continuous_proj Unit E (f.comp g))).prodMk
          (Pullback.continuous_lift Unit E (f.comp g)) }
  exact ⟨e, fun _ _ ↦ rfl⟩

omit hE in
/-- Canonical comparison between iterated pullback and pullback of a composite. -/
def pullbackCompIso (g : C(Z, X)) :
    Iso ((g : Z → X) *ᵖ ((f : X → Y) *ᵖ E))
      (((f.comp g : C(Z, Y)) : Z → Y) *ᵖ E) :=
  (exists_pullback_comp_iso (E := E) f g).choose

omit hE in
/-- The composite-pullback comparison keeps each actual fiber vector. -/
theorem pullbackCompIso_apply (g : C(Z, X)) (z : Z) (v : E (f (g z))) :
    (pullbackCompIso (E := E) f g).linearEquiv z v = v := by
  /- Apply the defining characterization of the chosen composition comparison.
  It is a vector-preserving identification of induced topologies, not a change of local frames. -/
  exact (exists_pullback_comp_iso (E := E) f g).choose_spec z v

end AtiyahSinger.ComplexBundle
