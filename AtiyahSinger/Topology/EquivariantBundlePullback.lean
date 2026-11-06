/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.EquivariantVectorBundle

/-!
# Equivariant pullback on the original bundle fibers

Public module ID: M1767.

An equivariant continuous map of bases pulls back the specified action on an
original complex bundle. The fiber over y is exactly E(f(y)), and the action
uses only the equality f(g*y)=g*f(y) to transport its target. Joint continuity
uses the native induced pullback topology. Original bundle maps and isomorphisms
retain their existing pullbacks, with the two pulled actions specified explicitly.

Sources: SG I.9, p.59, for bundle pullback and contravariance; Atiyah--Singer I,
Section 2, printed pp.494--495, for the equivariant extension. The explicit
continuous-action certificates on general topological groups and bases are
project supplements, not claims that the sources state this full generality.
No finite rank, compactness, local compactness or separation assumption is used.
The action laws, joint continuity and equivariance of the specified maps are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- The original moving-fiber map with target transported along the supplied base equivariance. -/
def EquivariantStructure.pullbackLinearMap (ρ : EquivariantStructure G E)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (g : G) (y : Y) :
    ((f : Y → X) *ᵖ E) y →ₗ[ℂ] ((f : Y → X) *ᵖ E) (g • y) := by
  change E (f y) →ₗ[ℂ] E (f (g • y))
  rw [heq g y]
  exact ρ.linearMap g (f y)

/-- The transported maps obey the action laws and are continuous in the native pullback topology. -/
theorem EquivariantStructure.pullback_properties (ρ : EquivariantStructure G E)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    (∀ (y : Y) (v : ((f : Y → X) *ᵖ E) y),
      (⟨(1 : G) • y, ρ.pullbackLinearMap f heq 1 y v⟩ :
        TotalSpace Unit ((f : Y → X) *ᵖ E)) = ⟨y, v⟩) ∧
    (∀ (g h : G) (y : Y) (v : ((f : Y → X) *ᵖ E) y),
      (⟨(g * h) • y, ρ.pullbackLinearMap f heq (g * h) y v⟩ :
        TotalSpace Unit ((f : Y → X) *ᵖ E)) =
      ⟨g • (h • y),
        ρ.pullbackLinearMap f heq g (h • y) (ρ.pullbackLinearMap f heq h y v)⟩) ∧
    Continuous (fun p : G × TotalSpace Unit ((f : Y → X) *ᵖ E) ↦
      (⟨p.1 • p.2.proj, ρ.pullbackLinearMap f heq p.1 p.2.proj p.2.snd⟩ :
        TotalSpace Unit ((f : Y → X) *ᵖ E))) := by
  /- Stage 1: the base coordinate obeys the given action laws on Y. Under
  Pullback.lift f, the displayed action sends (y,v) to the original action
  on (f(y),v); heq supplies precisely the target equality. Apply the original
  identity and multiplication laws and combine them with the base equations.
  Stage 2: the native pullback topology is induced jointly by its projection
  to Y and its lift to the original total space of E. The first component
  of the action is continuous by ContinuousSMul G Y. The second is the original
  jointly continuous action composed with the continuous pullback lift. These
  two components prove continuity without a chosen frame or replacement topology. -/
  -- The target transport changes only the base label of the original total vector.
  have hlift (g : G) (y : Y) (v : E (f y)) :
      (⟨f (g • y), ρ.pullbackLinearMap f heq g y v⟩ : TotalSpace Unit E) =
        ⟨g • f y, ρ.linearMap g (f y) v⟩ := by
    have hcast (a b : X) (hab : a = b) (L : E (f y) →ₗ[ℂ] E b) :
        (⟨a, (Eq.mpr (congrArg (fun x ↦ E (f y) →ₗ[ℂ] E x) hab) L) v⟩ :
          TotalSpace Unit E) = ⟨b, L v⟩ := by
      subst b
      rfl
    exact hcast (f (g • y)) (g • f y) (heq g y) (ρ.linearMap g (f y))
  have hext {u v : TotalSpace Unit ((f : Y → X) *ᵖ E)}
      (hbase : u.proj = v.proj) (hvector : Pullback.lift f u = Pullback.lift f v) :
      u = v := by
    rcases u with ⟨x, u⟩
    rcases v with ⟨y, v⟩
    dsimp only at hbase
    subst y
    exact congrArg (fun w ↦ (⟨x, w⟩ : TotalSpace Unit ((f : Y → X) *ᵖ E)))
      (TotalSpace.mk_injective (f x) hvector)
  refine ⟨?_, ?_, ?_⟩
  · -- Combine the base identity with the identity of the lifted original action.
    intro y v
    apply hext (one_smul G y)
    exact (hlift 1 y v).trans (ρ.one_map (f y) v)
  · intro g h y v
    apply hext (mul_smul g h y)
    calc
      (⟨f ((g * h) • y), ρ.pullbackLinearMap f heq (g * h) y v⟩ :
          TotalSpace Unit E) =
          ⟨(g * h) • f y, ρ.linearMap (g * h) (f y) v⟩ := hlift (g * h) y v
      _ = ⟨g • (h • f y), ρ.linearMap g (h • f y) (ρ.linearMap h (f y) v)⟩ :=
        ρ.mul_map g h (f y) v
      _ = ⟨g • f (h • y), ρ.linearMap g (f (h • y))
          (ρ.pullbackLinearMap f heq h y v)⟩ :=
        congrArg (fun z : TotalSpace Unit E ↦
          (⟨g • z.proj, ρ.linearMap g z.proj z.snd⟩ : TotalSpace Unit E))
          (hlift h y v).symm
      _ = ⟨f (g • (h • y)), ρ.pullbackLinearMap f heq g (h • y)
          (ρ.pullbackLinearMap f heq h y v)⟩ :=
        (hlift g (h • y) (ρ.pullbackLinearMap f heq h y v)).symm
  · -- Continuity is tested by the original base projection and bundle lift.
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
    have hcont := (continuous_fst.smul
      ((Pullback.continuous_proj Unit E f).comp continuous_snd)).prodMk
      (ρ.continuous_action.comp (continuous_fst.prodMk
        ((Pullback.continuous_lift Unit E f).comp continuous_snd)))
    apply hcont.congr
    intro p
    exact Prod.ext rfl (hlift p.1 p.2.proj p.2.snd).symm

/-- Pullback equips the original pullback bundle with the specified transported action. -/
def EquivariantStructure.pullback (ρ : EquivariantStructure G E)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    EquivariantStructure G ((f : Y → X) *ᵖ E) where
  linearMap := ρ.pullbackLinearMap f heq
  one_map := (ρ.pullback_properties f heq).1
  mul_map := (ρ.pullback_properties f heq).2.1
  continuous_action := (ρ.pullback_properties f heq).2.2

variable {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- The existing pullbacks of the same bundle maps and isomorphisms preserve equivariance. -/
theorem EquivariantStructure.pullback_maps
    (ρE : EquivariantStructure G E) (ρF : EquivariantStructure G F)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    (∀ (a : Hom E F), a.IsEquivariant ρE ρF →
      (a.pullback f).IsEquivariant (ρE.pullback f heq) (ρF.pullback f heq)) ∧
    (∀ (e : Iso E F), e.IsEquivariant ρE ρF →
      (e.pullback f).IsEquivariant (ρE.pullback f heq) (ρF.pullback f heq)) := by
  /- Stage 1: at y the existing Hom.pullback uses the original map at f(y).
  Its intertwining square is the supplied square at f(y), with both target
  fibers transported along the same heq g y. Thus the original map, not a
  newly chosen equivariant replacement, intertwines the actual pulled actions.
  Stage 2: the existing Iso.pullback has that same forward map on each fiber.
  Apply the Hom conclusion to the original forward isomorphism and its supplied
  equivariance. The existing inverse and total-space continuity remain unchanged. -/
  -- Transport the given intertwining square along the same base equality on both sides.
  have hmaps (a : Hom E F) (ha : a.IsEquivariant ρE ρF) :
      (a.pullback f).IsEquivariant (ρE.pullback f heq) (ρF.pullback f heq) := by
    intro g y v
    have htransport (x z : X) (hxz : x = z)
        (LE : E (f y) →ₗ[ℂ] E z) (LF : F (f y) →ₗ[ℂ] F z)
        (hsquare : ∀ w, a.linearMap z (LE w) = LF (a.linearMap (f y) w)) :
        a.linearMap x
            ((Eq.mpr (congrArg (fun b ↦ E (f y) →ₗ[ℂ] E b) hxz) LE) v) =
          (Eq.mpr (congrArg (fun b ↦ F (f y) →ₗ[ℂ] F b) hxz) LF)
            (a.linearMap (f y) v) := by
      subst z
      exact hsquare v
    exact htransport (f (g • y)) (g • f y) (heq g y)
      (ρE.linearMap g (f y)) (ρF.linearMap g (f y)) (ha g (f y))
  refine ⟨hmaps, ?_⟩
  -- The existing isomorphism pullback has exactly this same forward bundle map.
  intro e he
  exact hmaps e.toHom he

end AtiyahSinger.ComplexBundle
