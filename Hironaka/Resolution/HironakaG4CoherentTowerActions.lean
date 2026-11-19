import Hironaka.Resolution.HironakaG34EquivariantLiftAction

/-!
# Coherent ambient actions along a whole equivariant blowup history

A chosen family of isomorphisms of the restricted complete tower determines
compatible maps at every prefix. The same choice is used at all stages, so
successive lifted actions commute with each actual blowup.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CoherentTowerActions
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HironakaG34MaskFoldEquivariance

variable {n : ℕ} {X : CMfd.{u} n} {A : Type*} (U V : A → Opens X)
  (φ : ∀ a, CMfd.of (n := n) (U a) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    CMfd.of (n := n) (V a))

/-- Actions at all prefixes, commuting with the actual blowups on their
source opens and preserving each next centre. -/
def CoherentHistory : {Y : CMfd.{u} n} → (T : BlowupTower X Y) → (A → Y → Y) → Prop
  | _, .refl, act => ∀ a (x : X) (hx : x ∈ U a),
      act a x = ((φ a ⟨x, hx⟩ : V a) : X) ∧ ContinuousAt (act a) x
  | _, .step T C π _, act' =>
      ∃ act, CoherentHistory T act ∧
        (∀ a y, T.proj y ∈ U a → (act a y ∈ C ↔ y ∈ C)) ∧
        ∀ a z, T.proj (π z) ∈ U a →
          π (act' a z) = act a (π z) ∧ ContinuousAt (act' a) z

/-- Extend a family of local tower isomorphisms by the identity on the
complement, retaining the very same lifts at every prefix. -/
theorem exists_coherent_of_tower_isomorphisms :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y)
      (χ : ∀ a, CMfd.of (n := n) (openPreimage T (U a)) ≃ₘ⟮𝓘(ℂ, ComplexModel n),
        𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T (V a))),
      (∀ a, IsTowerIso (φ a) (restrict (U a) T) (restrict (V a) T) (χ a)) →
      ∃ act, CoherentHistory U V φ T act ∧ ∀ a (p : openPreimage T (U a)),
        act a p = ((χ a p : openPreimage T (V a)) : Y) := by
  classical
  intro Y T
  induction T with
  | refl =>
    intro χ hχ
    let act : A → X → X := fun a x =>
      if hx : x ∈ U a then ((χ a ⟨x, hx⟩ : V a) : X) else x
    have hact : ∀ a (p : U a), act a p = ((χ a p : V a) : X) := by
      intro a p
      simp only [act, dif_pos p.2]
      cases p
      rfl
    refine ⟨act, ?_, hact⟩
    intro a x hx
    have hχeq : χ a = φ a := IsTowerIso.refl_inv (hχ a)
    have hcomp : ContinuousAt ((act a) ∘ (Subtype.val : U a → X)) ⟨x,hx⟩ := by
      have heq : ((act a) ∘ (Subtype.val : U a → X)) =
          (fun p : U a => ((χ a p : V a) : X)) := funext (hact a)
      rw [heq]
      exact (continuous_subtype_val.comp (χ a).contMDiff.continuous).continuousAt
    refine ⟨?_, (U a).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hcomp⟩
    rw [hact a ⟨x,hx⟩, hχeq]
    rfl
  | @step Y Z T C π hπ ih =>
    intro χ₁ hχ₁
    let χ := fun a => Classical.choose (IsTowerIso.step_inv (hχ₁ a))
    have hχ : ∀ a, IsTowerIso (φ a) (restrict (U a) T) (restrict (V a) T) (χ a) :=
      fun a => (Classical.choose_spec (IsTowerIso.step_inv (hχ₁ a))).1
    obtain ⟨act, hhistory, hact⟩ := ih χ hχ
    let act' : A → Z → Z := fun a z =>
      if hz : z ∈ openPreimage (.step T C π hπ) (U a) then
        ((χ₁ a ⟨z, hz⟩ : openPreimage (.step T C π hπ) (V a)) : Z) else z
    have hact' : ∀ a (p : openPreimage (.step T C π hπ) (U a)), act' a p =
        ((χ₁ a p : openPreimage (.step T C π hπ) (V a)) : Z) := by
      intro a p
      simp only [act', dif_pos p.2]
    refine ⟨act', ⟨act, hhistory, ?_, ?_⟩, hact'⟩
    · intro a y hy
      have hy' : y ∈ openPreimage T (U a) := hy
      have hC := (Classical.choose_spec (IsTowerIso.step_inv (hχ₁ a))).2.2
      rw [hact a ⟨y,hy'⟩]
      exact Set.ext_iff.mp hC ⟨y,hy'⟩
    · intro a z hz
      have hz' : z ∈ openPreimage (.step T C π hπ) (U a) := hz
      have hcomp : ContinuousAt ((act' a) ∘
          (Subtype.val : openPreimage (.step T C π hπ) (U a) → Z)) ⟨z,hz'⟩ := by
        have heq : ((act' a) ∘ (Subtype.val : openPreimage (.step T C π hπ) (U a) → Z)) =
            (fun p : openPreimage (.step T C π hπ) (U a) =>
              ((χ₁ a p : openPreimage (.step T C π hπ) (V a)) : Z)) := funext (hact' a)
        rw [heq]
        exact (continuous_subtype_val.comp (χ₁ a).contMDiff.continuous).continuousAt
      have hcont : ContinuousAt (act' a) z :=
        (openPreimage (.step T C π hπ) (U a)).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hcomp
      refine ⟨?_, hcont⟩
      have hstep := (Classical.choose_spec (IsTowerIso.step_inv (hχ₁ a))).2.1 ⟨z,hz'⟩
      have hstep' := congrArg (fun p : openPreimage T (V a) => (p : Y)) hstep
      rw [hact' a ⟨z,hz'⟩, hact a ⟨π z,hz⟩]
      exact hstep'

/-- Equivariance supplies the isomorphisms and hence a single coherent
family of actual actions along the entire history. -/
theorem exists_coherent_of_equivariant {N : Set X} {E : List (Set X)}
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hEq : IsEquivariant N E T)
    (hN : ∀ a (p : U a), ((φ a p : V a) : X) ∈ N ↔ (p : X) ∈ N)
    (hE : ∀ a H, H ∈ E → ∀ p : U a, ((φ a p : V a) : X) ∈ H ↔ (p : X) ∈ H) :
    ∃ act, CoherentHistory U V φ T act := by
  classical
  let χ := fun a => Classical.choose (hEq (U a) (V a) (φ a) (hN a) (hE a))
  have hχ := fun a => Classical.choose_spec (hEq (U a) (V a) (φ a) (hN a) (hE a))
  obtain ⟨act, hact, -⟩ := exists_coherent_of_tower_isomorphisms U V φ T χ hχ
  exact ⟨act, hact⟩

end
end Hironaka.HironakaG4CoherentTowerActions
