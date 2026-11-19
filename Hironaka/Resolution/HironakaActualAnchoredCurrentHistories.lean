import Hironaka.Resolution.HironakaActualGeneratedCurrentHistories

/-! Extract the ACTUAL initial comparison from generated different histories.
Pure anchored geometry can then transplant new literal records from ONE
initial identity, without requiring a naturality law for all possible maps.
Chosen tangent functions and original strict carriers can use this anchor;
their actual transport and all recursive values remain separate obligations. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualAnchoredCurrentHistories
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism HironakaActualGeneratedCurrentHistories
variable {n : ℕ} {X X' : CMfd.{u} n}

inductive Anchored (V₀ : Opens X) (V₀' : Opens X')
    (φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀') :
    {Y Y' : CMfd.{u} n} → BlowupTower X Y → BlowupTower X' Y' →
      (U : Opens Y) → (U' : Opens Y') →
      (CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U') → Prop
  | initial : Anchored V₀ V₀' φ .refl .refl V₀ V₀' φ
  | shrink {Y Y' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
      {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η)
      (V : Opens Y) (V' : Opens Y') (hV : (V : Set Y)⊆U) (hV' : (V' : Set Y')⊆U')
      (htr : η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' (V' : Set Y'))=
        (Subtype.val : U → Y) ⁻¹' (V : Set Y)) :
      Anchored V₀ V₀' φ S T V V' (restrictComparison η V V' hV hV' htr)
  | step {Y Y' Z Z' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
      {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η)
      {C : Set Y} {C' : Set Y'} {π : Z → Y} {π' : Z' → Y'}
      (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong n C' π')
      (hC : η ⁻¹' ((Subtype.val : U' → Y') ⁻¹' C')=(Subtype.val : U → Y) ⁻¹' C) :
      Anchored V₀ V₀' φ (.step S C π hπ) (.step T C' π' hπ')
        (BlowupBiholomorphismLift.preOpen hπ U) (BlowupBiholomorphismLift.preOpen hπ' U')
        (nextComparison hπ hπ' U U' η hC)

theorem exists_actual_initial_anchor {A : MarkedIdeal n X} {B : MarkedIdeal n X'}
    {Y Y' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Generated A B S T U U' η) :
    ∃(V₀ : Opens X)(V₀' : Opens X')
      (φ : CMfd.of (n := n) V₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V₀'),
      MarkedIdeal.pullback (Subtype.val : V₀ → X) A=
        MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V₀' → X') B) ∧
      Anchored V₀ V₀' φ S T U U' η := by
  induction H with
  | initial V V' φ hrec => exact ⟨V,V',φ,hrec,Anchored.initial⟩
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    obtain ⟨V₀,V₀',φ,hrec,hG⟩ := ih
    exact ⟨V₀,V₀',φ,hrec,Anchored.shrink hG V V' hV hV' htr⟩
  | @step Y Y' Z Z' S T U U' η H C C' hAdm' π π' hπ hπ' hC ih =>
    obtain ⟨V₀,V₀',φ,hrec,hG⟩ := ih
    exact ⟨V₀,V₀',φ,hrec,Anchored.step hG hπ hπ' hC⟩

theorem Anchored.to_generated {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {Y Y' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η)
    (A : MarkedIdeal n X) (B : MarkedIdeal n X')
    (hInitial : MarkedIdeal.pullback (Subtype.val : V₀ → X) A=
      MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : V₀' → X') B))
    (hT : IsGeoTestTower B T) : Generated A B S T U U' η := by
  revert hT
  induction H with
  | initial => intro _;exact Generated.initial V₀ V₀' φ hInitial
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    intro ht
    exact Generated.shrink (ih ht) V V' hV hV' htr
  | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
    intro ht
    exact Generated.step (ih ht.1) ht.2 hπ hπ' hC

theorem Anchored.source_mem_initial {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {Y Y' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η) :
    ∀z : U,S.proj z.val∈V₀ := by
  induction H with
  | initial => intro z;exact z.property
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    intro z
    exact ih ⟨z.val,hV z.property⟩
  | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
    intro z
    exact ih ⟨π z.val,z.property⟩

theorem Anchored.target_mem_initial {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {Y Y' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η) :
    ∀z : U',T.proj z.val∈V₀' := by
  induction H with
  | initial => intro z;exact z.property
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    intro z
    exact ih ⟨z.val,hV' z.property⟩
  | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
    intro z
    exact ih ⟨π' z.val,z.property⟩

theorem Anchored.projection_square {V₀ : Opens X} {V₀' : Opens X'} {φ}
    {Y Y' : CMfd.{u} n} {S : BlowupTower X Y} {T : BlowupTower X' Y'}
    {U : Opens Y} {U' : Opens Y'} {η} (H : Anchored V₀ V₀' φ S T U U' η) :
    ∀z : U,T.proj (η z).val=(φ ⟨S.proj z.val,H.source_mem_initial z⟩).val := by
  induction H with
  | initial => intro z;rfl
  | @shrink Y Y' S T U U' η H V V' hV hV' htr ih =>
    intro z
    exact ih ⟨z.val,hV z.property⟩
  | @step Y Y' Z Z' S T U U' η H C C' π π' hπ hπ' hC ih =>
    intro z
    change T.proj (π' (nextComparison hπ hπ' U U' η hC z).val)=_
    rw [nextComparison_square hπ hπ' U U' η hC z]
    exact ih ⟨π z.val,z.property⟩

 end
end Hironaka.HironakaActualAnchoredCurrentHistories
