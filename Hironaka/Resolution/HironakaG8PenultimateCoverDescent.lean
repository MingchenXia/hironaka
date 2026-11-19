import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction

/-! Descend the penultimate diffeomorphism from actual local tower comparisons. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8PenultimateCoverDescent

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HironakaSharpActualCurveComparisonRestriction

variable {n : ℕ} {X X' A B Y Z : CMfd.{0} n}
local notation "𝓘c" => 𝓘(ℂ, ComplexModel n)

/-- Fixed local penultimate maps covering a commuting terminal square
descend uniquely, and the descended map reads back every supplied local map. -/
theorem exists_penultimate_diffeomorph_of_cover
    {I : Type*} (U : I → Opens A) (V : I → Opens B)
    (hU : ∀ x : A, ∃ i, x ∈ U i) (hV : ∀ y : B, ∃ i, y ∈ V i)
    (π : Y → A) (ρ : Z → B) (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (g : ∀ i, CMfd.of (n := n) (U i) ≃ₘ⟮𝓘c,𝓘c⟯ CMfd.of (n := n) (V i))
    (hSquare : ∀ i (z : Y) (hz : π z ∈ U i), ρ (e z) = (g i ⟨π z,hz⟩).val)
    (hTrace : ∀ i (z : Y), ρ (e z) ∈ V i → π z ∈ U i) :
    ∃ f : A ≃ₘ⟮𝓘c,𝓘c⟯ B,
      (∀ z, ρ (e z) = f (π z)) ∧ ∀ i (x : U i), f x.val = (g i x).val := by
  classical
  let F (x : A) : B := ρ (e (hπ x).choose)
  have hLocal (i : I) (x : U i) : F x.val = (g i x).val := by
    have hx := (hπ x.val).choose_spec
    have hh := hSquare i (hπ x.val).choose (hx.symm ▸ x.property)
    change ρ (e (hπ x.val).choose) = (g i x).val
    exact hh.trans (congrArg (fun p : U i => (g i p).val) (Subtype.ext hx))
  have hF (z : Y) : ρ (e z) = F (π z) := by
    obtain ⟨i,hi⟩ := hU (π z)
    exact (hSquare i z hi).trans (hLocal i ⟨π z,hi⟩).symm
  have hInj : Function.Injective F := by
    intro x y hxy
    obtain ⟨i,hi⟩ := hU x
    obtain ⟨z,rfl⟩ := hπ y
    have hz : ρ (e z) ∈ V i := by
      rw [hF,← hxy,hLocal i ⟨x,hi⟩]
      exact (g i ⟨x,hi⟩).property
    let hy := hTrace i z hz
    have hh : g i ⟨x,hi⟩ = g i ⟨π z,hy⟩ := by
      apply Subtype.ext
      exact (hLocal i ⟨x,hi⟩).symm.trans (hxy.trans (hLocal i ⟨π z,hy⟩))
    exact congrArg Subtype.val ((g i).injective hh)
  have hSurj : Function.Surjective F := by
    intro y
    obtain ⟨z,rfl⟩ := hρ y
    exact ⟨π (e.symm z),by rw [← hF,e.apply_symm_apply]⟩
  let E := Equiv.ofBijective F ⟨hInj,hSurj⟩
  have hInv (i : I) (y : V i) : E.symm y.val = ((g i).symm y).val := by
    apply E.injective
    change E (E.symm y.val) = F ((g i).symm y).val
    rw [E.apply_symm_apply,hLocal i ((g i).symm y),(g i).apply_symm_apply]
  have hSmooth : ContMDiff 𝓘c 𝓘c ∞ F := by
    intro x
    obtain ⟨i,hi⟩ := hU x
    apply (contMDiffAt_subtype_iff (x := (⟨x,hi⟩ : U i))).mp
    have hEq : ((fun x : U i => F x.val) : U i → B) = (Subtype.val : V i → B) ∘ g i :=
      funext (hLocal i)
    rw [hEq]
    exact (contMDiff_subtype_val.comp (g i).contMDiff).contMDiffAt
  have hInvSmooth : ContMDiff 𝓘c 𝓘c ∞ E.symm := by
    intro y
    obtain ⟨i,hi⟩ := hV y
    apply (contMDiffAt_subtype_iff (x := (⟨y,hi⟩ : V i))).mp
    have hEq : ((fun x : V i => E.symm x.val) : V i → A) = (Subtype.val : U i → A) ∘ (g i).symm :=
      funext (hInv i)
    rw [hEq]
    exact (contMDiff_subtype_val.comp (g i).symm.contMDiff).contMDiffAt
  exact ⟨⟨E,hSmooth,hInvSmooth⟩,hF,hLocal⟩


/-- The strict comparisons on one literal base open use the fixed ambient
endpoint map on underlying points. -/
def LocalStrictComparison
    (f : X ≃ₘ⟮𝓘c,𝓘c⟯ X') (S : BlowupTower X Y) (T : BlowupTower X' Z)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z) (U : Opens X') : Prop :=
  ∃ eU : CMfd.of (n := n) (openPreimage S (preimageOpen f U)) ≃ₘ⟮𝓘c,𝓘c⟯
      CMfd.of (n := n) (openPreimage T U),
    (∀ z, (eU z).val = e z.val) ∧
    IsTowerIso (openRestriction f (preimageOpen f U) U rfl)
      (restrict (preimageOpen f U) S) (restrict U T) eU

private theorem strict_step_data
    {f : X ≃ₘ⟮𝓘c,𝓘c⟯ X'} {S : BlowupTower X A} {T : BlowupTower X' B}
    {C : Set A} {D : Set B} {π : Y → A} {ρ : Z → B}
    {hπ : IsBlowupAlong n C π} {hρ : IsBlowupAlong n D ρ}
    {e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z}
    (h : IsTowerIso f (.step S C π hπ) (.step T D ρ hρ) e) :
    ∃ g : A ≃ₘ⟮𝓘c,𝓘c⟯ B, IsTowerIso f S T g ∧
      (∀ z, ρ (e z) = g (π z)) ∧ g ⁻¹' D = C := by
  cases h with
  | step hBefore _ _ _ hComm hCentre => exact ⟨_,hBefore,hComm,hCentre⟩

private theorem local_step_data
    {f : X ≃ₘ⟮𝓘c,𝓘c⟯ X'} {S : BlowupTower X A} {T : BlowupTower X' B}
    {C : Set A} {D : Set B} {π : Y → A} {ρ : Z → B}
    {hπ : IsBlowupAlong n C π} {hρ : IsBlowupAlong n D ρ}
    {e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z} {U : Opens X'}
    (h : LocalStrictComparison f (.step S C π hπ) (.step T D ρ hρ) e U) :
    ∃ g : CMfd.of (n := n) (openPreimage S (preimageOpen f U)) ≃ₘ⟮𝓘c,𝓘c⟯
        CMfd.of (n := n) (openPreimage T U),
      IsTowerIso (openRestriction f (preimageOpen f U) U rfl)
        (restrict (preimageOpen f U) S) (restrict U T) g ∧
      (∀ (z : Y) (hz : π z ∈ openPreimage S (preimageOpen f U)),
        ρ (e z) = (g ⟨π z,hz⟩).val) ∧
      ∀ x : openPreimage S (preimageOpen f U), (g x).val ∈ D ↔ x.val ∈ C := by
  obtain ⟨eU,heU,hIso⟩ := h
  obtain ⟨g,hBefore,hComm,hCentre⟩ := strict_step_data hIso
  refine ⟨g,hBefore,?_,?_⟩
  · intro z hz
    let zU : openPreimage (.step S C π hπ) (preimageOpen f U) := ⟨z,hz⟩
    have h := congrArg Subtype.val (hComm zU)
    change ρ (eU zU).val = (g ⟨π z,hz⟩).val at h
    rwa [heU zU] at h
  · intro x
    exact Set.ext_iff.mp hCentre x

/-- The global penultimate map compares the literal prefixes on every
open in the original cover and carries the exact last centre. -/
theorem penultimate_of_local_strict_comparisons
    {I : Type*} (U : I → Opens X') (hU : ∀ x : X', ∃ i, x ∈ U i)
    {f : X ≃ₘ⟮𝓘c,𝓘c⟯ X'} {S : BlowupTower X A} {T : BlowupTower X' B}
    {C : Set A} {D : Set B} {π : Y → A} {ρ : Z → B}
    (hπ : IsBlowupAlong n C π) (hρ : IsBlowupAlong n D ρ)
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z)
    (he : ∀ z, T.proj (ρ (e z)) = f (S.proj (π z)))
    (hLocal : ∀ i, LocalStrictComparison f (.step S C π hπ) (.step T D ρ hρ) e (U i)) :
    ∃ g : A ≃ₘ⟮𝓘c,𝓘c⟯ B,
      (∀ z, ρ (e z) = g (π z)) ∧ g ⁻¹' D = C ∧
      (∀ x, T.proj (g x) = f (S.proj x)) ∧
      ∀ i, LocalStrictComparison f S T g (U i) := by
  classical
  choose g hg hSquare hCentre using (fun i => local_step_data (hLocal i))
  have hπSurj := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ
  have hρSurj := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hρ
  obtain ⟨r,hr,hReads⟩ := exists_penultimate_diffeomorph_of_cover
    (fun i => openPreimage S (preimageOpen f (U i))) (fun i => openPreimage T (U i))
    (fun x => hU (f (S.proj x))) (fun x => hU (T.proj x))
    π ρ hπSurj hρSurj e g hSquare (fun i z hz => by
      change f (S.proj (π z)) ∈ U i
      rw [← he z]
      exact hz)
  refine ⟨r,hr,?_,?_,fun i => ⟨g i,fun z => (hReads i z).symm,hg i⟩⟩
  · ext x
    obtain ⟨i,hi⟩ := hU (f (S.proj x))
    let xU : openPreimage S (preimageOpen f (U i)) := ⟨x,hi⟩
    change r x ∈ D ↔ x ∈ C
    rw [hReads i xU]
    exact hCentre i xU
  · intro x
    obtain ⟨z,rfl⟩ := hπSurj x
    rw [← hr z]
    exact he z


/-- Strict actual comparisons on a base cover descend with their prescribed
global endpoint map. -/
theorem isTowerIso_of_local_strict_comparisons
    {I : Type*} (U : I → Opens X') (hU : ∀ x : X', ∃ i, x ∈ U i)
    {f : X ≃ₘ⟮𝓘c,𝓘c⟯ X'} {Y Z : CMfd.{0} n} {S : BlowupTower X Y} {T : BlowupTower X' Z}
    (e : Y ≃ₘ⟮𝓘c,𝓘c⟯ Z) (hLen : S.length = T.length)
    (he : ∀ z, T.proj (e z) = f (S.proj z))
    (hLocal : ∀ i, LocalStrictComparison f S T e (U i)) :
    IsTowerIso f S T e := by
  cases S with
  | refl =>
    cases T with
    | refl =>
      have hEq : e = f := Diffeomorph.ext he
      subst e
      exact .refl
    | step => simp [BlowupTower.length_step] at hLen
  | @step A Y S C π hπ =>
    cases T with
    | refl => simp [BlowupTower.length_step] at hLen
    | @step B Z T D ρ hρ =>
      obtain ⟨r,hr,hC,hProj,hPre⟩ :=
        penultimate_of_local_strict_comparisons U hU hπ hρ e he hLocal
      exact .step (isTowerIso_of_local_strict_comparisons U hU r (Nat.succ.inj hLen) hProj hPre)
        hπ hρ e hr hC
termination_by S.length
decreasing_by
  simp only [BlowupTower.length_step] at *
  omega

end Hironaka.HironakaG8PenultimateCoverDescent
