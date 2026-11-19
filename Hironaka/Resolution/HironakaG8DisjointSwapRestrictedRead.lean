import Hironaka.Resolution.HironakaG8DisjointSwapRecord
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareNonempty

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8DisjointSwapRestrictedRead
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism HironakaSharpActualCurveComparisonRestriction
  HironakaNormalCrossingsOpenRestrictionSeparation G3UniverseEmptyAwareCore
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8EmptyAwareTestTransport
  HironakaStageCenters

variable {n : ℕ} {X Y Z B Q : CMfd.{0} n}

private theorem swap_empty_core
    {C : Set X} {D : Set Y} {C' : Set B} {D' : Set X}
    {π : Y → X} {q : Z → Y} {ρ : B → X} {r : Q → B}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q)
    (hρ : IsBlowupAlong n D' ρ) (hr : IsBlowupAlong n C' r)
    (hD : D = ∅) (hD' : D' = ∅) (hC' : C' = ρ ⁻¹' C)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)
      (.step (.step .refl C π hπ) D q hq) (.step (.step .refl D' ρ hρ) C' r hr) e := by
  subst D
  subst D'
  subst C'
  obtain ⟨f,hf⟩ := exists_empty_blowup_biholomorphism hρ
  obtain ⟨g,hg⟩ := exists_empty_blowup_biholomorphism hq
  let idX := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have h0 : EmptyAwareTowerIso idX .refl (.step .refl ∅ ρ hρ) (idX.trans f.symm) :=
    .rightEmpty .refl hρ f hf
  have hStep := EmptyAwareTowerIso.step h0 hπ hr (g.symm.trans e)
    (by
      intro y
      apply f.injective
      change f (r (e (g.symm y))) = f (f.symm (π y))
      rw [f.apply_symm_apply,hf]
      have h := congrFun he (g.symm y)
      have hgy := hg (g.symm y)
      rw [g.apply_symm_apply] at hgy
      exact h.trans (congrArg π hgy.symm))
    (by
      ext x
      change ρ (f.symm x) ∈ C ↔ x ∈ C
      rw [← hf, f.apply_symm_apply])
  have hLast := EmptyAwareTowerIso.leftEmpty hStep hq g hg
  have hEq : g.trans (g.symm.trans e) = e := by ext x; simp
  rw [hEq] at hLast
  exact hLast

private abbrev twice {C : Set X} {D : Set Y} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q) : BlowupTower X Z :=
  .step (.step .refl C π hπ) D q hq

/-- On an open missing the centre moved from second to first, the two
literal restricted pairs agree after empty stages, with the actual
restriction of the supplied terminal map. -/
theorem restricted_swap_of_disjoint_right
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : B → X} {r : Q → B}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) (U : Opens X) (hU : Disjoint (U : Set X) D) :
    ∃ χ : CMfd.of (n := n) (openPreimage (twice hπ hq) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (twice hρ hr) U),
      (∀ z, (χ z).val = e z.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (twice hπ hq)) (restrict U (twice hρ hr)) χ := by
  let L := twice hπ hq
  let R := twice hρ hr
  have hOpen : (openPreimage L U : Set Z) = e ⁻¹' (openPreimage R U : Set Q) := by
    ext z
    change π (q z) ∈ U ↔ ρ (r (e z)) ∈ U
    rw [show ρ (r (e z)) = π (q z) from congrFun he z]
  let χ := openRestriction e (openPreimage L U) (openPreimage R U) hOpen
  have he' : (restrict U R).proj ∘ χ = (restrict U L).proj := by
    funext z
    apply Subtype.ext
    change (((restrict U R).proj (χ z) : U) : X) = ((restrict U L).proj z : U)
    rw [show (((restrict U R).proj (χ z) : U) : X) = R.proj (χ z).val from proj_restrict U R _,
      proj_restrict U L z]
    exact congrFun he z.val
  refine ⟨χ,fun _ => rfl,?_⟩
  apply swap_empty_core _ _ _ _ _ _ _ χ he'
  · ext y
    exact iff_false_intro (fun hy => disjoint_left.mp hU y.property hy)
  · ext x
    exact iff_false_intro (fun hx => disjoint_left.mp hU x.property hx)
  · rfl

/-- A strict comparison of the full tails extends restricted empty-aware
prefix compatibility, with the same terminal map on the underlying points. -/
theorem restricted_append_of_strict_suffix
    {P₁ : BlowupTower X Z} {P₂ : BlowupTower X Q} (U : Opens X)
    {e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q}
    {χ : CMfd.of (n := n) (openPreimage P₁ U)
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage P₂ U)}
    (hχ : ∀ z, (χ z).val = e z.val)
    (hP : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
      (restrict U P₁) (restrict U P₂) χ)
    {F G : CMfd.{0} n} {S : BlowupTower Z F} {T : BlowupTower Q G}
    {f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G}
    (hS : IsTowerIso e S T f) :
    ∃ β : CMfd.of (n := n) (openPreimage (P₁.append S) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (P₂.append T) U),
      (∀ z, (β z).val = f z.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (P₁.append S)) (restrict U (P₂.append T)) β := by
  induction hS with
  | refl => exact ⟨χ,hχ,hP⟩
  | @step Y₁ Y₂ Z₁ Z₂ S T η _ C₁ π₁ hπ₁ C₂ π₂ hπ₂ f hComm hCentre ih =>
    obtain ⟨β,hβ,hB⟩ := ih
    let L := P₁.append (.step S C₁ π₁ hπ₁)
    let R := P₂.append (.step T C₂ π₂ hπ₂)
    have hOpen : (openPreimage L U : Set Z₁) = f ⁻¹' (openPreimage R U : Set Z₂) := by
      ext z
      constructor
      · intro hz
        let p : openPreimage (P₁.append S) U := ⟨π₁ z,hz⟩
        have hp := (β p).property
        change (P₂.append T).proj (β p).val ∈ U at hp
        rw [hβ p, ← hComm] at hp
        exact hp
      · intro hz
        let p : openPreimage (P₂.append T) U := ⟨π₂ (f z),hz⟩
        have hp : (β.symm p).val = π₁ z := by
          apply η.injective
          change η (β.symm p).val = η (π₁ z)
          rw [← hβ, β.apply_symm_apply, ← hComm]
        have hup := (β.symm p).property
        change (P₁.append S).proj (β.symm p).val ∈ U at hup
        rwa [hp] at hup
    let δ := openRestriction f (openPreimage L U) (openPreimage R U) hOpen
    refine ⟨δ,fun _ => rfl,EmptyAwareTowerIso.step hB _ _ δ ?_ ?_⟩
    · intro p
      apply Subtype.ext
      change π₂ (f p.val) = (β ⟨π₁ p.val,p.property⟩).val
      rw [hβ,hComm]
    · ext p
      change (β p).val ∈ C₂ ↔ p.val ∈ C₁
      rw [hβ]
      exact Set.ext_iff.mp hCentre p.val

/-- On the literal base-open restriction, the switched pair and every
subsequent transported step retain the original terminal map. -/
theorem restricted_swap_with_full_suffix
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : B → X} {r : Q → B}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q) (U : Opens X)
    (hU : Disjoint (U : Set X) C ∨ Disjoint (U : Set X) D)
    {F G : CMfd.{0} n} {S : BlowupTower Z F} {T : BlowupTower Q G}
    {f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G} (hS : IsTowerIso e S T f) :
    let L := (twice hπ hq).append S
    let R := (twice hρ hr).append T
    ∃ β : CMfd.of (n := n) (openPreimage L U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
      (∀ z, (β z).val = f z.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U L) (restrict U R) β := by
  rcases hU with hUC | hUD
  · have he' : (π ∘ q) ∘ e.symm = ρ ∘ r := by
      funext z
      have h := congrFun he (e.symm z)
      change ρ (r (e (e.symm z))) = π (q (e.symm z)) at h
      rw [e.apply_symm_apply] at h
      exact h.symm
    obtain ⟨χ,hχ,hPair⟩ := restricted_swap_of_disjoint_right hρ hr hπ hq e.symm he' U hUC
    have hb := G3UniverseEmptyAwareCore.symm hPair
    have hId : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞).symm =
        Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞ := by ext x; rfl
    rw [hId] at hb
    refine restricted_append_of_strict_suffix U (χ := χ.symm) ?_ hb hS
    intro z
    have hh := hχ (χ.symm z)
    rw [χ.apply_symm_apply] at hh
    rw [hh,e.apply_symm_apply]
  · obtain ⟨χ,hχ,hPair⟩ := restricted_swap_of_disjoint_right hπ hq hρ hr e he U hUD
    exact restricted_append_of_strict_suffix U hχ hPair hS

open G3UniverseEmptyAwareNonempty

/-- Empty-free compression of the original restricted TEST towers
turns the empty-aware comparison into a strict one. Its terminal map is
the compressed form of the given actual restricted terminal map. -/
theorem strict_test_compressions_of_emptyAware
    {L : BlowupTower X Y} {R : BlowupTower X Z}
    {e : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) L R e)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hL : IsGeoTestTower M L) (hR : IsGeoTestTower M R) :
    ∃ (F G : CMfd.{0} n) (S : BlowupTower X F) (T : BlowupTower X G)
      (α : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
      (β : G ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z),
      IsGeoTestTower M S ∧ IsGeoTestTower M T ∧
      StageCentres (fun _ C => C.Nonempty) S ∧ StageCentres (fun _ C => C.Nonempty) T ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) S L α ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) T R β ∧
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞) S T ((α.trans e).trans β.symm) := by
  obtain ⟨F,S,α,hSO,_,hS,htS⟩ := test_empty_free_compression M hM L
  obtain ⟨G,T,β,hTO,_,hT,htT⟩ := test_empty_free_compression M hM R
  have hST := G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.trans hS h)
    (G3UniverseEmptyAwareCore.symm hT)
  refine ⟨F,G,S,T,α,β,htS.mpr hL,htT.mpr hR,hSO,hTO,hS,hT,?_⟩
  have hs := isTowerIso_of_emptyAware_nonempty hST hSO hTO
  have hId : ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).trans
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞)).trans
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞).symm =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞ := by ext x; rfl
  rwa [hId] at hs

private theorem prepend_same
    {A K Y₁ Y₂ : CMfd.{0} n} (P : BlowupTower A K)
    {L : BlowupTower K Y₁} {R : BlowupTower K Y₂}
    {e : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) K ∞) L R e) :
    EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞)
      (P.append L) (P.append R) e := by
  induction h with
  | refl => exact emptyAware_of_isTowerIso (IsTowerIso.refl_self P)
  | step _ hπ hρ χ hc hC ih => exact .step ih hπ hρ χ hc hC
  | leftEmpty _ hπ φ hφ ih => exact .leftEmpty ih hπ φ hφ
  | rightEmpty _ hπ φ hφ ih => exact .rightEmpty ih hπ φ hφ

open BlowupTowerIsoTail

/-- The strict common-prefix restriction can be restored over the
original base open, with the same full terminal map on points. -/
theorem restricted_prepend_same {A F G : CMfd.{0} n}
    (P : BlowupTower A X) (U : Opens A) {L : BlowupTower X F} {R : BlowupTower X G}
    {f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G}
    {β : CMfd.of (n := n) (openPreimage L (openPreimage P U))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R (openPreimage P U))}
    (hβ : ∀ z, (β z).val = f z.val)
    (h : EmptyAwareTowerIso
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (openPreimage P U)) ∞)
      (restrict (openPreimage P U) L) (restrict (openPreimage P U) R) β) :
    ∃ χ : CMfd.of (n := n) (openPreimage (P.append L) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (P.append R) U),
      (∀ z, (χ z).val = f z.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U (P.append L)) (restrict U (P.append R)) χ := by
  have hL := emptyAware_of_isTowerIso (isTowerIso_restrict_append U P L)
  have hR := emptyAware_of_isTowerIso (isTowerIso_restrict_append U P R).symm
  have hh := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans hL (prepend_same (restrict U P) h)) hR
  let left := opensCongr (n := n) (openPreimage_append P L U).symm
  let right := opensCongr (n := n) (openPreimage_append P R U).symm
  refine ⟨(left.trans β).trans right.symm,?_,?_⟩
  · intro z
    exact hβ (left z)
  · have hId : ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞).trans
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)).trans
        (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞).symm =
        Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞ := by ext x; rfl
    rwa [hId] at hh

/-- A base open missing either projected swapped locus sees an empty-aware
comparison at the same full terminal map. -/
theorem restricted_swap_with_prefix_and_suffix
    {A : CMfd.{0} n} (P : BlowupTower A X) (U : Opens A)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : B → X} {r : Q → B}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q)
    (he : (ρ ∘ r) ∘ e = π ∘ q)
    (hU : Disjoint (U : Set A) (P.proj '' C) ∨ Disjoint (U : Set A) (P.proj '' D))
    {F G : CMfd.{0} n} {S : BlowupTower Z F} {T : BlowupTower Q G}
    {f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G} (hS : IsTowerIso e S T f) :
    let L := P.append ((twice hπ hq).append S)
    let R := P.append ((twice hρ hr).append T)
    ∃ β : CMfd.of (n := n) (openPreimage L U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
      (∀ z, (β z).val = f z.val) ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U L) (restrict U R) β := by
  have hMiss (K : Set X) (hk : Disjoint (U : Set A) (P.proj '' K)) :
      Disjoint (openPreimage P U : Set X) K :=
    disjoint_left.mpr (fun _ ha hb => disjoint_left.mp hk ha (mem_image_of_mem _ hb))
  obtain ⟨χ,hχ,h⟩ := restricted_swap_with_full_suffix hπ hq hρ hr e he (openPreimage P U)
    (hU.imp (hMiss C) (hMiss D)) hS
  exact restricted_prepend_same P U hχ h

end
end Hironaka.HironakaG8DisjointSwapRestrictedRead

#print axioms Hironaka.HironakaG8DisjointSwapRestrictedRead.restricted_swap_with_full_suffix
#print axioms Hironaka.HironakaG8DisjointSwapRestrictedRead.strict_test_compressions_of_emptyAware

#print axioms Hironaka.HironakaG8DisjointSwapRestrictedRead.restricted_swap_with_prefix_and_suffix
