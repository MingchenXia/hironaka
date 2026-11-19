import Hironaka.Resolution.HironakaG8CompressedSwapComparison
import Hironaka.Resolution.HironakaG8ClosedNativeTestGlobalization

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8LiteralCompressedSwapComparison

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  MarkedIdealRestrictOpen HironakaStageCenters BlowupRestrictOpen
  BlowupTowerIsomorphism BlowupTowerIsoTail G3UniverseEmptyAwareCore
  HironakaSharpActualCurveComparisonRestriction HironakaG8CompressedSwapComparison

variable {n : ℕ} {A B X Y Z Y' Z' F G F₀ : CMfd.{0} n}

private abbrev pair {X Y Z : CMfd.{0} n} {C : Set X} {D : Set Y}
    {π : Y → X} {q : Z → Y} (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q) :
    BlowupTower X Z := .step (.step .refl C π hπ) D q hq

private theorem flatten {A X Y Z : CMfd.{0} n}
    (U : Opens A) (P : BlowupTower A X) (L : BlowupTower X Y) (S : BlowupTower Y Z) :
    let V := openPreimage P U
    let E := openPreimage L V
    ∃ e : CMfd.of (n := n) (openPreimage ((P.append L).append S) U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage S E),
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U ((P.append L).append S))
        (((restrict U P).append (restrict V L)).append (restrict E S)) e ∧
      ∀ z, (e z).val = z.val := by
  let V := openPreimage P U
  let E := openPreimage L V
  have h0 := isTowerIso_restrict_append U (P.append L) S
  have h1 := isTowerIso_restrict_append U P L
  have h2 : IsTowerIso (opensCongr (openPreimage_append P L U).symm)
      (restrict (openPreimage (P.append L) U) S) (restrict E S)
      (opensCongr (congrArg (openPreimage S) (openPreimage_append P L U).symm)) := by
    have hSame : ∀ (K K' : Opens Y) (h : K = K'),
        IsTowerIso (opensCongr h) (restrict K S) (restrict K' S)
          (opensCongr (congrArg (openPreimage S) h)) := by
      intro K K' h
      subst K'
      exact IsTowerIso.refl_self _
    exact hSame _ _ (openPreimage_append P L U).symm
  have hh := h0.trans (h1.append h2)
  have hId : ((Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞).trans
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)) =
        Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞ := by ext z; rfl
  rw [hId] at hh
  exact ⟨_,hh,fun _ => rfl⟩

private theorem restriction_on_named_opens {X Y Z W : CMfd.{0} n}
    {e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {f : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ W}
    {S : BlowupTower X Z} {T : BlowupTower Y W}
    (h : IsTowerIso e S T f) (U : Opens X) (V : Opens Y)
    (hU : (U : Set X) = e ⁻¹' (V : Set Y)) :
    ∃ g : CMfd.of (n := n) (openPreimage S U)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T V),
      IsTowerIso (openRestriction e U V hU) (restrict U S) (restrict V T) g ∧
      ∀ z, (g z).val = f z.val := by
  have hEq : U = preimageOpen e V := SetLike.coe_injective hU
  subst U
  exact ⟨_,HironakaSharpActualCurveComparisonRestriction.IsTowerIso.open_restriction h V,fun _ => rfl⟩

private theorem test_of_same_base_iso {A X Y : CMfd.{0} n}
    {P : BlowupTower A X} {T : BlowupTower A Y}
    {e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (h : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) P T e)
    (M : MarkedIdeal n A) (hM : M.IsWellFormed) (hTest : IsGeoTestTower M P) :
    IsGeoTestTower M T := by
  have hTest' := IsTowerIso.isGeoTestTower_iff (𝔪 := M) _
    hM.isClosedSubmanifold_N hM.isCoherent h
  have hId : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) M = M :=
    ContactCanonicalAlong.pullback_id M hM.isCoherent
  rw [hId] at hTest'
  exact hTest'.mp hTest

/-- When both swapped slots meet the smaller open, an actual compressed
smaller TEST can be swapped at the matching cut. Its post-swap history
compares to the literal larger restriction at the exact full endpoint. -/
theorem literal_restricted_compressed_swap
    (N : MarkedIdeal n B) (hN : N.IsWellFormed) (U : Opens B)
    (P : BlowupTower B X)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : Y' → X} {r : Z' → Y'}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hVis₀ : ((openPreimage P U : Set X) ∩ C).Nonempty)
    (hVis₁ : ((openPreimage P U : Set X) ∩ D).Nonempty)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z')
    (he : (ρ ∘ r) ∘ e = π ∘ q)
    (S : BlowupTower Z F) (T : BlowupTower Z' G)
    (f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G)
    (hTail : IsTowerIso e S T f)
    (hBefore : IsGeoTestTower N ((P.append (pair hπ hq)).append S))
    (hAfter : IsGeoTestTower N ((P.append (pair hρ hr)).append T))
    (S₀ : BlowupTower A F₀)
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (ψ : F₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage ((P.append (pair hπ hq)).append S) U))
    (hNested : EmptyAwareTowerIso φ S₀ (restrict U ((P.append (pair hπ hq)).append S)) ψ) :
    let T₀ := (P.append (pair hρ hr)).append T
    let M := MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : U → B) N)
    ∃ (F₁ G₁ : CMfd.{0} n) (Q : BlowupTower A F₁) (R : BlowupTower A G₁)
      (ψ₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F₀)
      (f₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₁)
      (χ : G₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₀ U)),
      StageCentres (fun _ K => K.Nonempty) Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) Q S₀ ψ₁ ∧
      R.proj ∘ f₁ = Q.proj ∧ IsGeoTestTower M Q ∧ IsGeoTestTower M R ∧
      EmptyAwareTowerIso φ R (restrict U T₀) χ ∧
      ∀ z, (χ (f₁ z)).val = f (ψ (ψ₁ z)).val := by
  let V := openPreimage P U
  let C₀ : Set V := Subtype.val ⁻¹' C
  let D₀ : Set V := Subtype.val ⁻¹' D
  let Pπ : BlowupTower X Y := .step .refl C π hπ
  let Pρ : BlowupTower X Y' := .step .refl D ρ hρ
  let L := pair hπ hq
  let K := pair hρ hr
  let π₀ : openPreimage Pπ V → V := fun y => ⟨π y.val,y.property⟩
  let ρ₀ : openPreimage Pρ V → V := fun y => ⟨ρ y.val,y.property⟩
  let q₀ : openPreimage L V → openPreimage Pπ V := fun y => ⟨q y.val,y.property⟩
  let r₀ : openPreimage K V → openPreimage Pρ V := fun y => ⟨r y.val,y.property⟩
  let hπ₀ : IsBlowupAlong n C₀ π₀ := isBlowupAlong_restrict hπ V _
  let hρ₀ : IsBlowupAlong n D₀ ρ₀ := isBlowupAlong_restrict hρ V _
  let hq₀ : IsBlowupAlong n (π₀ ⁻¹' D₀) q₀ := isBlowupAlong_restrict hq (openPreimage Pπ V) _
  let hr₀ : IsBlowupAlong n (ρ₀ ⁻¹' C₀) r₀ := isBlowupAlong_restrict hr (openPreimage Pρ V) _
  have hOpen : (openPreimage L V : Set Z) = e ⁻¹' (openPreimage K V : Set Z') := by
    ext z
    change π (q z) ∈ V ↔ ρ (r (e z)) ∈ V
    rw [show ρ (r (e z)) = π (q z) from congrFun he z]
  let e₀ := openRestriction e (openPreimage L V) (openPreimage K V) hOpen
  have he₀ : (ρ₀ ∘ r₀) ∘ e₀ = π₀ ∘ q₀ := by
    funext z
    apply Subtype.ext
    exact congrFun he z.val
  obtain ⟨g,hg,hgVal⟩ := restriction_on_named_opens hTail _ _ hOpen
  obtain ⟨a,ha,haVal⟩ := flatten U P L S
  obtain ⟨b,hb,hbVal⟩ := flatten U P K T
  let N₀ := MarkedIdeal.pullback (Subtype.val : U → B) N
  have hN₀ : N₀.IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val hN U
  have ht₀ := test_of_same_base_iso ha N₀ hN₀
    (isGeoTestTower_restrict (U := U) hN.isClosedSubmanifold_N hN.isCoherent _ hBefore)
  have ht₁ := test_of_same_base_iso hb N₀ hN₀
    (isGeoTestTower_restrict (U := U) hN.isClosedSubmanifold_N hN.isCoherent _ hAfter)
  have hRaw := G3UniverseEmptyAwareCore.trans hNested (emptyAware_of_isTowerIso ha)
  have hφ : φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞) = φ := by ext z; rfl
  rw [hφ] at hRaw
  have hOcc : StageCentres (fun _ K => K.Nonempty)
      (restrict V L) := by
    obtain ⟨x,hx,hxc⟩ := hVis₀
    obtain ⟨y,hy,hyd⟩ := hVis₁
    have hD : D₀.Nonempty := ⟨⟨y,hy⟩,hyd⟩
    exact ⟨⟨trivial,⟨⟨x,hx⟩,hxc⟩⟩,
      hD.preimage (HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ₀)⟩
  obtain ⟨_,F₁,G₁,P₁,p,S₁,T₁,ψ₁,f₁,χ,hQ,hQraw,_,hProj,hQt,hRt,hAfterCmp,hEnd⟩ :=
    compressed_swap_of_matched_cut
      (B := CMfd.of (n := n) U) (X := CMfd.of (n := n) V)
      (Y := CMfd.of (n := n) (openPreimage Pπ V))
      (Y' := CMfd.of (n := n) (openPreimage Pρ V))
      (Z := CMfd.of (n := n) (openPreimage L V))
      (Z' := CMfd.of (n := n) (openPreimage K V))
      (F := CMfd.of (n := n) (openPreimage S (openPreimage L V)))
      (G := CMfd.of (n := n) (openPreimage T (openPreimage K V)))
      N₀ hN₀ (restrict U P) (C := C₀) (D := D₀) (π := π₀) (q := q₀) (ρ := ρ₀) (r := r₀)
      hπ₀ hq₀ hρ₀ hr₀ hOcc e₀ he₀ _ _ g hg ht₀ ht₁ S₀ φ (ψ.trans a) hRaw
  have hh := G3UniverseEmptyAwareCore.trans hAfterCmp (emptyAware_of_isTowerIso hb.symm)
  have hφ' : φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞).symm = φ := by ext z; rfl
  rw [hφ'] at hh
  refine ⟨F₁,G₁,_,_,ψ₁,f₁,χ.trans b.symm,hQ,hQraw,hProj,hQt,hRt,hh,?_⟩
  intro z
  have hB := hbVal (b.symm (χ (f₁ z)))
  rw [b.apply_symm_apply] at hB
  change (b.symm (χ (f₁ z))).val = _
  rw [← hB,hEnd,hgVal]
  exact congrArg f (haVal (ψ (ψ₁ z)))

end Hironaka.HironakaG8LiteralCompressedSwapComparison
