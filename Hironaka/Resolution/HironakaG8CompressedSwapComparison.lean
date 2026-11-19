import Hironaka.Resolution.HironakaG8CompressionAtCuts
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaG8MatchedVisibleSwap

set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8CompressedSwapComparison

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  MarkedIdealTowerTransport MarkedIdealOpenBiholomorphism HironakaStageCenters
  BlowupTowerIsomorphism G3UniverseEmptyAwareCore HironakaG8CompressionAtCuts
  HironakaG8EmptyAwareTestTransport

variable {n : ℕ} {A B X Y Z Y' Z' F G F₀ : CMfd.{0} n}

private abbrev pair {X Y Z : CMfd.{0} n} {C : Set X} {D : Set Y}
    {π : Y → X} {q : Z → Y} (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q) :
    BlowupTower X Z := .step (.step .refl C π hπ) D q hq

private theorem occupied_transport
    {A B Y : CMfd.{0} n} (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B)
    (T : BlowupTower B Y) (h : StageCentres (fun _ C => C.Nonempty) T) :
    StageCentres (fun _ C => C.Nonempty) (transport (X' := A) φ T).tower := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    exact ⟨ih h.1,h.2.preimage (transport (X' := A) φ T).back.surjective⟩

/-- Given a raw nested match to a split restriction with an occupied
disjoint pair, retain the literal pulled pair in the smaller compression.
Swapping it and carrying its actual compressed suffix gives the raw
empty-aware comparison to the larger switched history. -/
theorem compressed_swap_of_matched_cut
    (N : MarkedIdeal n B) (hN : N.IsWellFormed)
    (P : BlowupTower B X)
    {C D : Set X} {π : Y → X} {q : Z → Y} {ρ : Y' → X} {r : Z' → Y'}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (hOcc : StageCentres (fun _ K => K.Nonempty) (pair hπ hq))
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z')
    (he : (ρ ∘ r) ∘ e = π ∘ q)
    (S : BlowupTower Z F) (T : BlowupTower Z' G)
    (f : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G)
    (hTail : IsTowerIso e S T f)
    (hBefore : IsGeoTestTower N ((P.append (pair hπ hq)).append S))
    (hAfter : IsGeoTestTower N ((P.append (pair hρ hr)).append T))
    (S₀ : BlowupTower A F₀)
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B)
    (ψ : F₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F)
    (hNested : EmptyAwareTowerIso φ S₀ ((P.append (pair hπ hq)).append S) ψ) :
    ∃ (A₁ F₁ G₁ : CMfd.{0} n) (P₁ : BlowupTower A A₁)
      (p : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
      (S₁ : BlowupTower Z F₁) (T₁ : BlowupTower Z' G₁)
      (ψ₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ F₀)
      (f₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₁)
      (χ : G₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      let Q := (P₁.append (transport (X' := A₁) p (pair hπ hq)).tower).append S₁
      let R := (P₁.append (transport (X' := A₁) p (pair hρ hr)).tower).append T₁
      StageCentres (fun _ K => K.Nonempty) Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) Q S₀ ψ₁ ∧
      IsTowerIso e S₁ T₁ f₁ ∧ R.proj ∘ f₁ = Q.proj ∧
      IsGeoTestTower (MarkedIdeal.pullback φ N) Q ∧ IsGeoTestTower (MarkedIdeal.pullback φ N) R ∧
      EmptyAwareTowerIso φ R ((P.append (pair hρ hr)).append T) χ ∧
      ∀ z, χ (f₁ z) = f (ψ (ψ₁ z)) := by
  obtain ⟨X₀,P₀,p₀,hPOcc,_,hP,_⟩ := test_empty_free_compression N hN P
  let H := transport (X' := A) φ P₀
  let p := H.back.trans p₀
  have hpRaw := G3UniverseEmptyAwareCore.trans
    (emptyAware_of_isTowerIso (transport_isTowerIso (X' := A) φ P₀)) hP
  have hφ : φ.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) B ∞) = φ := by ext x; rfl
  rw [hφ] at hpRaw
  have hp : EmptyAwareTowerIso φ H.tower P p := hpRaw
  let L := pair hπ hq
  let R₀ := pair hρ hr
  let b₁ := transport (X' := H.target) p L
  let b₂ := transport (X' := H.target) p R₀
  have hb₁ : IsTowerIso p b₁.tower L (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Z ∞) :=
    transport_isTowerIso (X' := H.target) p L
  have hb₂ : IsTowerIso p b₂.tower R₀ (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Z' ∞) :=
    transport_isTowerIso (X' := H.target) p R₀
  have hPrefixTest := ((isGeoTestTower_append_iff (𝔪 := N) (P.append L) S).mp hBefore).1
  let N' := geoTransformAlong N (P.append L)
  have hN' : N'.IsWellFormed := isWellFormed_geoTransformAlong hN _ hPrefixTest
  obtain ⟨F₁,K,k,hKOcc,_,hK,_⟩ := test_empty_free_compression N' hN' S
  let J := transport (X' := Z') e.symm K
  let f₁ := J.back.symm
  have hJ : IsTowerIso e K J.tower f₁ := by
    have hJ := (transport_isTowerIso (X' := Z') e.symm K).symm
    have hh : e.symm.symm = e := by ext z; rfl
    rwa [hh] at hJ
  have hNewTail := G3UniverseEmptyAwareCore.trans
    (G3UniverseEmptyAwareCore.trans
      (emptyAware_of_isTowerIso (transport_isTowerIso (X' := Z') e.symm K)) hK)
    (emptyAware_of_isTowerIso hTail)
  have hBase : (e.symm.trans (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Z ∞)).trans e =
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Z' ∞ := by
    ext z
    exact e.apply_symm_apply z
  rw [hBase] at hNewTail
  have hc₁ := append_emptyAware (append_emptyAware hp (emptyAware_of_isTowerIso hb₁)) hK
  have hc₂ := append_emptyAware (append_emptyAware hp (emptyAware_of_isTowerIso hb₂)) hNewTail
  have hRaw := G3UniverseEmptyAwareCore.trans hc₁ (G3UniverseEmptyAwareCore.symm hNested)
  have hId : φ.trans φ.symm = Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞ := by
    ext z
    exact φ.symm_apply_apply z
  rw [hId] at hRaw
  refine ⟨H.target,F₁,J.target,H.tower,p,K,J.tower,k.trans ψ.symm,f₁,
    (J.back.trans k).trans f, ?_,hRaw,hJ,?_,
    (isGeoTestTower_iff_of_emptyAware N hN φ hc₁).mpr hBefore,
    (isGeoTestTower_iff_of_emptyAware N hN φ hc₂).mpr hAfter,hc₂,?_⟩
  · exact stageCentres_nonempty_append (stageCentres_nonempty_append (occupied_transport φ P₀ hPOcc)
      (occupied_transport p L hOcc)) hKOcc
  · funext z
    apply φ.injective
    have h₁ := emptyAware_proj_comm hc₁ z
    have h₂ := emptyAware_proj_comm hc₂ (f₁ z)
    change ((P.append L).append S).proj (k z) = _ at h₁
    change ((P.append R₀).append T).proj (f (k (J.back (f₁ z)))) = _ at h₂
    dsimp only [f₁] at h₂
    rw [J.back.apply_symm_apply] at h₂
    change φ (((H.tower.append b₂.tower).append J.tower).proj (f₁ z)) =
      φ (((H.tower.append b₁.tower).append K).proj z)
    rw [← h₂,← h₁]
    simp only [BlowupTower.proj_append,Function.comp_apply]
    have ht := hTail.proj_comm (k z)
    rw [← ht]
    exact congrArg P.proj (congrFun he (S.proj (k z)))
  · intro z
    change f (k (J.back (J.back.symm z))) = f (ψ (ψ.symm (k z)))
    rw [J.back.apply_symm_apply,ψ.apply_symm_apply]

end Hironaka.HironakaG8CompressedSwapComparison
