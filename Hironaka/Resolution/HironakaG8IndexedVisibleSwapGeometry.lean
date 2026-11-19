import Hironaka.Resolution.HironakaG8IndexedDisjointSwap
import Hironaka.Resolution.HironakaG8LiteralCompressedSwapComparison

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8IndexedVisibleSwapGeometry
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealBiholomorphism.MarkedIdeal
  HironakaStageCenters HironakaG8OccupiedSlotComparison HironakaG8FirstFootprintOrder
  HironakaG8DisjointSwapFullHistory G3UniverseEmptyAwareCore HironakaG8LiteralCompressedSwapComparison

variable {n : ℕ} {A B F G H : CMfd.{0} n}

/-- The same actual indexed larger swap admits a smaller compressed swap
when both original footprints meet the nested open. -/
theorem compatible_visible_small_swap_of_geometry
    (N : MarkedIdeal n B) (hN : N.IsWellFormed)
    {T : BlowupTower B F} {R : BlowupTower B G}
    {e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G} {i : ℕ}
    (w : AdjacentSwapGeometry T R e i)
    (hBefore : IsGeoTestTower N T) (hAfter : IsGeoTestTower N R)
    (U : Opens B) (hVis₀ : (slotFootprint T i ∩ (U : Set B)).Nonempty)
    (hVis₁ : (slotFootprint T (i+1) ∩ (U : Set B)).Nonempty)
    (S : BlowupTower A H)
    (φ : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (ψ : H ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T U))
    (hNested : EmptyAwareTowerIso φ S (restrict U T) ψ) :
    let M := MarkedIdeal.pullback φ (MarkedIdeal.pullback (Subtype.val : U → B) N)
    ∃ (F₁ G₁ : CMfd.{0} n) (Q : BlowupTower A F₁) (R₁ : BlowupTower A G₁)
      (ψ₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ H)
      (f₁ : F₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G₁)
      (χ : G₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage R U)),
      StageCentres (fun _ K => K.Nonempty) Q ∧
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞) Q S ψ₁ ∧
      R₁.proj ∘ f₁ = Q.proj ∧ IsGeoTestTower M Q ∧ IsGeoTestTower M R₁ ∧
      EmptyAwareTowerIso φ R₁ (restrict U R) χ ∧
      (∀ z, (χ (f₁ z)).val = e (ψ (ψ₁ z)).val) ∧
      occupiedFootprints Q = (occupiedFootprints (restrict U T)).map (φ ⁻¹' ·) ∧
      occupiedFootprints R₁ = (occupiedFootprints (restrict U R)).map (φ ⁻¹' ·) := by
  obtain ⟨X,Y,Z,Y',Z',P,C,D,π,q,ρ,r,hπ,hq,hρ,hr,_,S₀,S₁,cmp,hcmp,hcarry,hidx,hBeforeEq,hAfterEq⟩ := w
  subst i
  subst T
  subst R
  let L : BlowupTower X Z := .step (.step .refl C π hπ) (π ⁻¹' D) q hq
  have hLen : (P.append L).length = P.length+2 := by rw [BlowupTower.length_append]; rfl
  have hLeft : slotFootprint ((P.append L).append S₀) P.length = P.proj '' C := by
    rw [slotFootprint_append,if_pos (by omega),slotFootprint_append,if_neg (by omega),Nat.sub_self]
    simp [L,slotFootprint,BlowupTower.length_step]
  have hRight : slotFootprint ((P.append L).append S₀) (P.length+1) = P.proj '' D := by
    rw [slotFootprint_append,if_pos (by omega),slotFootprint_append,if_neg (by omega)]
    have h : P.length+1-P.length = 1 := by omega
    rw [h]
    simp [L,slotFootprint,BlowupTower.length_step,
      Set.image_preimage_eq D (HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ)]
  change (slotFootprint ((P.append L).append S₀) P.length ∩ (U : Set B)).Nonempty at hVis₀
  change (slotFootprint ((P.append L).append S₀) (P.length+1) ∩ (U : Set B)).Nonempty at hVis₁
  rw [hLeft] at hVis₀
  rw [hRight] at hVis₁
  have hVis (K : Set X) (h : (P.proj '' K ∩ (U : Set B)).Nonempty) :
      ((openPreimage P U : Set X) ∩ K).Nonempty := by
    obtain ⟨_,⟨x,hx,rfl⟩,hu⟩ := h
    exact ⟨x,hu,hx⟩
  obtain ⟨F₁,G₁,Q,R₁,ψ₁,f₁,χ,hQ,hQcmp,hProj,hQT,hRT,hRcmp,hEnd⟩ :=
    literal_restricted_compressed_swap N hN U P hπ hq hρ hr (hVis C hVis₀) (hVis D hVis₁)
      cmp hcmp S₀ S₁ e hcarry hBefore hAfter S φ ψ hNested
  have hp := G3UniverseEmptyAwareCore.trans hQcmp hNested
  have hφ : (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞).trans φ = φ := by ext z; rfl
  rw [hφ] at hp
  exact ⟨F₁,G₁,Q,R₁,ψ₁,f₁,χ,hQ,hQcmp,hProj,hQT,hRT,hRcmp,hEnd,
    occupiedFootprints_emptyAware hp,occupiedFootprints_emptyAware hRcmp⟩
end Hironaka.HironakaG8IndexedVisibleSwapGeometry
