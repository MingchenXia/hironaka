import Hironaka.Resolution.HironakaG8DisjointSwapFullHistory
import Hironaka.Resolution.HironakaG8SurfaceLimitEndpoint

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8IndexedDisjointSwap
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaStageCenters HironakaEmbeddedAnalytic
  HironakaG8FirstFootprintOrder HironakaG8OccupiedSlotComparison
  HironakaG8DisjointSwapFullHistory HironakaG8DisjointMarkedSwap
  HironakaG8SurfaceLimitEndpoint HomogenizedGlueingTower StrictTransformComposition

open G3UniverseEmptyAwareCore

variable {n : ℕ} {B F : CMfd.{0} n}

private theorem exists_adjacent_decomposition (T : BlowupTower B F)
    (i : ℕ) (hi : i+1 < T.length) :
    ∃ (X Y Z : CMfd.{0} n) (P : BlowupTower B X) (C : Set X) (D : Set Y)
      (π : Y → X) (q : Z → Y) (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n D q)
      (S : BlowupTower Z F),
      P.length = i ∧ T = (BlowupTower.step (.step P C π hπ) D q hq).append S := by
  induction T with
  | refl => simp at hi
  | @step Y Z T D q hq ih =>
    by_cases h : i+1 < T.length
    · obtain ⟨A,B,C,P,D,E,π,ρ,hπ,hρ,S,hLen,rfl⟩ := ih h
      exact ⟨A,B,C,P,D,E,π,ρ,hπ,hρ,.step S _ _ hq,hLen,rfl⟩
    · cases T with
      | refl => simp at hi
      | @step X Y P C π hπ =>
        have hLen : P.length = i := by simp only [BlowupTower.length_step] at hi h; omega
        exact ⟨X,_,_,P,C,D,π,q,hπ,hq,.refl,hLen,rfl⟩

private theorem stages_prefix (W : Set B) {X : CMfd.{0} n}
    (P : BlowupTower B X) (S : BlowupTower X F)
    (h : StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj W))
      (P.append S)) :
    StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj W)) P := by
  induction S with
  | refl => exact h
  | step S C π hπ ih => exact ih h.1

/-- An indexed swap retains its full comparison on every eligible base open. -/
theorem swap_adjacent_at_index_with_geometry
    (T : BlowupTower B F) (i : ℕ) (hi : i+1 < T.length)
    (hDisj : Disjoint (slotFootprint T i) (slotFootprint T (i+1)))
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      (∀ j, slotFootprint R j = slotFootprint T (Equiv.swap i (i+1) j)) ∧
      (∀ U : Opens B,
        Disjoint (U : Set B) (slotFootprint T i) ∨ Disjoint (U : Set B) (slotFootprint T (i+1)) →
        ∃ χ : CMfd.of (n := n) (openPreimage T U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U T) (restrict U R) χ) ∧
      Nonempty (AdjacentSwapGeometry T R e i) := by
  obtain ⟨X,Y,Z,P,C,D,π,q,hπ,hq,S,hLen,rfl⟩ := exists_adjacent_decomposition T i hi
  subst i
  let J : BlowupTower B Y := .step P C π hπ
  let L : BlowupTower B Z := .step J D q hq
  have hLeft : slotFootprint (L.append S) P.length = P.proj '' C := by
    rw [slotFootprint_append, if_pos (by change P.length < P.length+1+1; omega)]
    simp [L,J,slotFootprint,BlowupTower.length_step]
  have hRight : slotFootprint (L.append S) (P.length+1) = P.proj '' (π '' D) := by
    rw [slotFootprint_append, if_pos (by change P.length+1 < P.length+1+1; omega)]
    simp [L,J,slotFootprint,BlowupTower.length_step,BlowupTower.proj_step,image_comp]
  rw [hLeft,hRight] at hDisj
  have hd : Disjoint C (π '' D) := by
    rw [Set.disjoint_left] at hDisj ⊢
    exact fun x hx hy => hDisj (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  have he := preimage_image_eq_of_disjoint_centre hπ D hd
  have hLStage := stages_prefix W L S hStage
  have hSStage := intrinsic_stage_tail W L S hStage
  have hPStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) P :=
    hLStage.1.1
  have hC : C ⊆ singularSet (n := n) (strictTransform n P.proj W) := hLStage.1.2
  have hD : D ⊆ singularSet (n := n) (strictTransform n π (strictTransform n P.proj W)) := by
    rw [← strictTransform_comp P.contMDiff_proj hπ.contMDiff]
    exact hLStage.2
  have hSL : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) (strictTransform n P.proj W)))) S := by
    rw [← strictTransform_comp P.contMDiff_proj (hπ.contMDiff.comp hq.contMDiff)]
    exact hSStage
  let Q : BlowupTower X Z := .step (.step .refl C π hπ) D q hq
  have hEq : P.append (Q.append S) = L.append S := by
    rw [← BlowupTower.append_assoc]
    rfl
  have ht : IsGeoTestTower M (P.append (Q.append S)) := hEq.symm ▸ hTest
  have hP := ((isGeoTestTower_append_iff (𝔪 := M) P (Q.append S)).mp ht).1
  have hCarrier : (geoTransformAlong M P).N = univ := by
    rw [N_geoTransformAlong,hN,HironakaG4CompactWholeMonomialMaskPhase.strict_univ]
  let hq' : IsBlowupAlong n (π ⁻¹' (π '' D)) q := he.symm ▸ hq
  have hQ : (.step (.step .refl C π hπ) (π ⁻¹' (π '' D)) q hq' : BlowupTower X Z) = Q := by
    unfold Q
    congr
  rw [← hQ] at ht hEq
  have hs := swap_adjacent_with_prefix_and_suffix_geometry P W M hM hP hCarrier hPStage
    hπ hq' hd S hC (he.symm ▸ hD) hSL ht
  dsimp only at hs
  rw [hEq] at hs
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot,hRead,hGeometry⟩ := hs
  refine ⟨G,R,e,hR,hProj,hStages,hFoot,?_,hGeometry⟩
  intro U hU
  rw [hLeft,hRight] at hU
  exact hRead U hU

/-- An indexed swap retains its full comparison on every eligible base open. -/
theorem swap_adjacent_at_index_with_readback
    (T : BlowupTower B F) (i : ℕ) (hi : i+1 < T.length)
    (hDisj : Disjoint (slotFootprint T i) (slotFootprint T (i+1)))
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      (∀ j, slotFootprint R j = slotFootprint T (Equiv.swap i (i+1) j)) ∧
      ∀ U : Opens B,
        Disjoint (U : Set B) (slotFootprint T i) ∨ Disjoint (U : Set B) (slotFootprint T (i+1)) →
        ∃ χ : CMfd.of (n := n) (openPreimage T U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U T) (restrict U R) χ := by
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot,hRead,_⟩ :=
    swap_adjacent_at_index_with_geometry T i hi hDisj W M hM hN hTest hStage
  exact ⟨G,R,e,hR,hProj,hStages,hFoot,hRead⟩

/-- An indexed disjoint pair in a literal finite TEST tower can be
reversed, including the actual suffix and the exact original footprints. -/
theorem swap_adjacent_at_index
    (T : BlowupTower B F) (i : ℕ) (hi : i+1 < T.length)
    (hDisj : Disjoint (slotFootprint T i) (slotFootprint T (i+1)))
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      ∀ j, slotFootprint R j = slotFootprint T (Equiv.swap i (i+1) j) := by
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot,_⟩ :=
    swap_adjacent_at_index_with_readback T i hi hDisj W M hM hN hTest hStage
  exact ⟨G,R,e,hR,hProj,hStages,hFoot⟩

/-- Evaluate a chronological list of adjacent transpositions as a map
from the final slot to its original slot. -/
def reordering (σ : ℕ ≃ ℕ) : List ℕ → ℕ ≃ ℕ
  | [] => σ
  | i :: word => reordering ((Equiv.swap i (i+1)).trans σ) word

/-- Each requested swap has an occupied right slot and disjoint original
footprints, tracked through the preceding transpositions. -/
def IsDisjointSwapWord (A : ℕ → Set B) (σ : ℕ ≃ ℕ) : List ℕ → Prop
  | [] => True
  | i :: word =>
    (A (σ (i+1))).Nonempty ∧ Disjoint (A (σ i)) (A (σ (i+1))) ∧
      IsDisjointSwapWord A ((Equiv.swap i (i+1)).trans σ) word

/-- The open misses at least one footprint at each evolving swap. -/
def OpenAvoidsSwapPairs (U : Opens B) (A : ℕ → Set B) (σ : ℕ ≃ ℕ) : List ℕ → Prop
  | [] => True
  | i :: word =>
    (Disjoint (U : Set B) (A (σ i)) ∨ Disjoint (U : Set B) (A (σ (i+1)))) ∧
      OpenAvoidsSwapPairs U A ((Equiv.swap i (i+1)).trans σ) word

private theorem realize_word
    (A : ℕ → Set B) (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed)
    (hN : M.N = univ) (word : List ℕ) :
    ∀ {F : CMfd.{0} n} (T : BlowupTower B F) (σ : ℕ ≃ ℕ),
      IsDisjointSwapWord A σ word →
      (∀ i, slotFootprint T i = A (σ i)) →
      IsGeoTestTower M T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T →
      ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
        (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
        IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
        (∀ j, slotFootprint R j = A (reordering σ word j)) ∧
        ∀ U : Opens B, OpenAvoidsSwapPairs U A σ word →
          ∃ χ : CMfd.of (n := n) (openPreimage T U)
              ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
            (∀ z, (χ z).val = e z.val) ∧
            EmptyAwareTowerIso
              (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
              (restrict U T) (restrict U R) χ := by
  induction word with
  | nil =>
    intro F T σ _ hFoot hTest hStage
    exact ⟨F,T,Diffeomorph.refl _ _ _,hTest,rfl,hStage,hFoot,
      fun U _ => ⟨Diffeomorph.refl _ _ _,fun _ => rfl,
        emptyAware_of_isTowerIso (BlowupTowerIsomorphism.IsTowerIso.refl_self (restrict U T))⟩⟩
  | cons i word ih =>
    intro F T σ hWord hFoot hTest hStage
    obtain ⟨hHit,hDisj,hNext⟩ := hWord
    have hActive : (slotFootprint T (i+1)).Nonempty := by rwa [hFoot]
    obtain ⟨x,hx⟩ := hActive
    have hBound := hit_slot_lt_length T hx
    have hD : Disjoint (slotFootprint T i) (slotFootprint T (i+1)) := by simpa only [hFoot]
    obtain ⟨G,R,e,hR,hProj,hRStage,hRFoot,hRead⟩ :=
      swap_adjacent_at_index_with_readback T i hBound hD W M hM hN hTest hStage
    have hRF : ∀ j, slotFootprint R j = A (((Equiv.swap i (i+1)).trans σ) j) :=
      fun j => (hRFoot j).trans (hFoot _)
    obtain ⟨H,Q,f,hQ,hQProj,hQStage,hQFoot,hReadTail⟩ :=
      ih R ((Equiv.swap i (i+1)).trans σ) hNext hRF hR hRStage
    refine ⟨H,Q,e.trans f,hQ,?_,hQStage,hQFoot,?_⟩
    · change Q.proj ∘ (f ∘ e) = T.proj
      rw [← Function.comp_assoc,hQProj,hProj]
    · intro U hAvoid
      obtain ⟨hPair,hTail⟩ := hAvoid
      obtain ⟨χ,hχ,hχIso⟩ := hRead U (by simpa only [hFoot])
      obtain ⟨ψ,hψ,hψIso⟩ := hReadTail U hTail
      refine ⟨χ.trans ψ,?_,?_⟩
      · intro z
        change (ψ (χ z)).val = f (e z.val)
        rw [hψ,hχ]
      · simpa only [Diffeomorph.refl_trans] using G3UniverseEmptyAwareCore.trans hχIso hψIso

/-- A single physical word realizes the requested reordering and
retains all compatible restricted histories at the same terminal map. -/
theorem realize_disjoint_swap_word_with_readback
    (T : BlowupTower B F) (word : List ℕ)
    (hWord : IsDisjointSwapWord (slotFootprint T) (Equiv.refl ℕ) word)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      (∀ j, slotFootprint R j = slotFootprint T (reordering (Equiv.refl ℕ) word j)) ∧
      ∀ U : Opens B, OpenAvoidsSwapPairs U (slotFootprint T) (Equiv.refl ℕ) word →
        ∃ χ : CMfd.of (n := n) (openPreimage T U)
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
          (∀ z, (χ z).val = e z.val) ∧
          EmptyAwareTowerIso
            (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
            (restrict U T) (restrict U R) χ :=
  realize_word (slotFootprint T) W M hM hN word T (Equiv.refl ℕ) hWord (fun _ => rfl) hTest hStage

/-- A finite list of footprint-disjoint swaps realizes the specified
reordering by one actual TEST and singular tower over the original source. -/
theorem realize_disjoint_swap_word
    (T : BlowupTower B F) (word : List ℕ)
    (hWord : IsDisjointSwapWord (slotFootprint T) (Equiv.refl ℕ) word)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed) (hN : M.N = univ)
    (hTest : IsGeoTestTower M T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = T.proj ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) R ∧
      ∀ j, slotFootprint R j = slotFootprint T (reordering (Equiv.refl ℕ) word j) := by
  obtain ⟨G,R,e,hR,hProj,hStages,hFoot,_⟩ :=
    realize_disjoint_swap_word_with_readback T word hWord W M hM hN hTest hStage
  exact ⟨G,R,e,hR,hProj,hStages,hFoot⟩

end
end Hironaka.HironakaG8IndexedDisjointSwap
