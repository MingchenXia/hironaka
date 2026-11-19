import Hironaka.Resolution.HironakaG8DisjointSwapRecord
import Hironaka.Resolution.HironakaG8FirstFootprintOrder
import Hironaka.Resolution.HironakaG8IntrinsicSingularBlockSchedule

import Hironaka.Resolution.HironakaG8DisjointSwapRestrictedRead

set_option autoImplicit false
open Set TopologicalSpace Function
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8DisjointSwapFullHistory
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport HironakaStageCenters
  HironakaEmbeddedAnalytic HironakaG8DisjointMarkedSwap HironakaG8DisjointSwapRecord
  HironakaG8IntrinsicSingularBlockSchedule HironakaG8FirstFootprintOrder
  HironakaG8OccupiedSlotComparison BlowupTowerIsomorphism
  HironakaG8SingularFootprintExtension HironakaLocalPrincipalization MarkedIdealOpenBiholomorphism

open G3UniverseEmptyAwareCore HironakaG8DisjointSwapRestrictedRead

variable {n : ℕ} {X Y Z F : CMfd.{0} n}

/-- The literal geometry of the original and reversed indexed histories,
including the same terminal map used by the full suffix transport. -/
structure AdjacentSwapGeometry {B F G : CMfd.{0} n}
    (T : BlowupTower B F) (R : BlowupTower B G)
    (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G) (i : ℕ) where
  X : CMfd.{0} n
  Y : CMfd.{0} n
  Z : CMfd.{0} n
  Y' : CMfd.{0} n
  Z' : CMfd.{0} n
  P : BlowupTower B X
  C : Set X
  D : Set X
  π : Y → X
  q : Z → Y
  ρ : Y' → X
  r : Z' → Y'
  hπ : IsBlowupAlong n C π
  hq : IsBlowupAlong n (π ⁻¹' D) q
  hρ : IsBlowupAlong n D ρ
  hr : IsBlowupAlong n (ρ ⁻¹' C) r
  disjoint : Disjoint C D
  S : BlowupTower Z F
  S' : BlowupTower Z' G
  comparison : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z'
  projection : (ρ ∘ r) ∘ comparison = π ∘ q
  carry : IsTowerIso comparison S S' e
  index : P.length = i
  before : (P.append (.step (.step .refl C π hπ) (π ⁻¹' D) q hq)).append S = T
  after : (P.append (.step (.step .refl D ρ hρ) (ρ ⁻¹' C) r hr)).append S' = R

private theorem two_slot_swap
    {B Q : CMfd.{0} n} {C D : Set X}
    {π : Y → X} {q : Z → Y} {ρ : B → X} {r : Q → B}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hρ : IsBlowupAlong n D ρ) (hr : IsBlowupAlong n (ρ ⁻¹' C) r)
    (i : ℕ) :
    slotFootprint (.step (.step .refl D ρ hρ) (ρ ⁻¹' C) r hr) i =
      slotFootprint (.step (.step .refl C π hπ) (π ⁻¹' D) q hq) (Equiv.swap 0 1 i) := by
  have hπD := image_preimage_eq D (surjective_of_isBlowupAlong hπ)
  have hρC := image_preimage_eq C (surjective_of_isBlowupAlong hρ)
  rcases i with _ | _ | i
  · simp [slotFootprint, Equiv.swap_apply_left, hπD]
  · simp [slotFootprint, Equiv.swap_apply_right, hρC]
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    simp [slotFootprint]

private theorem swap_first_two_with_readback
    (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : M.N = univ)
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hCD : Disjoint C D) (S : BlowupTower Z F)
    (hTest : IsGeoTestTower M ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))
    (hC : C ⊆ singularSet (n := n) A)
    (hD : π ⁻¹' D ⊆ singularSet (n := n) (strictTransform n π A))
    (hSing : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) A))) S) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower X G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e =
        ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S).proj ∧
      StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj A)) R ∧
      (∀ i, slotFootprint R i =
        slotFootprint ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S)
          (Equiv.swap 0 1 i)) ∧
      (∀ {A : CMfd.{0} n} (P : BlowupTower A X) (U : Opens A),
        Disjoint (U : Set A) (P.proj '' C) ∨ Disjoint (U : Set A) (P.proj '' D) →
        ∃ χ : CMfd.of (n := n) (openPreimage (P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S)) U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (P.append R) U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U (P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))) (restrict U (P.append R)) χ) ∧
      ∀ {A : CMfd.{0} n} (P : BlowupTower A X),
        Nonempty (AdjacentSwapGeometry
          (P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))
          (P.append R) e P.length) := by
  let L : BlowupTower X Z := .step (.step .refl C π hπ) (π ⁻¹' D) q hq
  obtain ⟨hL,hS⟩ := (isGeoTestTower_append_iff (𝔪 := M) L S).mp hTest
  have hImage := image_preimage_eq D (surjective_of_isBlowupAlong hπ)
  have hSwap := swap_actual_steps_of_disjoint_projected_footprints A hA M hM hπ hq
    (by rw [hImage]; exact hCD) hL hC hD
  rw [hImage] at hSwap
  obtain ⟨B,Q,ρ,r,hρ,hr,hR,hRC,hRD,χ,hχ⟩ := hSwap
  let V : BlowupTower X Q := .step (.step .refl D ρ hρ) (ρ ⁻¹' C) r hr
  let T := transport (X' := Q) χ.symm S
  have hTail := transport_tail_after_disjoint_swap A hA M hM hN
    hπ hq hρ hr hCD hL hR χ hχ S hS hSing
  have hIso := transport_isTowerIso (X' := Q) χ.symm S
  have hProj : V.proj ∘ χ = L.proj := hχ
  refine ⟨T.target,V.append T.tower,T.back.symm,
    (isGeoTestTower_append_iff (𝔪 := M) V T.tower).mpr ⟨hR,hTail.1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · funext z
    rw [BlowupTower.proj_append, BlowupTower.proj_append]
    change V.proj (T.tower.proj (T.back.symm z)) = L.proj (S.proj z)
    have he := proj_transport (Φ := χ.symm) S (T.back.symm z)
    rw [T.back.apply_symm_apply] at he
    change χ.symm (T.tower.proj (T.back.symm z)) = S.proj z at he
    have he' := congrArg χ he
    rw [χ.apply_symm_apply] at he'
    rw [he']
    exact congrFun hProj _
  · apply intrinsic_stage_append A V T.tower
    · refine ⟨⟨trivial, ?_⟩, hRD⟩
      simpa only [BlowupTower.proj_refl, HironakaG11PresTowerState.strictTransform_id hA] using hRC
    · exact hTail.2
  · intro i
    rw [slotFootprint_append,slotFootprint_append]
    rcases i with _ | _ | i
    · simpa [V,L, Equiv.swap_apply_left, BlowupTower.length_step] using two_slot_swap hπ hq hρ hr 0
    · simpa [V,L, Equiv.swap_apply_right, BlowupTower.length_step] using two_slot_swap hπ hq hρ hr 1
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      have hV : V.length = 2 := rfl
      have hL' : L.length = 2 := rfl
      change (if _ < V.length then _ else _) = (if _ < L.length then _ else _)
      rw [hV,hL',if_neg (by omega),if_neg (by omega)]
      rw [slotFootprint_of_isTowerIso hIso]
      have hImg : χ.symm ⁻¹' slotFootprint S (i+2-2) = χ '' slotFootprint S (i+2-2) := by
        ext x
        constructor
        · intro hx
          exact ⟨χ.symm x,hx,χ.apply_symm_apply x⟩
        · rintro ⟨y,hy,rfl⟩
          change χ.symm (χ y) ∈ slotFootprint S (i+2-2)
          rwa [χ.symm_apply_apply]
      change V.proj '' (χ.symm ⁻¹' slotFootprint S (i+2-2)) = _
      rw [hImg, image_image]
      exact congrArg (fun f => f '' slotFootprint S (i+2-2)) hProj

  · intro A P U hU
    exact restricted_swap_with_prefix_and_suffix P U hπ hq hρ hr χ hχ hU hIso.symm

  · intro A P
    exact ⟨⟨X,Y,Z,B,Q,P,C,D,π,q,ρ,r,hπ,hq,hρ,hr,hCD,S,T.tower,χ,hχ,hIso.symm,rfl,
      BlowupTower.append_assoc _ _ _,BlowupTower.append_assoc _ _ _⟩⟩

/-- Swap the first two disjoint occupied events, transporting the entire
suffix. The two slots are interchanged and every later projected
footprint is retained on the original source. -/
theorem swap_first_two_with_singular_test_suffix
    (A : Set X) (hA : IsClosed A) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hN : M.N = univ)
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hCD : Disjoint C D) (S : BlowupTower Z F)
    (hTest : IsGeoTestTower M ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))
    (hC : C ⊆ singularSet (n := n) A)
    (hD : π ⁻¹' D ⊆ singularSet (n := n) (strictTransform n π A))
    (hSing : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) A))) S) :
    ∃ (G : CMfd.{0} n) (R : BlowupTower X G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e =
        ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S).proj ∧
      StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj A)) R ∧
      ∀ i, slotFootprint R i =
        slotFootprint ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S)
          (Equiv.swap 0 1 i) := by
  obtain ⟨G,R,e,hR,hProj,hStage,hFoot,_⟩ :=
    swap_first_two_with_readback A hA M hM hN hπ hq hCD S hTest hC hD hSing
  exact ⟨G,R,e,hR,hProj,hStage,hFoot⟩

/-- Swap an adjacent pair and retain the comparison on eligible base opens. -/
theorem swap_adjacent_with_prefix_and_suffix_geometry
    {B : CMfd.{0} n} (P : BlowupTower B X)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed)
    (hP : IsGeoTestTower M P) (hCarrier : (geoTransformAlong M P).N = univ)
    (hPStage : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj W)) P)
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hCD : Disjoint C D) (S : BlowupTower Z F)
    (hC : C ⊆ singularSet (n := n) (strictTransform n P.proj W))
    (hD : π ⁻¹' D ⊆ singularSet (n := n) (strictTransform n π (strictTransform n P.proj W)))
    (hSing : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) (strictTransform n P.proj W)))) S)
    (hTest : IsGeoTestTower M
      (P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))) :
    let L := P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S)
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = L.proj ∧
      StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj W)) R ∧
      (∀ i, slotFootprint R i = slotFootprint L (Equiv.swap P.length (P.length+1) i)) ∧
      (∀ U : Opens B,
        Disjoint (U : Set B) (P.proj '' C) ∨ Disjoint (U : Set B) (P.proj '' D) →
        ∃ χ : CMfd.of (n := n) (openPreimage L U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U L) (restrict U R) χ) ∧
      Nonempty (AdjacentSwapGeometry L R e P.length) := by
  let L := (BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S
  have ht := ((isGeoTestTower_append_iff (𝔪 := M) P L).mp hTest).2
  obtain ⟨G,R,e,hR,hProj,hStage,hFoot,hRead,hGeometry⟩ := swap_first_two_with_readback
    (strictTransform n P.proj W) isClosed_closure (geoTransformAlong M P)
    (isWellFormed_geoTransformAlong hM P hP) hCarrier hπ hq hCD S ht hC hD hSing
  refine ⟨G,P.append R,e,(isGeoTestTower_append_iff (𝔪 := M) P R).mpr ⟨hP,hR⟩,
    ?_,intrinsic_stage_append W P R hPStage hStage,?_,hRead P,hGeometry P⟩
  · rw [BlowupTower.proj_append,BlowupTower.proj_append,Function.comp_assoc,hProj]
  · intro i
    rw [slotFootprint_append,slotFootprint_append]
    by_cases h0 : i = P.length
    · subst i
      rw [Equiv.swap_apply_left, if_neg (by omega), if_neg (by omega)]
      simpa [Equiv.swap_apply_left] using congrArg (fun A => P.proj '' A) (hFoot 0)
    by_cases h1 : i = P.length+1
    · subst i
      rw [Equiv.swap_apply_right, if_neg (by omega), if_neg (by omega)]
      have h : P.length + 1 - P.length = 1 := by omega
      simpa [h, Equiv.swap_apply_right] using congrArg (fun A => P.proj '' A) (hFoot 1)
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    split_ifs with hh
    · rfl
    · have hh0 : i - P.length ≠ 0 := by omega
      have hh1 : i - P.length ≠ 1 := by omega
      rw [hFoot, Equiv.swap_apply_of_ne_of_ne hh0 hh1]

/-- Swap an adjacent pair and retain the comparison on eligible base opens. -/
theorem swap_adjacent_with_prefix_and_suffix_readback
    {B : CMfd.{0} n} (P : BlowupTower B X)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed)
    (hP : IsGeoTestTower M P) (hCarrier : (geoTransformAlong M P).N = univ)
    (hPStage : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj W)) P)
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hCD : Disjoint C D) (S : BlowupTower Z F)
    (hC : C ⊆ singularSet (n := n) (strictTransform n P.proj W))
    (hD : π ⁻¹' D ⊆ singularSet (n := n) (strictTransform n π (strictTransform n P.proj W)))
    (hSing : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) (strictTransform n P.proj W)))) S)
    (hTest : IsGeoTestTower M
      (P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))) :
    let L := P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S)
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = L.proj ∧
      StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj W)) R ∧
      (∀ i, slotFootprint R i = slotFootprint L (Equiv.swap P.length (P.length+1) i)) ∧
      ∀ U : Opens B,
        Disjoint (U : Set B) (P.proj '' C) ∨ Disjoint (U : Set B) (P.proj '' D) →
        ∃ χ : CMfd.of (n := n) (openPreimage L U)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage R U),
        (∀ z, (χ z).val = e z.val) ∧
        EmptyAwareTowerIso
          (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
          (restrict U L) (restrict U R) χ := by
  obtain ⟨G,R,e,hR,hProj,hStage,hFoot,hRead,_⟩ :=
    swap_adjacent_with_prefix_and_suffix_geometry P W M hM hP hCarrier hPStage hπ hq hCD
      S hC hD hSing hTest
  exact ⟨G,R,e,hR,hProj,hStage,hFoot,hRead⟩

/-- At any actual prefix, disjoint projected loci allow the adjacent
events to trade places while preserving the other projected footprints. -/
theorem swap_adjacent_with_prefix_and_suffix
    {B : CMfd.{0} n} (P : BlowupTower B X)
    (W : Set B) (M : MarkedIdeal n B) (hM : M.IsWellFormed)
    (hP : IsGeoTestTower M P) (hCarrier : (geoTransformAlong M P).N = univ)
    (hPStage : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj W)) P)
    {C D : Set X} {π : Y → X} {q : Z → Y}
    (hπ : IsBlowupAlong n C π) (hq : IsBlowupAlong n (π ⁻¹' D) q)
    (hCD : Disjoint C D) (S : BlowupTower Z F)
    (hC : C ⊆ singularSet (n := n) (strictTransform n P.proj W))
    (hD : π ⁻¹' D ⊆ singularSet (n := n) (strictTransform n π (strictTransform n P.proj W)))
    (hSing : StageCentres (fun T K => K ⊆ singularSet (n := n)
      (strictTransform n T.proj (strictTransform n (π ∘ q) (strictTransform n P.proj W)))) S)
    (hTest : IsGeoTestTower M
      (P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S))) :
    let L := P.append ((BlowupTower.step (.step .refl C π hπ) (π ⁻¹' D) q hq).append S)
    ∃ (G : CMfd.{0} n) (R : BlowupTower B G)
      (e : F ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ G),
      IsGeoTestTower M R ∧ R.proj ∘ e = L.proj ∧
      StageCentres (fun T K => K ⊆ singularSet (n := n) (strictTransform n T.proj W)) R ∧
      ∀ i, slotFootprint R i = slotFootprint L (Equiv.swap P.length (P.length+1) i) := by
  obtain ⟨G,R,e,hR,hProj,hStage,hFoot,_⟩ :=
    swap_adjacent_with_prefix_and_suffix_readback P W M hM hP hCarrier hPStage hπ hq hCD
      S hC hD hSing hTest
  exact ⟨G,R,e,hR,hProj,hStage,hFoot⟩

end
end Hironaka.HironakaG8DisjointSwapFullHistory
