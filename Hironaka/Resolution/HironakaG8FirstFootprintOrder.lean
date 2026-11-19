import Hironaka.Resolution.HironakaG8OccupiedSlotComparison
import Hironaka.Resolution.HironakaG8LabelledNativeHistory
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS
import Hironaka.Resolution.HironakaG8DisjointMarkedSwap

/-! First hits of original singular fibres in actual labelled histories. -/
set_option autoImplicit false
open Set Pointwise Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FirstFootprintOrder
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HironakaG8OccupiedSlotComparison
  HironakaG8CofinalOccupiedAncestry HironakaG8NativePhaseCertificate
  HironakaG8LabelledNativeHistory HironakaEmbeddedAnalytic
  HironakaHolomorphicJetChartInvariance HironakaLocalPrincipalization
  HironakaG8DisjointMarkedSwap HironakaActualBlowupOffCentreIntrinsicHS
  StrictTransformComposition RestrictEmptyTower BlowupTowerIsomorphism
  HironakaResolutionSpaceLocal HironakaActualVanishingIntrinsicHSTransport
  HironakaBaseChange HironakaNormalCrossingsSeparationChoiceComparison
  HironakaOriginalCanonicalDimensionList HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaG3EmptyAwareHistory

variable {n : ℕ} {X Y Z : CMfd.{0} n}
local notation "HS[" W "]" => hilbertSamuelAt (vanishingIdeal (n := n) W)

theorem hit_slot_lt_length (T : BlowupTower X Y) {i : ℕ} {x : X}
    (h : x ∈ slotFootprint T i) : i < T.length :=
  occupied_lt_length T ((slotFootprint_nonempty_iff T i).mp ⟨x,h⟩)

theorem slotFootprint_subset_of_centresOver (T : BlowupTower X Y) {F : Set X}
    (h : CentresOver F T) (i : ℕ) : slotFootprint T i ⊆ F := by
  induction T with
  | refl => exact empty_subset _
  | step T C π hπ ih =>
    by_cases hi : i = T.length
    · rw [slotFootprint,if_pos hi]
      exact image_subset_iff.mpr h.2
    · rw [slotFootprint,if_neg hi]
      exact ih h.1

/-- The composite history indexes the earlier raw slots unchanged and
adds the exact prefix length to the later raw slots. -/
theorem slotFootprint_append (P : BlowupTower X Y) (Q : BlowupTower Y Z) (i : ℕ) :
    slotFootprint (P.append Q) i =
      if i < P.length then slotFootprint P i else P.proj '' slotFootprint Q (i-P.length) := by
  induction Q with
  | refl =>
    change slotFootprint P i = if i < P.length then slotFootprint P i else P.proj '' ∅
    by_cases hi : i < P.length
    · rw [if_pos hi]
    · rw [if_neg hi,image_empty]
      exact eq_empty_iff_forall_notMem.mpr (fun _ hx => hi (hit_slot_lt_length P hx))
  | step Q C π hπ ih =>
    by_cases hi : i < P.length
    · have hneq : i ≠ (P.append Q).length := by rw [BlowupTower.length_append]; omega
      rw [if_pos hi,BlowupTower.append_step,slotFootprint,if_neg hneq,ih,if_pos hi]
    · have hiff : i = (P.append Q).length ↔ i-P.length = Q.length := by
        rw [BlowupTower.length_append]
        omega
      rw [if_neg hi,BlowupTower.append_step,slotFootprint,slotFootprint]
      by_cases he : i = (P.append Q).length
      · rw [if_pos he,if_pos (hiff.mp he),BlowupTower.proj_append,image_comp]
      · rw [if_neg he,if_neg (fun he' => he (hiff.mpr he')),ih,if_neg hi]

/-- A strict physical tower comparison preserves every raw hit index. -/
theorem slotFootprint_of_isTowerIso
    {X' Y' : CMfd.{0} n}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    (h : IsTowerIso φ T' T χ) (i : ℕ) :
    slotFootprint T' i = φ ⁻¹' slotFootprint T i := by
  induction h with
  | refl => exact preimage_empty.symm
  | @step V' V W' W T' T χ h C' π' hπ' C π hπ χ' hcomm hC ih =>
    by_cases hi : i = T.length
    · rw [slotFootprint,slotFootprint,if_pos hi,if_pos (hi.trans h.length_eq.symm)]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        refine ⟨χ y,?_,(h.proj_comm y).symm⟩
        change y ∈ χ ⁻¹' C
        rwa [hC]
      · rintro ⟨y,hy,he⟩
        refine ⟨χ.symm y,?_,φ.injective ?_⟩
        · rw [← hC]
          change χ (χ.symm y) ∈ C
          rwa [χ.apply_symm_apply]
        · change φ (T'.proj (χ.symm y)) = φ x
          rw [h.proj_comm,χ.apply_symm_apply]
          exact he
    · rw [slotFootprint,slotFootprint,if_neg hi,if_neg (fun he => hi (he.trans h.length_eq))]
      exact ih

/-- Over a point missed by every literal centre, every lift retains
exact singularity and the complete intrinsic Hilbert–Samuel profile. -/
theorem untouched_fibre_intrinsic
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W) (P : BlowupTower X Y) (z : Y)
    (hMiss : ∀ i, P.proj z ∉ slotFootprint P i) :
    (z ∈ singularSet (n := n) (strictTransform n P.proj W) ↔ P.proj z ∈ singularSet (n := n) W) ∧
    HS[strictTransform n P.proj W] z = HS[W] (P.proj z) := by
  induction P with
  | refl =>
    have h := HironakaG11PresTowerState.strictTransform_id hW.isClosed
    rw [BlowupTower.proj_refl,h]
    exact ⟨Iff.rfl,rfl⟩
  | @step V B P C π hπ ih =>
    have hOut : π z ∉ C := by
      intro hz
      apply hMiss P.length
      rw [slotFootprint,if_pos rfl]
      exact ⟨π z,hz,rfl⟩
    have hMissP : ∀ i, P.proj (π z) ∉ slotFootprint P i := by
      intro i hi
      have hlt := hit_slot_lt_length P hi
      apply hMiss i
      rw [slotFootprint,if_neg (Nat.ne_of_lt hlt)]
      exact hi
    obtain ⟨hSing,hHS⟩ := ih (π z) hMissP
    have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW P
    change (_ ↔ P.proj (π z) ∈ _) ∧ _ = HS[W] (P.proj (π z))
    rw [BlowupTower.proj_step,strictTransform_comp P.contMDiff_proj hπ.contMDiff]
    have hd : Disjoint C ({π z} : Set V) := disjoint_left.mpr fun x hx hxe => by
      have hEq : x = π z := hxe
      exact hOut (hEq ▸ hx)
    have hStep := singularSet_at_disjoint_second_centre hπ hA.isClosed hd
      (show z ∈ π ⁻¹' ({π z} : Set V) from rfl)
    exact ⟨hStep.trans hSing,(funext (hilbertSamuelAt_actual_strict_blowup_off_centre hπ hA z hOut)).trans hHS⟩

private theorem tower_proj_surjective (T : BlowupTower X Y) : Function.Surjective T.proj := by
  induction T with
  | refl => exact Function.surjective_id
  | step T C π hπ ih =>
    rw [BlowupTower.proj_step]
    exact ih.comp (surjective_of_isBlowupAlong hπ)

/-- In an actual labelled native history, a larger original singular
profile is hit before any hit on a smaller original singular profile.
It suffices that the smaller-profile point is eventually hit. -/
theorem higher_original_profile_hit_first
    {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (h : LabelledNativeTower n W E K T L) :
    ∀ {x y : X}, x ∈ K → y ∈ K →
      x ∈ singularSet (n := n) W → y ∈ singularSet (n := n) W →
      toLex (HS[W] x) < toLex (HS[W] y) →
      ∀ j, x ∈ slotFootprint T j → ∃ i < j, y ∈ slotFootprint T i := by
  induction h with
  | smooth hW hE hSmooth =>
    intro x y hx hy hxs hys hLess j hHit
    exact hHit.elim
  | @phase X A Y W E K S T H L hW hE hUpper hPhase hLower hLater ih =>
    intro x y hx hy hxs hys hLess j hHit
    have hMissX : ∀ i, x ∉ slotFootprint S i := by
      intro i hi
      have hxH : HS[W] x = H := slotFootprint_subset_of_centresOver S hPhase.supports i hi
      have hY := hUpper y ⟨hy,hys⟩
      rw [hxH] at hLess
      exact (not_lt_of_ge hY) hLess
    have hj : S.length ≤ j := by
      by_contra hn
      rw [slotFootprint_append,if_pos (Nat.lt_of_not_ge hn)] at hHit
      exact hMissX j hHit
    by_cases hYHit : ∃ i, y ∈ slotFootprint S i
    · obtain ⟨i,hi⟩ := hYHit
      have hlt := hit_slot_lt_length S hi
      refine ⟨i,hlt.trans_le hj,?_⟩
      rwa [slotFootprint_append,if_pos hlt]
    · rw [slotFootprint_append,if_neg (not_lt_of_ge hj)] at hHit
      obtain ⟨x',hx',heX⟩ := hHit
      obtain ⟨y',heY⟩ := tower_proj_surjective S y
      obtain ⟨hSx,hHx⟩ := untouched_fibre_intrinsic W hW S x' (fun i => heX ▸ hMissX i)
      obtain ⟨hSy,hHy⟩ := untouched_fibre_intrinsic W hW S y' (fun i hi => hYHit ⟨i,heY ▸ hi⟩)
      have hLess' : toLex (HS[strictTransform n S.proj W] x') <
          toLex (HS[strictTransform n S.proj W] y') := by
        rw [hHx,hHy,heX,heY]
        exact hLess
      have hxK : x' ∈ S.proj ⁻¹' K := show S.proj x' ∈ K from heX ▸ hx
      have hyK : y' ∈ S.proj ⁻¹' K := show S.proj y' ∈ K from heY ▸ hy
      obtain ⟨i,hi,hyi⟩ := ih hxK hyK (hSx.mpr (heX ▸ hxs)) (hSy.mpr (heY ▸ hys))
        hLess' (j-S.length) hx'
      refine ⟨S.length+i,by omega,?_⟩
      rw [slotFootprint_append,if_neg (by omega)]
      have he : S.length+i-S.length = i := by omega
      rw [he]
      exact ⟨y',hyi,heY⟩
  | @restrictOpen X Y W E K T L h O ih =>
    intro x y hx hy hxs hys hLess j hHit
    rw [HironakaResolutionSpaceLocal.singularSet_preimage_val] at hxs hys
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any O W x),
      funext (hilbertSamuelAt_vanishing_actual_open_any O W y)] at hLess
    rw [slotFootprint_restrict] at hHit
    obtain ⟨i,hi,hyi⟩ := ih hx hy hxs hys hLess j hHit
    exact ⟨i,hi,by rwa [slotFootprint_restrict]⟩
  | @of_isTowerIso X X' Y Y' W E K T T' L h φ χ hIso ih =>
    intro x y hx hy hxs hys hLess j hHit
    rw [singularSet_preimage_eq (isSubmersion_biholomorphism φ)] at hxs hys
    rw [funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any φ W x),
      funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any φ W y)] at hLess
    rw [slotFootprint_of_isTowerIso hIso] at hHit
    obtain ⟨i,hi,hyi⟩ := ih hx hy hxs hys hLess j hHit
    exact ⟨i,hi,by rwa [slotFootprint_of_isTowerIso hIso]⟩


/-- Every original singular point of the literal source has an occupied
hit since the actual labelled terminal strict transform is smooth. -/
theorem exists_hit_original_singular
    {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (h : LabelledNativeTower n W E K T L) {x : X}
    (hx : x ∈ singularSet (n := n) W) :
    ∃ i, x ∈ slotFootprint T i := by
  by_contra hn
  obtain ⟨z,hz⟩ := tower_proj_surjective T x
  have hMiss : ∀ i, T.proj z ∉ slotFootprint T i := by
    intro i hi
    exact hn ⟨i,hz ▸ hi⟩
  have hs := (untouched_fibre_intrinsic W h.source_analytic T z hMiss).1
  have hSing := mem_singularSet_iff.mp (hs.mpr (hz ▸ hx))
  obtain ⟨d,hd⟩ := h.target_smooth.2 z hSing.1
  exact hSing.2 d hd

/-- Both first-hit indices exist and the larger HS profile has the
strictly earlier physical raw slot. No eventual-hit assumption is needed. -/
theorem exists_ordered_first_hits_of_original_profiles
    {W K : Set X} {E : List (Set X)} {T : BlowupTower X Y} {L : List (ℕ → ℕ)}
    (h : LabelledNativeTower n W E K T L)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hxs : x ∈ singularSet (n := n) W) (hys : y ∈ singularSet (n := n) W)
    (hLess : toLex (HS[W] x) < toLex (HS[W] y)) :
    ∃ i j, i < j ∧ y ∈ slotFootprint T i ∧ x ∈ slotFootprint T j ∧
      (∀ k < i, y ∉ slotFootprint T k) ∧ (∀ k < j, x ∉ slotFootprint T k) := by
  classical
  have hX := exists_hit_original_singular h hxs
  have hY := exists_hit_original_singular h hys
  let i := Nat.find hY
  let j := Nat.find hX
  have hj := Nat.find_spec hX
  obtain ⟨k,hkj,hk⟩ := higher_original_profile_hit_first h hx hy hxs hys hLess j hj
  refine ⟨i,j,(Nat.find_min' hY hk).trans_lt hkj,Nat.find_spec hY,hj,?_,?_⟩
  · exact fun _ hk => Nat.find_min hY hk
  · exact fun _ hk => Nat.find_min hX hk


/-- The first occupied hit of a base point lifts to the first occupied
hit of that same point on the full larger tower, regardless of its extra
stages outside the earlier comparison window. -/
theorem first_hit_preserved_by_occupiedLiftOnOpen
    {A B : CMfd.{0} n} {T : BlowupTower X Y} (S : BlowupTower A B) (V : Opens A)
    {φ : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V}
    {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage S V)}
    (h : EmptyAwareTowerIso φ T (restrict V S) ψ) (x : X) (p : {i // Occupied T i})
    (hHit : x ∈ slotFootprint T p.val) (hFirst : ∀ k < p.val, x ∉ slotFootprint T k) :
    (φ x).val ∈ slotFootprint S (occupiedLiftOnOpen V S h p).val ∧
    ∀ k < (occupiedLiftOnOpen V S h p).val, (φ x).val ∉ slotFootprint S k := by
  have hFp := slotFootprint_occupiedComparison h p
  rw [slotFootprint_restrict] at hFp
  refine ⟨?_,?_⟩
  · rw [hFp] at hHit
    exact hHit
  · intro k hk hHitS
    have hV : Occupied (restrict V S) k :=
      (occupied_restrict_iff_slotFootprint_meets S V k).mpr ⟨(φ x).val,hHitS,(φ x).property⟩
    obtain ⟨q,hq⟩ := (occupiedComparison h).surjective ⟨k,hV⟩
    have hqLess : q < p := by
      apply (occupiedComparison h).lt_iff_lt.mp
      rw [hq]
      exact hk
    have hFq := slotFootprint_occupiedComparison h q
    rw [slotFootprint_restrict,hq] at hFq
    apply hFirst q.val hqLess
    rw [hFq]
    exact hHitS


end
end Hironaka.HironakaG8FirstFootprintOrder
