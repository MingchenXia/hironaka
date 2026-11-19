import Hironaka.Resolution.HironakaG8ClassStep
import Hironaka.Resolution.HironakaG8LocalTransport
import Hironaka.Resolution.HironakaG8LocalContactStage
import Hironaka.Invariant.DropMembers

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The lower ideals of class-equivalent marked ideals are locally equivalent, level `0` (G8C lane, run 0080, round 2;
(B') plan module 10)

Blueprint: `hironaka-g8-class-step-lower.tex`.  Plan: lane G11B's `BPRIME-PLAN.md` §6c ("Modules 10--13"); the predicate
`HironakaG8ClassStep.LowerPairs`.  Source: Bierstone--Milman 2008, §5 Step I.A ("the marked ideals `𝒞_U(ℐ)` and `𝒞_V(ℐ)` ...
are equivalent in `U ∩ V` (since both are equivalent to `ℐ_{U∩V}`)") and Step I.B (the case `s = 0`: the centres of the
lower resolution avoid `E`).

For two marked ideals `A ≈ B` of the domain of maximal order (`LocWPEquiv`, the same divisor), along every multiple test
blow-up `T₀` of `J̄_A`, at a point `y₀` of the cosupport, on every open `O` of the stage inside both masks of level `0`, the two
lower ideals (Bierstone--Milman's coefficient ideals of `A_∅`, `B_∅` on maximal contact, transformed along `T₀`) are
`LocWPEquiv`: both are equivalent to the transforms of `A_∅`, `B_∅` there (lane G8's P4 `locWPEquiv_stage_contactCoeffBM`, moved
to `O` by lane G8's `locWPEquiv_restrict_of_le`), and on `O` these are the transforms of `A`, `B` with the original members
dropped, which are EMPTY on the mask (`maskB` avoids them), so the equivalence `A_{T₀}|_O ≈ B_{T₀}|_O` passes to them.

* **`locEquiv_drop`**: dropping members that are empty sets keeps a local equivalence (kinds without exceptional blowups),
  by the coinduction principle `HironakaG8LocalStable.LocEquiv.of_isLocStable` (`DropRel`, `isLocStable_dropRel`);
* **`locWPEquiv_lowerIdealBM_zero`**: the level-`0` lower ideals of `A ≈ B` restricted to a common open of the masks are
  `LocWPEquiv`.

Sorry-free.  Import discipline: no import of `Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8ClassStepLower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.BlowupStrictSubmanifold
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalStable
  Hironaka.MarkedIdealBiholomorphism
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv)
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)

noncomputable section

/-! ### Dropping empty members -/

section Drop

/-- **The relation of the coinduction**: `P'`, `Q'` are a locally equivalent pair `P ≈ Q` with a list `F` of EMPTY members
removed from the front of the boundary. -/
def DropRel (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} (P' Q' : MarkedIdeal m Y) : Prop :=
  ∃ (P Q : MarkedIdeal m Y) (F G : List (Set Y)), LocEquiv κ P Q ∧ P.E = F ++ G ∧ (∀ H ∈ F, H = ∅) ∧
    P' = { P with E := G } ∧ Q' = { Q with E := G }

/-- **Dropping empty members is stable under the local test actions.** -/
theorem isLocStable_dropRel (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => DropRel κ (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P' Q' ⟨P, Q, F, G, -, -, -, rfl, rfl⟩
    rfl
  cosupp_eq := by
    rintro m Y P' Q' ⟨P, Q, F, G, h, -, -, rfl, rfl⟩
    exact h.cosupp_eq_base
  controlled := by
    rintro m Y P' Q' ⟨P, Q, F, G, h, hPE, hF, rfl, rfl⟩ C Z π hπ hC
    have hCP : P.IsAdmissibleCentre C := by
      refine ⟨hC.1, hC.2.1, ?_⟩
      rw [hPE]
      refine DropMembers.hasNormalCrossings_of_forall_disjoint hC.2.2 fun H hH hHG => ?_
      rcases List.mem_append.mp hH with h1 | h1
      · rw [hF H h1]
        exact Set.disjoint_empty _
      · exact absurd h1 hHG
    refine ⟨P.geoTransform C π, Q.geoTransform C π, F.map (geoStrictTransform π C),
      G.map (geoStrictTransform π C) ++ [π ⁻¹' C], (isLocStable_locEquiv κ).controlled h C π hπ hCP, ?_, ?_, rfl, rfl⟩
    · show P.E.map (geoStrictTransform π C) ++ [π ⁻¹' C] =
        F.map (geoStrictTransform π C) ++ (G.map (geoStrictTransform π C) ++ [π ⁻¹' C])
      rw [hPE, List.map_append, List.append_assoc]
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      rw [hF H₀ hH₀]
      show closure (π ⁻¹' (∅ \ C)) = ∅
      simp
  projection := by
    rintro hp m Y P' Q' ⟨P, Q, F, G, h, hPE, hF, rfl, rfl⟩
    refine ⟨projectionTest P, projectionTest Q, F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·),
      G.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y], (isLocStable_locEquiv κ).projection hp h, ?_,
      ?_, rfl, rfl⟩
    · show P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y] =
        F.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++
          (G.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y])
      rw [hPE, List.map_append, List.append_assoc]
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      rw [hF H₀ hH₀, Set.preimage_empty]
  restrict := by
    rintro m Y P' Q' ⟨P, Q, F, G, h, hPE, hF, rfl, rfl⟩ U
    refine ⟨MarkedIdeal.pullback (Subtype.val : U → Y) P, MarkedIdeal.pullback (Subtype.val : U → Y) Q,
      F.map ((Subtype.val : U → Y) ⁻¹' ·), G.map ((Subtype.val : U → Y) ⁻¹' ·), (isLocStable_locEquiv κ).restrict h U,
      ?_, ?_, rfl, rfl⟩
    · show P.E.map ((Subtype.val : U → Y) ⁻¹' ·) = _
      rw [hPE, List.map_append]
    · intro H hH
      obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      rw [hF H₀ hH₀, Set.preimage_empty]

/-- **Dropping empty members keeps a local equivalence** (kinds without exceptional blowups): if `P ≈ Q` and the boundary
of `P` is `F ++ G` with every member of `F` empty, then `P ≈ Q` with boundary `G`. -/
theorem locEquiv_drop {κ : Kinds} (hexc : κ.exc = false) {n : ℕ} {X : CMfd.{u} n} {P Q : MarkedIdeal n X}
    (h : LocEquiv κ P Q) {F G : List (Set X)} (hE : P.E = F ++ G) (hF : ∀ H ∈ F, H = ∅) :
    LocEquiv κ { P with E := G } { Q with E := G } :=
  LocEquiv.of_isLocStable (isLocStable_dropRel κ) hexc ⟨P, Q, F, G, h, hE, hF, rfl, rfl⟩

end Drop

/-! ### The lower ideals at level `0` -/

section LevelZero

variable {n : ℕ} {X : CMfd.{0} n}

/-- **The level-`0` lower ideals of class-equivalent marked ideals are locally equivalent** on every common open of the
masks: for `A ≈ B` (`LocWPEquiv`, the same divisor) of the domain of maximal order, along a multiple test blow-up `T₀` of `J̄_A`,
at a point `y₀` of the cosupport, on an open `O` inside `maskBM A 0 T₀ y₀ ⊓ maskBM B 0 T₀ y₀`, the restrictions of
`lowerIdealBM A 0 T₀ y₀` and `lowerIdealBM B 0 T₀ y₀` are `LocWPEquiv` (BM08 §5 Step I.A, Corollary 4.2). -/
theorem locWPEquiv_lowerIdealBM_zero (hn : 0 < n) {k k' : ℕ} {A B : MarkedIdeal n X} (hA : IsInvDomain k A)
    (hB : IsInvDomain k' B) (hmA : IsMaximalOrderAlong A.N A.ideal A.d) (hmB : IsMaximalOrderAlong B.N B.ideal B.d)
    (h : LocWPEquiv A B) (hE : A.E = B.E) {Y₀ : CMfd.{0} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked A) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked A) T₀).cosupp)
    (O : Opens Y₀) (hOA : O ≤ maskBM A 0 T₀ y₀) (hOB : O ≤ maskBM B 0 T₀ y₀) :
    LocWPEquiv (X := CMfd.of (n := n) O) (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM A 0 T₀ y₀))
      (MarkedIdeal.pullback (Subtype.val : O → Y₀) (lowerIdealBM B 0 T₀ y₀)) := by
  have hWA : WEquiv (barMarked A) A := StepOneBridge.barMarked_wEquiv A hA
  have hWB : WEquiv (barMarked B) B := StepOneBridge.barMarked_wEquiv B hB
  have hW : WEquiv A B := LocEquiv.wEquiv h
  have hTA : IsGeoTestTower A T₀ := (hWA.2 T₀).1.mp hT₀
  have hTB : IsGeoTestTower B T₀ := (hW.2 T₀).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) T₀ := (hWB.2 T₀).1.mpr hTB
  have hyA : y₀ ∈ (geoTransformAlong A T₀).cosupp := (hWA.2 T₀).2 hT₀ ▸ hy₀
  have hyB : y₀ ∈ (geoTransformAlong (barMarked B) T₀).cosupp := by
    rw [(hWB.2 T₀).2 hTJB, ← (hW.2 T₀).2 hTA]
    exact hyA
  -- the tangent directions chosen at the base point
  obtain ⟨-, hwA⟩ := StepOneLowerDomain.tangentChoice_spec A
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp A hA.isWellFormed hA.one_le_d hmA T₀ hT₀ hy₀)
  obtain ⟨-, hwB⟩ := StepOneLowerDomain.tangentChoice_spec B
    (StepOneLowerDomain.exists_tangent_of_mem_cosupp B hB.isWellFormed hB.one_le_d hmB T₀ hTJB hyB)
  let UA : Opens X := ⟨(tangentChoice A (T₀.proj y₀)).1, hwA.isOpen⟩
  let UB : Opens X := ⟨(tangentChoice B (T₀.proj y₀)).1, hwB.isOpen⟩
  have hOUA : O ≤ openPreimage T₀ UA := fun z hz => (interior_subset (hOA hz)).1
  have hOUB : O ≤ openPreimage T₀ UB := fun z hz => (interior_subset (hOB hz)).1
  -- coherence of the ideals involved
  have hcohA := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := emptyBoundary A) hA.isWellFormed.isClosedSubmanifold_N hA.isWellFormed.isCoherent T₀
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary A T₀ hTA)).2
  have hcohB := (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
    (𝔪 := emptyBoundary B) hB.isWellFormed.isClosedSubmanifold_N hB.isWellFormed.isCoherent T₀
    (HironakaG11InvBMStage.isGeoTestTower_emptyBoundary B T₀ hTB)).2
  have hcLA := HironakaG11InvBMRebase.isCoherent_lowerIdealBM A hA.isWellFormed hA.one_le_d hn T₀ hT₀ y₀ 0
  have hcLB := HironakaG11InvBMRebase.isCoherent_lowerIdealBM B hB.isWellFormed hB.one_le_d hn T₀ hTJB y₀ 0
  -- P4 (BM08 Cor 4.2) at the stage, moved to `O`
  have h4A := HironakaG8LocalTransport.locWPEquiv_restrict_of_le hcohA hcLA hOUA
    (HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM hA.isWellFormed hA.one_le_d UA hwA T₀ hTA)
  have h4B := HironakaG8LocalTransport.locWPEquiv_restrict_of_le hcohB hcLB hOUB
    (HironakaG8LocalContactStage.locWPEquiv_stage_contactCoeffBM hB.isWellFormed hB.one_le_d UB hwB T₀ hTB)
  -- the transforms of `A`, `B` restricted to `O`, with the (empty) original members dropped
  have hmid := (h.geoTransformAlong T₀ hTA).restrict O
  have hEAB : (geoTransformAlong A T₀).E = (geoTransformAlong B T₀).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq hE T₀
  have hsplit : (MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong A T₀)).E =
      ((geoTransformAlong A T₀).E.take A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·) ++
        ((geoTransformAlong A T₀).E.drop A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·) := by
    show (geoTransformAlong A T₀).E.map ((Subtype.val : O → Y₀) ⁻¹' ·) = _
    rw [← List.map_append, List.take_append_drop]
  have hempty : ∀ H ∈ ((geoTransformAlong A T₀).E.take A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·), H = ∅ := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    have hH₀' : H₀ ∈ origMembers A T₀ := by
      show H₀ ∈ (geoTransformAlong (barMarked A) T₀).E.take A.E.length
      rw [MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq (𝔪 := barMarked A) (𝔫 := A) rfl T₀]
      exact hH₀
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    exact (interior_subset (hOA z.2)).2.1 H₀ hH₀' hz
  have hdrop := locEquiv_drop rfl hmid hsplit hempty
  have hAe : MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong (emptyBoundary A) T₀) =
      { MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong A T₀) with
        E := ((geoTransformAlong A T₀).E.drop A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·) } := by
    rw [HironakaG11InvBMStage.geoTransformAlong_emptyBoundary A T₀]
    rfl
  have hBe : MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong (emptyBoundary B) T₀) =
      { MarkedIdeal.pullback (Subtype.val : O → Y₀) (geoTransformAlong B T₀) with
        E := ((geoTransformAlong A T₀).E.drop A.E.length).map ((Subtype.val : O → Y₀) ⁻¹' ·) } := by
    rw [HironakaG11InvBMStage.geoTransformAlong_emptyBoundary B T₀, hEAB, ← hE]
    rfl
  rw [← hAe, ← hBe] at hdrop
  exact h4A.symm.trans (hdrop.trans h4B)

end LevelZero

end

end Hironaka.HironakaG8ClassStepLower
