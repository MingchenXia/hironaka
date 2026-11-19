import Hironaka.Resolution.HironakaG8MemberLocalRelation
import Hironaka.Resolution.HironakaG8ClassStepCut
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8MemberCutStable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  CoefficientIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdealAlongRestrictionTower DerivativeIdealAlong DerivativeIdealAlongCoherent RestrictedIdealWeight
  RestrictLeCalculus BlowupStrictSubmanifold BlowupFunctionTransform MarkedIdealBiholomorphism
  HironakaG8ContactGood HironakaG8LocalHistory HironakaG8LocalStable HironakaG8LocalContact
  HironakaG8MemberLocalRelation HironakaG8ClassStepCut NormalCrossings
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)
open scoped ProductComplexManifold
noncomputable section

def MemberCutR (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m} (Q Q' : MarkedIdeal m Y) : Prop :=
  ∃ (P R : MarkedIdeal m Y) (F : List (Set Y)) (S : Set Y) (D D' : ℕ → MarkedIdeal m Y),
    P.E = R.E ∧
    LocEquiv κ { P with E := F ++ P.E } { R with E := F ++ P.E } ∧
    IsSNCDivisor m (F ++ P.E) ∧
    (∀ H ∈ F, S ⊆ H ∨ H = ∅) ∧ MemberRel P Q D S ∧ MemberRel R Q' D' S

theorem memberCut_E_eq {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : MemberCutR κ Q Q') : Q'.E = Q.E := by
  obtain ⟨P,R,F,S,D,D',hE,_,_,_,hQ,hQ'⟩ := h
  exact hQ'.E_eq.trans (hE.symm.trans hQ.E_eq.symm)

theorem memberCut_cosupp_eq {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : MemberCutR κ Q Q') : Q.cosupp = Q'.cosupp := by
  obtain ⟨P,R,F,S,D,D',hE,hL,_,_,hQ,hQ'⟩ := h
  rw [← hQ.cosupp_eq, ← hQ'.cosupp_eq]
  exact congrArg (· ∩ S) hL.cosupp_eq_base

theorem memberCut_step {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : MemberCutR κ Q Q') (C : Set Y) {Z : CMfd.{u} m} (π : Z → Y)
    (hπ : IsBlowupAlong m C π) (hC : Q.IsAdmissibleCentre C) :
    MemberCutR κ (Q.geoTransform C π) (Q'.geoTransform C π) := by
  obtain ⟨P,R,F,S,D,D',hE,hL,hSNC,hFS,hQ,hQ'⟩ := h
  have hCS : C ⊆ S := fun x hx => ((hQ.cosupp_eq ▸ hC.2.1 hx) : x ∈ P.cosupp ∩ S).2
  have hCP : P.IsAdmissibleCentre C :=
    ⟨hC.1, fun x hx => ((hQ.cosupp_eq ▸ hC.2.1 hx) : x ∈ P.cosupp ∩ S).1,
      by rw [← hQ.E_eq]; exact hC.2.2⟩
  have hCR : R.IsAdmissibleCentre C :=
    ⟨hC.1, fun x hx => by
      have hp := hCP.2.1 hx
      exact hL.cosupp_eq_base ▸ hp,
      by rw [← hE, ← hQ.E_eq]; exact hC.2.2⟩
  have hNC : HasNormalCrossings m C (F ++ P.E) := by
    refine HironakaG11InvBMAdmissible.hasNormalCrossings_append_of_dichotomy hSNC hCP.2.2
      (fun H hH => ?_)
    rcases hFS H hH with hsub | rfl
    · exact Or.inl (Set.Subset.trans hCS hsub)
    · exact Or.inr (Set.disjoint_empty _)
  have hCA : ({ P with E := F ++ P.E } : MarkedIdeal m Y).IsAdmissibleCentre C :=
    ⟨hCP.1,hCP.2.1,hNC⟩
  have hLA := (isLocStable_locEquiv κ).controlled hL C π hπ hCA
  refine ⟨P.geoTransform C π, R.geoTransform C π, F.map (geoStrictTransform π C),
    geoStrictTransform π C S, fun i => (D i).geoTransform C π,
    fun i => (D' i).geoTransform C π, ?_, ?_, ?_, ?_,
    hQ.geoTransform hπ hCP hCS, hQ'.geoTransform hπ hCR hCS⟩
  · simp only [geoTransform_E,hE]
  · have hAP : ({ P with E := F ++ P.E } : MarkedIdeal m Y).geoTransform C π =
        { P.geoTransform C π with E := F.map (geoStrictTransform π C) ++ (P.geoTransform C π).E } := by
      show { P.geoTransform C π with E := (F ++ P.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] } = _
      rw [List.map_append, List.append_assoc]
      rfl
    have hBR : ({ R with E := F ++ P.E } : MarkedIdeal m Y).geoTransform C π =
        { R.geoTransform C π with E := F.map (geoStrictTransform π C) ++ (P.geoTransform C π).E } := by
      show { R.geoTransform C π with E := (F ++ P.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] } = _
      rw [List.map_append, List.append_assoc]
      rfl
    rw [hAP,hBR] at hLA
    exact hLA
  · simpa only [geoTransform_E, List.map_append, List.append_assoc] using
      SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hSNC hNC
  · intro H hH
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    rcases hFS H₀ hH₀ with hsub | rfl
    · exact Or.inl (geoStrictTransform_mono' π C hsub)
    · exact Or.inr (by simp [geoStrictTransform])

theorem memberCut_projection {κ : Kinds} (hp : κ.proj = true)
    {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : MemberCutR κ Q Q') : MemberCutR κ (projectionTest Q) (projectionTest Q') := by
  obtain ⟨P,R,F,S,D,D',hE,hL,hSNC,hFS,hQ,hQ'⟩ := h
  have hEP : ∀ A B : MarkedIdeal m Y, A.E = B.E → (projectionTest A).E = (projectionTest B).E := by
    intro A B hAB
    simp only [projectionTest, hAB]
  let f : projectionAmbient Y → Y := Prod.fst
  have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
  refine ⟨projectionTest P, projectionTest R, F.map (f ⁻¹' ·), f ⁻¹' S,
    fun i => projectionTest (D i), fun i => projectionTest (D' i), hEP _ _ hE, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := (isLocStable_locEquiv κ).projection hp hL
    have hAP : projectionTest ({ P with E := F ++ P.E } : MarkedIdeal m Y) =
        { projectionTest P with E := F.map (f ⁻¹' ·) ++ (projectionTest P).E } := by
      change { projectionTest P with E := (F ++ P.E).map (f ⁻¹' ·) ++ [horizontal Y] } = _
      rw [List.map_append, List.append_assoc]
      rfl
    have hBR : projectionTest ({ R with E := F ++ P.E } : MarkedIdeal m Y) =
        { projectionTest R with E := F.map (f ⁻¹' ·) ++ (projectionTest P).E } := by
      change { projectionTest R with E := (F ++ P.E).map (f ⁻¹' ·) ++ [horizontal Y] } = _
      rw [List.map_append, List.append_assoc]
      rfl
    rw [hAP,hBR] at hh
    exact hh
  · have hs := isSNCDivisor_projectionTest (A := ({ P with E := F ++ P.E } : MarkedIdeal m Y)) hSNC
    change IsSNCDivisor (m+1) ((F ++ P.E).map (f ⁻¹' ·) ++ [horizontal Y]) at hs
    change IsSNCDivisor (m+1) (F.map (f ⁻¹' ·) ++ (P.E.map (f ⁻¹' ·) ++ [horizontal Y]))
    simpa only [List.map_append, List.append_assoc] using hs
  · intro H hH
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    rcases hFS H₀ hH₀ with hsub | rfl
    · exact Or.inl (Set.preimage_mono hsub)
    · exact Or.inr (Set.preimage_empty)
  · exact hQ.pullback hf rfl rfl rfl (fun _ => rfl) (fun i hi => hEP _ _ (hQ.fE i hi))
      (fun _ => rfl) (fun _ => rfl) rfl (hEP _ _ hQ.E_eq) rfl rfl
  · exact hQ'.pullback hf rfl rfl rfl (fun _ => rfl) (fun i hi => hEP _ _ (hQ'.fE i hi))
      (fun _ => rfl) (fun _ => rfl) rfl (hEP _ _ hQ'.E_eq) rfl rfl

theorem memberCut_restrict {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : MemberCutR κ Q Q') (U : Opens Y) :
    MemberCutR κ (Y := CMfd.of (n := m) U) (MarkedIdeal.pullback (Subtype.val : U → Y) Q)
      (MarkedIdeal.pullback (Subtype.val : U → Y) Q') := by
  obtain ⟨P,R,F,S,D,D',hE,hL,hSNC,hFS,hQ,hQ'⟩ := h
  let f : U → Y := Subtype.val
  have hf := HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val (n := m) U
  refine ⟨MarkedIdeal.pullback f P, MarkedIdeal.pullback f R, F.map (f ⁻¹' ·), f ⁻¹' S,
    fun i => MarkedIdeal.pullback f (D i), fun i => MarkedIdeal.pullback f (D' i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MarkedIdeal.pullback,hE]
  · have hh := (isLocStable_locEquiv κ).restrict hL U
    simpa only [MarkedIdeal.pullback, List.map_append, hE] using hh
  · change IsSNCDivisor m (F.map (f ⁻¹' ·) ++ P.E.map (f ⁻¹' ·))
    simpa only [List.map_append, f] using
      (HironakaBaseChange.isOpenHoloEmbedding_val (n := m) U).isSNCDivisor_map_preimage hSNC
  · intro H hH
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    rcases hFS H₀ hH₀ with hsub | rfl
    · exact Or.inl (Set.preimage_mono hsub)
    · exact Or.inr Set.preimage_empty
  · exact hQ.pullback (r := 0) (Y' := CMfd.of (n := m) U) hf rfl rfl rfl (fun _ => rfl)
      (fun i hi => by simp only [MarkedIdeal.pullback, hQ.fE i hi]) (fun _ => rfl)
      (fun _ => rfl) rfl (by simp only [MarkedIdeal.pullback, hQ.E_eq, f]) rfl rfl
  · exact hQ'.pullback (r := 0) (Y' := CMfd.of (n := m) U) hf rfl rfl rfl (fun _ => rfl)
      (fun i hi => by simp only [MarkedIdeal.pullback, hQ'.fE i hi]) (fun _ => rfl)
      (fun _ => rfl) rfl (by simp only [MarkedIdeal.pullback, hQ'.E_eq, f]) rfl rfl

theorem isLocStable_memberCut (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} Q Q' => MemberCutR κ (m := m) (Y := Y) Q Q') where
  E_eq h := memberCut_E_eq h
  cosupp_eq h := memberCut_cosupp_eq h
  controlled := by
    intro m Y Q Q' h C Z π hπ hC
    exact memberCut_step h C π hπ hC
  projection := by
    intro hp m Y Q Q' h
    exact memberCut_projection hp h
  restrict := by
    intro m Y Q Q' h U
    exact memberCut_restrict h U

theorem memberLocal_of_split {κ : Kinds} (hexc : κ.exc = false)
    {n : ℕ} {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hL : LocEquiv κ A B) {F G : List (Set X)} (hE : A.E = F ++ G)
    {S : Set X} (hS : IsClosedSubmanifold n S) (hSA : S ⊆ A.N) (hSB : S ⊆ B.N)
    (hFS : ∀ H ∈ F, S ⊆ H ∨ H = ∅) :
    LocEquiv κ { withN (coeffMarkedAlong A) S with E := G }
      { withN (coeffMarkedAlong B) S with E := G } := by
  let P : MarkedIdeal n X := { A with E := G }
  let R : MarkedIdeal n X := { B with E := G }
  have hP : MemberRel P { withN (coeffMarkedAlong A) S with E := G }
      (fun i => derivMarkedAlong P i) S := by
    have h := memberRel_base P hA.isClosedSubmanifold_N hA.isCoherent hdA hS hSA
    simpa [P, withN, coeffMarkedAlong, HomogenizedIdealAlong.derivMarkedAlong,
      CoefficientIdeal.msum] using h
  have hR : MemberRel R { withN (coeffMarkedAlong B) S with E := G }
      (fun i => derivMarkedAlong R i) S := by
    have h := memberRel_base R hB.isClosedSubmanifold_N hB.isCoherent hdB hS hSB
    simpa [R, withN, coeffMarkedAlong, HomogenizedIdealAlong.derivMarkedAlong,
      CoefficientIdeal.msum] using h
  apply LocEquiv.of_isLocStable (isLocStable_memberCut κ) hexc
  refine ⟨P,R,F,S,fun i => derivMarkedAlong P i,fun i => derivMarkedAlong R i,rfl,?_,?_,hFS,hP,hR⟩
  · have hEB : B.E = F ++ G := hL.E_eq.trans hE
    have hp : ({ P with E := F ++ P.E } : MarkedIdeal n X) = A := by
      cases A
      simp_all [P]
    have hr : ({ R with E := F ++ P.E } : MarkedIdeal n X) = B := by
      cases B
      simp_all [P,R]
    rwa [hp,hr]
  · change IsSNCDivisor n (F ++ G)
    simpa only [← hE] using hA.isSNCDivisor

end
end Hironaka.HironakaG8MemberCutStable
