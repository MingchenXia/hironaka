import Hironaka.Resolution.HironakaG3SNCListPermutation
import Hironaka.Resolution.HironakaG8MemberIndexedLocal
import Hironaka.Resolution.HironakaG1MemberStageLocal
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.MarkedIdeal.GeoTransformWellFormed

/-!
# ORIGINAL member-cut local class on different parent carriers

Each actual cut has its OWN parent carrier intersected with the SAME
selected full-boundary slots. Full augmented parent well-formedness gives
actual strict-intersection transport. No target cut class, equality of
carriers, numerical invariant, or alternative BM lower engine is input.
Blueprint FIRST: `hironaka-g1-separate-carrier-member-cut.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG1SeparateCarrierMemberCut
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal CoefficientIdeal CoefficientIdealRestriction
  HomogenizedIdealAlong HomogenizedIdealAlongTower CoefficientIdealAlongRestrictionTower
  DerivativeIdealAlong DerivativeIdealAlongCoherent RestrictedIdealWeight RestrictLeCalculus
  BlowupStrictSubmanifold BlowupFunctionTransform MarkedIdealBiholomorphism
  HironakaG8ContactGood HironakaG8LocalHistory HironakaG8LocalStable HironakaG8LocalContact
  HironakaG8MemberLocalRelation HironakaG8ClassStepCut NormalCrossings
  InvDomainMemberRestriction MemberInterTowerAlong HironakaG8ClassStepPerm BoundaryCount
open Hironaka.HironakaActualProjectionTestRecord
  (projectionTest projectionAmbient horizontal)
open scoped ProductComplexManifold
noncomputable section

private def listInter {Y : Type*} (F : List (Set Y)) : Set Y := {x | ∀ H ∈ F, x ∈ H}

private def prefixSlots {Y : Type*} (F G : List (Set Y)) : Finset (Fin (F ++ G).length) :=
  (Finset.univ : Finset (Fin F.length)).map (Fin.castLEEmb (by simp only [List.length_append]; omega))

private theorem prefix_get {Y : Type*} (F G : List (Set Y)) (i : Fin F.length) :
    (F ++ G).get (Fin.castLE (by simp only [List.length_append]; omega) i) = F.get i := by
  simp only [List.get_eq_getElem, Fin.val_castLE, List.getElem_append_left i.isLt]

private theorem prefix_condition {Y Z : Type*} (F G : List (Set Y)) (f : Set Y → Set Z) :
    {z | ∀ i ∈ prefixSlots F G, z ∈ f ((F ++ G).get i)} = listInter (F.map f) := by
  ext z
  constructor
  · intro hz H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH₀
    have hi : Fin.castLE (by simp only [List.length_append]; omega) i ∈ prefixSlots F G :=
      Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa only [prefix_get] using hz _ hi
  · intro hz i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    change z ∈ f ((F ++ G).get (Fin.castLE (by simp only [List.length_append]; omega) j))
    rw [prefix_get]
    exact hz _ (List.mem_map.mpr ⟨F.get j, List.get_mem _ _, rfl⟩)

private theorem memberInter_prefix {Y : Type*} (F G : List (Set Y)) :
    memberInter (F ++ G) (prefixSlots F G) = listInter F := by
  change {z | ∀ i ∈ prefixSlots F G, z ∈ (F ++ G).get i} = listInter F
  simpa only [List.map_id_fun, id_eq] using prefix_condition F G (id : Set Y → Set Y)

private theorem listInter_preimage {Y Z : Type*} (F : List (Set Y)) (f : Z → Y) :
    listInter (F.map (f ⁻¹' ·)) = f ⁻¹' listInter F := by
  ext z
  simp only [listInter, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mem_ofPred_eq, mem_preimage]

private theorem strict_inter_list {m : ℕ} {Y Z : CMfd.{u} m} {C N : Set Y} {π : Z → Y}
    (hπ : IsBlowupAlong m C π) (hNc : IsClosed N) (hCN : C ⊆ N)
    (F G : List (Set Y)) (hE : IsSNCDivisor m (F ++ G))
    (hT : IsTransverse m N (F ++ G)) (hC : HasNormalCrossings m C (F ++ G)) :
    geoStrictTransform π C (N ∩ listInter F) =
      geoStrictTransform π C N ∩ listInter (F.map (geoStrictTransform π C)) := by
  have h := geoStrictTransform_inter_memberInter_eq hπ hNc hCN hE hT hC (prefixSlots F G)
  rw [memberInter_prefix, prefix_condition] at h
  exact h

/-- ORIGINAL cuts with separate actual parent intersections, retaining
full augmented parent WF and genuine derivative-family dictionaries. -/
def SeparateMemberCutR (κ : Kinds) {m : ℕ} {Y : CMfd.{u} m}
    (Q Q' : MarkedIdeal m Y) : Prop :=
  ∃ (P R : MarkedIdeal m Y) (F : List (Set Y)) (D D' : ℕ → MarkedIdeal m Y),
    P.E = R.E ∧
    LocEquiv κ { P with E := F ++ P.E } { R with E := F ++ P.E } ∧
    ({ P with E := F ++ P.E } : MarkedIdeal m Y).IsWellFormed ∧
    ({ R with E := F ++ P.E } : MarkedIdeal m Y).IsWellFormed ∧
    MemberRel P Q D (P.N ∩ listInter F) ∧ MemberRel R Q' D' (R.N ∩ listInter F)

private theorem separate_E_eq {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : SeparateMemberCutR κ Q Q') : Q'.E = Q.E := by
  obtain ⟨P,R,F,D,D',hE,_,_,_,hQ,hQ'⟩ := h
  exact hQ'.E_eq.trans (hE.symm.trans hQ.E_eq.symm)

private theorem separate_cosupp_eq {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : SeparateMemberCutR κ Q Q') : Q.cosupp = Q'.cosupp := by
  obtain ⟨P,R,F,D,D',_,hL,_,_,hQ,hQ'⟩ := h
  rw [← hQ.cosupp_eq, ← hQ'.cosupp_eq]
  have hcos : P.cosupp = R.cosupp := hL.cosupp_eq_base
  ext x
  constructor
  · rintro ⟨hx, _, hF⟩
    have hxR : x ∈ R.cosupp := hcos ▸ hx
    exact ⟨hxR, R.cosupp_subset_N hxR, hF⟩
  · rintro ⟨hx, _, hF⟩
    have hxP : x ∈ P.cosupp := hcos.symm ▸ hx
    exact ⟨hxP, P.cosupp_subset_N hxP, hF⟩

private theorem separate_step {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : SeparateMemberCutR κ Q Q') (C : Set Y) {Z : CMfd.{u} m} (π : Z → Y)
    (hπ : IsBlowupAlong m C π) (hC : Q.IsAdmissibleCentre C) :
    SeparateMemberCutR κ (Q.geoTransform C π) (Q'.geoTransform C π) := by
  have hcos := separate_cosupp_eq h
  obtain ⟨P,R,F,D,D',hE,hL,hWP,hWR,hQ,hQ'⟩ := h
  have hCS : C ⊆ P.N ∩ listInter F := fun x hx =>
    ((hQ.cosupp_eq ▸ hC.2.1 hx) : x ∈ P.cosupp ∩ (P.N ∩ listInter F)).2
  have hCS' : C ⊆ R.N ∩ listInter F := fun x hx =>
    ((hQ'.cosupp_eq ▸ (hcos ▸ hC.2.1 hx)) : x ∈ R.cosupp ∩ (R.N ∩ listInter F)).2
  have hCP : P.IsAdmissibleCentre C :=
    ⟨hC.1, fun x hx => ((hQ.cosupp_eq ▸ hC.2.1 hx) : x ∈ P.cosupp ∩ _).1,
      by rw [← hQ.E_eq]; exact hC.2.2⟩
  have hCR : R.IsAdmissibleCentre C :=
    ⟨hC.1, fun x hx => ((hQ'.cosupp_eq ▸ (hcos ▸ hC.2.1 hx)) : x ∈ R.cosupp ∩ _).1,
      by rw [← hE, ← hQ.E_eq]; exact hC.2.2⟩
  have hNC : HasNormalCrossings m C (F ++ P.E) :=
    HironakaG11InvBMAdmissible.hasNormalCrossings_append_of_dichotomy hWP.isSNCDivisor hCP.2.2
      (fun H hH => Or.inl (fun x hx => (hCS hx).2 H hH))
  have hCA : ({ P with E := F ++ P.E } : MarkedIdeal m Y).IsAdmissibleCentre C :=
    ⟨hCP.1,hCP.2.1,hNC⟩
  have hCB : ({ R with E := F ++ P.E } : MarkedIdeal m Y).IsAdmissibleCentre C :=
    ⟨hCR.1,hCR.2.1,hNC⟩
  have hLA := (isLocStable_locEquiv κ).controlled hL C π hπ hCA
  have hAP : ({ P with E := F ++ P.E } : MarkedIdeal m Y).geoTransform C π =
      { P.geoTransform C π with E := F.map (geoStrictTransform π C) ++ (P.geoTransform C π).E } := by
    show { P.geoTransform C π with E := (F ++ P.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] } = _
    rw [List.map_append, List.append_assoc]
    rfl
  have hBR : ({ R with E := F ++ P.E } : MarkedIdeal m Y).geoTransform C π =
      { R.geoTransform C π with E := F.map (geoStrictTransform π C) ++ (P.geoTransform C π).E } := by
    show { R.geoTransform C π with E := (F ++ P.E).map (geoStrictTransform π C) ++ [π ⁻¹' C] } = _
    rw [List.map_append, List.append_assoc]
    rfl
  refine ⟨P.geoTransform C π, R.geoTransform C π, F.map (geoStrictTransform π C),
    fun i => (D i).geoTransform C π, fun i => (D' i).geoTransform C π, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [geoTransform_E,hE]
  · rwa [hAP,hBR] at hLA
  · rw [← hAP]
    exact GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hWP hCA hπ
  · rw [← hBR]
    exact GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hWR hCB hπ
  · have hrel := hQ.geoTransform hπ hCP hCS
    rw [strict_inter_list hπ hWP.isClosedSubmanifold_N.1 hCP.subset_N F P.E
      hWP.isSNCDivisor hWP.isTransverse hNC] at hrel
    exact hrel
  · have hrel := hQ'.geoTransform hπ hCR hCS'
    rw [strict_inter_list hπ hWR.isClosedSubmanifold_N.1 hCR.subset_N F P.E
      hWR.isSNCDivisor hWR.isTransverse hNC] at hrel
    exact hrel

private theorem separate_projection {κ : Kinds} (hp : κ.proj = true)
    {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : SeparateMemberCutR κ Q Q') : SeparateMemberCutR κ (projectionTest Q) (projectionTest Q') := by
  obtain ⟨P,R,F,D,D',hE,hL,hWP,hWR,hQ,hQ'⟩ := h
  have hEP : ∀ A B : MarkedIdeal m Y, A.E = B.E → (projectionTest A).E = (projectionTest B).E := by
    intro A B hAB
    simp only [projectionTest,hAB]
  let f : projectionAmbient Y → Y := Prod.fst
  have hf := HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1)
  have hAP : projectionTest ({ P with E := F ++ P.E } : MarkedIdeal m Y) =
      { projectionTest P with E := F.map (f ⁻¹' ·) ++ (projectionTest P).E } := by
    change { projectionTest P with E := (F ++ P.E).map (f ⁻¹' ·) ++ [horizontal Y] } = _
    rw [List.map_append,List.append_assoc]
    rfl
  have hBR : projectionTest ({ R with E := F ++ P.E } : MarkedIdeal m Y) =
      { projectionTest R with E := F.map (f ⁻¹' ·) ++ (projectionTest P).E } := by
    change { projectionTest R with E := (F ++ P.E).map (f ⁻¹' ·) ++ [horizontal Y] } = _
    rw [List.map_append,List.append_assoc]
    rfl
  refine ⟨projectionTest P,projectionTest R,F.map (f ⁻¹' ·),
    fun i => projectionTest (D i),fun i => projectionTest (D' i),hEP _ _ hE,?_,?_,?_,?_,?_⟩
  · have h := (isLocStable_locEquiv κ).projection hp hL
    rwa [hAP,hBR] at h
  · rw [← hAP]
    exact isWellFormed_projectionTest hWP
  · rw [← hBR]
    exact isWellFormed_projectionTest hWR
  · change MemberRel (projectionTest P) (projectionTest Q) (fun i => projectionTest (D i))
      (f ⁻¹' P.N ∩ listInter (F.map (f ⁻¹' ·)))
    rw [listInter_preimage, ← preimage_inter]
    exact hQ.pullback hf rfl rfl rfl (fun _ => rfl) (fun i hi => hEP _ _ (hQ.fE i hi))
      (fun _ => rfl) (fun _ => rfl) rfl (hEP _ _ hQ.E_eq) rfl rfl
  · change MemberRel (projectionTest R) (projectionTest Q') (fun i => projectionTest (D' i))
      (f ⁻¹' R.N ∩ listInter (F.map (f ⁻¹' ·)))
    rw [listInter_preimage, ← preimage_inter]
    exact hQ'.pullback hf rfl rfl rfl (fun _ => rfl) (fun i hi => hEP _ _ (hQ'.fE i hi))
      (fun _ => rfl) (fun _ => rfl) rfl (hEP _ _ hQ'.E_eq) rfl rfl

private theorem separate_restrict {κ : Kinds} {m : ℕ} {Y : CMfd.{u} m} {Q Q' : MarkedIdeal m Y}
    (h : SeparateMemberCutR κ Q Q') (U : Opens Y) :
    SeparateMemberCutR κ (Y := CMfd.of (n := m) U)
      (MarkedIdeal.pullback (Subtype.val : U → Y) Q) (MarkedIdeal.pullback (Subtype.val : U → Y) Q') := by
  obtain ⟨P,R,F,D,D',hE,hL,hWP,hWR,hQ,hQ'⟩ := h
  let f : U → Y := Subtype.val
  have hf := HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val (n := m) U
  have hAP : MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f ({ P with E := F ++ P.E }) =
      { MarkedIdeal.pullback f P with E := F.map (f ⁻¹' ·) ++ (MarkedIdeal.pullback f P).E } := by
    simp only [MarkedIdeal.pullback,List.map_append]
  have hBR : MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f ({ R with E := F ++ P.E }) =
      { MarkedIdeal.pullback f R with E := F.map (f ⁻¹' ·) ++ (MarkedIdeal.pullback f P).E } := by
    simp only [MarkedIdeal.pullback,List.map_append]
  refine ⟨MarkedIdeal.pullback f P,MarkedIdeal.pullback f R,F.map (f ⁻¹' ·),
    fun i => MarkedIdeal.pullback f (D i),fun i => MarkedIdeal.pullback f (D' i),?_,?_,?_,?_,?_,?_⟩
  · simp only [MarkedIdeal.pullback,hE]
  · have hh := (isLocStable_locEquiv κ).restrict hL U
    rwa [hAP,hBR] at hh
  · rw [← hAP]
    exact MarkedIdealRestrictOpen.IsWellFormed.pullback_val hWP U
  · rw [← hBR]
    exact MarkedIdealRestrictOpen.IsWellFormed.pullback_val hWR U
  · change MemberRel (MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f P) (MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f Q)
      (fun i => MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f (D i)) (f ⁻¹' P.N ∩ listInter (F.map (f ⁻¹' ·)))
    rw [listInter_preimage, ← preimage_inter]
    exact hQ.pullback (r := 0) (Y' := CMfd.of (n := m) U) hf rfl rfl rfl (fun _ => rfl)
      (fun i hi => by simp only [MarkedIdeal.pullback,hQ.fE i hi]) (fun _ => rfl)
      (fun _ => rfl) rfl (by simp only [MarkedIdeal.pullback,hQ.E_eq,f]) rfl rfl
  · change MemberRel (MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f R) (MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f Q')
      (fun i => MarkedIdeal.pullback (M' := CMfd.of (n := m) U) f (D' i)) (f ⁻¹' R.N ∩ listInter (F.map (f ⁻¹' ·)))
    rw [listInter_preimage, ← preimage_inter]
    exact hQ'.pullback (r := 0) (Y' := CMfd.of (n := m) U) hf rfl rfl rfl (fun _ => rfl)
      (fun i hi => by simp only [MarkedIdeal.pullback,hQ'.fE i hi]) (fun _ => rfl)
      (fun _ => rfl) rfl (by simp only [MarkedIdeal.pullback,hQ'.E_eq,f]) rfl rfl

/-- ORIGINAL cut dictionaries on carrier-specific intersections are stable
under the full controlled/product/open weak-test calculus. -/
theorem isLocStable_separateMemberCut (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} Q Q' => SeparateMemberCutR κ (m := m) (Y := Y) Q Q') where
  E_eq := separate_E_eq
  cosupp_eq := separate_cosupp_eq
  controlled := by
    intro m Y Q Q' h C Z π hπ hC
    exact separate_step h C π hπ hC
  projection := by
    intro hp m Y Q Q' h
    exact separate_projection hp h
  restrict := by
    intro m Y Q Q' h U
    exact separate_restrict h U

private theorem memberLocal_of_split {κ : Kinds} (hexc : κ.exc = false)
    {n : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hL : LocEquiv κ A B) {F G : List (Set X)} (hE : A.E = F ++ G) :
    LocEquiv κ { withN (coeffMarkedAlong A) (A.N ∩ listInter F) with E := G }
      { withN (coeffMarkedAlong B) (B.N ∩ listInter F) with E := G } := by
  let P : MarkedIdeal n X := { A with E := G }
  let R : MarkedIdeal n X := { B with E := G }
  have hEB : B.E = F ++ G := hL.E_eq.trans hE
  have hPA : ({ P with E := F ++ P.E } : MarkedIdeal n X) = A := by
    cases A
    simp_all [P]
  have hRB : ({ R with E := F ++ P.E } : MarkedIdeal n X) = B := by
    cases B
    simp_all [P,R]
  have hSA : IsClosedSubmanifold n (A.N ∩ listInter F) := by
    have ht : IsTransverse n A.N (F ++ G) := hE ▸ hA.isTransverse
    have hs : IsSNCDivisor n (F ++ G) := hE ▸ hA.isSNCDivisor
    simpa only [memberInter_prefix] using MemberInterAlong.isClosedSubmanifold_inter_memberInter
      hn hA.isClosedSubmanifold_N.1 hs ht (prefixSlots F G)
  have hSB : IsClosedSubmanifold n (B.N ∩ listInter F) := by
    have ht : IsTransverse n B.N (F ++ G) := hEB ▸ hB.isTransverse
    have hs : IsSNCDivisor n (F ++ G) := hEB ▸ hB.isSNCDivisor
    simpa only [memberInter_prefix] using MemberInterAlong.isClosedSubmanifold_inter_memberInter
      hn hB.isClosedSubmanifold_N.1 hs ht (prefixSlots F G)
  have hP : MemberRel P { withN (coeffMarkedAlong A) (A.N ∩ listInter F) with E := G }
      (fun i => derivMarkedAlong P i) (P.N ∩ listInter F) := by
    have h := memberRel_base P hA.isClosedSubmanifold_N hA.isCoherent hdA hSA inter_subset_left
    simpa [P,withN,coeffMarkedAlong,HomogenizedIdealAlong.derivMarkedAlong,CoefficientIdeal.msum] using h
  have hR : MemberRel R { withN (coeffMarkedAlong B) (B.N ∩ listInter F) with E := G }
      (fun i => derivMarkedAlong R i) (R.N ∩ listInter F) := by
    have h := memberRel_base R hB.isClosedSubmanifold_N hB.isCoherent hdB hSB inter_subset_left
    simpa [R,withN,coeffMarkedAlong,HomogenizedIdealAlong.derivMarkedAlong,CoefficientIdeal.msum] using h
  apply LocEquiv.of_isLocStable (isLocStable_separateMemberCut κ) hexc
  refine ⟨P,R,F,fun i => derivMarkedAlong P i,fun i => derivMarkedAlong R i,rfl,?_,?_,?_,hP,hR⟩
  · rwa [hPA,hRB]
  · rwa [hPA]
  · rwa [hRB]

private theorem snc_map_perm_finRange {n : ℕ} {X : CMfd.{u} n} (E : List (Set X))
    (L : List (Fin E.length)) (hL : L.Perm (List.finRange E.length)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor n (L.map E.get) :=
  HironakaG3SNCListPermutation.snc_map_perm_finRange E L hL hE

/-- SAME literal selected slots, OWN parent carrier intersections; the
actual full coefficient ideals, true marks and remaining slots are retained. -/
theorem memberLocal_of_indexed {κ : Kinds} (hexc : κ.exc = false)
    {n : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hL : LocEquiv κ A B) (I : Finset (Fin A.E.length)) :
    LocEquiv κ (memberRestrict A I)
      { withN (coeffMarkedAlong B) (B.N ∩ memberInter A.E I) with E := (memberRestrict A I).E } := by
  let p : Fin A.E.length → Bool := fun i => decide (i ∈ I)
  let L₁ := (List.finRange A.E.length).filter p
  let L₂ := (List.finRange A.E.length).filter (fun i => !p i)
  let F := L₁.map A.E.get
  let G := L₂.map A.E.get
  let L := F ++ G
  have hpermI : (L₁ ++ L₂).Perm (List.finRange A.E.length) := List.filter_append_perm p _
  have hperm : L.Perm A.E := by
    have h := hpermI.map A.E.get
    simpa [L,F,G,List.map_append,List.map_get_finRange] using h
  let A' : MarkedIdeal n X := { A with E := L }
  let B' : MarkedIdeal n X := { B with E := L }
  have hLA : LocEquiv κ A' B' := locEquiv_perm hexc hL hperm
  have hSNC : IsSNCDivisor n L := by
    simpa only [L,F,G,List.map_append] using snc_map_perm_finRange A.E (L₁ ++ L₂) hpermI hA.isSNCDivisor
  have hsub : ∀ H ∈ L, H ∈ A.E := fun _ hH => hperm.subset hH
  have hsubB : ∀ H ∈ L, H ∈ B.E := fun H hH => hL.E_eq ▸ hsub H hH
  have hA' : A'.IsWellFormed := ⟨hA.isClosedSubmanifold_N,hA.isCoherent,hSNC,
    NormalCrossingsComparison.isTransverse_of_forall_mem hA.isTransverse hsub⟩
  have hB' : B'.IsWellFormed := ⟨hB.isClosedSubmanifold_N,hB.isCoherent,hSNC,
    NormalCrossingsComparison.isTransverse_of_forall_mem hB.isTransverse hsubB⟩
  have hF : listInter F = memberInter A.E I := by
    ext x
    constructor
    · intro hx i hi
      apply hx (A.E.get i)
      exact List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨List.mem_finRange i,by simpa only [p,decide_eq_true_eq] using hi⟩,rfl⟩
    · intro hx H hH
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
      exact hx i (by simpa only [L₁,p,decide_eq_true_eq] using (List.mem_filter.mp hi).2)
  have hEq := memberLocal_of_split hexc hn hA' hB' hdA hdB hLA (F := F) (G := G) rfl
  rw [hF] at hEq
  simpa [A',B',G,L₂,p,memberRestrict,withN,coeffMarkedAlong,
    HomogenizedIdealAlong.derivMarkedAlong,CoefficientIdeal.msum] using hEq

/-- The ACTUAL original members through a point give full local class on
their separate parent intersections. No parent N/dimension equality. -/
theorem memberLocal_membersThrough {κ : Kinds} (hexc : κ.exc = false)
    {n : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hL : LocEquiv κ A B) (E₀ : List (Set X)) (x : X) :
    LocEquiv κ (memberRestrict A (membersThrough A.E E₀ x))
      (memberRestrict B (membersThrough B.E E₀ x)) := by
  obtain ⟨NA,EA,IA,dA⟩ := A
  obtain ⟨NB,EB,IB,dB⟩ := B
  have hE : EB = EA := hL.E_eq
  subst EB
  exact memberLocal_of_indexed hexc hn hA hB hdA hdB hL _

/-- Actual bar-stage ORIGINAL member restrictions on EVERY prescribed
open after the actual common test prefix, without same-carrier input. -/
theorem member_stage_local_of_local {n kA kB : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (A B : MarkedIdeal n X) (hA : ResolutionInvariantSpec.IsInvDomain kA A)
    (hB : ResolutionInvariantSpec.IsInvDomain kB B) (hL : LocWPEquiv A B)
    (T : BlowupTower X Y) (hT : IsGeoTestTower A T) (U : Opens Y) (z : Y) :
    let P := geoTransformAlong (StepOneValue.barMarked A) T
    let Q := geoTransformAlong (StepOneValue.barMarked B) T
    LocWPEquiv (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y)
      (memberRestrict P (membersThrough P.E (StepOneValue.origMembers A T) z)))
      (MarkedIdeal.pullback (M' := CMfd.of (n := n) U) (Subtype.val : U → Y)
      (memberRestrict Q (membersThrough Q.E (StepOneValue.origMembers B T) z))) := by
  have hTB := (hL.wEquiv.2 T).1.mp hT
  have hTP := ((HironakaG8HomStable.bar_local_any_boundary A hA).wEquiv.2 T).1.mp hT
  have hTQ := ((HironakaG8HomStable.bar_local_any_boundary B hB).wEquiv.2 T).1.mp hTB
  have hPD := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (HironakaCoherentTransformExtension.isInvDomain_barMarked A hA) T hTP
  have hQD := InvDomainTowerAlong.isInvDomain_geoTransformAlong
    (HironakaCoherentTransformExtension.isInvDomain_barMarked B hB) T hTQ
  have hBar := (HironakaG1CoeffBarLocal.bar_local_of_local A B hA hB hL).geoTransformAlong T hTP
  have hOrig := HironakaG8MemberLoci.origMembers_eq_of_E_eq hL.wEquiv.1 T
  have hCut := memberLocal_membersThrough (κ := Kinds.wp) rfl hn hPD.isWellFormed hQD.isWellFormed
    hPD.one_le_d hQD.one_le_d hBar (StepOneValue.origMembers A T) z
  rw [hOrig] at hCut
  simpa only [hOrig] using hCut.restrict U

end
end Hironaka.HironakaG1SeparateCarrierMemberCut
