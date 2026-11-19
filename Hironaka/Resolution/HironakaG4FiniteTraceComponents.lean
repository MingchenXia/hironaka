import Hironaka.Resolution.HironakaMarkOneGammaBoundedMaxima
import Hironaka.Resolution.HironakaG4ZeroMaskSameGammaHistory

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4FiniteTraceComponents
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal DivisorExponentAlong MonomialPartAlong
  MonomialInvariant MonomialCaseAlong HironakaMarkOneGammaBoundedMaxima
  BlowupTowerTransforms HomogenizedGlueingTower BlowupStrictSubmanifold NormalCrossings
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4ZeroMaskSameGammaHistory
  RestrictedIdealExtension GermIdealOrder ResolutionDriver
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteChronologicalHistory
variable {n : ℕ} {X : CMfd.{u} n}

private theorem finite_range_of_finite_connected_components {α β : Type*} [TopologicalSpace α]
    [Finite (ConnectedComponents α)] {f : α → β} (hf : IsLocallyConstant f) : (Set.range f).Finite := by
  let r : ConnectedComponents α → α := fun c => Classical.choose (ConnectedComponents.surjective_coe c)
  have hr (c : ConnectedComponents α) : ConnectedComponents.mk (r c) = c := Classical.choose_spec (ConnectedComponents.surjective_coe c)
  apply (Set.finite_range (fun c => f (r c))).subset
  rintro _ ⟨x,rfl⟩
  refine ⟨ConnectedComponents.mk x,?_⟩
  have hmem : r (ConnectedComponents.mk x) ∈ connectedComponent x := by
    apply ConnectedComponents.coe_eq_coe'.mp
    exact hr (ConnectedComponents.mk x)
  exact hf.apply_eq_of_isPreconnected isPreconnected_connectedComponent hmem mem_connectedComponent

/-- Finite connected-component counts of each carrier/boundary trace give
one actual numerical bound on all source incident exponents. -/
theorem incident_exponents_bounded_of_finite_trace_components (hn : 0 < n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hComp : ∀ i : Fin M.E.length, Finite (ConnectedComponents {x : X | x ∈ M.N ∧ x ∈ M.E.get i})) :
    ∃ B : ℕ,∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B := by
  have hFinite (i : Fin M.E.length) :
      (Set.range (fun x : {x : X | x ∈ M.N ∧ x ∈ M.E.get i} =>
        divExpAlong n M.N M.ideal (M.E.get i) x.1)).Finite := by
    let : Finite (ConnectedComponents {x : X | x ∈ M.N ∧ x ∈ M.E.get i}) := hComp i
    apply finite_range_of_finite_connected_components
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro x
    have h := eventually_divExpAlong_get_eq hn hM.isClosedSubmanifold_N hM.isSNCDivisor
      hM.isTransverse hM.isCoherent hne i x.2.1 x.2.2
    filter_upwards [h.filter_mono (continuous_subtype_val.tendsto x)] with y hy
    exact hy y.2.1 y.2.2
  have hb (i : Fin M.E.length) := (hFinite i).bddAbove
  choose bound hBound using hb
  refine ⟨Finset.univ.sup bound,?_⟩
  intro x hx i hi
  exact le_trans (hBound i ⟨⟨x,M.cosupp_subset_N hx,hi⟩,rfl⟩)
    (Finset.le_sup (f := bound) (Finset.mem_univ i))

/-- Finite trace-component counts supply a shaped source Gamma bound. -/
theorem markOne_gamma_bound_of_finite_trace_components (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmono : IsMonomialAlong n M.N M.ideal M.E) (hd : M.d=1)
    (hComp : ∀ i : Fin M.E.length, Finite (ConnectedComponents {x : X | x ∈ M.N ∧ x ∈ M.E.get i})) :
    ∃ v : Val, (ofLex v).1=n-1 ∧
      ∀ x ∈ M.cosupp,gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot Val) := by
  obtain ⟨B,hB⟩ := incident_exponents_bounded_of_finite_trace_components hn M hM hne hComp
  exact markOne_gamma_bound_of_incident_exponents hn M hM hne hmono hd B hB

/-- Finite component counts give the bounded noncompact zero-mask history. -/
theorem exists_prepared_zero_mask_finite_trace_components_history (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let I := oldTraceIdeal N old
    let D := oldMonomialPart N old born
    let J := oldResidualPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
    let MI := fun i => (⟨N,born,I i,d i⟩ : MarkedIdeal n X)
    let MD := fun i => (⟨N,born,D i,d i⟩ : MarkedIdeal n X)
    let RJ := fun i => (⟨N,born,J i,0⟩ : MarkedIdeal n X)
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    (∀ i : Fin M.E.length, Finite (ConnectedComponents
      {x : X | x ∈ M.N ∧ x ∈ M.E.get i})) →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => MonomialStepAlong.towerInvAlong M (Y := Y) Q) T ∧
      IsGeoResolution M T ∧
      IsGeoTestTower (geometricTemplate N born) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
      CurrentSharpCentres N (old ++ born) T ∧
      (∀ i : Fin old.length,
        IsGeoTestTower (MI i) T ∧ IsGeoTestTower (MD i) T ∧ IsGeoTestTower (RJ i) T) ∧
      (∀ k : ℕ,
        let Q := BlowupTowerSplit.head T k
        let NQ := strictAlong Q N
        let oldQ := old.map (strictAlong Q)
        let bornQ := (geoTransformAlong (geometricTemplate N born) Q).E
        let eQ : Fin old.length ≃ Fin oldQ.length := finCongr (by simp [oldQ])
        let PQ := P.map eQ.toEmbedding
        let IQ := oldTraceIdeal NQ oldQ
        let DQ := oldMonomialPart NQ oldQ bornQ
        let JQ := oldResidualPart NQ oldQ bornQ
        let AQ : (BlowupTowerSplit.split T k).1 → Fin oldQ.length → Fin bornQ.length → ℕ :=
          fun z i j => divExpAlong n NQ (DQ i) (bornQ.get j) z
        let SigmaQ : GermIdeal n (BlowupTowerSplit.split T k).1 := ⟨fun z g =>
          IsInSpanAt (n := n) (fun f => ∃ i ∈ PQ,(DQ i).mem z f) z g⟩
        let MQ : MarkedIdeal n (BlowupTowerSplit.split T k).1 := ⟨NQ,bornQ,SigmaQ,1⟩
        geoTransformAlong M Q=MQ ∧
        IsClosedSubmanifold n NQ ∧ IsSNCDivisor n (oldQ ++ bornQ) ∧
        IsTransverse n NQ bornQ ∧
        NQ ⊆ closure (NQ \ ⋃ H ∈ oldQ ++ bornQ,H) ∧
        (∀ z ∈ NQ,∀ i,ordinaryTraceOrder NQ (JQ i) z ≤ 1) ∧
        (∀ z ∈ NQ,IsPreparedResidualSNCAt NQ oldQ bornQ z) ∧
        (∀ z ∈ NQ,tauD (AQ z) ≤ P.card) ∧
        (∀ z ∈ NQ,∀ i : Fin old.length,
          eQ i ∈ properRows (AQ z) → i ∈ properRows (A (Q.proj z))) ∧
        (∀ z ∈ NQ,tauD (AQ z)=P.card → nuOne (AQ z)=0) ∧
        MQ.IsWellFormed ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ SigmaQ z) ∧
        IsMonomialAlong n NQ SigmaQ bornQ ∧
        MQ.cosupp={z | z ∈ NQ ∧ PQ ⊆ properRows (AQ z)} ∧
        ∀ i : Fin old.length,
          (geoTransformAlong (MI i) Q).ideal=IQ (eQ i) ∧
          (geoTransformAlong (MD i) Q).ideal=DQ (eQ i) ∧
          (geoTransformAlong (RJ i) Q).ideal=JQ (eQ i) ∧
          IQ (eQ i)=RestrictedIdealExtension.restrictOn n NQ
            ((DQ (eQ i)).mul (JQ (eQ i))) ∧
          (IQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (IQ (eQ i)) z) ∧
          (DQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (DQ (eQ i)) z) ∧
          IsMonomialAlong n NQ (DQ (eQ i)) bornQ ∧
          (JQ (eQ i)).IsCoherent ∧ (∀ z ∈ NQ,IsNonzeroAlongAt NQ (JQ (eQ i)) z)) ∧
      let NT := strictAlong T N
      let BT := (geoTransformAlong (geometricTemplate N born) T).E
      let AT : Y → Fin old.length → Fin BT.length → ℕ := fun z i j =>
        divExpAlong n NT
          (monomialPartAlong n NT
            (restrictOn n NT (vanishingIdeal (n := n) (strictAlong T (old.get i)))) BT)
          (BT.get j) z
      ∀ z ∈ NT,¬P ⊆ properRows (AT z) := by
  classical
  dsimp only
  intro hTau hNu hComp
  obtain ⟨_hc,hNZ,_hMono,hWF,_hCos,_hRows,_hCentre,_hLocal⟩ :=
    HironakaG4ZeroResidualMonomialSum.actual_zero_residual_mask_sum_geometry
      hn hN hE hTr hdense P hP hTau hNu
  obtain ⟨B,hB⟩ := incident_exponents_bounded_of_finite_trace_components hn _ hWF hNZ hComp
  exact HironakaG4ZeroMaskSameGammaHistory.exists_prepared_zero_mask_exponent_bounded_history
    hn hN hE hTr hdense hOrd hPrepared P hP hTau hNu B hB

end
end Hironaka.HironakaG4FiniteTraceComponents
