import TranscendentalNakamaye.Pending.HironakaDisjointFunctionalControlledSuccessor
import TranscendentalNakamaye.Pending.MarkedIdealTowerTransport

/-! Construct actual finite mark-one ambient controlled histories from a
prescribed intrinsic test tower. The upper tower is an output of induction;
no incoming geometry lift or successor dictionary is assumed. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace TranscendentalNakamaye.Pending.HironakaDisjointFiniteControlledHistory
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  BlowupStrictSubmanifold SubmanifoldChartedSpace IdealWeightPowers
  GermIdealPullbackCalculus GermIdealOrder InvertibleIdealQuotient
  BlowupControlledTransform
  HironakaDisjointFunctionalControlledSuccessor

/-- The actual original contact, strictly transformed at every physical step. -/
def contactAlong {n : ℕ} {X : CMfd n} (N : Set X) :
    {Y : CMfd n} → BlowupTower X Y → Set Y
  | _, .refl => N
  | _, .step T C π _ => geoStrictTransform π C (contactAlong N T)

/-- Full-carrier mark-one data, retaining the given ideal and ordered boundary. -/
def fullMarked {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] (B : List (Set X)) (J : GermIdeal n X) :
    MarkedIdeal n X := ⟨univ,B,J,1⟩

/-- Exact endpoint assertions for an actually constructed ambient tower. -/
def Endpoint {d t : ℕ} {X : CMfd (d+t)} (N : Set X)
    (B : List (Set X)) (J : GermIdeal (d+t) X)
    {P Q : CMfd d} (ι : P → X) (M : MarkedIdeal d P)
    (T : BlowupTower P Q) {Y : CMfd (d+t)} (U : BlowupTower X Y) (η : Q → Y) : Prop :=
  let S := contactAlong N U
  let A := geoTransformAlong (fullMarked B J) U
  ∃ (_hc : IsClosed S) (hr : ∀ y∈S,RegularAtDim (n := d+t) S y d),
    A.ideal.IsCoherent ∧ (vanishingIdeal (n := d+t) S).Le A.ideal ∧
    IsSNCDivisor (d+t) A.E ∧ IsTransverse (d+t) S A.E ∧
    (letI := chartedSpace (Nat.le_add_right d t) hr
     letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
     ∃ F : Q ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ S,
       (fun z : Q => (F z).val)=η ∧ U.proj ∘ η=ι ∘ T.proj ∧
       GermIdeal.pullback (m := d) η A.ideal=
         (geoTransformAlong M T).ideal ∧
       A.E.map (fun H => η ⁻¹' H)=(geoTransformAlong M T).E)

/-- An output history retaining the SAME embeddings at successive physical
prefixes, every original centre image, and each whole ideal/boundary dictionary. -/
inductive CoupledHistory {d t : ℕ} {X : CMfd (d+t)} {P : CMfd d}
    (N : Set X) (B : List (Set X)) (J : GermIdeal (d+t) X)
    (ι : P → X) (M : MarkedIdeal d P) :
    {Q : CMfd d} → {Y : CMfd (d+t)} → BlowupTower P Q → BlowupTower X Y → (Q → Y) → Prop
  | refl (h : Endpoint N B J ι M .refl .refl ι) : CoupledHistory N B J ι M .refl .refl ι
  | step {Q R : CMfd d} {Y Z : CMfd (d+t)} {T : BlowupTower P Q} {U : BlowupTower X Y}
      {η : Q → Y} {η' : R → Z} {C : Set Q} {C' : Set Y} {ρ : R → Q} {π : Z → Y}
      {hρ : IsBlowupAlong d C ρ} {hπ : IsBlowupAlong (d+t) C' π}
      (previous : CoupledHistory N B J ι M T U η)
      (centre : C'=η '' C) (square : π∘η'=η∘ρ)
      (endpoint : Endpoint N B J ι M (.step T C ρ hρ) (.step U C' π hπ) η') :
      CoupledHistory N B J ι M (.step T C ρ hρ) (.step U C' π hπ) η'

/-- Every actual native mark-one test tower has an internally constructed
ambient test tower with the same physical length and whole endpoint data. -/
theorem exists_actual_finite_controlled_history {d t : ℕ} {X : CMfd (d+t)}
    {N : Set X} (hNc : IsClosed N)
    (hS : ∀ x∈N,RegularAtDim (n := d+t) N x d) (ht : 0<t)
    {B : List (Set X)} (hB : IsSNCDivisor (d+t) B) (hT : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent)
    (hnormal : (vanishingIdeal (n := d+t) N).Le J) :
    letI := chartedSpace (Nat.le_add_right d t) hS
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
    let M := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
      (GermIdeal.pullback (m := d) (Subtype.val : N → X) J)
    ∀ {Q : CMfd d} (T : BlowupTower (CMfd.of N) Q), IsGeoTestTower M T →
      ∃ (Y : CMfd (d+t)) (U : BlowupTower X Y) (η : Q → Y),
        IsGeoTestTower (fullMarked B J) U ∧ U.length=T.length ∧
        CoupledHistory N B J (Subtype.val : N → X) M T U η ∧
        Endpoint N B J (Subtype.val : N → X) M T U η := by
  let := chartedSpace (Nat.le_add_right d t) hS
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hS
  let M := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
    (GermIdeal.pullback (m := d) (Subtype.val : N → X) J)
  dsimp only
  intro Q T htest
  induction T with
  | refl =>
      have hinit : Endpoint N B J (Subtype.val : N → X) M
          (.refl : BlowupTower (CMfd.of N) (CMfd.of N)) (.refl : BlowupTower X X)
          (Subtype.val : N → X) := by
        refine ⟨hNc,hS,hJ,hnormal,hB,hT,Diffeomorph.refl 𝓘(ℂ,ComplexModel d) N ∞,rfl,rfl,rfl,rfl⟩
      exact ⟨X,.refl,Subtype.val,True.intro,rfl,.refl hinit,hinit⟩
  | @step Q R T C ρ hρ ih =>
      obtain ⟨Y,U,η,hU,hlen,hprevious,hc,hr,hK,hNorm,hE,hTr,F,hFη,hsquare,hideal,hboundary⟩ := ih htest.1
      subst η
      let S := contactAlong N U
      let A := geoTransformAlong (fullMarked B J) U
      let L := geoTransformAlong M T
      have hLN : L.N=univ := (pullback_eq_mul_geoTransformAlong M rfl
        (isCoherent_pullback (contMDiff_val (Nat.le_add_right d t) hS) hJ) T htest.1).1
      have hLI : L.ideal.IsCoherent := (pullback_eq_mul_geoTransformAlong M rfl
        (isCoherent_pullback (contMDiff_val (Nat.le_add_right d t) hS) hJ) T htest.1).2.1
      have hLd : L.d=1 := d_geoTransformAlong M T
      let := chartedSpace (Nat.le_add_right d t) hr
      let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
      let D : Set S := F.symm ⁻¹' C
      have hρ' : IsBlowupAlong d D (F ∘ ρ) :=
        MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse F.symm.contMDiff F.contMDiff
          F.symm_apply_apply F.apply_symm_apply hρ
      have hrebased : (MarkedIdealBiholomorphism.MarkedIdeal.pullback F.symm L).IsAdmissibleCentre D :=
        (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff hLI).mpr htest.2
      have hnativeI : GermIdeal.pullback (m := d) (Subtype.val : S → Y) A.ideal=
          GermIdeal.pullback (m := d) F.symm L.ideal := by
        calc
          _=GermIdeal.pullback (m := d) ((fun z : Q => (F z).val) ∘ F.symm) A.ideal := by
            congr 1
            funext p
            exact (congrArg Subtype.val (F.apply_symm_apply p)).symm
          _=GermIdeal.pullback (m := d) F.symm
              (GermIdeal.pullback (m := d) (fun z : Q => (F z).val) A.ideal) :=
            HironakaSmoothSubmersionOrderedChoiceImageTrace.coherent_pullback_comp
              ((contMDiff_val (Nat.le_add_right d t) hr).comp F.contMDiff) F.symm.contMDiff A.ideal hK
          _=_ := by rw [hideal]
      have hnativeE : A.E.map (fun H => (Subtype.val : S → Y) ⁻¹' H)=
          L.E.map (F.symm ⁻¹' ·) := by
        rw [← hboundary,List.map_map]
        apply List.map_congr_left
        intro H _hH
        ext p
        simp only [Function.comp_apply,mem_preimage,F.apply_symm_apply]
      have hDNC : HasNormalCrossings d D (A.E.map fun H => (Subtype.val : S → Y) ⁻¹' H) := by
        rw [hnativeE]
        exact hrebased.2.2
      have hadmlower : (GermIdeal.pullback (m := d) (Subtype.val : S → Y) A.ideal).Le
          (idealPow (vanishingIdeal (n := d) D) 1) := by
        rw [hnativeI]
        have hNreb : (MarkedIdealBiholomorphism.MarkedIdeal.pullback F.symm L).N=univ := by
          change F.symm ⁻¹' L.N=univ
          rw [hLN,preimage_univ]
        have hh := HadamardBridge.ideal_le_idealPow_of_isAdmissibleCentre hNreb
          (isCoherent_pullback F.symm.contMDiff hLI) hrebased
        simpa only [MarkedIdealBiholomorphism.MarkedIdeal.pullback,hLd] using hh
      obtain ⟨Z,τ,cs,hZ,π,hπ,_hupper,hc',hr',hK',hNorm',hE',hTr',G,hcomm,hwhole,_hold,_hborn,hlist⟩ :=
        exists_functional_controlled_successor hc hr ht hE hTr A.ideal hK hNorm D (F∘ρ) hρ'
          hDNC hadmlower
      let Z' : CMfd (d+t) := CMfd.of Z
      let U' : BlowupTower X Z' := .step U ((Subtype.val : S → Y) '' D) π hπ
      have hCosub := HironakaDisjointConstructedControlledLift.image_subset_cosupport_of_native_admissibility
        (Nat.le_add_right d t) hr A.ideal hK D hadmlower
      have hcentNC := HironakaDisjointEmbeddedBoundaryLift.hasNormalCrossings_native_image
        hr (by omega) hE hTr D hDNC
      have hAdata := pullback_eq_mul_geoTransformAlong (fullMarked B J) rfl hJ U hU
      have hAN : A.N=univ := hAdata.1
      have hAd : A.d=1 := d_geoTransformAlong (fullMarked B J) U
      have hadmupper : A.IsAdmissibleCentre ((Subtype.val : S → Y) '' D) := by
        refine ⟨hπ.1,?_,hcentNC⟩
        change _ ⊆ cosupport (d+t) A.N A.ideal A.d
        rw [hAN,hAd]
        exact hCosub
      have htransupper : (geoTransformAlong (fullMarked B J) U').ideal=controlledTransform hπ A.ideal 1 := by
        change (A.geoTransform _ π).ideal=_
        rw [geoTransform_ideal_eq_controlledTransform hAdata.1 hK hπ]
        change controlledTransform hπ A.ideal A.d=controlledTransform hπ A.ideal 1
        rw [hAd]
      have hrebase := MarkedIdealBiholomorphism.MarkedIdeal.geoTransform_pullback
        F.symm.contMDiff F.contMDiff F.symm_apply_apply F.apply_symm_apply L hLI C hρ.contMDiff
      have hnext : Endpoint N B J (Subtype.val : N → X) M (.step T C ρ hρ) U'
          (fun z : R => (G z).val) := by
        refine ⟨hc',hr',?_,?_,hE',hTr',G,rfl,?_,?_,?_⟩
        · rwa [htransupper]
        · rwa [htransupper]
        · funext z
          have hp := congrFun hcomm z
          have hs := congrFun hsquare (ρ z)
          change U.proj (π (G z).val)=_
          have hpval := congrArg Subtype.val hp
          change π (G z).val=(F (ρ z)).val at hpval
          rw [hpval]
          exact hs
        · rw [htransupper]
          refine hwhole.trans ?_
          change controlledTransform hρ' (GermIdeal.pullback (m := d) (Subtype.val : S → Y) A.ideal) 1=
            (L.geoTransform C ρ).ideal
          have htgt := congrArg MarkedIdeal.ideal hrebase
          rw [geoTransform_ideal_eq_controlledTransform (by simp only
            [MarkedIdealBiholomorphism.MarkedIdeal.pullback,hLN,preimage_univ])
            (isCoherent_pullback F.symm.contMDiff hLI) hρ'] at htgt
          simpa only [MarkedIdealBiholomorphism.MarkedIdeal.pullback,hLd,← hnativeI] using htgt
        · change _=(L.geoTransform C ρ).E
          have heq := congrArg MarkedIdeal.E hrebase
          rw [geoTransform_E] at heq
          have heq' : (A.E.map fun H => (Subtype.val : S → Y) ⁻¹' H).map
              (geoStrictTransform (F∘ρ) D) ++[(F∘ρ) ⁻¹' D]=(L.geoTransform C ρ).E := by
            simpa only [MarkedIdealBiholomorphism.MarkedIdeal.pullback,← hnativeE] using heq
          exact hlist.trans heq'
      refine ⟨Z',U',(fun z : R => (G z).val),⟨hU,hadmupper⟩,
        by simpa only [U',BlowupTower.length] using congrArg (·+1) hlen,?_,hnext⟩
      apply CoupledHistory.step hprevious _ _ hnext
      · ext y
        constructor
        · rintro ⟨p,hp,rfl⟩
          exact ⟨F.symm p,hp,congrArg Subtype.val (F.apply_symm_apply p)⟩
        · rintro ⟨p,hp,rfl⟩
          exact ⟨F p,by simpa only [D,mem_preimage,F.symm_apply_apply] using hp,rfl⟩
      · funext z
        exact congrArg Subtype.val (congrFun hcomm z)

end
end TranscendentalNakamaye.Pending.HironakaDisjointFiniteControlledHistory
