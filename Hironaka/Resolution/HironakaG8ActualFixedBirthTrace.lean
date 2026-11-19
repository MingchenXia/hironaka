import Hironaka.Resolution.HironakaG8PositiveSuffixDomainOpen
import Hironaka.Resolution.HironakaG8ActualContactEndpointDomain
import Hironaka.Resolution.HironakaG8ActualContactBirthRebase
import Hironaka.Resolution.HironakaG11ActualBirthEndpointExponent
import Hironaka.Resolution.HironakaG8ExceptionalDivOpen
import Hironaka.Resolution.HironakaG8RetainedSourcesOpen
import Hironaka.Resolution.HironakaG8RestrictedTracePush

/-! # Positive one-sided trace transfer at the actual contact birth -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ActualFixedBirthTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold BlowupRestrictOpen
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HomogenizedGlueingTower HomogenizedIdealAlongTower TangentDirectionAlong NormalCrossings
  GermIdealOrder DivisorExponentAlong StepOneValue ResolutionInvariantSpec
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMRebase HironakaG11InvBMClass
  HironakaG8LocalHistory HironakaG8CaseTActualAmbient HironakaG8CaseTContactPair
  HironakaG8ActualContactEndpointDomain HironakaG8ActualContactBirthRebase
  HironakaG8PositiveSuffixDomainOpen HironakaG8ExceptionalDivOpen
  HironakaG8RetainedSourcesOpen HironakaG8RestrictedTracePush
  HironakaG11ActualContactEndpointExponent

/-- Positive coefficient exponent and one-sided exceptional divisibility
transfer every retained trace across the genuine common contact birth. -/
theorem actual_fixed_birth_positive_trace_transfer
    {n : ℕ} (hn : 0 < n) {X Y Z W : CMfd.{0} n} {A B : MarkedIdeal n X} {k k' : ℕ}
    (hA : IsInvDomain k A) (hB : IsInvDomain k' B) (h : LocWPEquiv A B)
    (hd : A.d = B.d) (hdim : SameCarrierDim A B)
    (U : Opens X) {f g : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (hg : IsTangentDirectionAlong B.N B.ideal B.d U g)
    (P : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (Q : BlowupTower Z W)
    (hT : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q))
    {S : List (Set W)} (hS : ∀ K ∈ S, IsClosedSubmanifold n K) {e : ℕ} {z : W}
    (hzU : P.proj (π (Q.proj z)) ∈ U)
    (hzA : z ∈ (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).N)
    (hzB : z ∈ (contactCoeffBM B g ((BlowupTower.step P C π hπ).append Q)).N)
    (hnzA : IsNonzeroAlongAt (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).N
      (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).ideal z)
    (hnzB : IsNonzeroAlongAt (contactCoeffBM B g ((BlowupTower.step P C π hπ).append Q)).N
      (contactCoeffBM B g ((BlowupTower.step P C π hπ).append Q)).ideal z)
    (hzD : z ∈ strictAlong Q (π ⁻¹' C))
    (hpos : 0 < divExpAlong n (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).N
      (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).ideal (strictAlong Q (π ⁻¹' C)) z)
    (hdiv : IsDivNearAlong n (strictAlong Q (contactCoeffBM A f (.step P C π hπ)).N)
      (exceptionalTermBM (n := n) S e) (strictAlong Q (π ⁻¹' C)) 1 z)
    (hsource : ∀ K ∈ S, ∃ H : Set Y, IsClosedSubmanifold n H ∧
      IsClosedSubmanifold n (geoStrictTransform π C H) ∧
      K = strictAlong Q (geoStrictTransform π C H) ∧
      ∀ᶠ x in 𝓝 (π (Q.proj z)), x ∈ C → x ∈ H) :
    ∀ᶠ w in 𝓝 z, w ∈ strictAlong Q (contactCoeffBM B g (.step P C π hπ)).N →
      w ∈ strictAlong Q (π ⁻¹' C) → ∀ K ∈ S, w ∈ K := by
  by_cases hSne : S = []
  · simp [hSne]
  let V := openPreimage P U
  let V₁ : Opens Z := ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V₁ → V := fun x => ⟨π x.val,x.2⟩
  let C' : Set V := (Subtype.val : V → Y) ⁻¹' C
  let LA := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
  let LB := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM B g P)
  let LA₁ := MarkedIdeal.pullback (Subtype.val : V₁ → Z) (contactCoeffBM A f (.step P C π hπ))
  let LB₁ := MarkedIdeal.pullback (Subtype.val : V₁ → Z) (contactCoeffBM B g (.step P C π hπ))
  let F := (A.E.map (strictAlong P)).map ((Subtype.val : V → Y) ⁻¹' ·)
  let T := restrict V₁ Q
  let W' := openPreimage Q V₁
  let z' : W' := ⟨z,hzU⟩
  let S' := S.map ((Subtype.val : W' → W) ⁻¹' ·)
  let One : BlowupTower Y Z := .step .refl C π hπ
  let Tail := One.append Q
  have hFull : P.append Tail = (BlowupTower.step P C π hπ).append Q := by
    simp [Tail, One, ← BlowupTower.append_assoc]
  have hTP : IsGeoTestTower (barMarked A) (P.append Tail) := hFull ▸ hT
  have hTA : IsGeoTestTower A ((BlowupTower.step P C π hπ).append Q) := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have hTB : IsGeoTestTower B ((BlowupTower.step P C π hπ).append Q) := (h.wEquiv.2 _).1.mp hTA
  have hTJB : IsGeoTestTower (barMarked B) ((BlowupTower.step P C π hπ).append Q) := ((StepOneBridge.barMarked_wEquiv B hB).2 _).1.mpr hTB
  have hPA : IsGeoTestTower A P := (isGeoTestTower_step_iff A P C π hπ).mp ((isGeoTestTower_append_iff A _ Q).mp hTA).1 |>.1
  have hPB : IsGeoTestTower B P := (h.wEquiv.2 P).1.mp hPA
  have hRbA := actual_contact_birth_rebase A hA U hf P C π hπ Q hT
  have hRbB := actual_contact_birth_rebase B hB U hg P C π hπ Q hTJB
  have hρ : IsBlowupAlong n C' ρ := isBlowupAlong_restrict hπ V V₁.isOpen
  have hpair := actual_contact_pair A B hA.isWellFormed hB.isWellFormed hA.one_le_d hB.one_le_d h hdim U hf hg P hPA
  have hEqE : LB.E = LA.E := List.append_cancel_left hpair.1.E_eq
  have hrel : LocWPEquiv (X := CMfd.of (n := n) V) {LA with E := F ++ LA.E} {LB with E := F ++ LA.E} := by
    have hp := hpair.1
    rw [hEqE] at hp
    exact hp
  have hprefix := actual_contact_prefix A hA.isWellFormed hA.one_le_d U hf P hPA
  have hsnc : IsSNCDivisor n (F ++ LA.E) := by
    have he : F ++ LA.E = (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong A P)).E := hprefix.E_eq.symm
    rw [he]
    exact (IsWellFormed.pullback_val (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA.isWellFormed P hPA) V).isSNCDivisor
  have hdLA : 1 ≤ LA.d := by
    change 1 ≤ (contactCoeffBM A f P).d
    rw [contactCoeffBM_d]
    exact HironakaG8ClassStepCut.one_le_coeffEmptyBM_d A
  have hdLB : LB.d = LA.d := by
    change (contactCoeffBM B g P).d = (contactCoeffBM A f P).d
    rw [contactCoeffBM_d,contactCoeffBM_d,coeffEmptyBM_d,coeffEmptyBM_d,hd]
  have hzAT : z ∈ (contactCoeffBM A f (P.append Tail)).N := hFull.symm ▸ hzA
  have hzBT : z ∈ (contactCoeffBM B g (P.append Tail)).N := hFull.symm ▸ hzB
  have hnzAT : IsNonzeroAlongAt (contactCoeffBM A f (P.append Tail)).N (contactCoeffBM A f (P.append Tail)).ideal z := hFull.symm ▸ hnzA
  have hnzBT : IsNonzeroAlongAt (contactCoeffBM B g (P.append Tail)).N (contactCoeffBM B g (P.append Tail)).ideal z := hFull.symm ▸ hnzB
  have hTailProj : Tail.proj z = π (Q.proj z) := by
    change (One.append Q).proj z = π (Q.proj z)
    rw [BlowupTower.proj_append]
    rfl
  have hzUT : P.proj (Tail.proj z) ∈ U := by rw [hTailProj]; exact hzU
  obtain ⟨G,hG,hdomA,hdomB,-⟩ := actual_endpoint_common_domain_open hA hB h hd hdim U hf hg P Tail hTP hzUT hzAT hzBT hnzAT hnzBT
  have hG' : ρ (T.proj z') ∈ G := by
    have heq : (restrict V Tail).proj (⟨z,hzUT⟩ : openPreimage Tail V) = ρ (T.proj z') := by
      apply Subtype.ext
      change ((restrict V Tail).proj _).val = π (((restrict V₁ Q).proj z').val)
      rw [proj_restrict, proj_restrict, hTailProj]
    exact heq ▸ hG
  have hSources := retained_sources_restrict hπ V Q hzU hsource
  have hS' : ∀ K ∈ S', IsClosed K := by
    intro K hK
    obtain ⟨K₀,hK₀,rfl⟩ := List.mem_map.mp hK
    exact (hS K₀ hK₀).1.preimage continuous_subtype_val
  have hdiv' := (isDivNearAlong_exceptionalTermBM_pullback_val_iff W' hS hSne
    (strictAlong Q (contactCoeffBM A f (.step P C π hπ)).N) (strictAlong Q (π ⁻¹' C)) e 1 z').mpr hdiv
  have hNRA := hRbA.2.2.1.N_eq
  have hNRB := hRbB.2.2.1.N_eq
  have hzA' : z' ∈ strictAlong T (LA.geoTransform C' ρ).N := by
    rw [hNRA]
    change z' ∈ strictAlong T ((Subtype.val : V₁ → Z) ⁻¹' (contactCoeffBM A f (.step P C π hπ)).N)
    rw [strictAlong_restrict V₁ Q]
    change z ∈ strictAlong Q (contactCoeffBM A f (.step P C π hπ)).N
    simpa only [contactCoeffBM_N, MemberInterLocusAlong.strictAlong_append] using hzA
  have hzD' : z' ∈ strictAlong T (ρ ⁻¹' C') := by
    change z' ∈ strictAlong T ((Subtype.val : V₁ → Z) ⁻¹' (π ⁻¹' C))
    rw [strictAlong_restrict V₁ Q]
    exact hzD
  have hdiv'' : IsDivNearAlong n (strictAlong T (LA.geoTransform C' ρ).N)
      (exceptionalTermBM (n := n) S' e) (strictAlong T (ρ ⁻¹' C')) 1 z' := by
    rw [hNRA]
    change IsDivNearAlong n (strictAlong T ((Subtype.val : V₁ → Z) ⁻¹' (contactCoeffBM A f (.step P C π hπ)).N)) _
      (strictAlong T ((Subtype.val : V₁ → Z) ⁻¹' (π ⁻¹' C))) 1 z'
    rw [strictAlong_restrict V₁ Q,strictAlong_restrict V₁ Q]
    exact hdiv'
  have hExpFull : divExpAlong n (geoTransformAlong (LA.geoTransform C' ρ) T).N
      (geoTransformAlong (LA.geoTransform C' ρ) T).ideal
      ((Subtype.val : W' → W) ⁻¹' (strictAlong Q (π ⁻¹' C))) z' =
    divExpAlong n (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).N
      (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).ideal (strictAlong Q (π ⁻¹' C)) z :=
    HironakaG11ActualBirthEndpointExponent.actual_birth_endpoint_exponent A hA U hf P C π hπ Q hT hzU _
  have hpos' : 0 < divExpAlong n (geoTransformAlong (LA.geoTransform C' ρ) T).N
      (geoTransformAlong (LA.geoTransform C' ρ) T).ideal (strictAlong T (ρ ⁻¹' C')) z' := by
    rw [show strictAlong T (ρ ⁻¹' C') = (Subtype.val : W' → W) ⁻¹' (strictAlong Q (π ⁻¹' C)) from strictAlong_restrict V₁ Q (π ⁻¹' C)]
    rw [hExpFull]
    exact hpos
  have ht : ∀ᶠ q in 𝓝 z', q ∈ strictAlong T (LB.geoTransform C' ρ).N →
      q ∈ strictAlong T (ρ ⁻¹' C') → ∀ K ∈ S', q ∈ K :=
    positive_suffix_all_traces_transfer_on_domain_open (X := CMfd.of (n := n) V)
      (Y := CMfd.of (n := n) V₁) (Z := CMfd.of (n := n) W')
      hn LA LB hRbA.1 hRbB.1 hdLA F hrel hsnc hdLB hpair.2
      (C := C') (π := ρ) hρ hRbA.2.1 hRbB.2.1 G hdomA hdomB T
      hRbA.2.2.2.2.2.2 hRbB.2.2.2.2.2.2 (S := S') hS' e (z := z')
      hzA' hzD' hdiv'' hG' hpos' hSources
  have ht' : ∀ᶠ q in 𝓝 z', q ∈ strictAlong T ((Subtype.val : V₁ → Z) ⁻¹' (contactCoeffBM B g (.step P C π hπ)).N) →
      q ∈ strictAlong T ((Subtype.val : V₁ → Z) ⁻¹' (π ⁻¹' C)) → ∀ K ∈ S', q ∈ K := by
    change ∀ᶠ q in 𝓝 z', q ∈ strictAlong T LB₁.N →
      q ∈ strictAlong T (ρ ⁻¹' C') → ∀ K ∈ S', q ∈ K
    rw [← hNRB]
    exact ht
  exact all_member_trace_of_restrict V₁ Q hzU (contactCoeffBM B g (.step P C π hπ)).N (π ⁻¹' C) S ht'

end
end Hironaka.HironakaG8ActualFixedBirthTrace
