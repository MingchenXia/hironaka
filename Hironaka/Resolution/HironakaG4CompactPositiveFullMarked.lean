import Hironaka.Resolution.HironakaG4CompactPositivePhase
import Hironaka.Resolution.HironakaG4CompactTraceExponentBound
import Hironaka.Resolution.HironakaMarkOneNoncompactNativePhase
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactPositiveFullMarked
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres StepOneLowerDomain NonmonomialOrderLocal
  NonmonomialOrderCanonical NonmonomialOrderGlobalPhase NonmonomialOrderMonomialCanonical
  HironakaG4CompactPositivePhase HironakaG4CompactTraceExponentBound
  HironakaMarkOneGammaBoundedMaxima HironakaMarkOneNoncompactNativePhase
  MonomialInvariant MonomialCaseAlong MonomialStepAlong MonomialPartAlong DivisorExponentAlong
  RestrictEmptyTower HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Compact positive support and a source incident-exponent bound resolve the
actual mark-one ideal globally, without compactness of the full cosupport. -/
theorem exists_mark_one_phased_resolution_of_compact_positive_support (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (d+1) M) (hd : M.d=1)
    (hK : IsCompact (positiveSupport M)) (B : ℕ)
    (hExp : ∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B) :
    ∃ (Y : CMfd.{u} n) (P : BlowupTower X Y)
      (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      IsCanonical M ((invFamily hn (d+1)).inv M) P ∧ IsGeoTestTower M P ∧
      CentresOver (positiveSupport M) P ∧
      IsMonomialAlong n (geoTransformAlong M P).N (geoTransformAlong M P).ideal
        (geoTransformAlong M P).E ∧
      IsCanonicalSegment (geoTransformAlong M P)
        (fun {Q} R => towerInvAlong (geoTransformAlong M P) (Y := Q) R) S ∧
      IsGeoResolution M (P.append S) ∧ CentresOver M.cosupp (P.append S) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (P.append S).proj ∧
      IsProperMap (P.append S).proj ∧ IsIsomorphismOver n (P.append S).proj M.cosuppᶜ := by
  obtain ⟨Y,P,hCan,hTest,hOver,hMono⟩ :=
    exists_canonical_mark_one_compact_positive_monomial_exit hn d M hM hd hK
  let N := geoTransformAlong M P
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM P hTest
  have hdN : N.d=1 := by simpa only [N,d_geoTransformAlong] using hd
  obtain ⟨v₀,hv₀,hγ₀⟩ := markOne_gamma_bound_without_monomial M hM.isWellFormed hd B hExp
  have hKP : IsCompact (P.proj ⁻¹' positiveSupport M) :=
    (HironakaLocalPrincipalization.isProperMap_proj P).isCompact_preimage hK
  obtain ⟨C,hC⟩ := incident_exponents_bounded_on_compact hn N hDom.isWellFormed
    hDom.isNonzeroAlongAt (P.proj ⁻¹' positiveSupport M) hKP
  obtain ⟨v₁,hv₁,hγ₁⟩ := markOne_gamma_bound_on_of_incident_exponents N hDom.isWellFormed hdN
    (P.proj ⁻¹' positiveSupport M) C (fun x hx hxCos i hi => hC x hx (N.cosupp_subset_N hxCos) i hi)
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {D : CMfd.{u} n}
    (S : BlowupTower A D) (z : D) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn d) J S z
  have hf : OrdMonotone M ((invFamily hn (d+1)).inv M) := GeneralValue.ordMonotone_genInv lower M
  have hv : OrdZeroValue M ((invFamily hn (d+1)).inv M)
      (fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot Val ⊕ₗ WithTop (Lex (ℕ × WithTop (ValTy d)))))) := by
    intro Z Q hQ z hz hz0
    exact GeneralCanonicalTail.ordZeroValue_genInv (Y := Z) lower M Q hQ z hz hz0
  let v := max v₀ v₁
  have hvFirst : (ofLex v).1=n-1 := by
    rcases le_total v₀ v₁ with h | h
    · rw [show v=v₁ from max_eq_right h]; exact hv₁
    · rw [show v=v₀ from max_eq_left h]; exact hv₀
  have hBound : ∀ y ∈ N.cosupp,gammaAlong n N.N N.ideal N.E N.d y ≤ (v : WithBot Val) := by
    intro y hy
    by_cases hyK : P.proj y ∈ positiveSupport M
    · exact (hγ₁ y hyK hy).trans (WithBot.coe_le_coe.mpr (le_max_right v₀ v₁))
    · have hySrc : P.proj y ∈ M.cosupp :=
        proj_mem_cosupp_of_mem_cosupp hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent P hTest hy
      have hNot : P.proj y ∉ ordGe M 1 := fun ho => hyK ⟨hySrc,ho⟩
      have hZero : nmOrd M (P.proj y)=0 := Nat.eq_zero_of_le_zero (nmOrd_le_of_notMem hNot)
      have hTail := towerInvAlong_le_of_canonical hn hM hf strictMono_toLex_zero_inl hv
        (.refl : BlowupTower X X) P (by simpa only [BlowupTower.refl_append] using hTest)
        (by simpa only [BlowupTower.refl_append] using hCan) y
        (by simpa only [BlowupTower.refl_append] using hy) hZero
      have hGamma : gammaAlong n N.N N.ideal N.E N.d y ≤
          gammaAlong n M.N M.ideal M.E M.d (P.proj y) := by
        simpa [N,towerInvAlong] using hTail.2.2
      exact (hGamma.trans (hγ₀ _ hySrc)).trans (WithBot.coe_le_coe.mpr (le_max_left v₀ v₁))
  obtain ⟨Z,S,hSegment,hResS⟩ := exists_markOne_native_resolution_of_bound
    hn N hDom.isWellFormed hDom.isNonzeroAlongAt hMono hdN v hvFirst hBound
  have hRes : IsGeoResolution M (P.append S) := by
    refine ⟨(isGeoTestTower_append_iff M P S).mpr ⟨hTest,hResS.1⟩,?_⟩
    rw [geoTransformAlong_append]
    exact hResS.2
  have hAllOver := HironakaAdmissibleSequence.centresOver_cosupp M
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent (P.append S) hRes.1
  exact ⟨Y,P,Z,S,hCan,hTest,hOver,hMono,hSegment,hRes,hAllOver,(P.append S).contMDiff_proj,
    HironakaLocalPrincipalization.isProperMap_proj _,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ _ hAllOver⟩

/-- Compact positive support and a source incident-exponent bound resolve the
actual mark-one ideal globally, without compactness of the full cosupport. -/
theorem exists_mark_one_resolution_of_compact_positive_support (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (d+1) M) (hd : M.d=1)
    (hK : IsCompact (positiveSupport M)) (B : ℕ)
    (hExp : ∀ x ∈ M.cosupp,∀ i : Fin M.E.length,x ∈ M.E.get i →
      divExpAlong n M.N M.ideal (M.E.get i) x ≤ B) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution M T ∧ CentresOver M.cosupp T ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj M.cosuppᶜ := by
  obtain ⟨Y,P,Z,S,_hCan,_hTest,_hOver,_hMono,_hSegment,hRes,hAllOver,hHol,hProper,hIso⟩ :=
    exists_mark_one_phased_resolution_of_compact_positive_support hn d M hM hd hK B hExp
  exact ⟨Z,P.append S,hRes,hAllOver,hHol,hProper,hIso⟩

end
end Hironaka.HironakaG4CompactPositiveFullMarked
