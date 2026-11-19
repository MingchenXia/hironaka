import Hironaka.Resolution.HironakaActualPointLocalInitialValues

/-! Entire initial family values of raw records compared on an actual good
open. This is the value bridge for fresh INNER Step One records; it assumes
whole marked-record geometry, not a recursive numerical comparison. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualInitialFamilyRecordValues
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
open MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan GermIdealPullbackCalculus
open ResolutionInvariantSpec (IsInvDomain)
noncomputable section
variable {n : ℕ} {Z Z' : CMfd.{u} n}

theorem initial_family_values_from_record
 (hn : 0<n) (q : ℕ) (A : MarkedIdeal n Z) (B : MarkedIdeal n Z')
 (hhol : ∀ x g,A.ideal.mem x g → HolomorphicAt n g x)
 (hcl : ∀ x g,IsInSpanAt (n := n) (A.ideal.mem x) x g → A.ideal.mem x g)
 (hB : IsInvDomain q B) (U : Opens Z) (U' : Opens Z')
 (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U')
 (hrec : MarkedIdeal.pullback (Subtype.val : U → Z) A=
   MarkedIdeal.pullback η (MarkedIdeal.pullback (Subtype.val : U' → Z') B))
 (z : U) (hz : z.val∈A.cosupp) :
 (CanonicalCentres.invFamily hn q).inv A .refl z.val=
   (CanonicalCentres.invFamily hn q).inv B .refl (η z).val := by
 classical
 let AU : MarkedIdeal n (CMfd.of (n := n) U) := MarkedIdeal.pullback (Subtype.val : U → Z) A
 let BU : MarkedIdeal n (CMfd.of (n := n) U') := MarkedIdeal.pullback (Subtype.val : U' → Z') B
 have hBU : IsInvDomain q BU := InvDomainTowerAlong.isInvDomain_pullback_val U' hB
 have hAU : IsInvDomain q AU := by
   change IsInvDomain q (MarkedIdeal.pullback (Subtype.val : U → Z) A)
   rw [hrec]
   exact InvDomainTowerAlong.isInvDomain_pullback η hBU
 have hzAU : z∈AU.cosupp := by
   rw [cosupp_pullback_val A hhol U]
   exact hz
 have hzBU : η z∈BU.cosupp := by
   change z∈(MarkedIdeal.pullback (Subtype.val : U → Z) A).cosupp at hzAU
   rw [hrec,MarkedIdeal.cosupp_pullback η.contMDiff η.symm.contMDiff
     η.apply_symm_apply η.symm_apply_apply BU
     (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
       hBU.isWellFormed.isCoherent hg)] at hzAU
   exact hzAU
 have hzB : (η z).val∈B.cosupp := by
   change η z∈(MarkedIdeal.pullback (Subtype.val : U' → Z') B).cosupp at hzBU
   rw [cosupp_pullback_val B
     (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
       hB.isWellFormed.isCoherent hg) U'] at hzBU
   exact hzBU
 have hsrc := HironakaActualPointLocalInitialValues.initial_family_value_on_good_open
   hn q A hhol hcl U hAU z hz
 have hIso := (CanonicalCentres.invFamily hn q).isInvValue.towerIso
   (X := CMfd.of (n := n) U') (X' := CMfd.of (n := n) U)
   η BU hBU .refl .refl η (.refl) trivial z hzBU
 have hRes := (CanonicalCentres.invFamily hn q).isInvValue.restrictOpen B hB U' .refl trivial (η z) hzB
 have hRecValue := congrArg
   (fun Q : MarkedIdeal n (CMfd.of (n := n) U) => (CanonicalCentres.invFamily hn q).inv Q .refl z) hrec
 exact hsrc.trans (hRecValue.trans (hIso.trans hRes))

end
end Hironaka.HironakaActualInitialFamilyRecordValues
