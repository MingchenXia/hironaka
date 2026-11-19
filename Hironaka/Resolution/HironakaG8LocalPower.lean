import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Resolution.HironakaG8LogMixedHistory

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Powers and common marks for the local equivalence (G8 lane, run 0080, round 3; (B') port P0, local form)

Blueprint: `hironaka-g8-resume-local-power.tex`.

The (B') induction compares marked ideals of ONE common mark (`HironakaG11InvBMClass.ClassFunctorialFor` assumes
`A.d = B.d`); window records are normalized by `M ↦ M^e` (`HironakaActualPowerBoundaryExponents.powerMarked`).  The global
forms are `HironakaG8MixedEquiv.mixedEquiv_powerMarked`, `MixedEquiv.commonMark`, `HironakaG8ProjEquiv.projEquiv_powerMarked`.
This module proves the LOCAL forms, by the coinduction principle `HironakaG8LocalStable.LocEquiv.of_isLocStable` applied to
the relation "`Q` is restricted-equivalent to a power `P^e` of a marked ideal `P` in the native domain" (stable under one
admissible blowup: `original_power_transform`; one product with a line: `projection_power_normalization`; restriction to
an open subset: pullbacks of powers):

* `powerRel`, **`isLocStable_powerRel`**;
* **`locEquiv_powerMarked`**: `LocEquiv κ M (M^e)` for `M` in the native domain, `e ≥ 1`, `κ` without exceptional
  blowups (in particular `LocWPEquiv M (M^e)`);
* `locEquiv_pow`, **`locEquiv_commonMark`**: `LocEquiv κ M M'` (native domain) gives `LocEquiv κ (M^{d'}) (M'^{d})`, both
  of mark `d d'`.

Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalPower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism RelativePrincipalizationSpan
open Hironaka.ResolutionInvariantSpec (IsInvDomain)
open Hironaka.IdealWeightPowers (idealPow)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projection_test_isInvDomain)
open Hironaka.HironakaActualPowerBoundaryExponents (powerMarked powerMarked_isInvDomain
  powerMarked_cosupp)
open Hironaka.HironakaActualMixedPullbackNormalization (projection_power_normalization)
open Hironaka.HironakaActualOriginalPowerTransform (original_power_transform)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaG8LocalStable

noncomputable section

/-- **`Q` is restricted-equivalent to a power of a marked ideal `P` of the native domain.** -/
def powerRel {m : ℕ} {Y : CMfd.{u} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ k k' e : ℕ, 1 ≤ e ∧ IsInvDomain k P ∧ IsInvDomain k' Q ∧ RestrictEquiv Q (powerMarked P e)

/-- **The power relation is stable under the local test actions** (blowups, products with a line, open restrictions). -/
theorem isLocStable_powerRel (κ : Kinds) : IsLocStable.{u} κ (fun {m} {Y} P Q => powerRel (m := m) (Y := Y) P Q) where
  E_eq := by
    rintro m Y P Q ⟨k, k', e, he, hP, hQ, hr⟩
    exact hr.E_eq
  cosupp_eq := by
    rintro m Y P Q ⟨k, k', e, he, hP, hQ, hr⟩
    exact (powerMarked_cosupp P hP he).symm.trans hr.cosupp_eq.symm
  controlled := by
    rintro m Y P Q ⟨k, k', e, he, hP, hQ, hr⟩ C Z π hπ hC
    have hcos : P.cosupp = Q.cosupp := (powerMarked_cosupp P hP he).symm.trans hr.cosupp_eq.symm
    have hCQ : Q.IsAdmissibleCentre C := (isAdmissibleCentre_congr (show P.E = Q.E from hr.E_eq.symm) hcos C).mp hC
    have hT : IsGeoTestTower P (.step .refl C π hπ) := ⟨trivial, hC⟩
    have hTQ : IsGeoTestTower Q (.step .refl C π hπ) := ⟨trivial, hCQ⟩
    have hP' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hP (.step .refl C π hπ) hT
    have hQ' := InvDomainTowerAlong.isInvDomain_geoTransformAlong hQ (.step .refl C π hπ) hTQ
    have hpow := (original_power_transform P hP e he (.step .refl C π hπ) hT).2
    have heq : Q.geoTransform C π = (powerMarked P e).geoTransform C π :=
      hr.geoTransform_eq hQ.isWellFormed.isClosedSubmanifold_N.1 hQ.isWellFormed.isCoherent
        (powerMarked_isInvDomain P hP he).isWellFormed.isCoherent hπ.contMDiff
    refine ⟨k, k', e, he, hP', hQ', ?_⟩
    rw [heq]
    exact hpow
  projection := by
    rintro _ m Y P Q ⟨k, k', e, he, hP, hQ, hr⟩
    refine ⟨k + 1, k' + 1, e, he, projection_test_isInvDomain P hP, projection_test_isInvDomain Q hQ, ?_⟩
    obtain ⟨N', E', I', d'⟩ := Q
    obtain ⟨hN, hE, hd, hle, hge⟩ := hr
    change N' = P.N at hN
    change E' = P.E at hE
    change d' = P.d * e at hd
    subst hN hE hd
    exact projection_power_normalization P hP I' hQ.isWellFormed.isCoherent e hle hge
  restrict := by
    rintro m Y P Q ⟨k, k', e, he, hP, hQ, hr⟩ U
    refine ⟨k, k', e, he, InvDomainTowerAlong.isInvDomain_pullback_val U hP,
      InvDomainTowerAlong.isInvDomain_pullback_val U hQ, ?_⟩
    have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ (Subtype.val : U → Y) := contMDiff_subtype_val
    have hpow : GermIdeal.pullback (m := m) (Subtype.val : U → Y) (idealPow P.ideal e) =
        idealPow (GermIdeal.pullback (m := m) (Subtype.val : U → Y) P.ideal) e :=
      HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hval hP.isWellFormed.isCoherent e
    have hholP : ∀ x g, (idealPow P.ideal e).mem x g → HolomorphicAt m g x := fun x g hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem (GermIdealPullbackCalculus.isCoherent_idealPow hP.isWellFormed.isCoherent e) hg
    have hholQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt m g x := fun x g hg =>
      GermIdeal.IsCoherent.holomorphicAt_mem hQ.isWellFormed.isCoherent hg
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (Subtype.val : U → Y) ⁻¹' Q.N = (Subtype.val : U → Y) ⁻¹' P.N
      rw [hr.N_eq]
      rfl
    · show Q.E.map ((Subtype.val : U → Y) ⁻¹' ·) = P.E.map ((Subtype.val : U → Y) ⁻¹' ·)
      rw [hr.E_eq]
      rfl
    · show Q.d = P.d * e
      exact hr.d_eq
    · show RestrictLe ((Subtype.val : U → Y) ⁻¹' Q.N) (GermIdeal.pullback (m := m) (Subtype.val : U → Y) Q.ideal)
        (idealPow (GermIdeal.pullback (m := m) (Subtype.val : U → Y) P.ideal) e)
      rw [← hpow]
      exact HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hval (fun _ hp => hp) hholP hr.le
    · show RestrictLe ((Subtype.val : U → Y) ⁻¹' Q.N)
        (idealPow (GermIdeal.pullback (m := m) (Subtype.val : U → Y) P.ideal) e)
        (GermIdeal.pullback (m := m) (Subtype.val : U → Y) Q.ideal)
      rw [← hpow]
      exact HironakaG8LogMixedHistory.restrictLe_pullback_of_restrictLe hval (fun _ hp => hp) hholQ hr.ge

variable {n : ℕ} {X : CMfd.{u} n} {κ : Kinds}

/-- **`M` is locally equivalent to its powers** (native domain, `e ≥ 1`, kinds without exceptional blowups). -/
theorem locEquiv_powerMarked (hexc : κ.exc = false) {k : ℕ} (M : MarkedIdeal n X) (hM : IsInvDomain k M) {e : ℕ}
    (he : 1 ≤ e) : LocEquiv κ M (powerMarked M e) :=
  LocEquiv.of_isLocStable (isLocStable_powerRel κ) hexc
    ⟨k, k, e, he, hM, powerMarked_isInvDomain M hM he,
      RestrictEquiv.refl (powerMarked_isInvDomain M hM he).isWellFormed.isCoherent⟩

/-- **Powers of locally equivalent marked ideals are locally equivalent.** -/
theorem locEquiv_pow (hexc : κ.exc = false) {M M' : MarkedIdeal n X} {k k' : ℕ} (h : LocEquiv κ M M')
    (hM : IsInvDomain k M) (hM' : IsInvDomain k' M') {e e' : ℕ} (he : 1 ≤ e) (he' : 1 ≤ e') :
    LocEquiv κ (powerMarked M e) (powerMarked M' e') :=
  ((locEquiv_powerMarked hexc M hM he).symm.trans h).trans (locEquiv_powerMarked hexc M' hM' he')

/-- **Common-mark normalization for the local equivalence**: `M^{d'}` and `M'^{d}` are locally equivalent, both of mark
`d d'`. -/
theorem locEquiv_commonMark (hexc : κ.exc = false) {M M' : MarkedIdeal n X} {k k' : ℕ} (h : LocEquiv κ M M')
    (hM : IsInvDomain k M) (hM' : IsInvDomain k' M') :
    LocEquiv κ (powerMarked M M'.d) (powerMarked M' M.d) ∧ (powerMarked M M'.d).d = (powerMarked M' M.d).d := by
  refine ⟨locEquiv_pow hexc h hM hM' hM'.one_le_d hM.one_le_d, ?_⟩
  show M.d * M'.d = M'.d * M.d
  exact Nat.mul_comm _ _

end

end Hironaka.HironakaG8LocalPower
