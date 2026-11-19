import Hironaka.Resolution.HironakaG8BornExponents
import Hironaka.Resolution.HironakaStepOneZeroContactRemainderGlueing

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boundary exponents along towers with the native-domain condition only where it holds (G8 lane, run 0080, round 6)

Blueprint: `hironaka-g8-resume-domain-exponents.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c (module 6,
item (iv)), lane G11B's inbox item I-1348 (b): port P6 with "domain hypotheses only where they are used".

`HironakaG8BornExponents` (P6 core) propagates the agreement of the boundary exponents along common test towers for
`s(i,ii)`-equivalent marked ideals in the native domain.  For Bierstone--Milman's lower ideals the base objects are not in the
native domain: the coefficient ideal restricted to a hypersurface of maximal contact vanishes identically on the components
of the hypersurface contained in the codimension-one part of the cosupport.  The natural statement is POINTWISE: the
exponents agree at every cosupport point of a stage at which both transforms are nonzero along their carriers.  Two facts make
the induction along the tower work:

* **descent** (`isNonzeroAlongAt_of_geoTransform`): if the transform along an admissible blowup is nonzero along its carrier at
  `z`, the marked ideal is nonzero along its carrier at `π z` (off the centre the germs of the transform are pullbacks;
  over it, points off the exceptional divisor accumulate at `z`);
* **the domain is open** (`domOpen`): the points of the carrier at which the ideal is nonzero along it form the complement of
  the union of the components of the carrier contained in the cosupport (`HironakaStepOneZeroContactRemainderGlueing`), a
  closed set; on that open set the marked ideal is in the native domain (`isInvDomain_pullback_val_of_le_domOpen`).

At a step, restrict both stages to the intersection of their domain opens (it contains `π z` by descent), apply the P6 core
to the one-step tower there and come back by locality of the exponents (`expAgreeAt_pullback_val_iff`):

* `ExpAgreeAt P Q y` (pointwise `ExpAgree`), `expAgree_iff_forall_expAgreeAt`, `expAgreeAt_pullback_val_iff`;
* `divExpAlong_eq_of_restrictEquiv`, `isNonzeroAlongAt_iff_of_restrictEquiv`, `expAgreeAt_of_restrictEquiv`: restricted equivalence
  does not change exponents or the nonzero-along condition;
* **`expAgreeAt_geoTransform_of_domain`** (one step), **`expAgreeAt_geoTransformAlong_of_domain`** (along every common
  test tower; any initial agreement at domain points, e.g. `E = []`).

Sorry-free.  Universe `0` (as the P6 core).  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8DomainExponents

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen
  Hironaka.DivisorExponentAlong Hironaka.GermIdealOrder
  Hironaka.RelativePrincipalizationSpan Hironaka.InvertibleIdealQuotient
  Hironaka.BlowupStrictSubmanifold Hironaka.HironakaG8LocalHistory
open Hironaka.HironakaStepOneSpecialAnalyticLoci (selectedComponents
  isClosedSubmanifold_selectedComponents)
open Hironaka.HironakaStepOneZeroContactRemainderGlueing (selectedComponents_iff_not_isNonzeroAlongAt
  isNonzeroAlongAt_pullback_val_iff)
open Hironaka.MarkedIdealOperationsAlong.MarkedIdeal (RestrictEquiv)
open Hironaka.RestrictedIdealWeight (RestrictLe)
open Hironaka.ResolutionInvariantSpec (IsInvDomain DimLE)
open Hironaka.HironakaG8MixedBoundaryExponents (ExpAgree)
open Hironaka.HironakaG8MixedEquiv (isAdmissibleCentre_congr)
open Hironaka.HironakaG11InvBMClass (SameCarrierDim)

noncomputable section

variable {n : ℕ}

/-! ### Descent of the nonzero-along condition through one blowup -/

section Descent

variable {X Y : CMfd.{u} n} {C : Set X} {π : Y → X}

/-- **Off the centre, descent**: if `π z ∉ C` and the (coherent) transform is nonzero along its carrier at `z`, then `𝔪` is
nonzero along `N` at `π z` (there the germs of the transform are combinations of pullbacks of germs of `𝔪`). -/
theorem isNonzeroAlongAt_of_geoTransform_of_notMem (hπ : IsBlowupAlong n C π) (P : MarkedIdeal n X)
    (hN : IsClosed P.N) (hcoh : (P.geoTransform C π).ideal.IsCoherent) {z : Y} (hzC : π z ∉ C)
    (h : IsNonzeroAlongAt (P.geoTransform C π).N (P.geoTransform C π).ideal z) :
    IsNonzeroAlongAt P.N P.ideal (π z) := by
  obtain ⟨f, hf, hfreq⟩ := h
  have hfhol : HolomorphicAt n f z := GermIdeal.IsCoherent.holomorphicAt_mem hcoh hf
  have hspan : IsInSpanOnAt (n := n) (P.geoTransform C π).N ((P.geoTransform C π).ideal.mem z) z f :=
    IsInSpanAt.restrict (isInSpanAt_self hf hfhol)
  have hspan' := (MonomialBlowupAlongChart.isInSpanOnAt_geoTransform_iff_pullback_of_notMem hπ P hzC f).mp hspan
  obtain ⟨s, hs, hsfreq⟩ := NonmonomialStepAlong.isNonzeroAlongAt_of_isInSpanOnAt hspan' hfreq
  by_contra h0
  have hvan : ∀ g, P.ideal.mem (π z) g → ∀ᶠ x in 𝓝 (π z), x ∈ P.N → g x = 0 := by
    intro g hg
    have h' : ¬ ∃ᶠ x in 𝓝 (π z), x ∈ P.N ∧ g x ≠ 0 := fun hf' => h0 ⟨g, hg, hf'⟩
    rw [not_frequently] at h'
    filter_upwards [h'] with x hx hxN
    by_contra hne
    exact hx ⟨hxN, hne⟩
  obtain ⟨-, K, t, c, ht, -, hsum⟩ := GermIdeal.mem_pullback_iff.mp hs
  have htz : ∀ k, ∀ᶠ y in 𝓝 z, π y ∈ P.N → t k y = 0 := by
    intro k
    obtain ⟨g, hg, hgt⟩ := ht k
    have h1 := (hπ.contMDiff.continuous.tendsto z).eventually (hvan g hg)
    filter_upwards [h1] with y hy hyN
    rw [hgt]
    exact hy hyN
  have hsub : (P.geoTransform C π).N ⊆ π ⁻¹' P.N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN
  obtain ⟨y, ⟨hyN, hsy⟩, hy1, hy2⟩ := (hsfreq.and_eventually (hsum.and (eventually_all.mpr htz))).exists
  apply hsy
  have h1 : s y = ∑ k, c k y * t k y := hy1
  rw [h1]
  exact Finset.sum_eq_zero fun k _ => by rw [hy2 k (hsub hyN), mul_zero]

/-- **Descent of the nonzero-along condition through an admissible blowup**: if the transform is nonzero along its carrier at
`z`, then `𝔪` is nonzero along `N` at `π z` (`N` a closed submanifold, coherent ideal). -/
theorem isNonzeroAlongAt_of_geoTransform (hπ : IsBlowupAlong n C π) (P : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n P.N) (hI : P.ideal.IsCoherent) (hC : P.IsAdmissibleCentre C) {z : Y}
    (h : IsNonzeroAlongAt (P.geoTransform C π).N (P.geoTransform C π).ideal z) :
    IsNonzeroAlongAt P.N P.ideal (π z) := by
  have hcoh := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hN hI hC hπ
  by_contra h0
  have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt hI h0
  have hev' : ∀ᶠ x in 𝓝 (π z), ¬ IsNonzeroAlongAt P.N P.ideal x := by
    filter_upwards [hev] with x hx hnz
    obtain ⟨g, hg, hgf⟩ := hnz
    obtain ⟨w, ⟨hwN, hgw⟩, hw⟩ := (hgf.and_eventually (hx g hg)).exists
    exact hgw (hw hwN)
  have hevz : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 w, ¬ IsNonzeroAlongAt P.N P.ideal (π y) :=
    ((hπ.contMDiff.continuous.tendsto z).eventually hev').eventually_nhds
  obtain ⟨f, hf, hfreq⟩ := h
  have hmem : ∀ᶠ w in 𝓝 z, ∀ᶠ y in 𝓝 w, (P.geoTransform C π).ideal.mem y f :=
    (HomogenizedGlueing.eventually_mem hcoh hf).eventually_nhds
  obtain ⟨w, ⟨hwN, hfw⟩, hw0, hwm⟩ := (hfreq.and_eventually (hevz.and hmem)).exists
  have hfhol : HolomorphicAt n f w := GermIdeal.IsCoherent.holomorphicAt_mem hcoh hwm.self_of_nhds
  have hfne : ∀ᶠ y in 𝓝 w, f y ≠ 0 := hfhol.self_of_nhds.continuousAt.eventually_ne hfw
  have hdense : ∃ᶠ y in 𝓝 w, y ∈ π ⁻¹' (P.N \ C) := mem_closure_iff_frequently.mp hwN
  obtain ⟨y, hyD, hy0, hym, hyev⟩ := (hdense.and_eventually (hw0.and (hwm.and hfne.eventually_nhds))).exists
  have hyN : y ∈ (P.geoTransform C π).N := subset_closure hyD
  have hnzy : IsNonzeroAlongAt (P.geoTransform C π).N (P.geoTransform C π).ideal y :=
    ⟨f, hym, (mem_closure_iff_frequently.mp (subset_closure hyN)).and_eventually hyev⟩
  exact hy0 (isNonzeroAlongAt_of_geoTransform_of_notMem hπ P hN.1 hcoh hyD.2 hnzy)

end Descent

/-! ### The domain open -/

section Domain

variable {Y : CMfd.{u} n}

/-- **The domain open of a marked ideal**: the complement of the union of the components of the carrier contained in the
cosupport (`N` a closed submanifold). -/
def domOpen (P : MarkedIdeal n Y) (hN : IsClosedSubmanifold n P.N) : Opens Y :=
  ⟨(selectedComponents (n := n) P.N P.cosupp)ᶜ, (isClosedSubmanifold_selectedComponents hN P.cosupp).1.isOpen_compl⟩

/-- **A point of the carrier is in the domain open iff the ideal is nonzero along the carrier there.** -/
theorem mem_domOpen_iff {P : MarkedIdeal n Y} (hN : IsClosedSubmanifold n P.N) (hI : P.ideal.IsCoherent) (hd : 1 ≤ P.d)
    {x : Y} (hx : x ∈ P.N) : x ∈ domOpen P hN ↔ IsNonzeroAlongAt P.N P.ideal x := by
  show x ∉ selectedComponents (n := n) P.N P.cosupp ↔ _
  rw [selectedComponents_iff_not_isNonzeroAlongAt P hN hI hd hx, not_not]

/-- **On an open inside the domain open, the restriction is in the native domain** (well formed, `d ≥ 1`). -/
theorem isInvDomain_pullback_val_of_le_domOpen {P : MarkedIdeal n Y} (hwf : P.IsWellFormed) (hd : 1 ≤ P.d) {G : Opens Y}
    (hG : G ≤ domOpen P hwf.isClosedSubmanifold_N) :
    IsInvDomain n (MarkedIdeal.pullback (Subtype.val : G → Y) P) := by
  have hwfG := IsWellFormed.pullback_val hwf G
  refine ⟨hwfG, fun x hx => ?_, hd, fun p hp => ?_⟩
  · obtain ⟨j, hj⟩ := hwfG.isClosedSubmanifold_N.2 x hx
    exact ⟨j, le_of_regularAtDim_subset hj (AnalyticIrreducibleComponents.regularAtDim_univ x) (subset_univ _), hj⟩
  · have hp' : (p : Y) ∈ P.N := hp
    exact (isNonzeroAlongAt_pullback_val_iff hwf.isCoherent G p).mpr
      ((mem_domOpen_iff hwf.isClosedSubmanifold_N hwf.isCoherent hd hp').mp (hG p.2))

end Domain

/-! ### Exponents at a point -/

section At

variable {Y : CMfd.{u} n}

/-- **Agreement of the boundary exponents at one point.** -/
def ExpAgreeAt (P Q : MarkedIdeal n Y) (y : Y) : Prop :=
  ∀ H ∈ P.E, y ∈ P.cosupp → y ∈ H → divExpAlong n P.N P.ideal H y = divExpAlong n Q.N Q.ideal H y

/-- `ExpAgree` is `ExpAgreeAt` at every point. -/
theorem expAgree_iff_forall_expAgreeAt {P Q : MarkedIdeal n Y} :
    HironakaG11InvBMClass.ExpAgree P Q ↔ ∀ y, ExpAgreeAt P Q y :=
  ⟨fun h y H hH hy hyH => h H hH y hy hyH, fun h H hH y hy hyH => h y H hH hy hyH⟩

/-- **Exponents at a point are local**: they do not change under restriction to an open neighbourhood. -/
theorem expAgreeAt_pullback_val_iff {P Q : MarkedIdeal n Y} (hP : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x)
    (hQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt n g x) (U : Opens Y) (p : U) :
    ExpAgreeAt (Y := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → Y) P)
        (MarkedIdeal.pullback (Subtype.val : U → Y) Q) p ↔ ExpAgreeAt P Q p := by
  have hcosP : ∀ e, cosupport n ((Subtype.val : U → Y) ⁻¹' P.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → Y) P.ideal) e = (Subtype.val : U → Y) ⁻¹' cosupport n P.N P.ideal e :=
    fun e => cosupp_pullback_val (⟨P.N, [], P.ideal, e⟩ : MarkedIdeal n Y) hP U
  have hcosQ : ∀ e, cosupport n ((Subtype.val : U → Y) ⁻¹' Q.N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Q.ideal) e = (Subtype.val : U → Y) ⁻¹' cosupport n Q.N Q.ideal e :=
    fun e => cosupp_pullback_val (⟨Q.N, [], Q.ideal, e⟩ : MarkedIdeal n Y) hQ U
  have hmap : Filter.map (Subtype.val : U → Y) (𝓝 p) = 𝓝 (p : Y) :=
    map_nhds_subtype_coe_eq_nhds (p := fun x => x ∈ (U : Set Y)) p.2 (U.isOpen.mem_nhds p.2)
  have hcos : p ∈ (MarkedIdeal.pullback (Subtype.val : U → Y) P).cosupp ↔ (p : Y) ∈ P.cosupp := by
    rw [cosupp_pullback_val P hP U]
    rfl
  have hexp : ∀ H : Set Y, divExpAlong n ((Subtype.val : U → Y) ⁻¹' P.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) P.ideal) ((Subtype.val : U → Y) ⁻¹' H) p =
        divExpAlong n ((Subtype.val : U → Y) ⁻¹' Q.N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → Y) Q.ideal) ((Subtype.val : U → Y) ⁻¹' H) p ↔
      divExpAlong n P.N P.ideal H p = divExpAlong n Q.N Q.ideal H p := by
    intro H
    rw [MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosP hmap H,
      MonomialInvariantFunctorialAlong.divExpAlong_pullback hcosQ hmap H]
  constructor
  · intro h H hH hp hpH
    exact (hexp H).mp (h _ (List.mem_map_of_mem hH) (hcos.mpr hp) hpH)
  · intro h H' hH' hp hpH'
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
    exact (hexp H).mpr (h H hH (hcos.mp hp) hpH')

/-- **Restricted equivalence does not change the exponents.** -/
theorem divExpAlong_eq_of_restrictEquiv {P P' : MarkedIdeal n Y} (h : RestrictEquiv P P') (H : Set Y) (x : Y) :
    divExpAlong n P.N P.ideal H x = divExpAlong n P'.N P'.ideal H x := by
  rw [← h.N_eq]
  exact congrFun (congrFun (MonomialPartEtale.divExpAlong_congr fun e =>
    Subset.antisymm (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.ge e)
      (MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe h.le e)) H) x

/-- **Restricted equivalence does not change the nonzero-along condition.** -/
theorem isNonzeroAlongAt_iff_of_restrictEquiv {P P' : MarkedIdeal n Y} (h : RestrictEquiv P P') {x : Y} (hx : x ∈ P.N) :
    IsNonzeroAlongAt P.N P.ideal x ↔ IsNonzeroAlongAt P'.N P'.ideal x := by
  rw [← h.N_eq]
  constructor
  · rintro ⟨g, hg, hfreq⟩
    exact NonmonomialStepAlong.isNonzeroAlongAt_of_isInSpanOnAt (h.le x hx g hg) hfreq
  · rintro ⟨g, hg, hfreq⟩
    exact NonmonomialStepAlong.isNonzeroAlongAt_of_isInSpanOnAt (h.ge x hx g hg) hfreq

/-- **Pointwise exponent agreement is invariant under restricted equivalence on both sides.** -/
theorem expAgreeAt_of_restrictEquiv {P P' Q Q' : MarkedIdeal n Y} (hP : RestrictEquiv P P') (hQ : RestrictEquiv Q Q')
    {y : Y} (h : ExpAgreeAt P Q y) : ExpAgreeAt P' Q' y := by
  intro H hH hy hyH
  rw [← divExpAlong_eq_of_restrictEquiv hP H y, ← divExpAlong_eq_of_restrictEquiv hQ H y]
  exact h H (hP.E_eq ▸ hH) (hP.cosupp_eq ▸ hy) hyH

end At

/-! ### Exponents along towers, at the points of the domain -/

section Tower

variable {Y Z : CMfd.{0} n}

/-- **One step**: for `s(i,ii)`-equivalent well-formed marked ideals with the same mark `d ≥ 1` and carriers of the same
dimension whose exponents agree at the cosupport points where both are nonzero along their carriers, the exponents of the
transforms along a common admissible blowup agree at every cosupport point where both transforms are nonzero along their
carriers. -/
theorem expAgreeAt_geoTransform_of_domain {P Q : MarkedIdeal n Y} (hPQ : LocWPEquiv P Q) (hwfP : P.IsWellFormed)
    (hwfQ : Q.IsWellFormed) (hdP : 1 ≤ P.d) (hd : Q.d = P.d) (hdim : SameCarrierDim P Q)
    (hexp : ∀ x ∈ P.cosupp, IsNonzeroAlongAt P.N P.ideal x → IsNonzeroAlongAt Q.N Q.ideal x → ExpAgreeAt P Q x)
    {C : Set Y} (hC : P.IsAdmissibleCentre C) {π : Z → Y} (hπ : IsBlowupAlong n C π) {z : Z}
    (hz : z ∈ (P.geoTransform C π).cosupp)
    (hzP : IsNonzeroAlongAt (P.geoTransform C π).N (P.geoTransform C π).ideal z)
    (hzQ : IsNonzeroAlongAt (Q.geoTransform C π).N (Q.geoTransform C π).ideal z) :
    ExpAgreeAt (P.geoTransform C π) (Q.geoTransform C π) z := by
  have hNP := hwfP.isClosedSubmanifold_N
  have hNQ := hwfQ.isClosedSubmanifold_N
  have hIP := hwfP.isCoherent
  have hIQ := hwfQ.isCoherent
  have hholP : ∀ x g, P.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hIP hg
  have hholQ : ∀ x g, Q.ideal.mem x g → HolomorphicAt n g x := fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hIQ hg
  have hdQ : 1 ≤ Q.d := hd ▸ hdP
  have hcos : P.cosupp = Q.cosupp := hPQ.cosupp_eq_base
  have hCQ : Q.IsAdmissibleCentre C := (isAdmissibleCentre_congr hPQ.E_eq.symm hcos C).mp hC
  -- the one-step tower
  let T₁ : BlowupTower Y Z := .step .refl C π hπ
  have hT₁ : IsGeoTestTower P T₁ := ⟨trivial, hC⟩
  have hT₁Q : IsGeoTestTower Q T₁ := ⟨trivial, hCQ⟩
  -- descent to `x = π z`
  have hx : π z ∈ P.cosupp :=
    CompanionReductionAlong.mem_cosupp_of_mem_cosupp_geoTransform_along hNP.1 hholP hC hπ hz
  have hxP : IsNonzeroAlongAt P.N P.ideal (π z) :=
    isNonzeroAlongAt_of_geoTransform hπ P hNP hIP hC hzP
  have hxQ : IsNonzeroAlongAt Q.N Q.ideal (π z) :=
    isNonzeroAlongAt_of_geoTransform hπ Q hNQ hIQ hCQ hzQ
  -- the common domain open
  let G : Opens Y := domOpen P hNP ⊓ domOpen Q hNQ
  have hxG : π z ∈ G :=
    ⟨(mem_domOpen_iff hNP hIP hdP (P.cosupp_subset_N hx)).mpr hxP,
      (mem_domOpen_iff hNQ hIQ hdQ (Q.cosupp_subset_N (hcos ▸ hx))).mpr hxQ⟩
  have hdomP := isInvDomain_pullback_val_of_le_domOpen hwfP hdP (G := G) inf_le_left
  have hdomQ := isInvDomain_pullback_val_of_le_domOpen hwfQ hdQ (G := G) inf_le_right
  have hdimG := HironakaG8SpecialLoci.sameCarrierDim_pullback_val hholP hdim G
  have hexpG : ExpAgree (Y := CMfd.of (n := n) G) (MarkedIdeal.pullback (Subtype.val : G → Y) P)
      (MarkedIdeal.pullback (Subtype.val : G → Y) Q) := by
    refine (expAgree_iff_forall_expAgreeAt (Y := CMfd.of (n := n) G)).mpr fun p => ?_
    rw [expAgreeAt_pullback_val_iff hholP hholQ G p]
    intro H hH hp hpH
    have hpG : (p : Y) ∈ (G : Set Y) := p.2
    exact hexp p hp ((mem_domOpen_iff hNP hIP hdP (P.cosupp_subset_N hp)).mp hpG.1)
      ((mem_domOpen_iff hNQ hIQ hdQ (Q.cosupp_subset_N (hcos ▸ hp))).mp hpG.2) H hH hp hpH
  have key := HironakaG8BornExponents.locWPEquiv_expAgree_geoTransformAlong (hPQ.restrict G) hdomP hdomQ hdimG hd hexpG
    (restrict G T₁) (isGeoTestTower_restrict G hNP hIP T₁ hT₁)
  rw [geoTransformAlong_restrict G hNP hIP T₁ hT₁, geoTransformAlong_restrict G hNQ hIQ T₁ hT₁Q] at key
  have hzG : z ∈ openPreimage T₁ G := hxG
  have hP' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNP hIP hC hπ
  have hQ' := HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre hNQ hIQ hCQ hπ
  have h1 := (expAgree_iff_forall_expAgreeAt (Y := CMfd.of (n := n) (openPreimage T₁ G))).mp key ⟨z, hzG⟩
  exact (expAgreeAt_pullback_val_iff (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP' hg)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hQ' hg) (openPreimage T₁ G) ⟨z, hzG⟩).mp h1

/-- **Stage-local P6: boundary exponents along common test towers, at the points of the domain**: for `s(i,ii)`-equivalent
well-formed marked ideals `A`, `B` with the same mark `d ≥ 1` and carriers of the same dimension on the cosupport, whose
exponents agree at the cosupport points where both are nonzero along their carriers (e.g. `E = []`), along every common
test tower the exponents of `A_T` and `B_T` agree at every cosupport point where both are nonzero along their carriers.  No
native-domain hypothesis on `A`, `B` themselves. -/
theorem expAgreeAt_geoTransformAlong_of_domain {X : CMfd.{0} n} {A B : MarkedIdeal n X} (hAB : LocWPEquiv A B)
    (hwfA : A.IsWellFormed) (hwfB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hd : B.d = A.d) (hdim : SameCarrierDim A B)
    (hexp : ∀ x ∈ A.cosupp, IsNonzeroAlongAt A.N A.ideal x → IsNonzeroAlongAt B.N B.ideal x → ExpAgreeAt A B x) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower A T →
      ∀ y ∈ (geoTransformAlong A T).cosupp, IsNonzeroAlongAt (geoTransformAlong A T).N (geoTransformAlong A T).ideal y →
        IsNonzeroAlongAt (geoTransformAlong B T).N (geoTransformAlong B T).ideal y →
        ExpAgreeAt (geoTransformAlong A T) (geoTransformAlong B T) y
  | _, .refl, _ => hexp
  | _, .step T C π hπ, hT => by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff A T C π hπ).mp hT
    have ih := expAgreeAt_geoTransformAlong_of_domain hAB hwfA hwfB hdA hd hdim hexp T hTT
    have hTB : IsGeoTestTower B T := (hAB.wEquiv.2 T).1.mp hTT
    exact fun y hy hyA hyB => expAgreeAt_geoTransform_of_domain (hAB.geoTransformAlong T hTT)
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfA T hTT)
      (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwfB T hTB)
      (by rw [d_geoTransformAlong]; exact hdA) (by rw [d_geoTransformAlong, d_geoTransformAlong, hd])
      (HironakaG8SpecialLoci.sameCarrierDim_geoTransformAlong hwfA hwfB hAB.wEquiv hdim T hTT) ih hC hπ hy hyA hyB

/-- **With empty initial boundary** the initial agreement is vacuous. -/
theorem expAgreeAt_of_E_nil {X : CMfd.{0} n} {A B : MarkedIdeal n X} (hE : A.E = []) (x : X) : ExpAgreeAt A B x := by
  intro H hH
  rw [hE] at hH
  exact absurd hH List.not_mem_nil

end Tower

end

end Hironaka.HironakaG8DomainExponents
