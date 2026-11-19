import Hironaka.Resolution.HironakaG8ContactMax
import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.Resolution.HironakaSmoothSubmersionCoefficientIdeals
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace
import Hironaka.Resolution.HironakaAuxiliaryGraphGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The contact equivalence in local form (G8 lane, run 0080, round 5; (B') port P4)

Blueprint: `hironaka-g8-resume-local-contact.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §2 (P4),
§6b (module 6 and module 7 step (d2) need P4 in `LocWPEquiv` form); G8 `REPORT-r4.md` (route).

Bierstone--Milman 2008, Corollary 4.2 (with Remark 4.3 for the products with a line), along a closed submanifold `N`:
for a tangent direction `u` of `(𝔞|_N, d)` along `N`, `𝔪 ≈ 𝓒_N(𝔪)|_{N ∩ V(u)}`.  The library proves Włodarczyk's
equivalence (`ContactEquivalenceAlong.contact_wEquiv_along`, global multiple test blow-ups); here the LOCAL
`s(i,ii)`-equivalence `LocWPEquiv` of `HironakaG8LocalHistory` (admissible blowups, products with a line, restrictions to
open subsets of every stage), by the coinduction principle `HironakaG8LocalStable.LocEquiv.of_isLocStable`:

* **`ContactRel P Q F S`**: `P` has a closed carrier and a coherent ideal, mark `d ≥ 1`; `F i` (`i < d`) are marked ideals
  on `P.N` of mark `d - i`, coherent, with `F i ⊆ 𝓓_{P.N}^i(P.ideal)` on `P.N`; `S ⊆ P.N` is a closed submanifold of
  maximal contact (`HironakaG8ContactMax.MaxContact`) all of whose points are good
  (`HironakaG8ContactGood.GoodAt`); `Q` is restricted-equivalent to `(∑_i F i)|_S` (Włodarczyk's sum `msum`).
  `ContactRel.cosupp_eq` (`le:S` (2) and `le:Giraud` at a stage), **`ContactRel.geoTransform`** (one admissible blowup),
  **`ContactRel.pullback`** (pullback along a holomorphic submersion: products with a line, open restrictions),
  **`isLocStable_contactRel`**.
* **`locWPEquiv_contact_along`**: `𝔪 ≈ 𝓒_N(𝔪)|_{N ∩ V(u)}` (`LocWPEquiv`) for a tangent direction `u` on all of `X`;
  **`locWPEquiv_contact_open_along`**: on an open `U` (the strengthening of `contact_wEquiv_open_along`);
  **`locWPEquiv_contact_two_directions`**: two tangent directions `u`, `u'` give equivalent coefficient ideals on
  `U ∩ U'` (the tangent change of BM08 §5 Step I.A at the level of marked ideals).

Tools: `restrictEquiv_trans`, `restrictLe_pullback_map` (restricted inclusions pull back across dimensions),
`IsTangentDirectionAlong.mono_open`.

Sorry-free.  Universe-polymorphic.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalContact

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder IdealWeightPowers
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  CoefficientIdeal CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower
  CoefficientIdealAlongRestrictionTower DerivativeIdealAlong DerivativeIdealAlongCoherent RestrictedIdealWeight
  RestrictLeCalculus BlowupStrictSubmanifold BlowupFunctionTransform MarkedIdealBiholomorphism
  HironakaG8ContactGood HironakaG8ContactMax HironakaG8LocalHistory HironakaG8LocalStable
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient)
open Hironaka.HomogenizedGlueing (finSumIdeal)
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open scoped ProductComplexManifold

noncomputable section

/-! ### Two small tools -/

section Tools

variable {n m : ℕ} {M : CMfd.{u} n} {M' : CMfd.{u} m}

/-- **Restricted equivalence is transitive.** -/
theorem restrictEquiv_trans {A B C : MarkedIdeal n M} (h₁ : RestrictEquiv A B) (h₂ : RestrictEquiv B C) :
    RestrictEquiv A C := by
  have hle : RestrictLe A.N B.ideal C.ideal := by rw [h₁.N_eq]; exact h₂.le
  have hge : RestrictLe A.N C.ideal B.ideal := by rw [h₁.N_eq]; exact h₂.ge
  exact ⟨h₁.N_eq.trans h₂.N_eq, h₁.E_eq.trans h₂.E_eq, h₁.d_eq.trans h₂.d_eq, RestrictLe.trans h₁.le hle,
    RestrictLe.trans hge h₁.ge⟩

/-- **A restricted inclusion pulls back** along a holomorphic map between manifolds of possibly different dimensions
(the two-dimension form of `RestrictLeCalculus.restrictLe_pullback`). -/
theorem restrictLe_pullback_map {f : M' → M} (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {V : Set M} {W : Set M'} (hWV : ∀ y ∈ W, f y ∈ V) {𝔞 𝔟 : GermIdeal n M} (h𝔟 : 𝔟.IsCoherent)
    (h : RestrictLe V 𝔞 𝔟) :
    RestrictLe W (GermIdeal.pullback (m := m) f 𝔞) (GermIdeal.pullback (m := m) f 𝔟) := by
  intro y hy G hG
  refine RelativePrincipalizationSpan.IsInSpanOnAt.trans ?_ (RelativePrincipalizationSpan.IsInSpanAt.restrict
    (show IsInSpanAt (n := m) (fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) y G from hG))
  rintro s ⟨a, ha, rfl⟩
  obtain ⟨N, b, d, hb, hd, hsum⟩ := h (f y) (hWV y hy) a ha
  have hfd : ∀ w, MDifferentiableAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) f w :=
    fun w => (hf w).mdifferentiableAt (by simp)
  refine ⟨N, fun i => b i ∘ f, fun i => d i ∘ f, fun i => ?_,
    fun i => HadamardBridge.holomorphicAt_comp_map (Eventually.of_forall hfd) (hd i), ?_⟩
  · exact comp_mem_pullback hfd (hb i) (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔟 (hb i))
  · filter_upwards [hf.continuous.continuousAt.eventually hsum] with z hz hzW
    exact hz (hWV z hzW)

end Tools

/-! ### The relation -/

section Rel

variable {m : ℕ} {Y : CMfd.{u} m}

/-- **The contact relation at a stage**: `P` (closed carrier, coherent ideal, mark `d ≥ 1`), a family `F` of marked
ideals on `P.N` (`F i` of mark `d - i`, coherent, `F i ⊆ 𝓓_{P.N}^i(P.ideal)` on `P.N`; the stand-ins for the transforms
of the derivative ideals of the base), a closed submanifold `S ⊆ P.N` of maximal contact all of whose points are good,
and `Q` restricted-equivalent to `(F 0 + ⋯ + F (d-1))|_S`. -/
structure ContactRel (P Q : MarkedIdeal m Y) (F : ℕ → MarkedIdeal m Y) (S : Set Y) : Prop where
  closed : IsClosedSubmanifold m P.N
  coh : P.ideal.IsCoherent
  d_pos : 1 ≤ P.d
  fN : ∀ i < P.d, (F i).N = P.N
  fE : ∀ i < P.d, (F i).E = P.E
  fd : ∀ i < P.d, (F i).d = P.d - i
  fcoh : ∀ i < P.d, (F i).ideal.IsCoherent
  fle : ∀ i < P.d, RestrictLe P.N (F i).ideal (iterDerivIdealAlong P.N P.ideal i)
  sub : IsClosedSubmanifold m S
  SN : S ⊆ P.N
  contact : MaxContact P S
  good : ∀ p ∈ S, GoodAt P F S p
  qcoh : Q.ideal.IsCoherent
  equiv : RestrictEquiv Q (withN (msum F P.d) S)

namespace ContactRel

variable {P Q : MarkedIdeal m Y} {F : ℕ → MarkedIdeal m Y} {S : Set Y}

/-- The family `F` is a family on the closed submanifold `P.N`. -/
theorem fam (h : ContactRel P Q F S) : IsSubmanifoldFamily F P.d where
  N i hi := by rw [h.fN i hi, h.fN 0 h.d_pos]
  E i hi := by rw [h.fE i hi, h.fE 0 h.d_pos]
  closed := by rw [h.fN 0 h.d_pos]; exact h.closed
  coh := h.fcoh
  d i hi := by rw [h.fd i hi]; omega

/-- The same boundary. -/
theorem E_eq (h : ContactRel P Q F S) : Q.E = P.E := by
  rw [h.equiv.E_eq]
  exact h.fE 0 h.d_pos

/-- The cosupport of `P` lies in that of each `F i` (Giraud along `N`). -/
theorem cosupp_subset_F (h : ContactRel P Q F S) {i : ℕ} (hi : i < P.d) : P.cosupp ⊆ (F i).cosupp := by
  intro x hx
  have h1 : x ∈ cosupport m P.N P.ideal ((P.d - i) + i) := by rw [Nat.sub_add_cancel hi.le]; exact hx
  have h2 := TangentDirectionAlong.cosupport_add_subset_cosupport_iterDerivIdealAlong (hol_of_isCoherent h.coh)
    (P.d - i) i h1
  have h3 := cosupport_subset_of_restrictLe (h.fle i hi) _ h2
  show x ∈ cosupport m (F i).N (F i).ideal (F i).d
  rw [h.fN i hi, h.fd i hi]
  exact h3

/-- **The same cosupport** (`le:Giraud` and `le:S` (2) at a stage): `cosupp P = cosupp Q`. -/
theorem cosupp_eq (h : ContactRel P Q F S) : P.cosupp = Q.cosupp := by
  rw [h.equiv.cosupp_eq, cosupp_withN]
  have hfam := h.fam
  have hm := h.d_pos
  ext x
  constructor
  · intro hx
    have hxS : x ∈ S := h.contact.cosupp_subset h.coh hm hx
    have hK : x ∈ (msum F P.d).cosupp := by
      rw [cosupp_msum_along hfam hm]
      exact fun i hi => h.cosupp_subset_F hi hx
    have hSK : S ⊆ (msum F P.d).N := by
      show S ⊆ (F 0).N
      rw [h.fN 0 hm]
      exact h.SN
    exact CoefficientIdealAlongRestriction.cosupport_inter_subset_of_subset hSK _ _ ⟨hK, hxS⟩
  · intro hx
    have hxS : x ∈ S := hx.1
    have hJ : ∀ i < P.d, ∀ y g, (idealPow (F i).ideal (sumExp (fun j => (F j).d) P.d i)).mem y g →
        HolomorphicAt m g y := fun _ _ _ _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg
    have hx' : x ∈ cosupport m S (finSumIdeal (fun i => idealPow (F i).ideal (sumExp (fun j => (F j).d) P.d i)) P.d)
        (msum F P.d).d := hx
    have hD : ∀ i < P.d, OrderGE m S (F i).ideal x (P.d - i) := by
      intro i hi
      have hx3 := ((mem_cosupport_finSumIdeal hJ).mp hx').2 i hi
      have hpow := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along h.sub.2
        (hol_of_isCoherent (h.fcoh i hi)) (one_le_sumExp (fun j hj => hfam.d j hj) i) (F i).d
      have hmark : (msum F P.d).d = (F i).d * sumExp (fun j => (F j).d) P.d i :=
        (mul_sumExp (fun j => (F j).d) hi).symm
      rw [hmark, hpow, h.fd i hi] at hx3
      exact hx3.2
    exact ⟨h.SN hxS, (h.good x hxS).orderGE h.coh hD⟩

/-- **One admissible blowup.** -/
theorem geoTransform (h : ContactRel P Q F S) {C : Set Y} {Z : CMfd.{u} m} {π : Z → Y}
    (hπ : IsBlowupAlong m C π) (hC : P.IsAdmissibleCentre C) :
    ContactRel (P.geoTransform C π) (Q.geoTransform C π) (fun i => (F i).geoTransform C π)
      (geoStrictTransform π C S) := by
  have hm := h.d_pos
  have hfam := h.fam
  have hπc : Continuous π := hπ.contMDiff.continuous
  have hCS : C ⊆ S := fun x hx => h.contact.cosupp_subset h.coh hm (hC.2.1 hx)
  have hCF : ∀ i < P.d, (F i).IsAdmissibleCentre C := fun i hi =>
    ⟨hC.1, fun x hx => h.cosupp_subset_F hi (hC.2.1 hx), by rw [h.fE i hi]; exact hC.2.2⟩
  have hFN : ∀ i < P.d, IsClosedSubmanifold m (F i).N := fun i hi => by rw [h.fN i hi]; exact h.closed
  have hKN : (msum F P.d).N = P.N := h.fN 0 hm
  have hKcoh : (msum F P.d).ideal.IsCoherent := hfam.isCoherent_msum
  have hCK : (msum F P.d).IsAdmissibleCentre C := (isAdmissibleCentre_msum_along_iff hfam hm).mpr hCF
  have hSK : S ⊆ (msum F P.d).N := by rw [hKN]; exact h.SN
  have hCKS : (withN (msum F P.d) S).IsAdmissibleCentre C :=
    ⟨hC.1, fun x hx => CoefficientIdealAlongRestriction.cosupport_inter_subset_of_subset hSK _ _
      ⟨hCK.2.1 hx, hCS hx⟩, hCK.2.2⟩
  have hQeq : Q.geoTransform C π = (withN (msum F P.d) S).geoTransform C π :=
    h.equiv.geoTransform_eq (by rw [h.equiv.N_eq]; exact h.sub.1) h.qcoh hKcoh hπ.contMDiff
  refine ⟨isClosedSubmanifold_geoTransform_N h.closed hC hπ,
    HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre h.closed h.coh hC hπ, hm,
    fun i hi => by simp only [geoTransform_N, h.fN i hi], fun i hi => by simp only [geoTransform_E, h.fE i hi],
    fun i hi => h.fd i hi,
    fun i hi => HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (hFN i hi) (h.fcoh i hi)
      (hCF i hi) hπ,
    ?_, BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ h.sub hCS,
    geoStrictTransform_mono' π C h.SN, maxContact_geoTransform h.closed h.coh hm h.SN h.contact hπ hC, ?_, ?_, ?_⟩
  · -- the derivative inclusions (Giraud along `N`, monotonicity of the transform)
    intro i hi
    replace hi : i < P.d := hi
    have hCD' : (derivMarkedAlong P i).IsAdmissibleCentre C := by
      refine ⟨hC.1, fun y hy => ?_, hC.2.2⟩
      have h1 : y ∈ cosupport m P.N P.ideal ((P.d - i) + i) := by
        rw [Nat.sub_add_cancel hi.le]; exact hC.2.1 hy
      exact TangentDirectionAlong.cosupport_add_subset_cosupport_iterDerivIdealAlong (hol_of_isCoherent h.coh)
        (P.d - i) i h1
    have h1 := restrictLe_geoTransform_of_restrictLe (𝔫₁ := F i) (𝔫₂ := derivMarkedAlong P i) (hFN i hi)
      (h.fN i hi) (h.fd i hi) (h.fcoh i hi) (isCoherent_iterDerivIdealAlong h.coh h.closed i) (hCF i hi) hCD' hπ
      (by rw [h.fN i hi]; exact h.fle i hi)
    have h2 := DerivativeIdealAlongTransform.restrictLe_geoTransform_derivMarkedAlong P h.closed h.coh hC hπ
      (j := i) hi.le
    have hW : ((F i).geoTransform C π).N = geoStrictTransform π C P.N := by rw [geoTransform_N, h.fN i hi]
    rw [hW] at h1
    exact RestrictLe.trans h1 h2
  · -- every point of `S'` is good
    intro z hz
    have hpz : π z ∈ S := geoStrictTransform_subset_preimage hπc h.sub.1 hz
    by_cases hzC : π z ∈ C
    · exact goodAt_step_of_mem P F hπ h.closed h.coh h.fN h.fd h.fcoh hC hCF h.sub.1 h.SN hCS hz hzC (h.good _ hpz)
    · exact goodAt_step_of_notMem P F hπ h.closed.1 h.coh h.fcoh h.sub.1 hzC (h.good _ hpz)
  · rw [hQeq]
    exact HadamardBridgeAlong.isCoherent_geoTransform_ideal_of_isAdmissibleCentre (𝔪 := withN (msum F P.d) S) h.sub
      hKcoh hCKS hπ
  · rw [hQeq]
    have e1 := geoTransform_withN_restrictEquiv_along (𝔟 := msum F P.d) (by rw [hKN]; exact h.closed) hKcoh h.sub hSK
      hπ hCK hCKS
    have e2 := geoTransform_msum_restrictEquiv hfam hm hπ hCF
    have hS'sub : geoStrictTransform π C S ⊆ ((msum F P.d).geoTransform C π).N := geoStrictTransform_mono' π C hSK
    have e3 : RestrictEquiv (withN ((msum F P.d).geoTransform C π) (geoStrictTransform π C S))
        (withN (msum (fun i => (F i).geoTransform C π) P.d) (geoStrictTransform π C S)) :=
      ⟨rfl, e2.E_eq, e2.d_eq, restrictLe_mono hS'sub e2.le, restrictLe_mono hS'sub e2.ge⟩
    exact restrictEquiv_trans e1 e3

end ContactRel

end Rel

/-! ### Pullback along a holomorphic submersion -/

section Pullback

variable {n r : ℕ} {Y : CMfd.{u} n} {Y' : CMfd.{u} (n + r)} {f : Y' → Y}

/-- **Pullback along a holomorphic submersion** `f : Y' → Y` (`dim Y' = n + r`): the pulled-back data (any boundaries,
with `F' i` and `Q'` on the boundary of `P'`) are again related. -/
theorem ContactRel.pullback (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n + r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    {P Q : MarkedIdeal n Y} {F : ℕ → MarkedIdeal n Y} {S : Set Y} (h : ContactRel P Q F S)
    {P' Q' : MarkedIdeal (n + r) Y'} {F' : ℕ → MarkedIdeal (n + r) Y'}
    (hPN : P'.N = f ⁻¹' P.N) (hPI : P'.ideal = GermIdeal.pullback (m := n + r) f P.ideal) (hPd : P'.d = P.d)
    (hFN : ∀ i, (F' i).N = f ⁻¹' (F i).N) (hFE : ∀ i < P.d, (F' i).E = P'.E)
    (hFI : ∀ i, (F' i).ideal = GermIdeal.pullback (m := n + r) f (F i).ideal) (hFd : ∀ i, (F' i).d = (F i).d)
    (hQN : Q'.N = f ⁻¹' Q.N) (hQE : Q'.E = P'.E) (hQI : Q'.ideal = GermIdeal.pullback (m := n + r) f Q.ideal)
    (hQd : Q'.d = Q.d) : ContactRel P' Q' F' (f ⁻¹' S) := by
  have hfc := hf.contMDiff
  have hm := h.d_pos
  have hfam := h.fam
  have hKcoh : (msum F P.d).ideal.IsCoherent := hfam.isCoherent_msum
  have hI : (msum F' P'.d).ideal = GermIdeal.pullback (m := n + r) f (msum F P.d).ideal := by
    show finSumIdeal (fun i => idealPow (F' i).ideal (sumExp (fun j => (F' j).d) P'.d i)) P'.d =
      GermIdeal.pullback (m := n + r) f
        (finSumIdeal (fun i => idealPow (F i).ideal (sumExp (fun j => (F j).d) P.d i)) P.d)
    rw [HironakaSmoothSubmersionCoefficientIdeals.pullback_finSumIdeal hfc _ _
      (fun i hi => GermIdealPullbackCalculus.isCoherent_idealPow (h.fcoh i hi) _), hPd]
    refine finSumIdeal_congr fun i hi => ?_
    rw [hFI i, HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow hfc (h.fcoh i hi)]
    simp only [hFd]
  refine ⟨?_, ?_, by rw [hPd]; exact hm, fun i hi => ?_, fun i hi => hFE i (by rw [← hPd]; exact hi),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf h.sub, ?_,
    maxContact_pullback_submersion hf hPN hPI hPd h.closed h.coh h.contact,
    fun p hp => goodAt_pullback_submersion hf hPN hPI hPd (fun i _ => hFI i) h.coh h.fcoh (h.good _ hp), ?_, ?_⟩
  · rw [hPN]; exact HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf h.closed
  · rw [hPI]; exact GermIdealPullbackCalculus.isCoherent_pullback hfc h.coh
  · rw [hPd] at hi; rw [hFN, hPN, h.fN i hi]
  · rw [hPd] at hi ⊢; rw [hFd, h.fd i hi]
  · rw [hPd] at hi; rw [hFI]; exact GermIdealPullbackCalculus.isCoherent_pullback hfc (h.fcoh i hi)
  · rw [hPd] at hi
    rw [hFI, hPN, hPI, ← HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_iterDerivIdealAlong hf P.ideal
      h.coh P.N h.closed i]
    exact restrictLe_pullback_map hfc (fun y hy => hy) (isCoherent_iterDerivIdealAlong h.coh h.closed i) (h.fle i hi)
  · rw [hPN]; exact preimage_mono h.SN
  · rw [hQI]; exact GermIdealPullbackCalculus.isCoherent_pullback hfc h.qcoh
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hQN, h.equiv.N_eq]; rfl
    · show Q'.E = (F' 0).E
      rw [hQE, hFE 0 hm]
    · show Q'.d = (Finset.range P'.d).prod fun j => (F' j).d
      rw [hQd, h.equiv.d_eq, hPd]
      show ((Finset.range P.d).prod fun j => (F j).d) = (Finset.range P.d).prod fun j => (F' j).d
      simp only [hFd]
    · show RestrictLe Q'.N Q'.ideal (msum F' P'.d).ideal
      rw [hI, hQI, hQN]
      exact restrictLe_pullback_map hfc (fun y hy => hy) hKcoh h.equiv.le
    · show RestrictLe Q'.N (msum F' P'.d).ideal Q'.ideal
      rw [hI, hQI, hQN]
      exact restrictLe_pullback_map hfc (fun y hy => hy) h.qcoh h.equiv.ge

end Pullback

/-! ### Stability and the local contact equivalence -/

section Stable

/-- The relation of the coinduction: some family and some hypersurface relate `P` and `Q`. -/
def ContactR {m : ℕ} {Y : CMfd.{u} m} (P Q : MarkedIdeal m Y) : Prop :=
  ∃ (F : ℕ → MarkedIdeal m Y) (S : Set Y), ContactRel P Q F S

/-- **The contact relation is stable under the local test actions of kinds `wp`.** -/
theorem isLocStable_contactRel : IsLocStable.{u} Kinds.wp (fun {m} {Y} P Q => ContactR (m := m) (Y := Y) P Q) where
  E_eq := fun ⟨_, _, h⟩ => h.E_eq
  cosupp_eq := fun ⟨_, _, h⟩ => h.cosupp_eq
  controlled := fun ⟨F, S, h⟩ C _ π hπ hC => ⟨_, _, h.geoTransform hπ hC⟩
  projection := by
    intro _ m Y P Q ⟨F, S, h⟩
    have hEP : ∀ A B : MarkedIdeal m Y, A.E = B.E → (projectionTest A).E = (projectionTest B).E := by
      intro A B hAB
      simp only [projectionTest, hAB]
    exact ⟨fun i => projectionTest (F i), _, h.pullback (r := 1) (f := (Prod.fst : projectionAmbient Y → Y))
      (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := m) (m := 1) (X := Y) (Y := ComplexModel 1))
      rfl rfl rfl (fun _ => rfl) (fun i hi => hEP _ _ (h.fE i hi)) (fun _ => rfl) (fun _ => rfl) rfl
      (hEP _ _ h.E_eq) rfl rfl⟩
  restrict := by
    intro m Y P Q ⟨F, S, h⟩ U
    exact ⟨fun i => MarkedIdeal.pullback (Subtype.val : U → Y) (F i), _,
      h.pullback (r := 0) (Y' := CMfd.of (n := m) U) (f := (Subtype.val : U → Y))
        (HironakaSmoothSubmersionOrderedGlobalTrace.isSubmersion_val U)
        rfl rfl rfl (fun _ => rfl) (fun i hi => by simp only [MarkedIdeal.pullback, h.fE i hi]) (fun _ => rfl)
        (fun _ => rfl) rfl (by simp only [MarkedIdeal.pullback, h.E_eq]) rfl rfl⟩

variable {n : ℕ} {X : CMfd.{u} n}

/-- **Bierstone--Milman's Corollary 4.2 along `N`, local `s(i,ii)` form** (Włodarczyk `le:codim2` strengthened): for
`𝔪 = (X, N, E, 𝔞, d)` with `N` a closed submanifold, `𝔞` coherent, `d ≥ 1`, and a tangent direction `u` of `(𝔞|_N, d)`
along `N` on all of `X`, `𝔪 ≈ 𝓒_N(𝔪)|_{N ∩ V(u)}` for the local equivalence `LocWPEquiv` (admissible blowups, products
with a line, open restrictions of every stage). -/
theorem locWPEquiv_contact_along (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hd : 1 ≤ 𝔪.d) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d univ u) :
    LocWPEquiv 𝔪 (withN (coeffMarkedAlong 𝔪) (𝔪.N ∩ {x | u x = 0} ∩ univ)) := by
  have hS := ContactEquivalenceAlong.isClosedSubmanifold_contact_along hN h𝔞 hu
  have hSN : 𝔪.N ∩ {x | u x = 0} ∩ univ ⊆ 𝔪.N := fun x hx => hx.1.1
  refine LocEquiv.of_isLocStable isLocStable_contactRel rfl
    ⟨fun i => derivMarkedAlong 𝔪 i, 𝔪.N ∩ {x | u x = 0} ∩ univ, ?_⟩
  exact ⟨hN, h𝔞, hd, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun i _ => isCoherent_iterDerivIdealAlong h𝔞 hN i,
    fun i _ => restrictLe_refl (isCoherent_iterDerivIdealAlong h𝔞 hN i), hS, hSN, maxContact_base 𝔪 h𝔞 hu,
    fun p hp => goodAt_base 𝔪 hN h𝔞 hS hSN hp, isCoherent_coeffMarkedAlong h𝔞 hN,
    RestrictEquiv.refl (isCoherent_coeffMarkedAlong h𝔞 hN)⟩

/-- **The local contact equivalence on an open set**: for a tangent direction `u` along `N` on an open `U`,
`𝔪|_U ≈ (U, ι⁻¹(N ∩ V(u)), E|_U, 𝓒_N(𝔞)|_U, μ_𝓒)` (`LocWPEquiv`; the strengthening of
`ContactEquivalenceAlong.contact_wEquiv_open_along`). -/
theorem locWPEquiv_contact_open_along (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u) :
    LocWPEquiv (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪)
      (withN (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong 𝔪))
        ((Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {y | u y = 0}))) := by
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → X) := contMDiff_subtype_val
  have hNU : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hcohU : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval h𝔞
  have huU := ContactEquivalenceAlong.isTangentDirectionAlong_pullback_val U
    (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞) hu
  have h := locWPEquiv_contact_along (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) hNU
    hcohU hd huU
  rw [HomogenizedIdealAlong.pullback_val_coeffMarkedAlong U 𝔪 h𝔞 hN hd]
  have hS : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪).N ∩ {x : U | (u ∘ Subtype.val) x = 0} ∩ univ =
      (Subtype.val : U → X) ⁻¹' (𝔪.N ∩ {y | u y = 0}) := by
    ext y
    simp [MarkedIdeal.pullback]
  rw [← hS]
  exact h

/-- A tangent direction on `U` is one on every open subset of `U`. -/
theorem IsTangentDirectionAlong.mono_open {N : Set X} {𝔞 : GermIdeal n X} {μ : ℕ} {U W : Set X} {u : X → ℂ}
    (hu : TangentDirectionAlong.IsTangentDirectionAlong N 𝔞 μ U u) (hW : IsOpen W) (hWU : W ⊆ U) :
    TangentDirectionAlong.IsTangentDirectionAlong N 𝔞 μ W u :=
  ⟨hW, fun y hy => hu.mem y (hWU hy), fun y hy => hu.multiplicity_one y (hWU hy)⟩

/-- **Two tangent directions give locally equivalent coefficient ideals on a common open subset** (BM08 §5 Step I.A at
the level of marked ideals): for tangent directions `u` on `U` and `u'` on `U'` and an open `W ⊆ U ∩ U'`, the two
restricted coefficient ideals on `W` are `LocWPEquiv`. -/
theorem locWPEquiv_contact_two_directions (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N)
    (h𝔞 : 𝔪.ideal.IsCoherent) (hd : 1 ≤ 𝔪.d) {U U' : Set X} {u u' : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u) (hu' : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U' u')
    (W : Opens X) (hWU : (W : Set X) ⊆ U) (hWU' : (W : Set X) ⊆ U') :
    LocWPEquiv (X := CMfd.of (n := n) W)
      (withN (MarkedIdeal.pullback (Subtype.val : W → X) (coeffMarkedAlong 𝔪))
        ((Subtype.val : W → X) ⁻¹' (𝔪.N ∩ {y | u y = 0})))
      (withN (MarkedIdeal.pullback (Subtype.val : W → X) (coeffMarkedAlong 𝔪))
        ((Subtype.val : W → X) ⁻¹' (𝔪.N ∩ {y | u' y = 0}))) := by
  have h1 := locWPEquiv_contact_open_along 𝔪 hN h𝔞 hd W (IsTangentDirectionAlong.mono_open hu W.isOpen hWU)
  have h2 := locWPEquiv_contact_open_along 𝔪 hN h𝔞 hd W (IsTangentDirectionAlong.mono_open hu' W.isOpen hWU')
  exact h1.symm.trans h2

end Stable

end

end Hironaka.HironakaG8LocalContact
