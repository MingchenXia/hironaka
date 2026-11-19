import Hironaka.Resolution.HironakaG4RelativeDifferentialUnits
import Hironaka.Resolution.HironakaSharpActualPrincipalOrderOneTrace
import Hironaka.Resolution.HironakaSharpOriginalFirstMemberResidualPrincipal
import Hironaka.Resolution.HironakaSharpActualRelativeProductOrder
import Hironaka.Resolution.HironakaSharpActualTraceIncidence
import Hironaka.Resolution.HironakaSmoothSubmersionRelativeRestriction
import Hironaka.Resolution.HironakaMonomialBlowup
import Hironaka.Invariant.MemberInterAlong
import Hironaka.Resolution.HironakaSharpActualFirstAmbientStrictExponent

set_option autoImplicit false

/-!
# Actual prepared mixed-centre coordinates

The canonical WHOLE old trace includes all carrier-normal germs. The actual
nonmonomial residual supports and born traces are intrinsically prepared;
original old equations retain every monomial factor. No desired original NC,
reduction certificate, future step, blowup or termination is assumed.
Blueprint: `hironaka-g4-prepared-centre-coordinates.tex`.
-/

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4PreparedCentreCoordinates

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  Hironaka.RegularLocusDense BlowupTowers NormalCrossings NormalCrossingsComparison
  NormalCrossingsInvariance SimultaneousNormalCrossings BlowupFlatCoordinates
  HironakaSharpNormalCrossingsOpenLocus HironakaG4BoundaryDifferentialCriterion
  HironakaG4RelativeDifferentialUnits HironakaSharpActualPrincipalOrderOneTrace
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpActualRelativeProductOrder
  HironakaSharpActualTraceIncidence HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan RestrictedIdealExtension
  MonomialPartAlong DivisorExponentAlong InvertibleIdealQuotient MarkedIdeals
  MarkedIdeals.MarkedIdeal MemberPullback RankDegeneracy GermIdealOrder

variable {n : ℕ} {X : CMfd.{u} n}

/-- The whole actual old trace, including every carrier-normal germ. -/
def oldTraceIdeal (N : Set X) (old : List (Set X)) (i : Fin old.length) : GermIdeal n X :=
  restrictOn n N (vanishingIdeal (n := n) (old.get i))

/-- The independently defined actual monomial part of the whole old trace. -/
def oldMonomialPart (N : Set X) (old born : List (Set X)) (i : Fin old.length) : GermIdeal n X :=
  monomialPartAlong n N (oldTraceIdeal N old i) born

/-- The independently defined actual nonmonomial residual of the whole old trace. -/
def oldResidualPart (N : Set X) (old born : List (Set X)) (i : Fin old.length) : GermIdeal n X :=
  nonmonomialPartAlong n N (oldTraceIdeal N old i) born

/-- Literal residual supports together with literal born traces on the same carrier. -/
def preparedSupport (N : Set X) (old born : List (Set X)) :
    Fin old.length ⊕ Fin born.length → Set X :=
  Sum.elim (fun i => N ∩ (oldResidualPart N old born i).zeroLocus)
    (fun j => N ∩ born.get j)

/-- Genuine intrinsic joint SNC of the actual residual supports and all born
traces. Free indices are distinct only on actual incident support labels. -/
def IsPreparedResidualSNCAt (N : Set X) (old born : List (Set X)) (x : X) : Prop :=
  ∃ (S₀ : Finset (Fin n)) (p : Fin old.length ⊕ Fin born.length → Fin n),
    IsCoordinateFamilyAt n
      (fun o : Option (Fin old.length ⊕ Fin born.length) => o.elim N (preparedSupport N old born))
      (fun o => o.elim S₀ (fun a => S₀ ∪ {p a})) x ∧
    (∀ a, x ∈ preparedSupport N old born a → p a ∉ S₀) ∧
    Set.InjOn p {a | x ∈ preparedSupport N old born a}

/-- A transverse SNC list induces an intrinsic joint coordinate frame on its carrier. -/
theorem actual_trace_family_frame (hn : 0 < n) {N : Set X}
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E)
    {x : X} (hx : x ∈ N) :
    ∃ (Q : Finset (Fin n)) (s : Fin E.length → Fin n),
      IsCoordinateFamilyAt n
        (fun o : Option (Fin E.length) => o.elim N (fun i => N ∩ E.get i))
        (fun o => o.elim Q (fun i => Q ∪ {s i})) x ∧
      (∀ i,x ∈ N ∩ E.get i → s i ∉ Q) ∧
      Set.InjOn s {i | x ∈ N ∩ E.get i} := by
  obtain ⟨_kC,kN,Φ,s,_hsrc,hslt,hsinj,hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn
      (Subset.refl N) hE hTr hTr.hasNormalCrossings hx
  let Q : Finset (Fin n) := Finset.univ.filter fun t : Fin n => kN ≤ t.val
  refine ⟨Q,s,?_,?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | i) _hi y hy hyΦ
    · change y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.val)
      rw [coordSubspace_eq_complexCoordinatePlane]
      exact (hflat hy hyΦ).2.1
    · change y ∈ N ∩ E.get i ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace ((Finset.univ.filter fun t : Fin n => kN ≤ t.val) ∪ {s i})
      rw [ExceptionalPushforwardAlong.coordSubspace_union]
      change (y ∈ N ∧ y ∈ E.get i) ↔
        (Φ.toFun ((complexChartAt (n := n) x).val y) ∈
          coordSubspace (Finset.univ.filter fun t : Fin n => kN ≤ t.val) ∧
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace {s i})
      rw [coordSubspace_eq_complexCoordinatePlane,BlowupSNCTransform.mem_coordSubspace_singleton]
      exact and_congr (hflat hy hyΦ).2.1 ((hflat hy hyΦ).2.2 i _hi.2)
  · intro i hi hq
    have hge : kN ≤ (s i).val := (Finset.mem_filter.mp hq).2
    exact Nat.not_lt_of_ge hge (hslt i hi.2)
  · intro i hi j hj he
    exact hsinj hi.2 hj.2 he

/-- Both whole-ideal directions of normal-coordinate elimination along the
actual carrier. No reduced generator dictionary is an input. -/
theorem vanishingIdeal_coordinate_trace_mem_iff {N Z : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (S₀ : Finset (Fin n)) (p : Fin n) (_hp : p ∉ S₀)
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hNflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace S₀))
    (hZflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ Z ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S₀ ∪ {p})))
    (g : X → ℂ) :
    (vanishingIdeal (n := n) Z).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = flatCoord Φ p) x g := by
  classical
  have hwhole := HironakaSmoothSubmersionRelativeRestriction.vanishingIdeal_mem_iff_coordinate_family
    Φ (S₀ ∪ {p}) hsrc h0 hZflat g
  constructor
  · intro hg
    refine ⟨hg.1,IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (hwhole.mp hg))⟩
    intro a ha
    change ∃ j : Fin n, (if j ∈ S₀ ∪ {p} then flatCoord Φ j else fun _ : X => (0 : ℂ)) = a at ha
    obtain ⟨j,rfl⟩ := ha
    by_cases hj : j ∈ S₀
    · rw [if_pos (Finset.mem_union.mpr (Or.inl hj))]
      refine isInSpanOnAt_eq_iff.mpr ⟨0,holomorphicAt_const 0,?_⟩
      filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy hyN
      change Φ.toFun ((complexChartAt (n := n) x).val y) j = (0 : ℂ) * flatCoord Φ p y
      rw [zero_mul]
      exact ((hNflat hy.1 hy.2).mp hyN) j hj
    · by_cases hjp : j = p
      · subst j
        rw [if_pos (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self p)))]
        exact isInSpanOnAt_eq_iff.mpr ⟨1,holomorphicAt_const 1,
          Eventually.of_forall fun _ _ => by simp⟩
      · have hnot : j ∉ S₀ ∪ {p} := by simp only [Finset.mem_union,Finset.mem_singleton]; tauto
        rw [if_neg hnot]
        exact isInSpanOnAt_eq_iff.mpr ⟨0,holomorphicAt_const 0,
          Eventually.of_forall fun _ _ => by simp⟩
  · rintro ⟨hg,hspan⟩
    obtain ⟨a,_ha,hga⟩ := isInSpanOnAt_eq_iff.mp hspan
    refine ⟨hg,?_⟩
    filter_upwards [hga,(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy hyD hyZ
    have hz := (hZflat hyD.1 hyD.2).mp hyZ
    have hyN : y ∈ N := (hNflat hyD.1 hyD.2).mpr
      (fun j hj => hz j (Finset.mem_union.mpr (Or.inl hj)))
    rw [hy hyN]
    have hp0 := hz p (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self p)))
    change flatCoord Φ p y = 0 at hp0
    rw [hp0,mul_zero]

/-- Distinct free actual coordinate functions have independent native tangent
differentials, by the already proved genuine tangent-coordinate vectors. -/
theorem linearIndependent_restricted_flatCoords {N : Set X} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (S₀ : Finset (Fin n))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hNflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace S₀))
    {ι : Type*} [Fintype ι] (p : ι → Fin n) (hp : ∀ i, p i ∉ S₀)
    (hinj : Function.Injective p) :
    LinearIndependent ℂ (fun i => restrictedDifferential N (flatCoord Φ (p i)) x) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  obtain ⟨v,hv⟩ := exists_tangent_free_coordinate_vector Φ hsrc h0 S₀ hNflat (p i₀) (hp i₀)
  have heval (j : ι) : restrictedDifferential N (flatCoord Φ (p j)) x v =
      if j = i₀ then 1 else 0 := by
    change chartDifferential (flatCoord Φ (p j)) x (v : ComplexModel n) = _
    rw [hv]
    by_cases hj : j = i₀
    · subst j
      simp [EuclideanSpace.single]
    · have hpj : p j ≠ p i₀ := fun hh => hj (hinj hh)
      simp [EuclideanSpace.single,hj,hpj]
  have heq := DFunLike.congr_fun hc v
  simp only [sum_apply,smul_apply,zero_apply,heval,smul_eq_mul] at heq
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using heq

/-- The genuine canonical whole old trace and both native parts have actual
coherent nonzero geometry and the full normalized product identity. -/
theorem actual_old_parts_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length) :
    (oldTraceIdeal N old i).IsCoherent ∧
      (∀ y ∈ N,IsNonzeroAlongAt N (oldTraceIdeal N old i) y) ∧
      (oldResidualPart N old born i).IsCoherent ∧
      (∀ y ∈ N,IsNonzeroAlongAt N (oldResidualPart N old born i) y) ∧
      (oldMonomialPart N old born i).IsCoherent ∧
      (∀ y ∈ N,IsNonzeroAlongAt N (oldMonomialPart N old born i) y) ∧
      IsMonomialAlong n N (oldMonomialPart N old born i) born ∧
      oldTraceIdeal N old i = restrictOn n N
        ((oldMonomialPart N old born i).mul (oldResidualPart N old born i)) := by
  have hOld : IsSNCDivisor n old := isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hOld i)
  have hcI : (oldTraceIdeal N old i).IsCoherent :=
    isCoherent_restrictOn_of_isClosedSubmanifold hcH hN
  have hnzI : ∀ y ∈ N,IsNonzeroAlongAt N (oldTraceIdeal N old i) y := by
    intro y hy
    obtain ⟨g,hg,hfreq⟩ := originalMemberIdeal_isNonzeroAlongAt hE hdense
      (List.mem_append_left born (List.get_mem old i)) hy
    exact ⟨g,le_restrictOn hcH y g hg,hfreq⟩
  obtain ⟨hcJ,hcD,hnzD,hmD,_hNo,hnzJ,hFactor⟩ := NonmonomialTransformAlong.parts_hypotheses hn
    (⟨N,born,oldTraceIdeal N old i,0⟩ : MarkedIdeal n X) ⟨hN,hcI,hBorn,hTr⟩ hnzI
  have hWhole := MarkedIdealOperationsAlong.restrictOn_eq_of_restrictLe hN.1 hFactor.le hFactor.ge
  change restrictOn n N (oldTraceIdeal N old i) = restrictOn n N
    ((oldResidualPart N old born i).mul (oldMonomialPart N old born i)) at hWhole
  rw [RestrictLeCalculus.mul_comm' (oldResidualPart N old born i)
    (oldMonomialPart N old born i)] at hWhole
  have hNorm : restrictOn n N (oldTraceIdeal N old i) = oldTraceIdeal N old i := by
    ext y g
    exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
      fun hg => ⟨hg.1,IsInSpanAt.restrict (isInSpanAt_self hg hg.1)⟩⟩
  exact ⟨hcI,hnzI,hcJ,hnzJ,hcD,hnzD,hmD,hNorm.symm.trans hWhole⟩

private theorem actual_free_old_residual_dictionary (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    {x : X} (hx : x ∈ N) (hxH : x ∈ old.get i)
    (hUnit : (oldMonomialPart N old born i).mem x 1)
    (hOrd : ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1) :
    ∃ m : X → ℂ,HolomorphicAt n m x ∧ m x ≠ 0 ∧
      (∀ g,(oldMonomialPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=m) x g) ∧
      x ∈ preparedSupport N old born (Sum.inl i) ∧
      ∀ g,(oldResidualPart N old born i).mem x g ↔
        (vanishingIdeal (n := n) (preparedSupport N old born (Sum.inl i))).mem x g := by
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  obtain ⟨hcI,hnzI,hcJ,hnzJ,_hcD,_hnzD,_hmD,hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hE
    (List.mem_append_left born (List.get_mem old i)) x
  have hI : ∀ g,(oldTraceIdeal N old i).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
    fun g => and_congr_right fun _ => HironakaSharpOriginalMemberProduct.restricted_span_iff_principal hf hF g
  obtain ⟨_m,c,_hm,_hmD,hcJmem,_hfc,hJ⟩ :=
    exists_actual_relative_principal_residual hn hN hBorn hTr hcI hnzI hx f hf hI
  have hc : HolomorphicAt n c x := GermIdeal.IsCoherent.holomorphicAt_mem hcJ hcJmem
  obtain ⟨m,hmhol,_hpow,hmgen,_hmnz⟩ :=
    exists_generator_monomialPartAlong hn hN hBorn hTr hcI hnzI hx
  have hm := hmhol.self_of_nhds
  have hD := hmgen.self_of_nhds
  change ∀ g,(oldMonomialPart N old born i).mem x g ↔
    HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=m) x g at hD
  obtain ⟨a,_ha,haeq⟩ := isInSpanOnAt_eq_iff.mp ((hD 1).mp hUnit).2
  have hmx : m x ≠ 0 := by
    intro hz
    have hh := haeq.self_of_nhds hx
    simp only [hz,mul_zero] at hh
    exact one_ne_zero hh
  have hProd : ∀ g,(oldTraceIdeal N old i).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=(m*c)) x g := by
    rw [hWhole]
    exact restrictOn_mul_relative_principal_mem_iff hm hc hD hJ
  have hfI := (hF f).mpr (isInSpanAt_eq_iff.mpr
    ⟨hf,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp⟩)
  have hfx : f x = 0 := hfI.2.self_of_nhds hxH
  have hmcI := (hProd (m*c)).mpr ⟨hm.mul hc,isInSpanOnAt_eq_iff.mpr
    ⟨1,holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩⟩
  obtain ⟨b,_hb,hmc⟩ := isInSpanOnAt_eq_iff.mp ((hI (m*c)).mp hmcI).2
  have hmc0 : m x*c x = 0 := by simpa only [Pi.mul_apply,hfx,mul_zero] using hmc.self_of_nhds hx
  have hcx : c x = 0 := (mul_eq_zero.mp hmc0).resolve_left hmx
  have hxJ : x ∈ preparedSupport N old born (Sum.inl i) := by
    refine ⟨hx,fun g hg => ?_⟩
    obtain ⟨b,_hb,hgc⟩ := isInSpanOnAt_eq_iff.mp ((hJ g).mp hg).2
    simpa only [hcx,mul_zero] using hgc.self_of_nhds hx
  have hOne : x ∈ cosupport n N (oldResidualPart N old born i) 1 :=
    (cosupport_relative_principal_iff_vanishes hx hc hJ 1).mpr
      ((GermIdealOrder.vanishesToOrderOn_one_iff hx hc).mpr hcx)
  have hOrdOne : ordinaryTraceOrder N (oldResidualPart N old born i) x = 1 :=
    hOrd.antisymm ((HironakaSharpOriginalProductTraceOrder.ordinaryTraceOrder_cosupport_iff
      hN hcJ hnzJ hx 1).mp hOne)
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,_hreg⟩ :=
    actual_orderOne_relative_reduced_trace hN hcJ hnzJ hx c hc hJ hOrdOne
  exact ⟨m,hm,hmx,hD,hxJ,hRed⟩

private theorem actual_born_trace_dictionary (hn : 0 < n) {N : Set X}
    {born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hBorn : IsSNCDivisor n born) (hTr : IsTransverse n N born)
    (j : Fin born.length) {x : X} (hx : x ∈ N ∩ born.get j) :
    ∀ g,(restrictOn n N (vanishingIdeal (n := n) (born.get j))).mem x g ↔
      (vanishingIdeal (n := n) (N ∩ born.get j)).mem x g := by
  have hH : IsSNCDivisor n [born.get j] := isSNCDivisor_of_sublist hBorn (by simp)
  have hTH : IsTransverse n N [born.get j] := isTransverse_of_forall_mem hTr (by simp)
  obtain ⟨hcA,hnzA,hprA,hordA⟩ :=
    HironakaSharpActualFirstAmbientStrictExponent.actual_normalized_transverse_member_geometry hn hN hH hTH
  obtain ⟨f,hf,hF⟩ := hprA x hx.1
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,_hreg⟩ :=
    actual_orderOne_relative_reduced_trace hN hcA hnzA hx.1 f hf hF (hordA x hx)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hBorn j)
  have hSet : N ∩ (restrictOn n N (vanishingIdeal (n := n) (born.get j))).zeroLocus =
      N ∩ born.get j := by
    ext y
    constructor
    · rintro ⟨hyN,hyH⟩
      refine ⟨hyN,?_⟩
      have hh := (zeroLocus_restrictOn_iff hcH hyN).mp hyH
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
        (MonomialPart.isClosedSubmanifold_get hn hBorn j).1] at hh
    · rintro ⟨hyN,hyH⟩
      refine ⟨hyN,(zeroLocus_restrictOn_iff hcH hyN).mpr ?_⟩
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
        (MonomialPart.isClosedSubmanifold_get hn hBorn j).1]
  simpa only [hSet] using hRed

private theorem exists_prepared_relative_product_generator (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) {x : X} (hx : x ∈ N)
    (hOrd : ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (S₀ : Finset (Fin n)) (p : Fin old.length ⊕ Fin born.length → Fin n)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (hsrc : Φ.source ⊆ (complexChartAt (n := n) x).val.target)
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (hflat : ∀ o : Option (Fin old.length ⊕ Fin born.length),
      x ∈ o.elim N (preparedSupport N old born) → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ o.elim N (preparedSupport N old born) ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈
          coordSubspace (o.elim S₀ (fun a => S₀ ∪ {p a}))))
    (hfree : ∀ a,x ∈ preparedSupport N old born a → p a ∉ S₀)
    {H : Set X} (hxH : x ∈ H)
    (hH : H ∈ born ∨ ∃ i : Fin old.length,H=old.get i ∧ (oldMonomialPart N old born i).mem x 1) :
    ∃ (a : Fin old.length ⊕ Fin born.length) (m : X → ℂ),
      Sum.elim (fun i => old.get i) (fun j => born.get j) a = H ∧
      x ∈ preparedSupport N old born a ∧ HolomorphicAt n m x ∧ m x ≠ 0 ∧
      ∀ g,(restrictOn n N (vanishingIdeal (n := n) H)).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=(m*flatCoord Φ (p a))) x g := by
  have hNflat := fun {y : X} (hy : y ∈ (complexChartAt (n := n) x).val.source)
    (hyΦ : (complexChartAt (n := n) x).val y ∈ Φ.source) => hflat none hx hy hyΦ
  rcases hH with hBornH | ⟨i,rfl,hUnit⟩
  · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hBornH
    subst H
    have ha : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hx,hxH⟩
    have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
    have hRed := actual_born_trace_dictionary hn hN hBorn hTr j ha
    refine ⟨Sum.inr j,1,rfl,ha,holomorphicAt_const 1,one_ne_zero,?_⟩
    intro g
    exact (hRed g).trans (by
      simpa [preparedSupport] using vanishingIdeal_coordinate_trace_mem_iff Φ S₀ (p (Sum.inr j))
        (hfree _ ha) hsrc h0 hNflat (hflat (some (Sum.inr j)) ha) g)
  · obtain ⟨m,hm,hmx,hD,ha,hRed⟩ :=
      actual_free_old_residual_dictionary hn hN hE hTr hdense i hx hxH hUnit (hOrd i)
    have hJ : ∀ g,(oldResidualPart N old born i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=flatCoord Φ (p (Sum.inl i))) x g :=
      fun g => (hRed g).trans (vanishingIdeal_coordinate_trace_mem_iff Φ S₀ (p (Sum.inl i))
        (hfree _ ha) hsrc h0 hNflat (hflat (some (Sum.inl i)) ha) g)
    have hr := holomorphicAt_flatCoord Φ (p (Sum.inl i)) (mem_flatDomain_self Φ)
    obtain ⟨_hcI,_hnzI,_hcJ,_hnzJ,_hcD,_hnzD,_hmD,hWhole⟩ :=
      actual_old_parts_geometry hn hN hE hTr hdense i
    refine ⟨Sum.inl i,m,rfl,ha,hm,hmx,?_⟩
    change ∀ g,(oldTraceIdeal N old i).mem x g ↔ _
    rw [hWhole]
    exact restrictOn_mul_relative_principal_mem_iff hm hr hD hJ

/-- Genuine prepared residual geometry makes the actual original equations
independent for every retained born/unit-monomial old subfamily. -/
theorem linearIndependent_actual_free_boundary_equations (hn : 0 < n) {N : Set X}
    {old born F : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) {x : X} (hx : x ∈ N)
    (hOrd : ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : IsPreparedResidualSNCAt N old born x) (hFsub : F.Sublist (old ++ born))
    (hFree : ∀ H ∈ F,H ∈ born ∨ ∃ i : Fin old.length,
      H=old.get i ∧ (oldMonomialPart N old born i).mem x 1)
    (f : Fin F.length → X → ℂ) (hf : ∀ j,HolomorphicAt n (f j) x)
    (hgen : ∀ j g,(vanishingIdeal (n := n) (F.get j)).mem x g ↔
      IsInSpanAt (n := n) (·=f j) x g) :
    LinearIndependent ℂ (fun j : {j : Fin F.length // x ∈ F.get j} =>
      restrictedDifferential N (f j.val) x) := by
  classical
  obtain ⟨S₀,p,⟨Φ,hsrc,h0,hflat⟩,hp,hinj⟩ := hPrepared
  let K := {j : Fin F.length // x ∈ F.get j}
  have hRows (j : K) := exists_prepared_relative_product_generator hn hN hE hTr hdense hx hOrd
    S₀ p Φ hsrc h0 hflat hp j.property (hFree _ (List.get_mem F j.val))
  choose a m hLabel ha hm hmne hG using hRows
  have hFSNC : IsSNCDivisor n F := isSNCDivisor_of_sublist hE hFsub
  have haInj : Function.Injective a := by
    intro i j hij
    apply Subtype.ext
    apply SimultaneousNormalCrossings.eq_of_eventually_mem_iff hFSNC i.property j.property
    apply Eventually.of_forall
    intro y
    rw [← hLabel i,← hLabel j,hij]
  have hpInj : Function.Injective (fun j : K => p (a j)) := by
    intro i j hij
    exact haInj (hinj (ha i) (ha j) hij)
  have hCoordLI := linearIndependent_restricted_flatCoords Φ S₀ hsrc h0
    (fun hy hyΦ => hflat none hx hy hyΦ) (fun j : K => p (a j))
    (fun j => hp _ (ha j)) hpInj
  have hr (j : K) : HolomorphicAt n (flatCoord Φ (p (a j))) x :=
    holomorphicAt_flatCoord Φ (p (a j)) (mem_flatDomain_self Φ)
  have hr0 (j : K) : flatCoord Φ (p (a j)) x = 0 := by
    change Φ.toFun ((complexChartAt (n := n) x).val x) (p (a j)) = 0
    rw [h0]
    rfl
  let g : K → X → ℂ := fun j => m j*flatCoord Φ (p (a j))
  have hProductDifferential (j : K) : restrictedDifferential N (g j) x =
      m j x • restrictedDifferential N (flatCoord Φ (p (a j))) x :=
    restrictedDifferential_eq_smul_of_eventually_mul_on ((hm j).mul (hr j)) (hr j) (hm j) (hr0 j)
      (Eventually.of_forall fun _ _ => rfl)
  have hProductLI : LinearIndependent ℂ (fun j : K => restrictedDifferential N (g j) x) := by
    have hh := hCoordLI.units_smul (fun j : K => Units.mk0 (m j x) (hmne j))
    have heq : (fun j : K => restrictedDifferential N (g j) x) =
        fun j : K => m j x • restrictedDifferential N (flatCoord Φ (p (a j))) x :=
      funext hProductDifferential
    rw [heq]
    change LinearIndependent ℂ (fun j : K =>
      m j x • restrictedDifferential N (flatCoord Φ (p (a j))) x) at hh
    exact hh
  apply linearIndependent_restrictedDifferential_of_same_relative_generators
    (fun j : K => restrictOn n N (vanishingIdeal (n := n) (F.get j.val)))
    (fun j : K => f j.val) g
    (fun j => hf j.val) (fun j => (hm j).mul (hr j))
    (fun j => ?_) (fun j => by simp only [g,Pi.mul_apply,hr0,mul_zero])
    (fun j v => and_congr_right fun _ =>
      HironakaSharpOriginalMemberProduct.restricted_span_iff_principal (hf j.val) (hgen j.val) v)
    hG hProductLI
  have hfj := (hgen j.val (f j.val)).mpr (isInSpanAt_eq_iff.mpr
    ⟨hf j.val,1,holomorphicAt_const 1,Eventually.of_forall fun _ => by simp⟩)
  exact hfj.2.self_of_nhds j.property

/-- Actual prepared original equations give simultaneous coordinates for the
selected born intersection and every retained original member. -/
theorem normalCrossingsAt_prepared_selected_born_intersection (hn : 0 < n) {N : Set X}
    {old born F : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (S : Finset (Fin born.length))
    {x : X} (hx : x ∈ N ∩ BoundaryCount.memberInter born S)
    (hOrd : ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : IsPreparedResidualSNCAt N old born x) (hFsub : F.Sublist (old ++ born))
    (hFree : ∀ H ∈ F,H ∈ born ∨ ∃ i : Fin old.length,
      H=old.get i ∧ (oldMonomialPart N old born i).mem x 1)
    (hRetain : ∀ H ∈ born,H ∈ F) :
    normalCrossingsAt (n := n) (N ∩ BoundaryCount.memberInter born S) F x := by
  classical
  have hFSNC : IsSNCDivisor n F := isSNCDivisor_of_sublist hE hFsub
  have hgens (j : Fin F.length) := exists_originalMember_principal hn hFSNC (List.get_mem F j) x
  choose f hf hgen using hgens
  have hLI := linearIndependent_actual_free_boundary_equations hn hN hE hTr hdense hx.1 hOrd
    hPrepared hFsub hFree f hf hgen
  obtain ⟨S₀,T,⟨Φ,hsrc,h0,hflat⟩,hcard⟩ :=
    normalCrossingsAt_of_independent_boundary_differentials hn hN hFSNC hx.1 f hf hgen hLI
  have hidx (j : Fin born.length) : ∃ k : Fin F.length,F.get k=born.get j :=
    List.mem_iff_get.mp (hRetain _ (List.get_mem born j))
  choose idx hidx using hidx
  refine ⟨S₀ ∪ S.biUnion (fun j => T (idx j)),T,⟨Φ,hsrc,h0,?_⟩,hcard⟩
  rintro (_ | k) hxi y hy hyΦ
  · change (y ∈ N ∧ ∀ j ∈ S,y ∈ born.get j) ↔
      Φ.toFun ((complexChartAt (n := n) x).val y) ∈
        coordSubspace (S₀ ∪ S.biUnion (fun j => T (idx j)))
    have hunion (w : ComplexModel n) :
        w ∈ coordSubspace (S₀ ∪ S.biUnion (fun j => T (idx j))) ↔
          w ∈ coordSubspace S₀ ∧ w ∈ coordSubspace (S.biUnion (fun j => T (idx j))) := by
      simp only [coordSubspace,Finset.mem_union,mem_ofPred_eq]
      exact ⟨fun h => ⟨fun j hj => h j (Or.inl hj),fun j hj => h j (Or.inr hj)⟩,
        fun h j hj => hj.elim (h.1 j) (h.2 j)⟩
    rw [hunion,BoundaryCount.mem_coordSubspace_biUnion]
    refine and_congr (hflat none hx.1 hy hyΦ) (forall₂_congr fun j hj => ?_)
    have hborn := hflat (some (idx j))
      (by change x ∈ F.get (idx j); rw [hidx]; exact hx.2 j hj) hy hyΦ
    simpa only [Option.elim,hidx] using hborn
  · exact hflat (some k) hxi hy hyΦ

private theorem normalCrossingsAt_of_free_subfamily_and_local_containment
    {C : Set X} {E F : List (Set X)} (hC : IsClosed C) (hE : IsSNCDivisor n E)
    (hFsub : ∀ H ∈ F,H ∈ E) {x : X} (hx : x ∈ C)
    (hNC : normalCrossingsAt (n := n) C F x)
    (hcont : ∀ i : Fin E.length,E.get i ∉ F → ∀ᶠ y in 𝓝 x,y ∈ C → y ∈ E.get i) :
    normalCrossingsAt (n := n) C E x := by
  classical
  have hNCnear := eventually_normalCrossingsAt hC (fun H h => hE.1 H (hFsub H h)) hNC
  have hcontAll : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,E.get i ∉ F → y ∈ C → y ∈ E.get i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : E.get i ∈ F
    · exact Eventually.of_forall fun _ hnF => (hnF hi).elim
    · exact (hcont i hi).mono fun _ hy _ => hy
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp (hNCnear.and hcontAll)
  let U : Opens X := ⟨V,hVo⟩
  let z : U := ⟨x,hxV⟩
  let CU : Set U := (Subtype.val : U → X) ⁻¹' C
  let EU : List (Set U) := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let FU : List (Set U) := F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hCFU : HasNormalCrossings n CU FU := by
    intro y _hy
    exact HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mpr
      ((hV y.property).1)
  have hA : ∀ H ∈ EU,H ∉ FU → CU ⊆ H := by
    intro H hH hnot y hy
    obtain ⟨H₀,hH₀,rfl⟩ := List.mem_map.mp hH
    have hnot₀ : H₀ ∉ F := fun hh => hnot (List.mem_map.mpr ⟨H₀,hh,rfl⟩)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH₀
    change (y : X) ∈ H₀
    rw [← hi]
    exact (hV y.property).2 i (by rw [hi]; exact hnot₀) hy
  exact HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp
    (hasNormalCrossings_of_forall_notMem hEU hCFU hA z (show z ∈ CU from hx))

private theorem eventually_selected_centre_mem_old_of_row_hit (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    (S : Finset (Fin born.length)) {x : X} (hx : x ∈ N ∩ BoundaryCount.memberInter born S)
    (hHit : 1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) :
    ∀ᶠ y in 𝓝 x,y ∈ N ∩ BoundaryCount.memberInter born S → y ∈ old.get i := by
  have hOld : IsSNCDivisor n old := isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  obtain ⟨_hcI,_hnzI,hcJ,_hnzJ,hcD,hnzD,hmD,hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  have hCos := HironakaMonomialBlowup.eventually_mem_cosupp_of_le_sum hn
    (𝔪 := ⟨N,born,oldMonomialPart N old born i,1⟩) ⟨hN,hcD,hBorn,hTr⟩
    hnzD hmD hx.1 hx.2 hHit
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hOld i)
  filter_upwards [hCos] with y hy hyC
  have hyCos := hy hyC
  change y ∈ cosupport n N (oldMonomialPart N old born i) 1 at hyCos
  rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcD hg)] at hyCos
  have hyProd : y ∈ ((oldMonomialPart N old born i).mul (oldResidualPart N old born i)).zeroLocus := by
    rw [HironakaEffectiveDivisorSum.zeroLocus_mul_eq_union hcD hcJ]
    exact Or.inl hyCos.2
  have hyTrace : y ∈ (oldTraceIdeal N old i).zeroLocus := by
    rw [hWhole]
    exact (zeroLocus_restrictOn_iff (IdealWeightPowers.isCoherent_mul hcD hcJ) hyC.1).mpr hyProd
  have hyRaw := (zeroLocus_restrictOn_iff hcH hyC.1).mp hyTrace
  rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal
    (MonomialPart.isClosedSubmanifold_get hn hOld i).1] at hyRaw

/-- When every actual born factor is a unit the prepared frame is a
normal-crossings frame for the full ordered boundary. -/
theorem normalCrossingsAt_of_prepared_all_units {N : Set X} {old born : List (Set X)}
    (hn : 0<n) (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N⊆closure (N \ ⋃H∈old++born,H)) {x : X} (hx : x∈N)
    (hOrd : ∀a,ordinaryTraceOrder N (oldResidualPart N old born a) x≤1)
    (hPrep : IsPreparedResidualSNCAt N old born x)
    (hUnit : ∀a,(oldMonomialPart N old born a).mem x 1) :
    normalCrossingsAt (n:=n) N (old++born) x := by
  have h := normalCrossingsAt_prepared_selected_born_intersection hn hN hE hTr hdense
    (∅ : Finset (Fin born.length)) (by simpa [BoundaryCount.memberInter] using hx)
    hOrd hPrep (List.Sublist.refl _) (fun H hH => ?_) (fun _ h => List.mem_append_right _ h)
  · simpa [BoundaryCount.memberInter] using h
  · rcases List.mem_append.mp hH with hOld | hBorn
    · obtain ⟨a,rfl⟩ := List.mem_iff_get.mp hOld
      exact Or.inr ⟨a,rfl,hUnit a⟩
    · exact Or.inl hBorn

/-- The prepared born intersection has full-boundary normal crossings at a point whose nonunit rows are hit. -/
theorem prepared_selected_born_centre_nc_at (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (S : Finset (Fin born.length)) {x : X} (hx : x ∈ N ∩ BoundaryCount.memberInter born S)
    (hHit : ∀ i : Fin old.length,¬(oldMonomialPart N old born i).mem x 1 →
      1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) :
    normalCrossingsAt (n := n) (N ∩ BoundaryCount.memberInter born S) (old ++ born) x := by
  classical
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  have hC := MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hBorn hTr S
  let unitRow : Set X → Prop := fun H =>
    (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) born).mem x 1
  let F := (old ++ born).filter (fun H => decide (H ∈ born ∨ unitRow H))
  have hFmem (H : Set X) : H ∈ F ↔ H ∈ old ++ born ∧ (H ∈ born ∨ unitRow H) := by
    simp only [F,List.mem_filter,decide_eq_true_eq]
  have hFsub : F.Sublist (old ++ born) := List.filter_sublist
  have hFree : ∀ H ∈ F,H ∈ born ∨ ∃ i : Fin old.length,
      H=old.get i ∧ (oldMonomialPart N old born i).mem x 1 := by
    intro H hHF
    obtain ⟨hH,hKeep⟩ := (hFmem H).mp hHF
    rcases hKeep with hHB | hUnit
    · exact Or.inl hHB
    · rcases List.mem_append.mp hH with hHO | hHB
      · obtain ⟨i,hi⟩ := List.mem_iff_get.mp hHO
        refine Or.inr ⟨i,hi.symm,?_⟩
        change unitRow (old.get i)
        rw [hi]
        exact hUnit
      · exact Or.inl hHB
  have hRetain : ∀ H ∈ born,H ∈ F := by
    intro H hH
    exact (hFmem H).mpr ⟨List.mem_append_right old hH,Or.inl hH⟩
  have hNCfree := normalCrossingsAt_prepared_selected_born_intersection hn hN hE hTr hdense S hx
    (hOrd x hx.1) (hPrepared x hx.1) hFsub hFree hRetain
  apply normalCrossingsAt_of_free_subfamily_and_local_containment hC.1 hE
    (fun _ hH => hFsub.subset hH) hx hNCfree
  intro k hnot
  have hHfull : (old ++ born).get k ∈ old ++ born := List.get_mem _ _
  have hnotBorn : (old ++ born).get k ∉ born := by
    intro hB
    exact hnot ((hFmem _).mpr ⟨hHfull,Or.inl hB⟩)
  have hOld : (old ++ born).get k ∈ old := (List.mem_append.mp hHfull).resolve_right hnotBorn
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hOld
  have hNonunit : ¬(oldMonomialPart N old born i).mem x 1 := by
    intro hUnit
    apply hnot
    apply (hFmem _).mpr
    refine ⟨hHfull,Or.inr ?_⟩
    change unitRow (old.get i) at hUnit
    rwa [hi] at hUnit
  rw [← hi]
  exact eventually_selected_centre_mem_old_of_row_hit hn hN hE hTr hdense i S hx
    (hHit i hNonunit)


/-- A genuinely prepared selected born centre is closed smooth and has normal
crossings with the entire original ordered old-plus-born boundary. The actual
row-hit inequality produces all omitted old containments internally. -/
theorem prepared_selected_born_centre_geometry (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (S : Finset (Fin born.length))
    (hHit : ∀ x ∈ N ∩ BoundaryCount.memberInter born S,∀ i : Fin old.length,
      ¬(oldMonomialPart N old born i).mem x 1 →
        1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) :
    IsClosedSubmanifold n (N ∩ BoundaryCount.memberInter born S) ∧
      HasNormalCrossings n (N ∩ BoundaryCount.memberInter born S) (old ++ born) := by
  have hBorn : IsSNCDivisor n born := isSNCDivisor_of_sublist hE (List.sublist_append_right _ _)
  refine ⟨MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hBorn hTr S,?_⟩
  intro x hx
  exact prepared_selected_born_centre_nc_at hn hN hE hTr hdense hOrd hPrepared S hx (hHit x hx)

end

end Hironaka.HironakaG4PreparedCentreCoordinates
