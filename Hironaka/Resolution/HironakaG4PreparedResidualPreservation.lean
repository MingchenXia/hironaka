import Hironaka.Resolution.HironakaG4PreparedResidualTotalNoFactor
import Hironaka.Resolution.HironakaG4TransverseBoundaryStrictPullback
import Hironaka.Resolution.HironakaSharpActualRawMemberOpenStrict
import Hironaka.Resolution.HironakaSharpActualMixedCurveContactEvolution

/-! Actual prepared residual preservation on a genuine selected-born blowup.
Complete approved source-first proof: hironaka-g4-prepared-residual-preservation.tex.
Auxiliary ambient lifts live on real opens; no residual support is substituted
for an ambient divisor, and no future mixed residual dictionary is assumed. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4PreparedResidualPreservation

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupStrictSubmanifold NormalCrossings NormalCrossingsInvariance
  HironakaG4PreparedCentreCoordinates HironakaG4PreparedResidualTotalNoFactor
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalFirstMemberResidualPrincipal HironakaSharpActualPrincipalOrderOneTrace
  HironakaSharpOriginalMemberProduct RelativePrincipalizationSpan RestrictedIdealExtension
  GermIdealOrder MonomialPartAlong DivisorExponentAlong
  HironakaSharpNormalCrossingsOpenLocus BlowupFlatCoordinates BoundaryCount

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem isClosed_actual_flat_lift {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ) (q : Fin n) :
    IsClosed {a : U | flatCoord Φ q a.val = 0} := by
  have hc : Continuous (fun a : U => flatCoord Φ q a.val) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (holomorphicAt_flatCoord Φ q (hU a.property)).continuousAt.comp
      continuous_subtype_val.continuousAt
  exact isClosed_eq hc continuous_const

private theorem normalized_order_le_one_reduced {N : Set X} {I : GermIdeal n X}
    (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N I x)
    (hpr : ∀ x ∈ N,∃ f : X → ℂ,HolomorphicAt n f x ∧
      ∀ g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g)
    (hNormal : (vanishingIdeal (n := n) N).Le I)
    (hOrd : ∀ x ∈ N ∩ I.zeroLocus,ordinaryTraceOrder N I x ≤ 1) :
    IsClosedSubmanifold n (N ∩ I.zeroLocus) ∧
      I=vanishingIdeal (n := n) (N ∩ I.zeroLocus) := by
  let Z := N ∩ I.zeroLocus
  have hZeroSub : I.zeroLocus ⊆ N := by
    intro x hx
    have hh : x ∈ (vanishingIdeal (n := n) N).zeroLocus :=
      fun g hg => hx g (hNormal x g hg)
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hN.1] at hh
  have hZ : IsClosed Z := hN.1.inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus hI).isClosed
  have hPoint (x : X) (hx : x ∈ Z) :
      (∀ g,I.mem x g ↔ (vanishingIdeal (n := n) Z).mem x g) ∧
        ∃ k,RegularAtDim (n := n) N x k ∧ RegularAtDim (n := n) Z x (k-1) := by
    have hCos : x ∈ cosupport n N I 1 := by
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg)]
      exact hx
    have hOne : ordinaryTraceOrder N I x=1 :=
      (hOrd x hx).antisymm ((ordinaryTraceOrder_cosupport_iff hN hI hnz hx.1 1).mp hCos)
    obtain ⟨f,hf,hgen⟩ := hpr x hx.1
    obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,hReg⟩ :=
      actual_orderOne_relative_reduced_trace hN hI hnz hx.1 f hf hgen hOne
    exact ⟨hRed,hReg⟩
  refine ⟨⟨hZ,fun x hx => ?_⟩,?_⟩
  · obtain ⟨k,_hN,hZ⟩ := (hPoint x hx).2
    exact ⟨k-1,hZ⟩
  · ext x g
    by_cases hx : x ∈ Z
    · exact (hPoint x hx).1 g
    · have hxZero : x ∉ I.zeroLocus := fun h => hx ⟨hZeroSub h,h⟩
      have hex : ∃ f : X → ℂ,I.mem x f ∧ f x ≠ 0 := by
        by_contra hnot
        push Not at hnot
        exact hxZero (fun f hf => hnot f hf)
      obtain ⟨f,hf,hfx⟩ := hex
      have hUnit := CompanionReduction.one_mem_of_apply_ne_zero hI hf hfx
      constructor
      · intro hg
        refine ⟨GermIdeal.IsCoherent.holomorphicAt_mem hI hg,?_⟩
        filter_upwards [hZ.isOpen_compl.mem_nhds hx] with y hy hyZ
        exact (hy hyZ).elim
      · intro hg
        exact HomogenizedIdeal.mem_of_isInSpanAt hI
          (isInSpanAt_of_eq_mul hUnit hg.1 hg.1 (Eventually.of_forall fun _ => by simp))


private theorem actual_residual_reduced (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) (i : Fin old.length)
    (hOrd : ∀ x ∈ N,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1) :
    IsClosedSubmanifold n (N ∩ (oldResidualPart N old born i).zeroLocus) ∧
      oldResidualPart N old born i=
        vanishingIdeal (n := n) (N ∩ (oldResidualPart N old born i).zeroLocus) := by
  have hOld := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
    (List.sublist_append_left old born)
  have hBorn := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
    (List.sublist_append_right old born)
  obtain ⟨hcI,hnzI,hcJ,hnzJ,hcD,_hnzD,_hmD,_hWhole⟩ :=
    actual_old_parts_geometry hn hN hE hTr hdense i
  apply normalized_order_le_one_reduced hN hcJ hnzJ
  · intro x hx
    obtain ⟨f,hf,hF⟩ := exists_originalMember_principal hn hOld (List.get_mem old i) x
    have hI : ∀ g,(oldTraceIdeal N old i).mem x g ↔
        HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (·=f) x g :=
      fun g => and_congr_right fun _ => restricted_span_iff_principal hf hF g
    obtain ⟨_m,c,_hm,_hmD,hcmem,_hfc,hJ⟩ :=
      exists_actual_relative_principal_residual hn hN hBorn hTr hcI hnzI hx f hf hI
    exact ⟨c,GermIdeal.IsCoherent.holomorphicAt_mem hcJ hcmem,hJ⟩
  · intro x g hg
    refine ⟨hg.1,fun a ha => ?_⟩
    apply vanishingIdeal_le_restrictOn
    refine ⟨(GermIdeal.IsCoherent.holomorphicAt_mem hcD ha).mul hg.1,?_⟩
    filter_upwards [hg.2] with y hy hyN
    rw [hy hyN,mul_zero]
  · exact fun x hx => hOrd x hx.1

private theorem normalized_transverse_trace_reduced (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hTr : IsTransverse n N [H]) :
    restrictOn n N (vanishingIdeal (n := n) H)=vanishingIdeal (n := n) (N ∩ H) := by
  obtain ⟨hcA,hnzA,hprA,hordA⟩ :=
    HironakaSharpActualFirstAmbientStrictExponent.actual_normalized_transverse_member_geometry
      hn hN hH hTr
  have hHsm : IsClosedSubmanifold n H :=
    MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  have hSet : N ∩ (restrictOn n N (vanishingIdeal (n := n) H)).zeroLocus=N ∩ H := by
    ext x
    constructor
    · rintro ⟨hxN,hxA⟩
      have hxH := (HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff hcH hxN).mp hxA
      rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsm.1] at hxH
      exact ⟨hxN,hxH⟩
    · rintro ⟨hxN,hxH⟩
      refine ⟨hxN,(HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff hcH hxN).mpr ?_⟩
      rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hHsm.1]
  obtain ⟨_hZ,hRed⟩ := normalized_order_le_one_reduced hN hcA hnzA hprA
    vanishingIdeal_le_restrictOn (fun x hx => by
      have hxNH : x ∈ N ∩ H := by rwa [hSet] at hx
      exact (hordA x hxNH).le)
  rwa [hSet] at hRed

private theorem actual_partial_flat_frame {m : ℕ} {x : X} {R : Set X} (hx : x ∈ R)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (Q : Finset (Fin n))
    (hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ R ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q)) :
    let E : List (Set U) := List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
    let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
    ∀ a : U,IsCoordinateFamilyAt n
      (fun o : Option (Fin E.length) => o.elim ((Subtype.val : U → X) ⁻¹' R) E.get)
      (fun o => o.elim Q (fun i => {p (c i)})) a := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  change ∀ a : U,IsCoordinateFamilyAt n
    (fun o : Option (Fin E.length) => o.elim ((Subtype.val : U → X) ⁻¹' R) E.get)
    (fun o => o.elim Q (fun i => {p (c i)})) a
  have hget (i : Fin E.length) : E.get i=
      if P (c i) then {a : U | flatCoord Φ (p (c i)) a.val=0} else ∅ := by
    simp only [E,List.get_eq_getElem,List.getElem_ofFn,c]
  let A : Option (Fin m) → Set X := fun o =>
    o.elim R (fun k => if P k then {y | flatCoord Φ (p k) y=0} else ∅)
  let T : Option (Fin m) → Finset (Fin n) := fun o => o.elim Q (fun k => {p k})
  intro a
  have hflat : ∀ o,x ∈ A o → ∀ {y : X},
      y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ A o ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (T o)) := by
    rintro (_ | k) hi y hy hyΦ
    · exact hR hy hyΦ
    · by_cases hk : P k
      · simp only [A,T,Option.elim,if_pos hk,Set.mem_ofPred_eq,flatCoord,
          coordSubspace,Finset.mem_singleton,forall_eq]
        rfl
      · simp only [A,Option.elim,if_neg hk,mem_empty_iff_false] at hi
  have hseen : ∀ o,a.val ∈ A o → x ∈ A o := by
    rintro (_ | k) hi
    · exact hx
    · by_cases hk : P k
      · change x ∈ if P k then {y | flatCoord Φ (p k) y=0} else ∅
        rw [if_pos hk]
        change Φ.toFun ((complexChartAt (n := n) x).val x) (p k)=0
        rw [h0]
        rfl
      · simp only [A,Option.elim,if_neg hk,mem_empty_iff_false] at hi
  have hfX := coordinateFamilyAt_of_flattening Φ hflat
    (hU a.property).1 (hU a.property).2 hseen
  have hfU := isCoordinateFamilyAt_preimage_val_iff.mpr hfX
  apply IsCoordinateFamilyAt.reindex hfU (Option.map c)
  · rintro (_ | i)
    · rfl
    · change E.get i=(Subtype.val : U → X) ⁻¹' A (some (c i))
      rw [hget]
      by_cases hi : P (c i) <;> simp only [A,Option.elim,hi,if_pos,if_neg,
        preimage_empty,not_false_eq_true]
      rfl
  · rintro (_ | i) <;> rfl


private theorem actual_partial_flat_snc {m : ℕ} {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (hinj : Set.InjOn p {k | P k}) :
    IsSNCDivisor n (List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅) := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  have hget (i : Fin E.length) : E.get i=
      if P (c i) then {a : U | flatCoord Φ (p (c i)) a.val=0} else ∅ := by
    simp only [E,List.get_eq_getElem,List.getElem_ofFn,c]
  have hP {a : U} {i : Fin E.length} (hi : a ∈ E.get i) : P (c i) := by
    rw [hget] at hi
    by_contra hnot
    simp only [if_neg hnot,mem_empty_iff_false] at hi
  refine ⟨?_,fun a => ?_⟩
  · intro H hH
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hH
    by_cases hk : P k
    · rw [if_pos hk]
      exact isClosed_actual_flat_lift Φ U hU _
    · rw [if_neg hk]
      exact isClosed_empty
  · have hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
        (complexChartAt (n := n) x).val y ∈ Φ.source →
        (y ∈ (univ : Set X) ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace ∅) := by
      intro y _hy _hyΦ
      simp [coordSubspace]
    have hf := actual_partial_flat_frame (mem_univ x) Φ h0 U hU P p ∅ hR a
    refine ⟨fun i => {p (c i)},?_,fun _ _ => Finset.card_singleton _,?_⟩
    · exact IsCoordinateFamilyAt.reindex hf some (fun _ => rfl) (fun _ => rfl)
    · intro i hi j hj he
      have hij := hinj (hP hi) (hP hj) (Finset.singleton_injective he)
      exact Fin.ext (show i.val=j.val from congrArg (fun k : Fin m => k.val) hij)

private theorem actual_partial_flat_transverse {m : ℕ} {x : X} {R : Set X}
    (hx : x ∈ R)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (Q : Finset (Fin n))
    (hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ R ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q))
    (hfree : ∀ k,P k → p k ∉ Q) :
    IsTransverse n ((Subtype.val : U → X) ⁻¹' R) (List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅) := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  intro a _ha
  refine ⟨Q,fun i => {p (c i)},actual_partial_flat_frame hx Φ h0 U hU P p Q hR a,?_⟩
  intro i hi
  have hget : E.get i=if P (c i) then {a : U | flatCoord Φ (p (c i)) a.val=0} else ∅ := by
    simp only [E,List.get_eq_getElem,List.getElem_ofFn,c]
  have hP : P (c i) := by
    change a ∈ E.get i at hi
    rw [hget] at hi
    by_contra hn
    simp only [if_neg hn,mem_empty_iff_false] at hi
  refine ⟨Finset.card_singleton _,Finset.disjoint_left.mpr ?_⟩
  intro j hj hjQ
  rw [Finset.mem_singleton.mp hj] at hjQ
  exact hfree _ hP hjQ

private theorem actual_partial_flat_normalCrossings {m : ℕ} {x : X} {R : Set X}
    (hx : x ∈ R)
    (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x))
    (h0 : Φ.toFun ((complexChartAt (n := n) x).val x) = 0)
    (U : Opens X) (hU : (U : Set X) ⊆ flatDomain Φ)
    (P : Fin m → Prop) (p : Fin m → Fin n) (Q : Finset (Fin n))
    (hR : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ R ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q)) :
    HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' R) (List.ofFn fun k =>
      if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅) := by
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (p k) a.val=0} else ∅
  let c : Fin E.length → Fin m := fun i => ⟨i.val,by simpa only [E,List.length_ofFn] using i.isLt⟩
  intro a _ha
  exact ⟨Q,fun i => {p (c i)},actual_partial_flat_frame hx Φ h0 U hU P p Q hR a,
    fun _ _ => Finset.card_singleton _⟩


private theorem exists_actual_prepared_lift_window {N : Set X} {old born : List (Set X)}
    (S : Finset (Fin born.length)) (hC : IsClosed (N ∩ memberInter born S))
    (hClosed : ∀ a,IsClosed (preparedSupport N old born a))
    {x : X} (hxN : x ∈ N) (hPrepared : IsPreparedResidualSNCAt N old born x) :
    ∃ (U : Opens X),x ∈ U ∧ ∃ (E : List (Set U))
      (e : (Fin old.length ⊕ Fin born.length) ≃ Fin E.length),
      IsSNCDivisor n E ∧ IsTransverse n ((Subtype.val : U → X) ⁻¹' N) E ∧
      HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S)) E ∧
      (∀ a,(Subtype.val : U → X) ⁻¹' preparedSupport N old born a=
        ((Subtype.val : U → X) ⁻¹' N) ∩ E.get (e a)) ∧
      ∀ i : Fin old.length,IsTransverse n
        ((Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S)) [E.get (e (Sum.inl i))] := by
  obtain ⟨Q,p,⟨Φ,_hsrc,h0,hflat⟩,hfree,hinj⟩ := hPrepared
  let C := N ∩ memberInter born S
  have hNflat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace Q) :=
    fun hy hyΦ => hflat none hxN hy hyΦ
  have hOff : ∀ᶠ y in 𝓝 x,x ∉ C → y ∉ C := by
    by_cases hxC : x ∈ C
    · exact Eventually.of_forall fun _ hnot => False.elim (hnot hxC)
    · have hh : ∀ᶠ y in 𝓝 x,y ∉ C := hC.isOpen_compl.mem_nhds hxC
      exact hh.mono fun _ hy _ => hy
  have hData : ∀ᶠ y in 𝓝 x,y ∈ flatDomain Φ ∧
      (∀ a,y ∈ preparedSupport N old born a → x ∈ preparedSupport N old born a) ∧
      (x ∉ C → y ∉ C) := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),
      eventually_incident_subset (preparedSupport N old born) hClosed x,hOff]
      with y hy hs ho
    exact ⟨hy,hs,ho⟩
  obtain ⟨W,hWsub,hWopen,hxW⟩ := mem_nhds_iff.mp hData
  let U : Opens X := ⟨W,hWopen⟩
  have hU : (U : Set X) ⊆ flatDomain Φ := fun _ hu => (hWsub hu).1
  let m := old.length+born.length
  let b : (Fin old.length ⊕ Fin born.length) ≃ Fin m := finSumFinEquiv
  let P : Fin m → Prop := fun k => x ∈ preparedSupport N old born (b.symm k)
  let q : Fin m → Fin n := fun k => p (b.symm k)
  let E : List (Set U) := List.ofFn fun k =>
    if P k then {a : U | flatCoord Φ (q k) a.val=0} else ∅
  let e : (Fin old.length ⊕ Fin born.length) ≃ Fin E.length :=
    b.trans (finCongr (by simp only [E,List.length_ofFn]))
  have hget (a : Fin old.length ⊕ Fin born.length) : E.get (e a)=
      if x ∈ preparedSupport N old born a then {u : U | flatCoord Φ (p a) u.val=0} else ∅ := by
    have he : (⟨(e a).val,by simpa only [E,List.length_ofFn] using (e a).isLt⟩ : Fin m)=b a :=
      Fin.ext rfl
    simp only [E,List.get_eq_getElem,List.getElem_ofFn]
    rw [he]
    simp only [P,q,Equiv.symm_apply_apply]
  have hEinj : Set.InjOn q {k | P k} := by
    intro i hi j hj he
    exact b.symm.injective (hinj hi hj he)
  have hE : IsSNCDivisor n E := actual_partial_flat_snc Φ h0 U hU P q hEinj
  have hT : IsTransverse n ((Subtype.val : U → X) ⁻¹' N) E :=
    actual_partial_flat_transverse hxN Φ h0 U hU P q Q hNflat (fun k hk => hfree _ hk)
  have hTrace (a : Fin old.length ⊕ Fin born.length) :
      (Subtype.val : U → X) ⁻¹' preparedSupport N old born a=
        ((Subtype.val : U → X) ⁻¹' N) ∩ E.get (e a) := by
    ext u
    rw [hget]
    by_cases ha : x ∈ preparedSupport N old born a
    · rw [if_pos ha]
      change u.val ∈ preparedSupport N old born a ↔ u.val ∈ N ∧
        Φ.toFun ((complexChartAt (n := n) x).val u.val) (p a)=0
      have hZa : u.val ∈ preparedSupport N old born a ↔
          Φ.toFun ((complexChartAt (n := n) x).val u.val) ∈ coordSubspace (Q ∪ {p a}) :=
        hflat (some a) ha (hU u.property).1 (hU u.property).2
      rw [hZa,ExceptionalPushforwardAlong.coordSubspace_union,Set.mem_inter_iff,
        BlowupSNCTransform.mem_coordSubspace_singleton]
      change (Φ.toFun ((complexChartAt (n := n) x).val u.val) ∈ coordSubspace Q ∧
        Φ.toFun ((complexChartAt (n := n) x).val u.val) (p a)=0) ↔ _
      exact and_congr (hNflat (hU u.property).1 (hU u.property).2).symm Iff.rfl
    · rw [if_neg ha]
      change u.val ∈ preparedSupport N old born a ↔ u.val ∈ N ∧ u ∈ (∅ : Set U)
      simp only [mem_empty_iff_false,and_false,iff_false]
      exact fun hu => ha ((hWsub u.property).2.1 a hu)
  refine ⟨U,hxW,E,e,hE,hT,?_,hTrace,?_⟩
  · by_cases hxC : x ∈ C
    · let QC : Finset (Fin n) := Q ∪ S.image (fun j => p (Sum.inr j))
      have hCflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QC) := by
        intro y hy hyΦ
        constructor
        · intro hyC r hr
          rcases Finset.mem_union.mp hr with hr | hr
          · exact ((hNflat hy hyΦ).mp hyC.1) r hr
          · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
            have hjx : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hxC.1,hxC.2 j hj⟩
            exact ((hflat (some (Sum.inr j)) hjx hy hyΦ).mp ⟨hyC.1,hyC.2 j hj⟩)
              _ (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _)))
        · intro hyQ
          have hyN : y ∈ N := (hNflat hy hyΦ).mpr fun r hr =>
            hyQ r (Finset.mem_union.mpr (Or.inl hr))
          refine ⟨hyN,fun j hj => ?_⟩
          have hjx : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hxC.1,hxC.2 j hj⟩
          have hyBj : y ∈ preparedSupport N old born (Sum.inr j) := by
            apply (hflat (some (Sum.inr j)) hjx hy hyΦ).mpr
            intro r hr
            rcases Finset.mem_union.mp hr with hr | hr
            · exact hyQ r (Finset.mem_union.mpr (Or.inl hr))
            · rw [Finset.mem_singleton.mp hr]
              exact hyQ _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)))
          exact hyBj.2
      exact actual_partial_flat_normalCrossings hxC Φ h0 U hU P q QC hCflat
    · intro u hu
      exact False.elim ((hWsub u.property).2.2 hxC hu)
  · intro i
    by_cases hxC : x ∈ C
    · let QC : Finset (Fin n) := Q ∪ S.image (fun j => p (Sum.inr j))
      have hCflat : ∀ {y : X},y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ C ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace QC) := by
        intro y hy hyΦ
        constructor
        · intro hyC r hr
          rcases Finset.mem_union.mp hr with hr | hr
          · exact ((hNflat hy hyΦ).mp hyC.1) r hr
          · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hr
            have hjx : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hxC.1,hxC.2 j hj⟩
            exact ((hflat (some (Sum.inr j)) hjx hy hyΦ).mp ⟨hyC.1,hyC.2 j hj⟩)
              _ (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _)))
        · intro hyQ
          have hyN : y ∈ N := (hNflat hy hyΦ).mpr fun r hr =>
            hyQ r (Finset.mem_union.mpr (Or.inl hr))
          refine ⟨hyN,fun j hj => ?_⟩
          have hjx : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hxC.1,hxC.2 j hj⟩
          have hyBj : y ∈ preparedSupport N old born (Sum.inr j) := by
            apply (hflat (some (Sum.inr j)) hjx hy hyΦ).mpr
            intro r hr
            rcases Finset.mem_union.mp hr with hr | hr
            · exact hyQ r (Finset.mem_union.mpr (Or.inl hr))
            · rw [Finset.mem_singleton.mp hr]
              exact hyQ _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)))
          exact hyBj.2
      have hF : x ∈ preparedSupport N old born (Sum.inl i) → p (Sum.inl i) ∉ QC := by
        intro hi hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact hfree _ hi hr
        · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hr
          have hjx : x ∈ preparedSupport N old born (Sum.inr j) := ⟨hxC.1,hxC.2 j hj⟩
          have heq := hinj hjx hi he
          cases heq
      rw [hget]
      simpa only [List.ofFn_succ,List.ofFn_zero] using
        (actual_partial_flat_transverse hxC Φ h0 U hU
          (fun _ : Fin 1 => x ∈ preparedSupport N old born (Sum.inl i))
          (fun _ : Fin 1 => p (Sum.inl i)) QC hCflat (fun _ hi => hF hi))
    · intro u hu
      exact False.elim ((hWsub u.property).2.2 hxC hu)


private theorem actual_vanishingIdeal_open (Z : Set X)
    (hZ : IsClosedSubmanifold n Z) (U : Opens X) :
    GermIdeal.pullback (m := n) (Subtype.val : U → X) (vanishingIdeal (n := n) Z)=
      vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' Z) := by
  have hZU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hZ U
  have h := BlowupRestrictOpen.pullback_vanishingIdeal_opens (n := n) (m := n) U (id : U → U) Z
  rw [BlowupControlledTransform.pullback_id
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hZU)] at h
  exact h.symm

private theorem actual_total_open_lift_dictionary (hn : 0 < n) {N C : Set X}
    {I : GermIdeal n X} (hN : IsClosedSubmanifold n N) (hI : I.IsCoherent)
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCN : C ⊆ N)
    (U : Opens X) (H : Set U) (hH : IsSNCDivisor n [H])
    (hCT : IsTransverse n ((Subtype.val : U → X) ⁻¹' C) [H])
    (hSource : GermIdeal.pullback (m := n) (Subtype.val : U → X) I=
      restrictOn n ((Subtype.val : U → X) ⁻¹' N) (vanishingIdeal (n := n) H)) :
    let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V → U := fun z => ⟨π z,z.property⟩
    let CU := (Subtype.val : U → X) ⁻¹' C
    let NU := (Subtype.val : U → X) ⁻¹' N
    GermIdeal.pullback (m := n) (Subtype.val : V → Y) (nextTotalMarked N I C π).ideal=
      restrictOn n (geoStrictTransform ρ CU NU)
        (vanishingIdeal (n := n) (geoStrictTransform ρ CU H)) := by
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun z => ⟨π z,z.property⟩
  let CU := (Subtype.val : U → X) ⁻¹' C
  let NU := (Subtype.val : U → X) ⁻¹' N
  have hρ : IsBlowupAlong n CU ρ := BlowupRestrictOpen.isBlowupAlong_restrict hπ U V.isOpen
  have hNU : IsClosedSubmanifold n NU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hCU : CU ⊆ NU := fun _ hy => hCN hy
  have hNU' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hρ hNU hCU
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hRaw := HironakaSharpActualRawMemberOpenStrict.actual_raw_total_whole_open_pullback hN hI hπ hCN U
  have hTotal : (nextTotalMarked N I C π).ideal=
      restrictOn n (geoStrictTransform π C N) (GermIdeal.pullback (m := n) π I) :=
    HironakaSharpOriginalFirstMemberExceptionalFactor.geoTransform_zeroMark_ideal_eq_restricted_total
      (⟨N,[],I,0⟩ : MarkedIdeals.MarkedIdeal n X) rfl C π
  change GermIdeal.pullback (m := n) (Subtype.val : V → Y) (nextTotalMarked N I C π).ideal=_
  rw [hTotal,←hRaw,hSource]
  change restrictOn n (geoStrictTransform ρ CU NU)
    (GermIdeal.pullback (m := n) ρ (restrictOn n NU (vanishingIdeal (n := n) H)))=_
  have hNorm := HironakaSharpActualCompositeTotalResidual.actual_normalized_pullback_restrictOn
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) (N := NU)
    (W := geoStrictTransform ρ CU NU) (I := vanishingIdeal (n := n) H) (f := ρ)
    hNU hNU'.1 (VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm) hρ.contMDiff
    (fun _ hy => geoStrictTransform_subset_preimage hρ.contMDiff.continuous hNU.1 hy)
  rw [hNorm,HironakaG4TransverseBoundaryStrictPullback.pullback_vanishingIdeal_eq_strict_of_transverse
    (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) V) hn hH hCT hρ]

private theorem normalized_transverse_trace_order_le_one (hn : 0 < n) {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsSNCDivisor n [H])
    (hTr : IsTransverse n N [H]) :
    ∀ x ∈ N,ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) H)) x ≤ 1 := by
  obtain ⟨hcA,hnzA,_hprA,hordA⟩ :=
    HironakaSharpActualFirstAmbientStrictExponent.actual_normalized_transverse_member_geometry
      hn hN hH hTr
  have hHsm : IsClosedSubmanifold n H := MonomialPart.isClosedSubmanifold_get hn hH (0 : Fin [H].length)
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hHsm
  intro x hxN
  by_cases hxH : x ∈ H
  · exact (hordA x ⟨hxN,hxH⟩).le
  · have hUnitH : (vanishingIdeal (n := n) H).mem x (1 : X → ℂ) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      filter_upwards [hHsm.1.isOpen_compl.mem_nhds hxH] with y hy hyH
      exact (hy hyH).elim
    have hUnit := le_restrictOn (W := N) hcH x (1 : X → ℂ) hUnitH
    by_contra hgt
    have hCos := (ordinaryTraceOrder_cosupport_iff hN hcA hnzA hxN 1).mpr (by omega)
    have hOne := (vanishesToOrderOn_one_iff hxN (holomorphicAt_const 1)).mp (hCos.2 1 hUnit)
    exact one_ne_zero hOne


private def append_label_equiv {a b m : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin m) :
    (Fin a ⊕ Fin (b+1)) ≃ Fin (m+1) :=
  ((Equiv.sumCongr (Equiv.refl (Fin a)) finSumFinEquiv.symm).trans
    (Equiv.sumAssoc (Fin a) (Fin b) (Fin 1)).symm).trans
    ((Equiv.sumCongr e (Equiv.refl (Fin 1))).trans finSumFinEquiv)

private theorem append_label_equiv_old {a b m : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin m) (i : Fin a) :
    append_label_equiv e (Sum.inl i)=(e (Sum.inl i)).castAdd 1 := rfl

private theorem append_label_equiv_born {a b m : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin m) (j : Fin b) :
    append_label_equiv e (Sum.inr (j.castAdd 1))=(e (Sum.inr j)).castAdd 1 := by
  simp [append_label_equiv]

private theorem append_label_equiv_newborn {a b m : ℕ} (e : (Fin a ⊕ Fin b) ≃ Fin m) :
    append_label_equiv e (Sum.inr (Fin.last b))=Fin.last m := by
  apply Fin.ext
  simp [append_label_equiv]


theorem actual_selected_born_total_prepared (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hOrd : ∀ x ∈ N,∀ i : Fin old.length,
      ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (π : Y → X) (hπ : IsBlowupAlong n (N ∩ memberInter born S) π) :
    let C := N ∩ memberInter born S
    let N' := geoStrictTransform π C N
    let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    let T : Fin old.length → GermIdeal n Y := fun i =>
      (nextTotalMarked N (oldResidualPart N old born i) C π).ideal
    let Z : Fin old.length ⊕ Fin born'.length → Set Y :=
      Sum.elim (fun i => N' ∩ (T i).zeroLocus) (fun j => N' ∩ born'.get j)
    ∀ z ∈ N', (∀ i,ordinaryTraceOrder N' (T i) z ≤ 1) ∧
      ∃ (Q : Finset (Fin n)) (p : Fin old.length ⊕ Fin born'.length → Fin n),
        IsCoordinateFamilyAt n
          (fun o : Option (Fin old.length ⊕ Fin born'.length) => o.elim N' Z)
          (fun o => o.elim Q (fun a => Q ∪ {p a})) z ∧
        (∀ a,z ∈ Z a → p a ∉ Q) ∧ Set.InjOn p {a | z ∈ Z a} := by
  let C := N ∩ memberInter born S
  let N' := geoStrictTransform π C N
  let born' := born.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  let T : Fin old.length → GermIdeal n Y := fun i =>
    (nextTotalMarked N (oldResidualPart N old born i) C π).ideal
  let Z : Fin old.length ⊕ Fin born'.length → Set Y :=
    Sum.elim (fun i => N' ∩ (T i).zeroLocus) (fun j => N' ∩ born'.get j)
  change ∀ z ∈ N',(∀ i,ordinaryTraceOrder N' (T i) z ≤ 1) ∧ _
  have hCN : C ⊆ N := inter_subset_left
  have hN' : IsClosedSubmanifold n N' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hBorn := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
    (List.sublist_append_right old born)
  have hPackets := (prepared_residual_total_no_member_factor hn hN hE hTr hdense S hS
    (fun x hx => hOrd x hx.1) (fun x hx => hPrepared x hx.1)).2.2 π hπ
  have hReduced (i : Fin old.length) := actual_residual_reduced hn hN hE hTr hdense i
    (fun x hx => hOrd x hx i)
  have hClosed : ∀ a,IsClosed (preparedSupport N old born a) := by
    rintro (i | j)
    · exact (hReduced i).1.1
    · exact hN.1.inter (hBorn.1 _ (List.get_mem born j))
  intro z hz
  have hxN : π z ∈ N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
  obtain ⟨U,hxU,E,e,hEU,hTU,hCU,hTrace,hCT⟩ :=
    exists_actual_prepared_lift_window S hπ.1.1 hClosed hxN (hPrepared _ hxN)
  let V : Opens Y := ⟨π ⁻¹' (U : Set X),U.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V → U := fun u => ⟨π u,u.property⟩
  let CU := (Subtype.val : U → X) ⁻¹' C
  let NU := (Subtype.val : U → X) ⁻¹' N
  let NU' := geoStrictTransform ρ CU NU
  let E' := E.map (geoStrictTransform ρ CU) ++ [ρ ⁻¹' CU]
  let zv : V := ⟨z,hxU⟩
  have hρ : IsBlowupAlong n CU ρ := BlowupRestrictOpen.isBlowupAlong_restrict hπ U V.isOpen
  have hNU : IsClosedSubmanifold n NU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hCUN : CU ⊆ NU := fun _ hu => hu.1
  have hNU' : IsClosedSubmanifold n NU' :=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hρ hNU hCUN
  have hStrictN : NU'=(Subtype.val : V → Y) ⁻¹' N' :=
    MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen N
  have hzv : zv ∈ NU' := by rw [hStrictN]; exact hz
  have hEachE (k : Fin E.length) : IsSNCDivisor n [E.get k] :=
    NormalCrossingsComparison.isSNCDivisor_of_sublist hEU (by simp)
  have hEachT (k : Fin E.length) : IsTransverse n NU [E.get k] :=
    NormalCrossingsComparison.isTransverse_of_forall_mem hTU (by simp)
  have hSource (i : Fin old.length) :
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i)=
        restrictOn n NU (vanishingIdeal (n := n) (E.get (e (Sum.inl i)))) := by
    rw [(hReduced i).2,actual_vanishingIdeal_open _ (hReduced i).1 U]
    change vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹'
      preparedSupport N old born (Sum.inl i))=_
    rw [hTrace]
    exact (normalized_transverse_trace_reduced (X := CMfd.of (n := n) U) hn hNU
      (hEachE _) (hEachT _)).symm
  have hTotals (i : Fin old.length) :
      GermIdeal.pullback (m := n) (Subtype.val : V → Y) (T i)=
        restrictOn n NU' (vanishingIdeal (n := n)
          (geoStrictTransform ρ CU (E.get (e (Sum.inl i))))) := by
    have hcJ := (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.1
    exact actual_total_open_lift_dictionary hn hN hcJ hπ hCN U _ (hEachE _) (hCT i) (hSource i)
  have hE' : IsSNCDivisor n E' :=
    SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hρ hEU hCU
  have hT' : IsTransverse n NU' E' :=
    SimultaneousNormalCrossings.isTransverse_geoTransformE_of_hasNormalCrossings hρ hNU.1 hCUN hEU hTU hCU
  let t : Fin E.length → Fin E'.length := fun k => ⟨k.val,by
    simp only [E',List.length_append,List.length_map,List.length_singleton]
    omega⟩
  let nb : Fin E'.length := ⟨E.length,by
    simp only [E',List.length_append,List.length_map,List.length_singleton]
    omega⟩
  have hGetStrict (k : Fin E.length) : E'.get (t k)=geoStrictTransform ρ CU (E.get k) := by
    have hh := BlowupSNCTransform.get_map_append_singleton E (geoStrictTransform ρ CU) (ρ ⁻¹' CU) (t k)
    rw [dif_pos k.isLt] at hh
    exact hh
  have hGetNew : E'.get nb=ρ ⁻¹' CU := by
    have hh := BlowupSNCTransform.get_map_append_singleton E (geoStrictTransform ρ CU) (ρ ⁻¹' CU) nb
    rw [dif_neg (Nat.lt_irrefl E.length)] at hh
    exact hh
  have hEachE' (k : Fin E.length) : IsSNCDivisor n [geoStrictTransform ρ CU (E.get k)] := by
    rw [←hGetStrict]
    exact NormalCrossingsComparison.isSNCDivisor_of_sublist hE' (by simp)
  have hEachT' (k : Fin E.length) : IsTransverse n NU' [geoStrictTransform ρ CU (E.get k)] := by
    rw [←hGetStrict]
    exact NormalCrossingsComparison.isTransverse_of_forall_mem hT' (by simp)
  have hOldTraces (i : Fin old.length) :
      (Subtype.val : V → Y) ⁻¹' (N' ∩ (T i).zeroLocus)=
        NU' ∩ geoStrictTransform ρ CU (E.get (e (Sum.inl i))) := by
    have hIdeal := (hTotals i).trans
      (normalized_transverse_trace_reduced (X := CMfd.of (n := n) V) hn hNU' (hEachE' _) (hEachT' _))
    have hHclosed := hE'.1 _ (List.get_mem E' (t (e (Sum.inl i))))
    rw [hGetStrict] at hHclosed
    have hZero : (Subtype.val : V → Y) ⁻¹' (T i).zeroLocus=
        NU' ∩ geoStrictTransform ρ CU (E.get (e (Sum.inl i))) := by
      rw [←BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val (hPackets i).1,
        hIdeal,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hNU'.1.inter hHclosed)]
    rw [preimage_inter,hZero,←hStrictN,←inter_assoc,inter_self]
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let eb : Fin born.length ≃ Fin bornU.length := finCongr (by simp only [bornU,List.length_map])
  have hBornU : IsSNCDivisor n bornU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hBorn
  have hTBornU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hCBornU : HasNormalCrossings n CU bornU :=
    hasNormalCrossings_preimage (pullsBackCoordinates_val U) (MemberInterAlong.hasNormalCrossings_inter_memberInter hTr S)
  have hGetBornU (j : Fin born.length) : bornU.get (eb j)=(Subtype.val : U → X) ⁻¹' born.get j := by
    simp only [bornU,List.get_eq_getElem,List.getElem_map,eb,finCongr_apply]
    rfl
  have hBornTraces (j : Fin born.length) :
      (Subtype.val : V → Y) ⁻¹' (N' ∩ geoStrictTransform π C (born.get j))=
        NU' ∩ geoStrictTransform ρ CU (E.get (e (Sum.inr j))) := by
    have hInit : bornU.get (eb j) ∩ NU=E.get (e (Sum.inr j)) ∩ NU := by
      rw [hGetBornU,inter_comm _ NU,inter_comm (E.get _) NU]
      exact hTrace (Sum.inr j)
    have hBoth := congrArg (geoStrictTransform ρ CU) hInit
    rw [ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hρ hNU.1 hCUN
        hBornU hTBornU hCBornU (eb j),
      ExceptionalPushforwardAlong.geoStrictTransform_inter_eq hρ hNU.1 hCUN
        hEU hTU hCU (e (Sum.inr j)),hGetBornU,
      MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen (born.get j)] at hBoth
    rw [preimage_inter,←hStrictN,inter_comm, hBoth,inter_comm]
  let eb' : Fin born'.length ≃ Fin (born.length+1) :=
    finCongr (by simp only [born',List.length_append,List.length_map,List.length_singleton])
  let f : (Fin old.length ⊕ Fin born'.length) ≃ Fin E'.length :=
    ((Equiv.sumCongr (Equiv.refl (Fin old.length)) eb').trans (append_label_equiv e)).trans
      (finCongr (by simp only [E',List.length_append,List.length_map,List.length_singleton]))
  have hFOld (i : Fin old.length) : f (Sum.inl i)=t (e (Sum.inl i)) := Fin.ext rfl
  have hLabel (a : Fin old.length ⊕ Fin born'.length) :
      (Subtype.val : V → Y) ⁻¹' Z a=NU' ∩ E'.get (f a) := by
    cases a with
    | inl i => rw [hFOld,hGetStrict]; exact hOldTraces i
    | inr j =>
      have hget := BlowupSNCTransform.get_map_append_singleton born (geoStrictTransform π C) (π ⁻¹' C) j
      by_cases hj : j.val<born.length
      · let j0 : Fin born.length := ⟨j.val,hj⟩
        have hej : eb' j=j0.castAdd 1 := Fin.ext rfl
        have hfj : f (Sum.inr j)=t (e (Sum.inr j0)) := by
          apply Fin.ext
          change (append_label_equiv e (Sum.inr (eb' j))).val=(e (Sum.inr j0)).val
          rw [hej,append_label_equiv_born]
          rfl
        rw [dif_pos hj] at hget
        change (Subtype.val : V → Y) ⁻¹' (N' ∩ born'.get j)=_
        rw [hget,hfj,hGetStrict]
        exact hBornTraces j0
      · have hjval : j.val=born.length := by
          have hjlt := j.isLt
          simp only [born',List.length_append,List.length_map,List.length_singleton] at hjlt
          omega
        have hej : eb' j=Fin.last born.length := Fin.ext hjval
        have hfj : f (Sum.inr j)=nb := by
          apply Fin.ext
          change (append_label_equiv e (Sum.inr (eb' j))).val=E.length
          rw [hej,append_label_equiv_newborn]
          rfl
        rw [dif_neg hj] at hget
        change (Subtype.val : V → Y) ⁻¹' (N' ∩ born'.get j)=_
        rw [hget,hfj,hGetNew,preimage_inter,←hStrictN]
        rfl
  refine ⟨?_,?_⟩
  · intro i
    have hOrdLocal := normalized_transverse_trace_order_le_one (X := CMfd.of (n := n) V)
      hn hNU' (hEachE' (e (Sum.inl i))) (hEachT' _) zv hzv
    rw [←hTotals] at hOrdLocal
    have hOrdOpen := HironakaSharpActualMixedCurveContactEvolution.actual_ordinary_trace_order_pullback_open
      hn hN' (hPackets i).1 (hPackets i).2.1 V zv
    rw [←hStrictN] at hOrdOpen
    exact hOrdOpen ▸ hOrdLocal
  · obtain ⟨Q,s,hFrame,hFree,hInj⟩ := actual_trace_family_frame
      (X := CMfd.of (n := n) V) hn hE' hT' hzv
    let p' : Fin old.length ⊕ Fin born'.length → Fin n := fun a => s (f a)
    have hFamilyV : IsCoordinateFamilyAt n
        (fun o : Option (Fin old.length ⊕ Fin born'.length) =>
          (Subtype.val : V → Y) ⁻¹' o.elim N' Z)
        (fun o => o.elim Q (fun a => Q ∪ {p' a})) zv := by
      apply IsCoordinateFamilyAt.reindex hFrame (Option.map f)
      · rintro (_ | a)
        · exact hStrictN.symm
        · exact hLabel a
      · rintro (_ | a) <;> rfl
    refine ⟨Q,p',isCoordinateFamilyAt_preimage_val_iff.mp hFamilyV,?_,?_⟩
    · intro a ha
      have hInc : zv ∈ NU' ∩ E'.get (f a) := by rw [←hLabel]; exact ha
      exact hFree _ hInc
    · intro a ha b hb he
      have hIa : zv ∈ NU' ∩ E'.get (f a) := by rw [←hLabel]; exact ha
      have hIb : zv ∈ NU' ∩ E'.get (f b) := by rw [←hLabel]; exact hb
      exact f.injective (hInj hIa hIb he)

end
end Hironaka.HironakaG4PreparedResidualPreservation
