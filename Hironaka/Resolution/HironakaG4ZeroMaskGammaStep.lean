import Hironaka.Resolution.HironakaG4PreparedMixedSelectedStep
import Hironaka.Resolution.HironakaG4PreparedResidualPreservation
import Hironaka.Resolution.HironakaG3PreparedMixedGivenBlowup
import Hironaka.Resolution.HironakaG4ZeroResidualTopTransform
import Hironaka.Analytic.MonomialCaseLocal
import Hironaka.Resolution.HironakaG4MonomialRowChain

/-! The actual global gamma maximum step for a fixed nonempty original mask.
Complete approved source-first proof: hironaka-g4-zero-mask-gamma-step.tex.
Current actual SUM monomiality is a genuine state hypothesis. No future
prepared configuration, canonical dictionary or resolving history is supplied. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4ZeroMaskGammaStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupStrictSubmanifold NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  MonomialPartAlong MonomialPartEtale DivisorExponentAlong GermIdealOrder
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4MonomialMaximalContact HironakaG4MonomialTopStratum HironakaG4MonomialRowChain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep
  MonomialCaseAlong MonomialStepAlong MonomialCase IdealWeightPowers BoundaryCount
  NonmonomialTransformAlong HironakaSharpActualChronologicalResidualDictionary
  HironakaSharpActualControlledRelativeSaturation HironakaSharpActualFiniteChronologicalHistory

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem transformFamily_uniform_bound {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (S R : Finset (Fin b)) (m B : ℕ) (hB : ∀ i j,A i j ≤ B) :
    ∀ i j,transformFamily m S R A i j ≤ max B (b * B) := by
  intro i j
  have hs : rowWeight (A i) S ≤ b * B := by
    unfold rowWeight
    calc
      ∑ j ∈ S,A i j ≤ ∑ _j ∈ S,B := Finset.sum_le_sum fun j _ => hB i j
      _ = S.card * B := by simp
      _ ≤ b * B := Nat.mul_le_mul_right B (by simpa using Finset.card_le_univ S)
  induction j using Fin.lastCases with
  | last =>
      simp only [transformFamily,transformRow,Fin.lastCases_last]
      exact (Nat.sub_le _ _).trans (hs.trans (le_max_right _ _))
  | cast j =>
      simp only [transformFamily,transformRow,Fin.lastCases_castSucc]
      split
      · exact (hB i j).trans (le_max_left _ _)
      · exact Nat.zero_le _

private theorem appendAbsentFamily_uniform_bound {ι : Type} {b : ℕ} (A : ι → Fin b → ℕ)
    (B : ℕ) (hB : ∀ i j,A i j ≤ B) : ∀ i j,appendAbsentFamily A i j ≤ B := by
  intro i j
  induction j using Fin.lastCases with
  | last => simp [appendAbsentFamily,appendAbsentRow]
  | cast j => simpa [appendAbsentFamily,appendAbsentRow] using hB i j

private def maskSum {ι : Type*} (D : ι → GermIdeal n X) (P : Finset ι) : GermIdeal n X :=
  ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩

private theorem le_maskSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) {P : Finset ι} {i : ι} (hi : i ∈ P) :
    (D i).Le (maskSum D P) := by
  intro x g hg
  change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x g
  exact InvertibleIdealQuotient.isInSpanAt_self ⟨i,hi,hg⟩ (GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)

private theorem maskSum_insert {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) (i : ι) :
    maskSum D (insert i P)=sumIdeal (D i) (maskSum D P) := by
  ext x g
  change IsInSpanAt (n := n) (fun f => ∃ j ∈ insert i P,(D j).mem x f) x g ↔
    IsInSpanAt (n := n) (fun f => (D i).mem x f ∨ (maskSum D P).mem x f) x g
  constructor
  · intro hg
    apply IsInSpanAt.mono ?_ hg
    rintro f ⟨j,hj,hf⟩
    rcases Finset.mem_insert.mp hj with hji | hj
    · exact Or.inl (hji ▸ hf)
    · exact Or.inr (le_maskSum D hc hj x f hf)
  · intro hg
    apply IsInSpanAt.trans ?_ hg
    rintro f (hf | hf)
    · exact le_maskSum D hc (Finset.mem_insert_self i P) x f hf
    · change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x f at hf
      exact hf.mono (fun _ ⟨j,hj,hg⟩ => ⟨j,Finset.mem_insert_of_mem hj,hg⟩)

private theorem coherent_maskSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) : (maskSum D P).IsCoherent := by
  induction P using Finset.induction_on with
  | empty =>
    intro x
    refine ⟨univ,isOpen_univ,mem_univ x,0,Fin.elim0,fun i => i.elim0,?_⟩
    intro y _hy g
    change IsInSpanAt (n := n) (fun f => ∃ i ∈ (∅ : Finset ι),(D i).mem y f) y g ↔ _
    constructor
    · exact IsInSpanAt.mono (fun _ ⟨i,hi,_⟩ => (Finset.notMem_empty i hi).elim)
    · exact IsInSpanAt.mono (fun _ ⟨i,_⟩ => i.elim0)
  | insert i P _hi ih =>
    rw [maskSum_insert D hc P i]
    exact isCoherent_sumIdeal (hc i) ih

private theorem nonzero_maskSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) {P : Finset ι} (hP : P.Nonempty)
    {N : Set X} (hne : ∀ i,∀ x ∈ N,IsNonzeroAlongAt N (D i) x) :
    ∀ x ∈ N,IsNonzeroAlongAt N (maskSum D P) x := by
  intro x hx
  obtain ⟨i,hi⟩ := hP
  obtain ⟨g,hg,hfreq⟩ := hne i x hx
  exact ⟨g,le_maskSum D hc hi x g hg,hfreq⟩

private theorem cosupport_maskSum_one {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) (N : Set X) (x : X) :
    x ∈ cosupport n N (maskSum D P) 1 ↔
      x ∈ N ∧ ∀ i ∈ P,x ∈ cosupport n N (D i) 1 := by
  have hi (i : ι) : x ∈ cosupport n N (D i) 1 ↔
      x ∈ N ∧ ∀ g,(D i).mem x g → g x=0 := by
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)]
    rfl
  rw [cosupport_one (𝔞 := maskSum D P) (fun _ _ hg => hg.1)]
  constructor
  · rintro ⟨hxN,hx⟩
    exact ⟨hxN,fun i hPi => (hi i).mpr ⟨hxN,fun g hg => hx g (le_maskSum D hc hPi x g hg)⟩⟩
  · rintro ⟨hxN,hx⟩
    refine ⟨hxN,?_⟩
    intro g hg
    obtain ⟨_hg,K,s,a,hs,_ha,hEq⟩ := hg
    rw [hEq.self_of_nhds]
    apply Finset.sum_eq_zero
    intro k _hk
    obtain ⟨i,hPi,hsi⟩ := hs k
    rw [((hi i).mp (hx i hPi)).2 _ hsi,mul_zero]

private theorem carrierIdeal_le_monomialPart (N : Set X) (I : GermIdeal n X)
    (E : List (Set X)) : (vanishingIdeal (n := n) N).Le (monomialPartAlong n N I E) := by
  intro x g hg
  refine ⟨hg.1,fun _i _hxN _hxi => ?_⟩
  refine ⟨0,Fin.elim0,Fin.elim0,fun i => i.elim0,fun i => i.elim0,?_⟩
  filter_upwards [hg.2] with y hy hyN
  simpa using hy hyN

private theorem maskSum_normalized {ι : Type*} {N : Set X} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (hNormal : ∀ i,(vanishingIdeal (n := n) N).Le (D i))
    {P : Finset ι} (hP : P.Nonempty) : restrictOn n N (maskSum D P)=maskSum D P := by
  have hSumCoherent := coherent_maskSum D hc P
  obtain ⟨i,hi⟩ := hP
  have hLe : (vanishingIdeal (n := n) N).Le (maskSum D P) :=
    fun x g hg => le_maskSum D hc hi x g (hNormal i x g hg)
  rw [restrictOn_eq_sum_vanishingIdeal hSumCoherent]
  ext x g
  constructor
  · intro hg
    change IsInSpanAt (n := n) (fun f => (maskSum D P).mem x f ∨
      (vanishingIdeal (n := n) N).mem x f) x g at hg
    exact HomogenizedIdeal.mem_of_isInSpanAt hSumCoherent
      (hg.mono fun f hf => hf.elim id (hLe x f))
  · exact le_sumIdeal_left hSumCoherent x g

private theorem maskSum_singleton {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (i : ι) : maskSum D {i}=D i := by
  ext x g
  constructor
  · intro hg
    change IsInSpanAt (n := n) (fun f => ∃ j ∈ ({i} : Finset ι),(D j).mem x f) x g at hg
    exact HomogenizedIdeal.mem_of_isInSpanAt (hc i)
      (hg.mono fun _ ⟨j,hj,hf⟩ => (Finset.mem_singleton.mp hj) ▸ hf)
  · exact le_maskSum D hc (Finset.mem_singleton_self i) x g

private theorem idealPow_one_coherent (I : GermIdeal n X) (hc : I.IsCoherent) :
    idealPow I 1=I := by
  rw [idealPow_succ,idealPow_zero,RestrictLeCalculus.mul_comm',RestrictLeCalculus.mul_unitIdeal hc]

private theorem normalized_geoTransform (M : MarkedIdeal n X) (C : Set X) (β : Y → X) :
    restrictOn n (geoStrictTransform β C M.N) (M.geoTransform C β).ideal =
      (M.geoTransform C β).ideal := by
  ext z g
  exact restrictOn_colonAlong_mem_iff _ _ _
    (fun _ hg => GermIdealOrder.holomorphicAt_of_mem_idealPow hg) g

private theorem maskSum_controlled {ι : Type*} {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) {β : Y → X} (D : ι → GermIdeal n X) (G : ι → GermIdeal n Y)
    (hc : ∀ i,(D i).IsCoherent) (hcG : ∀ i,(G i).IsCoherent)
    (hNormG : ∀ i,(vanishingIdeal (n := n) (geoStrictTransform β C N)).Le (G i))
    (hβ : IsBlowupAlong n C β) (P : Finset ι) :
    P.Nonempty →
    (∀ i ∈ P,(⟨N,E,D i,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C) →
    (∀ i ∈ P,G i=((⟨N,E,D i,1⟩ : MarkedIdeal n X).geoTransform C β).ideal) →
    maskSum G P=((⟨N,E,maskSum D P,1⟩ : MarkedIdeal n X).geoTransform C β).ideal := by
  classical
  induction P using Finset.induction_on with
  | empty => intro hP; exact (Finset.not_nonempty_empty hP).elim
  | insert i P hi ih =>
    intro hP hC hG
    have hCi := hC i (Finset.mem_insert_self i P)
    have hGi := hG i (Finset.mem_insert_self i P)
    by_cases hPe : P.Nonempty
    · have hCP : ∀ j ∈ P,(⟨N,E,D j,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C :=
        fun j hj => hC j (Finset.mem_insert_of_mem hj)
      have hGP := ih hPe hCP (fun j hj => hG j (Finset.mem_insert_of_mem hj))
      have hCPsum : (⟨N,E,maskSum D P,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
        refine ⟨hCi.1,?_,hCi.2.2⟩
        intro x hx
        exact (cosupport_maskSum_one D hc P N x).mpr
          ⟨(hCi.2.1 hx).1,fun j hj => (hCP j hj).2.1 hx⟩
      have hcP := coherent_maskSum D hc P
      have hPair : IsSubmanifoldPair (⟨N,E,D i,1⟩ : MarkedIdeal n X)
          (⟨N,E,maskSum D P,1⟩ : MarkedIdeal n X) := ⟨rfl,rfl,hN,hc i,hcP⟩
      have hAdd := geoTransform_add_restrictEquiv hPair hβ hCi hCPsum
      have hcGi : (((⟨N,E,D i,1⟩ : MarkedIdeal n X).geoTransform C β).ideal).IsCoherent :=
        hGi ▸ hcG i
      have hcGP : (((⟨N,E,maskSum D P,1⟩ : MarkedIdeal n X).geoTransform C β).ideal).IsCoherent :=
        hGP ▸ coherent_maskSum G hcG P
      simp only [MarkedIdealOperationsTransform.MarkedIdeal.add,geoTransform_d,
        idealPow_one_coherent _ (hc i),idealPow_one_coherent _ hcP,
        idealPow_one_coherent _ hcGi,idealPow_one_coherent _ hcGP,Nat.mul_one] at hAdd
      have hEq := restrictOn_eq_of_restrictLe isClosed_closure hAdd.le hAdd.ge
      rw [←hGi,←hGP,←maskSum_insert G hcG P i,←maskSum_insert D hc P i] at hEq
      change restrictOn n (geoStrictTransform β C N)
        ((⟨N,E,maskSum D (insert i P),1⟩ : MarkedIdeal n X).geoTransform C β).ideal =
          restrictOn n (geoStrictTransform β C N) (maskSum G (insert i P)) at hEq
      rw [normalized_geoTransform (⟨N,E,maskSum D (insert i P),1⟩ : MarkedIdeal n X) C β,
        maskSum_normalized G hcG hNormG hP] at hEq
      exact hEq.symm
    · have hEmpty : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hPe
      subst P
      simpa only [Finset.insert_empty,maskSum_singleton D hc,maskSum_singleton G hcG] using hGi

private theorem canonical_row_cosupport (hn : 0<n) {N : Set X}
    {E : List (Set X)} {D : GermIdeal n X} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n E) (hTr : IsTransverse n N E) (hc : D.IsCoherent)
    (hne : ∀ y ∈ N,IsNonzeroAlongAt N D y) (hm : IsMonomialAlong n N D E)
    {x : X} (hx : x ∈ N) :
    x ∈ cosupport n N D 1 ↔ 0<∑ j : Fin E.length,divExpAlong n N D (E.get j) x := by
  rw [mem_cosupport_iff_of_isMonomialAlong hn hN hE hTr hc hne hm 1 hx]
  have hsum : (∑ i ∈ memberIdx E x,expDataAlong n N D E x i)=
      ∑ j : Fin E.length,divExpAlong n N D (E.get j) x := by
    rw [memberIdx,Finset.sum_map]
    simp only [Fin.valEmbedding_apply,expDataAlong,Fin.eta]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [dif_pos j.isLt]
    change (if x ∈ E.get j then divExpAlong n N D (E.get j) x else 0)=
      divExpAlong n N D (E.get j) x
    by_cases hxj : x ∈ E.get j
    · simp only [if_pos hxj]
    · simp only [if_neg hxj]
      have hNot : ¬∃ e,¬IsDivNearAlong n N D (E.get j) (e+1) x := by
        rintro ⟨e,he⟩
        exact he (isDivNearAlong_of_notMem (hN.1.inter (hE.1 _ (List.get_mem E j)))
          (fun h => hxj h.2) (e+1))
      symm
      unfold divExpAlong
      rw [dif_neg hNot]
  rw [hsum]
  omega

private theorem maskSum_canonical_cosupport {r : ℕ} (hn : 0<n) {N : Set X}
    {E : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (D : Fin r → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (hne : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (D i) y)
    (hm : ∀ i,IsMonomialAlong n N (D i) E) (P : Finset (Fin r)) :
    cosupport n N (maskSum D P) 1={x | x ∈ N ∧ P ⊆ properRows
      (fun i j => divExpAlong n N (D i) (E.get j) x)} := by
  ext x
  rw [cosupport_maskSum_one D hc P N x]
  constructor
  · rintro ⟨hx,hall⟩
    refine ⟨hx,fun i hi => ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (canonical_row_cosupport hn hN hE hTr (hc i) (hne i) (hm i) hx).mp (hall i hi)⟩
  · rintro ⟨hx,hall⟩
    exact ⟨hx,fun i hi =>
      (canonical_row_cosupport hn hN hE hTr (hc i) (hne i) (hm i) hx).mpr
        (Finset.mem_filter.mp (hall hi)).2⟩

private theorem maximum_selected_feasible {ι : Type*} (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hnzM : ∀ y ∈ M.N,IsNonzeroAlongAt M.N M.ideal y)
    (hmM : IsMonomialAlong n M.N M.ideal M.E) (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (hne : ∀ i,∀ y ∈ M.N,IsNonzeroAlongAt M.N (D i) y)
    (hm : ∀ i,IsMonomialAlong n M.N (D i) M.E) (P : Finset ι) (hP : P.Nonempty)
    (hRows : ∀ i ∈ P,maxLocusA M ⊆ cosupport n M.N (D i) 1)
    {x : X} (hx : x ∈ maxLocusA M) :
    ∃ S : Finset (Fin M.E.length),S.Nonempty ∧
      S ⊆ Finset.univ.filter (fun j => x ∈ M.E.get j) ∧
      (∀ i ∈ P,1 ≤ ∑ j ∈ S,divExpAlong n M.N (D i) (M.E.get j) x) ∧
      ∀ᶠ y in 𝓝 x,y ∈ maxLocusA M ↔ y ∈ M.N ∧ y ∈ memberInter M.E S := by
  have hC := isAdmissibleCentre_maxLocusA hn hM hnzM hmM
  have hCN : maxLocusA M ⊆ M.N := fun _ hy => M.cosupp_subset_N hy.1
  have hxN := hCN hx
  cases hv : gammaAlong n M.N M.ideal M.E M.d x with
  | bot =>
    exact ((gammaAlong_eq_bot_iff_of_isMonomialAlong hn hM.isClosedSubmanifold_N
      hM.isSNCDivisor hM.isTransverse hM.isCoherent hnzM hmM M.d hxN).mp hv hx.1).elim
  | coe v =>
    let S := topIdx M.E v
    have hWeight (i : ι) (hi : i ∈ P) :
        1 ≤ ∑ j ∈ S,divExpAlong n M.N (D i) (M.E.get j) x := by
      have h := NonmonomialStepAlong.le_sum_divExpAlong_of_subset_cosupport hn
        hM.isClosedSubmanifold_N hM.isSNCDivisor hM.isTransverse (hc i) (hne i) (hm i)
        hC.2.2 hCN (hRows i hi) hx
      rwa [filter_eventually_subset_eq_topIdx_along hn hM hnzM hmM hx hv] at h
    have hNonempty : S.Nonempty := by
      by_contra hno
      have hEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hno
      obtain ⟨i,hi⟩ := hP
      have h := hWeight i hi
      simp only [hEmpty,Finset.sum_empty] at h
      omega
    have hxS := mem_memberInter_of_gammaAlong_eq hn hM.isClosedSubmanifold_N
      hM.isSNCDivisor hM.isTransverse hM.isCoherent hnzM hxN hv
    exact ⟨S,hNonempty,fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxS j hj⟩,
      hWeight,eventually_mem_maxLocusA_iff hn hM hnzM hmM hx hv⟩

private theorem mem_pullback_open_comp_iff (U : Opens X) {I : GermIdeal n X}
    (hc : I.IsCoherent) {x : U} {g : X → ℂ} :
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) I).mem x (g ∘ Subtype.val) ↔
      I.mem x.val g := by
  constructor
  · intro hg
    have hmem := (MarkedIdealRestrictOpen.mem_pullback_val_iff U hc).mp hg
    apply HomogenizedIdeal.mem_congr hc hmem
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact extendOpens_val U (g ∘ Subtype.val) ⟨y,hy⟩
  · exact MarkedIdealRestrictOpen.comp_val_mem_pullback_val U hc

private theorem mem_iff_of_open_pullback_eq (U : Opens X) {I J : GermIdeal n X}
    (hcI : I.IsCoherent) (hcJ : J.IsCoherent)
    (hEq : GermIdeal.pullback (m := n) (Subtype.val : U → X) I =
      GermIdeal.pullback (m := n) (Subtype.val : U → X) J) {x : U} (g : X → ℂ) :
    I.mem x.val g ↔ J.mem x.val g := by
  rw [←mem_pullback_open_comp_iff U hcI,←mem_pullback_open_comp_iff U hcJ,hEq]

private def FreeFrameAt {ι : Type*} (N : Set X) (A : ι → Set X) (x : X) : Prop :=
  ∃ (Q : Finset (Fin n)) (p : ι → Fin n),
    IsCoordinateFamilyAt n (fun o : Option ι => o.elim N A)
      (fun o => o.elim Q (fun a => Q ∪ {p a})) x ∧
    (∀ a,x ∈ A a → p a ∉ Q) ∧ Set.InjOn p {a | x ∈ A a}

private theorem freeFrameAt_open_iff {ι : Type*} {N : Set X} {A : ι → Set X}
    (U : Opens X) {x : U} :
    FreeFrameAt (X := CMfd.of (n := n) U) ((Subtype.val : U → X) ⁻¹' N)
      (fun a => (Subtype.val : U → X) ⁻¹' A a) x ↔ FreeFrameAt N A x.val := by
  constructor
  · rintro ⟨Q,p,hFam,hFree,hInj⟩
    have hFam' : IsCoordinateFamilyAt n
        (fun o : Option ι => (Subtype.val : U → X) ⁻¹' o.elim N A)
        (fun o => o.elim Q (fun a => Q ∪ {p a})) x :=
      IsCoordinateFamilyAt.reindex hFam id (by rintro (_ | a) <;> rfl) (fun _ => rfl)
    exact ⟨Q,p,isCoordinateFamilyAt_preimage_val_iff.mp hFam',hFree,hInj⟩
  · rintro ⟨Q,p,hFam,hFree,hInj⟩
    refine ⟨Q,p,?_,hFree,hInj⟩
    exact IsCoordinateFamilyAt.reindex (isCoordinateFamilyAt_preimage_val_iff.mpr hFam)
      id (by rintro (_ | a) <;> rfl) (fun _ => rfl)

private theorem freeFrameAt_reindex {ι κ : Type*} {N : Set X}
    {A : ι → Set X} {B : κ → Set X} {x : X} (c : κ → ι) (hc : Function.Injective c)
    (hAB : ∀ k,B k=A (c k)) (h : FreeFrameAt N A x) : FreeFrameAt N B x := by
  obtain ⟨Q,p,hFam,hFree,hInj⟩ := h
  refine ⟨Q,p ∘ c,?_,?_,?_⟩
  · apply IsCoordinateFamilyAt.reindex hFam (Option.map c)
    · rintro (_ | a)
      · rfl
      · exact hAB a
    · rintro (_ | a) <;> rfl
  · intro a ha
    exact hFree (c a) (by rwa [hAB] at ha)
  · intro a ha b hb hab
    change x ∈ B a at ha
    change x ∈ B b at hb
    rw [hAB] at ha hb
    exact hc (hInj ha hb hab)

private theorem freeFrameAt_pullback {ι : Type} {N : Set X} {A : ι → Set X}
    {φ : Y → X} (hφ : PullsBackCoordinates (n := n) φ) {y : Y}
    (h : FreeFrameAt N A (φ y)) : FreeFrameAt (φ ⁻¹' N) (fun a => φ ⁻¹' A a) y := by
  obtain ⟨Q,p,hFam,hFree,hInj⟩ := h
  refine ⟨Q,p,?_,hFree,hInj⟩
  exact IsCoordinateFamilyAt.reindex (hφ _ _ y hFam) id
    (by rintro (_ | a) <;> rfl) (fun _ => rfl)

private theorem coordinateFamilyAt_congr_carrier {ι : Type*} {C D : Set X}
    {E : ι → Set X} {Q : Finset (Fin n)} {T : ι → Finset (Fin n)} {x : X}
    (hEq : ∀ᶠ y in 𝓝 x,y ∈ C ↔ y ∈ D)
    (h : IsCoordinateFamilyAt n (fun o : Option ι => o.elim D E)
      (fun o => o.elim Q T) x) :
    IsCoordinateFamilyAt n (fun o : Option ι => o.elim C E)
      (fun o => o.elim Q T) x := by
  obtain ⟨W,hW,hWo,hxW⟩ := mem_nhds_iff.mp hEq
  apply isCoordinateFamilyAt_of_inter_eq hWo hxW ?_ h
  rintro (_ | i)
  · ext y
    exact and_congr_left (fun hy => (hW hy).symm)
  · rfl

private def TransverseAt (C : Set X) (E : List (Set X)) (x : X) : Prop :=
  ∃ (Q : Finset (Fin n)) (T : Fin E.length → Finset (Fin n)),
    IsCoordinateFamilyAt n (fun o : Option (Fin E.length) => o.elim C (fun i => E.get i))
      (fun o => o.elim Q T) x ∧
    ∀ i,x ∈ E.get i → (T i).card=1 ∧ Disjoint (T i) Q

private theorem transverse_singleton_at_of_open {C H : Set X} (U : Opens X) {x : U}
    (hx : x.val ∈ C)
    (h : IsTransverse n ((Subtype.val : U → X) ⁻¹' C)
      [(Subtype.val : U → X) ⁻¹' H]) : TransverseAt C [H] x.val := by
  obtain ⟨Q,T,hFam,hCard⟩ := h x hx
  have hFam' : IsCoordinateFamilyAt n
      (fun o : Option (Fin 1) => (Subtype.val : U → X) ⁻¹' o.elim C (fun i => [H].get i))
      (fun o => o.elim Q T) x := by
    apply IsCoordinateFamilyAt.reindex hFam id
    · rintro (_ | i)
      · rfl
      · fin_cases i; rfl
    · intro o; rfl
  refine ⟨Q,T,isCoordinateFamilyAt_preimage_val_iff.mp hFam',?_⟩
  intro i hi
  fin_cases i
  exact hCard 0 hi

private theorem maximum_full_old_geometry (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) (Sigma : GermIdeal n X)
    (hM : (⟨N,born,Sigma,1⟩ : MarkedIdeal n X).IsWellFormed)
    (hneSigma : ∀ x ∈ N,IsNonzeroAlongAt N Sigma x)
    (hmonoSigma : IsMonomialAlong n N Sigma born)
    (hProper : ∀ x ∈ maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X),
      properRows (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=P)
    (hRows : ∀ i ∈ P,maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X) ⊆
      cosupport n N (oldMonomialPart N old born i) 1) :
    HasNormalCrossings n (maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) (old ++ born) ∧
      ∀ i : Fin old.length,i ∉ P →
        IsTransverse n (maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) [old.get i] := by
  let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
  let C := maxLocusA M
  let D := oldMonomialPart N old born
  let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
    divExpAlong n N (D i) (born.get j) x
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hc (i : Fin old.length) : (D i).IsCoherent := (hParts i).2.2.2.2.1
  have hnz (i : Fin old.length) : ∀ x ∈ N,IsNonzeroAlongAt N (D i) x := (hParts i).2.2.2.2.2.1
  have hm (i : Fin old.length) : IsMonomialAlong n N (D i) born := (hParts i).2.2.2.2.2.2.1
  have hAt (x : X) (hx : x ∈ C) :
      HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) C (old ++ born) x ∧
      ∀ i : Fin old.length,i ∉ P → TransverseAt C [old.get i] x := by
    have hxN : x ∈ N := hx.1.1
    obtain ⟨S,hS,hSJ,hFeasible,hLocal⟩ := maximum_selected_feasible hn M hM hneSigma
      hmonoSigma D hc hnz hm P hP hRows hx
    have hActive : (properRows (A x)).Nonempty := by rw [hProper x hx]; exact hP
    have hFeas : ∀ i ∈ properRows (A x),1 ≤ ∑ j ∈ S,A x i j := by
      rw [hProper x hx]
      exact hFeasible
    obtain ⟨U,hxU,hAny⟩ :=
      HironakaG3PreparedMixedGivenBlowup.exists_prepared_mixed_window_for_any_blowup
        hn hN hE hTr hdense hOrd hPrepared hxN hActive S hS hSJ hFeas
    let NU := (Subtype.val : U → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
    let SU := S.map e
    let CU := NU ∩ memberInter bornU SU
    have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
    have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
    have hBornU : IsSNCDivisor n bornU := isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hBorn
    have hTrU : IsTransverse n NU bornU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
    have hCU : IsClosedSubmanifold n CU :=
      MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hNU.1 hBornU hTrU SU
    have hThin : interior CU=∅ := by
      obtain ⟨j,hj⟩ := hS
      have hjU : e j ∈ SU := Finset.mem_map.mpr ⟨j,hj,rfl⟩
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have h := interior_mono (fun _ (hz : _ ∈ CU) => hz.2 (e j) hjU) hy
      rw [MonomialCase.interior_get_eq_empty hn hBornU (e j)] at h
      exact h.elim
    obtain ⟨Y0,α,hα⟩ := ResolutionDriver.exists_blowup (Y := CMfd.of (n := n) U) CU hCU hThin
    obtain ⟨hCeq,hxCU,_hCU,_hThin,hFull,_hSharp,_hOrdU,_hPrepU,_hN',_hSN',_hTr',
      _hDense',_hOrd',_hPrep',_hAU,hRowData,_hMatrix,_hOff⟩ := hAny Y0 α hα
    have hxStratum : x ∈ N ∩ memberInter born S :=
      ⟨hxN,fun j hj => (Finset.mem_filter.mp (hSJ hj)).2⟩
    have hFullPre : HasNormalCrossings n ((Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S))
        ((old ++ born).map ((Subtype.val : U → X) ⁻¹' ·)) := by
      rw [hCeq] at hFull
      simpa only [oldU,bornU,List.map_append] using hFull
    have hNC := HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp
      (hFullPre (⟨x,hxU⟩ : U) hxStratum)
    obtain ⟨Q,T,hFam,hCard⟩ := hNC
    refine ⟨⟨Q,T,coordinateFamilyAt_congr_carrier hLocal hFam,hCard⟩,?_⟩
    intro i hi
    have hiA : i ∉ properRows (A x) := by rw [hProper x hx]; exact hi
    have hTi := ((hRowData i).2.1 hiA).2
    rw [hCeq] at hTi
    obtain ⟨Q,T,hFam,hCard⟩ := transverse_singleton_at_of_open U (x := ⟨x,hxU⟩) hxStratum hTi
    exact ⟨Q,T,coordinateFamilyAt_congr_carrier hLocal hFam,hCard⟩
  exact ⟨fun x hx => (hAt x hx).1,fun i hi x hx => (hAt x hx).2 i hi⟩

theorem actual_next_full_geometry (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hC : IsClosedSubmanifold n C) (hCN : C ⊆ N)
    (hCFull : HasNormalCrossings n C (old ++ born))
    (hCBorn : HasNormalCrossings n C born) {β : Y → X} (hβ : IsBlowupAlong n C β) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
    IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old' ++ born') ∧ IsTransverse n N' born' ∧
      N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born',H) := by
  let N' := geoStrictTransform β C N
  let old' := old.map (geoStrictTransform β C)
  let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
  let T : BlowupTower X Y := .step .refl C β hβ
  have hGeo : IsGeoTestTower (geometricTemplate (X := X) N []) T := by
    refine ⟨trivial,hC,?_,hasNormalCrossings_nil_of_isClosedSubmanifold hC⟩
    change C ⊆ cosupport n N (unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact hCN
  have hAll : IsGeoTestTower (geometricTemplate (X := X) (univ : Set X) (old ++ born)) T := by
    refine ⟨trivial,hC,?_,hCFull⟩
    change C ⊆ cosupport n univ (unitIdeal n X) 0
    rw [cosupport_zero (fun _ _ hg => hg)]
    exact subset_univ C
  have hRecorded := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hN hE hdense T hGeo hAll
  have hN' : IsClosedSubmanifold n N' := hRecorded.1
  have hFull' : IsSNCDivisor n (old' ++ born') := by
    have h := SimultaneousNormalCrossings.isSNCDivisor_geoTransformE_of_hasNormalCrossings hβ hE hCFull
    simpa only [old',born',List.map_append,List.append_assoc] using h
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hTr' : IsTransverse n N' born' :=
    SimultaneousNormalCrossings.isTransverse_geoTransformE_of_hasNormalCrossings hβ hN.1 hCN hBorn hTr hCBorn
  have hDense' : N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born',H) := by
    have h := hRecorded.2.2.2.1
    change N' ⊆ closure (N' \ ⋃ H ∈ (old ++ born).map (geoStrictTransform β C) ++ [β ⁻¹' C],H) at h
    simpa only [old',born',List.map_append,List.append_assoc] using h
  exact ⟨hN',hFull',hTr',hDense'⟩

private theorem nested_blowup_comparison {C : Set X} {β : Y → X}
    (hβ : IsBlowupAlong n C β) (U : Opens X) {Y0 : CMfd.{u} n}
    {C0 : Set U} {α : Y0 → U} (hα : IsBlowupAlong n C0 α) (W : Opens U)
    (hCentres : (Subtype.val : W → U) ⁻¹' C0 =
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C)) :
    let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
    ∃ χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hβU W)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hα W),
      BlowupBiholomorphismLift.restrictMap hα W ∘ χ =
        BlowupBiholomorphismLift.restrictMap hβU W := by
  let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
  have hβW := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβU W
  have hαW := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hα W
  rw [hCentres] at hαW
  obtain ⟨a,b,ha,hb,hComp,_hCompInv,hba,hab⟩ :=
    BlowupUniqueness.exists_biholomorphism_over hβW hαW
  exact ⟨⟨⟨a,b,congrFun hba,congrFun hab⟩,ha,hb⟩,hComp⟩

private theorem parts_open_pullback (N : Set X) (I : GermIdeal n X) (E : List (Set X))
    (hcI : I.IsCoherent) (hcD : (monomialPartAlong n N I E).IsCoherent)
    (hcJ : (nonmonomialPartAlong n N I E).IsCoherent) (U : Opens X) :
    monomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) =
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (monomialPartAlong n N I E) ∧
    nonmonomialPartAlong n ((Subtype.val : U → X) ⁻¹' N)
        (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
        (E.map ((Subtype.val : U → X) ⁻¹' ·)) =
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (nonmonomialPartAlong n N I E) := by
  have hloc : ∀ y : U,∃ ψ : X → U,
      DerivativeIdealAlongEtale.IsLocalInverseAt n (Subtype.val : U → X) ψ y :=
    fun y => ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩
  exact ⟨(pullback_monomialPartAlong hloc
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)).symm,
    (pullback_nonmonomialPartAlong hloc hcI hcD hcJ).symm⟩

private theorem nested_strict_dictionary {C : Set X} {β : Y → X}
    (hβ : IsBlowupAlong n C β) (U : Opens X) {Y0 : CMfd.{u} n}
    {C0 : Set U} {α : Y0 → U} (hα : IsBlowupAlong n C0 α) (W : Opens U)
    (hCentres : (Subtype.val : W → U) ⁻¹' C0 =
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C)) :
    let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
    ∀ χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hβU W)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hα W),
      BlowupBiholomorphismLift.restrictMap hα W ∘ χ =
        BlowupBiholomorphismLift.restrictMap hβU W →
      let g := fun q : BlowupBiholomorphismLift.preOpen hβU W => (q.val.val : Y)
      let f := fun q => ((χ q).val : Y0)
      (∀ H : Set X,g ⁻¹' geoStrictTransform β C H=
        f ⁻¹' geoStrictTransform α C0 ((Subtype.val : U → X) ⁻¹' H)) ∧
      g ⁻¹' (β ⁻¹' C)=f ⁻¹' (α ⁻¹' C0) := by
  let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
  let βU := BlowupBiholomorphismLift.restrictMap hβ U
  let βW := BlowupBiholomorphismLift.restrictMap hβU W
  let αW := BlowupBiholomorphismLift.restrictMap hα W
  dsimp only
  intro χ hComp
  change αW ∘ χ=βW at hComp
  let g := fun q : BlowupBiholomorphismLift.preOpen hβU W => (q.val.val : Y)
  let f := fun q => ((χ q).val : Y0)
  constructor
  · intro H
    have hRU := MarkedIdealRestrictOpen.geoStrictTransform_restrict (C := C) (π := β) U
      (BlowupBiholomorphismLift.preOpen hβ U).isOpen H
    have hRW := MarkedIdealRestrictOpen.geoStrictTransform_restrict
      (C := (Subtype.val : U → X) ⁻¹' C) (π := βU) W
      (BlowupBiholomorphismLift.preOpen hβU W).isOpen ((Subtype.val : U → X) ⁻¹' H)
    have hRA := MarkedIdealRestrictOpen.geoStrictTransform_restrict (C := C0) (π := α) W
      (BlowupBiholomorphismLift.preOpen hα W).isOpen ((Subtype.val : U → X) ⁻¹' H)
    change geoStrictTransform βU ((Subtype.val : U → X) ⁻¹' C)
      ((Subtype.val : U → X) ⁻¹' H) =
        (Subtype.val : BlowupBiholomorphismLift.preOpen hβ U → Y) ⁻¹' geoStrictTransform β C H at hRU
    change geoStrictTransform βW
      ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C))
      ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' H)) =
        (Subtype.val : BlowupBiholomorphismLift.preOpen hβU W → BlowupBiholomorphismLift.preOpen hβ U) ⁻¹'
          geoStrictTransform βU ((Subtype.val : U → X) ⁻¹' C) ((Subtype.val : U → X) ⁻¹' H) at hRW
    change geoStrictTransform αW ((Subtype.val : W → U) ⁻¹' C0)
      ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' H)) =
        (Subtype.val : BlowupBiholomorphismLift.preOpen hα W → Y0) ⁻¹'
          geoStrictTransform α C0 ((Subtype.val : U → X) ⁻¹' H) at hRA
    calc
      g ⁻¹' geoStrictTransform β C H = geoStrictTransform βW
          ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C))
          ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' H)) := by
        rw [hRW,hRU]
        rfl
      _ = χ ⁻¹' geoStrictTransform αW
          ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C))
          ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' H)) := by
        rw [←hComp]
        exact BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ αW _ _
      _ = f ⁻¹' geoStrictTransform α C0 ((Subtype.val : U → X) ⁻¹' H) := by
        rw [←hCentres,hRA]
        rfl
  · ext q
    have hPoint : (α (f q) : X)=β (g q) :=
      congrArg Subtype.val (congrArg Subtype.val (congrFun hComp q))
    have hc := (Set.ext_iff.mp hCentres) (αW (χ q))
    change α (f q) ∈ C0 ↔ (α (f q) : X) ∈ C at hc
    change β (g q) ∈ C ↔ α (f q) ∈ C0
    rw [←hPoint]
    exact hc.symm

private theorem trace_diffeo_pullback
    (χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {N H : Set X} (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H) :
    restrictOn n (χ ⁻¹' N) (vanishingIdeal (n := n) (χ ⁻¹' H)) =
      GermIdeal.pullback (m := n) χ (restrictOn n N (vanishingIdeal (n := n) H)) := by
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hcI := isCoherent_restrictOn_of_isClosedSubmanifold hcH hN
  have hPreH := MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
    χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply hH
  have hVanish : GermIdeal.pullback (m := n) χ (vanishingIdeal (n := n) H)=
      vanishingIdeal (n := n) (χ ⁻¹' H) := by
    have h := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      (φ := (χ : Y → X)) (ψ := (χ.symm : X → Y))
      χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply
      (g := (id : Y → Y)) contMDiff_id H
    rw [BlowupControlledTransform.pullback_id
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hPreH),Function.comp_id] at h
    exact h.symm
  rw [←hVanish]
  ext z g
  rw [BlowupBiholomorphismLift.mem_restrictOn_pullback_diffeo_iff χ hcH,
    BlowupBiholomorphismLift.mem_pullback_diffeo_iff χ hcI]

private theorem nested_transform_dictionary {C : Set X} {β : Y → X}
    (hβ : IsBlowupAlong n C β) (U : Opens X) {Y0 : CMfd.{u} n}
    {C0 : Set U} {α : Y0 → U} (hα : IsBlowupAlong n C0 α) (W : Opens U)
    (hCentres : (Subtype.val : W → U) ⁻¹' C0 =
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C))
    (M : MarkedIdeal n X) (hc : M.ideal.IsCoherent)
    (hcT : (M.geoTransform C β).ideal.IsCoherent)
    (hcModel : (((MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) M).geoTransform C0 α).ideal).IsCoherent) :
    let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
    ∀ χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hβU W)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hα W),
      BlowupBiholomorphismLift.restrictMap hα W ∘ χ =
        BlowupBiholomorphismLift.restrictMap hβU W →
      GermIdeal.pullback (m := n) (Subtype.val : BlowupBiholomorphismLift.preOpen hβU W →
          BlowupBiholomorphismLift.preOpen hβ U)
        (GermIdeal.pullback (m := n) (Subtype.val : BlowupBiholomorphismLift.preOpen hβ U → Y)
          (M.geoTransform C β).ideal) =
      GermIdeal.pullback (m := n) χ
        (GermIdeal.pullback (m := n) (Subtype.val : BlowupBiholomorphismLift.preOpen hα W → Y0)
          ((MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M).geoTransform C0 α).ideal) := by
  let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
  let MU := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M
  let MW := MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W → U) MU
  let βU := BlowupBiholomorphismLift.restrictMap hβ U
  let βW := BlowupBiholomorphismLift.restrictMap hβU W
  let αW := BlowupBiholomorphismLift.restrictMap hα W
  have hcU : MU.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hBU := MarkedIdealRestrictOpen.geoTransform_pullback_val hc hβ hcT U
    (BlowupBiholomorphismLift.preOpen hβ U).isOpen
  change MU.geoTransform ((Subtype.val : U → X) ⁻¹' C) βU =
    MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : BlowupBiholomorphismLift.preOpen hβ U → Y) (M.geoTransform C β) at hBU
  have hcBU : (MU.geoTransform ((Subtype.val : U → X) ⁻¹' C) βU).ideal.IsCoherent := by
    rw [hBU]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcT
  have hBW := MarkedIdealRestrictOpen.geoTransform_pullback_val hcU hβU hcBU W
    (BlowupBiholomorphismLift.preOpen hβU W).isOpen
  change MW.geoTransform ((Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C)) βW =
    MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : BlowupBiholomorphismLift.preOpen hβU W → BlowupBiholomorphismLift.preOpen hβ U)
      (MU.geoTransform ((Subtype.val : U → X) ⁻¹' C) βU) at hBW
  have hAW := MarkedIdealRestrictOpen.geoTransform_pullback_val hcU hα hcModel W
    (BlowupBiholomorphismLift.preOpen hα W).isOpen
  change MW.geoTransform ((Subtype.val : W → U) ⁻¹' C0) αW =
    MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : BlowupBiholomorphismLift.preOpen hα W → Y0) (MU.geoTransform C0 α) at hAW
  have hcAW : (MW.geoTransform ((Subtype.val : W → U) ⁻¹' C0) αW).ideal.IsCoherent := by
    rw [hAW]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcModel
  have hcMW : MW.ideal.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcU
  have hαW := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hα W
  have hcCW := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hαW
  dsimp only
  intro χ hComp
  change αW ∘ χ=βW at hComp
  have hBW0 : MW.geoTransform ((Subtype.val : W → U) ⁻¹' C0) βW =
      MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : BlowupBiholomorphismLift.preOpen hβU W → BlowupBiholomorphismLift.preOpen hβ U)
        (MU.geoTransform ((Subtype.val : U → X) ⁻¹' C) βU) := by
    rw [hCentres]
    exact hBW
  have h := congrArg MarkedIdeal.ideal (BlowupBiholomorphismLift.geoTransform_comp_diffeo
    χ MW hcMW ((Subtype.val : W → U) ⁻¹' C0) hcCW hαW.contMDiff hcAW)
  rw [hComp,hBW0,hAW,hBU] at h
  exact h

private theorem nested_parts_dictionary (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N H : Set X} {N0 H0 : Set Y} {E : List (Set X)} {E0 : List (Set Y)}
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    (hN0 : IsClosedSubmanifold n N0) (hH0 : IsClosedSubmanifold n H0)
    (hcD : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).IsCoherent)
    (hcJ : (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).IsCoherent)
    (hcD0 : (monomialPartAlong n N0 (restrictOn n N0 (vanishingIdeal (n := n) H0)) E0).IsCoherent)
    (hcJ0 : (nonmonomialPartAlong n N0 (restrictOn n N0 (vanishingIdeal (n := n) H0)) E0).IsCoherent)
    (hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
    (hHC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' H) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' H0))
    (hEC : (E.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·) =
      (E0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·)) :
    let I := restrictOn n N (vanishingIdeal (n := n) H)
    let I0 := restrictOn n N0 (vanishingIdeal (n := n) H0)
    let pb := fun (I : GermIdeal n X) => GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
      (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I)
    let pb0 := fun (I : GermIdeal n Y) => GermIdeal.pullback (m := n) χ
      (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I)
    pb I=pb0 I0 ∧ pb (monomialPartAlong n N I E)=pb0 (monomialPartAlong n N0 I0 E0) ∧
      pb (nonmonomialPartAlong n N I E)=pb0 (nonmonomialPartAlong n N0 I0 E0) := by
  let I := restrictOn n N (vanishingIdeal (n := n) H)
  let I0 := restrictOn n N0 (vanishingIdeal (n := n) H0)
  let N1 := (Subtype.val : V1 → X) ⁻¹' N
  let N2 := (Subtype.val : V2 → V1) ⁻¹' N1
  let E1 := E.map ((Subtype.val : V1 → X) ⁻¹' ·)
  let E2 := E1.map ((Subtype.val : V2 → V1) ⁻¹' ·)
  let N0W := (Subtype.val : V0 → Y) ⁻¹' N0
  let E0W := E0.map ((Subtype.val : V0 → Y) ⁻¹' ·)
  let I1 := GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I
  let I0W := GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0
  let pb := fun (I : GermIdeal n X) => GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
    (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I)
  let pb0 := fun (I : GermIdeal n Y) => GermIdeal.pullback (m := n) χ
    (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I)
  have hcI : I.IsCoherent := isCoherent_restrictOn_of_isClosedSubmanifold
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) hN
  have hcI0 : I0.IsCoherent := isCoherent_restrictOn_of_isClosedSubmanifold
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hH0) hN0
  have hN1 := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN V1
  have hH1 := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hH V1
  have hN0W := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN0 V0
  have hH0W := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hH0 V0
  have hI1 := HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback hN hH V1
  have hI2 := HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback
    (X := CMfd.of (n := n) V1) hN1 hH1 V2
  have hI0W := HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback hN0 hH0 V0
  have hI : pb I=pb0 I0 := by
    dsimp only [pb,pb0,I,I0]
    rw [←hI1,←hI2,←hI0W,←trace_diffeo_pullback χ hN0W hH0W]
    rw [hNC,hHC]
  have hParts1 := parts_open_pullback N I E hcI hcD hcJ V1
  have hParts0 := parts_open_pullback N0 I0 E0 hcI0 hcD0 hcJ0 V0
  have hcI1 : I1.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcI
  have hcD1 : (monomialPartAlong n N1 I1 E1).IsCoherent := by
    rw [hParts1.1]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcD
  have hcJ1 : (nonmonomialPartAlong n N1 I1 E1).IsCoherent := by
    rw [hParts1.2]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcJ
  have hParts2 := parts_open_pullback (X := CMfd.of (n := n) V1) N1 I1 E1 hcI1 hcD1 hcJ1 V2
  have hcI0W : I0W.IsCoherent := GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcI0
  have hcD0W : (monomialPartAlong n N0W I0W E0W).IsCoherent := by
    rw [hParts0.1]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcD0
  have hcJ0W : (nonmonomialPartAlong n N0W I0W E0W).IsCoherent := by
    rw [hParts0.2]
    exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcJ0
  have hloc : ∀ q : V2,∃ ψ : V0 → V2,DerivativeIdealAlongEtale.IsLocalInverseAt n χ ψ q :=
    fun q => ⟨χ.symm,DerivativeIdealAlongEtale.isLocalInverseAt_of_inverse
      (fun y => (χ.contMDiff y).mdifferentiableAt (by simp))
      (fun y => (χ.symm.contMDiff y).mdifferentiableAt (by simp))
      χ.apply_symm_apply χ.symm_apply_apply q⟩
  have hD0 := pullback_monomialPartAlong (N := N0W) (E := E0W) hloc
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI0W hg)
  have hJ0 := pullback_nonmonomialPartAlong (N := N0W) (E := E0W) hloc hcI0W hcD0W hcJ0W
  refine ⟨hI,?_,?_⟩
  · calc
      pb (monomialPartAlong n N I E) = monomialPartAlong n N2 (pb I) E2 := by
        dsimp only [pb]
        rw [←hParts1.1,←hParts2.1]
      _ = monomialPartAlong n (χ ⁻¹' N0W) (pb0 I0) (E0W.map (χ ⁻¹' ·)) := by
        dsimp only [N2,N1,E2,E1,N0W,E0W]
        rw [hNC,hI,hEC]
      _ = pb0 (monomialPartAlong n N0 I0 E0) := by
        dsimp only [pb0]
        rw [←hParts0.1]
        exact hD0.symm
  · calc
      pb (nonmonomialPartAlong n N I E) = nonmonomialPartAlong n N2 (pb I) E2 := by
        dsimp only [pb]
        rw [←hParts1.2,←hParts2.2]
      _ = nonmonomialPartAlong n (χ ⁻¹' N0W) (pb0 I0) (E0W.map (χ ⁻¹' ·)) := by
        dsimp only [N2,N1,E2,E1,N0W,E0W]
        rw [hNC,hI,hEC]
      _ = pb0 (nonmonomialPartAlong n N0 I0 E0) := by
        dsimp only [pb0]
        rw [←hParts0.2]
        exact hJ0.symm

theorem column_equiv_invariants {r b c : ℕ}
    (A : Fin r → Fin b → ℕ) (B : Fin r → Fin c → ℕ) (e : Fin c ≃ Fin b)
    (h : ∀ i j,B i j=A i (e j)) :
    properRows B=properRows A ∧ tauD B=tauD A ∧ nuOne B=nuOne A := by
  have hRow (i : Fin r) : rowOrder B i=rowOrder A i := by
    unfold rowOrder
    simp_rw [h]
    exact Equiv.sum_comp e (A i)
  have hProper : properRows B=properRows A := by
    ext i
    simp only [properRows,Finset.mem_filter,Finset.mem_univ,true_and,hRow]
  have hGcd (j : Fin c) : gcdColumn B j=gcdColumn A (e j) := by
    simp only [gcdColumn,hProper,h]
  have hResidual (i : Fin r) :
      (∑ j,(B i j-gcdColumn B j))=∑ j,(A i j-gcdColumn A j) := by
    simp_rw [h,hGcd]
    exact Equiv.sum_comp e (fun j => A i j-gcdColumn A j)
  refine ⟨hProper,congrArg Finset.card hProper,?_⟩
  simp only [nuOne,hProper,hResidual]

theorem append_absent_invariants {r b : ℕ} (A : Fin r → Fin b → ℕ) :
    properRows (appendAbsentFamily A)=properRows A ∧ tauD (appendAbsentFamily A)=tauD A := by
  have hRow (i : Fin r) : rowOrder (appendAbsentFamily A) i=rowOrder A i := by
    simp [rowOrder,appendAbsentFamily,appendAbsentRow,Fin.sum_univ_castSucc]
  have hProper : properRows (appendAbsentFamily A)=properRows A := by
    ext i
    simp only [properRows,Finset.mem_filter,Finset.mem_univ,true_and,hRow]
  exact ⟨hProper,congrArg Finset.card hProper⟩

private theorem append_absent_nu_zero {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (hAct : (properRows A).Nonempty) (hNu : nuOne A=0) : nuOne (appendAbsentFamily A)=0 := by
  have hF : restrictIncidence (transformFamily 1 ∅ Finset.univ A) Finset.univ=appendAbsentFamily A := by
    funext i j
    refine Fin.lastCases ?_ (fun k => ?_) j <;>
      simp [restrictIncidence,transformFamily,transformRow,rowWeight,appendAbsentFamily,appendAbsentRow]
  have hTau : tauD (restrictIncidence (transformFamily 1 ∅ Finset.univ A) Finset.univ)=tauD A := by
    rw [hF]
    exact (append_absent_invariants A).2
  have h := HironakaG4ZeroResidualTopTransform.actual_transform_incidence_nu_zero_of_tau_eq
    A ∅ Finset.univ Finset.univ hAct hNu hTau
  rw [hF] at h
  exact h.2

private theorem nested_cosupport_dictionary (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N : Set X} {N0 : Set Y} {I : GermIdeal n X} {I0 : GermIdeal n Y}
    (hc : I.IsCoherent) (hc0 : I0.IsCoherent)
    (hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
    (hI : GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
        (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I) =
      GermIdeal.pullback (m := n) χ
        (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0)) (q : ℕ) :
    (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' cosupport n N I q) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' cosupport n N0 I0 q) := by
  have hloc1 : ∀ x : V1,∃ ψ : X → V1,DerivativeIdealAlongEtale.IsLocalInverseAt n (Subtype.val : V1 → X) ψ x :=
    fun x => ⟨DerivativeIdealAlongEtale.openInv V1 x,DerivativeIdealAlongEtale.isLocalInverseAt_val V1 x⟩
  have hloc2 : ∀ x : V2,∃ ψ : V1 → V2,DerivativeIdealAlongEtale.IsLocalInverseAt n (Subtype.val : V2 → V1) ψ x :=
    fun x => ⟨DerivativeIdealAlongEtale.openInv V2 x,DerivativeIdealAlongEtale.isLocalInverseAt_val V2 x⟩
  have hloc0 : ∀ x : V0,∃ ψ : Y → V0,DerivativeIdealAlongEtale.IsLocalInverseAt n (Subtype.val : V0 → Y) ψ x :=
    fun x => ⟨DerivativeIdealAlongEtale.openInv V0 x,DerivativeIdealAlongEtale.isLocalInverseAt_val V0 x⟩
  have hlocχ : ∀ x : V2,∃ ψ : V0 → V2,DerivativeIdealAlongEtale.IsLocalInverseAt n χ ψ x :=
    fun x => ⟨χ.symm,DerivativeIdealAlongEtale.isLocalInverseAt_of_inverse
      (fun y => (χ.contMDiff y).mdifferentiableAt (by simp))
      (fun y => (χ.symm.contMDiff y).mdifferentiableAt (by simp))
      χ.apply_symm_apply χ.symm_apply_apply x⟩
  have hc1 : (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hc0W : (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc0
  have hC1 := cosupport_pullback_of_local hloc1 (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg) N q
  have hC2 := cosupport_pullback_of_local hloc2 (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc1 hg)
    ((Subtype.val : V1 → X) ⁻¹' N) q
  have hC0 := cosupport_pullback_of_local hloc0 (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc0 hg) N0 q
  have hCχ := cosupport_pullback_of_local hlocχ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc0W hg)
    ((Subtype.val : V0 → Y) ⁻¹' N0) q
  rw [←hC1,←hC2,←hC0,←hCχ,hNC,hI]

private theorem frame_of_nested_dictionary {ι κ : Type}
    (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N : Set X} {N0 : Set Y} {A : ι → Set X} {A0 : κ → Set Y}
    (e : ι → κ) (he : Function.Injective e)
    (hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
    (hAC : ∀ a,(Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' A a) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' A0 (e a))) {x : V2}
    (hFrame : FreeFrameAt N0 A0 ((χ x).val)) : FreeFrameAt N A x.val.val := by
  have hOpen : FreeFrameAt (X := CMfd.of (n := n) V0)
      ((Subtype.val : V0 → Y) ⁻¹' N0) (fun a => (Subtype.val : V0 → Y) ⁻¹' A0 a) (χ x) :=
    (freeFrameAt_open_iff V0).mpr hFrame
  have hχ : PullsBackCoordinates n (χ : V2 → V0) :=
    pullsBackCoordinates_of_forall_notMem_exceptionalLocus χ.contMDiff
      (MarkedIdealBiholomorphism.notMem_exceptionalLocus_of_inverse χ.contMDiff χ.symm.contMDiff
        χ.apply_symm_apply χ.symm_apply_apply)
  have hPull := freeFrameAt_pullback (X := CMfd.of (n := n) V0) (Y := CMfd.of (n := n) V2) hχ hOpen
  have hActual : FreeFrameAt (X := CMfd.of (n := n) V2)
      ((Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N))
      (fun a => (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' A a)) x := by
    rw [hNC]
    exact freeFrameAt_reindex e he hAC hPull
  have hOnce := (freeFrameAt_open_iff (X := CMfd.of (n := n) V1) V2).mp hActual
  exact (freeFrameAt_open_iff V1).mp hOnce

private theorem order_le_one_of_nested_cosupport (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N : Set X} {N0 : Set Y} {I : GermIdeal n X} {I0 : GermIdeal n Y}
    (hN : IsClosedSubmanifold n N) (hN0 : IsClosedSubmanifold n N0)
    (hc : I.IsCoherent) (hc0 : I0.IsCoherent)
    (hne : ∀ y ∈ N,IsNonzeroAlongAt N I y) (hne0 : ∀ y ∈ N0,IsNonzeroAlongAt N0 I0 y)
    (hC2 : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' cosupport n N I 2) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' cosupport n N0 I0 2))
    {x : V2} (hx : x.val.val ∈ N) (hOrd0 : ordinaryTraceOrder N0 I0 ((χ x).val) ≤ 1) :
    ordinaryTraceOrder N I x.val.val ≤ 1 := by
  by_contra hnot
  have hOrd : 2 ≤ ordinaryTraceOrder N I x.val.val := by omega
  have hCos := (ordinaryTraceOrder_cosupport_iff hN hc hne hx 2).mpr hOrd
  have hCos0 : (χ x).val ∈ cosupport n N0 I0 2 := (Set.ext_iff.mp hC2 x).mp hCos
  have hBound := (ordinaryTraceOrder_cosupport_iff hN0 hc0 hne0 hCos0.1 2).mp hCos0
  omega

private theorem expDataAlong_open (N : Set X) (I : GermIdeal n X) (E : List (Set X))
    (hc : I.IsCoherent) (U : Opens X) (x : U) (k : ℕ) :
    expDataAlong n ((Subtype.val : U → X) ⁻¹' N)
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) I)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) x k=expDataAlong n N I E x.val k := by
  apply MonomialInvariantFunctorialAlong.expDataAlong_pullback
    (fun q => MarkedIdealRestrictOpen.cosupp_pullback_val (⟨N,[],I,q⟩ : MarkedIdeal n X)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg) U)
    (map_nhds_subtype_coe_eq_nhds (p := fun y => y ∈ (U : Set X)) x.property
      (U.isOpen.mem_nhds x.property)) E k

private theorem nested_expData_dictionary (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N : Set X} {N0 : Set Y} {I : GermIdeal n X} {I0 : GermIdeal n Y}
    {E : List (Set X)} {E0 : List (Set Y)} (hc : I.IsCoherent) (hc0 : I0.IsCoherent)
    (hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N) =
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
    (hEC : (E.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·) =
      (E0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·))
    (hI : GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
        (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I) =
      GermIdeal.pullback (m := n) χ
        (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0)) (x : V2) (k : ℕ) :
    expDataAlong n N I E x.val.val k=expDataAlong n N0 I0 E0 (χ x).val k := by
  have hc1 : (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc
  have hc0W : (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hc0
  have h1 := expDataAlong_open N I E hc V1 x.val k
  have h2 := expDataAlong_open (X := CMfd.of (n := n) V1)
    ((Subtype.val : V1 → X) ⁻¹' N) (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I)
    (E.map ((Subtype.val : V1 → X) ⁻¹' ·)) hc1 V2 x k
  have h0 := expDataAlong_open N0 I0 E0 hc0 V0 (χ x) k
  have hχ := MonomialInvariantFunctorialAlong.expDataAlong_pullback
    (fun q => MarkedIdealBiholomorphism.MarkedIdeal.cosupp_pullback
      χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply
      (⟨(Subtype.val : V0 → Y) ⁻¹' N0,[],
        GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0,q⟩ : MarkedIdeal n V0)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc0W hg))
    (χ.toHomeomorph.map_nhds_eq x) (E0.map ((Subtype.val : V0 → Y) ⁻¹' ·)) k
  rw [←h0]
  have hEq : expDataAlong n ((Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N))
      (GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
        (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I))
      ((E.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·)) x k =
    expDataAlong n (χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
      (GermIdeal.pullback (m := n) χ (GermIdeal.pullback (m := n) (Subtype.val : V0 → Y) I0))
      ((E0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·)) x k := by
    rw [hNC,hI,hEC]
  exact (h2.trans h1).symm.trans (hEq.trans hχ)

private theorem mem_iff_of_nested_pullback_eq (V1 : Opens X) (V2 : Opens V1)
    {I J : GermIdeal n X} (hcI : I.IsCoherent) (hcJ : J.IsCoherent)
    (hEq : GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
        (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I)=
      GermIdeal.pullback (m := n) (Subtype.val : V2 → V1)
        (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) J))
    (x : V2) (g : X → ℂ) : I.mem x.val.val g ↔ J.mem x.val.val g := by
  have hcI1 : (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) I).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcI
  have hcJ1 : (GermIdeal.pullback (m := n) (Subtype.val : V1 → X) J).IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcJ
  exact (mem_pullback_open_comp_iff V1 hcI).symm.trans
    ((mem_iff_of_open_pullback_eq (X := CMfd.of (n := n) V1) V2 hcI1 hcJ1 hEq
      (x := x) (g ∘ Subtype.val)).trans (mem_pullback_open_comp_iff V1 hcJ))

private theorem nested_get_dictionary (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {L : List (Set X)} {L0 : List (Set Y)} (hLen : L.length=L0.length)
    (hL : (L.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·)=
      (L0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·)) (i : Fin L.length) :
    (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' L.get i)=
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' L0.get (Fin.cast hLen i)) := by
  have hi0 : i.val<L0.length := by omega
  have hget := congrArg (fun L : List (Set V2) => L[i.val]?) hL
  simpa only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem hi0,Option.map_some,Option.some.injEq,
    List.get_eq_getElem,Fin.val_cast] using hget

private theorem nested_prepared_order (hn : 0<n)
    (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N : Set X} {N0 : Set Y} {old born : List (Set X)} {old0 born0 : List (Set Y)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hN0 : IsClosedSubmanifold n N0) (hFull0 : IsSNCDivisor n (old0++born0))
    (hTr0 : IsTransverse n N0 born0) (hdense0 : N0 ⊆ closure (N0 \ ⋃ H ∈ old0++born0,H))
    (hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N)=
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
    (hOld : (old.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·)=
      (old0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·))
    (hBorn : (born.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·)=
      (born0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·))
    (x : V2) (hx : x.val.val ∈ N)
    (hOrd0 : ∀ i,ordinaryTraceOrder N0 (oldResidualPart N0 old0 born0 i) (χ x).val ≤ 1)
    (hPrepared0 : IsPreparedResidualSNCAt N0 old0 born0 (χ x).val) :
    (∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x.val.val ≤ 1) ∧
      IsPreparedResidualSNCAt N old born x.val.val := by
  have hLenO : old.length=old0.length := by simpa using congrArg List.length hOld
  have hLenB : born.length=born0.length := by simpa using congrArg List.length hBorn
  let eO : Fin old.length ≃ Fin old0.length := finCongr hLenO
  let eB : Fin born.length ≃ Fin born0.length := finCongr hLenB
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hFull hTr hdense i
  have hParts0 (i : Fin old0.length) := actual_old_parts_geometry hn hN0 hFull0 hTr0 hdense0 i
  have hOldSNC := isSNCDivisor_of_sublist hFull (List.sublist_append_left old born)
  have hOldSNC0 := isSNCDivisor_of_sublist hFull0 (List.sublist_append_left old0 born0)
  have hJ (i : Fin old.length) :=
    (nested_parts_dictionary V1 V2 V0 χ hN (MonomialPart.isClosedSubmanifold_get hn hOldSNC i)
      hN0 (MonomialPart.isClosedSubmanifold_get hn hOldSNC0 (eO i))
      (hParts i).2.2.2.2.1 (hParts i).2.2.1
      (hParts0 (eO i)).2.2.2.2.1 (hParts0 (eO i)).2.2.1 hNC
      (nested_get_dictionary V1 V2 V0 χ hLenO hOld i) hBorn).2.2
  have hCos (i : Fin old.length) (q : ℕ) := nested_cosupport_dictionary V1 V2 V0 χ
    (hParts i).2.2.1 (hParts0 (eO i)).2.2.1 hNC (hJ i) q
  have hSupports (a : Fin old.length ⊕ Fin born.length) :
      (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' preparedSupport N old born a)=
        χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' preparedSupport N0 old0 born0 (Sum.map eO eB a)) := by
    cases a with
    | inl i =>
      have h := hCos i 1
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts i).2.2.1 hg),
        cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem
          (hParts0 (eO i)).2.2.1 hg)] at h
      exact h
    | inr j =>
      change (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' (N ∩ born.get j))=_
      rw [Set.preimage_inter,Set.preimage_inter,hNC,nested_get_dictionary V1 V2 V0 χ hLenB hBorn j]
      rfl
  refine ⟨?_,?_⟩
  · intro i
    exact order_le_one_of_nested_cosupport V1 V2 V0 χ hN hN0 (hParts i).2.2.1
      (hParts0 (eO i)).2.2.1 (hParts i).2.2.2.1 (hParts0 (eO i)).2.2.2.1
      (hCos i 2) hx (hOrd0 (eO i))
  · exact frame_of_nested_dictionary V1 V2 V0 χ (Sum.map eO eB)
      (Sum.map_injective.mpr ⟨eO.injective,eB.injective⟩) hNC hSupports hPrepared0

private theorem nested_boundary_dictionary {C : Set X} {β : Y → X}
    (hβ : IsBlowupAlong n C β) (U : Opens X) {Y0 : CMfd.{u} n}
    {C0 : Set U} {α : Y0 → U} (hα : IsBlowupAlong n C0 α) (W : Opens U)
    (hCentres : (Subtype.val : W → U) ⁻¹' C0=
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C)) :
    let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
    ∀ χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hβU W)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hα W),
      BlowupBiholomorphismLift.restrictMap hα W ∘ χ=
        BlowupBiholomorphismLift.restrictMap hβU W →
      let V1 := BlowupBiholomorphismLift.preOpen hβ U
      let V2 := BlowupBiholomorphismLift.preOpen hβU W
      let V0 := BlowupBiholomorphismLift.preOpen hα W
      (∀ L : List (Set X),
        ((L.map (geoStrictTransform β C)).map ((Subtype.val : V1 → Y) ⁻¹' ·)).map
          ((Subtype.val : V2 → V1) ⁻¹' ·)=
        ((((L.map ((Subtype.val : U → X) ⁻¹' ·)).map (geoStrictTransform α C0)).map
          ((Subtype.val : V0 → Y0) ⁻¹' ·)).map (χ ⁻¹' ·))) ∧
      ∀ E : List (Set X),
        (((E.map (geoStrictTransform β C)++[β ⁻¹' C]).map
          ((Subtype.val : V1 → Y) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·))=
        ((((E.map ((Subtype.val : U → X) ⁻¹' ·)).map (geoStrictTransform α C0)++[α ⁻¹' C0]).map
          ((Subtype.val : V0 → Y0) ⁻¹' ·)).map (χ ⁻¹' ·)) := by
  dsimp only
  intro χ hComp
  obtain ⟨hStrict,hExc⟩ := nested_strict_dictionary hβ U hα W hCentres χ hComp
  have hList (L : List (Set X)) :
      ((L.map (geoStrictTransform β C)).map
        ((Subtype.val : BlowupBiholomorphismLift.preOpen hβ U → Y) ⁻¹' ·)).map
        ((Subtype.val : BlowupBiholomorphismLift.preOpen
          (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U) W →
            BlowupBiholomorphismLift.preOpen hβ U) ⁻¹' ·)=
      ((((L.map ((Subtype.val : U → X) ⁻¹' ·)).map (geoStrictTransform α C0)).map
        ((Subtype.val : BlowupBiholomorphismLift.preOpen hα W → Y0) ⁻¹' ·)).map (χ ⁻¹' ·)) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro H _hH
    exact hStrict H
  refine ⟨hList,?_⟩
  intro E
  simp only [List.map_append,List.map_cons,List.map_nil]
  rw [hList E]
  congr 1
  exact congrArg (fun H => [H]) hExc

private theorem normalized_mem_of_notMem {N : Set X} (hN : IsClosed N)
    {I : GermIdeal n X} (hNorm : restrictOn n N I=I) {x : X} (hx : x ∉ N)
    {g : X → ℂ} (hg : HolomorphicAt n g x) : I.mem x g := by
  rw [←hNorm]
  refine ⟨hg,0,Fin.elim0,Fin.elim0,fun i => i.elim0,fun i => i.elim0,?_⟩
  filter_upwards [hN.isOpen_compl.mem_nhds hx] with y hy hyN
  exact (hy hyN).elim

private theorem id_empty_transform_normalized (M : MarkedIdeal n X)
    (hN : IsClosed M.N) (hc : M.ideal.IsCoherent)
    (hNorm : restrictOn n M.N M.ideal=M.ideal) :
    (M.geoTransform ∅ (id : X → X)).ideal=M.ideal := by
  have hStrict : geoStrictTransform (id : X → X) ∅ M.N=M.N :=
    ContactCanonicalAlong.geoStrictTransform_empty continuous_id hN
  have h1 := ContactCanonicalAlong.restrictLe_geoTransform_empty_le_pullback
    (BlowupExistenceCodimOne.isBlowupAlong_id_empty (X := X)) M
  have h2 := ContactCanonicalAlong.restrictLe_pullback_le_geoTransform (π := (id : X → X)) ∅ M
  have hWhole := restrictOn_eq_of_restrictLe isClosed_closure h1 h2
  calc
    (M.geoTransform ∅ (id : X → X)).ideal =
        restrictOn n (geoStrictTransform (id : X → X) ∅ M.N)
          (M.geoTransform ∅ (id : X → X)).ideal := (normalized_geoTransform M ∅ id).symm
    _ = restrictOn n (geoStrictTransform (id : X → X) ∅ M.N)
        (GermIdeal.pullback (m := n) (id : X → X) M.ideal) := hWhole
    _ = M.ideal := by rw [hStrict,BlowupControlledTransform.pullback_id hc,hNorm]

private theorem freeFrameAt_add_absent (hn : 0<n) {ι : Type*} {N : Set X}
    {A : ι → Set X} {x : X} (h : FreeFrameAt N A x) :
    FreeFrameAt N (fun o : Option ι => o.elim ∅ A) x := by
  obtain ⟨Q,p,⟨Φ,hsrc,h0,hflat⟩,hfree,hinj⟩ := h
  let p' : Option ι → Fin n := fun o => o.elim ⟨0,hn⟩ p
  refine ⟨Q,p',⟨Φ,hsrc,h0,?_⟩,?_,?_⟩
  · rintro (_ | (_ | a)) hxA
    · exact hflat none hxA
    · exact hxA.elim
    · exact hflat (some a) hxA
  · rintro (_ | a) hxA
    · exact hxA.elim
    · exact hfree a hxA
  · rintro (_ | a) ha (_ | b) hb hab
    · exact ha.elim
    · exact ha.elim
    · exact hb.elim
    · exact congrArg some (hinj ha hb hab)

private def appendLabel {r b : ℕ} : Fin r ⊕ Fin (b+1) → Option (Fin r ⊕ Fin b) :=
  Sum.elim (fun i => some (Sum.inl i)) (Fin.lastCases none (fun j => some (Sum.inr j)))

private theorem appendLabel_injective {r b : ℕ} :
    Function.Injective (appendLabel (r := r) (b := b)) := by
  let back : Option (Fin r ⊕ Fin b) → Fin r ⊕ Fin (b+1) :=
    fun o => o.elim (Sum.inr (Fin.last b)) (Sum.elim Sum.inl (fun j => Sum.inr j.castSucc))
  have h : Function.LeftInverse back appendLabel := by
    rintro (i | j)
    · rfl
    · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [back,appendLabel]
  exact h.injective

private theorem prepared_append_empty (hn : 0<n) {N : Set X} {old born : List (Set X)}
    {x : X} (h : IsPreparedResidualSNCAt N old born x) :
    IsPreparedResidualSNCAt N old (born++[∅]) x := by
  have hFrame := freeFrameAt_add_absent hn (show FreeFrameAt N (preparedSupport N old born) x from h)
  let c : Fin old.length ⊕ Fin (born++[∅]).length → Fin old.length ⊕ Fin (born.length+1) :=
    Sum.map id (Fin.cast (by simp))
  have hc : Function.Injective c := Sum.map_injective.mpr
    ⟨Function.injective_id,Fin.cast_injective _⟩
  apply freeFrameAt_reindex (fun a => appendLabel (c a)) (appendLabel_injective.comp hc) ?_ hFrame
  rintro (i | j)
  · simp only [preparedSupport,Sum.elim_inl,c,Sum.map_inl,id_eq,appendLabel,Option.elim_some]
    simp only [oldResidualPart,MonomialPartEtale.nonmonomialPartAlong_append_empty]
  · change N ∩ (born++[∅]).get j=_
    let j' : Fin (born.length+1) := Fin.cast (by simp) j
    have hj : (born++[∅]).get j=(born++[∅]).get (Fin.cast (by simp) j') := by
      congr 1
    rw [hj]
    change N ∩ (born++[∅]).get (Fin.cast (by simp) j')=
      (appendLabel (Sum.inr j')).elim ∅ (preparedSupport N old born)
    refine Fin.lastCases ?_ (fun k => ?_) j'
    · simp [appendLabel]
    · simp [appendLabel,preparedSupport,List.get_eq_getElem,List.getElem_append_left]

private theorem full_geometry_open {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H)) (U : Opens X) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    IsClosedSubmanifold n NU ∧ IsSNCDivisor n (oldU++bornU) ∧ IsTransverse n NU bornU ∧
      NU ⊆ closure (NU \ ⋃ H ∈ oldU++bornU,H) := by
  refine ⟨BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U,?_,
    isTransverse_preimage (pullsBackCoordinates_val U) hTr,?_⟩
  · simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hFull
  · intro q hq
    have hp : q ∈ (Subtype.val : U → X) ⁻¹' closure (N \ ⋃ H ∈ old++born,H) := hdense hq
    erw [U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (N \ ⋃ H ∈ old++born,H)] at hp
    have hSet : ((Subtype.val : U → X) ⁻¹' N) \
        ⋃ H ∈ old.map ((Subtype.val : U → X) ⁻¹' ·)++born.map ((Subtype.val : U → X) ⁻¹' ·),H=
        (Subtype.val : U → X) ⁻¹' (N \ ⋃ H ∈ old++born,H) := by
      ext z
      simp only [←List.map_append,Set.mem_sdiff,Set.mem_preimage,Set.mem_iUnion]
      constructor
      · rintro ⟨hzN,hz⟩
        refine ⟨hzN,?_⟩
        rintro ⟨H,hm,hzH⟩
        exact hz ⟨_,List.mem_map.mpr ⟨H,hm,rfl⟩,hzH⟩
      · rintro ⟨hzN,hz⟩
        refine ⟨hzN,?_⟩
        rintro ⟨H,hm,hzH⟩
        obtain ⟨H,hH,rfl⟩ := List.mem_map.mp hm
        exact hz ⟨H,hH,hzH⟩
    rw [hSet]
    exact hp

private theorem actual_current_source (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let I := oldTraceIdeal N old
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let M : MarkedIdeal n X := ⟨N,born,maskSum D P,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) → IsMonomialAlong n N M.ideal born →
    let C := maxLocusA M
    let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
    M.ideal.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N M.ideal x) ∧ M.IsWellFormed ∧
      M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} ∧
      M.IsAdmissibleCentre C ∧ interior C=∅ ∧ HasNormalCrossings n C (old++born) ∧
      C ⊆ originalSharpBadLocus (n := n) N (old++born) ∧
      (∀ x ∈ C,properRows (A x)=P) ∧
      (∀ i : Fin old.length,
        (i ∈ P → C ⊆ old.get i) ∧
        (i ∉ P → (∀ x ∈ C,(D i).mem x (fun _ => (1 : ℂ))) ∧ IsTransverse n C [old.get i]) ∧
        (⟨N,born,I i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
        (⟨N,born,D i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C) := by
  dsimp only
  intro hTau hMono
  let I := oldTraceIdeal N old
  let D := oldMonomialPart N old born
  let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
    divExpAlong n N (D i) (born.get j) x
  let M : MarkedIdeal n X := ⟨N,born,maskSum D P,1⟩
  let C := maxLocusA M
  let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hOld := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hcD (i : Fin old.length) : (D i).IsCoherent := (hParts i).2.2.2.2.1
  have hnzD (i : Fin old.length) : ∀ x ∈ N,IsNonzeroAlongAt N (D i) x := (hParts i).2.2.2.2.2.1
  have hmD (i : Fin old.length) : IsMonomialAlong n N (D i) born := (hParts i).2.2.2.2.2.2.1
  have hcSum : M.ideal.IsCoherent := coherent_maskSum D hcD P
  have hnzSum : ∀ x ∈ N,IsNonzeroAlongAt N M.ideal x := nonzero_maskSum D hcD hP hnzD
  have hM : M.IsWellFormed := ⟨hN,hcSum,hBorn,hTr⟩
  have hCos : M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} :=
    maskSum_canonical_cosupport hn hN hBorn hTr D hcD hnzD hmD P
  have hMax := isAdmissibleCentre_maxLocus_gammaAlong hn hN hBorn hTr hcSum hnzSum M rfl rfl rfl hMono
  have hC : M.IsAdmissibleCentre C := hMax.1
  have hProper : ∀ x ∈ C,properRows (A x)=P := by
    intro x hx
    have hp := ((Set.ext_iff.mp hCos x).mp hx.1).2
    exact (Finset.eq_of_subset_of_card_le hp (hTau x hx.1.1)).symm
  have hRows : ∀ i ∈ P,C ⊆ cosupport n N (D i) 1 := by
    intro i hi x hx
    exact (cosupport_maskSum_one D hcD P N x).mp hx.1 |>.2 i hi
  obtain ⟨hFull,hTrans⟩ := maximum_full_old_geometry hn hN hE hTr hdense hOrd hPrepared
    P hP M.ideal hM hnzSum hMono hProper hRows
  have hContain : ∀ i ∈ P,C ⊆ old.get i := by
    intro i hi x hx
    have hzD : x ∈ (D i).zeroLocus := by
      have h := hRows i hi hx
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at h
      exact h.2
    have hzI : x ∈ (I i).zeroLocus :=
      fun g hg => hzD g (le_monomialPartAlong hn hBorn hTr (hParts i).1 x g hg)
    have hH := MonomialPart.isClosedSubmanifold_get hn hOld i
    have h := (HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) hx.1.1).mp hzI
    rwa [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1] at h
  have hUnit (i : Fin old.length) (hi : i ∉ P) : ∀ x ∈ C,(D i).mem x (fun _ => (1 : ℂ)) := by
    intro x hx
    have hi0 : i ∉ properRows (A x) := by rwa [hProper x hx]
    have hOrder : rowOrder (A x) i=0 := by
      have : ¬0<rowOrder (A x) i := by simpa only [properRows,Finset.mem_filter,
        Finset.mem_univ,true_and] using hi0
      omega
    have hz : ∀ j : Fin born.length,A x i j=0 := by
      intro j
      have hle : A x i j ≤ rowOrder (A x) i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    exact HironakaG4CanonicalZeroRowUnit.one_mem_of_zero_canonical_row hn hN hBorn hTr
      (hcD i) (hnzD i) (hmD i) hx.1.1 hz
  have hSharp : C ⊆ originalSharpBadLocus (n := n) N (old++born) := by
    obtain ⟨i,hi⟩ := hP
    let oi : Fin (old++born).length := ⟨i.val,by simp only [List.length_append]; omega⟩
    let bornIndex : Fin born.length → Fin (old++born).length :=
      fun j => ⟨old.length+j.val,by simp only [List.length_append]; omega⟩
    let L : List (Fin (old++born).length) := List.ofFn bornIndex
    have hOldGet : (old++born).get oi=old.get i := by simp [oi,List.get_eq_getElem]
    have hBornGet (j) : (old++born).get (bornIndex j)=born.get j := by
      simp [bornIndex,List.get_eq_getElem]
    have hLmap : L.map (old++born).get=born := by
      rw [show L=List.ofFn bornIndex from rfl,List.map_ofFn]
      convert List.ofFn_get born using 1
      congr 1
      funext j
      exact hBornGet j
    have hApart : ∀ j ∈ L,oi ≠ j := by
      intro j hj
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hj
      intro heq
      have hv := congrArg Fin.val heq
      dsimp [oi,bornIndex] at hv
      have hb := i.isLt
      omega
    have hBad := HironakaG4ActiveMonomialSharpBad.active_old_monomial_subset_originalSharpBadLocus
      hn hN hE hdense oi L hApart
    intro x hx
    apply hBad
    refine ⟨hx.1.1,?_⟩
    rw [hOldGet,hLmap]
    intro hOne
    have h := hRows i hi hx
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)] at h
    exact one_ne_zero (h.2 _ hOne)
  refine ⟨hcSum,hnzSum,hM,hCos,hC,hMax.2 (by simp [M]),hFull,hSharp,hProper,?_⟩
  intro i
  refine ⟨hContain i,fun hi => ⟨hUnit i hi,hTrans i hi⟩,?_,?_⟩
  · refine ⟨hC.1,?_,hC.2.2⟩
    intro x hx
    by_cases hi : i ∈ P
    · have hH := MonomialPart.isClosedSubmanifold_get hn hOld i
      change x ∈ cosupport n N (I i) (d i)
      rw [show d i=1 by simp [d,hi],cosupport_one
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts i).1 hg)]
      exact ⟨hx.1.1,(HironakaSharpActualTraceIncidence.zeroLocus_restrictOn_iff
        (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) hx.1.1).mpr
          (by rw [BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hH.1]; exact hContain i hi hx)⟩
    · change x ∈ cosupport n N (I i) (d i)
      rw [show d i=0 by simp [d,hi],cosupport_zero
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts i).1 hg)]
      exact hx.1.1
  · refine ⟨hC.1,?_,hC.2.2⟩
    intro x hx
    change x ∈ cosupport n N (D i) (d i)
    by_cases hi : i ∈ P
    · rw [show d i=1 by simp [d,hi]]
      exact hRows i hi hx
    · rw [show d i=0 by simp [d,hi],cosupport_zero
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hcD i) hg)]
      exact hx.1.1

private theorem identity_model_geometry (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H)) :
    IsSNCDivisor n (old++(born++[∅])) ∧ IsTransverse n N (born++[∅]) ∧
      N ⊆ closure (N \ ⋃ H ∈ old++(born++[∅]),H) := by
  have hEmpty : IsClosedSubmanifold n (∅ : Set X) := ⟨isClosed_empty,by simp⟩
  have hId := BlowupExistenceCodimOne.isBlowupAlong_id_empty (n := n) (X := X)
  have h := actual_next_full_geometry hn hN hE hTr hdense hEmpty (empty_subset N)
    (fun _ hx => hx.elim) (fun _ hx => hx.elim) hId
  have hNid : geoStrictTransform (id : X → X) ∅ N=N :=
    ContactCanonicalAlong.geoStrictTransform_empty continuous_id hN.1
  have hMap (L : List (Set X)) (hClosed : ∀ H ∈ L,IsClosed H) :
      L.map (geoStrictTransform (id : X → X) ∅)=L := by
    calc
      L.map (geoStrictTransform (id : X → X) ∅)=L.map id := List.map_congr_left
        (fun H hH => ContactCanonicalAlong.geoStrictTransform_empty continuous_id (hClosed H hH))
      _ = L := List.map_id L
  have hOld := hMap old (fun H hH => hE.1 H (List.mem_append_left born hH))
  have hBorn := hMap born (fun H hH => hE.1 H (List.mem_append_right old hH))
  simpa only [hNid,hOld,hBorn,Set.preimage_id] using h.2

private theorem nested_canonical_columns (hn : 0<n)
    (V1 : Opens X) (V2 : Opens V1) (V0 : Opens Y)
    (χ : CMfd.of (n := n) V2 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) V0)
    {N : Set X} {N0 : Set Y} {old born : List (Set X)} {old0 born0 : List (Set Y)}
    (hN : IsClosedSubmanifold n N) (hFull : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hN0 : IsClosedSubmanifold n N0) (hFull0 : IsSNCDivisor n (old0++born0))
    (hTr0 : IsTransverse n N0 born0) (hdense0 : N0 ⊆ closure (N0 \ ⋃ H ∈ old0++born0,H))
    (hLenO : old.length=old0.length) (hLenB : born.length=born0.length)
    (hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → X) ⁻¹' N)=
      χ ⁻¹' ((Subtype.val : V0 → Y) ⁻¹' N0))
    (hOld : (old.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·)=
      (old0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·))
    (hBorn : (born.map ((Subtype.val : V1 → X) ⁻¹' ·)).map ((Subtype.val : V2 → V1) ⁻¹' ·)=
      (born0.map ((Subtype.val : V0 → Y) ⁻¹' ·)).map (χ ⁻¹' ·)) (x : V2) :
    ∀ (i : Fin old.length) (j : Fin born.length),
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) x.val.val=
        divExpAlong n N0 (oldMonomialPart N0 old0 born0 (Fin.cast hLenO i))
          (born0.get (Fin.cast hLenB j)) (χ x).val := by
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hFull hTr hdense i
  have hParts0 (i : Fin old0.length) := actual_old_parts_geometry hn hN0 hFull0 hTr0 hdense0 i
  have hOldSNC := isSNCDivisor_of_sublist hFull (List.sublist_append_left old born)
  have hOldSNC0 := isSNCDivisor_of_sublist hFull0 (List.sublist_append_left old0 born0)
  intro i j
  let i0 := Fin.cast hLenO i
  have hD := (nested_parts_dictionary V1 V2 V0 χ hN
    (MonomialPart.isClosedSubmanifold_get hn hOldSNC i) hN0
    (MonomialPart.isClosedSubmanifold_get hn hOldSNC0 i0)
    (hParts i).2.2.2.2.1 (hParts i).2.2.1
    (hParts0 i0).2.2.2.2.1 (hParts0 i0).2.2.1 hNC
    (nested_get_dictionary V1 V2 V0 χ hLenO hOld i) hBorn).2.1
  have hExp := nested_expData_dictionary V1 V2 V0 χ (hParts i).2.2.2.2.1
    (hParts0 i0).2.2.2.2.1 hNC hBorn hD x j.val
  have hj0 : j.val<born0.length := by omega
  simpa only [i0,expDataAlong,dif_pos j.isLt,dif_pos hj0,Fin.cast,Fin.eta] using hExp

private theorem trace_parts_open_pullback {N H : Set X} (E : List (Set X))
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    (hcD : (monomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).IsCoherent)
    (hcJ : (nonmonomialPartAlong n N (restrictOn n N (vanishingIdeal (n := n) H)) E).IsCoherent)
    (U : Opens X) :
    let NU := (Subtype.val : U → X) ⁻¹' N
    let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let I := restrictOn n N (vanishingIdeal (n := n) H)
    let IU := restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' H))
    IU=GermIdeal.pullback (m := n) (Subtype.val : U → X) I ∧
      monomialPartAlong n NU IU EU=
        GermIdeal.pullback (m := n) (Subtype.val : U → X) (monomialPartAlong n N I E) ∧
      nonmonomialPartAlong n NU IU EU=
        GermIdeal.pullback (m := n) (Subtype.val : U → X) (nonmonomialPartAlong n N I E) := by
  have hcI := isCoherent_restrictOn_of_isClosedSubmanifold
    (VanishingIdealCoherent.isCoherent_vanishingIdeal hH) hN
  have hI := HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback hN hH U
  have hParts := parts_open_pullback N (restrictOn n N (vanishingIdeal (n := n) H)) E hcI hcD hcJ U
  refine ⟨hI,?_,?_⟩
  · rw [hI]
    exact hParts.1
  · rw [hI]
    exact hParts.2

private theorem normalized_of_carrierIdeal_le {N : Set X} (I : GermIdeal n X)
    (hc : I.IsCoherent) (hLe : (vanishingIdeal (n := n) N).Le I) : restrictOn n N I=I := by
  let D : Unit → GermIdeal n X := fun _ => I
  have hSum := maskSum_normalized D (fun _ => hc) (fun _ => hLe)
    (P := {()}) (by simp)
  rw [maskSum_singleton D (fun _ => hc) ()] at hSum
  exact hSum

private theorem normalized_trace (N : Set X) (H : Set X) :
    restrictOn n N (restrictOn n N (vanishingIdeal (n := n) H))=
      restrictOn n N (vanishingIdeal (n := n) H) := by
  ext y g
  exact ⟨fun hg => ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ha.2) hg.2⟩,
    fun hg => ⟨hg.1,IsInSpanAt.restrict (InvertibleIdealQuotient.isInSpanAt_self hg hg.1)⟩⟩

private theorem normalized_nonmonomial (N : Set X) (I : GermIdeal n X) (E : List (Set X)) :
    restrictOn n N (nonmonomialPartAlong n N I E)=nonmonomialPartAlong n N I E := by
  ext x g
  exact restrictOn_colonAlong_mem_iff N I (monomialPartAlong n N I E) (fun _ hg => hg.1) g

private theorem controlled_germ_of_nested_model {C : Set X} {β : Y → X}
    (hβ : IsBlowupAlong n C β) (U : Opens X) {Y0 : CMfd.{u} n}
    {C0 : Set U} {α : Y0 → U} (hα : IsBlowupAlong n C0 α) (W : Opens U)
    (hCentres : (Subtype.val : W → U) ⁻¹' C0=
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C))
    (M : MarkedIdeal n X) (hc : M.ideal.IsCoherent)
    (K : GermIdeal n Y) (K0 : GermIdeal n Y0) (hcK : K.IsCoherent) (hcK0 : K0.IsCoherent)
    (hcT : (M.geoTransform C β).ideal.IsCoherent)
    (hModel : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) M).geoTransform C0 α).ideal=K0) :
    let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
    ∀ χ : CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hβU W)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (BlowupBiholomorphismLift.preOpen hα W),
      BlowupBiholomorphismLift.restrictMap hα W ∘ χ=
        BlowupBiholomorphismLift.restrictMap hβU W →
      GermIdeal.pullback (m := n)
          (Subtype.val : BlowupBiholomorphismLift.preOpen hβU W → BlowupBiholomorphismLift.preOpen hβ U)
        (GermIdeal.pullback (m := n) (Subtype.val : BlowupBiholomorphismLift.preOpen hβ U → Y) K)=
      GermIdeal.pullback (m := n) χ
        (GermIdeal.pullback (m := n) (Subtype.val : BlowupBiholomorphismLift.preOpen hα W → Y0) K0) →
      ∀ (q : BlowupBiholomorphismLift.preOpen hβU W) (g : Y → ℂ),
        (M.geoTransform C β).ideal.mem q.val.val g ↔ K.mem q.val.val g := by
  have hcModel : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) M).geoTransform C0 α).ideal.IsCoherent := by rw [hModel]; exact hcK0
  dsimp only
  intro χ hComp hCanon q g
  have hT := nested_transform_dictionary hβ U hα W hCentres M hc hcT hcModel χ hComp
  rw [hModel] at hT
  exact mem_iff_of_nested_pullback_eq (BlowupBiholomorphismLift.preOpen hβ U)
    (BlowupBiholomorphismLift.preOpen (BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U) W)
    hcT hcK (hT.trans hCanon.symm) q g


private theorem proper_transform_subset {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (S R : Finset (Fin b)) : properRows (transformFamily 1 S R A) ⊆ properRows A := by
  intro i hi
  by_contra hnot
  have hOrder : rowOrder A i=0 := by
    have h := hnot
    simp only [properRows,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] at h
    omega
  have hz (j : Fin b) : A i j=0 := by
    have hle : A i j ≤ rowOrder A i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hNew (j : Fin (b+1)) : transformFamily 1 S R A i j=0 := by
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [transformFamily,transformRow,rowWeight,hz]
  have hZero : rowOrder (transformFamily 1 S R A) i=0 := by simp [rowOrder,hNew]
  have hPos := (Finset.mem_filter.mp hi).2
  omega

theorem actual_target_prepared_over_selected_with_matrix_intrinsic_pointwise (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hCN : C ⊆ N)
    {β : Y → X} (hβ : IsBlowupAlong n (C) β)
    (hNext : let C := C
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β (C) N)
    (hzC : β z ∈ C)
    (hProper : properRows (fun i j =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z))=P)
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => β z ∈ born.get j))
    (hFeas : ∀ i ∈ P,1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z))
    (hLocal : ∀ᶠ y in 𝓝 (β z),y ∈ C ↔ y ∈ N ∧ y ∈ memberInter born S) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    let A' : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
    let A := fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z)
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      (∀ (i : Fin old.length) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g)) ∧
      properRows A' ⊆ properRows A ∧
      (nuOne A=0 → tauD A'=tauD A → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (born.length * B)) ∧
      (RowsChain A → RowsChain A') ∧
      ∃ (b₀ : ℕ) (eSrc : Fin born.length ≃ Fin b₀)
        (eDst : Fin born'.length ≃ Fin (b₀+1))
        (A₀ : Fin old.length → Fin b₀ → ℕ) (S₀ R₀ : Finset (Fin b₀)) (p₀ : Fin b₀),
        S₀ = S.map eSrc.toEmbedding ∧ (∀ j, (eSrc j).val=j.val) ∧ (∀ j, (eDst j).val=j.val) ∧ R₀ ⊆ (Finset.univ.filter (fun j => β z ∈ born.get j)).map eSrc.toEmbedding ∧ (∀ j, eSrc j ∈ R₀ ↔ z ∈ geoStrictTransform β C (born.get j)) ∧ p₀ ∈ S₀ ∧ p₀ ∉ R₀ ∧
        (∀ i j,A₀ i (eSrc j)=A i j) ∧
        ∀ i j,A' i j=transformFamily 1 S₀ R₀ A₀ i (eDst j) := by
  let N' := geoStrictTransform β C N
  let old' := old.map (geoStrictTransform β C)
  let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
  let D := oldMonomialPart N old born
  let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
    divExpAlong n N (D i) (born.get j) x
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hAct : (properRows (A (β z))).Nonempty := by rw [hProper]; exact hP
  have hFeasible : ∀ i ∈ properRows (A (β z)),1 ≤ ∑ j ∈ S,A (β z) i j := by
    rw [hProper]
    exact hFeas
  obtain ⟨U,hxU,hAny⟩ :=
    HironakaG3PreparedMixedGivenBlowup.exists_prepared_mixed_window_for_any_blowup
      hn hN hE hTr hdense hOrd hPrepared (hCN hzC) hAct S hS hSJ hFeasible
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let e : Fin born.length ↪ Fin bornU.length := (finCongr (by simp [bornU])).toEmbedding
  let SU := S.map e
  let CU := NU ∩ memberInter bornU SU
  obtain ⟨hNU,hFullU,hTrU,_hDenseU⟩ := full_geometry_open hN hE hTr hdense U
  have hBornU := isSNCDivisor_of_sublist hFullU (List.sublist_append_right oldU bornU)
  have hCU : IsClosedSubmanifold n CU :=
    MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hNU.1 hBornU hTrU SU
  have hThin : interior CU=∅ := by
    obtain ⟨j,hj⟩ := hS
    have hjU : e j ∈ SU := Finset.mem_map.mpr ⟨j,hj,rfl⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have h := interior_mono (fun _ (hz : _ ∈ CU) => hz.2 (e j) hjU) hy
    rw [MonomialCase.interior_get_eq_empty hn hBornU (e j)] at h
    exact h.elim
  obtain ⟨Y0,α,hα⟩ := ResolutionDriver.exists_blowup (Y := CMfd.of (n := n) U) CU hCU hThin
  obtain ⟨hCeq,_hxCU,_hCU,_hThin,_hCFull,_hSharp,_hOrdU,_hPrepU,hN0,hFull0,hTr0,
    hDense0,hOrd0,hPrep0,hAU,hRowData,hMatrix,_hOff⟩ := hAny Y0 α hα
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hLocal
  let W : Opens U := ⟨(Subtype.val : U → X) ⁻¹' V,hVo.preimage continuous_subtype_val⟩
  have hCeq' : CU=(Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S) := hCeq
  have hCentres : (Subtype.val : W → U) ⁻¹' CU=
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C) := by
    rw [hCeq']
    ext y
    exact (hV y.property).symm
  let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
  let V1 := BlowupBiholomorphismLift.preOpen hβ U
  let V2 := BlowupBiholomorphismLift.preOpen hβU W
  let V0 := BlowupBiholomorphismLift.preOpen hα W
  obtain ⟨χ,hComp⟩ := nested_blowup_comparison hβ U hα W hCentres
  let q : V2 := ⟨(⟨z,hxU⟩ : V1),hxV⟩
  have hSets := nested_strict_dictionary hβ U hα W hCentres χ hComp
  have hLists := nested_boundary_dictionary hβ U hα W hCentres χ hComp
  let N0 := geoStrictTransform α CU NU
  let old0 := oldU.map (geoStrictTransform α CU)
  let born0 := bornU.map (geoStrictTransform α CU)++[α ⁻¹' CU]
  have hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → Y) ⁻¹' N')=
      χ ⁻¹' ((Subtype.val : V0 → Y0) ⁻¹' N0) := hSets.1 N
  have hz0 : (χ q).val ∈ N0 := (Set.ext_iff.mp hNC q).mp hz
  have hPreparedTarget := nested_prepared_order hn V1 V2 V0 χ hNext.1 hNext.2.1 hNext.2.2.1 hNext.2.2.2
    hN0 hFull0 hTr0 hDense0 hNC (hLists.1 old) (hLists.2 born) q hz
    (hOrd0 _ hz0) (hPrep0 _ hz0)
  let I' : Fin old.length → GermIdeal n Y := fun i =>
    restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
  let IU : Fin old.length → GermIdeal n U := fun i =>
    restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let DU := fun i => monomialPartAlong n NU (IU i) bornU
  let JU := fun i => nonmonomialPartAlong n NU (IU i) bornU
  let I0 : Fin old.length → GermIdeal n Y0 := fun i =>
    restrictOn n N0 (vanishingIdeal (n := n) (geoStrictTransform α CU ((Subtype.val : U → X) ⁻¹' old.get i)))
  let D0 := fun i => monomialPartAlong n N0 (I0 i) born0
  let J0 := fun i => nonmonomialPartAlong n N0 (I0 i) born0
  let eO' : Fin old.length → Fin old'.length := Fin.cast (by simp [old'])
  have hGet' (i : Fin old.length) : old'.get (eO' i)=geoStrictTransform β C (old.get i) := by
    simp [old',eO',List.get_eq_getElem]
  have hParts' (i : Fin old.length) := actual_old_parts_geometry (N := N') (old := old') (born := born') hn hNext.1 hNext.2.1
    hNext.2.2.1 hNext.2.2.2 (eO' i)
  have hRowGerms : ∀ (i : Fin old.length) (g : Y → ℂ),
      (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
        (I' i).mem z g) ∧
      (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
        (D' i).mem z g) ∧
      ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g) := by
    intro i g
    obtain ⟨_hcont,_hunit,_hAdmI,_hAdmD,hLawI0,hLawD0,hLawJ0,_hfactor,hcI0,_hnzI0,
      hcD0,_hnzD0,_hmD0,hcJ0,_hnzJ0,_hMPJ0⟩ := hRowData i
    have hcI' : (I' i).IsCoherent := by simpa only [oldTraceIdeal,hGet'] using (hParts' i).1
    have hcD' : (D' i).IsCoherent := by
      simpa only [oldMonomialPart,oldTraceIdeal,hGet'] using (hParts' i).2.2.2.2.1
    have hcJ' : (J' i).IsCoherent := by
      simpa only [oldResidualPart,oldTraceIdeal,hGet'] using (hParts' i).2.2.1
    have hOldSNC := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
    have hH := MonomialPart.isClosedSubmanifold_get hn hOldSNC i
    have hH' := MonomialPart.isClosedSubmanifold_get hn
      (isSNCDivisor_of_sublist hNext.2.1 (List.sublist_append_left old' born')) (eO' i)
    rw [hGet'] at hH'
    have hH0 : IsClosedSubmanifold n (geoStrictTransform α CU ((Subtype.val : U → X) ⁻¹' old.get i)) := by
      have h := MonomialPart.isClosedSubmanifold_get hn
        (isSNCDivisor_of_sublist hFull0 (List.sublist_append_left old0 born0))
        (Fin.cast (by simp [old0,oldU]) i)
      simpa only [old0,oldU,List.get_eq_getElem,List.getElem_map,Fin.val_cast] using h
    have hCanon := nested_parts_dictionary V1 V2 V0 χ hNext.1 hH' hN0 hH0
      hcD' hcJ' hcD0 hcJ0 hNC (hSets.1 (old.get i)) (hLists.2 born)
    have hSource := trace_parts_open_pullback born hN hH (hParts i).2.2.2.2.1 (hParts i).2.2.1 U
    have hMark : (if i ∈ properRows (A (β z)) then 1 else 0)=(if i ∈ P then 1 else 0) := by
      rw [hProper]
    let MI : MarkedIdeal n X := ⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩
    let MD : MarkedIdeal n X := ⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩
    let MJ : MarkedIdeal n X := ⟨N,[],oldResidualPart N old born i,0⟩
    have hMIU : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) MI=
        (⟨NU,bornU,IU i,if i ∈ properRows (A (β z)) then 1 else 0⟩ : MarkedIdeal n U) :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSource.1.symm hMark.symm
    have hMDU : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) MD=
        (⟨NU,bornU,DU i,if i ∈ properRows (A (β z)) then 1 else 0⟩ : MarkedIdeal n U) :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSource.2.1.symm hMark.symm
    have hMJU : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) MJ=
        (⟨NU,[],JU i,0⟩ : MarkedIdeal n U) :=
      MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSource.2.2.symm rfl
    have hModelI : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : U → X) MI).geoTransform CU α).ideal=I0 i := by
      rw [hMIU]
      exact hLawI0
    have hModelD : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : U → X) MD).geoTransform CU α).ideal=D0 i := by
      rw [hMDU]
      exact hLawD0.symm
    have hModelJ : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : U → X) MJ).geoTransform CU α).ideal=J0 i := by
      rw [hMJU]
      exact hLawJ0.symm
    have hcTI := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
      MI hN (hParts i).1 hβ hCN
    have hcTD := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
      MD hN (hParts i).2.2.2.2.1 hβ hCN
    have hcTJ := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
      MJ hN (hParts i).2.2.1 hβ hCN
    exact ⟨controlled_germ_of_nested_model hβ U hα W hCentres MI (hParts i).1
        (I' i) (I0 i) hcI' hcI0 hcTI hModelI χ hComp hCanon.1 q g,
      controlled_germ_of_nested_model hβ U hα W hCentres MD (hParts i).2.2.2.2.1
        (D' i) (D0 i) hcD' hcD0 hcTD hModelD χ hComp hCanon.2.1 q g,
      controlled_germ_of_nested_model hβ U hα W hCentres MJ (hParts i).2.2.1
        (J' i) (J0 i) hcJ' hcJ0 hcTJ hModelJ χ hComp hCanon.2.2 q g⟩
  let At : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
  let AU : Fin old.length → Fin bornU.length → ℕ := fun i j =>
    divExpAlong n NU (DU i) (bornU.get j) (⟨β z,hxU⟩ : U)
  let R := Finset.univ.filter (fun j => (χ q).val ∈ geoStrictTransform α CU (bornU.get j))
  let B := transformFamily 1 SU R AU
  have hPoint : α (χ q).val=(⟨β z,hxU⟩ : U) := congrArg Subtype.val (congrFun hComp q)
  obtain ⟨hR,hPivot,hMatRows⟩ := hMatrix (χ q).val hz0 hPoint
  have hLenO : old'.length=old0.length := by simp [old',old0,oldU]
  have hLenB : born'.length=born0.length := by simp [born',born0,bornU]
  have hCols := nested_canonical_columns hn V1 V2 V0 χ hNext.1 hNext.2.1 hNext.2.2.1 hNext.2.2.2
    hN0 hFull0 hTr0 hDense0 hLenO hLenB hNC (hLists.1 old) (hLists.2 born) q
  have hCanonical (i : Fin old.length) (j : Fin born'.length) :
      At i j=divExpAlong n N0 (D0 i) (born0.get (Fin.cast hLenB j)) (χ q).val := by
    have h := hCols (eO' i) j
    simpa only [At,D',I',D0,I0,q,oldMonomialPart,oldTraceIdeal,old',old0,oldU,eO',Fin.val_cast,
      List.get_eq_getElem,List.getElem_map] using h
  have hTargetLen : born'.length=bornU.length+1 := by simp [born',bornU]
  have hAtB (i : Fin old.length) (j : Fin born'.length) : At i j=B i (Fin.cast hTargetLen j) := by
    let j0 : Fin born0.length := Fin.cast hLenB j
    have hIndex : Fin.cast (show born0.length=bornU.length+1 by simp [born0]) j0=
        Fin.cast hTargetLen j := Fin.ext rfl
    calc
      At i j=divExpAlong n N0 (D0 i) (born0.get j0) (χ q).val := hCanonical i j
      _ = B i (Fin.cast hTargetLen j) := by
        have h := (hMatRows i j0).2
        change divExpAlong n N0 (D0 i) (born0.get j0) (χ q).val=
          B i (Fin.cast (show born0.length=bornU.length+1 by simp [born0]) j0) at h
        rwa [hIndex] at h
  let eSource : Fin born.length ≃ Fin bornU.length := finCongr (by simp [bornU])
  have hSourceInv := column_equiv_invariants AU (A (β z)) eSource (fun i j => (hAU i j).symm)
  have hTargetInv := column_equiv_invariants B At (finCongr hTargetLen) hAtB
  have hActAU : (properRows AU).Nonempty := by rw [←hSourceInv.1]; exact hAct
  refine ⟨hPreparedTarget.1,hPreparedTarget.2,hRowGerms,?_,?_,?_,?_,?_⟩
  · rw [hTargetInv.1,hSourceInv.1]
    exact proper_transform_subset AU SU R
  · intro hNu hTau
    have hNuAU : nuOne AU=0 := hSourceInv.2.2.symm.trans hNu
    have hTauB : tauD B=tauD AU := hTargetInv.2.1.symm.trans (hTau.trans hSourceInv.2.1)
    have hRestrict : restrictIncidence B Finset.univ=B := by
      funext i j
      simp [restrictIncidence]
    have hTauRestrict : tauD (restrictIncidence B Finset.univ)=tauD AU := by rw [hRestrict]; exact hTauB
    have hTop := HironakaG4ZeroResidualTopTransform.actual_transform_incidence_nu_zero_of_tau_eq
      AU SU R Finset.univ hActAU hNuAU hTauRestrict
    have hNuB := hTop.2
    change nuOne (restrictIncidence B Finset.univ)=0 at hNuB
    rw [hRestrict] at hNuB
    exact hTargetInv.2.2.trans hNuB

  · intro Bound hBound i j
    have hAUbound (i : Fin old.length) (j : Fin bornU.length) : AU i j ≤ Bound := by
      have hh : AU i (eSource (eSource.symm j)) = A (β z) i (eSource.symm j) :=
        hAU i (eSource.symm j)
      simp only [Equiv.apply_symm_apply] at hh
      rw [hh]
      exact hBound i (eSource.symm j)
    have hh := transformFamily_uniform_bound AU SU R 1 Bound hAUbound i (Fin.cast hTargetLen j)
    change At i j ≤ max Bound (born.length * Bound)
    rw [hAtB i j]
    simpa only [bornU,List.length_map] using hh
  · intro hChain
    have hAUChain : RowsChain AU := by
      apply rowsChain_of_column_equiv (A (β z)) AU eSource.symm ?_ hChain
      intro i j
      have hh : AU i (eSource (eSource.symm j)) = A (β z) i (eSource.symm j) :=
        hAU i (eSource.symm j)
      simpa only [Equiv.apply_symm_apply] using hh
    have hBChain : RowsChain B := transformFamily_rowsChain AU SU R 1 hAUChain
    change RowsChain At
    apply rowsChain_of_column_equiv B At (finCongr hTargetLen) ?_ hBChain
    exact hAtB


  · obtain ⟨p₀,hp₀,hpR⟩ := hPivot
    refine ⟨bornU.length,eSource,finCongr hTargetLen,AU,SU,R,p₀,?_,?_,?_,?_,?_,hp₀,hpR,?_,?_⟩
    · rfl
    · intro j
      rfl
    · intro j
      rfl
    · intro j hj
      have hh := hR hj
      have hmem : β z ∈ born.get (eSource.symm j) := by
        have hh' := (Finset.mem_filter.mp hh).2
        simpa [bornU,eSource] using hh'
      exact Finset.mem_map.mpr ⟨eSource.symm j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem⟩,
        eSource.apply_symm_apply j⟩
    · intro j
      have hh := Set.ext_iff.mp (hSets.1 (born.get j)) q
      simpa [R,bornU,eSource,q,List.get_eq_getElem] using hh.symm
    · intro i j
      have heq : eSource j=e j := Fin.ext rfl
      rw [heq]
      exact hAU i j
    · exact hAtB


theorem actual_target_prepared_over_selected_with_matrix_intrinsic (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hCN : C ⊆ N)
    (hProper : ∀ x ∈ C,
      properRows (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=P)
    {β : Y → X} (hβ : IsBlowupAlong n (C) β)
    (hNext : let C := C
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β (C) N)
    (hzC : β z ∈ C)
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => β z ∈ born.get j))
    (hFeas : ∀ i ∈ P,1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z))
    (hLocal : ∀ᶠ y in 𝓝 (β z),y ∈ C ↔ y ∈ N ∧ y ∈ memberInter born S) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    let A' : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
    let A := fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z)
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      (∀ (i : Fin old.length) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g)) ∧
      properRows A' ⊆ properRows A ∧
      (nuOne A=0 → tauD A'=tauD A → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (born.length * B)) ∧
      (RowsChain A → RowsChain A') ∧
      ∃ (b₀ : ℕ) (eSrc : Fin born.length ≃ Fin b₀)
        (eDst : Fin born'.length ≃ Fin (b₀+1))
        (A₀ : Fin old.length → Fin b₀ → ℕ) (S₀ R₀ : Finset (Fin b₀)) (p₀ : Fin b₀),
        S₀ = S.map eSrc.toEmbedding ∧ (∀ j, (eSrc j).val=j.val) ∧ (∀ j, (eDst j).val=j.val) ∧ R₀ ⊆ (Finset.univ.filter (fun j => β z ∈ born.get j)).map eSrc.toEmbedding ∧ (∀ j, eSrc j ∈ R₀ ↔ z ∈ geoStrictTransform β C (born.get j)) ∧ p₀ ∈ S₀ ∧ p₀ ∉ R₀ ∧
        (∀ i j,A₀ i (eSrc j)=A i j) ∧
        ∀ i j,A' i j=transformFamily 1 S₀ R₀ A₀ i (eDst j) := by
  exact actual_target_prepared_over_selected_with_matrix_intrinsic_pointwise hn hN hE hTr hdense hOrd hPrepared
    P hP hCN hβ hNext z hz hzC (hProper _ hzC) S hS hSJ hFeas hLocal

theorem actual_target_prepared_over_selected_with_matrix_pointwise (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hCN : C ⊆ N)
    {β : Y → X} (hβ : IsBlowupAlong n (C) β)
    (hNext : let C := C
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β (C) N)
    (hzC : β z ∈ C)
    (hProper : properRows (fun i j =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z))=P)
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => β z ∈ born.get j))
    (hFeas : ∀ i ∈ P,1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z))
    (hLocal : ∀ᶠ y in 𝓝 (β z),y ∈ C ↔ y ∈ N ∧ y ∈ memberInter born S) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    let A' : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
    let A := fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z)
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      (∀ (i : Fin old.length) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g)) ∧
      properRows A' ⊆ properRows A ∧
      (nuOne A=0 → tauD A'=tauD A → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (born.length * B)) ∧
      (RowsChain A → RowsChain A') ∧
      ∃ (b₀ : ℕ) (eSrc : Fin born.length ≃ Fin b₀)
        (eDst : Fin born'.length ≃ Fin (b₀+1))
        (A₀ : Fin old.length → Fin b₀ → ℕ) (S₀ R₀ : Finset (Fin b₀)) (p₀ : Fin b₀),
        S₀ = S.map eSrc.toEmbedding ∧ p₀ ∈ S₀ ∧ p₀ ∉ R₀ ∧
        (∀ i j,A₀ i (eSrc j)=A i j) ∧
        ∀ i j,A' i j=transformFamily 1 S₀ R₀ A₀ i (eDst j) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,b₀,eSrc,eDst,A₀,S₀,R₀,p₀,hSet,_hSourceVal,_hTargetVal,_hR,_hIntrinsic,hp,hpR,hSrc,hDst⟩ :=
    actual_target_prepared_over_selected_with_matrix_intrinsic_pointwise hn hN hE hTr hdense hOrd hPrepared
      P hP hCN hβ hNext z hz hzC hProper S hS hSJ hFeas hLocal
  exact ⟨h1,h2,h3,h4,h5,h6,h7,b₀,eSrc,eDst,A₀,S₀,R₀,p₀,hSet,hp,hpR,hSrc,hDst⟩


theorem actual_target_prepared_over_selected_with_matrix (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hCN : C ⊆ N)
    (hProper : ∀ x ∈ C,
      properRows (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=P)
    {β : Y → X} (hβ : IsBlowupAlong n (C) β)
    (hNext : let C := C
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β (C) N)
    (hzC : β z ∈ C)
    (S : Finset (Fin born.length)) (hS : S.Nonempty)
    (hSJ : S ⊆ Finset.univ.filter (fun j => β z ∈ born.get j))
    (hFeas : ∀ i ∈ P,1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z))
    (hLocal : ∀ᶠ y in 𝓝 (β z),y ∈ C ↔ y ∈ N ∧ y ∈ memberInter born S) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    let A' : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
    let A := fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z)
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      (∀ (i : Fin old.length) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g)) ∧
      properRows A' ⊆ properRows A ∧
      (nuOne A=0 → tauD A'=tauD A → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (born.length * B)) ∧
      (RowsChain A → RowsChain A') ∧
      ∃ (b₀ : ℕ) (eSrc : Fin born.length ≃ Fin b₀)
        (eDst : Fin born'.length ≃ Fin (b₀+1))
        (A₀ : Fin old.length → Fin b₀ → ℕ) (S₀ R₀ : Finset (Fin b₀)) (p₀ : Fin b₀),
        S₀ = S.map eSrc.toEmbedding ∧ p₀ ∈ S₀ ∧ p₀ ∉ R₀ ∧
        (∀ i j,A₀ i (eSrc j)=A i j) ∧
        ∀ i j,A' i j=transformFamily 1 S₀ R₀ A₀ i (eDst j) := by
  exact actual_target_prepared_over_selected_with_matrix_pointwise hn hN hE hTr hdense hOrd hPrepared
    P hP hCN hβ hNext z hz hzC (hProper _ hzC) S hS hSJ hFeas hLocal

theorem actual_target_prepared_over_selected (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty)
    (hCN : C ⊆ N)
    (hProper : ∀ x ∈ C,
      properRows (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=P)
    (hSelected : ∀ x ∈ C, ∃ S : Finset (Fin born.length), S.Nonempty ∧
      S ⊆ Finset.univ.filter (fun j => x ∈ born.get j) ∧
      (∀ i ∈ P,1 ≤ ∑ j ∈ S,divExpAlong n N (oldMonomialPart N old born i) (born.get j) x) ∧
      ∀ᶠ y in 𝓝 x,y ∈ C ↔ y ∈ N ∧ y ∈ memberInter born S)
    {β : Y → X} (hβ : IsBlowupAlong n (C) β)
    (hNext : let C := C
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β (C) N)
    (hzC : β z ∈ C) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    let A' : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
    let A := fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z)
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      (∀ (i : Fin old.length) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g)) ∧
      properRows A' ⊆ properRows A ∧
      (nuOne A=0 → tauD A'=tauD A → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (born.length * B)) ∧
      (RowsChain A → RowsChain A') := by
  obtain ⟨S,hS,hSJ,hFeas,hLocal⟩ := hSelected (β z) hzC
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,_hMatrix⟩ :=
    actual_target_prepared_over_selected_with_matrix hn hN hE hTr hdense hOrd hPrepared
      P hP hCN hProper hβ hNext z hz hzC S hS hSJ hFeas hLocal
  exact ⟨h1,h2,h3,h4,h5,h6,h7⟩

private theorem actual_target_prepared_over_maximum (hn : 0<n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) (Sigma : GermIdeal n X)
    (hM : (⟨N,born,Sigma,1⟩ : MarkedIdeal n X).IsWellFormed)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N Sigma x) (hMono : IsMonomialAlong n N Sigma born)
    (hProper : ∀ x ∈ maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X),
      properRows (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=P)
    (hRows : ∀ i ∈ P,maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X) ⊆
      cosupport n N (oldMonomialPart N old born i) 1)
    {β : Y → X} (hβ : IsBlowupAlong n (maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) β)
    (hNext : let C := maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β (maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) N)
    (hzC : β z ∈ maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) :
    let C := maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    let A' : Fin old.length → Fin born'.length → ℕ := fun i j => divExpAlong n N' (D' i) (born'.get j) z
    let A := fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) (β z)
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      (∀ (i : Fin old.length) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g)) ∧
      properRows A' ⊆ properRows A ∧
      (nuOne A=0 → tauD A'=tauD A → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (born.length * B)) ∧
      (RowsChain A → RowsChain A') := by
  have hCN : maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X) ⊆ N := fun _ hx => hx.1.1
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hSelected (x : X) (hx : x ∈ maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) :=
    maximum_selected_feasible hn (⟨N,born,Sigma,1⟩ : MarkedIdeal n X) hM hnz hMono
      (oldMonomialPart N old born) (fun i => (hParts i).2.2.2.2.1)
      (fun i => (hParts i).2.2.2.2.2.1) (fun i => (hParts i).2.2.2.2.2.2.1)
      P hP hRows hx
  exact actual_target_prepared_over_selected hn hN hE hTr hdense hOrd hPrepared
    P hP hCN hProper hSelected hβ hNext z hz hzC

theorem actual_target_prepared_off_centre (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    {β : Y → X} (hβ : IsBlowupAlong n C β) (hCN : C ⊆ N)
    (hNext : let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    (z : Y) (hz : z ∈ geoStrictTransform β C N) (hzC : β z ∉ C) :
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧
      ∀ (i : Fin old.length) (d : ℕ) (g : Y → ℂ),
        (((⟨N,born,oldTraceIdeal N old i,d⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (I' i).mem z g) ∧
        (((⟨N,born,oldMonomialPart N old born i,d⟩ : MarkedIdeal n X).geoTransform C β).ideal.mem z g ↔
          (D' i).mem z g) ∧
        ((nextTotalMarked N (oldResidualPart N old born i) C β).ideal.mem z g ↔ (J' i).mem z g) := by
  let N' := geoStrictTransform β C N
  let old' := old.map (geoStrictTransform β C)
  let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
  let U : Opens X := ⟨Cᶜ,hβ.1.1.isOpen_compl⟩
  let NU := (Subtype.val : U → X) ⁻¹' N
  let oldU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let bornU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  obtain ⟨hNU,hFullU,hTrU,hDenseU⟩ := full_geometry_open hN hE hTr hdense U
  let α : CMfd.of (n := n) U → U := id
  have hα : IsBlowupAlong n (∅ : Set U) α :=
    BlowupExistenceCodimOne.isBlowupAlong_id_empty
  let W : Opens U := ⊤
  have hCentres : (Subtype.val : W → U) ⁻¹' (∅ : Set U)=
      (Subtype.val : W → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' C) := by
    ext y
    constructor
    · exact False.elim
    · intro hy
      exact (y.val.property hy).elim
  let hβU := BlowupBiholomorphismLift.isBlowupAlong_restrictMap hβ U
  let V1 := BlowupBiholomorphismLift.preOpen hβ U
  let V2 := BlowupBiholomorphismLift.preOpen hβU W
  let V0 := BlowupBiholomorphismLift.preOpen hα W
  obtain ⟨χ,hComp⟩ := nested_blowup_comparison hβ U hα W hCentres
  let q : V2 := ⟨(⟨z,hzC⟩ : V1),Set.mem_univ _⟩
  have hSets := nested_strict_dictionary hβ U hα W hCentres χ hComp
  have hLists := nested_boundary_dictionary hβ U hα W hCentres χ hComp
  let N0 := geoStrictTransform α ∅ NU
  let old0 := oldU.map (geoStrictTransform α ∅)
  let born0 := bornU.map (geoStrictTransform α ∅)++[α ⁻¹' ∅]
  have hNid : N0=NU := ContactCanonicalAlong.geoStrictTransform_empty continuous_id hNU.1
  have hIdList (L : List (Set U)) (hClosed : ∀ H ∈ L,IsClosed H) :
      L.map (geoStrictTransform α ∅)=L := by
    calc
      L.map (geoStrictTransform α ∅)=L.map id := List.map_congr_left
        (fun H hH => ContactCanonicalAlong.geoStrictTransform_empty continuous_id (hClosed H hH))
      _ = L := List.map_id L
  have hOldid : old0=oldU := hIdList oldU
    (fun H hH => hFullU.1 H (List.mem_append_left bornU hH))
  have hBornid : born0=bornU++[∅] := by
    rw [show born0=bornU.map (geoStrictTransform α ∅)++[α ⁻¹' ∅] from rfl,
      hIdList bornU (fun H hH => hFullU.1 H (List.mem_append_right oldU hH))]
    rfl
  have hEmpty : IsClosedSubmanifold n (∅ : Set U) := ⟨isClosed_empty,by simp⟩
  have hModel := actual_next_full_geometry (X := CMfd.of (n := n) U) hn hNU hFullU hTrU hDenseU
    hEmpty (empty_subset NU) (fun _ hx => hx.elim) (fun _ hx => hx.elim) hα
  have hNC : (Subtype.val : V2 → V1) ⁻¹' ((Subtype.val : V1 → Y) ⁻¹' N')=
      χ ⁻¹' ((Subtype.val : V0 → U) ⁻¹' N0) := hSets.1 N
  have hz0 : (χ q).val ∈ N0 := (Set.ext_iff.mp hNC q).mp hz
  have hzNU : (χ q).val ∈ NU := hNid ▸ hz0
  let cO : Fin oldU.length → Fin old.length := Fin.cast (by simp [oldU])
  let cB : Fin bornU.length → Fin born.length := Fin.cast (by simp [bornU])
  have hOldGet (i : Fin oldU.length) : oldU.get i=(Subtype.val : U → X) ⁻¹' old.get (cO i) := by
    simp [oldU,cO,List.get_eq_getElem]
  have hBornGet (j : Fin bornU.length) : bornU.get j=(Subtype.val : U → X) ⁻¹' born.get (cB j) := by
    simp [bornU,cB,List.get_eq_getElem]
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hPartsU (i : Fin oldU.length) := actual_old_parts_geometry
    (X := CMfd.of (n := n) U) hn hNU hFullU hTrU hDenseU i
  have hOldSNC := isSNCDivisor_of_sublist hE (List.sublist_append_left old born)
  have hJU (i : Fin oldU.length) : oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i=
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born (cO i)) := by
    have hTrace := HironakaSharpActualStrictTraceOpenNonmonomial.actual_normalized_trace_whole_open_pullback
      hN (MonomialPart.isClosedSubmanifold_get hn hOldSNC (cO i)) U
    have hPart := parts_open_pullback N (oldTraceIdeal N old (cO i)) born
      (hParts (cO i)).1 (hParts (cO i)).2.2.2.2.1 (hParts (cO i)).2.2.1 U
    change nonmonomialPartAlong n NU (restrictOn n NU (vanishingIdeal (n := n) (oldU.get i))) bornU=_
    rw [hOldGet,hTrace]
    exact hPart.2
  have hOrdU : ∀ i,ordinaryTraceOrder NU
      (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) (χ q).val ≤ 1 := by
    intro i
    by_contra ho
    have hTwo : 2 ≤ ordinaryTraceOrder NU
        (oldResidualPart (X := CMfd.of (n := n) U) NU oldU bornU i) (χ q).val := by omega
    have hCos := (ordinaryTraceOrder_cosupport_iff hNU (hPartsU i).2.2.1
      (hPartsU i).2.2.2.1 hzNU 2).mpr hTwo
    rw [hJU,cosupport_pullback_of_local
      (fun y : U => ⟨DerivativeIdealAlongEtale.openInv U y,DerivativeIdealAlongEtale.isLocalInverseAt_val U y⟩)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hParts (cO i)).2.2.1 hg)] at hCos
    have hTwo0 := (ordinaryTraceOrder_cosupport_iff hN (hParts (cO i)).2.2.1
      (hParts (cO i)).2.2.2.1 hzNU 2).mp hCos
    have hBound := hOrd (χ q).val.val hzNU (cO i)
    omega
  have hFrame : FreeFrameAt (X := CMfd.of (n := n) U) NU
      (fun a => (Subtype.val : U → X) ⁻¹' preparedSupport N old born a) (χ q).val :=
    (freeFrameAt_open_iff U).mpr (hPrepared (χ q).val.val hzNU)
  let c := Sum.map cO cB
  have hc : Function.Injective c := Sum.map_injective.mpr
    ⟨Fin.cast_injective _,Fin.cast_injective _⟩
  have hSupport (a : Fin oldU.length ⊕ Fin bornU.length) :
      preparedSupport (X := CMfd.of (n := n) U) NU oldU bornU a=
        (Subtype.val : U → X) ⁻¹' preparedSupport N old born (c a) := by
    cases a with
    | inl i =>
      simp only [preparedSupport,Sum.elim_inl,c,Sum.map_inl]
      rw [hJU,BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val (hParts (cO i)).2.2.1]
      rfl
    | inr j =>
      simp only [preparedSupport,Sum.elim_inr,c,Sum.map_inr]
      rw [hBornGet]
      rfl
  have hPrepU : IsPreparedResidualSNCAt (X := CMfd.of (n := n) U) NU oldU bornU (χ q).val :=
    freeFrameAt_reindex c hc hSupport hFrame
  have hOrd0 : ∀ i,ordinaryTraceOrder N0 (oldResidualPart N0 old0 born0 i) (χ q).val ≤ 1 := by
    rw [hNid,hOldid,hBornid]
    intro i
    simpa only [oldResidualPart,MonomialPartEtale.nonmonomialPartAlong_append_empty] using hOrdU i
  have hPrep0 : IsPreparedResidualSNCAt N0 old0 born0 (χ q).val := by
    rw [hNid,hOldid,hBornid]
    exact prepared_append_empty hn hPrepU
  have hPreparedTarget := nested_prepared_order hn V1 V2 V0 χ hNext.1 hNext.2.1 hNext.2.2.1 hNext.2.2.2
    hModel.1 hModel.2.1 hModel.2.2.1 hModel.2.2.2 hNC (hLists.1 old) (hLists.2 born)
    q hz hOrd0 hPrep0
  let I' : Fin old.length → GermIdeal n Y := fun i =>
    restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
  let IU : Fin old.length → GermIdeal n U := fun i =>
    restrictOn n NU (vanishingIdeal (n := n) ((Subtype.val : U → X) ⁻¹' old.get i))
  let DU := fun i => monomialPartAlong n NU (IU i) bornU
  let JU := fun i => nonmonomialPartAlong n NU (IU i) bornU
  let I0 : Fin old.length → GermIdeal n U := fun i =>
    restrictOn n N0 (vanishingIdeal (n := n) (geoStrictTransform α ∅ ((Subtype.val : U → X) ⁻¹' old.get i)))
  let D0 := fun i => monomialPartAlong n N0 (I0 i) born0
  let J0 := fun i => nonmonomialPartAlong n N0 (I0 i) born0
  let eO' : Fin old.length → Fin old'.length := Fin.cast (by simp [old'])
  have hGet' (i : Fin old.length) : old'.get (eO' i)=geoStrictTransform β C (old.get i) := by
    simp [old',eO',List.get_eq_getElem]
  have hParts' (i : Fin old.length) := actual_old_parts_geometry (N := N') (old := old') (born := born')
    hn hNext.1 hNext.2.1 hNext.2.2.1 hNext.2.2.2 (eO' i)
  refine ⟨hPreparedTarget.1,hPreparedTarget.2,?_⟩
  intro i d g
  have hcI' : (I' i).IsCoherent := by simpa only [oldTraceIdeal,hGet'] using (hParts' i).1
  have hcD' : (D' i).IsCoherent := by
    simpa only [oldMonomialPart,oldTraceIdeal,hGet'] using (hParts' i).2.2.2.2.1
  have hcJ' : (J' i).IsCoherent := by
    simpa only [oldResidualPart,oldTraceIdeal,hGet'] using (hParts' i).2.2.1
  have hH := MonomialPart.isClosedSubmanifold_get hn hOldSNC i
  have hHU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hH U
  have hH' := MonomialPart.isClosedSubmanifold_get hn
    (isSNCDivisor_of_sublist hNext.2.1 (List.sublist_append_left old' born')) (eO' i)
  rw [hGet'] at hH'
  have hHid : geoStrictTransform α ∅ ((Subtype.val : U → X) ⁻¹' old.get i)=
      (Subtype.val : U → X) ⁻¹' old.get i :=
    ContactCanonicalAlong.geoStrictTransform_empty continuous_id hHU.1
  have hH0 : IsClosedSubmanifold n (geoStrictTransform α ∅ ((Subtype.val : U → X) ⁻¹' old.get i)) :=
    hHid.symm ▸ hHU
  have hI0id : I0 i=IU i := by change restrictOn n N0 (vanishingIdeal (n := n) _)=_; rw [hNid,hHid]
  have hD0id : D0 i=DU i := by
    change monomialPartAlong n N0 (I0 i) born0=_
    rw [hNid,hI0id,hBornid,MonomialPartEtale.monomialPartAlong_append_empty]
  have hJ0id : J0 i=JU i := by
    change nonmonomialPartAlong n N0 (I0 i) born0=_
    rw [hNid,hI0id,hBornid,MonomialPartEtale.nonmonomialPartAlong_append_empty]
  have hSource := trace_parts_open_pullback born hN hH (hParts i).2.2.2.2.1 (hParts i).2.2.1 U
  have hSourceI : IU i=GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldTraceIdeal N old i) := hSource.1
  have hSourceD : DU i=GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldMonomialPart N old born i) := hSource.2.1
  have hSourceJ : JU i=GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) := hSource.2.2
  have hcIU : (IU i).IsCoherent := by rw [hSourceI]; exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (hParts i).1
  have hcDU : (DU i).IsCoherent := by rw [hSourceD]; exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (hParts i).2.2.2.2.1
  have hcJU : (JU i).IsCoherent := by rw [hSourceJ]; exact GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val (hParts i).2.2.1
  have hcI0 : (I0 i).IsCoherent := hI0id.symm ▸ hcIU
  have hcD0 : (D0 i).IsCoherent := hD0id.symm ▸ hcDU
  have hcJ0 : (J0 i).IsCoherent := hJ0id.symm ▸ hcJU
  have hCanon := nested_parts_dictionary V1 V2 V0 χ hNext.1 hH' hModel.1 hH0
    hcD' hcJ' hcD0 hcJ0 hNC (hSets.1 (old.get i)) (hLists.2 born)
  let MI : MarkedIdeal n X := ⟨N,born,oldTraceIdeal N old i,d⟩
  let MD : MarkedIdeal n X := ⟨N,born,oldMonomialPart N old born i,d⟩
  let MJ : MarkedIdeal n X := ⟨N,[],oldResidualPart N old born i,0⟩
  have hMIU : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) MI=
      (⟨NU,bornU,IU i,d⟩ : MarkedIdeal n U) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSource.1.symm rfl
  have hMDU : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) MD=
      (⟨NU,bornU,DU i,d⟩ : MarkedIdeal n U) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSource.2.1.symm rfl
  have hMJU : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) MJ=
      (⟨NU,[],JU i,0⟩ : MarkedIdeal n U) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSource.2.2.symm rfl
  have hModelI : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) MI).geoTransform ∅ α).ideal=I0 i := by
    rw [hMIU]
    exact (id_empty_transform_normalized _ hNU.1 hcIU
      (normalized_trace (X := CMfd.of (n := n) U) NU ((Subtype.val : U → X) ⁻¹' old.get i))).trans hI0id.symm
  have hModelD : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) MD).geoTransform ∅ α).ideal=D0 i := by
    rw [hMDU]
    exact (id_empty_transform_normalized _ hNU.1 hcDU
      (normalized_of_carrierIdeal_le (X := CMfd.of (n := n) U) (DU i) hcDU
        (carrierIdeal_le_monomialPart (X := CMfd.of (n := n) U) NU (IU i) bornU))).trans hD0id.symm
  have hModelJ : ((MarkedIdealBiholomorphism.MarkedIdeal.pullback
      (Subtype.val : U → X) MJ).geoTransform ∅ α).ideal=J0 i := by
    rw [hMJU]
    exact (id_empty_transform_normalized _ hNU.1 hcJU (normalized_nonmonomial (X := CMfd.of (n := n) U) NU (IU i) bornU)).trans hJ0id.symm
  have hcTI := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    MI hN (hParts i).1 hβ hCN
  have hcTD := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    MD hN (hParts i).2.2.2.2.1 hβ hCN
  have hcTJ := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    MJ hN (hParts i).2.2.1 hβ hCN
  exact ⟨controlled_germ_of_nested_model hβ U hα W hCentres MI (hParts i).1
      (I' i) (I0 i) hcI' hcI0 hcTI hModelI χ hComp hCanon.1 q g,
    controlled_germ_of_nested_model hβ U hα W hCentres MD (hParts i).2.2.2.2.1
      (D' i) (D0 i) hcD' hcD0 hcTD hModelD χ hComp hCanon.2.1 q g,
    controlled_germ_of_nested_model hβ U hα W hCentres MJ (hParts i).2.2.1
      (J' i) (J0 i) hcJ' hcJ0 hcTJ hModelJ χ hComp hCanon.2.2 q g⟩

/-- Equal ideal germs at all nearby carrier points yield equal exponents at
this point, with no global equality of ideals. -/
private theorem divExpAlong_eq_of_eventual_germs {N H : Set X} {I J : GermIdeal n X} {x : X}
    (h : ∀ᶠ y in 𝓝 x,y ∈ N → ∀ g,I.mem y g ↔ J.mem y g) :
    divExpAlong n N I H x=divExpAlong n N J H x := by
  have hDiv (e : ℕ) : IsDivNearAlong n N I H e x ↔ IsDivNearAlong n N J H e x := by
    constructor <;> intro he
    · filter_upwards [h,he] with y hy he' hyN hyH
      have hc := he' hyN hyH
      refine ⟨hyN,?_⟩
      intro g hg
      exact hc.2 g ((hy hyN g).mpr hg)
    · filter_upwards [h,he] with y hy he' hyN hyH
      have hc := he' hyN hyH
      refine ⟨hyN,?_⟩
      intro g hg
      exact hc.2 g ((hy hyN g).mp hg)
  have hex : (∃ e,¬IsDivNearAlong n N I H (e+1) x) ↔
      ∃ e,¬IsDivNearAlong n N J H (e+1) x := exists_congr fun e => not_congr (hDiv (e+1))
  by_cases hEx : ∃ e,¬IsDivNearAlong n N I H (e+1) x
  · have hEx' := hex.mp hEx
    simp only [divExpAlong,dif_pos hEx,dif_pos hEx']
    exact Nat.find_congr' fun {e} => not_congr (hDiv (e+1))
  · have hEx' : ¬∃ e,¬IsDivNearAlong n N J H (e+1) x := fun he => hEx (hex.mpr he)
    simp only [divExpAlong,dif_neg hEx,dif_neg hEx']

/-- Off an arbitrary admissible center, every actual old-row exponent is
unchanged on old born columns and zero on the new exceptional column. -/
theorem actual_old_row_columns_off_centre (hn : 0<n) {N C : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old++born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (hCN : C ⊆ N) (hCNC : HasNormalCrossings n C (old++born))
    {β : Y → X} (hβ : IsBlowupAlong n C β)
    (hNext : let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H))
    {z : Y} (hz : z ∈ geoStrictTransform β C N) (hzC : β z ∉ C) :
    let N' := geoStrictTransform β C N
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let D' : Fin old.length → GermIdeal n Y := fun i => monomialPartAlong n N'
      (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))) born'
    ∀ i : Fin old.length,∀ j : Fin born'.length,
      divExpAlong n N' (D' i) (born'.get j) z =
      appendAbsentRow (fun k => divExpAlong n N (oldMonomialPart N old born i) (born.get k) (β z))
        (Fin.cast (by simp [born']) j) := by
  dsimp only
  let N' := geoStrictTransform β C N
  let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
  let D' : Fin old.length → GermIdeal n Y := fun i => monomialPartAlong n N'
    (restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))) born'
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hCBorn : HasNormalCrossings n C born :=
    hasNormalCrossings_of_forall_mem hCNC (List.sublist_append_right old born).subset
  have hOff : ∀ᶠ y in 𝓝 z,β y ∉ C :=
    hβ.contMDiff.continuous.continuousAt.tendsto.eventually (hβ.1.1.isOpen_compl.mem_nhds hzC)
  intro i j
  let M : MarkedIdeal n X := ⟨N,born,oldMonomialPart N old born i,0⟩
  have hParts := actual_old_parts_geometry hn hN hE hTr hdense i
  have hc : M.ideal.IsCoherent := hParts.2.2.2.2.1
  have hWF : M.IsWellFormed := ⟨hN,hc,hBorn,hTr⟩
  have hAdm : M.IsAdmissibleCentre C := by
    refine ⟨hβ.1,?_,hCBorn⟩
    change C ⊆ cosupport n N (oldMonomialPart N old born i) 0
    rw [cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg)]
    exact hCN
  have hGerms : ∀ᶠ y in 𝓝 z,y ∈ N' → ∀ g,(D' i).mem y g ↔ (M.geoTransform C β).ideal.mem y g := by
    filter_upwards [hOff] with y hy hyN g
    have h := actual_target_prepared_off_centre hn hN hE hTr hdense hOrd hPrepared hβ hCN hNext y hyN hy
    exact ((h.2.2 i 0 g).2.1).symm
  have hExp := divExpAlong_eq_of_eventual_germs (H := born'.get j) hGerms
  have hCanon := HironakaG4SelectedBornCanonicalColumns.canonical_columns_geoTransform_of_notMem
    hn hWF hParts.2.2.2.2.2.1 hParts.2.2.2.2.2.2.1 hAdm hβ hz hzC j
  exact hExp.trans hCanon

private theorem normalized_ideal_eq_of_carrier_germs {N : Set X} (hN : IsClosed N)
    {I K : GermIdeal n X} (hcI : I.IsCoherent) (hcK : K.IsCoherent)
    (hNI : restrictOn n N I=I) (hNK : restrictOn n N K=K)
    (hAt : ∀ x ∈ N,∀ g,I.mem x g ↔ K.mem x g) : I=K := by
  ext x g
  by_cases hx : x ∈ N
  · exact hAt x hx g
  · constructor
    · intro hg
      exact normalized_mem_of_notMem hN hNK hx (GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)
    · intro hg
      exact normalized_mem_of_notMem hN hNI hx (GermIdeal.IsCoherent.holomorphicAt_mem hcK hg)

private theorem actual_global_rows (hn : 0<n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old++born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old++born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) (Sigma : GermIdeal n X)
    (hM : (⟨N,born,Sigma,1⟩ : MarkedIdeal n X).IsWellFormed)
    (hnz : ∀ x ∈ N,IsNonzeroAlongAt N Sigma x) (hMono : IsMonomialAlong n N Sigma born)
    (hProper : ∀ x ∈ maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X),
      properRows (fun i j => divExpAlong n N (oldMonomialPart N old born i) (born.get j) x)=P)
    (hRows : ∀ i ∈ P,maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X) ⊆
      cosupport n N (oldMonomialPart N old born i) 1)
    {β : Y → X} (hβ : IsBlowupAlong n (maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)) β)
    (hNext : let C := maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)
      let N' := geoStrictTransform β C N
      let old' := old.map (geoStrictTransform β C)
      let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
      IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old'++born') ∧ IsTransverse n N' born' ∧
        N' ⊆ closure (N' \ ⋃ H ∈ old'++born',H)) :
    let C := maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)
    let N' := geoStrictTransform β C N
    let old' := old.map (geoStrictTransform β C)
    let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
    let I' : Fin old.length → GermIdeal n Y := fun i =>
      restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
    let D' := fun i => monomialPartAlong n N' (I' i) born'
    let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
    (∀ z ∈ N',∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      (∀ z ∈ N',IsPreparedResidualSNCAt N' old' born' z) ∧
      ∀ i : Fin old.length,
        ((⟨N,born,oldTraceIdeal N old i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal=I' i ∧
        D' i=((⟨N,born,oldMonomialPart N old born i,if i ∈ P then 1 else 0⟩ : MarkedIdeal n X).geoTransform C β).ideal ∧
        J' i=(nextTotalMarked N (oldResidualPart N old born i) C β).ideal ∧
        I' i=restrictOn n N' ((D' i).mul (J' i)) ∧
        (I' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (I' i) z) ∧
        (D' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (D' i) z) ∧
        IsMonomialAlong n N' (D' i) born' ∧
        (J' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (J' i) z) ∧
        monomialPartAlong n N' (J' i) born'=unitIdeal n Y := by
  let C := maxLocusA (⟨N,born,Sigma,1⟩ : MarkedIdeal n X)
  let N' := geoStrictTransform β C N
  let old' := old.map (geoStrictTransform β C)
  let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
  let I' : Fin old.length → GermIdeal n Y := fun i =>
    restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
  let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
  let MI : Fin old.length → MarkedIdeal n X := fun i => ⟨N,born,oldTraceIdeal N old i,d i⟩
  let MD : Fin old.length → MarkedIdeal n X := fun i => ⟨N,born,oldMonomialPart N old born i,d i⟩
  let MJ : Fin old.length → MarkedIdeal n X := fun i => ⟨N,[],oldResidualPart N old born i,0⟩
  let ThreeRowGerms (z : Y) : Prop := ∀ (i : Fin old.length) (g : Y → ℂ),
    (((MI i).geoTransform C β).ideal.mem z g ↔ (I' i).mem z g) ∧
      (((MD i).geoTransform C β).ideal.mem z g ↔ (D' i).mem z g) ∧
      (((MJ i).geoTransform C β).ideal.mem z g ↔ (J' i).mem z g)
  have hCN : C ⊆ N := fun _ hx => hx.1.1
  have hAt : ∀ z ∈ N',
      (∀ i,ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
      IsPreparedResidualSNCAt N' old' born' z ∧ ThreeRowGerms z := by
    intro z hz
    by_cases hzC : β z ∈ C
    · have h := actual_target_prepared_over_maximum hn hN hE hTr hdense hOrd hPrepared
        P hP Sigma hM hnz hMono hProper hRows hβ hNext z hz hzC
      exact ⟨h.1,h.2.1,h.2.2.1⟩
    · have h := actual_target_prepared_off_centre hn hN hE hTr hdense hOrd hPrepared
        hβ hCN hNext z hz hzC
      exact ⟨h.1,h.2.1,fun i g => h.2.2 i (d i) g⟩
  let eO' : Fin old.length → Fin old'.length := Fin.cast (by simp [old'])
  have hGet' (i : Fin old.length) : old'.get (eO' i)=geoStrictTransform β C (old.get i) := by
    simp [old',eO',List.get_eq_getElem]
  have hData (i : Fin old.length) :
      (I' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (I' i) z) ∧
      (J' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (J' i) z) ∧
      (D' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (D' i) z) ∧
      IsMonomialAlong n N' (D' i) born' ∧ I' i=restrictOn n N' ((D' i).mul (J' i)) := by
    have h := actual_old_parts_geometry (N := N') (old := old') (born := born')
      hn hNext.1 hNext.2.1 hNext.2.2.1 hNext.2.2.2 (eO' i)
    simpa only [oldTraceIdeal,oldMonomialPart,oldResidualPart,hGet'] using h
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  refine ⟨fun z hz => (hAt z hz).1,fun z hz => (hAt z hz).2.1,?_⟩
  intro i
  obtain ⟨hcI',hnzI',hcJ',hnzJ',hcD',hnzD',hmD',hFactor⟩ := hData i
  have hcTI := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    (MI i) hN (hParts i).1 hβ hCN
  have hcTD := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    (MD i) hN (hParts i).2.2.2.2.1 hβ hCN
  have hcTJ := HironakaCoherentTransformExtension.isCoherent_geoTransform_ideal_without_inclusion
    (MJ i) hN (hParts i).2.2.1 hβ hCN
  have hI := normalized_ideal_eq_of_carrier_germs isClosed_closure hcTI hcI'
    (normalized_geoTransform (MI i) C β) (normalized_trace N' (geoStrictTransform β C (old.get i)))
    (fun z hz g => ((hAt z hz).2.2 i g).1)
  have hD := normalized_ideal_eq_of_carrier_germs isClosed_closure hcTD hcD'
    (normalized_geoTransform (MD i) C β)
    (normalized_of_carrierIdeal_le (D' i) hcD' (carrierIdeal_le_monomialPart N' (I' i) born'))
    (fun z hz g => ((hAt z hz).2.2 i g).2.1)
  have hJ := normalized_ideal_eq_of_carrier_germs isClosed_closure hcTJ hcJ'
    (normalized_geoTransform (MJ i) C β) (normalized_nonmonomial N' (I' i) born')
    (fun z hz g => ((hAt z hz).2.2 i g).2.2)
  have hBorn' := isSNCDivisor_of_sublist hNext.2.1 (List.sublist_append_right old' born')
  obtain ⟨_hcJ,_hcD,_hneD,_hmD,hNo,_hneJ,_hFactor⟩ := parts_hypotheses hn
    (⟨N',born',I' i,0⟩ : MarkedIdeal n Y) ⟨hNext.1,hcI',hBorn',hNext.2.2.1⟩ hnzI'
  have hMPJ : monomialPartAlong n N' (J' i) born'=unitIdeal n Y :=
    monomialPartAlong_eq_unit_of_no_member_factor hBorn' hNext.2.2.1 hcJ' hNo
  exact ⟨hI,hD.symm,hJ.symm,hFactor,hcI',hnzI',hcD',hnzD',hmD',hcJ',hnzJ',hMPJ⟩

private theorem actual_arithmetic_off_centre {r : ℕ} (hn : 0<n) {N C : Set X}
    {E : List (Set X)} (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n E)
    (hTr : IsTransverse n N E) (D : Fin r → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (hnz : ∀ i,∀ x ∈ N,IsNonzeroAlongAt N (D i) x)
    (hm : ∀ i,IsMonomialAlong n N (D i) E) (d : Fin r → ℕ)
    (hAdm : ∀ i,(⟨N,E,D i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C)
    {β : Y → X} (hβ : IsBlowupAlong n C β) (G : Fin r → GermIdeal n Y)
    (hLaw : ∀ i,G i=((⟨N,E,D i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal)
    {z : Y} (hz : z ∈ geoStrictTransform β C N) (hzC : β z ∉ C) :
    let E' := E.map (geoStrictTransform β C)++[β ⁻¹' C]
    let A := fun i j => divExpAlong n N (D i) (E.get j) (β z)
    let A' : Fin r → Fin E'.length → ℕ := fun i j =>
      divExpAlong n (geoStrictTransform β C N) (G i) (E'.get j) z
    properRows A'=properRows A ∧
      ((properRows A).Nonempty → nuOne A=0 → nuOne A'=0) ∧
      (∀ B, (∀ i j,A i j ≤ B) → ∀ i j,A' i j ≤ max B (E.length * B)) ∧
      (RowsChain A → RowsChain A') := by
  let E' := E.map (geoStrictTransform β C)++[β ⁻¹' C]
  let A : Fin r → Fin E.length → ℕ := fun i j => divExpAlong n N (D i) (E.get j) (β z)
  let A' : Fin r → Fin E'.length → ℕ := fun i j =>
    divExpAlong n (geoStrictTransform β C N) (G i) (E'.get j) z
  have hLen : E'.length=E.length+1 := by simp [E']
  have hCols (i : Fin r) (j : Fin E'.length) :
      A' i j=appendAbsentFamily A i (Fin.cast hLen j) := by
    have h := HironakaG4SelectedBornCanonicalColumns.canonical_columns_geoTransform_of_notMem hn
      (M := (⟨N,E,D i,d i⟩ : MarkedIdeal n X)) ⟨hN,hc i,hE,hTr⟩ (hnz i) (hm i) (hAdm i) hβ hz hzC j
    change divExpAlong n (geoStrictTransform β C N)
      ((⟨N,E,D i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal (E'.get j) z=
        appendAbsentFamily A i (Fin.cast hLen j) at h
    rwa [←hLaw i] at h
  have hInv := column_equiv_invariants (appendAbsentFamily A) A' (finCongr hLen) hCols
  refine ⟨hInv.1.trans (append_absent_invariants A).1,
    fun hAct hNu => hInv.2.2.trans (append_absent_nu_zero A hAct hNu),?_,?_⟩
  intro B hBound i j
  change A' i j ≤ max B (E.length * B)
  rw [hCols i j]
  exact (appendAbsentFamily_uniform_bound A B hBound i (Fin.cast hLen j)).trans (le_max_left _ _)
  · intro hChain
    change RowsChain A'
    apply rowsChain_of_column_equiv (appendAbsentFamily A) A' (finCongr hLen) ?_
      (appendAbsentFamily_rowsChain A hChain)
    exact hCols


theorem prepared_zero_mask_global_gamma_step (hn : 0 < n) {N : Set X}
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
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    IsMonomialAlong n N Sigma born →
    let C := maxLocusA M
    let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
    Sigma.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N Sigma x) ∧ M.IsWellFormed ∧
      M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} ∧
      M.IsAdmissibleCentre C ∧ interior C=∅ ∧
      HasNormalCrossings n C (old ++ born) ∧
      C ⊆ originalSharpBadLocus (n := n) N (old ++ born) ∧
      (∀ x ∈ C,properRows (A x)=P) ∧
      (∀ i : Fin old.length,
        (i ∈ P → C ⊆ old.get i) ∧
        (i ∉ P → (∀ x ∈ C,(D i).mem x (fun _ => (1 : ℂ))) ∧
          IsTransverse n C [old.get i]) ∧
        (⟨N,born,I i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
        (⟨N,born,D i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C) ∧
      ∀ (Y : CMfd.{u} n) (β : Y → X),IsBlowupAlong n C β →
        let N' := geoStrictTransform β C N
        let old' := old.map (geoStrictTransform β C)
        let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
        let I' : Fin old.length → GermIdeal n Y := fun i =>
          restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
        let D' := fun i => monomialPartAlong n N' (I' i) born'
        let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
        let A' : Y → Fin old.length → Fin born'.length → ℕ := fun z i j =>
          divExpAlong n N' (D' i) (born'.get j) z
        let Sigma' : GermIdeal n Y := ⟨fun z g =>
          IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D' i).mem z f) z g⟩
        let M' : MarkedIdeal n Y := ⟨N',born',Sigma',1⟩
        IsClosedSubmanifold n N' ∧ IsSNCDivisor n (old' ++ born') ∧
          IsTransverse n N' born' ∧
          N' ⊆ closure (N' \ ⋃ H ∈ old' ++ born',H) ∧
          old'.length=old.length ∧ born'.length=born.length+1 ∧
          (∀ z ∈ N',∀ i,
            ordinaryTraceOrder N' (oldResidualPart N' old' born' i) z ≤ 1) ∧
          (∀ z ∈ N',IsPreparedResidualSNCAt N' old' born' z) ∧
          (∀ i : Fin old.length,
            ((⟨N,born,I i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal=I' i ∧
            D' i=((⟨N,born,D i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal ∧
            J' i=(nextTotalMarked N (J i) C β).ideal ∧
            I' i=restrictOn n N' ((D' i).mul (J' i)) ∧
            (I' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (I' i) z) ∧
            (D' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (D' i) z) ∧
            IsMonomialAlong n N' (D' i) born' ∧
            (J' i).IsCoherent ∧ (∀ z ∈ N',IsNonzeroAlongAt N' (J' i) z) ∧
            monomialPartAlong n N' (J' i) born'=IdealWeightPowers.unitIdeal n Y) ∧
          M'=M.geoTransform C β ∧
          M'.IsWellFormed ∧ (∀ z ∈ N',IsNonzeroAlongAt N' Sigma' z) ∧
          IsMonomialAlong n N' Sigma' born' ∧
          (∀ z ∈ N',properRows (A' z) ⊆ properRows (A (β z))) ∧
          (∀ z ∈ N',tauD (A' z) ≤ P.card) ∧
          ((∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
            ∀ z ∈ N',tauD (A' z)=P.card → nuOne (A' z)=0) ∧
          M'.cosupp={z | z ∈ N' ∧ P ⊆ properRows (A' z)} := by
  dsimp only
  intro hTau hMono
  let I := oldTraceIdeal N old
  let D := oldMonomialPart N old born
  let J := oldResidualPart N old born
  let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
    divExpAlong n N (D i) (born.get j) x
  let Sigma := maskSum D P
  let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
  let C := maxLocusA M
  let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
  obtain ⟨hcSigma,hnzSigma,hM,hSupport,hC,hThin,hFull,hSharp,hProper,hCurrentRows⟩ :=
    actual_current_source hn hN hE hTr hdense hOrd hPrepared P hP hTau hMono
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hcD (i : Fin old.length) : (D i).IsCoherent := (hParts i).2.2.2.2.1
  have hnzD (i : Fin old.length) : ∀ x ∈ N,IsNonzeroAlongAt N (D i) x := (hParts i).2.2.2.2.2.1
  have hmD (i : Fin old.length) : IsMonomialAlong n N (D i) born := (hParts i).2.2.2.2.2.2.1
  have hCN : C ⊆ N := fun _ hx => (hC.2.1 hx).1
  have hAdmD (i : Fin old.length) : (⟨N,born,D i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C :=
    (hCurrentRows i).2.2.2
  have hRows : ∀ i ∈ P,C ⊆ cosupport n N (D i) 1 := by
    intro i hi x hx
    have h := (hAdmD i).2.1 hx
    change x ∈ cosupport n N (D i) (d i) at h
    simpa only [d,if_pos hi] using h
  refine ⟨hcSigma,hnzSigma,hM,hSupport,hC,hThin,hFull,hSharp,hProper,hCurrentRows,?_⟩
  intro Y β hβ
  let N' := geoStrictTransform β C N
  let old' := old.map (geoStrictTransform β C)
  let born' := born.map (geoStrictTransform β C)++[β ⁻¹' C]
  let I' : Fin old.length → GermIdeal n Y := fun i =>
    restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  let J' := fun i => nonmonomialPartAlong n N' (I' i) born'
  let A' : Y → Fin old.length → Fin born'.length → ℕ := fun z i j =>
    divExpAlong n N' (D' i) (born'.get j) z
  let Sigma' := maskSum D' P
  let M' : MarkedIdeal n Y := ⟨N',born',Sigma',1⟩
  have hNext := actual_next_full_geometry hn hN hE hTr hdense hC.1 hCN hFull hC.2.2 hβ
  have hGlobal := actual_global_rows hn hN hE hTr hdense hOrd hPrepared P hP Sigma
    hM hnzSigma hMono hProper hRows hβ hNext
  have hLawD (i : Fin old.length) : D' i=((⟨N,born,D i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal :=
    (hGlobal.2.2 i).2.1
  have hcD' (i : Fin old.length) : (D' i).IsCoherent := by
    obtain ⟨_,_,_,_,_,_,hc,_,_,_,_,_⟩ := hGlobal.2.2 i
    exact hc
  have hnzD' (i : Fin old.length) : ∀ z ∈ N',IsNonzeroAlongAt N' (D' i) z := by
    obtain ⟨_,_,_,_,_,_,_,hnz,_,_,_,_⟩ := hGlobal.2.2 i
    exact hnz
  have hmD' (i : Fin old.length) : IsMonomialAlong n N' (D' i) born' := by
    obtain ⟨_,_,_,_,_,_,_,_,hm,_,_,_⟩ := hGlobal.2.2 i
    exact hm
  have hSumLaw : Sigma'=(M.geoTransform C β).ideal := by
    apply maskSum_controlled (E := born) hN D D' hcD hcD'
      (fun i => carrierIdeal_le_monomialPart N' (I' i) born') hβ P hP
    · intro i hi
      simpa only [d,if_pos hi] using hAdmD i
    · intro i hi
      simpa only [d,if_pos hi] using hLawD i
  have hWholeM : M'=M.geoTransform C β :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hSumLaw rfl
  have hMonomialNext := monomial_step_along hn hM hnzSigma hMono hβ
  rw [←hWholeM] at hMonomialNext
  have hOff (z : Y) (hz : z ∈ N') (hzC : β z ∉ C) :=
    actual_arithmetic_off_centre hn hN hBorn hTr D hcD hnzD hmD d hAdmD hβ D' hLawD hz hzC
  have hCentre (z : Y) (hz : z ∈ N') (hzC : β z ∈ C) :=
    actual_target_prepared_over_maximum hn hN hE hTr hdense hOrd hPrepared P hP Sigma
      hM hnzSigma hMono hProper hRows hβ hNext z hz hzC
  have hSubset : ∀ z ∈ N',properRows (A' z) ⊆ properRows (A (β z)) := by
    intro z hz
    by_cases hzC : β z ∈ C
    · exact (hCentre z hz hzC).2.2.2.1
    · exact (hOff z hz hzC).1.subset
  have hSourceN (z : Y) (hz : z ∈ N') : β z ∈ N :=
    geoStrictTransform_subset_preimage hβ.contMDiff.continuous hN.1 hz
  have hCount (z : Y) (hz : z ∈ N') : tauD (A' z) ≤ tauD (A (β z)) :=
    Finset.card_le_card (hSubset z hz)
  have hCap : ∀ z ∈ N',tauD (A' z) ≤ P.card :=
    fun z hz => (hCount z hz).trans (hTau (β z) (hSourceN z hz))
  have hNuPreserved : (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
      ∀ z ∈ N',tauD (A' z)=P.card → nuOne (A' z)=0 := by
    intro hNu z hz hEq
    have hSourceCap : tauD (A (β z))≤P.card := hTau (β z) (hSourceN z hz)
    have hSourceCount : tauD (A' z)≤tauD (A (β z)) := hCount z hz
    have hEq0 : tauD (A (β z))=P.card := by omega
    have hNu0 := hNu (β z) (hSourceN z hz) hEq0
    by_cases hzC : β z ∈ C
    · exact (hCentre z hz hzC).2.2.2.2.1 hNu0 (hEq.trans hEq0.symm)
    · have hPositive : 0<P.card := Finset.card_pos.mpr hP
      have hActive : (properRows (A (β z))).Nonempty := Finset.card_pos.mp (by
        change 0<tauD (A (β z))
        omega)
      exact (hOff z hz hzC).2.1 hActive hNu0
  have hBorn' := isSNCDivisor_of_sublist hNext.2.1 (List.sublist_append_right old' born')
  have hSupport' : M'.cosupp={z | z ∈ N' ∧ P ⊆ properRows (A' z)} :=
    maskSum_canonical_cosupport hn hNext.1 hBorn' hNext.2.2.1 D' hcD' hnzD' hmD' P
  exact ⟨hNext.1,hNext.2.1,hNext.2.2.1,hNext.2.2.2,by simp,by simp,
    hGlobal.1,hGlobal.2.1,hGlobal.2.2,hWholeM,hMonomialNext.1,hMonomialNext.2.1,
    hMonomialNext.2.2.1,hSubset,hCap,hNuPreserved,hSupport'⟩

end
end Hironaka.HironakaG4ZeroMaskGammaStep


/-! Public access to the existing private proof; no strengthened statement. -/
namespace Hironaka.HironakaG4ZeroMaskGammaStep

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupStrictSubmanifold NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  MonomialPartAlong MonomialPartEtale DivisorExponentAlong GermIdealOrder
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  MarkedIdealOperationsAlong.MarkedIdeal
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4MonomialMaximalContact HironakaG4MonomialTopStratum HironakaG4MonomialRowChain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualChronologicalStrictStep
  MonomialCaseAlong MonomialStepAlong MonomialCase IdealWeightPowers BoundaryCount
  NonmonomialTransformAlong HironakaSharpActualChronologicalResidualDictionary
  HironakaSharpActualControlledRelativeSaturation HironakaSharpActualFiniteChronologicalHistory

variable {n : ℕ} {X Y Z : CMfd.{u} n}

set_option linter.unusedVariables false in
/-- A uniform bound for every source row and born column survives an actual
prepared Gamma blowup, with an explicit bound on the newly born column. -/
theorem prepared_zero_mask_gamma_step_uniform_rows (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma := maskSum D P
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) → IsMonomialAlong n N Sigma born →
    ∀ B, (∀ x ∈ N,∀ i j,A x i j ≤ B) →
    ∀ (Y : CMfd.{u} n) (β : Y → X) (hβ : IsBlowupAlong n (maxLocusA M) β),
      let C := maxLocusA M
      let N' := geoStrictTransform β C N
      let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
      let I' : Fin old.length → GermIdeal n Y := fun i =>
        restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
      let D' := fun i => monomialPartAlong n N' (I' i) born'
      ∀ z ∈ N',∀ i j,divExpAlong n N' (D' i) (born'.get j) z ≤ max B (born.length * B) := by
  dsimp only
  intro hTau hMono B hBound Y β hβ
  let D := oldMonomialPart N old born
  let Sigma := maskSum D P
  let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
  let C := maxLocusA M
  let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
  obtain ⟨_hcSigma,hnzSigma,hM,_hSupport,hC,_hThin,hFull,_hSharp,hProper,hCurrentRows⟩ :=
    actual_current_source hn hN hE hTr hdense hOrd hPrepared P hP hTau hMono
  have hCN : C ⊆ N := fun _ hx => (hC.2.1 hx).1
  have hAdmD (i : Fin old.length) : (⟨N,born,D i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C :=
    (hCurrentRows i).2.2.2
  have hRows : ∀ i ∈ P,C ⊆ cosupport n N (D i) 1 := by
    intro i hi x hx
    have h := (hAdmD i).2.1 hx
    change x ∈ cosupport n N (D i) (d i) at h
    simpa only [d,if_pos hi] using h
  have hNext := actual_next_full_geometry hn hN hE hTr hdense hC.1 hCN hFull hC.2.2 hβ
  have hGlobal := actual_global_rows hn hN hE hTr hdense hOrd hPrepared P hP Sigma
    hM hnzSigma hMono hProper hRows hβ hNext
  let N' := geoStrictTransform β C N
  let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
  let I' : Fin old.length → GermIdeal n Y := fun i =>
    restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  have hLawD (i : Fin old.length) : D' i=((⟨N,born,D i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal :=
    (hGlobal.2.2 i).2.1
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  intro z hz i j
  have hzN : β z ∈ N := geoStrictTransform_subset_preimage hβ.contMDiff.continuous hN.1 hz
  by_cases hzC : β z ∈ C
  · have h := actual_target_prepared_over_maximum hn hN hE hTr hdense hOrd hPrepared P hP Sigma
      hM hnzSigma hMono hProper hRows hβ hNext z hz hzC
    exact h.2.2.2.2.2.1 B (hBound (β z) hzN) i j
  · have h := actual_arithmetic_off_centre hn hN hBorn hTr D
      (fun i => (hParts i).2.2.2.2.1) (fun i => (hParts i).2.2.2.2.2.1)
      (fun i => (hParts i).2.2.2.2.2.2.1) d hAdmD hβ D' hLawD hz hzC
    exact h.2.2.1 B (hBound (β z) hzN) i j


set_option linter.unusedVariables false in
/-- Componentwise row comparability survives the actual prepared Gamma step. -/
theorem prepared_zero_mask_gamma_step_rowsChain_at (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma := maskSum D P
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) → IsMonomialAlong n N Sigma born →
    ∀ (Y : CMfd.{u} n) (β : Y → X) (hβ : IsBlowupAlong n (maxLocusA M) β),
      let C := maxLocusA M
      let N' := geoStrictTransform β C N
      let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
      let I' : Fin old.length → GermIdeal n Y := fun i =>
        restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
      let D' := fun i => monomialPartAlong n N' (I' i) born'
      ∀ z ∈ N',RowsChain (A (β z)) → RowsChain (fun i j => divExpAlong n N' (D' i) (born'.get j) z) := by
  dsimp only
  intro hTau hMono Y β hβ
  let D := oldMonomialPart N old born
  let Sigma := maskSum D P
  let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
  let C := maxLocusA M
  let d : Fin old.length → ℕ := fun i => if i ∈ P then 1 else 0
  obtain ⟨_hcSigma,hnzSigma,hM,_hSupport,hC,_hThin,hFull,_hSharp,hProper,hCurrentRows⟩ :=
    actual_current_source hn hN hE hTr hdense hOrd hPrepared P hP hTau hMono
  have hCN : C ⊆ N := fun _ hx => (hC.2.1 hx).1
  have hAdmD (i : Fin old.length) : (⟨N,born,D i,d i⟩ : MarkedIdeal n X).IsAdmissibleCentre C :=
    (hCurrentRows i).2.2.2
  have hRows : ∀ i ∈ P,C ⊆ cosupport n N (D i) 1 := by
    intro i hi x hx
    have h := (hAdmD i).2.1 hx
    change x ∈ cosupport n N (D i) (d i) at h
    simpa only [d,if_pos hi] using h
  have hNext := actual_next_full_geometry hn hN hE hTr hdense hC.1 hCN hFull hC.2.2 hβ
  have hGlobal := actual_global_rows hn hN hE hTr hdense hOrd hPrepared P hP Sigma
    hM hnzSigma hMono hProper hRows hβ hNext
  let N' := geoStrictTransform β C N
  let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
  let I' : Fin old.length → GermIdeal n Y := fun i =>
    restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
  let D' := fun i => monomialPartAlong n N' (I' i) born'
  have hLawD (i : Fin old.length) : D' i=((⟨N,born,D i,d i⟩ : MarkedIdeal n X).geoTransform C β).ideal :=
    (hGlobal.2.2 i).2.1
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hBorn := isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  intro z hz hChain
  by_cases hzC : β z ∈ C
  · have h := actual_target_prepared_over_maximum hn hN hE hTr hdense hOrd hPrepared P hP Sigma
      hM hnzSigma hMono hProper hRows hβ hNext z hz hzC
    exact h.2.2.2.2.2.2 hChain
  · have h := actual_arithmetic_off_centre hn hN hBorn hTr D
      (fun i => (hParts i).2.2.2.2.1) (fun i => (hParts i).2.2.2.2.2.1)
      (fun i => (hParts i).2.2.2.2.2.2.1) d hAdmD hβ D' hLawD hz hzC
    exact h.2.2.2 hChain


set_option linter.unusedVariables false in
theorem prepared_zero_mask_gamma_step_rowsChain (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1)
    (hPrepared : ∀ x ∈ N,IsPreparedResidualSNCAt N old born x)
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let Sigma := maskSum D P
    let M : MarkedIdeal n X := ⟨N,born,Sigma,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) → IsMonomialAlong n N Sigma born →
    (∀ x ∈ N,RowsChain (A x)) →
    ∀ (Y : CMfd.{u} n) (β : Y → X) (hβ : IsBlowupAlong n (maxLocusA M) β),
      let C := maxLocusA M
      let N' := geoStrictTransform β C N
      let born' := born.map (geoStrictTransform β C) ++ [β ⁻¹' C]
      let I' : Fin old.length → GermIdeal n Y := fun i =>
        restrictOn n N' (vanishingIdeal (n := n) (geoStrictTransform β C (old.get i)))
      let D' := fun i => monomialPartAlong n N' (I' i) born'
      ∀ z ∈ N',RowsChain (fun i j => divExpAlong n N' (D' i) (born'.get j) z) := by
  dsimp only
  intro hTau hMono hChain Y β hβ z hz
  apply prepared_zero_mask_gamma_step_rowsChain_at hn hN hE hTr hdense hOrd hPrepared P hP hTau hMono Y β hβ z hz
  exact hChain (β z) (geoStrictTransform_subset_preimage hβ.contMDiff.continuous hN.1 hz)

theorem finite_mask_sum_controlled {ι : Type*} {N C : Set X} {E : List (Set X)}
    (hN : IsClosedSubmanifold n N) {β : Y → X} (D : ι → GermIdeal n X) (G : ι → GermIdeal n Y)
    (hc : ∀ i,(D i).IsCoherent) (hcG : ∀ i,(G i).IsCoherent)
    (hNormG : ∀ i,(vanishingIdeal (n := n) (geoStrictTransform β C N)).Le (G i))
    (hβ : IsBlowupAlong n C β) (P : Finset ι) :
    P.Nonempty →
    (∀ i ∈ P,(⟨N,E,D i,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C) →
    (∀ i ∈ P,G i=((⟨N,E,D i,1⟩ : MarkedIdeal n X).geoTransform C β).ideal) →
    (⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(G i).mem x f) x g⟩ : GermIdeal n Y)=((⟨N,E,(⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩ : GermIdeal n X),1⟩ : MarkedIdeal n X).geoTransform C β).ideal :=
  maskSum_controlled hN D G hc hcG hNormG hβ P

end
end Hironaka.HironakaG4ZeroMaskGammaStep
