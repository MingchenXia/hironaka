import Hironaka.Resolution.HironakaOriginalCompactCosupportGlobalScheduler
import Hironaka.Invariant.NonmonomialOrderGlobalPhase
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.NonmonomialOrderMonomialCanonical
import Hironaka.Invariant.NonmonomialOrderZero
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaG4CompactPositivePhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  ResolutionInvariantSeq ResolutionInvariantDriver ResolutionInvariantOrder
  ResolutionDriver CanonicalCentres StepOneLowerDomain NonmonomialOrderLocal
  NonmonomialOrderCanonical NonmonomialOrderGlobalPhase NonmonomialOrderMonomialCanonical
  NonmonomialOrderZero RestrictEmptyTower DivisorExponentAlong MonomialPartAlong MonomialCaseAlong GermIdealOrder
  NonmonomialTransformAlong RelativePrincipalizationSpan RestrictLeCalculus MarkedIdealOperationsAlong
open ResolutionInvariantSpec (IsInvDomain IsCanonical countCentresMeeting)
variable {n k : ℕ} {X Y : CMfd.{u} n}
variable {Λ : Type v} [LinearOrder Λ]

def positiveSupport (M : MarkedIdeal n X) : Set X := M.cosupp ∩ ordGe M 1

/-- Along an actual canonical test tower, positive nonmonomial order cannot
appear over a source point of order zero. -/
theorem positive_support_subset_preimage (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (hf : OrdMonotone M f) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T → IsCanonical M f T →
      positiveSupport (geoTransformAlong M T) ⊆ T.proj ⁻¹' positiveSupport M := by
  intro Y T
  induction T with
  | refl => intro _ _ z hz; exact hz
  | @step Y Z T C π hπ ih =>
    intro hTest hCan z hz
    have hCur := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (.step T C π hπ) hTest)
    have hzPos : 1 ≤ nmOrd (geoTransformAlong M (.step T C π hπ)) z :=
      (mem_ordGe_iff hCur.isWellFormed hCur.isNonzeroAlongAt hz.1.1 1).mp hz.2
    have hStep := nmOrd_step_le_of_canonical hn hM hf T C π hπ hTest hCan.2 hz.1
    have hPrev : π z ∈ positiveSupport (geoTransformAlong M T) :=
      ⟨hStep.1,mem_ordGe_of_succ_le (hzPos.trans hStep.2)⟩
    exact ih hTest.1 hCan.1 hPrev

/-- Positive support remains compact in every actual canonical test prefix. -/
theorem current_positive_support_compact (hn : 0<n)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (hf : OrdMonotone M f)
    (hK : IsCompact (positiveSupport M)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (hCan : IsCanonical M f T) :
    IsCompact (positiveSupport (geoTransformAlong M T)) := by
  have hCur := (InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT)
  have hClosed : IsClosed (positiveSupport (geoTransformAlong M T)) :=
    (GiraudAlong.isClosed_cosupport_along hCur.isWellFormed.isCoherent
      hCur.isWellFormed.isClosedSubmanifold_N (geoTransformAlong M T).d).inter
      (isClosed_ordGe hn hCur.isWellFormed hCur.isNonzeroAlongAt 1)
  exact ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hClosed (positive_support_subset_preimage hn M hM f hf T hT hCan)

/-- If a current positive point exists, compact positive support forces a
true maximum of the full invariant on the entire current cosupport. -/
theorem exists_global_max_of_positive_compact (hn : 0<n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hf : OrdMonotone M (R.inv M)) (hK : IsCompact (positiveSupport M))
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (hCan : IsCanonical M (R.inv M) T)
    (hne : (positiveSupport (geoTransformAlong M T)).Nonempty) :
    ∃ x ∈ positiveSupport (geoTransformAlong M T),
      ∀ y ∈ (geoTransformAlong M T).cosupp,R.inv M T y ≤ R.inv M T x := by
  have hCompact := current_positive_support_compact hn M hM (R.inv M) hf hK T hT hCan
  obtain ⟨x,hx,hMax⟩ := ((R.isInvValue.usc M hM T hCan).mono Set.inter_subset_left).exists_isMaxOn hCompact hne
  refine ⟨x,hx,?_⟩
  intro y hy
  by_cases hyPos : y ∈ positiveSupport (geoTransformAlong M T)
  · exact hMax y hyPos
  · have hNot : y ∉ ordGe (geoTransformAlong M T) 1 := fun h => hyPos ⟨hy,h⟩
    have hyZero : nmOrd (geoTransformAlong M T) y=0 := Nat.eq_zero_of_le_zero (nmOrd_le_of_notMem hNot)
    have hCur := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
    have hxPos : 1 ≤ nmOrd (geoTransformAlong M T) x :=
      (mem_ordGe_iff hCur.isWellFormed hCur.isNonzeroAlongAt hx.1.1 1).mp hx.2
    by_contra hle
    have hInv : R.inv M T x ≤ R.inv M T y := le_of_not_ge hle
    have hOrd := hf T hT x hx.1 y hy hInv
    omega
/-- An actual finite canonical test history removes every positive
nonmonomial-order point when only that source locus is compact. The full
marked cosupport and carrier may be noncompact. -/
theorem exists_actual_compact_positive_order_exit (hn : 0<n)
    (R : ResolutionInvariantSeq.ResolutionInvariant.{u,v} n k Λ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (hf : OrdMonotone M (R.inv M)) (hK : IsCompact (positiveSupport M)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical M (R.inv M) T ∧ IsGeoTestTower M T ∧
      CentresOver (positiveSupport M) T ∧
      ∀ y ∈ (geoTransformAlong M T).cosupp,nmOrd (geoTransformAlong M T) y=0 := by
  let A := {p : Σ Y : CMfd.{u} n,BlowupTower X Y // IsCanonical M (R.inv M) p.2}
  have hext : ∀ p : A,∃ q : A,∃ (C : Set p.1.1) (π : q.1.1 → p.1.1)
      (hπ : IsBlowupAlong n C π),q.1.2=.step p.1.2 C π hπ ∧
      C ⊆ positiveSupport (geoTransformAlong M p.1.2) ∧
      ((positiveSupport (geoTransformAlong M p.1.2)).Nonempty → C.Nonempty) := by
    intro p
    have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM p.1.2 p.2
    by_cases hp : (positiveSupport (geoTransformAlong M p.1.2)).Nonempty
    · let C := maxLocus (R.inv M p.1.2) (geoTransformAlong M p.1.2).cosupp
      obtain ⟨x,hx,hMax⟩ := exists_global_max_of_positive_compact hn R M hM hf hK p.1.2 ht p.2 hp
      have hxC : x ∈ C := ⟨hx.1,hMax⟩
      have hCpos : C ⊆ positiveSupport (geoTransformAlong M p.1.2) := by
        intro y hy
        have hCur := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM p.1.2 ht
        have hxOrd : 1 ≤ nmOrd (geoTransformAlong M p.1.2) x :=
          (mem_ordGe_iff hCur.isWellFormed hCur.isNonzeroAlongAt hx.1.1 1).mp hx.2
        have hyOrd := hf p.1.2 ht x hx.1 y hy.1 (hy.2 x hx.1)
        exact ⟨hy.1,mem_ordGe_of_succ_le (hxOrd.trans hyOrd)⟩
      have hadm := R.isInvValue.isAdmissibleCentre_maxLocus hM p.1.2 p.2 ht
      obtain ⟨Z,π,hπ⟩ := exists_blowup C hadm.1 (interior_maxLocus_eq_empty hM p.1.2 ht _)
      exact ⟨⟨⟨Z,.step p.1.2 C π hπ⟩,p.2,Or.inr rfl⟩,C,π,hπ,rfl,hCpos,fun _ => ⟨x,hxC⟩⟩
    · let π : p.1.1 → p.1.1 := id
      have hπ : IsBlowupAlong n (∅ : Set p.1.1) π := BlowupExistenceCodimOne.isBlowupAlong_id_empty
      exact ⟨⟨⟨p.1.1,.step p.1.2 ∅ π hπ⟩,p.2,Or.inl rfl⟩,∅,π,hπ,rfl,empty_subset _,fun h => (hp h).elim⟩
  choose next hnext using hext
  let a0 : A := ⟨⟨X,.refl⟩,trivial⟩
  let s : GrowingSeq X := GrowingSeq.ofIterate (fun p : A => p.1) next a0 rfl (fun p => by
    obtain ⟨C,π,hπ,he,_hC,_hne⟩ := hnext p
    exact ⟨C,π,hπ,he⟩)
  have hcan : ∀ i,IsCanonical M (R.inv M) (s.stage i).2 := fun i => (next^[i] a0).2
  have hmaps : ∀ i,∃ (C : Set (s.stage i).1) (π : (s.stage (i+1)).1 → (s.stage i).1)
      (hπ : IsBlowupAlong n C π),(s.stage (i+1)).2=.step (s.stage i).2 C π hπ ∧
      C ⊆ positiveSupport (geoTransformAlong M (s.stage i).2) ∧
      ((positiveSupport (geoTransformAlong M (s.stage i).2)).Nonempty → C.Nonempty) := by
    intro i
    change ∃ (C : Set (next^[i] a0).1.1) (π : (next^[i+1] a0).1.1 → (next^[i] a0).1.1)
      (hπ : IsBlowupAlong n C π),(next^[i+1] a0).1.2=.step (next^[i] a0).1.2 C π hπ ∧ _
    rw [Function.iterate_succ_apply']
    exact hnext (next^[i] a0)
  have hOver : ∀ i,CentresOver (positiveSupport M) (s.stage i).2 := by
    intro i
    induction i with
    | zero => trivial
    | succ i ih =>
      obtain ⟨C,π,hπ,he,hC,_hne⟩ := hmaps i
      have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM (s.stage i).2 (hcan i)
      have hSub := positive_support_subset_preimage hn M hM (R.inv M) hf (s.stage i).2 ht (hcan i)
      rw [he]
      exact ⟨ih,hC.trans hSub⟩
  have hterminal : ∃ N,(positiveSupport (geoTransformAlong M (s.stage N).2))=∅ := by
    by_contra hno
    have hne : ∀ i,(positiveSupport (geoTransformAlong M (s.stage i).2)).Nonempty := by
      intro i
      exact Set.nonempty_iff_ne_empty.mpr (fun he => hno ⟨i,he⟩)
    obtain ⟨bound,hbound⟩ := R.seqLocallyFinite M hM (positiveSupport M) hK s hcan
    have hcount : ∀ i,countCentresMeeting (positiveSupport M) (s.stage i).2=i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        obtain ⟨C,π,hπ,he,hC,hCne⟩ := hmaps i
        have ht := R.isInvValue.isGeoTestTower_of_isCanonical hM (s.stage i).2 (hcan i)
        have hSub := positive_support_subset_preimage hn M hM (R.inv M) hf (s.stage i).2 ht (hcan i)
        obtain ⟨x,hx⟩ := hCne (hne i)
        have hhit : (C ∩ (s.stage i).2.proj ⁻¹' positiveSupport M).Nonempty := ⟨x,hx,hSub (hC hx)⟩
        rw [he]
        simp only [countCentresMeeting,if_pos hhit,ih]
    have hh := hbound (bound+1)
    rw [hcount] at hh
    omega
  obtain ⟨N,hN⟩ := hterminal
  refine ⟨(s.stage N).1,(s.stage N).2,hcan N,
    R.isInvValue.isGeoTestTower_of_isCanonical hM (s.stage N).2 (hcan N),hOver N,?_⟩
  intro y hy
  have hNot : y ∉ ordGe (geoTransformAlong M (s.stage N).2) 1 := by
    intro ho
    have : y ∈ positiveSupport (geoTransformAlong M (s.stage N).2) := ⟨hy,ho⟩
    rw [hN] at this
    exact this
  exact Nat.eq_zero_of_le_zero (nmOrd_le_of_notMem hNot)

/-- The internally constructed canonical invariant supplies the order
monotonicity; only the actual positive nonmonomial locus must be compact. -/
theorem exists_canonical_compact_positive_order_exit (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (d+1) M)
    (hK : IsCompact (positiveSupport M)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical M ((invFamily hn (d+1)).inv M) T ∧ IsGeoTestTower M T ∧
      CentresOver (positiveSupport M) T ∧
      ∀ y ∈ (geoTransformAlong M T).cosupp,nmOrd (geoTransformAlong M T) y=0 := by
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
    (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn d) J S z
  have hf : OrdMonotone M ((invFamily hn (d+1)).inv M) := GeneralValue.ordMonotone_genInv lower M
  exact exists_actual_compact_positive_order_exit hn (invFamily hn (d+1)) M hM hf hK

/-- For mark one, zero nonmonomial order throughout the cosupport makes the
whole actual ideal monomial along its carrier. -/
theorem mark_one_monomial_of_zero_on_cosupport (hn : 0<n) (M : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hne : ∀ x ∈ M.N,IsNonzeroAlongAt M.N M.ideal x)
    (hd : M.d=1) (hZero : ∀ x ∈ M.cosupp,nmOrd M x=0) :
    IsMonomialAlong n M.N M.ideal M.E := by
  have hParts := NonmonomialTransformAlong.parts_hypotheses hn M hM hne
  have hLe := NonmonomialTransformAlong.le_nonmonomialPartAlong_self (N := M.N) (E := M.E) hM.isCoherent
  have hSub : ordGe M 1 ⊆ M.cosupp := by
    change cosupport n M.N (nonmonomialPartAlong n M.N M.ideal M.E) 1 ⊆
      cosupport n M.N M.ideal M.d
    rw [hd]
    exact cosupport_subset_of_restrictLe
      (restrictLe_of_le (W := M.N) hParts.1 hLe) 1
  intro x hx g hg
  apply restrictLe_monomialPartAlong_of_notMem hx ?_ hg
  change x ∉ ordGe M 1
  intro hOrd
  have hxCos : x ∈ M.cosupp := hSub hOrd
  have hOne := (mem_ordGe_iff hM hne hx 1).mp hOrd
  have h0 := hZero x hxCos
  omega

/-- A compact positive-order locus for an actual mark-one ideal gives a
finite canonical test history whose terminal ideal is globally monomial
along its actual carrier, even with noncompact cosupport. -/
theorem exists_canonical_mark_one_compact_positive_monomial_exit (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain (d+1) M) (hd : M.d=1)
    (hK : IsCompact (positiveSupport M)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical M ((invFamily hn (d+1)).inv M) T ∧ IsGeoTestTower M T ∧
      CentresOver (positiveSupport M) T ∧
      IsMonomialAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E := by
  obtain ⟨Y,T,hCan,hTest,hOver,hZero⟩ := exists_canonical_compact_positive_order_exit hn d M hM hK
  have hCur := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hTest
  have hdT : (geoTransformAlong M T).d=1 := by simpa only [d_geoTransformAlong] using hd
  exact ⟨Y,T,hCan,hTest,hOver,mark_one_monomial_of_zero_on_cosupport hn _
    hCur.isWellFormed hCur.isNonzeroAlongAt hdT hZero⟩

end
end Hironaka.HironakaG4CompactPositivePhase
