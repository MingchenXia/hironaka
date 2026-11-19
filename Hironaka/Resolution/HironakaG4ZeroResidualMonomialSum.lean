import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.HironakaG4MonomialFamilyInvariant
import Hironaka.Resolution.HironakaG4CanonicalZeroRowUnit
import Hironaka.Analytic.MonomialCaseLocal
import Hironaka.Resolution.HironakaMarkOneNoncompactNativePhase

/-! Actual zero-residual canonical old-factor SUM and its SAME native finite gamma history.
Complete source-first proof: hironaka-g4-zero-residual-monomial-sum.tex.
No later recomputed D/J/Prepared/full-old compatibility is assumed or claimed. -/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG4ZeroResidualMonomialSum
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings NormalCrossingsComparison
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4CanonicalZeroRowUnit RelativePrincipalizationSpan
  DivisorExponentAlong MonomialPartAlong MonomialCaseAlong MonomialCase
  RestrictedIdealExtension InvertibleIdealQuotient GermIdealOrder
  BlowupFlatCoordinates SimultaneousNormalCrossings
  MonomialStepAlong MarkedIdeals MarkedIdeals.MarkedIdeal BoundaryCount
variable {n : ℕ} {X : CMfd.{u} n}


def finiteSum {ι : Type*} (D : ι → GermIdeal n X) (P : Finset ι) : GermIdeal n X :=
  ⟨fun x g => IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩

theorem le_finiteSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) {P : Finset ι} {i : ι} (hi : i ∈ P) :
    (D i).Le (finiteSum D P) := by
  intro x g hg
  change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x g
  exact isInSpanAt_self ⟨i,hi,hg⟩ (GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)

theorem coherent_finiteSum {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) : (finiteSum D P).IsCoherent := by
  classical
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
    have heq : finiteSum D (insert i P)=sumIdeal (D i) (finiteSum D P) := by
      ext x g
      change IsInSpanAt (n := n) (fun f => ∃ j ∈ insert i P,(D j).mem x f) x g ↔
        IsInSpanAt (n := n) (fun f => (D i).mem x f ∨ (finiteSum D P).mem x f) x g
      constructor
      · apply IsInSpanAt.mono
        rintro f ⟨j,hj,hf⟩
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl hf
        · exact Or.inr (le_finiteSum D hc hj x f hf)
      · apply IsInSpanAt.trans
        rintro f (hf | hf)
        · exact le_finiteSum D hc (Finset.mem_insert_self i P) x f hf
        · change IsInSpanAt (n := n) (fun f => ∃ j ∈ P,(D j).mem x f) x f at hf
          exact hf.mono (fun _ ⟨j,hj,hg⟩ => ⟨j,Finset.mem_insert_of_mem hj,hg⟩)
    rw [heq]
    exact isCoherent_sumIdeal (hc i) ih

private theorem span_finiteSum_iff {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) (N : Set X) (x : X) (g : X → ℂ) :
    IsInSpanOnAt (n := n) N ((finiteSum D P).mem x) x g ↔
      IsInSpanOnAt (n := n) N (fun f => ∃ i ∈ P,(D i).mem x f) x g := by
  constructor
  · exact IsInSpanOnAt.trans (fun _ hf => IsInSpanAt.restrict hf)
  · exact IsInSpanOnAt.mono (fun f ⟨i,hi,hf⟩ => le_finiteSum D hc hi x f hf)

private theorem cosupport_finiteSum_one {ι : Type*} (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (P : Finset ι) (N : Set X) (x : X) :
    x ∈ cosupport n N (finiteSum D P) 1 ↔
      x ∈ N ∧ ∀ i ∈ P,x ∈ cosupport n N (D i) 1 := by
  have hrow (i : ι) : x ∈ cosupport n N (D i) 1 ↔
      x ∈ N ∧ ∀ g,(D i).mem x g → g x=0 := by
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hg)]
    rfl
  rw [cosupport_one (𝔞 := finiteSum D P) (fun _ _ hg => hg.1)]
  constructor
  · rintro ⟨hxN,hx⟩
    exact ⟨hxN,fun i hi => (hrow i).mpr ⟨hxN,fun g hg =>
      hx g (le_finiteSum D hc hi x g hg)⟩⟩
  · rintro ⟨hxN,hx⟩
    refine ⟨hxN,?_⟩
    intro g hg
    obtain ⟨_hg,K,s,a,hs,_ha,heq⟩ := hg
    rw [heq.self_of_nhds]
    apply Finset.sum_eq_zero
    intro k _hk
    obtain ⟨i,hi,hsi⟩ := hs k
    rw [((hrow i).mp (hx i hi)).2 _ hsi,mul_zero]

private theorem exponent_zero_of_not_mem {N H : Set X} {I : GermIdeal n X}
    (hc : IsClosed (N ∩ H)) {x : X} (hx : x ∉ H) :
    divExpAlong n N I H x=0 := by
  have hnot : ¬∃ e,¬IsDivNearAlong n N I H (e+1) x := by
    rintro ⟨e,he⟩
    exact he (isDivNearAlong_of_notMem hc (fun h => hx h.2) (e+1))
  unfold divExpAlong
  rw [dif_neg hnot]

private theorem row_cosupport_iff (hn : 0<n) {N : Set X}
    {B : List (Set X)} {D : GermIdeal n X} (hN : IsClosedSubmanifold n N)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B) (hc : D.IsCoherent)
    (hne : ∀ y ∈ N,IsNonzeroAlongAt N D y) (hm : IsMonomialAlong n N D B)
    {x : X} (hx : x ∈ N) :
    x ∈ cosupport n N D 1 ↔ 0<∑ j : Fin B.length,divExpAlong n N D (B.get j) x := by
  rw [mem_cosupport_iff_of_isMonomialAlong hn hN hB hTr hc hne hm 1 hx]
  have hsum : (∑ i ∈ memberIdx B x,expDataAlong n N D B x i)=
      ∑ j : Fin B.length,divExpAlong n N D (B.get j) x := by
    rw [memberIdx,Finset.sum_map]
    simp only [Fin.valEmbedding_apply,expDataAlong,Fin.eta]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [dif_pos j.isLt]
    change (if x ∈ B.get j then divExpAlong n N D (B.get j) x else 0)=
      divExpAlong n N D (B.get j) x
    by_cases hxj : x ∈ B.get j
    · simp only [if_pos hxj]
    · simp only [if_neg hxj]
      exact (exponent_zero_of_not_mem (hN.1.inter (hB.1 _ (List.get_mem B j))) hxj).symm
  rw [hsum]
  omega


theorem principal_of_least_row {ι : Type*} (hn : 0<n) {N : Set X}
    {B : List (Set X)} (hN : IsClosedSubmanifold n N) (hB : IsSNCDivisor n B)
    (hTr : IsTransverse n N B) (D : ι → GermIdeal n X)
    (hc : ∀ i,(D i).IsCoherent) (hne : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (D i) y)
    (hm : ∀ i,IsMonomialAlong n N (D i) B) (P : Finset ι)
    {x : X} (hx : x ∈ N) (w : ι) (hw : w ∈ P)
    (hle : ∀ i ∈ P,∀ j : Fin B.length,
      divExpAlong n N (D w) (B.get j) x ≤ divExpAlong n N (D i) (B.get j) x) :
    IsPrincipalMonomialAlongAt n N (finiteSum D P) B x ∧
      ∀ g,IsInSpanOnAt (n := n) N ((finiteSum D P).mem x) x g ↔
        IsInSpanOnAt (n := n) N ((D w).mem x) x g := by
  classical
  obtain ⟨_kC,kN,Φ,σ,hsrc,hσk,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn subset_rfl hB hTr hTr.hasNormalCrossings hx
  have hNflat : ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kN) :=
    fun hy1 hy2 => (hflat hy1 hy2).2.1
  have hA : ∀ i,x ∈ B.get i → ∀ {y : X},y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ B.get i ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ i)=0) :=
    fun i hi _ hy1 hy2 => (hflat hy1 hy2).2.2 i hi
  let T : Finset (Fin B.length) := Finset.univ.filter fun j => x ∈ B.get j
  let a (i : ι) (j : Fin B.length) := divExpAlong n N (D i) (B.get j) x
  let m (i : ι) : X → ℂ := fun z => ∏ j ∈ T,flatCoord Φ (σ j) z ^ a i j
  have hgen (i : ι) (g : X → ℂ) : IsInSpanOnAt (n := n) N ((D i).mem x) x g ↔
      IsInSpanOnAt (n := n) N (·=m i) x g :=
    isInSpanOnAt_iff_generator_of_isMonomialAlong hsrc hNflat hA hn hN hB hTr
      (hc i) (hne i) (hm i) hx hσk hinj g
  have hrow (i : ι) (hi : i ∈ P) (g : X → ℂ)
      (hg : IsInSpanOnAt (n := n) N ((D i).mem x) x g) :
      IsInSpanOnAt (n := n) N ((D w).mem x) x g := by
    obtain ⟨c,hc0,hcg⟩ := isInSpanOnAt_eq_iff.mp ((hgen i g).mp hg)
    let q : X → ℂ := fun z => ∏ j ∈ T,flatCoord Φ (σ j) z ^ (a i j-a w j)
    have hq : HolomorphicAt n q x :=
      holomorphicAt_generator (σ := σ) T (fun j => a i j-a w j) (mem_flatDomain_self Φ)
    have heq (z : X) : m i z=q z*m w z := by
      simp only [m,q]
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _hj
      rw [←pow_add,Nat.sub_add_cancel (hle i hi j)]
    apply (hgen w g).mpr
    apply isInSpanOnAt_eq_iff.mpr
    refine ⟨fun z => c z*q z,hc0.mul hq,?_⟩
    filter_upwards [hcg] with z hz hzN
    rw [hz hzN,heq z]
    ring
  have hEq (g : X → ℂ) : IsInSpanOnAt (n := n) N ((finiteSum D P).mem x) x g ↔
      IsInSpanOnAt (n := n) N ((D w).mem x) x g := by
    constructor
    · intro hg
      apply IsInSpanOnAt.trans ?_ ((span_finiteSum_iff D hc P N x g).mp hg)
      rintro f ⟨i,hi,hf⟩
      exact hrow i hi f (IsInSpanAt.restrict (isInSpanAt_self hf
        (GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hf)))
    · exact IsInSpanOnAt.mono (fun f hf => le_finiteSum D hc hw x f hf)
  refine ⟨?_,hEq⟩
  exact ⟨kN,Φ,σ,a w,hsrc,hNflat,hσk,hinj,hA,fun g => (hEq g).trans (hgen w g)⟩

private theorem principal_of_one (hn : 0<n) {N : Set X} {B : List (Set X)}
    {I : GermIdeal n X} (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B)
    (hc : I.IsCoherent) {x : X} (hx : x ∈ N) (hOne : I.mem x (fun _ => (1 : ℂ))) :
    IsPrincipalMonomialAlongAt n N I B x := by
  classical
  obtain ⟨_kC,kN,Φ,σ,hsrc,hσk,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn subset_rfl hB hTr hTr.hasNormalCrossings hx
  have hgen (g : X → ℂ) : IsInSpanOnAt (n := n) N (I.mem x) x g ↔
      IsInSpanOnAt (n := n) N (·=fun _ => (1 : ℂ)) x g := by
    constructor
    · apply IsInSpanOnAt.trans
      intro f hf
      exact isInSpanOnAt_eq_iff.mpr ⟨f,GermIdeal.IsCoherent.holomorphicAt_mem hc hf,
        Eventually.of_forall fun _ _ => by simp⟩
    · exact IsInSpanOnAt.mono (by rintro f rfl; exact hOne)
  refine ⟨kN,Φ,σ,fun _ => 0,hsrc,fun hy1 hy2 => (hflat hy1 hy2).2.1,
    hσk,hinj,fun i hi _ hy1 hy2 => (hflat hy1 hy2).2.2 i hi,?_⟩
  intro g
  simpa only [pow_zero,Finset.prod_const_one] using hgen g


/-- The zero-residual SUM geometry, with no compactness premise. -/
theorem actual_zero_residual_mask_sum_geometry (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let I : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,I,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    I.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N I x) ∧
      IsMonomialAlong n N I born ∧ M.IsWellFormed ∧
      M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} ∧
      (∀ x ∈ M.cosupp,properRows (A x)=P ∧ ∃ w ∈ P,
        (∀ j,A x w j=gcdColumn (A x) j) ∧
        ∀ g,IsInSpanOnAt (n := n) N (I.mem x) x g ↔
          IsInSpanOnAt (n := n) N ((D w).mem x) x g) ∧
      M.IsAdmissibleCentre (maxLocusA M) ∧
      (∀ x ∈ maxLocusA M,∃ S : Finset (Fin born.length),
        S.Nonempty ∧ S ⊆ Finset.univ.filter (fun j => x ∈ born.get j) ∧
        ∀ᶠ y in 𝓝 x,y ∈ maxLocusA M ↔ y ∈ N ∧ y ∈ memberInter born S) := by
  classical
  let D := oldMonomialPart N old born
  let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
    divExpAlong n N (D i) (born.get j) x
  let I := finiteSum D P
  let M : MarkedIdeal n X := ⟨N,born,I,1⟩
  change (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) → _
  intro hTau hNu
  have hBorn : IsSNCDivisor n born :=
    isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hc (i : Fin old.length) : (D i).IsCoherent := (hParts i).2.2.2.2.1
  have hnz (i : Fin old.length) : ∀ x ∈ N,IsNonzeroAlongAt N (D i) x :=
    (hParts i).2.2.2.2.2.1
  have hm (i : Fin old.length) : IsMonomialAlong n N (D i) born :=
    (hParts i).2.2.2.2.2.2.1
  have hcI : I.IsCoherent := coherent_finiteSum D hc P
  obtain ⟨i0,hi0⟩ := hP
  have hnzI : ∀ x ∈ N,IsNonzeroAlongAt N I x := by
    intro x hx
    obtain ⟨g,hg,hfreq⟩ := hnz i0 x hx
    exact ⟨g,le_finiteSum D hc hi0 x g hg,hfreq⟩
  have hCosupp : M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} := by
    ext x
    change x ∈ cosupport n N (finiteSum D P) 1 ↔ _
    rw [cosupport_finiteSum_one D hc P N x]
    constructor
    · rintro ⟨hx,hall⟩
      refine ⟨hx,fun i hi => ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (row_cosupport_iff hn hN hBorn hTr (hc i) (hnz i) (hm i) hx).mp (hall i hi)⟩
    · rintro ⟨hx,hall⟩
      refine ⟨hx,fun i hi => ?_⟩
      exact (row_cosupport_iff hn hN hBorn hTr (hc i) (hnz i) (hm i) hx).mpr
        (Finset.mem_filter.mp (hall hi)).2
  have hData (x : X) (hx : x ∈ M.cosupp) :
      properRows (A x)=P ∧ ∃ w ∈ P,(∀ j,A x w j=gcdColumn (A x) j) ∧
        IsPrincipalMonomialAlongAt n N I born x ∧
        ∀ g,IsInSpanOnAt (n := n) N (I.mem x) x g ↔
          IsInSpanOnAt (n := n) N ((D w).mem x) x g := by
    obtain ⟨hxN,hsub⟩ := hCosupp ▸ hx
    have hProper : properRows (A x)=P :=
      (Finset.eq_of_subset_of_card_le hsub (hTau x hxN)).symm
    have hact : (properRows (A x)).Nonempty := by
      rw [hProper]
      exact ⟨i0,hi0⟩
    have hzero : nuOne (A x)=0 := hNu x hxN (by change (properRows (A x)).card=P.card; rw [hProper])
    obtain ⟨w,hw,hgcd⟩ := (nuOne_eq_zero_iff_exists_gcd_row (A x) hact).mp hzero
    have hwP : w ∈ P := hProper ▸ hw
    have hle (i : Fin old.length) (hi : i ∈ P) (j : Fin born.length) :
        divExpAlong n N (D w) (born.get j) x ≤ divExpAlong n N (D i) (born.get j) x := by
      change A x w j ≤ A x i j
      rw [hgcd j,gcdColumn,dif_pos hact]
      exact Finset.inf'_le _ (hProper.symm ▸ hi)
    obtain ⟨hPrincipal,hEq⟩ := principal_of_least_row hn hN hBorn hTr D hc hnz hm P hxN w hwP hle
    exact ⟨hProper,w,hwP,hgcd,hPrincipal,hEq⟩
  have hLoc (x : X) (hx : x ∈ N) : IsPrincipalMonomialAlongAt n N I born x := by
    by_cases hxs : x ∈ M.cosupp
    · obtain ⟨_hProper,w,_hw,_hgcd,hPrincipal,_hEq⟩ := hData x hxs
      exact hPrincipal
    · have hnot : ¬P ⊆ properRows (A x) := by
        intro hsub
        exact hxs (hCosupp.symm ▸ ⟨hx,hsub⟩)
      have hex : ∃ i ∈ P,i ∉ properRows (A x) := by
        by_contra hno
        apply hnot
        intro i hi
        by_contra hbad
        exact hno ⟨i,hi,hbad⟩
      obtain ⟨i,hi,hni⟩ := hex
      have hOrder : rowOrder (A x) i=0 := by
        have hpos : ¬0<rowOrder (A x) i := fun hp =>
          hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
        omega
      have hZero (j : Fin born.length) : divExpAlong n N (D i) (born.get j) x=0 := by
        have hle : A x i j ≤ rowOrder (A x) i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        rw [hOrder] at hle
        exact Nat.eq_zero_of_le_zero hle
      have hOne := one_mem_of_zero_canonical_row hn hN hBorn hTr (hc i) (hnz i) (hm i) hx hZero
      exact principal_of_one hn hBorn hTr hcI hx (le_finiteSum D hc hi x _ hOne)
  have hmI : IsMonomialAlong n N I born :=
    (isNonzeroAlongAt_and_isMonomialAlong_of_principal hn hN hBorn hTr hcI hLoc).2
  have hwf : M.IsWellFormed := ⟨hN,hcI,hBorn,hTr⟩
  have hCentre := isAdmissibleCentre_maxLocusA hn hwf hnzI hmI
  have hLocalCentre : ∀ x ∈ maxLocusA M,∃ S : Finset (Fin born.length),
      S.Nonempty ∧ S ⊆ Finset.univ.filter (fun j => x ∈ born.get j) ∧
      ∀ᶠ y in 𝓝 x,y ∈ maxLocusA M ↔ y ∈ N ∧ y ∈ memberInter born S := by
    intro x hx
    have hxN : x ∈ N := hx.1.1
    cases hv : gammaAlong n N I born 1 x with
    | bot =>
      exact ((gammaAlong_eq_bot_iff_of_isMonomialAlong hn hN hBorn hTr hcI hnzI hmI 1 hxN).mp hv hx.1).elim
    | coe v =>
      let S := topIdx born v
      have hTop := (top_of_gammaAlong_eq hv).1
      have hWeight := (MonomialInvariant.mem_feasible.mp hTop).2
      rw [←sum_topIdx_eq_along (𝔪 := M) hv] at hWeight
      have hNonempty : S.Nonempty := by
        by_contra hno
        have hEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hno
        change 1 ≤ ∑ j ∈ S,divExpAlong n N I (born.get j) x at hWeight
        simp only [hEmpty,Finset.sum_empty] at hWeight
        omega
      have hxS := mem_memberInter_of_gammaAlong_eq hn hN hBorn hTr hcI hnzI hxN hv
      refine ⟨S,hNonempty,fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxS j hj⟩,?_⟩
      exact eventually_mem_maxLocusA_iff hn hwf hnzI hmI hx hv
  refine ⟨hcI,hnzI,hmI,hwf,hCosupp,?_,hCentre,hLocalCentre⟩
  · intro x hx
    obtain ⟨hProper,w,hw,hgcd,_hPrincipal,hEq⟩ := hData x hx
    exact ⟨hProper,w,hw,hgcd,hEq⟩

theorem actual_zero_residual_mask_sum_monomial (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let I : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,I,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    IsCompact M.cosupp →
    I.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N I x) ∧
      IsMonomialAlong n N I born ∧ M.IsWellFormed ∧
      M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} ∧
      (∀ x ∈ M.cosupp,properRows (A x)=P ∧ ∃ w ∈ P,
        (∀ j,A x w j=gcdColumn (A x) j) ∧
        ∀ g,IsInSpanOnAt (n := n) N (I.mem x) x g ↔
          IsInSpanOnAt (n := n) N ((D w).mem x) x g) ∧
      M.IsAdmissibleCentre (maxLocusA M) ∧
      (∀ x ∈ maxLocusA M,∃ S : Finset (Fin born.length),
        S.Nonempty ∧ S ⊆ Finset.univ.filter (fun j => x ∈ born.get j) ∧
        ∀ᶠ y in 𝓝 x,y ∈ maxLocusA M ↔ y ∈ N ∧ y ∈ memberInter born S) ∧
      ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
        ResolutionDriver.IsCanonicalSegment M (fun {Y} T => towerInvAlong M (Y := Y) T) T ∧
        IsGeoResolution M T := by
  classical
  dsimp only
  intro hTau hNu hK
  obtain ⟨hc,hNZ,hMono,hWF,hCos,hRows,hCentre,hLocal⟩ :=
    actual_zero_residual_mask_sum_geometry hn hN hE hTr hdense P hP hTau hNu
  refine ⟨hc,hNZ,hMono,hWF,hCos,hRows,hCentre,hLocal,?_⟩
  exact MonomialCaseLocal.exists_isGeoResolution_of_monomialAlong_of_isCompact
    hn _ hWF hNZ hMono (show 1 ≤ 1 from Nat.le_refl 1) hK


/-- The same actual SUM has a terminating native Gamma history on a noncompact
source under a shaped bound on its original invariant. -/
theorem actual_zero_residual_mask_sum_noncompact_of_bound (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (P : Finset (Fin old.length)) (hP : P.Nonempty) :
    let D := oldMonomialPart N old born
    let A : X → Fin old.length → Fin born.length → ℕ := fun x i j =>
      divExpAlong n N (D i) (born.get j) x
    let I : GermIdeal n X := ⟨fun x g =>
      IsInSpanAt (n := n) (fun f => ∃ i ∈ P,(D i).mem x f) x g⟩
    let M : MarkedIdeal n X := ⟨N,born,I,1⟩
    (∀ x ∈ N,tauD (A x) ≤ P.card) →
    (∀ x ∈ N,tauD (A x)=P.card → nuOne (A x)=0) →
    (v : MonomialInvariant.Val) → (ofLex v).1 = n - 1 →
    (∀ x ∈ M.cosupp, gammaAlong n M.N M.ideal M.E M.d x ≤ (v : WithBot MonomialInvariant.Val)) →
    I.IsCoherent ∧ (∀ x ∈ N,IsNonzeroAlongAt N I x) ∧
      IsMonomialAlong n N I born ∧ M.IsWellFormed ∧
      M.cosupp={x | x ∈ N ∧ P ⊆ properRows (A x)} ∧
      (∀ x ∈ M.cosupp,properRows (A x)=P ∧ ∃ w ∈ P,
        (∀ j,A x w j=gcdColumn (A x) j) ∧
        ∀ g,IsInSpanOnAt (n := n) N (I.mem x) x g ↔
          IsInSpanOnAt (n := n) N ((D w).mem x) x g) ∧
      M.IsAdmissibleCentre (maxLocusA M) ∧
      (∀ x ∈ maxLocusA M,∃ S : Finset (Fin born.length),
        S.Nonempty ∧ S ⊆ Finset.univ.filter (fun j => x ∈ born.get j) ∧
        ∀ᶠ y in 𝓝 x,y ∈ maxLocusA M ↔ y ∈ N ∧ y ∈ memberInter born S) ∧
      ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
        ResolutionDriver.IsCanonicalSegment M (fun {Y} T => towerInvAlong M (Y := Y) T) T ∧
        IsGeoResolution M T := by
  classical
  dsimp only
  intro hTau hNu v hFirst hBound
  obtain ⟨hc,hNZ,hMono,hWF,hCos,hRows,hCentre,hLocal⟩ :=
    actual_zero_residual_mask_sum_geometry hn hN hE hTr hdense P hP hTau hNu
  refine ⟨hc,hNZ,hMono,hWF,hCos,hRows,hCentre,hLocal,?_⟩
  exact HironakaMarkOneNoncompactNativePhase.exists_markOne_native_resolution_of_bound
    hn _ hWF hNZ hMono rfl v hFirst hBound

end
end Hironaka.HironakaG4ZeroResidualMonomialSum
