import Hironaka.Resolution.HironakaG4PreparedCentreCoordinates
import Hironaka.Resolution.HironakaG4MonomialTopStratum
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MemberInterAlong
import Hironaka.Analytic.AnalyticSubsetOpens

/-! Actual original canonical D-matrix windows and first-pair strata.
Complete source-first proof: hironaka-g4-actual-monomial-pair-windows.tex.
No prepared residual, centre, selector, future history or termination premise.
The top locus is a finite union of actual born intersections, not a centre. -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4ActualMonomialPairWindows

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings NormalCrossingsComparison MonomialCase MonomialCaseAlong
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaG4MonomialMaximalContact HironakaG4MonomialTopStratum
  DivisorExponentAlong BoundaryCount ResolutionInvariantOrder

variable {n : ℕ} {X : CMfd.{u} n}

private theorem exponent_zero_of_not_mem {N H : Set X} {I : GermIdeal n X}
    (hc : IsClosed (N ∩ H)) {x : X} (hx : x ∉ H) :
    divExpAlong n N I H x=0 := by
  have hnot : ¬∃ e,¬IsDivNearAlong n N I H (e+1) x := by
    rintro ⟨e,he⟩
    exact he (isDivNearAlong_of_notMem hc (fun h => hx h.2) (e+1))
  unfold divExpAlong
  rw [dif_neg hnot]

private theorem eventually_matrix_restriction {r : ℕ} (hn : 0 < n)
    {N : Set X} {B : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hB : IsSNCDivisor n B) (hTr : IsTransverse n N B)
    (I : Fin r → GermIdeal n X) (hc : ∀ i,(I i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (I i) y) {x : X} (hx : x ∈ N) :
    let A : X → Fin r → Fin B.length → ℕ := fun y i j =>
      divExpAlong n N (I i) (B.get j) y
    let K : X → Finset (Fin B.length) := fun y =>
      Finset.univ.filter fun j => y ∈ B.get j
    ∀ᶠ y in 𝓝 x,y ∈ N → K y ⊆ K x ∧ A y=restrictIncidence (A x) (K y) := by
  classical
  let A : X → Fin r → Fin B.length → ℕ := fun y i j =>
    divExpAlong n N (I i) (B.get j) y
  let K : X → Finset (Fin B.length) := fun y =>
    Finset.univ.filter fun j => y ∈ B.get j
  change ∀ᶠ y in 𝓝 x,y ∈ N → K y ⊆ K x ∧ A y=restrictIncidence (A x) (K y)
  have hrow (i : Fin r) := eventually_expDataAlong_eq hn hN hB hTr (hc i) (hnz i) hx
  filter_upwards [eventually_all.mpr hrow,eventually_memberIdx_subset B hB.1 x]
    with y hy hsub hyN
  refine ⟨?_,?_⟩
  · intro j hj
    have hyj : y ∈ B.get j := (Finset.mem_filter.mp hj).2
    obtain ⟨_hlt,hxj⟩ := (mem_memberIdx B).mp
      (hsub ((mem_memberIdx B).mpr ⟨j.isLt,hyj⟩))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using hxj⟩
  · funext i j
    by_cases hyj : y ∈ B.get j
    · have he := hy i hyN j.val ((mem_memberIdx B).mpr ⟨j.isLt,hyj⟩)
      have he' : A y i j=A x i j := by
        simpa only [A,expDataAlong,dif_pos j.isLt] using he
      simpa only [restrictIncidence,K,Finset.mem_filter,Finset.mem_univ,true_and,
        if_pos hyj] using he'
    · simp only [restrictIncidence,K,Finset.mem_filter,Finset.mem_univ,true_and,
        if_neg hyj]
      exact exponent_zero_of_not_mem (hN.1.inter (hB.1 _ (List.get_mem B j))) hyj

private theorem pair_restriction_le {r b : ℕ} (A : Fin r → Fin b → ℕ)
    (K : Finset (Fin b)) :
    tauD (restrictIncidence A K) ≤ tauD A ∧
      (tauD (restrictIncidence A K)=tauD A →
        nuOne (restrictIncidence A K) ≤ nuOne A) := by
  classical
  have hsub : properRows (restrictIncidence A K) ⊆ properRows A := by
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    have heq : rowOrder (restrictIncidence A K) i=rowWeight (A i) K := by
      simp [rowOrder,restrictIncidence,rowWeight]
    have hle : rowWeight (A i) K ≤ rowOrder A i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ K)
    rw [heq] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le hp hle⟩
  refine ⟨Finset.card_le_card hsub,fun htau => ?_⟩
  rw [nuOne_restrictIncidence_of_tau_eq A K htau]
  by_cases ha : (properRows A).Nonempty
  · obtain ⟨i,hi,hmin⟩ := Finset.exists_mem_eq_inf' ha
      (fun i => ∑ j,(A i j-gcdColumn A j))
    rw [fixedResidualMinimum,dif_pos ha,nuOne,dif_pos ha]
    calc
      (properRows A).inf' ha (fun i => residualWeight A i K) ≤ residualWeight A i K :=
        Finset.inf'_le _ hi
      _ ≤ ∑ j,(A i j-gcdColumn A j) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ K)
      _ = (properRows A).inf' ha (fun i => ∑ j,(A i j-gcdColumn A j)) := hmin.symm
  · simp [fixedResidualMinimum,nuOne,ha]

theorem companion_mono {r b : ℕ} (A : Fin r → Fin b → ℕ)
    {S K : Finset (Fin b)} (hSK : S ⊆ K)
    (h : TopCompanionCosupport A 1 S) : TopCompanionCosupport A 1 K := by
  rcases h with ⟨ha,h⟩
  refine ⟨ha,?_⟩
  by_cases hz : nuOne A=0
  · simp only [hz,if_true] at h ⊢
    exact h.trans (Finset.sum_le_sum_of_subset hSK)
  · simp only [hz,if_false] at h ⊢
    exact ⟨fun i hi => (h.1 i hi).trans (Finset.sum_le_sum_of_subset hSK),
      fun hl => (h.2 hl).trans (Finset.sum_le_sum_of_subset hSK)⟩

private theorem analytic_finset_union {ι : Type*} (t : Finset ι) (C : ι → Set X)
    (hC : ∀ i ∈ t,IsComplexAnalyticSubset (n := n) (C i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t,C i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hC i (Finset.mem_insert_self i t))
      (ih (fun j hj => hC j (Finset.mem_insert_of_mem hj)))

/-- ONLY genuine current original geometry produces real canonical D-matrix
windows, finite actual matrix ranges, native first-pair USC and the literal
active top-pair analytic locus. No top-locus smoothness or centre is claimed. -/
theorem exists_actual_old_monomial_pair_window (hn : 0 < n)
    {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H)) :
    let A : X → Fin old.length → Fin born.length → ℕ := fun y i j =>
      divExpAlong n N (oldMonomialPart N old born i) (born.get j) y
    let K : X → Finset (Fin born.length) := fun y =>
      Finset.univ.filter fun j => y ∈ born.get j
    IsInvUSCOn (fun y => toLex (tauD (A y),nuOne (A y))) N ∧
      ∀ x ∈ N,∃ U : Opens X,x ∈ U ∧
        (∀ y ∈ N,y ∈ U → K y ⊆ K x ∧ A y=restrictIncidence (A x) (K y)) ∧
        (A '' (N ∩ (U : Set X))).Finite ∧
        (∀ y ∈ N,y ∈ U → tauD (A y) ≤ tauD (A x) ∧
          (tauD (A y)=tauD (A x) → nuOne (A y) ≤ nuOne (A x))) ∧
        (0<tauD (A x) →
          let F : Finset (Finset (Fin born.length)) := Finset.univ.filter fun S =>
            S ⊆ K x ∧ TopCompanionCosupport (A x) 1 S
          let L : Set X := {y | y ∈ N ∧ tauD (A y)=tauD (A x) ∧
            nuOne (A y)=nuOne (A x)}
          (Subtype.val : U → X) ⁻¹' L =
            (⋃ S ∈ F,(Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S)) ∧
          IsComplexAnalyticSubset (n := n) ((Subtype.val : U → X) ⁻¹' L)) := by
  classical
  let A : X → Fin old.length → Fin born.length → ℕ := fun y i j =>
    divExpAlong n N (oldMonomialPart N old born i) (born.get j) y
  let K : X → Finset (Fin born.length) := fun y =>
    Finset.univ.filter fun j => y ∈ born.get j
  change IsInvUSCOn (fun y => toLex (tauD (A y),nuOne (A y))) N ∧ _
  have hBorn : IsSNCDivisor n born :=
    isSNCDivisor_of_sublist hE (List.sublist_append_right old born)
  have hParts (i : Fin old.length) := actual_old_parts_geometry hn hN hE hTr hdense i
  have hc (i : Fin old.length) : (oldMonomialPart N old born i).IsCoherent :=
    (hParts i).2.2.2.2.1
  have hnz (i : Fin old.length) :
      ∀ y ∈ N,IsNonzeroAlongAt N (oldMonomialPart N old born i) y :=
    (hParts i).2.2.2.2.2.1
  have hWindow (x : X) (hx : x ∈ N) :
      ∀ᶠ y in 𝓝 x,y ∈ N → K y ⊆ K x ∧ A y=restrictIncidence (A x) (K y) :=
    eventually_matrix_restriction hn hN hBorn hTr (oldMonomialPart N old born) hc hnz hx
  refine ⟨?_,?_⟩
  · intro x hx
    filter_upwards [hWindow x hx] with y hy hyN
    obtain ⟨_hSub,hMat⟩ := hy hyN
    have hb := pair_restriction_le (A x) (K y)
    rw [←hMat] at hb
    apply Prod.Lex.toLex_le_toLex.mpr
    rcases lt_or_eq_of_le hb.1 with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq,hb.2 heq⟩
  · intro x hx
    obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp (hWindow x hx)
    let U : Opens X := ⟨V,hVo⟩
    have hMat (y : X) (hyN : y ∈ N) (hyU : y ∈ U) :
        K y ⊆ K x ∧ A y=restrictIncidence (A x) (K y) := hVsub hyU hyN
    refine ⟨U,hxV,hMat,?_,?_,?_⟩
    · apply (Set.finite_range (fun S : Finset (Fin born.length) =>
        restrictIncidence (A x) S)).subset
      rintro _ ⟨y,⟨hyN,hyU⟩,rfl⟩
      exact ⟨K y,(hMat y hyN hyU).2.symm⟩
    · intro y hyN hyU
      change tauD (A y) ≤ tauD (A x) ∧
        (tauD (A y)=tauD (A x) → nuOne (A y) ≤ nuOne (A x))
      rw [(hMat y hyN hyU).2]
      exact pair_restriction_le (A x) (K y)
    · intro hpos
      let F : Finset (Finset (Fin born.length)) := Finset.univ.filter fun S =>
        S ⊆ K x ∧ TopCompanionCosupport (A x) 1 S
      let L : Set X := {y | y ∈ N ∧ tauD (A y)=tauD (A x) ∧
        nuOne (A y)=nuOne (A x)}
      change (Subtype.val : U → X) ⁻¹' L =
        (⋃ S ∈ F,(Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S)) ∧ _
      have hEq : (Subtype.val : U → X) ⁻¹' L =
          ⋃ S ∈ F,(Subtype.val : U → X) ⁻¹' (N ∩ memberInter born S) := by
        ext y
        constructor
        · rintro ⟨hyN,hTau,hNu⟩
          obtain ⟨hSub,hMatrix⟩ := hMat y hyN y.property
          have hComp : TopCompanionCosupport (A x) 1 (K y) := by
            apply (top_companion_iff_retained_tau_nu (A x) (K y)).mpr
            rw [←hMatrix]
            exact ⟨hpos,hTau,hNu⟩
          refine mem_iUnion₂.mpr ⟨K y,Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,hSub,hComp⟩,hyN,?_⟩
          intro j hj
          exact (Finset.mem_filter.mp hj).2
        · intro hy
          obtain ⟨S,hSF,hyN,hyS⟩ := mem_iUnion₂.mp hy
          have hSK : S ⊆ K y := fun j hj =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyS j hj⟩
          have hComp := companion_mono (A x) hSK (Finset.mem_filter.mp hSF).2.2
          have hPair := (top_companion_iff_retained_tau_nu (A x) (K y)).mp hComp
          rw [←(hMat y hyN y.property).2] at hPair
          exact ⟨hyN,hPair.2.1,hPair.2.2⟩
      refine ⟨hEq,?_⟩
      have hAnalytic : IsComplexAnalyticSubset (n := n)
          (⋃ S ∈ F,N ∩ memberInter born S) := by
        apply analytic_finset_union F
        intro S _hS
        exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
          (MemberInterAlong.isClosedSubmanifold_inter_memberInter hn hN.1 hBorn hTr S)
      rw [hEq]
      simpa only [Set.preimage_iUnion] using
        AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hAnalytic U

end
end Hironaka.HironakaG4ActualMonomialPairWindows
