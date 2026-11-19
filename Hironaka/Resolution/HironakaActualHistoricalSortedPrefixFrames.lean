import Hironaka.Resolution.HironakaActualHistoricalNormalizedWeakPresentation

/-! The original labels are degree ordered ONCE. Every later literal degree
prefix is the SAME ordered words/members after the actual finite cast, and
all whole/homogeneous frames transport at EVERY natural cutoff. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalSortedPrefixFrames
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames

variable {n k l : ℕ}

/-- The literal FULL degree-prefix positions enumerate ALL original labels.
The original bound is actual finite source data, not a target rank witness. -/
def historicalDegreeFullLabelEquiv (w : Fin k → CoordinateWord n) (M : ℕ)
    (hBound : ∀j,normalExponentDegree (wordExponent (w j))≤M) :
    Fin (historicalDegreePrefixCount w M) ≃ Fin k :=
  (historicalDegreePrefixLabelEquiv w M).trans {
    toFun:=Subtype.val
    invFun:=fun j=>⟨j,hBound j⟩
    left_inv:=fun _=>Subtype.ext rfl
    right_inv:=fun _=>rfl }

/-- A genuine original label equivalence preserves every literal prefix
COUNT, before any frame or order law is considered. -/
theorem historical_degree_prefix_count_reindex (w : Fin k → CoordinateWord n)
    (p : Fin l ≃ Fin k) (m : ℕ) :
    historicalDegreePrefixCount (fun j=>w (p j)) m=historicalDegreePrefixCount w m := by
  let eFiltered : {j : Fin l // normalExponentDegree (wordExponent (w (p j)))≤m} ≃
      {i : Fin k // normalExponentDegree (wordExponent (w i))≤m} := {
    toFun:=fun j=>⟨p j.val,j.property⟩
    invFun:=fun i=>⟨p.symm i.val,by simpa only [p.apply_symm_apply] using i.property⟩
    left_inv:=fun j=>Subtype.ext (p.symm_apply_apply j.val)
    right_inv:=fun i=>Subtype.ext (p.apply_symm_apply i.val) }
  let e:=(historicalDegreePrefixLabelEquiv (fun j=>w (p j)) m).trans
    (eFiltered.trans (historicalDegreePrefixLabelEquiv w m).symm)
  simpa only [Fintype.card_fin] using Fintype.card_congr e

private theorem reindexed_degree_key_strictMono (w : Fin k → CoordinateWord n)
    (p : Fin l ≃ Fin k) (hSorted : StrictMono (fun j=>historicalDegreeKey w (p j))) :
    StrictMono (historicalDegreeKey (fun j=>w (p j))) := by
  intro i j hij
  have h:=hSorted hij
  change toLex (normalExponentDegree (wordExponent (w (p i))),p i)<
    toLex (normalExponentDegree (wordExponent (w (p j))),p j) at h
  change toLex (normalExponentDegree (wordExponent (w (p i))),i)<
    toLex (normalExponentDegree (wordExponent (w (p j))),j)
  exact Prod.Lex.toLex_lt_toLex'.mpr ⟨(Prod.Lex.toLex_lt_toLex'.mp h).1,fun _=>hij⟩

/-- Sorting the SAME already degree-ordered original list again on any
degree prefix gives the LITERAL same old label map after the finite cast. -/
theorem historical_sorted_reindex_prefix_label (w : Fin k → CoordinateWord n)
    (p : Fin l ≃ Fin k) (hSorted : StrictMono (fun j=>historicalDegreeKey w (p j)))
    (m : ℕ) (j : Fin (historicalDegreePrefixCount (fun i=>w (p i)) m)) :
    p (historicalDegreePrefixLabel (fun i=>w (p i)) m j)=
      historicalDegreePrefixLabel w m (Fin.cast (historical_degree_prefix_count_reindex w p m) j) := by
  let v:=fun i=>w (p i)
  let hCount:=historical_degree_prefix_count_reindex w p m
  have hCard : (historicalDegreePrefixKeys w m).card=historicalDegreePrefixCount v m:=hCount.symm
  have hKey:=reindexed_degree_key_strictMono w p hSorted
  have hLabel : StrictMono (historicalDegreePrefixLabel v m) := by
    intro a b hab
    exact hKey.lt_iff_lt.mp (historicalDegreePrefixLabel_strictMono v m hab)
  have hFmem (i : Fin (historicalDegreePrefixCount v m)) :
      historicalDegreeKey w (p (historicalDegreePrefixLabel v m i))∈historicalDegreePrefixKeys w m := by
    apply Finset.mem_image.mpr
    refine ⟨p (historicalDegreePrefixLabel v m i),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact historicalDegreePrefixLabel_mem v m i
  have hGmem (i : Fin (historicalDegreePrefixCount v m)) :
      historicalDegreeKey w (historicalDegreePrefixLabel w m (Fin.cast hCount i))∈
        historicalDegreePrefixKeys w m := by
    rw [historicalDegreePrefixLabel_key]
    exact ((historicalDegreePrefixKeys w m).orderIsoOfFin rfl (Fin.cast hCount i)).property
  have hF:=Finset.orderEmbOfFin_unique hCard hFmem (hSorted.comp hLabel)
  have hG:=Finset.orderEmbOfFin_unique hCard hGmem
    ((historicalDegreePrefixLabel_strictMono w m).comp (Fin.cast_strictMono hCount))
  have hEqual:=congrFun (hF.trans hG.symm) j
  exact congrArg (fun z : Lex (ℕ × Fin k)=>(ofLex z).2) hEqual

private theorem frame_cast {r s : ℕ} (h : r=s) (v : Fin s → CoordinateWord n)
    (g : Fin s → MvPowerSeries (Fin n) ℂ) :
    ((∀q,Function.Bijective (historicalWholeJetMap v g q)) ∧
      ∀d,Function.Bijective (historicalHomogeneousColumnMap v g d)) →
    ((∀q,Function.Bijective (historicalWholeJetMap (fun j : Fin r=>v (Fin.cast h j))
      (fun j=>g (Fin.cast h j)) q)) ∧
      ∀d,Function.Bijective (historicalHomogeneousColumnMap (fun j : Fin r=>v (Fin.cast h j))
        (fun j=>g (Fin.cast h j)) d)) := by
  cases h
  exact id

/-- The one original degree ordering transports ALL whole/homogeneous
prefix frames with literal original words/members, for EVERY natural m. -/
theorem historical_sorted_reindex_prefix_frames (w : Fin k → CoordinateWord n)
    (g : Fin k → MvPowerSeries (Fin n) ℂ) (p : Fin l ≃ Fin k)
    (hSorted : StrictMono (fun j=>historicalDegreeKey w (p j)))
    (hFrames : ∀m,HistoricalDegreePrefixFrames w g m) :
    ∀m,HistoricalDegreePrefixFrames (fun j=>w (p j)) (fun j=>g (p j)) m := by
  intro m
  let v:=fun j=>w (p j)
  let hCount:=historical_degree_prefix_count_reindex w p m
  have hWords : historicalDegreePrefixWords v m=
      fun j=>historicalDegreePrefixWords w m (Fin.cast hCount j) := by
    funext j
    exact congrArg w (historical_sorted_reindex_prefix_label w p hSorted m j)
  have hMembers : (fun j=>g (p (historicalDegreePrefixLabel v m j)))=
      fun j=>g (historicalDegreePrefixLabel w m (Fin.cast hCount j)) := by
    funext j
    exact congrArg g (historical_sorted_reindex_prefix_label w p hSorted m j)
  unfold HistoricalDegreePrefixFrames
  rw [hWords,hMembers]
  exact frame_cast hCount (historicalDegreePrefixWords w m)
    (fun j=>g (historicalDegreePrefixLabel w m j)) (hFrames m)

end
end Hironaka.HironakaActualHistoricalSortedPrefixFrames
