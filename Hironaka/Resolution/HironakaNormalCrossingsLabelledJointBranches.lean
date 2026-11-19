import Hironaka.Resolution.HironakaNormalCrossingsLabelledBoundaryTransport
import Hironaka.Resolution.HironakaNormalCrossingsJointBranchCharts

/-!
# Same actual labelled coordinates supply old branch groups and the whole born list

The original whole labelled NC list and actual SNC born list internally
produce every local branch and original position group in the SAME chart.
No grouping, centre permission or history certificate is an input.
Blueprint: `hironaka-normal-crossings-labelled-joint-branches-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsLabelledJointBranches
noncomputable section
open Hironaka.BlowupSequences NormalCrossings BlowupFlatCoordinates
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsLabelledBoundary
  HironakaNormalCrossingsLabelledBoundaryTransport HironakaNormalCrossingsJointBranchCharts
  BlowupTowers NormalCrossingsInvariance
variable {n : ℕ} {X : CMfd.{u} n}

private theorem shared_coordinates {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (x : X) :
    ∃ (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (a : Fin L.length → Finset (Fin n)) (b : Fin E.length → Finset (Fin n)),
      Φ.source⊆(chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀ i j,i≠j → Disjoint (a i) (a j)) ∧
      (∀ i j,i≠j → Disjoint (b i) (b j)) ∧
      (∀ i j,Disjoint (a i) (b j)) ∧
      (∀ i y,y∈flatDomain Φ → (y∈L.get i ↔ ∃ k∈a i,flatCoord Φ k y=0)) ∧
      (∀ i y,y∈flatDomain Φ → (y∈E.get i ↔ ∃ k∈b i,flatCoord Φ k y=0)) := by
  obtain ⟨Φ,S,hsrc,h0,hdis,hEq⟩ := h.2 x
  let il (i : Fin L.length) : Fin (L++E).length := ⟨i.val,by rw [List.length_append];omega⟩
  let ir (i : Fin E.length) : Fin (L++E).length := ⟨L.length+i.val,by rw [List.length_append];omega⟩
  have hleft (i : Fin L.length) : (L++E).get (il i)=L.get i := by
    change (L++E)[i.val]=L[i.val]
    exact List.getElem_append_left i.isLt
  have hright (i : Fin E.length) : (L++E).get (ir i)=E.get i := by
    change (L++E)[L.length+i.val]=E[i.val]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
  refine ⟨Φ,(fun i=>S (il i)),(fun i=>S (ir i)),hsrc,h0,?_,?_,?_,?_,?_⟩
  · intro i j hij
    apply hdis
    intro he
    apply hij
    have hv := congrArg Fin.val he
    exact Fin.ext hv
  · intro i j hij
    apply hdis
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val he
    change L.length+i.val=L.length+j.val at hv
    omega
  · intro i j
    apply hdis
    intro he
    have hv := congrArg Fin.val he
    change i.val=L.length+j.val at hv
    have hi := i.isLt
    omega
  · intro i y hy
    simpa only [hleft] using hEq (il i) y hy
  · intro i y hy
    simpa only [hright] using hEq (ir i) y hy

private theorem born_singleton_in_shared_coordinates {E : List (Set X)}
    (hE : IsSNCDivisor n E) {x : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (b : Fin E.length → Finset (Fin n))
    (hEq : ∀ i y,y∈flatDomain Φ → (y∈E.get i ↔ ∃ k∈b i,flatCoord Φ k y=0))
    (i : Fin E.length) (hi : x∈E.get i) : (b i).card=1 := by
  let hNC := isNormalCrossingsCarrier_get (isNormalCrossingsBoundary_of_snc hE) i
  have hShared := branchMultiplicity_eq_card hNC Φ h0 (b i) (hEq i)
  obtain ⟨D,⟨Ψ,_hsrc,hΨ0,hΨ⟩,hcard,_hinj⟩ := hE.2 x
  have hOwn : branchMultiplicity hNC x=(D i).card := by
    apply branchMultiplicity_eq_card hNC Ψ hΨ0 (D i)
    intro y hy
    have he := hΨ i hi hy.1 hy.2
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard i hi)
    rw [ha] at he ⊢
    simpa only [coordSubspace,mem_ofPred_eq,Finset.mem_singleton,forall_eq,
      exists_eq_left,flatCoord,complexChartAt] using he
  exact hShared.symm.trans (hOwn.trans (hcard i hi))

private theorem old_union_reader {L : List (Set X)} {x : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (a : Fin L.length → Finset (Fin n))
    (hEq : ∀ i y,y∈flatDomain Φ → (y∈L.get i ↔ ∃ k∈a i,flatCoord Φ k y=0)) :
    ∀ y∈flatDomain Φ,y∈(⋃ A∈L,A) ↔ ∃ k∈Finset.univ.biUnion a,flatCoord Φ k y=0 := by
  intro y hy
  constructor
  · intro h
    obtain ⟨A,hA,hyA⟩ := mem_iUnion₂.mp h
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hA
    obtain ⟨k,hk,hzero⟩ := (hEq i y hy).mp hyA
    exact ⟨k,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hk⟩,hzero⟩
  · rintro ⟨k,hk,hzero⟩
    obtain ⟨i,_hi,hki⟩ := Finset.mem_biUnion.mp hk
    exact mem_iUnion₂.mpr ⟨L.get i,List.get_mem _ _,(hEq i y hy).mpr ⟨k,hki,hzero⟩⟩

/-- The ORIGINAL whole labelled input supplies an actual old-union/born
adapted pair, using the SAME shared flattening for every original position. -/
theorem boundaryAdapted_union_of_labelled {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E) :
    IsBoundaryAdaptedCarrier (n:=n) (⋃ A∈L,A) E := by
  refine ⟨(List.finite_toSet L).isClosed_biUnion (fun A hA=>h.1 A (List.mem_append_left _ hA)),hE.1,?_⟩
  intro x
  obtain ⟨Φ,a,b,hsrc,h0,ha,hb,hab,hOld,hBorn⟩ := shared_coordinates h x
  let S:=Finset.univ.biUnion a
  have hcard (i : Fin E.length) (hi : x∈E.get i) : (b i).card=1 :=
    born_singleton_in_shared_coordinates hE Φ h0 b hBorn i hi
  have hdis (i : Fin E.length) : Disjoint S (b i) := by
    apply Finset.disjoint_left.mpr
    intro k hk hki
    obtain ⟨j,_hj,hkj⟩ := Finset.mem_biUnion.mp hk
    exact Finset.disjoint_left.mp (hab j i) hkj hki
  refine ⟨Φ,S,b,hsrc,h0,old_union_reader Φ a hOld,(fun i hi=>⟨hcard i hi,hdis i⟩),?_,?_⟩
  · intro i hi j _hj he
    by_contra hij
    obtain ⟨k,hk⟩ := Finset.card_pos.mp (by rw [hcard i hi];omega)
    exact Finset.disjoint_left.mp (hb i j hij) hk (he ▸ hk)
  · intro i hi y hy
    have he := hBorn i y hy
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp (hcard i hi)
    rw [hk] at he ⊢
    simpa only [coordSubspace,mem_ofPred_eq,Finset.mem_singleton,forall_eq,
      exists_eq_left,flatCoord,complexChartAt] using he

private theorem injOn_append_nonempty {a b : ℕ}
    (A : Fin a→Finset (Fin n)) (B : Fin b→Finset (Fin n))
    (hA : Set.InjOn A {i | (A i).Nonempty}) (hB : Set.InjOn B {i | (B i).Nonempty})
    (hdis : ∀ i j,Disjoint (A i) (B j)) :
    Set.InjOn (Fin.append A B) {i | (Fin.append A B i).Nonempty} := by
  intro i hi j hj heq
  revert hi j hj heq
  refine Fin.addCases ?_ ?_ i
  · intro i hi j hj heq
    revert hj heq
    refine Fin.addCases ?_ ?_ j
    · intro j hj heq
      simp only [Set.mem_ofPred_eq,Fin.append_left] at hi hj heq
      exact congrArg (Fin.castAdd b) (hA hi hj heq)
    · intro j _hj heq
      simp only [Set.mem_ofPred_eq,Fin.append_left,Fin.append_right] at hi heq
      obtain ⟨v,hv⟩ := hi
      exact False.elim (Finset.disjoint_left.mp (hdis i j) hv (heq ▸ hv))
  · intro i hi j hj heq
    revert hj heq
    refine Fin.addCases ?_ ?_ j
    · intro j hj heq
      simp only [Set.mem_ofPred_eq,Fin.append_left,Fin.append_right] at hj heq
      obtain ⟨v,hv⟩ := hj
      exact False.elim (Finset.disjoint_left.mp (hdis j i) hv (heq.symm ▸ hv))
    · intro j hj heq
      simp only [Set.mem_ofPred_eq,Fin.append_right] at hi hj heq
      exact congrArg (Fin.natAdd a) (hB hi hj heq)


/-- SAME labelled coordinates internally give every original position group,
all actual branches, and the ENTIRE born trace as one true SNC family. -/
theorem exists_labelled_joint_branch_chart {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E) (x : X) :
    let hPair := boundaryAdapted_union_of_labelled h hE
    ∃ (U : Opens X) (B : List (Set U)) (G : Fin L.length → Finset (Fin B.length)),
      x∈U ∧ IsSNCDivisor n (B++E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (∀ i j,i≠j → Disjoint (G i) (G j)) ∧
      (∀ i,(Subtype.val : U → X) ⁻¹' L.get i=⋃ j∈G i,B.get j) ∧
      (Subtype.val : U → X) ⁻¹' (⋃ A∈L,A)=(⋃ A∈B,A) ∧
      ∀ r : ℕ,(∀ y : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hPair) y≤r) →
        r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hPair) x →
        ∀ C∈B,(Subtype.val : U → X) ⁻¹'
          {y | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hPair) y}⊆C := by
  dsimp only
  obtain ⟨Φ,a,b,hsrc,h0,ha,hb,hab,hOld,hBorn⟩ := shared_coordinates h x
  let S:=Finset.univ.biUnion a
  let J:=S.toList
  let U : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let B : List (Set U) := J.map fun j=>{p | flatCoord Φ j p.val=0}
  let c : Fin B.length → Fin J.length := Fin.cast (by simp [B])
  let G (i : Fin L.length) : Finset (Fin B.length) :=
    Finset.univ.filter (fun j=>J.get (c j)∈a i)
  let one : Fin J.length → Finset (Fin n) := fun i=>{J.get i}
  let A:=Fin.append one b
  have hbi (i : Fin E.length) : (b i).Nonempty ↔ x∈E.get i := by
    constructor
    · rintro ⟨k,hk⟩
      apply (hBorn i x (mem_flatDomain_self Φ)).mpr
      refine ⟨k,hk,?_⟩
      change (Φ.toFun (chartAt (ComplexModel n) x x)) k=0
      rw [h0]
      rfl
    · intro hi
      obtain ⟨k,hk,_hz⟩ := (hBorn i x (mem_flatDomain_self Φ)).mp hi
      exact ⟨k,hk⟩
  have hBcard (i : Fin E.length) : (b i).card≤1 := by
    by_cases hi : (b i).Nonempty
    · exact (born_singleton_in_shared_coordinates hE Φ h0 b hBorn i ((hbi i).mp hi)).le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hi]
      exact Nat.zero_le _
  have hAcard : ∀ i,(A i).card≤1 := Fin.addCases
    (fun i=>by simp [A,one]) (fun i=>by simpa only [A,Fin.append_right] using hBcard i)
  have hAinj : Set.InjOn A {i | (A i).Nonempty} := by
    apply injOn_append_nonempty one b
    · intro i _hi j _hj he
      exact (Finset.nodup_toList S).injective_get (Finset.singleton_injective he)
    · intro i hi j _hj he
      by_contra hij
      obtain ⟨k,hk⟩ := hi
      exact Finset.disjoint_left.mp (hb i j hij) hk (he ▸ hk)
    · intro i j
      apply Finset.disjoint_left.mpr
      intro k hk hkj
      have hkJ : k=J.get i := Finset.mem_singleton.mp hk
      have hkS : k∈S := hkJ.symm ▸ Finset.mem_toList.mp (List.get_mem J i)
      obtain ⟨l,_hl,hkl⟩ := Finset.mem_biUnion.mp hkS
      exact Finset.disjoint_left.mp (hab l j) hkl hkj
  let T0 : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let χ:=flatDomainDiffeomorph Φ hsrc
  let f : U → LiftedModel.{u} n := fun p=>(χ p).val
  have hModel:=isSNCDivisor_coordinateFamily.{u} A hAcard hAinj
  have hTarget := isSNCDivisor_map_preimage (pullsBackCoordinates_val (liftedOpens.{u} T0))
    continuous_subtype_val hModel
  have hFlat := isSNCDivisor_map_preimage (MarkedIdealTowerTransport.pullsBackCoordinates χ)
    χ.continuous hTarget
  have hFU : IsSNCDivisor n ((coordinateFamily.{u} A).map (f ⁻¹' ·)) := by
    rw [List.map_map] at hFlat
    exact hFlat
  have hSplit : coordinateFamily.{u} A=
      J.map (fun j=>coordinateMember.{u} {j})++List.ofFn (fun i=>coordinateMember.{u} (b i)) := by
    have he : (fun i=>coordinateMember.{u} (A i))=
        Fin.append (fun i=>coordinateMember.{u} (one i)) (fun i=>coordinateMember.{u} (b i)) :=
      funext (Fin.addCases (fun _=>by simp only [A,Fin.append_left])
        (fun _=>by simp only [A,Fin.append_right]))
    change List.ofFn (fun i=>coordinateMember.{u} (A i))=_
    rw [he,List.ofFn_fin_append]
    congr 1
    simpa only [List.ofFn_get] using List.ofFn_comp' J.get (fun j=>coordinateMember.{u} {j})
  have hOldModel : (J.map (fun j=>coordinateMember.{u} {j})).map (f ⁻¹' ·)=B := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j _hj
    ext p
    simp only [coordinateMember,Finset.singleton_nonempty,if_true,mem_ofPred_eq,
      BlowupSNCTransform.mem_coordSubspace_singleton]
    rfl
  have hListE : E.map ((Subtype.val : U → X) ⁻¹' ·)=
      List.ofFn (fun i : Fin E.length=>(Subtype.val : U → X) ⁻¹' E.get i) := by
    have he:=List.ofFn_comp' E.get ((Subtype.val : U → X) ⁻¹' ·)
    rw [List.ofFn_get] at he
    exact he.symm
  have hBornModel : (List.ofFn (fun i=>coordinateMember.{u} (b i))).map (f ⁻¹' ·)=
      E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    rw [hListE,List.map_ofFn]
    congr 1
    funext i
    ext p
    change f p∈coordinateMember.{u} (b i) ↔ p.val∈E.get i
    by_cases hi : (b i).Nonempty
    · obtain ⟨k,hk⟩ := Finset.card_eq_one.mp
        (born_singleton_in_shared_coordinates hE Φ h0 b hBorn i ((hbi i).mp hi))
      have he:=(hBorn i p.val p.property).symm
      rw [hk] at he ⊢
      simp only [coordinateMember,Finset.singleton_nonempty,if_true,mem_ofPred_eq,
        BlowupSNCTransform.mem_coordSubspace_singleton]
      change flatCoord Φ k p.val=0 ↔ p.val∈E.get i
      simpa only [Finset.mem_singleton,exists_eq_left] using he
    · have he:=(hBorn i p.val p.property).symm
      simpa only [coordinateMember,Finset.not_nonempty_iff_eq_empty.mp hi,
        Finset.not_nonempty_empty,if_false,mem_empty_iff_false,Finset.notMem_empty,false_and,exists_false] using he
  have hList : (coordinateFamily.{u} A).map (f ⁻¹' ·)=B++E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    rw [hSplit,List.map_append,hOldModel,hBornModel]
  have hget (j : Fin B.length) : B.get j={p : U | flatCoord Φ (J.get (c j)) p.val=0} := by
    simp only [B,List.get_eq_getElem,List.getElem_map]
    rfl
  have hG : ∀ i j,i≠j → Disjoint (G i) (G j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hk hkj
    exact Finset.disjoint_left.mp (ha i j hij) (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hkj).2
  have hMember (i : Fin L.length) : (Subtype.val : U → X) ⁻¹' L.get i=⋃ j∈G i,B.get j := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hki,hzero⟩ := (hOld i p.val p.property).mp hp
      have hkS : k∈S := Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hki⟩
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hkS)
      let jB : Fin B.length := ⟨j.val,by simpa only [B,List.length_map] using j.isLt⟩
      have hc : c jB=j := Fin.ext rfl
      have hg : jB∈G i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hc,hj];exact hki⟩
      apply mem_iUnion₂.mpr
      refine ⟨jB,hg,?_⟩
      rw [hget,hc,hj]
      exact hzero
    · intro hp
      obtain ⟨j,hj,hpB⟩ := mem_iUnion₂.mp hp
      have hja := (Finset.mem_filter.mp hj).2
      rw [hget] at hpB
      exact (hOld i p.val p.property).mpr ⟨J.get (c j),hja,hpB⟩
  have hReader:=old_union_reader Φ a hOld
  have hUnion : (Subtype.val : U → X) ⁻¹' (⋃ A∈L,A)=(⋃ A∈B,A) := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk,hzero⟩ := (hReader p.val p.property).mp hp
      exact mem_iUnion₂.mpr ⟨{p : U | flatCoord Φ k p.val=0},
        List.mem_map.mpr ⟨k,Finset.mem_toList.mpr hk,rfl⟩,hzero⟩
    · intro hp
      obtain ⟨C,hC,hpC⟩ := mem_iUnion₂.mp hp
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hC
      exact (hReader p.val p.property).mpr ⟨k,Finset.mem_toList.mp hk,hpC⟩
  refine ⟨U,B,G,mem_flatDomain_self Φ,hList ▸ hFU,hG,hMember,hUnion,?_⟩
  intro r hbound hx C hC p hp
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hC
  have hlevel := (highest_superlevel_flattening
    (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE))
    hbound hx Φ h0 S hReader).2
  exact ((hlevel p.val p.property).mp hp) k (Finset.mem_toList.mp hk)

/-- A genuine original highest bound specializes the SAME internally produced
labelled chart, retaining EVERY original position and entire born trace. -/
theorem exists_highest_labelled_joint_branch_chart {L E : List (Set X)}
    (h : IsNormalCrossingsBoundary (n:=n) (L++E)) (hE : IsSNCDivisor n E) {r : ℕ}
    (hbound : ∀ y : X,branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y≤r)
    {x : X} (hx : r≤branchMultiplicity
      (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) x) :
    ∃ (U : Opens X) (B : List (Set U)) (G : Fin L.length → Finset (Fin B.length)),
      x∈U ∧ IsSNCDivisor n (B++E.map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      (∀ i j,i≠j → Disjoint (G i) (G j)) ∧
      (∀ i,(Subtype.val : U → X) ⁻¹' L.get i=⋃ j∈G i,B.get j) ∧
      (Subtype.val : U → X) ⁻¹' (⋃ A∈L,A)=(⋃ A∈B,A) ∧
      ∀ C∈B,(Subtype.val : U → X) ⁻¹'
        {y | r≤branchMultiplicity
          (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_labelled h hE)) y}⊆C := by
  obtain ⟨U,B,G,hxU,hSNC,hG,hMember,hUnion,hHigh⟩ := exists_labelled_joint_branch_chart h hE x
  exact ⟨U,B,G,hxU,hSNC,hG,hMember,hUnion,hHigh r hbound hx⟩

end
end Hironaka.HironakaNormalCrossingsLabelledJointBranches
