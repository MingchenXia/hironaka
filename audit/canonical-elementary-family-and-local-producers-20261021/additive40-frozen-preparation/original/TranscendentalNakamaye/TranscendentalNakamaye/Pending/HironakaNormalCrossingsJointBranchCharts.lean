import TranscendentalNakamaye.Pending.HironakaBoundaryCoefficientStratumResolution

/-!
# Actual original joint old-NC branch and entire born-boundary charts

The whole finite coordinate array retains empty absent-born positions.
Shrinking avoids precisely those originally absent members; a genuine actual
flattening pullback constructs SNC of old branches PLUS the ENTIRE born list.
No joint local SNC certificate or global branch labelling is assumed.
Blueprint: `hironaka-normal-crossings-joint-branch-charts-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaNormalCrossingsJointBranchCharts
noncomputable section
open FirstPass FirstPass.BlowupSequences BlowupFlatCoordinates NormalCrossings
  NormalCrossingsInvariance BlowupTowers HironakaNormalCrossingsLocalBranches
  HironakaNormalCrossingsMultiplicityStrata HironakaNormalCrossingsBoundaryTransform
  HironakaNormalCrossingsHighestSubcentreAdmissibility
variable {n : ℕ}

/-- Empty original index positions represent EMPTY sets, not the whole model. -/
def coordinateMember (S : Finset (Fin n)) : Set (LiftedModel.{u} n) :=
  if S.Nonempty then {w | w.down∈coordSubspace S} else ∅

def coordinateFamily {m : ℕ} (A : Fin m→Finset (Fin n)) : List (Set (LiftedModel.{u} n)) :=
  List.ofFn fun i=>coordinateMember (A i)

private theorem mem_coordinateMember_iff (S : Finset (Fin n)) (w : LiftedModel.{u} n) :
    w∈coordinateMember S↔S.Nonempty∧w.down∈coordSubspace S := by
  classical
  by_cases h : S.Nonempty <;> simp [coordinateMember,h]

private def translateAt (w : ComplexModel n) : LocalHolomorphicEquivAt (n := n) w where
  source:=univ
  target:=univ
  isOpen_source:=isOpen_univ
  isOpen_target:=isOpen_univ
  center_mem_source:=mem_univ _
  toFun:=fun z=>z-w
  invFun:=fun z=>z+w
  toFun_holomorphic:=(differentiable_id.sub_const w).differentiableOn
  invFun_holomorphic:=(differentiable_id.add_const w).differentiableOn
  mapsTo_toFun:=fun _ _=>mem_univ _
  mapsTo_invFun:=fun _ _=>mem_univ _
  left_inv:=fun _ _=>sub_add_cancel _ _
  right_inv:=fun _ _=>add_sub_cancel_right _ _

/-- The whole genuine finite coordinate SNC family, including every empty slot. -/
theorem isSNCDivisor_coordinateFamily {m : ℕ} (A : Fin m→Finset (Fin n))
    (hcard : ∀ i,(A i).card≤1) (hinj : Set.InjOn A {i | (A i).Nonempty}) :
    IsSNCDivisor n (coordinateFamily.{u} A) := by
  classical
  let E := coordinateFamily.{u} A
  let c : Fin E.length→Fin m := Fin.cast (by simp [E,coordinateFamily])
  have hget (i : Fin E.length) : E.get i=coordinateMember (A (c i)) := by
    exact List.get_ofFn (fun i : Fin m=>coordinateMember.{u} (A i)) i
  refine ⟨?_,fun w=>?_⟩
  · intro H hH
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hH
    by_cases hi : (A i).Nonempty
    · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp ((hcard i).antisymm (Finset.card_pos.mpr hi))
      rw [coordinateMember,if_pos hi,hj]
      simp only [BlowupSNCTransform.mem_coordSubspace_singleton]
      exact isClosed_eq ((EuclideanSpace.proj j : ComplexModel n→L[ℂ] ℂ).continuous.comp continuous_uliftDown) continuous_const
    · simp [coordinateMember,hi]
  · have hw (i : Fin E.length) (hi : w∈E.get i) :
        (A (c i)).Nonempty∧w.down∈coordSubspace (A (c i)) :=
      (mem_coordinateMember_iff _ w).mp ((hget i) ▸ hi)
    refine ⟨fun i=>A (c i),⟨translateAt w.down,?_,?_,?_⟩,?_,?_⟩
    · intro z _
      change z∈(chartAt (ComplexModel n) w).target
      exact mem_univ _
    · exact sub_self _
    · intro i hi y _hy _hyΦ
      change y∈E.get i↔(y.down-w.down)∈coordSubspace (A (c i))
      rw [hget,mem_coordinateMember_iff]
      simp only [(hw i hi).1,true_and]
      change (∀ j∈A (c i),y.down j=0)↔∀ j∈A (c i),(y.down-w.down) j=0
      constructor
      · intro hy j hj
        change y.down j-w.down j=0
        rw [hy j hj,(hw i hi).2 j hj,sub_zero]
      · intro hy j hj
        have hh := hy j hj
        change y.down j-w.down j=0 at hh
        rwa [(hw i hi).2 j hj,sub_zero] at hh
    · intro i hi
      exact (hcard (c i)).antisymm (Finset.card_pos.mpr (hw i hi).1)
    · intro i hi j hj hij
      exact Fin.cast_injective _ (hinj (hw i hi).1 (hw j hj).1 hij)

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


variable {X : CMfd.{u} n}

/-- SAME original joint coordinates internally construct a WHOLE old-branch
+ENTIRE born-boundary SNC chart, with every original index retained. -/
theorem exists_highest_joint_branch_chart {H : Set X} {E : List (Set X)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r)
    {x : X} (hx : r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x) :
    ∃ (U : Opens X) (B : List (Set U)),x∈U ∧
      IsSNCDivisor n (B ++ E.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
      (Subtype.val : U→X) ⁻¹' H=(⋃ C∈B,C) ∧
      ∀ C∈B,(Subtype.val : U→X) ⁻¹'
        {y | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) y}⊆C := by
  classical
  obtain ⟨Φ,S,D,hsrc,h0,hflat,hD,hinj,hE⟩ := h.2.2 x
  obtain ⟨_hcard,hlevel⟩ := highest_superlevel_flattening
    (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound hx Φ h0 S hflat
  let W : Set X := ⋂ i : Fin E.length,if x∈E.get i then univ else (E.get i)ᶜ
  have hW : IsOpen W := isOpen_iInter_of_finite fun i=>by
    by_cases hi : x∈E.get i
    · rw [if_pos hi];exact isOpen_univ
    · rw [if_neg hi];exact (h.2.1 _ (List.get_mem E i)).isOpen_compl
  have hxW : x∈W := mem_iInter.mpr fun i=>by
    by_cases hi : x∈E.get i
    · rw [if_pos hi];exact mem_univ _
    · rw [if_neg hi];exact hi
  let U : Opens X := ⟨flatDomain Φ∩W,(isOpen_flatDomain Φ).inter hW⟩
  let J := S.toList
  let B : List (Set U) := J.map fun j=>{p | flatCoord Φ j p.1=0}
  let a : Fin J.length→Finset (Fin n) := fun i=>{J.get i}
  let b : Fin E.length→Finset (Fin n) := fun i=>if x∈E.get i then D i else ∅
  let A := Fin.append a b
  have haMem (i : Fin J.length) : J.get i∈S := Finset.mem_toList.mp (List.get_mem J i)
  have hb (i : Fin E.length) : (b i).Nonempty↔x∈E.get i := by
    change (if x∈E.get i then D i else ∅).Nonempty↔x∈E.get i
    by_cases hi : x∈E.get i
    · rw [if_pos hi]
      exact iff_of_true (Finset.card_pos.mp (by rw [(hD i hi).1];omega)) hi
    · rw [if_neg hi]
      exact iff_of_false Finset.not_nonempty_empty hi
  have hAcard : ∀ i,(A i).card≤1 := Fin.addCases
    (fun i=>by simp [A,a]) (fun i=>by
      dsimp only [A]
      rw [Fin.append_right]
      dsimp only [b]
      by_cases hi : x∈E.get i
      · rw [if_pos hi,(hD i hi).1]
      · rw [if_neg hi]
        exact Nat.zero_le _)
  have hAinj : Set.InjOn A {i | (A i).Nonempty} := by
    apply injOn_append_nonempty a b
    · intro i _hi j _hj heq
      exact (Finset.nodup_toList S).injective_get (Finset.singleton_injective heq)
    · intro i hi j hj heq
      have hxi := (hb i).mp hi
      have hxj := (hb j).mp hj
      apply hinj hxi hxj
      simpa only [b,if_pos hxi,if_pos hxj] using heq
    · intro i j
      by_cases hj : x∈E.get j
      · apply Finset.disjoint_left.mpr
        intro v hv hvb
        have heq : v=J.get i := Finset.mem_singleton.mp hv
        have hvS : v∈S := heq.symm ▸ haMem i
        exact Finset.disjoint_left.mp (hD j hj).2 hvS (by simpa only [b,if_pos hj] using hvb)
      · dsimp only [b]
        rw [if_neg hj]
        simp
  let D0 : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let T0 : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let χ := flatDomainDiffeomorph Φ hsrc
  let inc : U→D0 := fun p=>⟨p.1,p.2.1⟩
  have hinc : HironakaBaseChange.IsOpenHoloEmbedding n inc :=
    (HironakaBaseChange.isOpenHoloEmbedding_val U).codRestrict D0 (fun p=>p.2.1)
  let f : U→LiftedModel.{u} n := fun p=>(χ (inc p)).val
  have hModel : IsSNCDivisor n (coordinateFamily.{u} A) := isSNCDivisor_coordinateFamily A hAcard hAinj
  have hTarget : IsSNCDivisor n ((coordinateFamily.{u} A).map
      ((Subtype.val : LiftedOpen.{u} T0→LiftedModel.{u} n) ⁻¹' ·)) :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (liftedOpens.{u} T0)) continuous_subtype_val hModel
  have hFlat := isSNCDivisor_map_preimage (MarkedIdealTowerTransport.pullsBackCoordinates χ)
    χ.contMDiff.continuous hTarget
  have hFU : IsSNCDivisor n ((coordinateFamily.{u} A).map (f ⁻¹' ·)) := by
    have hh := hinc.isSNCDivisor_map_preimage hFlat
    have hMap : (((coordinateFamily.{u} A).map
        ((Subtype.val : LiftedOpen.{u} T0→LiftedModel.{u} n) ⁻¹' ·)).map (χ ⁻¹' ·)).map (inc ⁻¹' ·)=
        (coordinateFamily.{u} A).map (f ⁻¹' ·) := by
      rw [List.map_map,List.map_map]
      apply List.map_congr_left
      intro C _hC
      ext p
      rfl
    exact hMap ▸ hh
  have hSplit : coordinateFamily.{u} A=
      J.map (fun j=>coordinateMember.{u} {j}) ++ List.ofFn (fun i=>coordinateMember.{u} (b i)) := by
    have heq : (fun i=>coordinateMember.{u} (A i))=
        Fin.append (fun i=>coordinateMember.{u} (a i)) (fun i=>coordinateMember.{u} (b i)) :=
      funext (Fin.addCases (fun _=>by simp only [A,Fin.append_left])
        (fun _=>by simp only [A,Fin.append_right]))
    change List.ofFn (fun i=>coordinateMember.{u} (A i))=_
    rw [heq,List.ofFn_fin_append]
    congr 1
    simpa only [List.ofFn_get] using List.ofFn_comp' J.get (fun j=>coordinateMember.{u} {j})
  have hOld : (J.map (fun j=>coordinateMember.{u} {j})).map (f ⁻¹' ·)=B := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j _hj
    ext p
    change f p∈coordinateMember.{u} {j}↔flatCoord Φ j p.1=0
    rw [mem_coordinateMember_iff]
    simp only [Finset.singleton_nonempty,true_and,BlowupSNCTransform.mem_coordSubspace_singleton]
    rfl
  have hListE : E.map ((Subtype.val : U→X) ⁻¹' ·)=
      List.ofFn (fun i : Fin E.length=>(Subtype.val : U→X) ⁻¹' E.get i) := by
    have hh := List.ofFn_comp' E.get ((Subtype.val : U→X) ⁻¹' ·)
    rw [List.ofFn_get] at hh
    exact hh.symm
  have hBorn : (List.ofFn (fun i=>coordinateMember.{u} (b i))).map (f ⁻¹' ·)=
      E.map ((Subtype.val : U→X) ⁻¹' ·) := by
    rw [hListE,List.map_ofFn]
    congr 1
    funext i
    ext p
    change f p∈coordinateMember.{u} (b i)↔p.1∈E.get i
    rw [mem_coordinateMember_iff]
    by_cases hi : x∈E.get i
    · dsimp only [b]
      rw [if_pos hi]
      have hDi : (D i).Nonempty := Finset.card_pos.mp (by rw [(hD i hi).1];omega)
      simp only [hDi,true_and]
      exact (hE i hi p.1 p.2.1).symm
    · dsimp only [b]
      rw [if_neg hi]
      simp only [Finset.not_nonempty_empty,false_and,false_iff]
      have hp := mem_iInter.mp p.2.2 i
      change p.1∈(if x∈E.get i then (univ : Set X) else (E.get i)ᶜ) at hp
      rw [if_neg hi] at hp
      exact hp
  have hList : (coordinateFamily.{u} A).map (f ⁻¹' ·)=B ++ E.map ((Subtype.val : U→X) ⁻¹' ·) := by
    rw [hSplit,List.map_append,hOld,hBorn]
  refine ⟨U,B,⟨mem_flatDomain_self Φ,hxW⟩,hList ▸ hFU,?_,?_⟩
  · ext p
    change p.1∈H↔p∈⋃ C∈B,C
    rw [hflat p.1 p.2.1]
    constructor
    · rintro ⟨j,hj,hzero⟩
      exact mem_iUnion₂.mpr ⟨{p : U | flatCoord Φ j p.1=0},
        List.mem_map.mpr ⟨j,Finset.mem_toList.mpr hj,rfl⟩,hzero⟩
    · intro hp
      obtain ⟨C,hC,hpC⟩ := mem_iUnion₂.mp hp
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hC
      exact ⟨j,Finset.mem_toList.mp hj,hpC⟩
  · intro C hC p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hC
    exact ((hlevel p.1 p.2.1).mp hp) j (Finset.mem_toList.mp hj)


end
end TranscendentalNakamaye.Pending.HironakaNormalCrossingsJointBranchCharts
