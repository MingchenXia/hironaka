import Hironaka.Resolution.HironakaG8StageRankCoherence

/-! Predecessor counts at points of projected event footprints. -/
set_option autoImplicit false
open Set

namespace Hironaka.HironakaG8PointCountRank

open HironakaG8StageRankCoherence

def pointPredecessors {X I : Type*} (F : I → Set X) (R : I → I → Prop)
    (x : X) (b : I) : Set I := {a | x ∈ F a ∧ R a b}

noncomputable def pointCount {X I : Type*} (F : I → Set X) (R : I → I → Prop)
    (x : X) (b : I) : ℕ := (pointPredecessors F R x b).ncard

theorem pointCount_strict {X I : Type*} (F : I → Set X) (R : I → I → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hIrrefl : ∀ a, ¬ R a a) (hFin : ∀ x, {a | x ∈ F a}.Finite)
    {x : X} {a b : I} (hR : R a b) (hx : x ∈ F a) :
    pointCount F R x a < pointCount F R x b := by
  apply Set.ncard_lt_ncard
  · refine ⟨fun z hz => ⟨hz.1,hTrans hz.2 hR⟩,?_⟩
    intro hBack
    exact hIrrefl a (hBack ⟨hx,hR⟩).2
  · exact (hFin x).subset (fun _ h => h.1)

theorem exists_rank_of_overlap_maxima {X I : Type*}
    (F : I → Set X) (R : I → I → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hIrrefl : ∀ a, ¬ R a a) (hFin : ∀ x, {a | x ∈ F a}.Finite)
    (hMax : ∀ a, ∃ x ∈ F a, ∀ y ∈ F a, pointCount F R y a ≤ pointCount F R x a)
    (hOverlap : ∀ {a b}, R a b → (F a ∩ F b).Nonempty →
      ∃ x ∈ F a ∩ F b, ∀ y ∈ F a, pointCount F R y a ≤ pointCount F R x a) :
    ∃ rank : I → ℕ, ∀ {a b}, R a b → (F a ∩ F b).Nonempty → rank a < rank b := by
  classical
  choose pt hPt hUpper using hMax
  refine ⟨fun a => pointCount F R (pt a) a,?_⟩
  intro a b hab hMeet
  obtain ⟨x,hxa,hAt⟩ := hOverlap hab hMeet
  exact (hAt _ (hPt a)).trans_lt
    ((pointCount_strict F R hTrans hIrrefl hFin hab hxa.1).trans_le
      (hUpper b x hxa.2))

theorem exists_rank_of_point_count_constancy {X I : Type*}
    (F : I → Set X) (R : I → I → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hIrrefl : ∀ a, ¬ R a a) (hFin : ∀ x, {a | x ∈ F a}.Finite)
    (hNonempty : ∀ a, (F a).Nonempty)
    (hConstant : ∀ a x y, x ∈ F a → y ∈ F a →
      pointCount F R x a = pointCount F R y a) :
    ∃ rank : I → ℕ, ∀ {a b}, R a b → (F a ∩ F b).Nonempty → rank a < rank b := by
  apply exists_rank_of_overlap_maxima F R hTrans hIrrefl hFin
  · intro a
    obtain ⟨x,hx⟩ := hNonempty a
    exact ⟨x,hx,fun y hy => (hConstant a y x hy hx).le⟩
  · intro a b _ hMeet
    obtain ⟨x,hxa,hxb⟩ := hMeet
    exact ⟨x,⟨hxa,hxb⟩,fun y hy => (hConstant a y x hy hxa).le⟩

theorem local_path_length_le_count {X I : Type*}
    (F : I → Set X) (R : I → I → Prop)
    (hTrans : ∀ {a b c}, R a b → R b c → R a c)
    (hIrrefl : ∀ a, ¬ R a a) (hFin : ∀ x, {a | x ∈ F a}.Finite)
    (x : X) {b : I} {l : ℕ}
    (hPath : DependencyPath (fun a b => R a b ∧ x ∈ F a ∧ x ∈ F b) l b) :
    l ≤ pointCount F R x b := by
  induction hPath with
  | nil => exact Nat.zero_le _
  | step h _ ih =>
    exact Nat.succ_le_of_lt (ih.trans_lt
      (pointCount_strict F R hTrans hIrrefl hFin h.1 h.2.1))

theorem pointCount_orderIso {X Y I J : Type*} [Preorder I] [Preorder J]
    (F : I → Set X) (G : J → Set Y) (e : I ≃o J) (x : X) (y : Y)
    (hMem : ∀ a, x ∈ F a ↔ y ∈ G (e a)) (b : I) :
    pointCount F (· < ·) x b = pointCount G (· < ·) y (e b) := by
  apply Set.ncard_congr (fun a _ => e a)
  · intro a ha
    exact ⟨(hMem a).mp ha.1,e.strictMono ha.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro a ha
    refine ⟨e.symm a,⟨?_,?_⟩,e.apply_symm_apply a⟩
    · exact (hMem _).mpr (by simpa only [e.apply_symm_apply] using ha.1)
    · exact e.lt_iff_lt.mp (by simpa only [e.apply_symm_apply] using ha.2)

end Hironaka.HironakaG8PointCountRank
