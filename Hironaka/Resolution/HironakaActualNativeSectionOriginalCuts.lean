import Hironaka.Resolution.HironakaActualNativeSectionFiniteHistory
import Hironaka.Blowup.BlowupTowerSplit

/-! Actual literal head/tail cuts of geometry-only native histories.
The midpoint is the SAME induced native manifold; no initial record is
replaced and the tail starts with the entire original current boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeSectionOriginalCuts
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  SubmanifoldChartedSpace NormalCrossings BlowupTowerSplit
  HironakaActualNativeSectionFiniteHistory
variable {n k : ℕ}

private theorem boundary_head_tail {X Y : CMfd.{0} n}
    (E : List (Set X)) (T : BlowupTower X Y) (j : ℕ) :
    boundary (boundary E (head T j)) (tail T j)=boundary E T := by
  let M : MarkedIdeal n X:=⟨univ,E,IdealWeightPowers.unitIdeal n X,1⟩
  have he:=MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
    (𝔪:=geoTransformAlong M (head T j))
    (𝔫:=⟨univ,boundary E (head T j),IdealWeightPowers.unitIdeal n _,1⟩)
    rfl (tail T j)
  change (geoTransformAlong (geoTransformAlong M (head T j)) (tail T j)).E=
    boundary (boundary E (head T j)) (tail T j) at he
  rw [←he,←geoTransformAlong_head_tail M T j]
  rfl

def recastTarget {X Y Y' : CMfd.{0} k} (e : Y=Y') (Q : BlowupTower X Y) : BlowupTower X Y':=e ▸ Q
def recastSource {X X' Y : CMfd.{0} k} (e : X=X') (Q : BlowupTower X Y) : BlowupTower X' Y:=e ▸ Q

private theorem recastSource_step {X X' Y Z : CMfd.{0} k} (e : X=X')
    (Q : BlowupTower X Y) (D : Set Y) (π : Z→Y) (hπ : IsBlowupAlong k D π) :
    recastSource e (.step Q D π hπ)=.step (recastSource e Q) D π hπ := by
  cases e
  rfl

variable {X : CMfd.{0} n} {hk : k≤n} {W : Set X} {hWc : IsClosed W}
  {hW : ∀x∈W,RegularAtDim (n:=n) W x k} {E : List (Set X)}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀y∈V,RegularAtDim (n:=n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

theorem Lift.original_head_tails (h : Lift hk W hWc hW E T V hVc hV Q) (j : ℕ) :
    ∃(P : Set (split T j).1)(hPc : IsClosed P)
      (hP : ∀x∈P,RegularAtDim (n:=n) P x k)
      (e : (split Q j).1=nativeManifold hk P hP),
      Lift hk W hWc hW E (head T j) P hPc hP (recastTarget e (head Q j)) ∧
      Lift hk P hPc hP (boundary E (head T j)) (tail T j) V hVc hV
        (recastSource e (tail Q j)) := by
  induction h generalizing j with
  | refl =>
    cases j with
    | zero => exact ⟨W,hWc,hW,rfl,Lift.refl,Lift.refl⟩
    | succ j => exact ⟨W,hWc,hW,rfl,Lift.refl,Lift.refl⟩
  | @step Y Z T V hVc hV Q h D hD hint π hπ hNC ih =>
    cases j with
    | zero => exact ⟨_,_,_,rfl,Lift.step h D hD hint π hπ hNC,Lift.refl⟩
    | succ j =>
      obtain ⟨P,hPc,hP,e,hHead,hTail⟩:=ih j
      refine ⟨P,hPc,hP,e,hHead,?_⟩
      change Lift hk P hPc hP (boundary E (head T j))
        (.step (tail T j) ((Subtype.val : V→Y) '' D) π hπ) _ _ _
        (recastSource e (.step (tail Q j) D (nativeProjection hk hVc hV D π hπ)
          (nativeProjection_genuine hk hVc hV D hD hint π hπ)))
      rw [recastSource_step]
      apply Lift.step hTail D hD hint π hπ
      rwa [boundary_head_tail E T j]

end
end Hironaka.HironakaActualNativeSectionOriginalCuts
