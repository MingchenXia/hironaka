import Hironaka.Resolution.HironakaG3SNCListPermutation
import Hironaka.Resolution.HironakaG8MemberCutStable
import Hironaka.Resolution.HironakaG8ClassStepPerm
import Hironaka.Resolution.HironakaActualBoundarySlotReindex
import Hironaka.Invariant.InvDomainMemberRestriction
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8MemberIndexedLocal
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  HomogenizedIdealAlong CoefficientIdealRestriction HironakaG8LocalHistory HironakaG8ClassStepPerm HironakaG8MemberCutStable
  HironakaActualBoundarySlotReindex InvDomainMemberRestriction NormalCrossings

private theorem partition_perm {α : Type*} (p : α → Bool) (l : List α) :
    ((l.filter p) ++ (l.filter fun a => !p a)).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : p a with
    | false =>
      simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, Bool.not_false] 
      exact List.perm_middle.trans (ih.cons a)
    | true =>
      simp only [List.filter_cons, h, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      exact ih.cons a

private theorem snc_map_perm_finRange {n : ℕ} {X : CMfd.{u} n} (E : List (Set X))
    (L : List (Fin E.length)) (hL : L.Perm (List.finRange E.length)) (hE : IsSNCDivisor n E) :
    IsSNCDivisor n (L.map E.get) :=
  HironakaG3SNCListPermutation.snc_map_perm_finRange E L hL hE

theorem memberLocal_of_indexed {κ : Kinds} (hexc : κ.exc = false)
    {n : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hN : A.N = B.N) (hL : LocEquiv κ A B) (I : Finset (Fin A.E.length)) :
    LocEquiv κ (memberRestrict A I)
      { withN (coeffMarkedAlong B) (memberRestrict A I).N with E := (memberRestrict A I).E } := by
  let p : Fin A.E.length → Bool := fun i => decide (i ∈ I)
  let L₁ := (List.finRange A.E.length).filter p
  let L₂ := (List.finRange A.E.length).filter (fun i => !p i)
  let F := L₁.map A.E.get
  let G := L₂.map A.E.get
  let L := F ++ G
  have hpermI : (L₁ ++ L₂).Perm (List.finRange A.E.length) := partition_perm p _
  have hperm : L.Perm A.E := by
    have h := hpermI.map A.E.get
    simpa [L,F,G,List.map_append, List.map_get_finRange] using h
  let A' : MarkedIdeal n X := { A with E := L }
  let B' : MarkedIdeal n X := { B with E := L }
  have hLA : LocEquiv κ A' B' := locEquiv_perm hexc hL hperm
  have hSNC : IsSNCDivisor n L := by
    simpa [L,F,G,List.map_append] using snc_map_perm_finRange A.E (L₁ ++ L₂) hpermI hA.isSNCDivisor
  have hsub : ∀ H ∈ L, H ∈ A.E := fun _ hH => hperm.subset hH
  have hsubB : ∀ H ∈ L, H ∈ B.E := fun H hH => hL.E_eq ▸ hsub H hH
  have hA' : A'.IsWellFormed := ⟨hA.isClosedSubmanifold_N,hA.isCoherent,hSNC,
    NormalCrossingsComparison.isTransverse_of_forall_mem hA.isTransverse hsub⟩
  have hB' : B'.IsWellFormed := ⟨hB.isClosedSubmanifold_N,hB.isCoherent,hSNC,
    NormalCrossingsComparison.isTransverse_of_forall_mem hB.isTransverse hsubB⟩
  let S := (memberRestrict A I).N
  have hS : IsClosedSubmanifold n S := (isWellFormed_memberRestrict hn hA I).isClosedSubmanifold_N
  have hSA : S ⊆ A'.N := by intro x hx; exact hx.1
  have hSB : S ⊆ B'.N := by intro x hx; rw [← hN]; exact hx.1
  have hFS : ∀ H ∈ F, S ⊆ H ∨ H = ∅ := by
    intro H hH
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiI : i ∈ I := by simpa [L₁,p] using (List.mem_filter.mp hi).2
    exact Or.inl (fun x hx => hx.2 i hiI)
  have hEq := memberLocal_of_split hexc hA' hB' hdA hdB hLA (F := F) (G := G) rfl hS hSA hSB hFS
  simpa [A', B', S, G, L₂, p, memberRestrict, withN, coeffMarkedAlong,
    HomogenizedIdealAlong.derivMarkedAlong, CoefficientIdeal.msum] using hEq

theorem memberLocal_of_matching_indexed {κ : Kinds} (hexc : κ.exc = false)
    {n : ℕ} (hn : 0 < n) {X : CMfd.{u} n} {A B : MarkedIdeal n X}
    (hA : A.IsWellFormed) (hB : B.IsWellFormed) (hdA : 1 ≤ A.d) (hdB : 1 ≤ B.d)
    (hN : A.N = B.N) (hL : LocEquiv κ A B)
    (I : Finset (Fin A.E.length)) (J : Finset (Fin B.E.length))
    (hSN : (memberRestrict A I).N = (memberRestrict B J).N)
    (hSE : (memberRestrict A I).E = (memberRestrict B J).E) :
    LocEquiv κ (memberRestrict A I) (memberRestrict B J) := by
  have hR : memberRestrict B J =
      { withN (coeffMarkedAlong B) (memberRestrict A I).N with E := (memberRestrict A I).E } := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · exact hSN.symm
    · exact hSE.symm
    · rfl
    · rfl
  rw [hR]
  exact memberLocal_of_indexed hexc hn hA hB hdA hdB hN hL I

end
end Hironaka.HironakaG8MemberIndexedLocal
