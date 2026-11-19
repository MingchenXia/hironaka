import Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
import Hironaka.Analytic.Unibranch.ComplexSpaceAnalyticSubsets
import Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
import Hironaka.Analytic.ConstantRankImage

/-! # Hironaka's selected higher-stratum set -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SourceCSet

open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus

noncomputable section

/-- An analytic subset meets `T` in a relatively open subset. -/
def IsRelOpen {α : Type*} [TopologicalSpace α] (A T : Set α) : Prop :=
  ∃ U : Set α, IsOpen U ∧ A ∩ T = A ∩ U

/-- The actual maximal irreducible analytic components of a relative stratum. -/
def IsStratumComponent {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B : Set X.obj.left) (j : ℕ) (C : Set X.obj.left) : Prop :=
  X.IsIrreducibleAnalyticSubset C ∧ C ⊆ strata f B j ∧
    ∀ D : Set X.obj.left, X.IsIrreducibleAnalyticSubset D →
      C ⊆ D → D ⊆ strata f B j → D = C

/-- The indexed actual higher components meeting a tracked set off the next
  stratum (the set called `A_i` in Hironaka 4.5.1). -/
def selectedHigherComponents {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B : Set X.obj.left) {q : ℕ} (Z : Fin q → Set X.obj.left) (i : ℕ) :
    Set (ℕ × Set X.obj.left) :=
  {jC | i < jC.1 ∧ IsStratumComponent f B jC.1 jC.2 ∧
    ∃ p, ((jC.2 \ strata f B (jC.1 + 1)) ∩ Z p).Nonempty}

/-- Hironaka's actual bad component set Δ. -/
def badComponents {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B : Set X.obj.left) {q : ℕ} (Z : Fin q → Set X.obj.left) :
    Set (ℕ × Set X.obj.left) :=
  {jC | 1 ≤ jC.1 ∧ IsStratumComponent f B jC.1 jC.2 ∧
    (∃ p, ((jC.2 \ strata f B (jC.1 + 1)) ∩ Z p).Nonempty) ∧
    ∃ p, ¬ IsRelOpen jC.2 (Z p)}

/-- The union of the actual selected higher components, Hironaka's `C_i`. -/
def Cset {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (B : Set X.obj.left) {q : ℕ} (Z : Fin q → Set X.obj.left) (i : ℕ) : Set X.obj.left :=
  ⋃ jC ∈ selectedHigherComponents f B Z i, jC.2

/-- A union of two native analytic subsets is analytic. -/
theorem analytic_union {X : SourceReducedComplexSpace} {A B : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) : X.IsAnalyticSubset (A ∪ B) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e,LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val '' (e.toPoint ⁻¹' A)) ∪ (Subtype.val '' (e.toPoint ⁻¹' B)),
    Hironaka.ConstantRankImage.IsComplexAnalyticSubset.union
      (analytic_image_trace hA e) (analytic_image_trace hB e), ?_⟩
  rw [Set.preimage_union, Set.preimage_union,
    Set.preimage_image_eq _ Subtype.val_injective,
    Set.preimage_image_eq _ Subtype.val_injective]

/-- Any finite union of native analytic subsets is analytic. -/
theorem analytic_finite_biUnion {X : SourceReducedComplexSpace} {ι : Type*}
    (S : Set ι) (hS : S.Finite) (A : ι → Set X.obj.left)
    (hA : ∀ i ∈ S, X.IsAnalyticSubset (A i)) : X.IsAnalyticSubset (⋃ i ∈ S, A i) := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => simpa using (isAnalyticSubset_empty (X := X))
  | @insert a S ha hS ih =>
    have haA : X.IsAnalyticSubset (A a) := hA a (Set.mem_insert a S)
    have hSA : ∀ i ∈ S, X.IsAnalyticSubset (A i) := fun i hi => hA i (Set.mem_insert_of_mem a hi)
    simpa only [Set.biUnion_insert] using analytic_union haA (ih hSA)

/-- A relatively open trace on a closed set has closed complement in that set. -/
private theorem closed_diff_of_relOpen {α : Type*} [TopologicalSpace α]
    {A T : Set α} (hA : IsClosed A) (h : IsRelOpen A T) : IsClosed (A \ T) := by
  obtain ⟨U,hU,hEq⟩ := h
  have heq : A \ T = A ∩ Uᶜ := by
    ext x
    have hx := Set.ext_iff.mp hEq x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff] at hx ⊢
    tauto
  rw [heq]
  exact hA.inter hU.isClosed_compl

/-- Hironaka 4.5.1(1), using the actual component predicates. Finiteness of
  the selected components is explicit until the native component theorem and
  Frisch filtration are available. -/
theorem Cset_closed_relOpen_and_nonflat {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (B : Set X.obj.left) {q : ℕ} (Z : Fin q → Set X.obj.left) (i : ℕ)
    (hfinite : (selectedHigherComponents f B Z i).Finite)
    (hmax : ∀ jC ∈ badComponents f B Z, jC.1 ≤ i) :
    X.IsAnalyticSubset (Cset f B Z i) ∧ IsClosed (Cset f B Z i) ∧
      (∀ p, IsRelOpen (Cset f B Z i) (Z p)) ∧ Cset f B Z i ⊆ nonflatImage f := by
  have hclosed : ∀ jC ∈ selectedHigherComponents f B Z i, IsClosed jC.2 := by
    intro jC hjC
    exact hjC.2.1.1.1.isClosed
  have hrel : ∀ jC ∈ selectedHigherComponents f B Z i, ∀ p, IsRelOpen jC.2 (Z p) := by
    intro jC hjC p
    by_contra hn
    have hjpos : 1 ≤ jC.1 := Nat.succ_le_iff.mpr (lt_of_le_of_lt (Nat.zero_le i) hjC.1)
    have hbad : jC ∈ badComponents f B Z := ⟨hjpos, hjC.2.1, hjC.2.2, p, hn⟩
    exact (not_lt_of_ge (hmax jC hbad)) hjC.1
  have hCi : IsClosed (Cset f B Z i) := hfinite.isClosed_biUnion hclosed
  have hCia : X.IsAnalyticSubset (Cset f B Z i) :=
    analytic_finite_biUnion _ hfinite Prod.snd (fun jC hjC => hjC.2.1.1.1)
  refine ⟨hCia, hCi, ?_, ?_⟩
  · intro p
    have hdiff : Cset f B Z i \ Z p =
        ⋃ jC ∈ selectedHigherComponents f B Z i, (jC.2 \ Z p) := by
      ext x
      simp only [Cset, Set.mem_sdiff, Set.mem_iUnion]
      constructor
      · rintro ⟨⟨jC,hjC,hx⟩,hZ⟩
        exact ⟨jC,hjC,hx,hZ⟩
      · rintro ⟨jC,hjC,hx,hZ⟩
        exact ⟨⟨jC,hjC,hx⟩,hZ⟩
    have hdclosed : IsClosed (Cset f B Z i \ Z p) := by
      rw [hdiff]
      exact hfinite.isClosed_biUnion (fun jC hjC => closed_diff_of_relOpen (hclosed jC hjC) (hrel jC hjC p))
    refine ⟨(Cset f B Z i \ Z p)ᶜ, hdclosed.isOpen_compl, ?_⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  · intro x hx
    simp only [Cset, Set.mem_iUnion] at hx
    obtain ⟨jC,hjC,hxC⟩ := hx
    have hjpos : 0 < jC.1 := lt_of_le_of_lt (Nat.zero_le i) hjC.1
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
    have hmem := hjC.2.1.2.1 hxC
    rw [hk] at hmem
    exact strata_succ_subset_nonflatImage f B k hmem

end
end Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
