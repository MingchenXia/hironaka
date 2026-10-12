/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionDivisorExponents
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Complete original monomial ordering under arbitrary dimensional submersions

Actual submersion coordinates internally produce the dimension inequality.
Actual SNC coordinates internally bound the original member sets. The
unchanged dimension-dependent keys then preserve and reflect whole gamma
ordering and equality, including bottom values. Actual surjectivity gives
the literal original marked maximum-locus preimage dictionary. No caller
order, cardinality, value or maximum certificate occurs. Higher invariants,
canonical blowup base change and complete G2 remain OPEN.
Blueprint: `hironaka-smooth-submersion-monomial-ordering-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothSubmersionMonomialOrdering
open Hironaka.HolomorphicIdealSheaves
open MonomialInvariant MonomialCase NormalCrossings MarkedIdeals GermIdealOrder
open HironakaSmoothSubmersionOrder HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionDivisorExponents
noncomputable section

variable {n m : ℕ} {X Y : Type*} [TopologicalSpace X]
 [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
 [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

omit [IsComplexManifold n X] [IsComplexManifold m Y] in
/-- The real submersion coordinates internally give the true ambient dimension inequality. -/
theorem dimension_le_of_submersionAt {f : Y → X} {y : Y}
 (hf : Manifold.IsSubmersionAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f y) : n ≤ m := by
 let D : ComplexModel m →ₗ[ℂ] ComplexModel n :=
   (LinearMap.fst ℂ (ComplexModel n) _).comp hf.equiv.toLinearEquiv.toLinearMap
 have hD : Function.Surjective D := by
   intro v
   refine ⟨hf.equiv.symm (v,0), ?_⟩
   change (hf.equiv (hf.equiv.symm (v,0))).1 = v
   rw [hf.equiv.apply_symm_apply]
 simpa only [ComplexModel, finrank_euclideanSpace_fin] using
   LinearMap.finrank_le_finrank_of_surjective hD

/-- All actual key comparisons are reflected, including different whole exponent functions. -/
theorem key_lt_key_dimension_iff (n m : ℕ) (hnm : n ≤ m)
 (a b : ℕ → ℕ) (K L : Finset ℕ) (hK : K.card ≤ n) (hL : L.card ≤ n) :
 key n a K < key n b L ↔ key m a K < key m b L := by
 rw [key_lt_key_iff,key_lt_key_iff]
 have hlt : n-K.card < n-L.card ↔ m-K.card < m-L.card := by omega
 have heq : n-K.card = n-L.card ↔ m-K.card = m-L.card := by omega
 rw [hlt,heq]

/-- The whole weak key ordering is reflected by the same actual dimension change. -/
theorem key_le_key_dimension_iff (n m : ℕ) (hnm : n ≤ m)
 (a b : ℕ → ℕ) (K L : Finset ℕ) (hK : K.card ≤ n) (hL : L.card ≤ n) :
 key n a K ≤ key n b L ↔ key m a K ≤ key m b L := by
 simpa only [not_lt] using
   not_congr (key_lt_key_dimension_iff n m hnm b a L K hL hK)

/-- One internally produced actual feasible subset is the original top in both dimensions. -/
theorem exists_common_top_dimensions (n m : ℕ) (hnm : n ≤ m)
 (S : Finset ℕ) (a : ℕ → ℕ) (d : ℕ) (hS : S.card ≤ n) (hd : d ≤ ∑ i ∈ S, a i) :
 ∃ I ∈ feasible S a d,
   inv n S a d = key n a I ∧ inv m S a d = key m a I ∧
   (∀ K ∈ feasible S a d, key n a K ≤ key n a I) ∧
   (∀ K ∈ feasible S a d, key m a K ≤ key m a I) := by
 obtain ⟨I,hI,hin,hmax⟩ := exists_top (n := n) hd
 have hIn : I.card ≤ n := (Finset.card_le_card (mem_feasible.mp hI).1).trans hS
 have hm : ∀ K ∈ feasible S a d, key m a K ≤ key m a I := by
   intro K hK
   exact (key_le_key_dimension_iff n m hnm a a K I
     ((Finset.card_le_card (mem_feasible.mp hK).1).trans hS) hIn).mp (hmax K hK)
 refine ⟨I,hI,hin,?_,hmax,hm⟩
 apply le_antisymm
 · apply Finset.max_le
   intro v hv
   obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hv
   exact WithBot.coe_le_coe.mpr (hm K hK)
 · exact Finset.le_max (Finset.mem_image_of_mem _ hI)

/-- COMPLETE invariant comparison, with internally produced tops and literal empty feasible cases. -/
theorem inv_le_inv_dimension_iff (n m : ℕ) (hnm : n ≤ m)
 (S T : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ) (hS : S.card ≤ n) (hT : T.card ≤ n) :
 inv n S a d ≤ inv n T b e ↔ inv m S a d ≤ inv m T b e := by
 by_cases hd : d ≤ ∑ i ∈ S, a i
 · obtain ⟨I,hI,hin,him,_,_⟩ := exists_common_top_dimensions n m hnm S a d hS hd
   by_cases he : e ≤ ∑ i ∈ T, b i
   · obtain ⟨J,hJ,hjn,hjm,_,_⟩ := exists_common_top_dimensions n m hnm T b e hT he
     rw [hin,him,hjn,hjm,WithBot.coe_le_coe,WithBot.coe_le_coe]
     exact key_le_key_dimension_iff n m hnm a b I J
       ((Finset.card_le_card (mem_feasible.mp hI).1).trans hS)
       ((Finset.card_le_card (mem_feasible.mp hJ).1).trans hT)
   · have hen : inv n T b e = ⊥ := inv_eq_bot_iff.mpr (by omega)
     have hem : inv m T b e = ⊥ := inv_eq_bot_iff.mpr (by omega)
     rw [hin,him,hen,hem]
     simp
 · have hdn : inv n S a d = ⊥ := inv_eq_bot_iff.mpr (by omega)
   have hdm : inv m S a d = ⊥ := inv_eq_bot_iff.mpr (by omega)
   rw [hdn,hdm]
   simp

/-- Entire invariant equality is reflected by the genuine dimension change. -/
theorem inv_eq_inv_dimension_iff (n m : ℕ) (hnm : n ≤ m)
 (S T : Finset ℕ) (a b : ℕ → ℕ) (d e : ℕ) (hS : S.card ≤ n) (hT : T.card ≤ n) :
 inv n S a d = inv n T b e ↔ inv m S a d = inv m T b e := by
 rw [le_antisymm_iff,le_antisymm_iff,
   inv_le_inv_dimension_iff n m hnm S T a b d e hS hT,
   inv_le_inv_dimension_iff n m hnm T S b a e d hT hS]

variable {f : Y → X}
variable (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
 {I : GermIdeal n X} (hI : I.IsCoherent) {E : List (Set X)} (hE : IsSNCDivisor n E)
include hf hI hE

/-- Actual original SNC inputs internally produce the WHOLE pulled gamma ordering dictionary. -/
theorem gamma_pullback_le_iff (d : ℕ) (y z : Y) :
 gamma m (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y ≤
   gamma m (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d z ↔
 gamma n I E d (f y) ≤ gamma n I E d (f z) := by
 rw [gamma_pullback_original_dictionary hf hI E d y,
   gamma_pullback_original_dictionary hf hI E d z]
 exact (inv_le_inv_dimension_iff n m (dimension_le_of_submersionAt (hf.isSubmersionAt y))
   (memberIdx E (f y)) (memberIdx E (f z)) (expData n I E (f y))
   (expData n I E (f z)) d d (card_memberIdx_le E hE (f y)) (card_memberIdx_le E hE (f z))).symm

/-- Actual original gamma equality, including literal bottom and whole colex ties. -/
theorem gamma_pullback_eq_iff (d : ℕ) (y z : Y) :
 gamma m (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d y =
   gamma m (GermIdeal.pullback (m := m) f I) (E.map (f ⁻¹' ·)) d z ↔
 gamma n I E d (f y) = gamma n I E d (f z) := by
 rw [le_antisymm_iff,le_antisymm_iff,
   gamma_pullback_le_iff hf hI hE d y z,gamma_pullback_le_iff hf hI hE d z y]

omit hI hE in
/-- Genuine surjectivity transports the literal original marked maximum locus on actual cosupport. -/
theorem maxLocus_gamma_markedPullback_eq (hsurj : Function.Surjective f)
 (M : MarkedIdeal n X) (hN : M.N = univ)
 (hM : M.ideal.IsCoherent) (hME : IsSNCDivisor n M.E) :
 ResolutionDriver.maxLocus
   (gamma m (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).E M.d)
   (markedPullback (m := m) f M).cosupp =
 f ⁻¹' ResolutionDriver.maxLocus (gamma n M.ideal M.E M.d) M.cosupp := by
 have hcs : (markedPullback (m := m) f M).cosupp = f ⁻¹' M.cosupp := by
   change cosupport m (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal) M.d =
     f ⁻¹' cosupport n M.N M.ideal M.d
   rw [hN,Set.preimage_univ]
   exact cosupport_pullback_eq hf hM M.d
 ext y
 change (y ∈ (markedPullback (m := m) f M).cosupp ∧ ∀ z ∈
   (markedPullback (m := m) f M).cosupp,
   gamma m (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).E M.d z ≤
   gamma m (markedPullback (m := m) f M).ideal (markedPullback (m := m) f M).E M.d y) ↔
   f y ∈ M.cosupp ∧ ∀ x ∈ M.cosupp, gamma n M.ideal M.E M.d x ≤ gamma n M.ideal M.E M.d (f y)
 rw [hcs]
 constructor
 · rintro ⟨hy,hmax⟩
   refine ⟨hy,?_⟩
   intro x hx
   obtain ⟨z,rfl⟩ := hsurj x
   exact (gamma_pullback_le_iff hf hM hME M.d z y).mp (hmax z hx)
 · rintro ⟨hy,hmax⟩
   refine ⟨hy,?_⟩
   intro z hz
   exact (gamma_pullback_le_iff hf hM hME M.d z y).mpr (hmax (f z) hz)

end
end Hironaka.HironakaSmoothSubmersionMonomialOrdering
