/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSNCComponentCoefficients
import Hironaka.Resolution.HironakaConnectedBoundaryComponents
import Hironaka.Resolution.HironakaEffectiveDivisorSum

set_option autoImplicit false

/-!
# The genuine locally finite component sum of an SNC-supported divisor

The global component coefficients are produced from the original divisor.
Local finiteness selects actual global connected carriers, and the intrinsic
monomial ideal gives the complete local product stalks. No compactness or
incoming ideal factorization is assumed.
Blueprint: `hironaka-locally-finite-divisor-sum-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaLocallyFiniteDivisorSum

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open NormalCrossings IdealWeightPowers HironakaDivisorResidual
  HironakaDivisorPowers HironakaSNCComponentCoefficients
  HironakaSNCSupportedMonomialIdeal HironakaConnectedBoundaryComponents
  HironakaEffectiveDivisorSum MonomialPart DivisorExponent
  RelativePrincipalizationSpan BlowupStrictIdeal

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Equality of the complete original stalks identifies all actual powers. -/
theorem idealPow_mem_iff_of_mem_iff {I J : GermIdeal n M} {x : M}
    (h : ∀ g, I.mem x g ↔ J.mem x g) (r : ℕ) (g : M → ℂ) :
    (idealPow I r).mem x g ↔ (idealPow J r).mem x g :=
  ⟨ExceptionalIdealPushforward.mem_idealPow_of_mem_at (fun g => (h g).mp) r,
    ExceptionalIdealPushforward.mem_idealPow_of_mem_at (fun g => (h g).mpr) r⟩

/-- The actual finite hypersurface sum is supported on its genuine carriers. -/
theorem support_componentSum_subset (A : List (Set M × ℕ))
    (hA : ∀ p ∈ A, IsClosed p.1 ∧
      ∀ x ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 x d ∧ d + 1 = n) :
    (componentSum A hA).support ⊆ ⋃ C ∈ A.map Prod.fst, C := by
  induction A with
  | nil => simp [componentSum]
  | cons p A ih =>
    have ht := ih (fun q hq => hA q (List.mem_cons_of_mem p hq))
    have hp : (p.2 • hypersurfaceDivisor (hA p (by simp)).1
        (hA p (by simp)).2).support ⊆ p.1 := by
      by_cases hz : p.2 = 0
      · simp [hz]
      · rw [support_nsmul _ (Nat.pos_of_ne_zero hz), support_hypersurfaceDivisor]
    intro x hx
    change x ∈ (p.2 • hypersurfaceDivisor (n := n) (hA p (by simp)).1
      (hA p (by simp)).2 + componentSum A (fun q hq =>
        hA q (List.mem_cons_of_mem p hq))).support at hx
    rw [support_add] at hx
    rcases hx with hx | hx
    · exact mem_iUnion₂.mpr ⟨p.1, by simp, hp hx⟩
    · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion₂.mpr ⟨C, by simp only [List.map_cons, List.mem_cons]; exact Or.inr hC,
        hxC⟩

private theorem filter_positive_componentPowerProduct (A : List (Set M × ℕ))
    (hA : ∀ p ∈ A, IsClosedSubmanifold n p.1) :
    componentPowerProduct (n := n) (A.filter fun p => 0 < p.2) =
      componentPowerProduct (n := n) A := by
  induction A with
  | nil => rfl
  | cons p A ih =>
    have ht := ih (fun q hq => hA q (List.mem_cons_of_mem p hq))
    by_cases hp : 0 < p.2
    · simp [hp, componentPowerProduct, ht]
    · have hz : p.2 = 0 := Nat.eq_zero_of_not_pos hp
      rw [List.filter_cons_of_neg (by simpa using hp), ht]
      rw [componentPowerProduct, hz, idealPow_zero]
      exact (BlowupControlledTransform.unitIdeal_mul
        (isCoherent_componentPowerProduct A
          (fun q hq => hA q (List.mem_cons_of_mem p hq)))).symm

section Positive

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- One genuine original-divisor exponent on every actual boundary component. -/
theorem exists_original_coefficients_boundaryComponents {E : List (Set X)}
    (hE : IsSNCDivisor (m + 1) E) (D : EffectiveDivisor (m + 1) X) :
    ∃ a : boundaryComponents E → ℕ,
      ∀ C : boundaryComponents E, ∀ x ∈ (C : Set X),
        divExp (m + 1) D.ideal (C : Set X) x = a C := by
  obtain ⟨a, ha⟩ := exists_multiplicities_boundaryComponents hE D
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt (m + 1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
  refine ⟨a, fun C x hx => Nat.le_antisymm ?_ ?_⟩
  · exact (ha C x hx _).mp (isDivNear_divExp hhol x)
  · exact (isDivNear_iff_le_divExp hhol hx
      (isNonzeroAt_of_isInvertible D.isInvertible x)).mp ((ha C x hx _).mpr le_rfl)

private theorem component_parent_germ {E : List (Set X)}
    (hE : IsSNCDivisor (m + 1) E) {C : Set X} (hC : C ∈ boundaryComponents E)
    {x : X} (hx : x ∈ C) (I : GermIdeal (m + 1) X) :
    ∃ i : Fin E.length, x ∈ E.get i ∧
      (∀ᶠ z in 𝓝 x, z ∈ C ↔ z ∈ E.get i) ∧
      divExp (m + 1) I C x = divExp (m + 1) I (E.get i) x := by
  obtain ⟨i, c, hc, rfl⟩ := hC
  obtain ⟨V, -, hVC, -, -, -, -, hlocal⟩ :=
    SNCGlobalPrimeComponents.exists_global_prime_component hE i hc
  obtain ⟨U, hU, hxU, heq⟩ := hlocal x (hVC.symm ▸ hx)
  rw [hVC] at heq
  refine ⟨i, connectedComponentIn_subset (E.get i) c hx, ?_,
    divExp_connectedComponent_eq hE i hc hx I⟩
  filter_upwards [hU.mem_nhds hxU] with z hzU
  have hz := Set.ext_iff.mp heq z
  simpa only [mem_inter_iff, hzU, and_true] using hz.symm

/-- Every complete intrinsic monomial stalk is the actual finite component
product whenever the finite refinement contains all components through it. -/
theorem monomialPart_mem_iff_componentPowerProduct_of_refinement
    (D : EffectiveDivisor (m + 1) X) {E : List (Set X)}
    (hE : IsSNCDivisor (m + 1) E) (F : List (Set X)) (hFnd : F.Nodup)
    (hF : ∀ C ∈ F, C ∈ boundaryComponents E)
    (a : boundaryComponents E → ℕ)
    (ha : ∀ C : boundaryComponents E, ∀ y ∈ (C : Set X),
      divExp (m + 1) D.ideal (C : Set X) y = a C)
    (b : Set X → ℕ) (hb : ∀ C (hC : C ∈ F), b C = a ⟨C, hF C hC⟩)
    {x : X} (hcomplete : ∀ C ∈ boundaryComponents E, x ∈ C → C ∈ F) (g : X → ℂ) :
    (monomialPart (m + 1) D.ideal E).mem x g ↔
      (componentPowerProduct (n := m + 1) (F.map fun C => (C, b C))).mem x g := by
  let A := F.map fun C => (C, b C)
  have hmap : A.map Prod.fst = F := by simp [A, List.map_map, Function.comp_def]
  have hgeom : ∀ p ∈ A, IsClosed p.1 ∧
      ∀ y ∈ p.1, ∃ d, RegularAtDim (n := m + 1) p.1 y d ∧ d + 1 = m + 1 := by
    intro p hp
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hp
    have hg := (component_geometry hE (hF C hC)).1
    exact ⟨hg.1, fun y hy => ⟨m, hg.2.2 y hy, rfl⟩⟩
  let G := componentSum A hgeom
  have hGI : G.ideal = componentPowerProduct (n := m + 1) A := ideal_componentSum A hgeom
  have hFsnc := isSNCDivisor_component_refinement hE hF hFnd
  have hGmono : G.ideal = monomialPart (m + 1) G.ideal F :=
    ideal_eq_monomialPart_of_support_subset G F hFsnc (by
      simpa only [hmap] using support_componentSum_subset A hgeom)
  have hGexp : ∀ C (hC : C ∈ F), ∀ y ∈ C,
      divExp (m + 1) G.ideal C y = b C := by
    intro C hC y hy
    rw [hGI]
    exact divExp_componentPowerProduct_eq A (hmap.symm ▸ hFsnc) (hmap.symm ▸ hFnd)
      (show (C, b C) ∈ A from List.mem_map.mpr ⟨C, hC, rfl⟩) hy
  have hDF : (monomialPart (m + 1) D.ideal E).mem x g ↔
      (monomialPart (m + 1) D.ideal F).mem x g := by
    constructor
    · intro hg
      refine ⟨hg.1, fun j hxC => ?_⟩
      have hC := hF (F.get j) (List.get_mem F j)
      obtain ⟨i, hxi, hlocal, hexp⟩ := component_parent_germ hE hC hxC D.ideal
      rw [hexp]
      exact (idealPow_mem_iff_of_mem_iff
        (fun q => vanishingIdeal_mem_congr hlocal q) _ g).mpr (hg.2 i hxi)
    · intro hg
      refine ⟨hg.1, fun i hxi => ?_⟩
      let C := connectedComponentIn (E.get i) x
      have hxC : x ∈ C := mem_connectedComponentIn hxi
      have hC : C ∈ boundaryComponents E := ⟨i, x, hxi, rfl⟩
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp (hcomplete C hC hxC)
      obtain ⟨V, -, hVC, -, -, -, -, hlocal⟩ :=
        SNCGlobalPrimeComponents.exists_global_prime_component hE i hxi
      obtain ⟨U, hU, hxU, heq⟩ := hlocal x (hVC.symm ▸ hxC)
      rw [hVC] at heq
      have hset : ∀ᶠ z in 𝓝 x, z ∈ C ↔ z ∈ E.get i := by
        filter_upwards [hU.mem_nhds hxU] with z hzU
        have hz := Set.ext_iff.mp heq z
        simpa only [mem_inter_iff, hzU, and_true] using hz.symm
      have hexp := divExp_connectedComponent_eq hE i hxi hxC D.ideal
      have hmem := hg.2 j (hj ▸ hxC)
      rw [hj, hexp] at hmem
      exact (idealPow_mem_iff_of_mem_iff (fun q => vanishingIdeal_mem_congr hset q) _ g).mp hmem
  have hDG : (monomialPart (m + 1) D.ideal F).mem x g ↔
      (monomialPart (m + 1) G.ideal F).mem x g := by
    have he : ∀ j : Fin F.length, x ∈ F.get j →
        divExp (m + 1) D.ideal (F.get j) x = divExp (m + 1) G.ideal (F.get j) x := by
      intro j hxj
      have hC := List.get_mem F j
      rw [ha ⟨F.get j, hF _ hC⟩ x hxj, hGexp _ hC x hxj, hb _ hC]
    constructor
    · exact fun hg => ⟨hg.1, fun j hxj => (he j hxj) ▸ hg.2 j hxj⟩
    · exact fun hg => ⟨hg.1, fun j hxj => (he j hxj).symm ▸ hg.2 j hxj⟩
  exact hDF.trans (hDG.trans (by rw [← hGmono, hGI]))

/-- Local finiteness and the actual monomial ideal produce finite nearby
products, with the original global coefficients and every zero factor removed. -/
theorem exists_positive_locallyFinite_original_component_products
    (D : EffectiveDivisor (m + 1) X) (E : List (Set X))
    (hE : IsSNCDivisor (m + 1) E) (hsupport : D.support ⊆ ⋃ C ∈ E, C) :
    ∃ a : boundaryComponents E → ℕ,
      LocallyFinite (fun C : boundaryComponents E => (C : Set X)) ∧
      (∀ C : boundaryComponents E, ∀ y ∈ (C : Set X),
        divExp (m + 1) D.ideal (C : Set X) y = a C) ∧
      ∀ x : X, ∃ U : Set X, ∃ A : List (Set X × ℕ), IsOpen U ∧ x ∈ U ∧
        (A.map Prod.fst).Nodup ∧
        (∀ p ∈ A, ∃ hC : p.1 ∈ boundaryComponents E, p.2 = a ⟨p.1, hC⟩ ∧ 0 < p.2) ∧
        ∀ y ∈ U, ∀ g, D.ideal.mem y g ↔ (componentPowerProduct (n := m + 1) A).mem y g := by
  classical
  obtain ⟨a, ha⟩ := exists_original_coefficients_boundaryComponents hE D
  refine ⟨a, locallyFinite_boundaryComponents hE, ha, fun x => ?_⟩
  obtain ⟨U, hU, hxU, hfin⟩ := exists_isOpen_finite_boundaryComponents hE x
  let F := hfin.toFinset.toList
  have hmem : ∀ C, C ∈ F ↔ C ∈ boundaryComponents E ∧ (C ∩ U).Nonempty := by
    intro C
    simp [F]
  have hF : ∀ C ∈ F, C ∈ boundaryComponents E := fun C hC => ((hmem C).mp hC).1
  have hnd : F.Nodup := Finset.nodup_toList _
  let b : Set X → ℕ := fun C => if hC : C ∈ boundaryComponents E then a ⟨C, hC⟩ else 0
  have hb : ∀ C (hC : C ∈ F), b C = a ⟨C, hF C hC⟩ := by
    intro C hC
    simp only [b, dif_pos (hF C hC)]
  let A := F.map fun C => (C, b C)
  have hmap : A.map Prod.fst = F := by simp [A, List.map_map, Function.comp_def]
  have hgeom : ∀ p ∈ A, IsClosedSubmanifold (m + 1) p.1 := by
    intro p hp
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hp
    have hg := (component_geometry hE (hF C hC)).1
    exact ⟨hg.1, fun y hy => ⟨m, hg.2.2 y hy⟩⟩
  have hfull : ∀ y ∈ U, ∀ g, D.ideal.mem y g ↔
      (componentPowerProduct (n := m + 1) A).mem y g := by
    intro y hy g
    rw [ideal_eq_monomialPart_of_support_subset D E hE hsupport]
    exact monomialPart_mem_iff_componentPowerProduct_of_refinement D hE F hnd hF a ha b hb
      (fun C hC hyC => (hmem C).mpr ⟨hC, y, hyC, hy⟩) g
  let B := A.filter fun p => 0 < p.2
  have hBA : componentPowerProduct (n := m + 1) B = componentPowerProduct A :=
    filter_positive_componentPowerProduct A hgeom
  refine ⟨U, B, hU, hxU, ?_, ?_, ?_⟩
  · exact (hmap.symm ▸ hnd).sublist (List.filter_sublist.map Prod.fst)
  · intro p hp
    have hpA := (List.mem_filter.mp hp).1
    have hp0 : 0 < p.2 := by simpa using (List.mem_filter.mp hp).2
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hpA
    exact ⟨hF C hC, hb C hC, hp0⟩
  · intro y hy g
    rw [hBA]
    exact hfull y hy g

end Positive

/-- Without compactness, the genuine locally finite carrier family has one
original coefficient function and complete positive local product stalks. -/
theorem exists_locallyFinite_original_component_products
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ C ∈ E, C) :
    ∃ a : boundaryComponents E → ℕ,
      LocallyFinite (fun C : boundaryComponents E => (C : Set M)) ∧
      (∀ C : boundaryComponents E, ∀ y ∈ (C : Set M), divExp n D.ideal (C : Set M) y = a C) ∧
      ∀ x : M, ∃ U : Set M, ∃ A : List (Set M × ℕ), IsOpen U ∧ x ∈ U ∧
        (A.map Prod.fst).Nodup ∧
        (∀ p ∈ A, ∃ hC : p.1 ∈ boundaryComponents E, p.2 = a ⟨p.1, hC⟩ ∧ 0 < p.2) ∧
        ∀ y ∈ U, ∀ g, D.ideal.mem y g ↔ (componentPowerProduct (n := n) A).mem y g := by
  cases n with
  | succ m => exact exists_positive_locallyFinite_original_component_products D E hE hsupport
  | zero =>
    have hempty := boundaryComponents_eq_empty_of_isSNCDivisor_zero hE
    let : IsEmpty (boundaryComponents E) :=
      ⟨fun C => (eq_empty_iff_forall_notMem.mp hempty) C.1 C.2⟩
    have hunit : D.ideal = unitIdeal 0 M :=
      (ideal_eq_monomialPart_of_support_subset D E hE hsupport).trans
        (monomialPart_eq_unitIdeal_of_dim_zero D.ideal E hE)
    refine ⟨fun C => isEmptyElim C, locallyFinite_of_finite _, ?_, fun x => ?_⟩
    · intro C
      exact isEmptyElim C
    · refine ⟨univ, [], isOpen_univ, mem_univ x, List.nodup_nil, ?_, ?_⟩
      · simp
      · intro y _ g
        rw [hunit]
        rfl

/-- The positive local products are ideals of actual finite divisor sums,
with the same original coefficients on the same genuine global carriers. -/
theorem exists_locallyFinite_original_component_sums
    (D : EffectiveDivisor n M) (E : List (Set M)) (hE : IsSNCDivisor n E)
    (hsupport : D.support ⊆ ⋃ C ∈ E, C) :
    ∃ a : boundaryComponents E → ℕ,
      LocallyFinite (fun C : boundaryComponents E => (C : Set M)) ∧
      (∀ C : boundaryComponents E, ∀ y ∈ (C : Set M), divExp n D.ideal (C : Set M) y = a C) ∧
      ∀ x : M, ∃ U : Set M, ∃ A : List (Set M × ℕ), IsOpen U ∧ x ∈ U ∧
        (A.map Prod.fst).Nodup ∧
        (∀ p ∈ A, ∃ hC : p.1 ∈ boundaryComponents E, p.2 = a ⟨p.1, hC⟩ ∧ 0 < p.2) ∧
        ∃ hA : ∀ p ∈ A, IsClosed p.1 ∧
          ∀ y ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 y d ∧ d + 1 = n,
          ∀ y ∈ U, ∀ g, D.ideal.mem y g ↔ (componentSum A hA).ideal.mem y g := by
  obtain ⟨a, hlf, ha, hlocal⟩ := exists_locallyFinite_original_component_products D E hE hsupport
  refine ⟨a, hlf, ha, fun x => ?_⟩
  obtain ⟨U, A, hU, hxU, hnd, hcoef, hfull⟩ := hlocal x
  have hA : ∀ p ∈ A, IsClosed p.1 ∧
      ∀ y ∈ p.1, ∃ d, RegularAtDim (n := n) p.1 y d ∧ d + 1 = n := by
    cases n with
    | zero =>
      intro p hp
      obtain ⟨hC, -, -⟩ := hcoef p hp
      rw [boundaryComponents_eq_empty_of_isSNCDivisor_zero hE] at hC
      exact False.elim hC
    | succ m =>
      intro p hp
      obtain ⟨hC, -, -⟩ := hcoef p hp
      have hg := (component_geometry hE hC).1
      exact ⟨hg.1, fun y hy => ⟨m, hg.2.2 y hy, rfl⟩⟩
  refine ⟨U, A, hU, hxU, hnd, hcoef, hA, fun y hy g => ?_⟩
  rw [ideal_componentSum]
  exact hfull y hy g

end
end Hironaka.HironakaLocallyFiniteDivisorSum
