/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaLocallyFiniteDivisorSum
import Hironaka.Resolution.HironakaBaseChange
import Hironaka.Blowup.LiftedOpenModel

import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.MarkedIdeal.GermIdealOrderBounds

set_option autoImplicit false

/-!
# Actual local branches of general normal crossings carriers

Coordinate hyperplanes, the actual flattening biholomorphism, and open
restriction produce the local branch list and original-divisor dictionary.
Global canonical blowup descent for general NC is a separate obligation.
Blueprint: `hironaka-normal-crossings-local-branches-extension.tex`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNormalCrossingsLocalBranches

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open NormalCrossings NormalCrossingsInvariance BlowupFlatCoordinates
  HironakaLocallyFiniteDivisorSum HironakaConnectedBoundaryComponents
  HironakaDivisorResidual HironakaDivisorPowers DivisorExponent
  RelativePrincipalizationSpan GermIdealTotalTransform BlowupRestrictOpen

noncomputable section

variable {n : ℕ}

private def coordinateTranslation (w : ComplexModel n) :
    LocalHolomorphicEquivAt (n := n) w where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := fun z => z - w
  invFun := fun z => z + w
  toFun_holomorphic := (differentiable_id.sub_const w).differentiableOn
  invFun_holomorphic := (differentiable_id.add_const w).differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => sub_add_cancel _ _
  right_inv := fun _ _ => add_sub_cancel_right _ _

/-- The actual distinct coordinate hyperplanes, lifted only for universe compatibility. -/
def coordinateHyperplanes (S : Finset (Fin n)) : List (Set (LiftedModel.{u} n)) :=
  S.toList.map fun j => {w | w.down j = 0}

/-- Actual coordinate hyperplanes satisfy the SNC condition at every point. -/
theorem isSNCDivisor_coordinateHyperplanes (S : Finset (Fin n)) :
    IsSNCDivisor n (coordinateHyperplanes.{u} S) := by
  classical
  let J := S.toList
  let E := coordinateHyperplanes.{u} S
  let c : Fin E.length → Fin J.length := Fin.cast (List.length_map _)
  let σ : Fin E.length → Fin n := fun i => J.get (c i)
  have hget : ∀ i : Fin E.length, E.get i = {w : LiftedModel.{u} n | w.down (σ i) = 0} := by
    intro i
    change (J.map fun j => {w : LiftedModel.{u} n | w.down j = 0})[i.1]'i.2 =
      {w : LiftedModel.{u} n | w.down (J.get (c i)) = 0}
    simp only [LiftedModel, List.getElem_map]
    rfl
  have hinj : Function.Injective σ := by
    intro i j hij
    exact Fin.cast_injective _ ((Finset.nodup_toList S).injective_get hij)
  refine ⟨?_, fun w => ?_⟩
  · intro H hH
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hH
    exact isClosed_eq
      ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).continuous.comp continuous_uliftDown)
      continuous_const
  · have he : chartAt (ComplexModel n) w = LiftedModel.chart := rfl
    refine ⟨fun i => {σ i}, ⟨coordinateTranslation w.down, ?_, ?_, ?_⟩,
      fun _ _ => Finset.card_singleton _, fun i _ j _ hij => ?_⟩
    · intro z _
      change z ∈ (chartAt (ComplexModel n) w).target
      rw [he]
      exact mem_univ _
    · change w.down - w.down = 0
      exact sub_self _
    · intro i hwi y _ _
      change w ∈ E.get i at hwi
      change y ∈ E.get i ↔ (coordinateTranslation w.down).toFun
        (chartAt (ComplexModel n) w y) ∈ coordSubspace {σ i}
      rw [hget] at hwi ⊢
      change w.down (σ i) = 0 at hwi
      change y.down (σ i) = 0 ↔ (y.down - w.down) ∈ coordSubspace {σ i}
      simp [coordSubspace, hwi]
    · exact hinj (Finset.singleton_injective hij)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- General normal crossings are a local union of distinct coordinate hyperplanes,
with no global smooth list or global component labelling required. -/
def IsNormalCrossingsCarrier (H : Set M) : Prop :=
  IsClosed H ∧ ∀ x : M,
    ∃ Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      ∃ S : Finset (Fin n), ∀ y ∈ flatDomain Φ,
        y ∈ H ↔ ∃ j ∈ S, flatCoord Φ j y = 0

variable {x : M}

/-- The actual flattening map, with its actual inverse, is a biholomorphism
between the open flat domain and the open flattening target. -/
def flatDomainDiffeomorph
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    (⟨flatDomain Φ, isOpen_flatDomain Φ⟩ : Opens M) ≃ₘ⟮𝓘(ℂ, ComplexModel n),
      𝓘(ℂ, ComplexModel n)⟯ LiftedOpen.{u} ⟨Φ.target, Φ.isOpen_target⟩ := by
  let U : Opens M := ⟨flatDomain Φ, isOpen_flatDomain Φ⟩
  let T : Opens (ComplexModel n) := ⟨Φ.target, Φ.isOpen_target⟩
  let f : U → LiftedOpen.{u} T := fun p =>
    LiftedOpen.mk T (Φ.toFun (chartAt (ComplexModel n) x p.1)) (Φ.mapsTo_toFun p.2.2)
  let g : LiftedOpen.{u} T → U := fun q =>
    ⟨(chartAt (ComplexModel n) x).symm (Φ.invFun (LiftedOpen.toModel T q)),
      (flatInverse_mem Φ q.2 hsrc).1⟩
  have hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f := by
    intro p
    apply LiftedOpen.contMDiffAt_of_toModel
    change ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun q : U => Φ.toFun (chartAt (ComplexModel n) x q.1)) p
    have hΦ : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.toFun
        (chartAt (ComplexModel n) x p.1) :=
      (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source p.2.2).contMDiffAt
    have he : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (chartAt (ComplexModel n) x) p.1 :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt
        ((chartAt (ComplexModel n) x).open_source.mem_nhds p.2.1)
    exact hΦ.comp p (he.comp p (contMDiff_subtype_val p))
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g := by
    dsimp only [g]
    refine contMDiff_opens_mk (V := U) (f := fun q : LiftedOpen.{u} T =>
      (chartAt (ComplexModel n) x).symm (Φ.invFun (LiftedOpen.toModel T q)))
        (fun q => ?_) (fun q => (flatInverse_mem Φ q.2 hsrc).1)
    have hΦ : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.invFun
        (LiftedOpen.toModel T q) :=
      (contDiffAt_of_differentiableOn_complex Φ.invFun_holomorphic Φ.isOpen_target q.2).contMDiffAt
    have he : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
        (chartAt (ComplexModel n) x).symm (Φ.invFun (LiftedOpen.toModel T q)) :=
      (contMDiffOn_chart_symm (n := ∞)).contMDiffAt
        ((chartAt (ComplexModel n) x).open_target.mem_nhds (hsrc (Φ.mapsTo_invFun q.2)))
    exact he.comp q (hΦ.comp q (LiftedOpen.contMDiff_toModel T q))
  refine ⟨⟨f, g, fun p => ?_, fun q => ?_⟩, hf, hg⟩
  · exact Subtype.ext (flatInverse_flat Φ p.2)
  · apply Subtype.ext
    apply ULift.ext
    exact (flatInverse_mem Φ q.2 hsrc).2

/-- Actual general-NC coordinates internally produce a whole-neighbourhood
SNC list, retaining its real coordinate-preimage construction. -/
theorem exists_actual_snc_branches {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) :
    ∃ (U : Opens M) (E : List (Set U)), x ∈ U ∧ IsSNCDivisor n E ∧
      (Subtype.val : U → M) ⁻¹' H = ⋃ C ∈ E, C ∧
      ∃ (T : Opens (ComplexModel n))
        (χ : U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ LiftedOpen.{u} T)
        (S : Finset (Fin n)),
        E = ((coordinateHyperplanes.{u} S).map
          ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' ·)).map (χ ⁻¹' ·) := by
  classical
  obtain ⟨Φ, hsrc, -, S, hflat⟩ := hH.2 x
  let U : Opens M := ⟨flatDomain Φ, isOpen_flatDomain Φ⟩
  let T : Opens (ComplexModel n) := ⟨Φ.target, Φ.isOpen_target⟩
  let χ := flatDomainDiffeomorph Φ hsrc
  let F := (coordinateHyperplanes.{u} S).map
    ((Subtype.val : LiftedOpen.{u} T → LiftedModel.{u} n) ⁻¹' ·)
  let E := F.map (χ ⁻¹' ·)
  have hFsnc : IsSNCDivisor n F := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (liftedOpens.{u} T)) continuous_subtype_val
    (isSNCDivisor_coordinateHyperplanes S)
  have hEsnc : IsSNCDivisor n E := isSNCDivisor_map_preimage
    (MarkedIdealTowerTransport.pullsBackCoordinates χ) χ.contMDiff.continuous hFsnc
  have hEeq : E = S.toList.map (fun j => {p : U | flatCoord Φ j p.1 = 0}) := by
    simp only [E, F, coordinateHyperplanes, List.map_map]
    apply List.map_congr_left
    intro j _
    rfl
  refine ⟨U, E, mem_flatDomain_self Φ, hEsnc, ?_, T, χ, S, rfl⟩
  ext p
  change p.1 ∈ H ↔ p ∈ ⋃ C ∈ E, C
  rw [hflat p.1 p.2, hEeq]
  constructor
  · rintro ⟨j, hj, hz⟩
    exact mem_iUnion₂.mpr ⟨{p : U | flatCoord Φ j p.1 = 0},
      List.mem_map.mpr ⟨j, Finset.mem_toList.mpr hj, rfl⟩, hz⟩
  · intro hp
    obtain ⟨C, hC, hpC⟩ := mem_iUnion₂.mp hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hC
    exact ⟨j, Finset.mem_toList.mp hj, hpC⟩

/-- The genuine effective divisor obtained by the actual open pullback ideal. -/
def restrictDivisor (D : EffectiveDivisor n M) (U : Opens M) : EffectiveDivisor n U :=
  ⟨GermIdeal.pullback (m := n) (Subtype.val : U → M) D.ideal,
    isInvertible_pullback contMDiff_subtype_val (by
      rw [HironakaBaseChange.exceptionalLocus_val, interior_empty]) D.isInvertible⟩

@[simp] theorem ideal_restrictDivisor (D : EffectiveDivisor n M) (U : Opens M) :
    (restrictDivisor D U).ideal = GermIdeal.pullback (m := n) (Subtype.val : U → M) D.ideal := rfl

/-- Actual open restriction retains exactly the original divisor support. -/
theorem support_restrictDivisor (D : EffectiveDivisor n M) (U : Opens M) :
    (restrictDivisor D U).support = (Subtype.val : U → M) ⁻¹' D.support :=
  BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)

/-- Every germ on the open subset is identified with its whole original
ideal stalk membership, using its actual extension near that original point. -/
theorem mem_restrictDivisor_iff (D : EffectiveDivisor n M) (U : Opens M)
    (p : U) (g : U → ℂ) :
    (restrictDivisor D U).ideal.mem p g ↔ D.ideal.mem p.1 (extendOpens U g) :=
  MarkedIdealRestrictOpen.mem_pullback_val_iff U
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible)

private theorem isDivNear_restrictDivisor_iff (D : EffectiveDivisor n M) (U : Opens M)
    (C : Set U) (r : ℕ) (p : U) :
    IsDivNear n (restrictDivisor D U).ideal C r p ↔
      IsDivNear n D.ideal ((Subtype.val : U → M) '' C) r p.1 := by
  have hcoh := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg
  have hc := MarkedIdealRestrictOpen.cosupp_pullback_val
    (⟨univ, [], D.ideal, r⟩ : MarkedIdeals.MarkedIdeal n M) hhol U
  have hcos : ∀ q : U, q ∈ GermIdealOrder.cosupport n univ (restrictDivisor D U).ideal r ↔
      q.1 ∈ GermIdealOrder.cosupport n univ D.ideal r := by
    intro q
    have hq := Set.ext_iff.mp hc q
    simpa only [ideal_restrictDivisor, MarkedIdeals.MarkedIdeal.cosupp,
      MarkedIdealBiholomorphism.MarkedIdeal.pullback, preimage_univ, mem_preimage] using hq
  constructor
  · intro hd
    apply (eventually_nhds_val_iff U).mpr
    filter_upwards [hd] with q hq hqimage
    obtain ⟨v, hv, hvq⟩ := hqimage
    have hvq' : v = q := Subtype.ext hvq
    exact (hcos q).mp (hq (hvq' ▸ hv))
  · intro hd
    have hp := (eventually_nhds_val_iff U).mp hd
    filter_upwards [hp] with q hq hqC
    exact (hcos q).mpr (hq ⟨q, hqC, rfl⟩)

/-- The component exponent on the actual open restriction is the exponent
of the original divisor on the actual image carrier at every original point. -/
theorem divExp_restrictDivisor_eq (D : EffectiveDivisor n M) (U : Opens M)
    (C : Set U) {p : U} (hp : p ∈ C) :
    divExp n (restrictDivisor D U).ideal C p =
      divExp n D.ideal ((Subtype.val : U → M) '' C) p.1 := by
  have hcohD := DivisorMetric.isCoherent_of_isInvertible D.isInvertible
  have hcohU := DivisorMetric.isCoherent_of_isInvertible (restrictDivisor D U).isInvertible
  have hholD : ∀ x g, D.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcohD hg
  have hholU : ∀ x g, (restrictDivisor D U).ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcohU hg
  have hpimage : p.1 ∈ (Subtype.val : U → M) '' C := ⟨p, hp, rfl⟩
  apply Nat.le_antisymm
  · exact (isDivNear_iff_le_divExp hholD hpimage
      (isNonzeroAt_of_isInvertible D.isInvertible p.1)).mp
      ((isDivNear_restrictDivisor_iff D U C _ p).mp (isDivNear_divExp hholU p))
  · exact (isDivNear_iff_le_divExp hholU hp
      (isNonzeroAt_of_isInvertible (restrictDivisor D U).isInvertible p)).mp
      ((isDivNear_restrictDivisor_iff D U C _ p).mpr (isDivNear_divExp hholD p.1))

/-- General NC geometry internally gives the actual local SNC branches,
original-D component coefficients, and every complete nearby product stalk. -/
theorem exists_original_local_component_dictionary (D : EffectiveDivisor n M)
    {H : Set M} (hH : IsNormalCrossingsCarrier (n := n) H) (hsupport : D.support ⊆ H) (x : M) :
    ∃ (U : Opens M) (E : List (Set U)), x ∈ U ∧ IsSNCDivisor n E ∧
      (Subtype.val : U → M) ⁻¹' H = ⋃ C ∈ E, C ∧
      ∃ a : boundaryComponents E → ℕ,
        LocallyFinite (fun C : boundaryComponents E => (C : Set U)) ∧
        (∀ C : boundaryComponents E, ∀ y ∈ (C : Set U),
          divExp n D.ideal ((Subtype.val : U → M) '' (C : Set U)) y.1 = a C) ∧
        ∀ p : U, ∃ V : Set U, ∃ A : List (Set U × ℕ), IsOpen V ∧ p ∈ V ∧
          (A.map Prod.fst).Nodup ∧
          (∀ q ∈ A, ∃ hC : q.1 ∈ boundaryComponents E, q.2 = a ⟨q.1, hC⟩ ∧ 0 < q.2) ∧
          ∀ y ∈ V, ∀ g : U → ℂ, D.ideal.mem y.1 (extendOpens U g) ↔
            (componentPowerProduct (n := n) A).mem y g := by
  obtain ⟨U, E, hxU, hE, heq, -⟩ := exists_actual_snc_branches hH x
  have hDs : (restrictDivisor D U).support ⊆ ⋃ C ∈ E, C := by
    intro p hp
    rw [← heq]
    exact hsupport ((Set.ext_iff.mp (support_restrictDivisor D U) p).mp hp)
  obtain ⟨a, hlf, ha, hlocal⟩ :=
    exists_locallyFinite_original_component_products (restrictDivisor D U) E hE hDs
  refine ⟨U, E, hxU, hE, heq, a, hlf, ?_, fun p => ?_⟩
  · intro C y hy
    rw [← divExp_restrictDivisor_eq D U (C : Set U) hy]
    exact ha C y hy
  · obtain ⟨V, A, hV, hpV, hnd, hcoef, hfull⟩ := hlocal p
    refine ⟨V, A, hV, hpV, hnd, hcoef, fun y hy g => ?_⟩
    exact (mem_restrictDivisor_iff D U y g).symm.trans (hfull y hy g)

end
end Hironaka.HironakaNormalCrossingsLocalBranches
