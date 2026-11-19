/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.Embedded
public import Hironaka.Resolution.Algebraic.Kol07.StrictTransformUnion
import Hironaka.Algebra.Util.OpenMapGenericPoints
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Transform.Reduced
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Hironaka.Scheme.IdealSheaf.Order.Exceptional
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tools for the loop of `BED` along a smooth surjection

Clause (d) of [Wlo05, Theorem 1.0.2] ([Wlo05, 4.1]; the first clause of [Kol07, 34.1]): the
embedded desingularization sequence commutes with smooth morphisms. The loop of
`Hironaka.Resolution.Algebraic.Wlo05.Embedded` runs `BMO_1` and stops at the first stage where a
centre contains the strict transform of one of the remaining components `Yᵢ` of `Y`. Along a smooth
surjection `h : X' → X` carrying the pullback data, `BMO_1` itself commutes ([Kol07, Theorem 69]),
and this module supplies the bookkeeping of the STOP RULE and of the COMPONENTS:

* the irreducible components of `h⁻¹(Y)` are the components of the `h⁻¹(Yᵢ)`
  (`mem_genericPoints_preimage_iff`); the relation `IsPullbackComponents h C C'` records "`C'` =
  the components of the preimages of the members of `C`", the loop's invariant along `h`;
* the strict transform of a finite union is the union of the strict transforms
  (`coe_support_strictTransformSeq_biUnion`), and strict transforms are monotone in the ideal
  (`strictTransformSeq_mono`);
* **the stop rules coincide stagewise** (`stopRule_aux`): downstairs "`Z_n ⊇ X̄_n(Yᵢ)`" gives
  upstairs "`Z'_n ⊇ X̄'_n(Y'_{ij})`" for every component `Y'_{ij}` of `h⁻¹(Yᵢ)` by monotonicity
  (`h⁻¹ X̄_n(Yᵢ) = X̄'_n(h⁻¹ Yᵢ) ⊆ X̄'_n(Y'_{ij})`); conversely the generic point of
  `X̄'_n(Y'_{ij})`
  (the proof of [Kol07, Corollary 22]: the strict transform of an integral scheme has a generic
  point over the original one before its first containing centre,
  `exists_isGenericPoint_strictTransformSeq`) lies over the generic point of `X̄_n(Yᵢ)`, so a
  centre `Z'_n = h_n⁻¹(Z_n)` containing the former forces `Z_n` to contain the latter — both
  directions need that no earlier centre absorbed the component, which is exactly the loop's
  situation at its first absorbing stage (proved by strong induction on the stage);
* the truncation `S.take n` has the same stop rule as `S` below `n` (`centerContains_take_iff`,
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersMiss`), and the last-stage lift of a truncation
  carries the strict transforms and stage maps (`strictTransformSeq_pullback_last`,
  `pullbackLastHom_stageMap`).

The pullback and pushforward of blow-up sequences are those of [Kol07, Definition 30]. Used by
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullback` (the functoriality clause) and by the CP
modules.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  Hironaka BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

/-! ### Generic points of finite unions and of preimages -/

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- A closed set is the union of the closures of its generic points (every point is a
specialization of one of them). -/
theorem coe_closeds_eq_iUnion_closure_genericPoints [T0Space X] [QuasiSober X] (Z : Closeds X) :
    (Z : Set X) = ⋃ η ∈ Z.genericPoints, closure {η} := by
  ext x
  constructor
  · intro hx
    obtain ⟨η, hη, hηx⟩ := Closeds.exists_mem_genericPoints_specializes Z hx
    exact Set.mem_iUnion₂.mpr ⟨η, hη, specializes_iff_mem_closure.mp hηx⟩
  · intro hx
    obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hx
    exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη.1) hxη

/-- The generic point of a member of a finite family of closed sets that is maximal among the
members is a generic point of the union. -/
theorem mem_genericPoints_of_isGenericPoint_of_maximal [T0Space X] {ι : Type*}
    (s : Set ι) (A : ι → Closeds X) (Z : Closeds X) (hZ : (Z : Set X) = ⋃ i ∈ s, (A i : Set X))
    {i₀ : ι} (hi₀ : i₀ ∈ s) {g : X} (hg : IsGenericPoint g (A i₀ : Set X))
    (hmax : ∀ j ∈ s, (A i₀ : Set X) ⊆ A j → (A j : Set X) ⊆ A i₀) : g ∈ Z.genericPoints := by
  refine ⟨?_, fun ξ hξ hspec => ?_⟩
  · rw [← SetLike.mem_coe, hZ]
    exact Set.mem_iUnion₂.mpr ⟨i₀, hi₀, hg.mem⟩
  · have hξZ : ξ ∈ (Z : Set X) := hξ
    rw [hZ] at hξZ
    obtain ⟨j, hj, hξj⟩ := Set.mem_iUnion₂.mp hξZ
    have hgj : g ∈ (A j : Set X) :=
      (A j).isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξj)
        (specializes_iff_mem_closure.mp hspec)
    have hsub : (A i₀ : Set X) ⊆ A j := by
      rw [← hg.def]
      exact (A j).isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hgj)
    exact eq_of_specializes_of_isGenericPoint hg (hmax j hj hsub hξj) hspec

/-- A generic point of a finite union of irreducible closed sets is the generic point of one of
them. -/
theorem exists_eq_of_mem_genericPoints_biUnion {ι : Type*} (s : Set ι)
    (A : ι → Closeds X) (Z : Closeds X) (hZ : (Z : Set X) = ⋃ i ∈ s, (A i : Set X)) (g : ι → X)
    (hg : ∀ i ∈ s, IsGenericPoint (g i) (A i : Set X)) {η : X} (hη : η ∈ Z.genericPoints) :
    ∃ i ∈ s, η = g i := by
  have hηZ : η ∈ (Z : Set X) := hη.1
  rw [hZ] at hηZ
  obtain ⟨i, hi, hηi⟩ := Set.mem_iUnion₂.mp hηZ
  refine ⟨i, hi, ?_⟩
  have hgZ : g i ∈ Z := by
    rw [← SetLike.mem_coe, hZ]
    exact Set.mem_iUnion₂.mpr ⟨i, hi, (hg i hi).mem⟩
  exact (hη.2 hgZ ((hg i hi).specializes hηi)).symm

/-- Under a continuous open map from a Noetherian sober space, the generic points of the preimage
of `Z` are the generic points of the preimages of the components of `Z` ([Wlo05, 4.1], read on the
components of `Y`). -/
theorem mem_genericPoints_preimage_iff [T0Space X] [QuasiSober X] {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] [QuasiSober Y] [NoetherianSpace Y] {f : Y → X} (hf : Continuous f)
    (ho : IsOpenMap f) (Z : Closeds X) (η' : Y) :
    η' ∈ (Z.preimage hf).genericPoints ↔
      ∃ η ∈ Z.genericPoints, η' ∈ ((Closeds.closure {η}).preimage hf).genericPoints := by
  constructor
  · intro h
    refine ⟨f η', mem_genericPoints_of_mem_genericPoints_preimage hf ho Z h, ?_⟩
    refine ⟨?_, fun ξ hξ hspec => h.2 ?_ hspec⟩
    · change f η' ∈ closure {f η'}
      exact subset_closure (Set.mem_singleton _)
    · change f ξ ∈ closure {f η'} at hξ
      change f ξ ∈ Z
      exact Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h.1) hξ
  · rintro ⟨η, hη, hη'⟩
    have hfη' : f η' = η := by
      have hgp := mem_genericPoints_of_mem_genericPoints_preimage hf ho
        (Closeds.closure {η}) hη'
      have hmem : f η' ∈ closure {η} := hη'.1
      exact (hgp.2 (subset_closure (Set.mem_singleton η))
        (specializes_iff_mem_closure.mpr hmem)).symm
    refine ⟨?_, fun ξ hξ hspec => ?_⟩
    · change f η' ∈ Z
      rw [hfη']
      exact hη.1
    · have hfξ : f ξ = η := hη.2 hξ (hfη' ▸ hspec.map hf)
      have hξ' : ξ ∈ (Closeds.closure {η}).preimage hf := by
        change f ξ ∈ closure {η}
        rw [hfξ]
        exact subset_closure (Set.mem_singleton η)
      exact hη'.2 hξ' hspec

end Topology

/-! ### Reduced ideals of closed sets -/

section StrictTransform

variable {X : Scheme.{u}}

/-- A reduced ideal sheaf is the reduced ideal of its support. -/
theorem vanishingIdeal_support_of_isReduced (J : X.IdealSheafData) [IsReduced J.subscheme] :
    vanishingIdeal J.support = J := by
  rw [vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]

/-- The reduced ideal of the closure of a point cuts out an integral closed subscheme. -/
theorem isIntegral_subscheme_vanishingIdeal_closure (η : X) :
    IsIntegral (vanishingIdeal (Closeds.closure {η})).subscheme := by
  have := isReduced_subscheme_vanishingIdeal (X := X) (Closeds.closure {η})
  have := irreducibleSpace_subscheme_of_isGenericPoint _
    (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A reduced strict transform with a generic point is the reduced ideal of the closure of that
point. -/
theorem strictTransformSeq_eq_vanishingIdeal_closure (S : BlowUpSequence X) (J : X.IdealSheafData)
    [IsReduced J.subscheme] (i : Fin (S.length + 1)) {ζ : S.stage i}
    (hζ : IsGenericPoint ζ ((S.strictTransformSeq J i).support : Set (S.stage i))) :
    S.strictTransformSeq J i = vanishingIdeal (Closeds.closure {ζ}) := by
  have := isReduced_strictTransformSeq_subscheme S J i
  rw [← vanishingIdeal_support_of_isReduced (S.strictTransformSeq J i)]
  congr 1
  exact SetLike.coe_injective hζ.def.symm

end StrictTransform

/-! ### The components relation along `h` -/

section Components

variable {X X' : Scheme.{u}}

/-- `C'` is the family of the irreducible components of the preimages `h⁻¹(V(c))`, `c ∈ C` — the
reduced ideals of the closures of the generic points of the `h⁻¹(V(c))`: the loop's invariant along
a smooth `h` ([Wlo05, 4.1]). -/
def IsPullbackComponents (h : X' ⟶ X) (C : Finset X.IdealSheafData)
    (C' : Finset X'.IdealSheafData) : Prop :=
  ∀ c', c' ∈ C' ↔ ∃ c ∈ C, ∃ η' ∈ (c.support.preimage h.continuous).genericPoints,
    c' = vanishingIdeal (Closeds.closure {η'})

/-- A component of `h⁻¹(V(I_{closure {η}}))` along a smooth `h` lies over `η`. -/
theorem apply_eq_of_mem_genericPoints_preimage [NoetherianSpace X'] (h : X' ⟶ X) [Smooth h]
    {η : X} {η' : X'} (hη' : η' ∈ ((Closeds.closure {η}).preimage h.continuous).genericPoints) :
    h η' = η := by
  have hgp := mem_genericPoints_of_mem_genericPoints_preimage h.continuous
    h.isOpenMap (Closeds.closure {η}) hη'
  have hmem : h η' ∈ closure {η} := hη'.1
  exact (hgp.2 (subset_closure (Set.mem_singleton η)) (specializes_iff_mem_closure.mpr hmem)).symm

/-- The inverse image of the reduced ideal of a component is contained in the reduced ideal of
each component of its preimage (`V(c') ⊆ h⁻¹(V(c))`). -/
theorem comap_le_of_mem_genericPoints_preimage (h : X' ⟶ X) {η : X} {η' : X'}
    (hη' : η' ∈ ((Closeds.closure {η}).preimage h.continuous).genericPoints) :
    (vanishingIdeal (Closeds.closure {η})).comap h ≤ vanishingIdeal (Closeds.closure {η'}) := by
  have := isReduced_subscheme_vanishingIdeal (X := X') (Closeds.closure {η'})
  refine le_of_support_subset _ _ ?_
  rw [support_comap, support_vanishingIdeal_eq, support_vanishingIdeal_eq]
  have hmem : η' ∈ ((Closeds.closure {η}).preimage h.continuous : Set X') := hη'.1
  exact ((Closeds.closure {η}).preimage h.continuous).isClosed.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr hmem)

/-- The support of `h⁻¹(V(c))` is the union of the components' supports (indexed by their
generic points). -/
theorem coe_support_comap_eq_iUnion (h : X' ⟶ X) (c : X.IdealSheafData) :
    ((c.comap h).support : Set X') =
      ⋃ η' ∈ (c.support.preimage h.continuous).genericPoints,
        ((vanishingIdeal (Closeds.closure {η'})).support : Set X') := by
  rw [support_comap, coe_closeds_eq_iUnion_closure_genericPoints]
  simp only [support_vanishingIdeal_eq, Closeds.coe_closure]

end Components

/-! ### The base case: the components of `V(h^* I)` -/

section Base

variable {k : Type u} [Field k]

/-- The members of `componentIdeals T` are reduced ideals of closures of points. -/
theorem componentIdeals_prime (T : Triple k) :
    ∀ c ∈ componentIdeals T, ∃ η : T.X.left, c = vanishingIdeal (Closeds.closure {η}) := by
  intro c hc
  simp only [componentIdeals, Finset.mem_image, Set.Finite.mem_toFinset] at hc
  obtain ⟨η, -, rfl⟩ := hc
  exact ⟨η, rfl⟩

/-- Along a smooth `h` carrying the pullback data the components of `V(h^* I_Y)` are the
components of the preimages of the components of `V(I_Y)` ([Wlo05, 4.1]). -/
theorem isPullbackComponents_componentIdeals (TX TX' : Triple k)
    (h : TX'.X.left ⟶ TX.X.left) [Smooth h] (hp : TX'.IsPullbackOf TX h) :
    IsPullbackComponents h (componentIdeals TX) (componentIdeals TX') := by
  have := Hironaka.BD.noetherianSpace_triple TX
  have := Hironaka.BD.noetherianSpace_triple TX'
  intro c'
  have hI : TX'.I.support = TX.I.support.preimage h.continuous := by rw [hp.2.1, support_comap]
  simp only [componentIdeals, Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨η', hη', rfl⟩
    rw [hI, mem_genericPoints_preimage_iff h.continuous h.isOpenMap] at hη'
    obtain ⟨η, hη, hη'⟩ := hη'
    refine ⟨_, ⟨η, hη, rfl⟩, η', ?_, rfl⟩
    rwa [support_vanishingIdeal_eq]
  · rintro ⟨c, ⟨η, hη, rfl⟩, η', hη', rfl⟩
    refine ⟨η', ?_, rfl⟩
    rw [hI, mem_genericPoints_preimage_iff h.continuous h.isOpenMap]
    rw [support_vanishingIdeal_eq] at hη'
    exact ⟨η, hη, hη'⟩

end Base

/-! ### The stop rules coincide -/

section StopRule

variable {X X' : Scheme.{u}} (S : BlowUpSequence X) (h : X' ⟶ X)

/-- Downstairs to upstairs (monotonicity): if `V(c') ⊆ h⁻¹(V(c))`, a centre containing the strict
transform of `V(c)` pulls back to a centre containing the strict transform of `V(c')`. -/
theorem centerContains_pullback_of_le [Flat h] {c : X.IdealSheafData} {c' : X'.IdealSheafData}
    (hle : c.comap h ≤ c') {n : ℕ} (hc : CenterContains S c n) :
    CenterContains (S.pullback h) c' n := by
  obtain ⟨hn, hle'⟩ := hc
  have hn' : n < (S.pullback h).length := by rwa [length_pullback]
  refine ⟨hn', ?_⟩
  have e1 : (S.pullback h).center ⟨n, hn'⟩ =
      (S.center ⟨n, hn⟩).comap (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩) :=
    center_pullback_mk S h n hn
  have e2 : (S.pullback h).strictTransformSeq (c.comap h) ⟨n, Nat.lt_succ_of_lt hn'⟩ =
      (S.strictTransformSeq c ⟨n, Nat.lt_succ_of_lt hn⟩).comap
        (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩) :=
    strictTransformSeq_pullback_mk S h c n (Nat.lt_succ_of_lt hn)
  rw [e1]
  exact (comap_mono _ hle').trans (e2.symm.le.trans (strictTransformSeq_mono_mk _ hle n _))

/-- Upstairs to downstairs (the proof of [Kol07, Corollary 22]): before any absorption of `V(c)` or
of the component `V(c')` of its preimage, the generic point of the strict transform of `V(c')` lies
over the generic point of the strict transform of `V(c)`; a centre `h_n⁻¹(Z_n)` containing the
former forces `Z_n` to contain the latter. -/
theorem centerContains_of_centerContains_pullback [IsLocallyNoetherian X]
    [IsLocallyNoetherian X'] (c : X.IdealSheafData) [IsIntegral c.subscheme] {η : X}
    (hη : IsGenericPoint η (c.support : Set X)) (c' : X'.IdealSheafData) [IsReduced c'.subscheme]
    {η' : X'} (hη' : IsGenericPoint η' (c'.support : Set X')) (hηη' : h η' = η) {n : ℕ}
    (hhist : ∀ m < n, ¬ CenterContains S c m)
    (hhist' : ∀ m < n, ¬ CenterContains (S.pullback h) c' m)
    (hc' : CenterContains (S.pullback h) c' n) : CenterContains S c n := by
  obtain ⟨hn', hle'⟩ := hc'
  have hn : n < S.length := by rwa [length_pullback] at hn'
  refine ⟨hn, ?_⟩
  have hred : IsReduced c.subscheme := inferInstance
  obtain ⟨ηn, hgen, -, huniq⟩ := exists_isGenericPoint_strictTransformSeq_mk ‹_› S c hη hred n
    (Nat.lt_succ_of_lt hn) (fun m hm hle => hhist m hm ⟨by omega, hle⟩)
  obtain ⟨ηn', hgen', hmap', -⟩ := exists_isGenericPoint_strictTransformSeq_mk ‹_› (S.pullback h)
    c' hη' ‹_› n (Nat.lt_succ_of_lt hn') (fun m hm hle => hhist' m hm ⟨by omega, hle⟩)
  -- the stage lift carries `ηn'` to `ηn`
  have hcomm : S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩ ηn' = ηn := by
    apply huniq
    have key := congrArg (fun φ : (S.pullback h).stage _ ⟶ X => φ ηn')
      (pullbackStageHom_stageMap_mk S h n (Nat.lt_succ_of_lt hn))
    simp only [Scheme.Hom.comp_apply] at key
    have hmap'' : (S.pullback h).stageMap (S.pullbackStageIdx h ⟨n, Nat.lt_succ_of_lt hn⟩) ηn' =
        η' := hmap'
    rw [hmap'', hηη'] at key
    exact key
  -- `V(X̄'_n) ⊆ V(Z'_n) = h_n⁻¹(V(Z_n))`, so `ηn ∈ V(Z_n)`
  have e1 : (S.pullback h).center ⟨n, hn'⟩ =
      (S.center ⟨n, hn⟩).comap (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩) :=
    center_pullback_mk S h n hn
  rw [e1] at hle'
  have hmem' : ηn' ∈ ((S.center ⟨n, hn⟩).comap
      (S.pullbackStageHom h ⟨n, Nat.lt_succ_of_lt hn⟩)).support :=
    support_antitone hle' hgen'.mem
  rw [mem_support_comap_iff_apply, hcomm] at hmem'
  -- `V(X̄_n) = closure {ηn} ⊆ V(Z_n)`
  have hint : IsIntegral (S.strictTransformSeq c ⟨n, Nat.lt_succ_of_lt hn⟩).subscheme :=
    isIntegral_strictTransformSeq_mk ‹_› S c ‹_› n (Nat.lt_succ_of_lt hn)
      (fun m hm hle => hhist m hm ⟨by omega, hle⟩)
  refine le_of_support_subset _ _ ?_
  rw [← hgen.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hmem') (S.center ⟨n, hn⟩).support.isClosed

/-- **The stop rules coincide** (the proof of [Wlo05, Theorem 4.7.1] along `h`) — for a family `C`
of reduced ideals of irreducible closed sets and `C'` the components of their preimages, if no
member of `C` is absorbed before stage `n`, then no member of `C'` is absorbed before stage `n`,
and at stage `n` a component `V(c')` of `h⁻¹(V(c))` is absorbed by the pulled-back run exactly when
`V(c)` is absorbed by the run. Strong induction on `n`. -/
theorem stopRule_aux [Smooth h] [IsLocallyNoetherian X]
    [NoetherianSpace X'] (C : Finset X.IdealSheafData) (C' : Finset X'.IdealSheafData)
    (hC : ∀ c ∈ C, ∃ η : X, c = vanishingIdeal (Closeds.closure {η}))
    (hCC' : IsPullbackComponents h C C') :
    ∀ n, (∀ m < n, ∀ c ∈ C, ¬ CenterContains S c m) →
      (∀ c' ∈ C', ∀ m < n, ¬ CenterContains (S.pullback h) c' m) ∧
      (∀ c ∈ C, ∀ η' ∈ (c.support.preimage h.continuous).genericPoints,
        (CenterContains (S.pullback h) (vanishingIdeal (Closeds.closure {η'})) n ↔
          CenterContains S c n)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hhist
  have part1 : ∀ c' ∈ C', ∀ m < n, ¬ CenterContains (S.pullback h) c' m := by
    intro c' hc' m hm hcc
    obtain ⟨c, hc, η', hη', rfl⟩ := (hCC' c').mp hc'
    have := (ih m hm (fun m' hm' => hhist m' (hm'.trans hm))).2 c hc η' hη'
    exact hhist m hm c hc (this.mp hcc)
  refine ⟨part1, fun c hc η' hη' => ⟨fun hcc' => ?_, fun hcc => ?_⟩⟩
  · obtain ⟨η, rfl⟩ := hC c hc
    rw [support_vanishingIdeal_eq] at hη'
    have hc'mem : vanishingIdeal (Closeds.closure {η'}) ∈ C' := by
      refine (hCC' _).mpr ⟨_, hc, η', ?_, rfl⟩
      rwa [support_vanishingIdeal_eq]
    have := isIntegral_subscheme_vanishingIdeal_closure η
    have := isReduced_subscheme_vanishingIdeal (X := X') (Closeds.closure {η'})
    exact centerContains_of_centerContains_pullback S h _
      (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η) _
      (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η')
      (apply_eq_of_mem_genericPoints_preimage h hη') (fun m hm => hhist m hm _ hc)
      (part1 _ hc'mem) hcc'
  · obtain ⟨η, rfl⟩ := hC c hc
    rw [support_vanishingIdeal_eq] at hη'
    exact centerContains_pullback_of_le S h (comap_le_of_mem_genericPoints_preimage h hη') hcc

end StopRule

/-! ### Transport to the truncation and to the last-stage lift -/

section Take

variable {X X' : Scheme.{u}}

/-- No absorption of `V(c)` before stage `n` gives the history hypothesis of the generic point
lemma on the truncation `S.take n`. -/
theorem forall_not_center_le_take (S : BlowUpSequence X) (c : X.IdealSheafData) {n : ℕ}
    (hn : n ≤ S.length) (hhist : ∀ m < n, ¬ CenterContains S c m) :
    ∀ m : Fin (S.take n).length,
      ¬ (S.take n).center m ≤ (S.take n).strictTransformSeq c m.castSucc := by
  intro m hle
  have hlen : (S.take n).length = n := length_take_of_le S hn
  have hm : m.val < n := m.2.trans_eq hlen
  exact hhist m.val hm ((centerContains_take_iff S c n m.val hm).mp ⟨m.2, hle⟩)

/-- The last-stage lift lies over `h` ([Kol07, Definition 30, 30.1]). -/
theorem pullbackLastHom_stageMap (Q : BlowUpSequence X) (h : X' ⟶ X) :
    Q.pullbackLastHom h ≫ Q.stageMap (Fin.last _) = (Q.pullback h).stageMap (Fin.last _) ≫ h := by
  rw [stageMap_eq_idx (Q.pullback h) (pullbackStageIdx_last Q h), Category.assoc,
    ← pullbackStageHom_stageMap]
  exact Category.assoc _ _ _

/-- The proof of [Kol07, Corollary 22] on both sides of `h`: for a component `V(I_{closure {η'}})`
of `h⁻¹(closure {η})`, with no absorption of either along the truncated run `Q`, the generic points
`ηQ` and `ηQ'` of the two strict transforms at the last stage exist, the last-stage lift carries
`ηQ'` to `ηQ`, and `ηQ'` lies over `η'`. -/
theorem exists_genericPoints_strictTransformSeq_pullback_last [IsLocallyNoetherian X]
    [NoetherianSpace X'] (Q : BlowUpSequence X) (h : X' ⟶ X) [Smooth h]
    {η : X} {η' : X'} (hη' : η' ∈ ((Closeds.closure {η}).preimage h.continuous).genericPoints)
    (hhist : ∀ m : Fin Q.length,
      ¬ Q.center m ≤ Q.strictTransformSeq (vanishingIdeal (Closeds.closure {η})) m.castSucc)
    (hhist' : ∀ m : Fin (Q.pullback h).length, ¬ (Q.pullback h).center m ≤
      (Q.pullback h).strictTransformSeq (vanishingIdeal (Closeds.closure {η'})) m.castSucc) :
    ∃ (ηQ : Q.stage (Fin.last _)) (ηQ' : (Q.pullback h).stage (Fin.last _)),
      IsGenericPoint ηQ ((Q.strictTransformSeq (vanishingIdeal (Closeds.closure {η}))
        (Fin.last _)).support : Set (Q.stage (Fin.last _))) ∧
      IsGenericPoint ηQ' (((Q.pullback h).strictTransformSeq
        (vanishingIdeal (Closeds.closure {η'})) (Fin.last _)).support :
          Set ((Q.pullback h).stage (Fin.last _))) ∧
      Q.pullbackLastHom h ηQ' = ηQ ∧ (Q.pullback h).stageMap (Fin.last _) ηQ' = η' := by
  have := LocallyOfFiniteType.isLocallyNoetherian h
  have := isReduced_subscheme_vanishingIdeal (X := X) (Closeds.closure {η})
  have := isReduced_subscheme_vanishingIdeal (X := X') (Closeds.closure {η'})
  have hηη' : h η' = η := apply_eq_of_mem_genericPoints_preimage h hη'
  obtain ⟨ηQ, hgenQ, hmapQ, huniqQ⟩ := exists_isGenericPoint_strictTransformSeq Q _
    (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η) (Fin.last _) (fun m _ => hhist m)
  obtain ⟨ηQ', hgenQ', hmapQ', -⟩ := exists_isGenericPoint_strictTransformSeq (Q.pullback h) _
    (Hironaka.BMO.isGenericPoint_support_vanishingIdeal_closure η') (Fin.last _)
    (fun m _ => hhist' m)
  refine ⟨ηQ, ηQ', hgenQ, hgenQ', huniqQ _ ?_, hmapQ'⟩
  have key := congrArg (fun φ : (Q.pullback h).stage (Fin.last _) ⟶ X => φ ηQ')
    (pullbackLastHom_stageMap Q h)
  simp only [Scheme.Hom.comp_apply] at key
  rw [hmapQ', hηη'] at key
  exact key

end Take

end Hironaka.Resolution
