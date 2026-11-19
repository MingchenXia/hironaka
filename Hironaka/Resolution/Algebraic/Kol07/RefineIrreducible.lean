/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.RefineFamily
public import Hironaka.Resolution.Algebraic.Kol07.Componentwise
public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransport
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUp.ProductCenter
import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.ExceptionalDivisor
import Hironaka.Scheme.Smooth.ExceptionalModel
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Refinement of a blow-up sequence to irreducible centers

Clause (i) of Hironaka's Main Theorem II [Hir64, Main Theorem II] asks for irreducible centers,
while Kollár's smooth centers [Kol07, Definition 66] may be disconnected. This module shows that a
smooth blow-up sequence of order `d` refines to one with regular irreducible centers, of length
`∑ᵢ rᵢ` (`rᵢ` the number of irreducible components of the `i`-th center), with the same composite,
the same final weak transform `J_r` and the same final boundary `E_r`
(`IsOrderSeq.exists_refineIrreducible`). The refinement is built stage by stage: the center `Z_0`
is replaced by its componentwise sequence
(`Hironaka/Resolution/Algebraic/Kol07/ComponentwiseBlowUp.lean`, `ComponentwiseTransforms.lean`),
and the refinement of the tail, a sequence on `B_{Z_0} X` by the induction hypothesis, is carried
across the canonical isomorphism of the end results (`pullback` along an isomorphism) and
concatenated (`Hironaka/Scheme/BlowUpSequence/ConcatApi.lean`). The simple normal crossing
conditions are transported through the subdivision relation of
`Hironaka/Resolution/Algebraic/Kol07/RefineFamily.lean`.

The module also holds the transport lemmas along isomorphisms that the induction uses (the stage
lifts of an isomorphism are isomorphisms, Hironaka's boundaries pull back along isomorphisms), and
the subdivision of the total transforms along a componentwise sequence
(`subdivides_totalTransformSeq_ofCenters_last`), proved locally on the open sets missing all
components but one and glued as in the proof of [Kol07, Proposition 37].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The stage lifts of an isomorphism along a blow-up sequence are isomorphisms (the cartesian
squares `isPullback_pullbackStageHom`, isomorphisms being stable under base change). -/
theorem isIso_pullbackStageHom_of_isIso (S : BlowUpSequence X) (e : Y ⟶ X) [IsIso e]
    (i : Fin (S.length + 1)) : IsIso (S.pullbackStageHom e i) :=
  (MorphismProperty.isomorphisms.iff _).mp
    (property_of_isPullback (MorphismProperty.isomorphisms Scheme.{u})
      (isPullback_pullbackStageHom S e i) ((MorphismProperty.isomorphisms.iff _).mpr inferInstance))

/-- Hironaka's boundaries pull back along an isomorphism of the base: `red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`
is a vanishing ideal, and the inverse image of a vanishing ideal along an isomorphism is the
vanishing ideal of the preimage (`comap_vanishingIdeal_of_isIso`), the squares of `blowUpMap`
(`blowUpMap_π`) matching the preimages. -/
theorem boundarySeq_pullback_of_isIso (S : BlowUpSequence X) (e : Y ⟶ X) [IsIso e]
    (E₀ : X.IdealSheafData) (i : Fin (S.length + 1)) :
    (S.pullback e).boundarySeq (E₀.comap e) (S.pullbackStageIdx e i) =
      (S.boundarySeq E₀ i).comap (S.pullbackStageHom e i) := by
  induction S generalizing Y with
  | nil X =>
    change E₀.comap e = E₀.comap ((nil X).pullbackStageHom e i)
    rfl
  | cons X D rest ih =>
    rcases i with ⟨_ | j, hj⟩
    · change E₀.comap e = E₀.comap ((cons X D rest).pullbackStageHom e 0)
      rfl
    · have hiso : IsIso (Scheme.Hom.blowUpMap e D) :=
        isIso_blowUpMap_of_isIso e D
      have hsq : ⇑D.blowUpπ ∘ ⇑(Scheme.Hom.blowUpMap e D) = ⇑e ∘
          ⇑(D.comap e).blowUpπ :=
        congrArg (fun φ : (D.comap e).blowUp ⟶ X => (⇑φ : (D.comap e).blowUp → X))
          (blowUpMap_π e D)
      have hred : (E₀.comap e).reducedTransform (D.comap e) =
          (E₀.reducedTransform D).comap (Scheme.Hom.blowUpMap e D) := by
        unfold reducedTransform
        rw [comap_vanishingIdeal_of_isIso]
        congr 1
        rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
        refine SetLike.coe_injective ?_
        change (D.comap e).blowUpπ ⁻¹' (e ⁻¹' (E₀.support : Set X)) ∪
            (D.comap e).blowUpπ ⁻¹' (e ⁻¹' (D.support : Set X)) =
          (Scheme.Hom.blowUpMap e D) ⁻¹' (D.blowUpπ ⁻¹' (E₀.support : Set X) ∪
            D.blowUpπ ⁻¹' (D.support : Set X))
        rw [Set.preimage_union, ← Set.preimage_comp, ← Set.preimage_comp, ← Set.preimage_comp,
          ← Set.preimage_comp, hsq]
      change (rest.pullback (Scheme.Hom.blowUpMap e D)).boundarySeq
          ((E₀.comap e).reducedTransform (D.comap e)) ⟨j, _⟩ =
        (rest.boundarySeq (E₀.reducedTransform D) ⟨j, _⟩).comap
          (rest.pullbackStageHom (Scheme.Hom.blowUpMap e D) ⟨j, _⟩)
      rw [hred]
      exact ih (Scheme.Hom.blowUpMap e D) (E₀.reducedTransform D)
          ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-! ### Total transforms along the componentwise sequence -/

/-- A componentwise equality of families along an injection of index sets is a subdivision. -/
theorem subdivides_of_component_eq {F G : DivisorFamily X} (e : F.ι → G.ι)
    (he : Function.Injective e) (hc : ∀ j, F.component j = G.component (e j)) :
    F.Subdivides G := fun _ =>
  ⟨fun j => some (e j), fun _ _ _ _ h => he (Option.some_injective _ h),
    fun j _ => ⟨e j, rfl, by rw [hc j]⟩⟩

/-- `((J ∘ ψ) ∘ π : K^∞) = (J ∘ (π ≫ ψ) : K^∞)` (`comap_comp`). -/
theorem strictTransformAlong_comap_left {Y B : Scheme.{u}} (J : X.IdealSheafData) (ψ : Y ⟶ X)
    (π : B ⟶ Y) (K : B.IdealSheafData) :
    (J.comap ψ).strictTransformAlong π K = J.strictTransformAlong (π ≫ ψ) K := by
  rw [strictTransformAlong, strictTransformAlong, ← comap_comp]

/-- `((J : K^∞) ∘ ψ) = ((J ∘ ψ) : (K ∘ ψ)^∞)` along a flat `ψ` (`saturate_comap_of_flat` with
`comap_comp`). -/
theorem comap_strictTransformAlong_of_flat {B B' : Scheme.{u}} (ψ : B' ⟶ B) [Flat ψ]
    (π : B ⟶ X) {K : B.IdealSheafData} (hK : K.IsInvertible) (J : X.IdealSheafData) :
    (J.strictTransformAlong π K).comap ψ = J.strictTransformAlong (ψ ≫ π) (K.comap ψ) := by
  rw [strictTransformAlong, strictTransformAlong, saturate_comap_of_flat ψ _ hK, ← comap_comp]

/-- The total transform along `π` of the inverse image of a family along `ψ` has the components of
the total transform along `π ≫ ψ` (`strictTransformAlong_comap_left`); the distinguished divisor
is unchanged. (The proof goes through explicit intermediate terms: the kernel must never compare
two total transforms argumentwise.) -/
theorem totalTransformAlong_comap_component {Y B : Scheme.{u}} (E : DivisorFamily X) (ψ : Y ⟶ X)
    (π : B ⟶ Y) (K : B.IdealSheafData) (i : E.ι ⊕ₗ PUnit.{u + 1}) :
    ((E.comap ψ).totalTransformAlong π K).component i =
      (E.totalTransformAlong (π ≫ ψ) K).component i := by
  rcases i with j | u
  · have h1 : ((E.comap ψ).totalTransformAlong π K).component (Sum.inl j) =
        ((E.comap ψ).component j).strictTransformAlong π K := rfl
    have h2 : (E.comap ψ).component j = (E.component j).comap ψ := rfl
    have h3 : (E.component j).strictTransformAlong (π ≫ ψ) K =
        (E.totalTransformAlong (π ≫ ψ) K).component (Sum.inl j) := rfl
    exact h1.trans ((congrArg ((·.strictTransformAlong π K)) h2).trans
      ((strictTransformAlong_comap_left (E.component j) ψ π K).trans h3))
  · have h1 : ((E.comap ψ).totalTransformAlong π K).component (Sum.inr u) = K := rfl
    have h3 : K = (E.totalTransformAlong (π ≫ ψ) K).component (Sum.inr u) := rfl
    exact h1.trans h3

theorem subdivides_totalTransformAlong_comap {Y B : Scheme.{u}} (E : DivisorFamily X) (ψ : Y ⟶ X)
    (π : B ⟶ Y) (K : B.IdealSheafData) :
    ((E.comap ψ).totalTransformAlong π K).Subdivides (E.totalTransformAlong (π ≫ ψ) K) :=
  subdivides_of_component_eq (fun i : E.ι ⊕ₗ PUnit.{u + 1} => i) (fun _ _ h => h)
    (totalTransformAlong_comap_component E ψ π K)

theorem subdivides_totalTransformAlong_comap' {Y B : Scheme.{u}} (E : DivisorFamily X) (ψ : Y ⟶ X)
    (π : B ⟶ Y) (K : B.IdealSheafData) :
    (E.totalTransformAlong (π ≫ ψ) K).Subdivides ((E.comap ψ).totalTransformAlong π K) :=
  subdivides_of_component_eq (fun i : E.ι ⊕ₗ PUnit.{u + 1} => i) (fun _ _ h => h)
    (fun i => (totalTransformAlong_comap_component E ψ π K i).symm)

/-- Along a flat `ψ` the inverse image of a total transform along `π` with invertible distinguished
divisor `K` has the components of the total transform along `ψ ≫ π` with distinguished divisor
`K.comap ψ` (`comap_strictTransformAlong_of_flat`). -/
theorem comap_totalTransformAlong_component_of_flat {B B' : Scheme.{u}} (ψ : B' ⟶ B) [Flat ψ]
    (E : DivisorFamily X) (π : B ⟶ X) {K : B.IdealSheafData} (hK : K.IsInvertible)
    (i : E.ι ⊕ₗ PUnit.{u + 1}) :
    ((E.totalTransformAlong π K).comap ψ).component i =
      (E.totalTransformAlong (ψ ≫ π) (K.comap ψ)).component i := by
  rcases i with j | u
  · have h1 : ((E.totalTransformAlong π K).comap ψ).component (Sum.inl j) =
        ((E.totalTransformAlong π K).component (Sum.inl j)).comap ψ := rfl
    have h2 : (E.totalTransformAlong π K).component (Sum.inl j) =
        (E.component j).strictTransformAlong π K := rfl
    have h3 : (E.component j).strictTransformAlong (ψ ≫ π) (K.comap ψ) =
        (E.totalTransformAlong (ψ ≫ π) (K.comap ψ)).component (Sum.inl j) := rfl
    exact h1.trans ((congrArg (fun I : B.IdealSheafData => I.comap ψ) h2).trans
      ((comap_strictTransformAlong_of_flat ψ π hK (E.component j)).trans h3))
  · have h1 : ((E.totalTransformAlong π K).comap ψ).component (Sum.inr u) =
        ((E.totalTransformAlong π K).component (Sum.inr u)).comap ψ := rfl
    have h2 : (E.totalTransformAlong π K).component (Sum.inr u) = K := rfl
    have h3 : K.comap ψ = (E.totalTransformAlong (ψ ≫ π) (K.comap ψ)).component (Sum.inr u) :=
      rfl
    exact h1.trans ((congrArg (fun I : B.IdealSheafData => I.comap ψ) h2).trans h3)

theorem subdivides_comap_totalTransformAlong_of_flat {B B' : Scheme.{u}} (ψ : B' ⟶ B) [Flat ψ]
    (E : DivisorFamily X) (π : B ⟶ X) {K : B.IdealSheafData} (hK : K.IsInvertible) :
    ((E.totalTransformAlong π K).comap ψ).Subdivides
      (E.totalTransformAlong (ψ ≫ π) (K.comap ψ)) :=
  subdivides_of_component_eq (fun i : E.ι ⊕ₗ PUnit.{u + 1} => i) (fun _ _ h => h)
    (comap_totalTransformAlong_component_of_flat ψ E π hK)

theorem subdivides_comap_totalTransformAlong_of_flat' {B B' : Scheme.{u}} (ψ : B' ⟶ B) [Flat ψ]
    (E : DivisorFamily X) (π : B ⟶ X) {K : B.IdealSheafData} (hK : K.IsInvertible) :
    (E.totalTransformAlong (ψ ≫ π) (K.comap ψ)).Subdivides
      ((E.totalTransformAlong π K).comap ψ) :=
  subdivides_of_component_eq (fun i : E.ι ⊕ₗ PUnit.{u + 1} => i) (fun _ _ h => h)
    (fun i => (comap_totalTransformAlong_component_of_flat ψ E π hK i).symm)

/-- The total transform under the blow-up of the unit ideal subdivides the inverse image of the
family: the exceptional divisor is the unit ideal and passes through no point, and every strict
transform has the stalk of the inverse image (`stalkIdeal_strictTransformAlong_of_notMem_support`,
every point lying off the exceptional divisor). -/
theorem subdivides_totalTransform_of_eq_top (F : DivisorFamily X) {D : X.IdealSheafData}
    (hD : D = ⊤) : (F.totalTransform D).Subdivides (F.comap D.blowUpπ) := by
  subst hD
  intro y
  have hexc : ∀ y' : (⊤ : X.IdealSheafData).blowUp, y' ∉ (⊤ :
      X.IdealSheafData).exceptionalDivisor.support := by
    intro y' hy'
    rw [exceptionalDivisor, comap_top] at hy'
    exact notMem_support_of_stalkIdeal_eq_top (stalkIdeal_top y') hy'
  have hstalk : ∀ j : F.ι, ((F.component j).strictTransform ⊤).stalkIdeal y =
      ((F.component j).comap (⊤ : X.IdealSheafData).blowUpπ).stalkIdeal y := by
    intro j
    rw [stalkIdeal_comap]
    exact stalkIdeal_strictTransformAlong_of_notMem_support ⊤ (F.component j) (hexc y)
  refine ⟨fun j' => Sum.elim some (fun _ => none) (ofLex j'), ?_, ?_⟩
  · rintro (j | u) (j' | u') hj hj' heq
    · exact congrArg (fun j => (toLex (Sum.inl j) : (F.totalTransform ⊤).ι))
        (Option.some_injective _ heq)
    · exact absurd hj' (hexc y)
    · exact absurd hj (hexc y)
    · exact absurd hj (hexc y)
  · rintro (j | u) hj
    · exact ⟨j, rfl, hstalk j⟩
    · exact absurd hj (hexc y)

/-- A family subdivides the inverse image, along a section `e` of a blow-up `π` of the unit ideal
(an isomorphism), of its total transform along `π`: the strict transforms come back to the
components (`saturate_top`) and the exceptional divisor is the unit ideal. -/
theorem subdivides_totalTransformAlong_top_comap (G : DivisorFamily X) {B : Scheme.{u}}
    (π : B ⟶ X) (e : X ⟶ B) (he : e ≫ π = 𝟙 X) :
    G.Subdivides ((G.totalTransformAlong π ⊤).comap e) := by
  have hcomp : ∀ i, ((G.component i).strictTransformAlong π (⊤ : B.IdealSheafData)).comap e =
      G.component i := fun i => by
    rw [strictTransformAlong, saturate_top, ← comap_comp, he, comap_id]
  intro x
  refine ⟨fun i => some (toLex (Sum.inl i)), fun i i' _ _ heq => ?_, fun i _ => ?_⟩
  · exact Sum.inl.inj (Option.some_injective _ heq)
  · refine ⟨toLex (Sum.inl i), rfl, ?_⟩
    change (G.component i).stalkIdeal x =
      (((G.component i).strictTransformAlong π ⊤).comap e).stalkIdeal x
    rw [hcomp]

/-- Along a componentwise sequence of unit centers (isomorphisms), the total transform of `F` at
the end subdivides the inverse image of `F` under the composite: each step adds a unit exceptional
divisor (`subdivides_totalTransform_of_eq_top`). -/
theorem subdivides_totalTransformSeq_ofCenters_last_of_forall_top (c : ℕ) :
    ∀ {X : Scheme.{u}} (D : Fin c → X.IdealSheafData), (∀ l, D l = ⊤) →
      ∀ F : DivisorFamily X,
        ((ofCenters c D).totalTransformSeq F (Fin.last _)).Subdivides
          (F.comap (ofCenters c D).composite) := by
  induction c with
  | zero =>
    intro X D _ F
    change F.Subdivides (F.comap (𝟙 X))
    rw [DivisorFamily.comap_id]
    exact subdivides_refl F
  | succ c ih =>
    intro X D hD F
    have h1 := ih (fun l => (D l.succ).comap (D 0).blowUpπ)
      (fun l => by rw [hD l.succ, comap_top]) (F.totalTransform (D 0))
    have h0 := subdivides_comap (subdivides_totalTransform_of_eq_top F (hD 0))
      (ofCenters c fun l => (D l.succ).comap (D 0).blowUpπ).composite
    rw [← DivisorFamily.comap_comp] at h0
    exact subdivides_trans h1 h0

/-- Along a componentwise sequence with a single non-unit center `D k₀` (the restriction of the
componentwise sequence of `⊔ Z_k` to the open set missing the other components), the total
transform of a family `F` subdividing `G` subdivides the inverse image, along the canonical map `e`
to any blow-up `π` of `∏ D`, of the total transform of `G` along `π`. By induction on the length: a
unit center before `k₀` is an isomorphism, absorbed into `π` (`IsBlowUp.comp_iso`); at `k₀` the
canonical map is the composite of the remaining unit blow-ups
(`subdivides_totalTransformSeq_ofCenters_last_of_forall_top`), by uniqueness of the lift
(`IsBlowUp.exists_iso`). Stated for a variable sequence `S` equal to the componentwise sequence and
a variable last index `i`, so that it applies to pulled-back sequences. -/
theorem subdivides_totalTransformSeq_of_single (c : ℕ) :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (D : Fin c → X.IdealSheafData),
      S = ofCenters c D → ∀ (k₀ : Fin c), (∀ l, l ≠ k₀ → D l = ⊤) →
      ∀ {F G : DivisorFamily X}, F.Subdivides G → ∀ {B : Scheme.{u}} (π : B ⟶ X),
      IsBlowUp (∏ l, D l) π → ∀ (i : Fin (S.length + 1)), i.val = S.length →
      ∀ (e : S.stage i ⟶ B), e ≫ π = S.stageMap i →
      (S.totalTransformSeq F i).Subdivides
        ((G.totalTransformAlong π ((∏ l, D l).comap π)).comap e) := by
  induction c with
  | zero =>
    intro X S D _ k₀
    exact k₀.elim0
  | succ c ih =>
    intro X S D hS k₀ htop F G hFG B π hπ i hi e he
    subst hS
    have hi' : i = Fin.last _ := Fin.ext hi
    subst hi'
    set tail := ofCenters c fun l => (D l.succ).comap (D 0).blowUpπ with htail
    revert e he
    change ∀ (e : tail.last ⟶ B), e ≫ π = tail.composite ≫ (D 0).blowUpπ →
      (tail.totalTransformSeq (F.totalTransform (D 0)) (Fin.last _)).Subdivides
        ((G.totalTransformAlong π ((∏ l, D l).comap π)).comap e)
    intro e he
    induction k₀ using Fin.cases with
    | zero =>
      have hD' : ∀ l : Fin c, (D l.succ).comap (D 0).blowUpπ = ⊤ := fun l => by
        rw [htop l.succ (Fin.succ_ne_zero l), comap_top]
      have hprod : ∏ l, D l = D 0 := by
        rw [Fin.prod_univ_succ, Finset.prod_eq_one fun l _ => htop l.succ (Fin.succ_ne_zero l),
          mul_one]
      have hπ₀ : IsBlowUp (∏ l, D l) (D 0).blowUpπ := by
        rw [hprod]; exact blowUp.isBlowUp (D 0)
      obtain ⟨ψ, hψ, -⟩ := hπ₀.exists_iso hπ
      have hadm : ((∏ l, D l).comap (tail.composite ≫ (D 0).blowUpπ)).IsInvertible :=
        (isBlowUp_composite_ofCenters (c + 1) D).admissible
      have hcomp : (tail.composite ≫ ψ.hom) ≫ π = tail.composite ≫ (D 0).blowUpπ := by
        rw [Category.assoc, hψ]
      have he' : e = tail.composite ≫ ψ.hom := by
        obtain ⟨g, -, huniq⟩ := hπ.existsUnique_lift (tail.composite ≫ (D 0).blowUpπ) hadm
        exact (huniq e he).trans (huniq _ hcomp).symm
      have hK0 : ((∏ l, D l).comap π).comap ψ.hom = (D 0).comap (D 0).blowUpπ := by
        rw [← comap_comp, hψ, hprod]
      have hlast := subdivides_comap_totalTransformAlong_of_flat' ψ.hom G π hπ.admissible
      rw [hK0, hψ] at hlast
      have h1 := subdivides_totalTransformSeq_ofCenters_last_of_forall_top c _ hD'
        (F.totalTransform (D 0))
      have hfinal := subdivides_trans h1 (subdivides_trans
        (subdivides_comap (subdivides_totalTransform hFG (D 0)) tail.composite)
        (subdivides_comap hlast tail.composite))
      rw [← DivisorFamily.comap_comp] at hfinal
      rw [he']
      exact hfinal
    | succ k =>
      have hD0 : D 0 = ⊤ := htop 0 (Fin.succ_ne_zero k).symm
      have hD' : ∀ l : Fin c, l ≠ k → (D l.succ).comap (D 0).blowUpπ = ⊤ :=
          fun l hl => by
        rw [htop l.succ fun h => hl (Fin.succ_injective _ h), comap_top]
      have hiso : IsIso (D 0).blowUpπ := by rw [hD0]; exact blowUp.isIso_π_top
      have hprod : ∏ l, D l = ∏ l : Fin c, D l.succ := by rw [Fin.prod_univ_succ, hD0, top_mul]
      have hπW : IsBlowUp (∏ l : Fin c, D l.succ) π := by rw [← hprod]; exact hπ
      have hπ' : IsBlowUp (∏ l : Fin c, (D l.succ).comap (D 0).blowUpπ)
          (π ≫ inv (D 0).blowUpπ) := by
        have h := hπW.comp_iso (asIso (D 0).blowUpπ).symm
        rw [Iso.symm_inv, asIso_hom, Iso.symm_hom, asIso_inv, comap_finset_prod] at h
        exact h
      have he' : e ≫ (π ≫ inv (D 0).blowUpπ) = tail.composite := by
        rw [← Category.assoc, he, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have h := ih tail _ htail k hD' (subdivides_trans (subdivides_totalTransform_of_eq_top F hD0)
        (subdivides_comap hFG (D 0).blowUpπ)) (π ≫ inv (D 0).blowUpπ) hπ'
            (Fin.last _) rfl
        e he'
      have hm : (π ≫ inv (D 0).blowUpπ) ≫ (D 0).blowUpπ = π := by
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      have hK : (∏ l : Fin c, (D l.succ).comap (D 0).blowUpπ).comap
          (π ≫ inv (D 0).blowUpπ) = (∏ l, D l).comap π := by
        rw [← comap_finset_prod, ← comap_comp, hm, ← hprod]
      rw [hK] at h
      have hcoarse := subdivides_totalTransformAlong_comap G (D 0).blowUpπ
        (π ≫ inv (D 0).blowUpπ) ((∏ l, D l).comap π)
      rw [hm] at hcoarse
      exact subdivides_trans h (subdivides_comap hcoarse e)

/-- The case of at least one center of `subdivides_totalTransformSeq_ofCenters_last`, by the cover
argument on the open sets `X ∖ ⋃_{l ≠ k} V(D l)`. -/
theorem subdivides_totalTransformSeq_ofCenters_last_succ (c : ℕ)
    (D : Fin (c + 1) → X.IdealSheafData)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support) {F G : DivisorFamily X}
    (hFG : F.Subdivides G) {B : Scheme.{u}} (π : B ⟶ X) (hπ : IsBlowUp (∏ l, D l) π)
    (e : (ofCenters (c + 1) D).last ⟶ B) (he : e ≫ π = (ofCenters (c + 1) D).composite) :
    ((ofCenters (c + 1) D).totalTransformSeq F (Fin.last _)).Subdivides
      ((G.totalTransformAlong π ((∏ l, D l).comap π)).comap e) := by
  classical
  revert e
  change ∀ (e : (ofCenters (c + 1) D).stage (Fin.last _) ⟶ B),
    e ≫ π = (ofCenters (c + 1) D).stageMap (Fin.last _) →
      ((ofCenters (c + 1) D).totalTransformSeq F (Fin.last _)).Subdivides
        ((G.totalTransformAlong π ((∏ l, D l).comap π)).comap e)
  intro e he
  have hcov : ∀ y : (ofCenters (c + 1) D).stage (Fin.last _), ∃ (k : Fin (c + 1))
      (w : ((ofCenters (c + 1) D).pullback (complOthers D k).ι).stage
        ((ofCenters (c + 1) D).pullbackStageIdx (complOthers D k).ι (Fin.last _))),
      (ofCenters (c + 1) D).pullbackStageHom (complOthers D k).ι (Fin.last _) w = y := by
    intro y
    obtain ⟨k, hk⟩ : ∃ k : Fin (c + 1),
        (ofCenters (c + 1) D).stageMap (Fin.last _) y ∈ complOthers D k := by
      by_cases hx : ∃ k, (ofCenters (c + 1) D).stageMap (Fin.last _) y ∈ (D k).support
      · obtain ⟨k, hk⟩ := hx
        refine ⟨k, (mem_complOthers_iff D k _).mpr fun l hl hxl => ?_⟩
        have this : Disjoint (D l).support (D k).support := hdisj hl
        rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot] at this
        exact Set.eq_empty_iff_forall_notMem.mp this _ ⟨hxl, hk⟩
      · exact ⟨0, (mem_complOthers_iff D 0 _).mpr fun l _ hxl => hx ⟨l, hxl⟩⟩
    have hy : y ∈ Set.range
        ((ofCenters (c + 1) D).pullbackStageHom (complOthers D k).ι (Fin.last _)) := by
      rw [range_pullbackStageHom, Set.mem_preimage, Scheme.Opens.range_ι]
      exact hk
    obtain ⟨w, hw⟩ := hy
    exact ⟨k, w, hw⟩
  have hoi : ∀ k : Fin (c + 1), IsOpenImmersion
      ((ofCenters (c + 1) D).pullbackStageHom (complOthers D k).ι (Fin.last _)) := fun k =>
    property_of_isPullback (@IsOpenImmersion)
      (isPullback_pullbackStageHom (ofCenters (c + 1) D) (complOthers D k).ι (Fin.last _))
      inferInstance
  refine subdivides_of_cover (fun k : Fin (c + 1) =>
    (ofCenters (c + 1) D).pullbackStageHom (complOthers D k).ι (Fin.last _)) hcov fun k => ?_
  set ι := (complOthers D k).ι with hι
  rw [← totalTransformSeq_pullback (ofCenters (c + 1) D) ι F (Fin.last _),
    ← DivisorFamily.comap_comp]
  -- the canonical maps to the blow-up of the restricted center
  have hadm0 : ((∏ l, D l).comap ((ofCenters (c + 1) D).stageMap
      (Fin.last (ofCenters (c + 1) D).length))).IsInvertible :=
    (isBlowUp_composite_ofCenters _ D).admissible
  have hadm1 : ((∏ l, D l).comap ((ofCenters (c + 1) D).pullbackStageHom ι (Fin.last _) ≫
      (ofCenters (c + 1) D).stageMap (Fin.last (ofCenters (c + 1) D).length))).IsInvertible := by
    rw [comap_comp]; exact IsInvertible.comap_of_isOpenImmersion _ hadm0
  have hsq : (ofCenters (c + 1) D).pullbackStageHom ι (Fin.last _) ≫
      (ofCenters (c + 1) D).stageMap (Fin.last (ofCenters (c + 1) D).length) =
      ((ofCenters (c + 1) D).pullback ι).stageMap
        ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)) ≫ ι :=
    pullbackStageHom_stageMap (ofCenters (c + 1) D) ι (Fin.last _)
  have hadm2 : (((∏ l, D l).comap ι).comap (((ofCenters (c + 1) D).pullback ι).stageMap
      ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)))).IsInvertible := by
    rw [← comap_comp, ← hsq]; exact hadm1
  obtain ⟨φ, hφ, -⟩ := (blowUp.isBlowUp (∏ l, D l)).exists_iso hπ
  let m : IdealSheafData.blowUp ((∏ l, D l).comap ι) ⟶ B := Hom.blowUpMap ι (∏ l, D l) ≫ φ.hom
  have hflat : Flat m :=
    inferInstanceAs (Flat (Hom.blowUpMap ι (∏ l, D l) ≫ φ.hom))
  have hm : m ≫ π = IdealSheafData.blowUpπ ((∏ l, D l).comap ι) ≫ ι := by
    simp only [m, Category.assoc, hφ, blowUpMap_π]
  let ek : ((ofCenters (c + 1) D).pullback ι).stage
      ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)) ⟶
          IdealSheafData.blowUp ((∏ l, D l).comap ι) :=
    blowUp.lift _ _ hadm2
  have hek : ek ≫ IdealSheafData.blowUpπ ((∏ l, D l).comap ι) = ((ofCenters
      (c + 1) D).pullback ι).stageMap
      ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)) := blowUp.lift_π _ _ hadm2
  have huniq : (ofCenters (c + 1) D).pullbackStageHom ι (Fin.last _) ≫ e = ek ≫ m := by
    obtain ⟨g, -, hg⟩ := hπ.existsUnique_lift
      (((ofCenters (c + 1) D).pullback ι).stageMap
        ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)) ≫ ι) (by rw [← hsq]; exact hadm1)
    have h₁ : ((ofCenters (c + 1) D).pullbackStageHom ι (Fin.last _) ≫ e) ≫ π =
        ((ofCenters (c + 1) D).pullback ι).stageMap
          ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)) ≫ ι := by
      rw [Category.assoc, he, hsq]
    have h₂ : (ek ≫ m) ≫ π = ((ofCenters (c + 1) D).pullback ι).stageMap
        ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _)) ≫ ι := by
      rw [Category.assoc, hm, ← Category.assoc, hek]
    exact (hg _ h₁).trans (hg _ h₂).symm
  rw [huniq, DivisorFamily.comap_comp]
  have hK : ((∏ l, D l).comap π).comap m =
      (∏ l, (D l).comap ι).comap (IdealSheafData.blowUpπ ((∏ l, D l).comap ι)) := by
    rw [← comap_comp, hm, comap_comp, comap_finset_prod]
  have hc1 := subdivides_comap_totalTransformAlong_of_flat' m G π hπ.admissible
  rw [hm, hK] at hc1
  have hc2 := subdivides_totalTransformAlong_comap G ι (IdealSheafData.blowUpπ ((∏ l, D l).comap ι))
    ((∏ l, (D l).comap ι).comap (IdealSheafData.blowUpπ ((∏ l, D l).comap ι)))
  have hloc := subdivides_totalTransformSeq_of_single (c + 1) ((ofCenters (c + 1) D).pullback ι)
    (fun l => (D l).comap ι) (pullback_ofCenters (c + 1) D ι) k
    (fun l hl => comap_ι_eq_top_of_disjoint (D l) (complOthers D k)
      fun x hx => (mem_complOthers_iff D k x).mp hx l hl)
    (subdivides_comap hFG ι) (IdealSheafData.blowUpπ ((∏ l, D l).comap ι))
    (by rw [← comap_finset_prod]; exact blowUp.isBlowUp _)
    ((ofCenters (c + 1) D).pullbackStageIdx ι (Fin.last _))
    (congrArg Fin.val (pullbackStageIdx_last (ofCenters (c + 1) D) ι)) ek hek
  exact subdivides_trans hloc (subdivides_comap (subdivides_trans hc2 hc1) ek)

/-- Along the componentwise sequence of pairwise disjoint centers `D`, the total transform at the
end of a family `F` subdividing `G` subdivides the inverse image, under the canonical map `e` to
any blow-up `π` of `∏ D`, of the total transform of `G` along `π`. The relation is local
(`subdivides_of_cover`), and the sequence pulls back along open immersions as in [Kol07, 30.1]; on
the open set `X ∖ ⋃_{l ≠ k} V(D l)` only the center `D k` survives (`comap_ι_eq_top_of_disjoint`),
the pulled-back sequence is the componentwise sequence of the restricted centers
(`pullback_ofCenters`), its total transforms are the inverse images of those of `X`
(`totalTransformSeq_pullback`), and the blow-up of the restricted center maps to `B` by the open
immersion `blowUpMap` followed by the canonical isomorphism, through which the single-center case
`subdivides_totalTransformSeq_of_single` applies. -/
theorem subdivides_totalTransformSeq_ofCenters_last (c : ℕ) (D : Fin c → X.IdealSheafData)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support) {F G : DivisorFamily X}
    (hFG : F.Subdivides G) {B : Scheme.{u}} (π : B ⟶ X) (hπ : IsBlowUp (∏ l, D l) π)
    (e : (ofCenters c D).last ⟶ B) (he : e ≫ π = (ofCenters c D).composite) :
    ((ofCenters c D).totalTransformSeq F (Fin.last _)).Subdivides
      ((G.totalTransformAlong π ((∏ l, D l).comap π)).comap e) := by
  cases c with
  | zero =>
    have hprod : ∏ l : Fin 0, D l = ⊤ := by rw [Finset.univ_eq_empty, Finset.prod_empty]; rfl
    rw [hprod, comap_top]
    exact subdivides_trans hFG (subdivides_totalTransformAlong_top_comap G π e he)
  | succ c => exact subdivides_totalTransformSeq_ofCenters_last_succ c D hdisj hFG π hπ e he

/-! ### Transport along isomorphisms and along equal indices -/

/-- The stage map at an index equal to another one, through the equality of the stages. -/
theorem stageMap_congr_idx (S : BlowUpSequence X) {i j : Fin (S.length + 1)} (h : i = j) :
    S.stageMap i = eqToHom (congrArg S.stage h) ≫ S.stageMap j := by
  subst h; simp

/-- The composite as the stage map at an index equal to the last one. -/
theorem composite_congr_idx (S : BlowUpSequence X) {j : Fin (S.length + 1)}
    (h : Fin.last S.length = j) :
    S.composite = eqToHom (congrArg S.stage h) ≫ S.stageMap j :=
  stageMap_congr_idx S h

theorem weakTransformSeq_congr_idx (S : BlowUpSequence X) (J : X.IdealSheafData)
    {i j : Fin (S.length + 1)} (h : i = j) :
    S.weakTransformSeq J i = (S.weakTransformSeq J j).comap (eqToHom (congrArg S.stage h)) := by
  subst h; rw [eqToHom_refl, comap_id]

theorem boundarySeq_congr_idx (S : BlowUpSequence X) (E₀ : X.IdealSheafData)
    {i j : Fin (S.length + 1)} (h : i = j) :
    S.boundarySeq E₀ i = (S.boundarySeq E₀ j).comap (eqToHom (congrArg S.stage h)) := by
  subst h; rw [eqToHom_refl, comap_id]

/-- The closed subscheme of the inverse image of `Z` along an isomorphism is irreducible when
`V(Z)` is (the isomorphism `V(Z ∘ e) ≅ V(Z)`, `isIso_subschemeMap_comap_of_isIso`). -/
theorem irreducibleSpace_subscheme_comap_of_isIso (e : Y ⟶ X) [IsIso e] (Z : X.IdealSheafData)
    (hZ : IrreducibleSpace Z.subscheme) : IrreducibleSpace (Z.comap e).subscheme := by
  have := isIso_subschemeMap_comap_of_isIso e Z
  exact (Homeomorph.irreducibleSpace_iff (Scheme.homeoOfIso (asIso
    (Scheme.IdealSheafData.subschemeMap _ _ _ (Scheme.IdealSheafData.le_map_comap _ _))))).mpr hZ

/-- The closed subscheme of the inverse image of `Z` along an isomorphism is regular when `V(Z)`
is: the stalks correspond under the isomorphism `V(Z ∘ e) ≅ V(Z)`
(`IsRegularLocalRing.of_ringEquiv`). -/
theorem isRegular_subscheme_comap_of_isIso (e : Y ⟶ X) [IsIso e] (Z : X.IdealSheafData)
    (hZ : IsRegular Z.subscheme) : IsRegular (Z.comap e).subscheme := by
  have hm := isIso_subschemeMap_comap_of_isIso e Z
  refine ⟨fun z => ?_⟩
  have h1 : IsRegularLocalRing (Z.subscheme.presheaf.stalk
      ((Scheme.IdealSheafData.subschemeMap _ _ _ (Scheme.IdealSheafData.le_map_comap _ _)) z)) :=
    hZ.isRegularAt _
  exact IsRegularLocalRing.of_ringEquiv (asIso ((Scheme.IdealSheafData.subschemeMap _ _ _
    (Scheme.IdealSheafData.le_map_comap _ _)).stalkMap z)).commRingCatIsoToRingEquiv

/-- `boundarySeq_ofCenters_last'` for an `E₀` equal to the vanishing ideal of its support: the
form in which the reducedness of `E₀` enters (`radical_eq_self_of_isReduced_subscheme`), and the
form Hironaka's boundaries themselves have (`reducedTransform` is a vanishing ideal). -/
theorem boundarySeq_ofCenters_last_of_vanishingIdeal_eq {c : ℕ} (D : Fin c → X.IdealSheafData)
    (Z : X.IdealSheafData) (hZ : ∏ i, D i = Z) (e : (ofCenters c D).last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = (ofCenters c D).composite) (E₀ : X.IdealSheafData)
    (hE₀ : vanishingIdeal E₀.support = E₀) :
    (ofCenters c D).boundarySeq E₀ (Fin.last _) = (E₀.reducedTransform Z).comap e := by
  subst hZ
  obtain ⟨e₀, he₀, huniq⟩ := exists_iso_last_ofCenters c D
  obtain rfl : e = e₀.hom := huniq e he
  rw [boundarySeq_ofCenters_last_eq_vanishingIdeal_support c D E₀ hE₀]
  change _ = (vanishingIdeal _).comap e₀.hom
  rw [comap_vanishingIdeal_of_isIso]
  congr 1
  refine SetLike.coe_injective ?_
  rw [coe_support_boundarySeq_ofCenters_last]
  change (ofCenters c D).composite ⁻¹' _ =
    e₀.hom ⁻¹' (((∏ i, D i).blowUpπ) ⁻¹' ((E₀.support : Set X)) ∪
      (∏ i, D i).blowUpπ ⁻¹' (((∏ i, D i).support : Set X)))
  rw [← he₀, ← Set.preimage_union]
  rfl

/-- `boundarySeq_componentwiseSeq_last` for an `E₀` equal to the vanishing ideal of its
support. -/
theorem boundarySeq_componentwiseSeq_last_of_vanishingIdeal_eq [NoetherianSpace X]
    (Z : X.IdealSheafData) (hZ : IsRegular Z.subscheme)
        (e : Z.componentwiseSeq.last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = Z.componentwiseSeq.composite) (E₀ : X.IdealSheafData)
    (hE₀ : vanishingIdeal E₀.support = E₀) :
    Z.componentwiseSeq.boundarySeq E₀ (Fin.last _) = (E₀.reducedTransform Z).comap e := by
  unfold Scheme.IdealSheafData.componentwiseSeq
  exact boundarySeq_ofCenters_last_of_vanishingIdeal_eq _ Z
    ((DivisorFamily.prod_orderedComponent _).trans
        (prod_componentFamily_eq Z hZ)) e he
    E₀ hE₀

/-- The inverse image along a fourfold composite, as nested inverse images (`comap_comp`). -/
theorem comap_comp₄ {X₀ X₁ X₂ X₃ X₄ : Scheme.{u}} (I : X₄.IdealSheafData) (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) :
    I.comap (a ≫ b ≫ c ≫ d) = (((I.comap d).comap c).comap b).comap a := by
  rw [comap_comp, comap_comp, comap_comp]

/-! ### The refinement -/

section Main

variable {k : Type u} [Field k] [CharZero k]

/-- The refinement to irreducible centers, the induction: a smooth blow-up sequence `S` of order
`d` for `(X, J, E)` [Kol07, Definition 66] refines, for every subdivision `F` of `E`, to a sequence
`S'` of order `d` for `(X, J, F)` with regular irreducible centers, of length `∑ᵢ rᵢ`, with the
same composite, weak transform and boundaries (for `E₀` a vanishing ideal) across an isomorphism
`S'.last ≅ S.last`. Induction on `S`: the first center `Z` is replaced by its componentwise
sequence `T` (`isOrderSeq_componentwiseSeq`, `exists_iso_last_componentwiseSeq`), the tail is
refined by the inductive hypothesis for the subdivision `(T.totalTransformSeq F).comap e₁⁻¹` of
`E.totalTransform Z` (`subdivides_totalTransformSeq_ofCenters_last`), carried across `e₁` by
pullback (`IsOrderSeq.pullback`), and the two are concatenated (`isOrderSeq_concat`); the
conditions at the last stage follow from the concatenation, componentwise and pullback transport
lemmas. -/
theorem exists_refineIrreducible_aux :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (S : BlowUpSequence X) (f : X ⟶ Spec (.of k)) (n : ℕ)
      [SmoothOfRelativeDimension n f] (J : X.IdealSheafData) (E F : DivisorFamily X) (d : ℕ),
      F.Subdivides E → S.IsOrderSeq f J E d →
      ∃ S' : BlowUpSequence X, S'.IsOrderSeq f J F d ∧
        (∀ i : Fin S'.length,
          IsRegular (S'.center i).subscheme ∧ IrreducibleSpace (S'.center i).subscheme) ∧
        S'.length = ∑ i : Fin S.length, Nat.card (S.center i).support.genericPoints ∧
        ∃ e : S'.last ≅ S.last, e.hom ≫ S.composite = S'.composite ∧
          S'.weakTransformSeq J (Fin.last S'.length) =
            (S.weakTransformSeq J (Fin.last S.length)).comap e.hom ∧
          ∀ E₀ : X.IdealSheafData, vanishingIdeal E₀.support = E₀ →
            S'.boundarySeq E₀ (Fin.last S'.length) =
              (S.boundarySeq E₀ (Fin.last S.length)).comap e.hom := by
  intro X inst S
  revert inst
  induction S with
  | nil X =>
    intro _ f n _ J E F d _ hS
    refine ⟨nil X, ⟨hS.1, fun i => i.elim0⟩, fun i => i.elim0, ?_, Iso.refl _, by simp,
      ?_, fun E₀ _ => ?_⟩
    · change (0 : ℕ) = ∑ i : Fin 0, Nat.card ((nil X).center i).support.genericPoints
      simp
    · change J = J.comap (𝟙 X)
      simp
    · change E₀ = E₀.comap (𝟙 X)
      simp
  | cons X Z rest ih =>
    intro _ f n _ J E F d hFE hS
    rw [isOrderSeq_cons_iff] at hS
    obtain ⟨⟨hZ, hsnc, hord⟩, hrest⟩ := hS
    have := hZ
    have hreg : IsRegular Z.subscheme := ⟨fun z =>
      isRegularLocalRing_stalk (Z.subschemeι ≫ f) z⟩
    have hN : IsNoetherian Z.blowUp := blowUp.isNoetherian Z
    have hsm : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n Z
    obtain ⟨e₁, he₁⟩ := exists_iso_last_componentwiseSeq Z hreg
    have hprod : ∏ l, Z.componentFamily.nth l = Z :=
      (DivisorFamily.prod_orderedComponent _).trans
          (prod_componentFamily_eq Z hreg)
    have hπZ : IsBlowUp (∏ l, Z.componentFamily.nth l) Z.blowUpπ := by
      rw [hprod]; exact blowUp.isBlowUp Z
    have hsub : (Z.componentwiseSeq.totalTransformSeq F (Fin.last _)).Subdivides
        ((E.totalTransform Z).comap e₁.hom) := by
      have h := subdivides_totalTransformSeq_ofCenters_last _ Z.componentFamily.nth
        (pairwise_disjoint_support_orderedComponent Z hreg) hFE
            Z.blowUpπ hπZ e₁.hom he₁
      rwa [hprod] at h
    have hcomp : ((E.totalTransform Z).comap e₁.hom).comap e₁.inv = E.totalTransform Z := by
      rw [← DivisorFamily.comap_comp, Iso.inv_hom_id, DivisorFamily.comap_id]
    have hF₁ : ((Z.componentwiseSeq.totalTransformSeq F (Fin.last _)).comap
        e₁.inv).Subdivides (E.totalTransform Z) := hcomp ▸ subdivides_comap hsub e₁.inv
    have hcomp' : ((Z.componentwiseSeq.totalTransformSeq F (Fin.last _)).comap e₁.inv).comap
        e₁.hom = Z.componentwiseSeq.totalTransformSeq F (Fin.last _) :=
      (DivisorFamily.comap_comp _ e₁.hom e₁.inv).symm.trans
        (by rw [Iso.hom_inv_id]; exact DivisorFamily.comap_id _)
    obtain ⟨R, hR, hRcent, hRlen, eR, heR, hRweak, hRbd⟩ :=
      ih (Z.blowUpπ ≫ f) n (J.weakTransform Z) (E.totalTransform Z) _ d hF₁ hrest
    -- retype the isomorphism of the inductive hypothesis at the last stage
    obtain ⟨eR, rfl⟩ : ∃ e' : R.stage (Fin.last R.length) ≅ rest.last, e' = eR := ⟨eR, rfl⟩
    have heR' : eR.hom ≫ rest.composite = R.stageMap (Fin.last R.length) := heR
    have hRweak' : R.weakTransformSeq (J.weakTransform Z) (Fin.last R.length) =
        (rest.weakTransformSeq (J.weakTransform Z) (Fin.last rest.length)).comap eR.hom := hRweak
    have hRbd' : ∀ E₀ : Z.blowUp.IdealSheafData, vanishingIdeal E₀.support = E₀ →
        R.boundarySeq E₀ (Fin.last R.length) =
          (rest.boundarySeq E₀ (Fin.last rest.length)).comap eR.hom := hRbd
    have hps : R.pullbackStageHom e₁.hom (Fin.last _) ≫ R.stageMap (Fin.last R.length) =
        (R.pullback e₁.hom).stageMap (R.pullbackStageIdx e₁.hom (Fin.last _)) ≫ e₁.hom :=
      pullbackStageHom_stageMap R e₁.hom (Fin.last _)
    have hidx : (R.pullback e₁.hom).last =
        (R.pullback e₁.hom).stage (R.pullbackStageIdx e₁.hom (Fin.last R.length)) :=
      congrArg _ (pullbackStageIdx_last R e₁.hom).symm
    have hiso := isIso_pullbackStageHom_of_isIso R e₁.hom (Fin.last R.length)
    refine ⟨Z.componentwiseSeq.concat (R.pullback e₁.hom), ?_, ?_, ?_, ?_⟩
    · refine isOrderSeq_concat f Z.componentwiseSeq (R.pullback e₁.hom)
        (isOrderSeq_componentwiseSeq f n Z hZ hord (hasSncWith_of_subdivides hFE hsnc)) ?_
      have hf' : Z.componentwiseSeq.composite ≫ f = e₁.hom ≫ Z.blowUpπ ≫ f := by
        rw [← Category.assoc, he₁]
      rw [hf', weakTransformSeq_componentwiseSeq_last f n Z hZ hord e₁.hom he₁, ← hcomp']
      exact IsOrderSeq.pullback (Z.blowUpπ ≫ f) n e₁.hom (d := 0) hR
    · refine forall_center_concat
        (fun {Y} W => IsRegular W.subscheme ∧ IrreducibleSpace W.subscheme)
        Z.componentwiseSeq (R.pullback e₁.hom)
        (fun i => ⟨isRegular_center_componentwiseSeq Z hreg i,
          irreducibleSpace_center_componentwiseSeq Z hreg i⟩) fun j => ?_
      have hidx' : R.pullbackCenterIdx e₁.hom (Fin.cast (length_pullback R e₁.hom) j) = j :=
        Fin.ext rfl
      rw [← hidx', center_pullback]
      obtain ⟨h1, h2⟩ := hRcent (Fin.cast (length_pullback R e₁.hom) j)
      have := isIso_pullbackStageHom_of_isIso R e₁.hom
        (Fin.cast (length_pullback R e₁.hom) j).castSucc
      exact ⟨isRegular_subscheme_comap_of_isIso _ _ h1,
        irreducibleSpace_subscheme_comap_of_isIso _ _ h2⟩
    · rw [length_concat, length_componentwiseSeq, length_pullback, hRlen]
      change _ = ∑ i : Fin (rest.length + 1),
        Nat.card ((cons X Z rest).center i).support.genericPoints
      rw [Fin.sum_univ_succ]
      rfl
    · refine ⟨eqToIso (last_concat _ _) ≪≫ eqToIso hidx ≪≫
        asIso (R.pullbackStageHom e₁.hom (Fin.last R.length)) ≪≫ eR, ?_, ?_, ?_⟩
      · have hRc : (R.pullback e₁.hom).composite = eqToHom hidx ≫
            (R.pullback e₁.hom).stageMap (R.pullbackStageIdx e₁.hom (Fin.last R.length)) :=
          composite_congr_idx _ (pullbackStageIdx_last R e₁.hom).symm
        have hstage : (R.pullback e₁.hom).stageMap (R.pullbackStageIdx e₁.hom (Fin.last R.length))
            ≫ Z.componentwiseSeq.composite = R.pullbackStageHom e₁.hom (Fin.last R.length) ≫
              R.stageMap (Fin.last R.length) ≫ Z.blowUpπ := by
          rw [← he₁, ← Category.assoc, ← hps, Category.assoc]
        rw [composite_concat, hRc, Category.assoc, hstage]
        change (eqToHom (last_concat Z.componentwiseSeq (R.pullback e₁.hom)) ≫ eqToHom hidx ≫
          R.pullbackStageHom e₁.hom (Fin.last R.length) ≫ eR.hom) ≫
            rest.composite ≫ Z.blowUpπ = _
        simp only [Category.assoc]
        rw [reassoc_of% heR']
      · rw [weakTransformSeq_concat_last,
          weakTransformSeq_componentwiseSeq_last f n Z hZ hord e₁.hom he₁,
          weakTransformSeq_congr_idx (R.pullback e₁.hom) _ (pullbackStageIdx_last R e₁.hom).symm,
          IsOrderSeq.weakTransformSeq_pullback (Z.blowUpπ ≫ f) n e₁.hom (d := 0) hR
            (Fin.last R.length), hRweak']
        exact (comap_comp₄ (rest.weakTransformSeq (J.weakTransform Z) (Fin.last _))
          (eqToHom (last_concat _ _)) (eqToHom hidx) (R.pullbackStageHom e₁.hom (Fin.last R.length))
          eR.hom).symm
      · intro E₀ hE₀
        have hred : vanishingIdeal (E₀.reducedTransform Z).support = E₀.reducedTransform Z := by
          unfold reducedTransform
          rw [support_vanishingIdeal_eq]
        rw [boundarySeq_concat_last,
          boundarySeq_componentwiseSeq_last_of_vanishingIdeal_eq Z hreg e₁.hom he₁ E₀ hE₀,
          boundarySeq_congr_idx (R.pullback e₁.hom) _ (pullbackStageIdx_last R e₁.hom).symm,
          boundarySeq_pullback_of_isIso R e₁.hom (E₀.reducedTransform Z) (Fin.last R.length),
          hRbd' _ hred]
        exact (comap_comp₄ (rest.boundarySeq (E₀.reducedTransform Z) (Fin.last _))
          (eqToHom (last_concat _ _)) (eqToHom hidx) (R.pullbackStageHom e₁.hom (Fin.last R.length))
          eR.hom).symm

end Main

end Hironaka.Sequence

namespace Hironaka.Sequence

/-- **Refinement to irreducible centers**: a smooth blow-up sequence of order `d` for `(X, J, E)`
[Kol07, Definition 66] refines to one with regular irreducible centers, as clause (i) of
[Hir64, Main Theorem II] demands, of length `∑ᵢ rᵢ`, with the same composite, the same `J_r` and
the same `E_r` (the boundary for every reduced `E₀`) across the canonical isomorphism of the last
stages. This is `exists_refineIrreducible_aux` for the trivial subdivision `E` of itself, a reduced
`E₀` being the vanishing ideal of its support (`radical_eq_self_of_isReduced_subscheme`). -/
theorem IsOrderSeq.exists_refineIrreducible {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
    [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {S : BlowUpSequence X} {J : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ}
    (h : S.IsOrderSeq f J E d) :
    ∃ S' : BlowUpSequence X, S'.IsOrderSeq f J E d ∧
      (∀ i : Fin S'.length,
        IsRegular (S'.center i).subscheme ∧ IrreducibleSpace (S'.center i).subscheme) ∧
      S'.length = ∑ i : Fin S.length, Nat.card (S.center i).support.genericPoints ∧
      ∃ e : S'.last ≅ S.last, e.hom ≫ S.composite = S'.composite ∧
        S'.weakTransformSeq J (Fin.last S'.length) =
          (S.weakTransformSeq J (Fin.last S.length)).comap e.hom ∧
        ∀ E₀ : X.IdealSheafData, IsReduced E₀.subscheme →
          S'.boundarySeq E₀ (Fin.last S'.length) =
            (S.boundarySeq E₀ (Fin.last S.length)).comap e.hom := by
  obtain ⟨S', h1, h2, h3, e, h4, h5, h6⟩ :=
    exists_refineIrreducible_aux S f n J E E d (subdivides_refl E) h
  refine ⟨S', h1, h2, h3, e, h4, h5, fun E₀ _ => h6 E₀ ?_⟩
  rw [vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]

end Hironaka.Sequence

namespace Hironaka.Sequence

/-! ### The order statements with the binders in the order of the main theorems

The four theorems below duplicate `isOrderSeq_ofCenters`, `weakTransformSeq_ofCenters_last`
(`Hironaka/Resolution/Algebraic/Kol07/ComponentwiseTransport.lean`, `ComponentwiseTransforms.lean`),
`isOrderSeq_componentwiseSeq` and `weakTransformSeq_componentwiseSeq_last`
(`ComponentwiseTransforms.lean`), differing only in the order and explicitness of the binders:
`{k} [Field k] {X} [IsNoetherian X] [CharZero k] (f) (n) [SmoothOfRelativeDimension n f]`, the
Noetherian hypothesis present in every statement, which is the order in which the proof of Main
Theorem II supplies them. -/

/-- `Hironaka.Sequence.isOrderSeq_ofCenters` with the binders in the order of the main theorems;
a duplicate kept for the proofs that supply the hypotheses in this order. -/
theorem isOrderSeq_ofCenters' {k : Type u} [Field k] {X : Scheme.{u}} [CharZero k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {c : ℕ}
    (D : Fin c → X.IdealSheafData)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hZ : Smooth ((∏ i, D i).subschemeι ≫ f)) {J : X.IdealSheafData} {E : DivisorFamily X}
    {d : ℕ} (hord : J.OrdAlongEq (∏ i, D i).support (d : ℕ∞)) (hsnc : E.HasSncWith (∏ i, D i)) :
    (ofCenters c D).IsOrderSeq f J E d :=
  Hironaka.Sequence.isOrderSeq_ofCenters f n D hdisj hZ hord hsnc

/-- `Hironaka.Sequence.weakTransformSeq_ofCenters_last` with the binders in the order of the main
theorems; a duplicate kept for the proofs that supply the hypotheses in this order. -/
theorem weakTransformSeq_ofCenters_last'' {k : Type u} [Field k] {X : Scheme.{u}}
    [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {c : ℕ}
    (D : Fin c → X.IdealSheafData)
    (hdisj : Pairwise fun i j => Disjoint (D i).support (D j).support)
    (hZ : Smooth ((∏ i, D i).subschemeι ≫ f)) {J : X.IdealSheafData} {d : ℕ}
    (hord : J.OrdAlongEq (∏ i, D i).support (d : ℕ∞))
    (e : (ofCenters c D).last ⟶ (∏ i, D i).blowUp)
    (he : e ≫ (∏ i, D i).blowUpπ = (ofCenters c D).composite) :
    (ofCenters c D).weakTransformSeq J (Fin.last _) = (J.weakTransform (∏ i, D i)).comap e :=
  Hironaka.Sequence.weakTransformSeq_ofCenters_last f n D hdisj hZ hord e he

/-- `Hironaka.Sequence.isOrderSeq_componentwiseSeq` with the binders in the order of the main
theorems; a duplicate kept for the proofs that supply the hypotheses in this order. -/
theorem isOrderSeq_componentwiseSeq' {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
    [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ f)) {J : X.IdealSheafData}
    {E : DivisorFamily X} {d : ℕ} (hord : J.OrdAlongEq Z.support (d : ℕ∞))
    (hsnc : E.HasSncWith Z) : Z.componentwiseSeq.IsOrderSeq f J E d :=
  Hironaka.Sequence.isOrderSeq_componentwiseSeq f n Z hZ hord hsnc

/-- `Hironaka.Sequence.weakTransformSeq_componentwiseSeq_last` with the binders in the order of the
main theorems; a duplicate kept for the proofs that supply the hypotheses in this order. -/
theorem weakTransformSeq_componentwiseSeq_last' {k : Type u} [Field k] {X : Scheme.{u}}
    [IsNoetherian X] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData) (hZ : Smooth (Z.subschemeι ≫ f)) {J : X.IdealSheafData} {d : ℕ}
    (hord : J.OrdAlongEq Z.support (d : ℕ∞)) (e : Z.componentwiseSeq.last ⟶ Z.blowUp)
    (he : e ≫ Z.blowUpπ = Z.componentwiseSeq.composite) :
    Z.componentwiseSeq.weakTransformSeq J (Fin.last _) = (J.weakTransform Z).comap e :=
  Hironaka.Sequence.weakTransformSeq_componentwiseSeq_last f n Z hZ hord e he

end Hironaka.Sequence
