import Hironaka.Resolution.HironakaG3IndexedMixedLocalCover
import Hironaka.Resolution.HironakaG3LocalMixedOverlap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3IndexedMixedOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms RestrictEmptyTower
  MarkedIdealRestrictOpen BlowupRestrictOpen NormalCrossings HironakaBaseChange MaxLocusLocal
  HironakaEmbeddedAnalyticLocal HironakaG3FiniteMixedBadLocus HironakaG3MixedOrderedSeparation
  HironakaG3OrderedFiniteWindows HironakaG3LocalMixedOverlap HironakaG3MixedFilteredComparison
  HironakaOriginalTerminalOverlapComparison HironakaOriginalCanonicalSeparationChainChoice

variable {n : ℕ} {X X' : CMfd.{0} n}
private theorem closedParts_pulled
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : closedParts (pulledParts Φ L)=pulledParts Φ (closedParts L) := by
  simp only [closedParts,pulledParts,List.map_map]
  congr 1
  funext p
  exact Prod.ext (Φ.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage Φ.continuous p.1).symm rfl

private theorem nonemptyParts_closedParts {Z : Type u} [TopologicalSpace Z]
    (L : List (Set Z × ℕ)) : nonemptyParts (closedParts L)=closedParts (nonemptyParts L) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hc : (closure p.1).Nonempty ↔ p.1.Nonempty := closure_nonempty_iff
    by_cases hp : p.1.Nonempty <;> simp [closedParts,nonemptyParts,hc,hp] at ih ⊢ <;> exact ih

private theorem nonemptyParts_pulled
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (L : List (Set X × ℕ)) : nonemptyParts (pulledParts Φ L)=pulledParts Φ (nonemptyParts L) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hp : (Φ ⁻¹' p.1).Nonempty ↔ p.1.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨Φ x,hx⟩,fun h => h.preimage Φ.surjective⟩
    by_cases hne : p.1.Nonempty <;> simp [nonemptyParts,pulledParts,hp,hne] at ih ⊢ <;> exact ih

private theorem filter_preimage {P Q : Type*} (f : P → Q) (hf : Surjective f)
    (E : List (Set Q)) :
    (E.map (f ⁻¹' ·)).filter (fun H => decide H.Nonempty)=
      (E.filter (fun H => decide H.Nonempty)).map (f ⁻¹' ·) := by
  induction E with
  | nil => rfl
  | cons H E ih =>
    have hh : (f ⁻¹' H).Nonempty ↔ H.Nonempty :=
      ⟨fun ⟨x,hx⟩ => ⟨f x,hx⟩,fun h => h.preimage hf⟩
    by_cases hne : H.Nonempty <;> simp [hh,hne,ih]


/-- Sorted finite-window histories pull back to actual histories over smaller
opens and identify with literal tower restrictions. -/
theorem sorted_window_actual_restriction {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (s : Finset ι) (r : Finset κ) (U : Opens X)
    {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y) (Ef : List (Set Y))
    (hTree : CanonicalMixedSeparation (((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·))
      ((s.sort (· ≤ ·)).map (fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim))) T Ef)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s.sort (· ≤ ·)).length => V ((s.sort (· ≤ ·)).get j))) T)
    (W : Opens (CMfd.of (n := n) U)) :
    ∃ (C : CMfd.{0} n) (Q : BlowupTower (CMfd.of (n := n) W) C) (g : C → Y)
      (β : C ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T W)),
      CanonicalMixedSeparation
        ((((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·)).map ((Subtype.val : W → U) ⁻¹' ·))
        (((s.sort (· ≤ ·)).map (fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim))).map
          (fun p => ((Subtype.val : W → U) ⁻¹' p.1,p.2))) Q (Ef.map (g ⁻¹' ·)) ∧
      (∀ q, (restrict W T).proj (β q) = Q.proj q) ∧ (∀ q, (β q : openPreimage T W).val = g q) := by
  let l := s.sort (· ≤ ·)
  let V' : Fin l.length → ClosedIrreducibleAnalyticSubvariety n X := fun j => V (l.get j)
  have he : Injective l.get := (s.sort_nodup (· ≤ ·)).injective_get
  have hmap : (List.finRange l.length).map (fun a => ((Subtype.val : U → X) ⁻¹' (V' a).carrier,(V' a).dim)) =
      l.map (fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim)) := by
    change (List.finRange l.length).map ((fun a => ((Subtype.val : U → X) ⁻¹' (V a).carrier,(V a).dim)) ∘ l.get) = _
    rw [← List.map_map,List.map_get_finRange]
  have hTree' : CanonicalMixedSeparation (((r.sort (· ≤ ·)).map D).map ((Subtype.val : U → X) ⁻¹' ·))
      ((List.finRange l.length).map fun a => ((Subtype.val : U → X) ⁻¹' (V' a).carrier,(V' a).dim)) T Ef := by
    rw [hmap]
    exact hTree
  obtain ⟨C,Q,g,β,hQ,hβ,hg⟩ := local_mixed_tree_actual_restriction V'
    (fun a => hDim (l.get a))
    (fun a b hab => hDistinct (l.get a) (l.get b) (fun h => hab (he h)))
    ((r.sort (· ≤ ·)).map D) U T Ef hTree' hOver W
  rw [hmap] at hQ
  exact ⟨C,Q,g,β,hQ,hβ,hg⟩
/-- Ordered finite windows compare over any base biholomorphism when their
labelled traces agree there and both contain every visible label. -/
theorem sorted_window_choice_over_equiv {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    {Y Y' : CMfd.{0} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (F : ι → Set X) (F' : ι → Set X') (d : ι → ℕ) (G : κ → Set X) (G' : κ → Set X')
    (hF : ∀ i, F' i = Φ ⁻¹' F i) (hG : ∀ i, G' i = Φ ⁻¹' G i)
    (s t : Finset ι) (r q : Finset κ)
    (hs : ∀ i, (F' i).Nonempty → i ∈ s) (ht : ∀ i, (F' i).Nonempty → i ∈ t)
    (hr : ∀ i, (G' i).Nonempty → i ∈ r) (hq : ∀ i, (G' i).Nonempty → i ∈ q)
    (T : BlowupTower X Y) (S : BlowupTower X' Y') {Ef : List (Set Y)} {Ef' : List (Set Y')}
    (hT : CanonicalMixedSeparation ((r.sort (· ≤ ·)).map G)
      ((s.sort (· ≤ ·)).map (fun i => (F i,d i))) T Ef)
    (hS : CanonicalMixedSeparation ((q.sort (· ≤ ·)).map G')
      ((t.sort (· ≤ ·)).map (fun i => (F' i,d i))) S Ef') :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      (∀ z,T.proj (η z)=Φ (S.proj z)) ∧
      Ef'.filter (fun H => decide H.Nonempty)=
        (Ef.filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) ∧
      ∀ P : Set X,strictTransform n S.proj (Φ ⁻¹' P)=η ⁻¹' strictTransform n T.proj P := by
  have hB := sorted_boundary_traces_agree G' r q hr hq
  have hE : ((q.sort (· ≤ ·)).map G').filter (fun H => decide H.Nonempty) =
      (((r.sort (· ≤ ·)).map G).filter (fun H => decide H.Nonempty)).map (Φ ⁻¹' ·) := by
    rw [← filter_preimage Φ Φ.surjective]
    have hmap : ((r.sort (· ≤ ·)).map G).map (Φ ⁻¹' ·) = (r.sort (· ≤ ·)).map G' := by
      simp only [List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro i hi
      exact (hG i).symm
    rw [hmap]
    exact hB.symm
  have hc := sorted_component_traces_agree (fun i => closure (F' i)) d s t
    (fun i hi => hs i (closure_nonempty_iff.mp hi))
    (fun i hi => ht i (closure_nonempty_iff.mp hi))
  have hL : nonemptyParts (closedParts ((t.sort (· ≤ ·)).map (fun i => (F' i,d i)))) =
      pulledParts Φ (nonemptyParts (closedParts ((s.sort (· ≤ ·)).map (fun i => (F i,d i))))) := by
    rw [← nonemptyParts_pulled,← closedParts_pulled]
    have hmap : pulledParts Φ ((s.sort (· ≤ ·)).map (fun i => (F i,d i))) =
        (s.sort (· ≤ ·)).map (fun i => (F' i,d i)) := by
      simp only [pulledParts,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro i hi
      exact Prod.ext (hF i).symm rfl
    rw [hmap]
    simpa [closedParts,List.map_map,Function.comp_def] using hc.symm
  exact mixed_choice_over_base_closedParts Φ hT hS hE hL
/-- Actual sorted local histories with complete visible windows compare on
their literal ambient overlap. -/
theorem indexed_mixed_trees_overlap_with_boundary {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (s₁ s₂ : Finset ι) (r₁ r₂ : Finset κ) (U₁ U₂ : Opens X)
    (hs₁ : ∀ i, ((V i).carrier ∩ (U₁ : Set X)).Nonempty → i ∈ s₁)
    (hs₂ : ∀ i, ((V i).carrier ∩ (U₂ : Set X)).Nonempty → i ∈ s₂)
    (hr₁ : ∀ i, (D i ∩ (U₁ : Set X)).Nonempty → i ∈ r₁)
    (hr₂ : ∀ i, (D i ∩ (U₂ : Set X)).Nonempty → i ∈ r₂)
    {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (Ef₁ : List (Set Y₁)) (Ef₂ : List (Set Y₂))
    (hTree₁ : CanonicalMixedSeparation (((r₁.sort (· ≤ ·)).map D).map ((Subtype.val : U₁ → X) ⁻¹' ·))
      ((s₁.sort (· ≤ ·)).map (fun a => ((Subtype.val : U₁ → X) ⁻¹' (V a).carrier,(V a).dim))) T₁ Ef₁)
    (hTree₂ : CanonicalMixedSeparation (((r₂.sort (· ≤ ·)).map D).map ((Subtype.val : U₂ → X) ⁻¹' ·))
      ((s₂.sort (· ≤ ·)).map (fun a => ((Subtype.val : U₂ → X) ⁻¹' (V a).carrier,(V a).dim))) T₂ Ef₂)
    (hOver₁ : CentresOver ((Subtype.val : U₁ → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s₁.sort (· ≤ ·)).length => V ((s₁.sort (· ≤ ·)).get j))) T₁)
    (hOver₂ : CentresOver ((Subtype.val : U₂ → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s₂.sort (· ≤ ·)).length => V ((s₂.sort (· ≤ ·)).get j))) T₂) :
    let W₁ := nestedOpens U₁ (U₁ ⊓ U₂)
    let W₂ := nestedOpens U₂ (U₁ ⊓ U₂)
    ∃ η : CMfd.of (n := n) (openPreimage T₁ W₁) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ W₂),
      (∀ z, ((T₂.proj (η z).val : U₂) : X) = ((T₁.proj z.val : U₁) : X)) ∧
      ((Ef₁.map ((Subtype.val : openPreimage T₁ W₁ → Y₁) ⁻¹' ·)).filter (fun H => decide H.Nonempty)) =
        ((Ef₂.map ((Subtype.val : openPreimage T₂ W₂ → Y₂) ⁻¹' ·)).filter (fun H => decide H.Nonempty)).map (η ⁻¹' ·) := by
  let W₁ := nestedOpens U₁ (U₁ ⊓ U₂)
  let W₂ := nestedOpens U₂ (U₁ ⊓ U₂)
  let Φ := overlapBaseEquiv (n := n) (inf_le_left : U₁ ⊓ U₂ ≤ U₁) inf_le_right
  obtain ⟨C₁,Q₁,g₁,β₁,hQ₁,hβ₁,hg₁⟩ :=
    sorted_window_actual_restriction V hDim hDistinct D s₁ r₁ U₁ T₁ Ef₁ hTree₁ hOver₁ W₁
  obtain ⟨C₂,Q₂,g₂,β₂,hQ₂,hβ₂,hg₂⟩ :=
    sorted_window_actual_restriction V hDim hDistinct D s₂ r₂ U₂ T₂ Ef₂ hTree₂ hOver₂ W₂
  let F₁ (i : ι) : Set W₁ := (Subtype.val : W₁ → U₁) ⁻¹' ((Subtype.val : U₁ → X) ⁻¹' (V i).carrier)
  let F₂ (i : ι) : Set W₂ := (Subtype.val : W₂ → U₂) ⁻¹' ((Subtype.val : U₂ → X) ⁻¹' (V i).carrier)
  let G₁ (i : κ) : Set W₁ := (Subtype.val : W₁ → U₁) ⁻¹' ((Subtype.val : U₁ → X) ⁻¹' D i)
  let G₂ (i : κ) : Set W₂ := (Subtype.val : W₂ → U₂) ⁻¹' ((Subtype.val : U₂ → X) ⁻¹' D i)
  have hF : ∀ i, F₁ i = Φ ⁻¹' F₂ i := fun _ => rfl
  have hG : ∀ i, G₁ i = Φ ⁻¹' G₂ i := fun _ => rfl
  have hvs₁ : ∀ i, (F₁ i).Nonempty → i ∈ s₁ := by
    intro i ⟨z,hz⟩
    exact hs₁ i ⟨_,hz,z.val.property⟩
  have hvs₂ : ∀ i, (F₁ i).Nonempty → i ∈ s₂ := by
    intro i ⟨z,hz⟩
    exact hs₂ i ⟨_,hz,z.property.2⟩
  have hvr₁ : ∀ i, (G₁ i).Nonempty → i ∈ r₁ := by
    intro i ⟨z,hz⟩
    exact hr₁ i ⟨_,hz,z.val.property⟩
  have hvr₂ : ∀ i, (G₁ i).Nonempty → i ∈ r₂ := by
    intro i ⟨z,hz⟩
    exact hr₂ i ⟨_,hz,z.property.2⟩
  have hQ₁' : CanonicalMixedSeparation ((r₁.sort (· ≤ ·)).map G₁)
      ((s₁.sort (· ≤ ·)).map (fun i => (F₁ i,(V i).dim))) Q₁ (Ef₁.map (g₁ ⁻¹' ·)) := by
    simpa [F₁,G₁,List.map_map,Function.comp_def] using hQ₁
  have hQ₂' : CanonicalMixedSeparation ((r₂.sort (· ≤ ·)).map G₂)
      ((s₂.sort (· ≤ ·)).map (fun i => (F₂ i,(V i).dim))) Q₂ (Ef₂.map (g₂ ⁻¹' ·)) := by
    simpa [F₂,G₂,List.map_map,Function.comp_def] using hQ₂
  obtain ⟨γ,⟨hγ,hγE,_hγstrict⟩,_⟩ := sorted_window_choice_over_equiv Φ F₂ F₁
    (fun i => (V i).dim) G₂ G₁ hF hG s₂ s₁ r₂ r₁ hvs₂ hvs₁ hvr₂ hvr₁ Q₂ Q₁ hQ₂' hQ₁'
  let η := β₁.symm.trans (γ.trans β₂)
  have hη : ∀ z, ((T₂.proj (η z).val : U₂) : X) = ((T₁.proj z.val : U₁) : X) := by
    intro z
    let q := β₁.symm z
    have h₁ := congrArg (fun p : W₁ => ((p.val : U₁) : X)) (hβ₁ q)
    have h₂ := congrArg (fun p : W₂ => ((p.val : U₂) : X)) (hβ₂ (γ q))
    have hγ' : ((Q₂.proj (γ q) : W₂).val : U₂) =
        (Φ (Q₁.proj q)).val := congrArg Subtype.val (hγ q)
    have hγ'' : (((Q₂.proj (γ q) : W₂).val : U₂) : X) =
        (((Q₁.proj q : W₁).val : U₁) : X) := by
      rw [hγ']
      rfl
    simp only [proj_restrict] at h₁ h₂
    have hq : β₁ q = z := β₁.apply_symm_apply z
    rw [hq] at h₁
    change ((T₂.proj (β₂ (γ q)).val : U₂) : X) = ((T₁.proj z.val : U₁) : X)
    exact h₂.trans (hγ''.trans h₁.symm)
  refine ⟨η,hη,?_⟩
  let B₁ := Ef₁.map ((Subtype.val : openPreimage T₁ W₁ → Y₁) ⁻¹' ·)
  let B₂ := Ef₂.map ((Subtype.val : openPreimage T₂ W₂ → Y₂) ⁻¹' ·)
  have hB₁ : Ef₁.map (g₁ ⁻¹' ·) = B₁.map (β₁ ⁻¹' ·) := by
    simp only [B₁,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro H hH
    ext q
    change g₁ q ∈ H ↔ (β₁ q).val ∈ H
    rw [hg₁]
  have hB₂ : Ef₂.map (g₂ ⁻¹' ·) = B₂.map (β₂ ⁻¹' ·) := by
    simp only [B₂,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro H hH
    ext q
    change g₂ q ∈ H ↔ (β₂ q).val ∈ H
    rw [hg₂]
  rw [hB₁,hB₂,filter_preimage β₁ β₁.surjective,filter_preimage β₂ β₂.surjective] at hγE
  have h := congrArg (List.map (β₁.symm ⁻¹' ·)) hγE
  simp only [List.map_map,Function.comp_def] at h
  have hLeft : ∀ H : Set (openPreimage T₁ W₁), β₁.symm ⁻¹' (β₁ ⁻¹' H) = H := by
    intro H; ext x; simp
  have hRight : ∀ H : Set (openPreimage T₂ W₂),
      β₁.symm ⁻¹' (γ ⁻¹' (β₂ ⁻¹' H)) = η ⁻¹' H := by
    intro H; ext x; rfl
  simp only [hLeft,hRight] at h
  change List.map id _ = _ at h
  rw [List.map_id] at h
  exact h

/-- Actual sorted local histories with complete visible windows compare on
their literal ambient overlap. -/
theorem indexed_mixed_trees_overlap {n : ℕ} {X : CMfd.{0} n}
    {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (V : ι → ClosedIrreducibleAnalyticSubvariety n X)
    (hDim : ∀ a, (V a).dim < n)
    (hDistinct : ∀ a b, a ≠ b → ¬ (V a).carrier ⊆ (V b).carrier)
    (D : κ → Set X) (s₁ s₂ : Finset ι) (r₁ r₂ : Finset κ) (U₁ U₂ : Opens X)
    (hs₁ : ∀ i, ((V i).carrier ∩ (U₁ : Set X)).Nonempty → i ∈ s₁)
    (hs₂ : ∀ i, ((V i).carrier ∩ (U₂ : Set X)).Nonempty → i ∈ s₂)
    (hr₁ : ∀ i, (D i ∩ (U₁ : Set X)).Nonempty → i ∈ r₁)
    (hr₂ : ∀ i, (D i ∩ (U₂ : Set X)).Nonempty → i ∈ r₂)
    {Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower (CMfd.of (n := n) U₁) Y₁)
    (T₂ : BlowupTower (CMfd.of (n := n) U₂) Y₂)
    (Ef₁ : List (Set Y₁)) (Ef₂ : List (Set Y₂))
    (hTree₁ : CanonicalMixedSeparation (((r₁.sort (· ≤ ·)).map D).map ((Subtype.val : U₁ → X) ⁻¹' ·))
      ((s₁.sort (· ≤ ·)).map (fun a => ((Subtype.val : U₁ → X) ⁻¹' (V a).carrier,(V a).dim))) T₁ Ef₁)
    (hTree₂ : CanonicalMixedSeparation (((r₂.sort (· ≤ ·)).map D).map ((Subtype.val : U₂ → X) ⁻¹' ·))
      ((s₂.sort (· ≤ ·)).map (fun a => ((Subtype.val : U₂ → X) ⁻¹' (V a).carrier,(V a).dim))) T₂ Ef₂)
    (hOver₁ : CentresOver ((Subtype.val : U₁ → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s₁.sort (· ≤ ·)).length => V ((s₁.sort (· ≤ ·)).get j))) T₁)
    (hOver₂ : CentresOver ((Subtype.val : U₂ → X) ⁻¹'
      mixedBadLocus (fun j : Fin (s₂.sort (· ≤ ·)).length => V ((s₂.sort (· ≤ ·)).get j))) T₂) :
    let W₁ := nestedOpens U₁ (U₁ ⊓ U₂)
    let W₂ := nestedOpens U₂ (U₁ ⊓ U₂)
    ∃ η : CMfd.of (n := n) (openPreimage T₁ W₁) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T₂ W₂),
      ∀ z, ((T₂.proj (η z).val : U₂) : X) = ((T₁.proj z.val : U₁) : X) := by
  obtain ⟨η,hη,_⟩ := indexed_mixed_trees_overlap_with_boundary V hDim hDistinct D s₁ s₂ r₁ r₂ U₁ U₂ hs₁ hs₂ hr₁ hr₂ T₁ T₂ Ef₁ Ef₂ hTree₁ hTree₂ hOver₁ hOver₂
  exact ⟨η,hη⟩

end
end Hironaka.HironakaG3IndexedMixedOverlap
