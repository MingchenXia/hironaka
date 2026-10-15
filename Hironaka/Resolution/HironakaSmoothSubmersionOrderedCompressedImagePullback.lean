/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaNormalCrossingsOrderedChoiceOpenCompression

/-!
Actual cross-dimensional matched/silent tower traces for the ordered marking-one
monomial procedures. Complete mathematical proofs precede Lean in Mathematics.tex.
All-head target globalization outside the literal image restriction remains open.
Formal registration, native builds and publication are pending root recovery.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOrderedCompressedImagePullback
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupRestrictOpen
  BlowupTowerIsomorphism HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaNormalCrossingsOrderedChoiceComparison HironakaNormalCrossingsOrderedOpenTrace
  HironakaNormalCrossingsOrderedChoiceOpenCompression HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionOrderedImageTrace HironakaSmoothSubmersionOrderedMonomialProcedure
  HironakaNormalCrossingsOrderedMonomialTail HironakaNormalCrossingsFiniteMarkedCompletion
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings HironakaSmoothSubmersionCoefficientIdeals
  GermIdealPullbackCalculus IdealWeightPowers
noncomputable section
variable {n m : ℕ}

/-- A genuine smooth trace retains each actual target head, omitting only empty inverse-image centres. -/
inductive IsSmoothTowerTrace {A : CMfd.{u} n} {B : CMfd.{u} m} (f : B → A) :
    {D' : CMfd.{u} m} → {D : CMfd.{u} n} → BlowupTower B D' → BlowupTower A D →
      (D' → D) → Prop
  | refl (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
      IsSmoothTowerTrace f .refl .refl f
  | matched {D' : CMfd.{u} m} {D : CMfd.{u} n} {Z' : CMfd.{u} m} {Z : CMfd.{u} n}
      {T' : BlowupTower B D'} {T : BlowupTower A D} {g : D' → D}
      (h : IsSmoothTowerTrace f T' T g) {C' : Set D'} {π' : Z' → D'}
      (hπ' : IsBlowupAlong m C' π') {C : Set D} {π : Z → D}
      (hπ : IsBlowupAlong n C π) (g₁ : Z' → Z)
      (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g₁)
      (hcomm : ∀ x, π (g₁ x) = g (π' x)) (hC : g ⁻¹' C = C')
      (hcart : HolomorphicSquarePullback g g₁ π' π) :
      IsSmoothTowerTrace f (.step T' C' π' hπ') (.step T C π hπ) g₁
  | silent {D' : CMfd.{u} m} {D Z : CMfd.{u} n}
      {T' : BlowupTower B D'} {T : BlowupTower A D} {g : D' → D}
      (h : IsSmoothTowerTrace f T' T g) {C : Set D} {π : Z → D}
      (hπ : IsBlowupAlong n C π) (g₁ : D' → Z)
      (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g₁)
      (hcomm : ∀ x, π (g₁ x) = g x) (hC : g ⁻¹' C = ∅)
      (hcart : HolomorphicSquarePullback g g₁ (id : D' → D') π) :
      IsSmoothTowerTrace f T' (.step T C π hπ) g₁

theorem IsSmoothTowerTrace.isSubmersion {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerTrace f T' T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g := by
  cases h with
  | refl hf => exact hf
  | matched _ _ _ _ hg _ _ _ => exact hg
  | silent _ _ _ hg _ _ _ => exact hg

theorem IsSmoothTowerTrace.length_le {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerTrace f T' T g) : T'.length ≤ T.length := by
  induction h with
  | refl => exact le_rfl
  | matched _ _ _ _ _ _ _ _ ih => exact Nat.add_le_add_right ih 1
  | silent _ _ _ _ _ _ _ ih => exact ih.trans (Nat.le_add_right _ _)

theorem IsSmoothTowerTrace.proj_comm {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerTrace f T' T g) : ∀ x, T.proj (g x) = f (T'.proj x) := by
  induction h with
  | refl => exact fun _ => rfl
  | @matched D' D Z' Z T' T g h C' π' hπ' C π hπ g₁ hg hc hC hcart ih =>
    intro x
    change T.proj (π (g₁ x)) = f (T'.proj (π' x))
    rw [hc]
    exact ih _
  | @silent D' D Z T' T g h C π hπ g₁ hg hc hC hcart ih =>
    intro x
    change T.proj (π (g₁ x)) = f (T'.proj x)
    rw [hc]
    exact ih _

theorem IsSmoothTowerTrace.append {A D Z : CMfd.{u} n} {B D' Z' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {k : Z' → Z} {T' : BlowupTower B D'} {T : BlowupTower A D}
    {S' : BlowupTower D' Z'} {S : BlowupTower D Z}
    (h : IsSmoothTowerTrace f T' T g) (hs : IsSmoothTowerTrace g S' S k) :
    IsSmoothTowerTrace f (T'.append S') (T.append S) k := by
  induction hs with
  | refl => exact h
  | matched _ hπ' hπ g₁ hg hc hC hcart ih =>
    exact IsSmoothTowerTrace.matched ih hπ' hπ g₁ hg hc hC hcart
  | silent _ hπ g₁ hg hc hC hcart ih =>
    exact IsSmoothTowerTrace.silent ih hπ g₁ hg hc hC hcart

/-- A silent real target head never consumes a source head. -/
theorem IsSmoothTowerTrace.head {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerTrace f T' T g) (j : ℕ) :
    ∃ i : ℕ, ∃ k : (split T' i).1 → (split T j).1,
      IsSmoothTowerTrace f (head T' i) (head T j) k := by
  induction h generalizing j with
  | refl hf => cases j <;> exact ⟨0,_,IsSmoothTowerTrace.refl hf⟩
  | matched h hπ' hπ g₁ hg hc hC hcart ih =>
    cases j with
    | zero => exact ⟨0,g₁,IsSmoothTowerTrace.matched h hπ' hπ g₁ hg hc hC hcart⟩
    | succ j =>
      obtain ⟨i,k,hk⟩ := ih j
      exact ⟨i+1,k,hk⟩
  | @silent D' D Z T' T g h C π hπ g₁ hg hc hC hcart ih =>
    cases j with
    | zero => cases T' <;> exact ⟨0,g₁,IsSmoothTowerTrace.silent h hπ g₁ hg hc hC hcart⟩
    | succ j => exact ih j

theorem IsSmoothTowerTrace.universal {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerTrace f T' T g) : HolomorphicSquarePullback f g T'.proj T.proj := by
  induction h with
  | refl =>
    exact holomorphicSquarePullback_conjugate (Diffeomorph.refl _ A ∞) (Diffeomorph.refl _ B ∞) f
  | @matched D' D Z' Z T' T g h C' π' hπ' C π hπ g₁ hg hc hC hcart ih =>
    intro ℓ P u v hu hv hcone
    obtain ⟨w₀,hw₀,huniq₀⟩ := ih ℓ P u (π ∘ v) hu (hπ.contMDiff.comp hv) hcone
    obtain ⟨w,hw,huniq⟩ := hcart ℓ P w₀ v hw₀.1 hv hw₀.2.2
    refine ⟨w,⟨hw.1,?_,hw.2.2⟩,?_⟩
    · intro x
      change T'.proj (π' (w x)) = u x
      rw [hw.2.1]
      exact hw₀.2.1 x
    · intro z hz
      have hmid : (π' ∘ z) = w₀ := huniq₀ _ ⟨hπ'.contMDiff.comp hz.1,hz.2.1,by
        intro x
        change g (π' (z x)) = π (v x)
        rw [← hc,hz.2.2]⟩
      exact huniq z ⟨hz.1,fun x => congrFun hmid x,hz.2.2⟩
  | @silent D' D Z T' T g h C π hπ g₁ hg hc hC hcart ih =>
    intro ℓ P u v hu hv hcone
    obtain ⟨w₀,hw₀,huniq₀⟩ := ih ℓ P u (π ∘ v) hu (hπ.contMDiff.comp hv) hcone
    obtain ⟨w,hw,huniq⟩ := hcart ℓ P w₀ v hw₀.1 hv hw₀.2.2
    refine ⟨w,⟨hw.1,?_,hw.2.2⟩,?_⟩
    · intro x
      have hwx : w x = w₀ x := hw.2.1 x
      rw [hwx]
      exact hw₀.2.1 x
    · intro z hz
      have hmid : z = w₀ := huniq₀ _ ⟨hz.1,hz.2.1,by
        intro x
        change g (z x) = π (v x)
        rw [← hc,hz.2.2]⟩
      exact huniq z ⟨hz.1,fun x => congrFun hmid x,hz.2.2⟩

section TargetTransport
variable {A A' D D' : CMfd.{u} n} {B Z : CMfd.{u} m}

/-- Actual target biholomorphisms transport genuine holomorphic square universals. -/
theorem holomorphicSquarePullback_target_transport
    (a : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (b : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D)
    {f : B → A} {g : Z → D} {π' : Z → B} {π : D → A} {ρ : D' → A'}
    (hcart : HolomorphicSquarePullback f g π' π)
    (hc : ∀ x, π (b x) = a (ρ x)) :
    HolomorphicSquarePullback (a.symm ∘ f) (b.symm ∘ g) π' ρ := by
  intro ℓ P u v hu hv hcone
  have hcone' : ∀ x, f (u x) = π ((b ∘ v) x) := by
    intro x
    rw [Function.comp_apply,hc,← hcone]
    exact (a.apply_symm_apply _).symm
  obtain ⟨w,hw,huniq⟩ := hcart ℓ P u (b ∘ v) hu (b.contMDiff.comp hv) hcone'
  refine ⟨w,⟨hw.1,hw.2.1,?_⟩,?_⟩
  · intro x
    change b.symm (g (w x)) = v x
    rw [hw.2.2]
    exact b.symm_apply_apply _
  · intro z hz
    apply huniq z
    refine ⟨hz.1,hz.2.1,?_⟩
    intro x
    apply b.symm.injective
    exact (hz.2.2 x).trans (b.symm_apply_apply (v x)).symm
end TargetTransport

section ActualTraceComposition
variable {A₀ A D₀ D : CMfd.{u} n} {B V : CMfd.{u} m}

/-- Real all-head compression and real stage pullback internally compose into a genuine smooth trace. -/
theorem smoothTrace_of_compression_pullback
    {Φ : A₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A}
    {R : BlowupTower A₀ D₀} {S : BlowupTower A D}
    {χ : D₀ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D}
    {f : B → A} {T : BlowupTower B V} {g : V → D}
    (hc : IsStageCompression Φ R S χ) (hp : IsSmoothTowerPullback f T S g) :
    IsSmoothTowerTrace (Φ.symm ∘ f) T R (χ.symm ∘ g) := by
  induction hc generalizing V with
  | refl =>
    cases hp with
    | refl hf _ =>
      exact IsSmoothTowerTrace.refl
        (isSubmersion_conjugate Φ (Diffeomorph.refl _ B ∞) hf)
  | @matched Y₀ Y Z₀ Z R S χ hc C₀ π₀ hπ₀ C π hπ χ₁ hcomm hC ih =>
    cases hp with
    | step hp hπ' hπ g₁ hg hs hcomm' hC' hcart =>
      rename_i V₀ T₀ C' π' g₀
      refine IsSmoothTowerTrace.matched (ih hp) hπ' hπ₀ (χ₁.symm ∘ g)
        (isSubmersion_conjugate χ₁ (Diffeomorph.refl _ _ ∞) hg) ?_ ?_
        (holomorphicSquarePullback_target_transport χ χ₁ hcart hcomm)
      · intro x
        apply χ.injective
        change χ (π₀ (χ₁.symm (g x))) = χ (χ.symm (g₀ (π' x)))
        rw [← hcomm,χ₁.apply_symm_apply,χ.apply_symm_apply,hcomm']
      · rw [← hC]
        ext x
        simp only [mem_preimage,Function.comp_apply,χ.apply_symm_apply]
        exact Set.ext_iff.mp hC' x
  | @silent Y₀ Y Z₀ R S χ hc π₀ hπ₀ χ₁ hcomm ih =>
    let a := χ₁.trans χ.symm
    have ha : (a : Z₀ → Y₀) = π₀ := by
      funext z
      change χ.symm (χ₁ z) = π₀ z
      rw [hcomm]
      exact χ.symm_apply_apply _
    have hcart : HolomorphicSquarePullback (χ.symm ∘ g) (χ₁.symm ∘ g)
        (id : V → V) π₀ := by
      have h := holomorphicSquarePullback_conjugate a
        (Diffeomorph.refl 𝓘(ℂ, ComplexModel m) V ∞) (χ.symm ∘ g)
      rw [ha] at h
      have hl : (a.symm ∘ (χ.symm ∘ g) ∘ (Diffeomorph.refl 𝓘(ℂ, ComplexModel m) V ∞)) = χ₁.symm ∘ g := by
        funext x
        change χ₁.symm (χ (χ.symm (g x))) = χ₁.symm (g x)
        rw [χ.apply_symm_apply]
      rw [hl] at h
      exact h
    refine IsSmoothTowerTrace.silent (ih hp) hπ₀ (χ₁.symm ∘ g)
      (isSubmersion_conjugate χ₁ (Diffeomorph.refl _ V ∞) hp.isSubmersion) ?_ ?_ hcart
    · intro x
      apply χ.injective
      change χ (π₀ (χ₁.symm (g x))) = χ (χ.symm (g x))
      rw [← hcomm,χ₁.apply_symm_apply,χ.apply_symm_apply]
    · exact preimage_empty
end ActualTraceComposition

section OriginalInput
variable {A : CMfd.{u} n} {B : CMfd.{u} m} {f : B → A}

/-- The source procedure is independently generated on the literal whole image-factor pullback. -/
def imageSourceProcedure (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) : ChosenOutput B :=
  chosenProcedure α (traceCount (Subtype.val : imageOpen hf → A) n q F) B
    (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
    (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))

/-- Both actual independent procedures use the ENTIRE genuine original source input. -/
theorem imageSourceProcedure_input
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) :
    pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F) =
      pulledWeights f F := imageFactor_weights hf F

/-- A real compressed smooth lift is constructed from two independently produced genuine comparisons. -/
def compressedImageLift (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (q : ℕ) (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageSourceProcedure α q hf F hF).D →
      CMfd.of (n := n) (openPreimage (chosenProcedure β q A F hF).T (imageOpen hf)) :=
  (chosenOpenCompression β γ q (imageOpen hf) F hF).symm ∘
    actualLift (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
      α γ (traceCount (Subtype.val : imageOpen hf → A) n q F) (imageFactor hf)
      (imageFactor_isSubmersion hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)
      (image_weights_isSNCDivisor hf F hF)

/-- Genuine original nonsurjective submersion and SNC data internally produce the ALL-HEAD cross-dimensional trace. -/
theorem compressedImageLift_actual_trace
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSmoothTowerTrace (imageFactor hf) (imageSourceProcedure α q hf F hF).T
      (restrict (imageOpen hf) (chosenProcedure β q A F hF).T)
      (compressedImageLift β γ α q hf F hF) := by
  have h := smoothTrace_of_compression_pullback
    (chosenOpenCompression_spec β γ q (imageOpen hf) F hF)
    (chosenProcedure_stage_pullback (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
      α γ (traceCount (Subtype.val : imageOpen hf → A) n q F)
      (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
      (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF))
  simpa only [Diffeomorph.symm_refl,Diffeomorph.coe_refl,Function.id_comp,
    imageSourceProcedure,compressedImageLift] using h

theorem compressedImageLift_isSubmersion
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (compressedImageLift β γ α q hf F hF) :=
  (compressedImageLift_actual_trace β γ α q hf F hF).isSubmersion

theorem compressedImageLift_proj_comm
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (restrict (imageOpen hf) (chosenProcedure β q A F hF).T).proj
        (compressedImageLift β γ α q hf F hF x) =
      imageFactor hf ((imageSourceProcedure α q hf F hF).T.proj x) :=
  (compressedImageLift_actual_trace β γ α q hf F hF).proj_comm

theorem compressedImageLift_universal
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback (imageFactor hf) (compressedImageLift β γ α q hf F hF)
      (imageSourceProcedure α q hf F hF).T.proj
      (restrict (imageOpen hf) (chosenProcedure β q A F hF).T).proj :=
  (compressedImageLift_actual_trace β γ α q hf F hF).universal

/-- Every original literal restricted global head has its own real source head and actual lift. -/
theorem compressedImageLift_all_heads
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ∃ i : ℕ, ∃ k : (split (imageSourceProcedure α q hf F hF).T i).1 →
        (split (restrict (imageOpen hf) (chosenProcedure β q A F hF).T) j).1,
      IsSmoothTowerTrace (imageFactor hf) (head (imageSourceProcedure α q hf F hF).T i)
        (head (restrict (imageOpen hf) (chosenProcedure β q A F hF).T) j) k :=
  (compressedImageLift_actual_trace β γ α q hf F hF).head j

private theorem restricted_global_projection_injective
    (β : CartierBlowupChoices.{u} n) (q : ℕ) (U : Opens A)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Function.Injective (restrict U (chosenProcedure β q A F hF).T).proj := by
  intro x y he
  apply Subtype.ext
  apply (chosenProcedure β q A F hF).back.injective
  change (chosenProcedure β q A F hF).back x.val = (chosenProcedure β q A F hF).back y.val
  have hv := congrArg (Subtype.val : U → A) he
  rw [proj_restrict,proj_restrict] at hv
  rw [ChosenOutput.proj_eq]
  exact hv

/-- Genuine compatible projection cones have exactly the actual produced terminal lift. -/
theorem compressedImageLift_unique
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (k : (imageSourceProcedure α q hf F hF).D →
      CMfd.of (n := n) (openPreimage (chosenProcedure β q A F hF).T (imageOpen hf)))
    (hk : ∀ x, (restrict (imageOpen hf) (chosenProcedure β q A F hF).T).proj (k x) =
      imageFactor hf ((imageSourceProcedure α q hf F hF).T.proj x)) :
    k = compressedImageLift β γ α q hf F hF := by
  funext x
  apply restricted_global_projection_injective β q (imageOpen hf) F hF
  rw [hk,compressedImageLift_proj_comm]

/-- Actual projection uniqueness eliminates every primitive intermediate image choice. -/
theorem compressedImageLift_intermediate_choice
    (β γ₁ γ₂ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    compressedImageLift β γ₁ α q hf F hF = compressedImageLift β γ₂ α q hf F hF :=
  compressedImageLift_unique β γ₂ α q hf F hF _ (compressedImageLift_proj_comm β γ₁ α q hf F hF)

/-- The literal terminal inclusion gives the genuine SAME unrestricted global projection square. -/
theorem compressedImageLift_global_proj_comm
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (chosenProcedure β q A F hF).T.proj (compressedImageLift β γ α q hf F hF x).val =
      f ((imageSourceProcedure α q hf F hF).T.proj x) := by
  intro x
  have h := congrArg (Subtype.val : imageOpen hf → A) (compressedImageLift_proj_comm β γ α q hf F hF x)
  rw [proj_restrict] at h
  exact h

/-- The full terminal map is the actual original global conjugate lift, not an arbitrary comparison. -/
theorem compressedImageLift_global_map
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (Subtype.val : openPreimage (chosenProcedure β q A F hF).T (imageOpen hf) →
      (chosenProcedure β q A F hF).D) ∘ compressedImageLift β γ α q hf F hF =
      (chosenProcedure β q A F hF).back.symm ∘ f ∘ (imageSourceProcedure α q hf F hF).back := by
  funext x
  apply (chosenProcedure β q A F hF).back.injective
  change (chosenProcedure β q A F hF).back (compressedImageLift β γ α q hf F hF x).val =
    (chosenProcedure β q A F hF).back ((chosenProcedure β q A F hF).back.symm
      (f ((imageSourceProcedure α q hf F hF).back x)))
  rw [Diffeomorph.apply_symm_apply,(chosenProcedure β q A F hF).proj_eq,
    (imageSourceProcedure α q hf F hF).proj_eq]
  exact compressedImageLift_global_proj_comm β γ α q hf F hF x

def sourceImageMarked (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (imageSourceProcedure α q hf F hF).D :=
  geoTransformAlong
    (monomialMarkedIdeal (n := m)
      ((pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)).map Prod.fst)
      (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
    (imageSourceProcedure α q hf F hF).T

/-- The genuine surjective image-factor producer internally gives the entire source control. -/
theorem sourceImageMarked_whole_image
    (γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    sourceImageMarked α q hf F hF =
      markedPullback (m := m)
        (actualLift (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
          α γ (traceCount (Subtype.val : imageOpen hf → A) n q F) (imageFactor hf)
          (imageFactor_isSubmersion hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)
          (image_weights_isSNCDivisor hf F hF))
        (localOpenMarked γ q (imageOpen hf) F hF) := by
  have h := actualLift_whole_controlled_marked (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
    α γ (traceCount (Subtype.val : imageOpen hf → A) n q F)
    (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)
  rw [markedPullback_indexed_dictionary (imageFactor_isSubmersion hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)] at h
  exact h

/-- The true raw entire ideal is internally coherent, including after every literal restricted empty step. -/
theorem rawImageMarked_coherent
    (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (rawRestrictedMarked β q (imageOpen hf) F hF).ideal.IsCoherent := by
  rw [rawRestrictedMarked_eq]
  exact isCoherent_pullback contMDiff_subtype_val (chosen_stage_coherent β q F hF)

/-- Actual compressed lift and true creation-event mask define the entire retained raw record. -/
def compressedRetainedMarked
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (imageSourceProcedure α q hf F hF).D :=
  { markedPullback (m := m) (compressedImageLift β γ α q hf F hF)
      (rawRestrictedMarked β q (imageOpen hf) F hF) with
    E := ((List.range F.length) ++ newHistoryTrace (Subtype.val : imageOpen hf → A) n q F).map
      (fun i => (compressedImageLift β γ α q hf F hF) ⁻¹'
        (rawRestrictedMarked β q (imageOpen hf) F hF).E.getD i ∅) }

/-- Whole genuine controlled source records equal the true compressed pullback, with all retained history literal. -/
theorem sourceImageMarked_whole_raw
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    sourceImageMarked α q hf F hF = compressedRetainedMarked β γ α q hf F hF := by
  rw [sourceImageMarked_whole_image γ α q hf F hF,localOpenMarked_eq_retained β γ q (imageOpen hf) F hF]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change _ ⁻¹' (_ ⁻¹' _) = (_ ∘ _) ⁻¹' _
    rfl
  · change List.map _ (List.map _ _) = List.map _ _
    rw [List.map_map]
    rfl
  · change GermIdeal.pullback (m := m) _ (GermIdeal.pullback (m := n) _ _) =
      GermIdeal.pullback (m := m) (_ ∘ _) _
    exact (coherent_pullback_comp (chosenOpenCompression β γ q (imageOpen hf) F hF).symm.contMDiff
      (actualLift_isSubmersion (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
        α γ (traceCount (Subtype.val : imageOpen hf → A) n q F) (imageFactor_isSubmersion hf)
        (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)).contMDiff
      _ (rawImageMarked_coherent β q hf F hF)).symm
  · rfl

/-- The genuine independently computed source OWN initial coefficient sum is retained literally. -/
def completedImageSourceProcedure (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) : ChosenOutput B :=
  chosenProcedure α
    (coefficientSum (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))) B
    (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
    (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))

def completedCompressedImageLift
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedImageSourceProcedure α hf F hF).D →
      CMfd.of (n := n) (openPreimage (chosenProcedure β (coefficientSum F) A F hF).T (imageOpen hf)) :=
  (completedChosenOpenCompression β γ (imageOpen hf) F hF).symm ∘
    completedActualLift (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
      α γ (imageFactor hf) (imageFactor_isSubmersion hf)
      (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)

/-- BOTH true OWN completions yield the genuine ALL-HEAD cross-dimensional marked-one image trace. -/
theorem completedCompressedImageLift_actual_trace
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSmoothTowerTrace (imageFactor hf) (completedImageSourceProcedure α hf F hF).T
      (restrict (imageOpen hf) (chosenProcedure β (coefficientSum F) A F hF).T)
      (completedCompressedImageLift β γ α hf F hF) := by
  have h := smoothTrace_of_compression_pullback
    (completedChosenOpenCompression_spec β γ (imageOpen hf) F hF)
    (completed_chosenProcedure_stage_pullback (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
      α γ (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
      (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF))
  simpa only [Diffeomorph.symm_refl,Diffeomorph.coe_refl,Function.id_comp,
    completedImageSourceProcedure,completedCompressedImageLift] using h

theorem completedCompressedImageLift_isSubmersion
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (completedCompressedImageLift β γ α hf F hF) :=
  (completedCompressedImageLift_actual_trace β γ α hf F hF).isSubmersion

theorem completedCompressedImageLift_proj_comm
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (restrict (imageOpen hf) (chosenProcedure β (coefficientSum F) A F hF).T).proj
        (completedCompressedImageLift β γ α hf F hF x) =
      imageFactor hf ((completedImageSourceProcedure α hf F hF).T.proj x) :=
  (completedCompressedImageLift_actual_trace β γ α hf F hF).proj_comm

theorem completedCompressedImageLift_universal
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback (imageFactor hf) (completedCompressedImageLift β γ α hf F hF)
      (completedImageSourceProcedure α hf F hF).T.proj
      (restrict (imageOpen hf) (chosenProcedure β (coefficientSum F) A F hF).T).proj :=
  (completedCompressedImageLift_actual_trace β γ α hf F hF).universal

theorem completedImageSourceProcedure_length
    (γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedImageSourceProcedure α hf F hF).T.length =
      traceCount (Subtype.val : imageOpen hf → A) n (coefficientSum F) F :=
  (completed_chosenProcedure_length_eq (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
    α γ (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)).trans
      (completed_chosen_open_length γ (imageOpen hf) F hF)

def completedSourceImageMarked (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (completedImageSourceProcedure α hf F hF).D :=
  geoTransformAlong
    (monomialMarkedIdeal (n := m)
      ((pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)).map Prod.fst)
      (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
    (completedImageSourceProcedure α hf F hF).T

theorem completedSourceImageMarked_unit (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedSourceImageMarked α hf F hF).ideal =
      unitIdeal m (completedImageSourceProcedure α hf F hF).D :=
  chosenProcedure_ideal_eq_unit α _
    (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))

theorem completedImageSourceProcedure_resolution (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoResolution
      (monomialMarkedIdeal (n := m)
        ((pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)).map Prod.fst)
        (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
      (completedImageSourceProcedure α hf F hF).T :=
  chosenProcedure_isGeoResolution α _
    (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))

theorem completedSourceImageMarked_whole_image
    (γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedSourceImageMarked α hf F hF =
      markedPullback (m := m)
        (completedActualLift (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
          α γ (imageFactor hf) (imageFactor_isSubmersion hf)
          (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF))
        (completedLocalOpenMarked γ (imageOpen hf) F hF) := by
  have h := completedActualLift_whole_controlled_marked (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
    α γ (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)
  rw [markedPullback_indexed_dictionary (imageFactor_isSubmersion hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)] at h
  exact h

def completedCompressedRetainedMarked
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (completedImageSourceProcedure α hf F hF).D :=
  { markedPullback (m := m) (completedCompressedImageLift β γ α hf F hF)
      (rawRestrictedMarked β (coefficientSum F) (imageOpen hf) F hF) with
    E := ((List.range F.length) ++ newHistoryTrace (Subtype.val : imageOpen hf → A) n (coefficientSum F) F).map
      (fun i => (completedCompressedImageLift β γ α hf F hF) ⁻¹'
        (rawRestrictedMarked β (coefficientSum F) (imageOpen hf) F hF).E.getD i ∅) }

/-- Whole OWN controlled source record has its genuine raw pullback and literal creation-history mask. -/
theorem completedSourceImageMarked_whole_raw
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedSourceImageMarked α hf F hF = completedCompressedRetainedMarked β γ α hf F hF := by
  rw [completedSourceImageMarked_whole_image γ α hf F hF,
    completedLocalOpenMarked_eq_retained β γ (imageOpen hf) F hF]
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · change _ ⁻¹' (_ ⁻¹' _) = (_ ∘ _) ⁻¹' _
    rfl
  · change List.map _ (List.map _ _) = List.map _ _
    rw [List.map_map]
    rfl
  · change GermIdeal.pullback (m := m) _ (GermIdeal.pullback (m := n) _ _) =
      GermIdeal.pullback (m := m) (_ ∘ _) _
    exact (coherent_pullback_comp (completedChosenOpenCompression β γ (imageOpen hf) F hF).symm.contMDiff
      (completedActualLift_isSubmersion (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
        α γ (imageFactor_isSubmersion hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)
        (image_weights_isSNCDivisor hf F hF)).contMDiff
      _ (rawImageMarked_coherent β (coefficientSum F) hf F hF)).symm
  · rfl

theorem imageSourceProcedure_length
    (γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageSourceProcedure α q hf F hF).T.length =
      traceCount (Subtype.val : imageOpen hf → A) n q F :=
  (chosenProcedure_stage_pullback (A := CMfd.of (n := n) (imageOpen hf)) (B := B)
    α γ (traceCount (Subtype.val : imageOpen hf → A) n q F)
    (imageFactor_isSubmersion hf) (imageFactor_surjective hf)
    (pulledWeights (Subtype.val : imageOpen hf → A) F) (image_weights_isSNCDivisor hf F hF)).length_eq.trans
      (chosen_open_length γ q (imageOpen hf) F hF)

theorem completedCompressedImageLift_all_heads
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ∃ i : ℕ, ∃ k : (split (completedImageSourceProcedure α hf F hF).T i).1 →
        (split (restrict (imageOpen hf) (chosenProcedure β (coefficientSum F) A F hF).T) j).1,
      IsSmoothTowerTrace (imageFactor hf) (head (completedImageSourceProcedure α hf F hF).T i)
        (head (restrict (imageOpen hf) (chosenProcedure β (coefficientSum F) A F hF).T) j) k :=
  (completedCompressedImageLift_actual_trace β γ α hf F hF).head j

theorem completedCompressedImageLift_unique
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (k : (completedImageSourceProcedure α hf F hF).D →
      CMfd.of (n := n) (openPreimage (chosenProcedure β (coefficientSum F) A F hF).T (imageOpen hf)))
    (hk : ∀ x, (restrict (imageOpen hf) (chosenProcedure β (coefficientSum F) A F hF).T).proj (k x) =
      imageFactor hf ((completedImageSourceProcedure α hf F hF).T.proj x)) :
    k = completedCompressedImageLift β γ α hf F hF := by
  funext x
  apply restricted_global_projection_injective β (coefficientSum F) (imageOpen hf) F hF
  rw [hk,completedCompressedImageLift_proj_comm]

theorem completedCompressedImageLift_intermediate_choice
    (β γ₁ γ₂ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedCompressedImageLift β γ₁ α hf F hF = completedCompressedImageLift β γ₂ α hf F hF :=
  completedCompressedImageLift_unique β γ₂ α hf F hF _
    (completedCompressedImageLift_proj_comm β γ₁ α hf F hF)

theorem completedCompressedImageLift_global_proj_comm
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (chosenProcedure β (coefficientSum F) A F hF).T.proj
        (completedCompressedImageLift β γ α hf F hF x).val =
      f ((completedImageSourceProcedure α hf F hF).T.proj x) := by
  intro x
  have h := congrArg (Subtype.val : imageOpen hf → A)
    (completedCompressedImageLift_proj_comm β γ α hf F hF x)
  rw [proj_restrict] at h
  exact h

theorem completedCompressedImageLift_global_map
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (Subtype.val : openPreimage (chosenProcedure β (coefficientSum F) A F hF).T (imageOpen hf) →
      (chosenProcedure β (coefficientSum F) A F hF).D) ∘ completedCompressedImageLift β γ α hf F hF =
      (chosenProcedure β (coefficientSum F) A F hF).back.symm ∘ f ∘
        (completedImageSourceProcedure α hf F hF).back := by
  funext x
  apply (chosenProcedure β (coefficientSum F) A F hF).back.injective
  change (chosenProcedure β (coefficientSum F) A F hF).back
      (completedCompressedImageLift β γ α hf F hF x).val =
    (chosenProcedure β (coefficientSum F) A F hF).back
      ((chosenProcedure β (coefficientSum F) A F hF).back.symm
        (f ((completedImageSourceProcedure α hf F hF).back x)))
  rw [Diffeomorph.apply_symm_apply,(chosenProcedure β (coefficientSum F) A F hF).proj_eq,
    (completedImageSourceProcedure α hf F hF).proj_eq]
  exact completedCompressedImageLift_global_proj_comm β γ α hf F hF x

/-- Real source and restricted global choice comparisons commute with the actual compressed smooth lift. -/
theorem compressedImageLift_choice_cocycle
    (β₁ β₂ γ₁ γ₂ : CartierBlowupChoices.{u} n) (α₁ α₂ : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (restrictedChoiceComparison β₁ β₂ q (imageOpen hf) F hF : _ → _) ∘
      compressedImageLift β₁ γ₁ α₁ q hf F hF =
    compressedImageLift β₂ γ₂ α₂ q hf F hF ∘
      (choiceComparison (A := B) α₁ α₂ (traceCount (Subtype.val : imageOpen hf → A) n q F)
        (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
        (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF)) : _ → _) := by
  funext x
  let ψ := choiceComparison (A := B) α₁ α₂ (traceCount (Subtype.val : imageOpen hf → A) n q F)
    (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
    (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))
  have hs : (imageSourceProcedure α₁ q hf F hF).T.proj x =
      (imageSourceProcedure α₂ q hf F hF).T.proj (ψ x) :=
    (choiceComparison_isTowerIso (A := B) α₁ α₂
      (traceCount (Subtype.val : imageOpen hf → A) n q F)
      (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
      (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))).proj_comm x
  apply restricted_global_projection_injective β₂ q (imageOpen hf) F hF
  change (restrict (imageOpen hf) (chosenProcedure β₂ q A F hF).T).proj
      (restrictedChoiceComparison β₁ β₂ q (imageOpen hf) F hF
        (compressedImageLift β₁ γ₁ α₁ q hf F hF x)) =
    (restrict (imageOpen hf) (chosenProcedure β₂ q A F hF).T).proj
      (compressedImageLift β₂ γ₂ α₂ q hf F hF (ψ x))
  calc
    _ = (restrict (imageOpen hf) (chosenProcedure β₁ q A F hF).T).proj
        (compressedImageLift β₁ γ₁ α₁ q hf F hF x) :=
      (restrictedChoiceComparison_proj_comm β₁ β₂ q (imageOpen hf) F hF _).symm
    _ = imageFactor hf ((imageSourceProcedure α₁ q hf F hF).T.proj x) :=
      compressedImageLift_proj_comm β₁ γ₁ α₁ q hf F hF x
    _ = imageFactor hf ((imageSourceProcedure α₂ q hf F hF).T.proj (ψ x)) := congrArg _ hs
    _ = _ := (compressedImageLift_proj_comm β₂ γ₂ α₂ q hf F hF (ψ x)).symm

theorem completedCompressedImageLift_choice_cocycle
    (β₁ β₂ γ₁ γ₂ : CartierBlowupChoices.{u} n) (α₁ α₂ : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (restrictedChoiceComparison β₁ β₂ (coefficientSum F) (imageOpen hf) F hF : _ → _) ∘
      completedCompressedImageLift β₁ γ₁ α₁ hf F hF =
    completedCompressedImageLift β₂ γ₂ α₂ hf F hF ∘
      (choiceComparison (A := B) α₁ α₂
        (coefficientSum (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
        (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
        (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF)) : _ → _) := by
  funext x
  let ψ := choiceComparison (A := B) α₁ α₂
    (coefficientSum (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
    (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
    (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))
  have hs : (completedImageSourceProcedure α₁ hf F hF).T.proj x =
      (completedImageSourceProcedure α₂ hf F hF).T.proj (ψ x) :=
    (choiceComparison_isTowerIso (A := B) α₁ α₂
      (coefficientSum (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
      (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
      (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF))).proj_comm x
  apply restricted_global_projection_injective β₂ (coefficientSum F) (imageOpen hf) F hF
  change (restrict (imageOpen hf) (chosenProcedure β₂ (coefficientSum F) A F hF).T).proj
      (restrictedChoiceComparison β₁ β₂ (coefficientSum F) (imageOpen hf) F hF
        (completedCompressedImageLift β₁ γ₁ α₁ hf F hF x)) =
    (restrict (imageOpen hf) (chosenProcedure β₂ (coefficientSum F) A F hF).T).proj
      (completedCompressedImageLift β₂ γ₂ α₂ hf F hF (ψ x))
  calc
    _ = (restrict (imageOpen hf) (chosenProcedure β₁ (coefficientSum F) A F hF).T).proj
        (completedCompressedImageLift β₁ γ₁ α₁ hf F hF x) :=
      (restrictedChoiceComparison_proj_comm β₁ β₂ (coefficientSum F) (imageOpen hf) F hF _).symm
    _ = imageFactor hf ((completedImageSourceProcedure α₁ hf F hF).T.proj x) :=
      completedCompressedImageLift_proj_comm β₁ γ₁ α₁ hf F hF x
    _ = imageFactor hf ((completedImageSourceProcedure α₂ hf F hF).T.proj (ψ x)) := congrArg _ hs
    _ = _ := (completedCompressedImageLift_proj_comm β₂ γ₂ α₂ hf F hF (ψ x)).symm

end OriginalInput

end
end Hironaka.HironakaSmoothSubmersionOrderedCompressedImagePullback
