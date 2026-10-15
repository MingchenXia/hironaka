/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedCompressedImagePullback

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOrderedGlobalTrace
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupRestrictOpen
  HironakaSmoothSubmersionOrderedCompressedImagePullback
  HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaNormalCrossingsOrderedChoiceOpenCompression
  HironakaNormalCrossingsOrderedChoiceComparison
  HironakaSmoothSubmersionOrderedImageTrace HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionOrderedMonomialProcedure HironakaSmoothSubmersionNormalCrossings
  HironakaNormalCrossingsOrderedMonomialTail HironakaNormalCrossingsFiniteMarkedCompletion NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
  HironakaNormalCrossingsOrderedOpenTrace HironakaSmoothSubmersionCoefficientIdeals
noncomputable section
variable {n m : ℕ}

/-- Actual open partial inclusion inverses are holomorphic on their true domain. -/
private theorem opens_inverse_holomorphic {A : CMfd.{u} n}
    (V : TopologicalSpace.Opens A) (hV : Nonempty V) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (V.openPartialHomeomorphSubtypeCoe hV).symm
      (V.openPartialHomeomorphSubtypeCoe hV).target := by
  let e := V.openPartialHomeomorphSubtypeCoe hV
  have hval : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : V → A) ∘ e.symm) e.target := by
    apply contMDiffOn_id.congr
    intro x hx
    exact e.right_inv hx
  intro x hx
  exact (ContMDiffWithinAt.subtypeVal_comp_iff V e.symm e.target x).mp (hval x hx)

/-- A maximal chart on an actual open extends to a genuine maximal ambient chart. -/
private theorem ambientChart_maximal {A : CMfd.{u} n}
    (V : TopologicalSpace.Opens A) (hV : Nonempty V)
    (e : OpenPartialHomeomorph V (ComplexModel n))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ V) :
    (V.openPartialHomeomorphSubtypeCoe hV).symm.trans e ∈
      IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ A := by
  let v := V.openPartialHomeomorphSubtypeCoe hV
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (e ∘ v.symm) (v.target ∩ v.symm ⁻¹' e.source)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      ((opens_inverse_holomorphic V hV).mono inter_subset_left) (fun _ hz => hz.2)
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : V → A) ∘ e.symm) (e.target ∩ e.symm ⁻¹' v.source)
    exact contMDiff_subtype_val.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)

/-- True open inclusions preserve the SAME globally chosen actual submersion complement. -/
theorem isSubmersionOfComplement_val_comp {A : CMfd.{u} n} {B : CMfd.{u} m}
    (V : TopologicalSpace.Opens A) {g : B → V}
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g) :
    Manifold.IsSubmersionOfComplement hg.complement
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : V → A) ∘ g) := by
  intro b
  let h := hg.isSubmersionOfComplement_complement b
  have hV : Nonempty V := ⟨g b⟩
  let v := V.openPartialHomeomorphSubtypeCoe hV
  let c := v.symm.trans h.codChart
  have hv : ∀ a : V, v.symm a.val = a := fun a => v.left_inv (mem_univ a)
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv h.domChart c
  · exact h.mem_domChart_source
  · change (g b).val ∈ v.target ∧ v.symm (g b).val ∈ h.codChart.source
    constructor
    · simp [v]
    · rw [hv]
      exact h.mem_codChart_source
  · exact h.domChart_mem_maximalAtlas
  · exact ambientChart_maximal V hV h.codChart h.codChart_mem_maximalAtlas
  · intro x hx
    change (g x).val ∈ v.target ∧ v.symm (g x).val ∈ h.codChart.source
    constructor
    · simp [v]
    · rw [hv]
      exact h.source_subset_preimage_source hx
  · intro z hz
    have he := h.writtenInCharts hz
    simpa [c,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps,hv] using he

/-- Forgetting the SAME actual complement gives genuine open composite submersion. -/
theorem isSubmersion_val_comp {A : CMfd.{u} n} {B : CMfd.{u} m}
    (V : TopologicalSpace.Opens A) {g : B → V}
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : V → A) ∘ g) :=
  (isSubmersionOfComplement_val_comp V hg).isSubmersion

/-- An arbitrary genuine open inclusion is a submersion, including the empty open. -/
theorem isSubmersion_val {A : CMfd.{u} n} (V : TopologicalSpace.Opens A) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : V → A) :=
  by simpa only [Function.comp_id] using
    (isSubmersion_val_comp (B := CMfd.of (n := n) V) (g := id) V Manifold.IsSubmersion.id)

/-- A true arbitrary blowup restricted to an actual open is a real holomorphic pullback square. -/
theorem holomorphicSquarePullback_restrict {A D : CMfd.{u} n}
    {C : Set A} {π : D → A} (hπ : IsBlowupAlong n C π) (V : TopologicalSpace.Opens A) :
    let W : TopologicalSpace.Opens D := ⟨π ⁻¹' (V : Set A),V.isOpen.preimage hπ.contMDiff.continuous⟩
    HolomorphicSquarePullback (A := A) (D := D) (B := CMfd.of (n := n) V)
      (D' := CMfd.of (n := n) W) (Subtype.val : V → A) (Subtype.val : W → D)
      (fun z : W => (⟨π z.val,z.property⟩ : V)) π := by
  intro W ℓ P a b ha hb hcomm
  have hmem : ∀ x, b x ∈ W := fun x => by
    change π (b x) ∈ (V : Set A)
    rw [← hcomm x]
    exact (a x).property
  refine ⟨fun x => (⟨b x,hmem x⟩ : W),⟨contMDiff_opens_mk hb hmem,?_,?_⟩,?_⟩
  · intro x
    exact Subtype.ext (hcomm x).symm
  · intro x
    rfl
  · intro k hk
    funext x
    exact Subtype.ext (hk.2.2 x)

/-- The real open-square producer composes with an actual matched or silent source square. -/
theorem holomorphicSquarePullback_globalize_restrict {A D : CMfd.{u} n}
    {B D' : CMfd.{u} m} {C : Set A} {π : D → A} (hπ : IsBlowupAlong n C π)
    (V : TopologicalSpace.Opens A)
    (f : B → V)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (g : D' → (⟨π ⁻¹' (V : Set A),V.isOpen.preimage hπ.contMDiff.continuous⟩ : TopologicalSpace.Opens D))
    (π' : D' → B)
    (hcart : HolomorphicSquarePullback (A := CMfd.of (n := n) V)
      (D := CMfd.of (n := n) (⟨π ⁻¹' (V : Set A),V.isOpen.preimage hπ.contMDiff.continuous⟩ : TopologicalSpace.Opens D))
      f g π' (fun z => (⟨π z.val,z.property⟩ : V))) :
    HolomorphicSquarePullback (A := A) (D := D) (B := B) (D' := D')
      ((Subtype.val : V → A) ∘ f) (Subtype.val ∘ g) π' π := by
  intro ℓ P u v hu hv hcomm
  obtain ⟨w₀,hw₀,huniq₀⟩ := holomorphicSquarePullback_restrict hπ V
    ℓ P (f ∘ u) v (hf.comp hu) hv hcomm
  obtain ⟨w,hw,huniq⟩ := hcart ℓ P u w₀ hu hw₀.1 (fun x => (hw₀.2.1 x).symm)
  refine ⟨w,⟨hw.1,hw.2.1,?_⟩,?_⟩
  · intro x
    exact (congrArg Subtype.val (hw.2.2 x)).trans (hw₀.2.2 x)
  · intro k hk
    apply huniq k
    refine ⟨hk.1,hk.2.1,?_⟩
    intro x
    exact Subtype.ext ((hk.2.2 x).trans (hw₀.2.2 x).symm)


/-- Genuine matched open tower geometry, internally produced from actual literal restriction. -/
inductive IsOpenTowerPullback {A B : CMfd.{u} n} :
    (B → A) → {D' D : CMfd.{u} n} → BlowupTower B D' → BlowupTower A D → (D' → D) → Prop
  | refl (U : TopologicalSpace.Opens A)
      (Φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U) :
      IsOpenTowerPullback (Subtype.val ∘ Φ) .refl .refl (Subtype.val ∘ Φ)
  | step {f : B → A} {D' D Z' Z : CMfd.{u} n}
      {R : BlowupTower B D'} {T : BlowupTower A D} {g : D' → D}
      (h : IsOpenTowerPullback f R T g) {C' : Set D'} {π' : Z' → D'}
      (hπ' : IsBlowupAlong n C' π') {C : Set D} {π : Z → D}
      (hπ : IsBlowupAlong n C π) (U : TopologicalSpace.Opens Z)
      (χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) U)
      (hcomm : ∀ x, π (χ x).val = g (π' x)) (hC : g ⁻¹' C = C')
      (hcart : HolomorphicSquarePullback g (Subtype.val ∘ χ) π' π) :
      IsOpenTowerPullback f (.step R C' π' hπ') (.step T C π hπ) (Subtype.val ∘ χ)

/-- True open projection squares compose with actual matched or silent smooth squares. -/
theorem holomorphicSquarePullback_open_comp {A D : CMfd.{u} n} {B E : CMfd.{u} n}
    {P Q : CMfd.{u} m} {a : B → A} {b : E → D} {π : D → A} {ρ : E → B}
    {f : P → B} {g : Q → E} {σ : Q → P}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hb : Function.Injective b)
    (hout : HolomorphicSquarePullback a b ρ π)
    (hin : HolomorphicSquarePullback f g σ ρ) :
    HolomorphicSquarePullback (a ∘ f) (b ∘ g) σ π := by
  intro ℓ X u v hu hv hcomm
  obtain ⟨w₀,hw₀,huniq₀⟩ := hout ℓ X (f ∘ u) v (hf.comp hu) hv hcomm
  obtain ⟨w,hw,huniq⟩ := hin ℓ X u w₀ hu hw₀.1 (fun x => (hw₀.2.1 x).symm)
  refine ⟨w,⟨hw.1,hw.2.1,?_⟩,?_⟩
  · intro x
    exact (congrArg b (hw.2.2 x)).trans (hw₀.2.2 x)
  · intro k hk
    apply huniq k
    refine ⟨hk.1,hk.2.1,?_⟩
    intro x
    exact hb ((hk.2.2 x).trans (hw₀.2.2 x).symm)

/-- Joint genuine geometry induction retains all actual smooth matched/silent heads. -/
theorem smoothTrace_of_open_pullback {A B D E : CMfd.{u} n} {P Q : CMfd.{u} m}
    {a : B → A} {R : BlowupTower B E} {T : BlowupTower A D} {b : E → D}
    {f : P → B} {S : BlowupTower P Q} {g : Q → E}
    (ho : IsOpenTowerPullback a R T b) (hs : IsSmoothTowerTrace f S R g) :
    IsSmoothTowerTrace (a ∘ f) S T (b ∘ g) := by
  induction ho generalizing Q with
  | refl U Φ =>
    cases hs with
    | refl hf =>
      have hc := isSubmersion_conjugate Φ.symm (Diffeomorph.refl _ P ∞) hf
      exact IsSmoothTowerTrace.refl (isSubmersion_val_comp U hc)
  | @step a D' D Z' Z R T b₀ ho C' π' hπ' C π hπ U χ hcomm hC hcartOut ih =>
    have hχ : Function.Injective ((Subtype.val : U → Z) ∘ χ) := by
      intro x y he
      exact χ.injective (Subtype.ext he)
    cases hs with
    | matched hs hσ hπ' g₁ hg hc hCs hcart =>
      rename_i Q₀ S₀ C₀ σ g₀
      have hsub := isSubmersion_val_comp U
        (isSubmersion_conjugate χ.symm (Diffeomorph.refl _ _ ∞) hg)
      refine IsSmoothTowerTrace.matched (ih hs) hσ hπ (Subtype.val ∘ χ ∘ g)
        hsub ?_ ?_ (holomorphicSquarePullback_open_comp (b := (Subtype.val : U → Z) ∘ χ) hs.isSubmersion.contMDiff
          hχ hcartOut hcart)
      · intro x
        rw [Function.comp_apply,Function.comp_apply,hcomm,hc]
        rfl
      · rw [preimage_comp,hC]
        exact hCs
    | silent hs hπ' g₁ hg hc hCs hcart =>
      rename_i g₀
      have hsub := isSubmersion_val_comp U
        (isSubmersion_conjugate χ.symm (Diffeomorph.refl _ _ ∞) hg)
      refine IsSmoothTowerTrace.silent (ih hs) hπ (Subtype.val ∘ χ ∘ g)
        hsub ?_ ?_ (holomorphicSquarePullback_open_comp (b := (Subtype.val : U → Z) ∘ χ) hs.isSubmersion.contMDiff
          hχ hcartOut hcart)
      · intro x
        rw [Function.comp_apply,Function.comp_apply,hcomm,hc]
        rfl
      · rw [preimage_comp,hC]
        exact hCs

/-- ANY genuine tower internally produces actual matched geometry for its literal open restriction. -/
theorem actual_open_tower_pullback {A D : CMfd.{u} n}
    (T : BlowupTower A D) (U : TopologicalSpace.Opens A) :
    IsOpenTowerPullback (A := A) (B := CMfd.of (n := n) U)
      (Subtype.val : U → A) (restrict U T) T (Subtype.val : openPreimage T U → D) := by
  induction T with
  | refl => exact IsOpenTowerPullback.refl U (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) _ ∞)
  | @step Y Z T C π hπ ih =>
    exact IsOpenTowerPullback.step ih
      (isBlowupAlong_restrict hπ (openPreimage T U)
        ((openPreimage T U).isOpen.preimage hπ.contMDiff.continuous)) hπ
      (openPreimage (.step T C π hπ) U) (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) _ ∞)
      (fun _ => rfl) rfl (holomorphicSquarePullback_restrict hπ (openPreimage T U))

/-- Literal restriction of ANY genuine tower globalizes the true all-head matched/silent smooth trace. -/
theorem smoothTrace_globalize {A D : CMfd.{u} n}
    (T : BlowupTower A D) (U : TopologicalSpace.Opens A)
    {B D' : CMfd.{u} m} {f : B → U}
    {S : BlowupTower B D'} {g : D' → openPreimage T U}
    (h : IsSmoothTowerTrace (A := CMfd.of (n := n) U)
      (D := CMfd.of (n := n) (openPreimage T U)) f S (restrict U T) g) :
    IsSmoothTowerTrace ((Subtype.val : U → A) ∘ f) S T (Subtype.val ∘ g) :=
  smoothTrace_of_open_pullback (actual_open_tower_pullback T U) h

section ActualOriginalInput
variable {A : CMfd.{u} n} {B : CMfd.{u} m} {f : B → A}

/-- The genuine original unrestricted lift from the independently generated source procedure. -/
def globalLift (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (imageSourceProcedure α q hf F hF).D → (chosenProcedure β q A F hF).D :=
  Subtype.val ∘ compressedImageLift β γ α q hf F hF

/-- No caller trace certificate: original geometry internally produces ALL unrestricted target heads. -/
theorem globalLift_actual_trace
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSmoothTowerTrace f (imageSourceProcedure α q hf F hF).T (chosenProcedure β q A F hF).T
      (globalLift β γ α q hf F hF) :=
  smoothTrace_globalize _ (imageOpen hf) (compressedImageLift_actual_trace β γ α q hf F hF)

theorem globalLift_all_heads
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ∃ i : ℕ, ∃ g : (split (imageSourceProcedure α q hf F hF).T i).1 →
        (split (chosenProcedure β q A F hF).T j).1,
      IsSmoothTowerTrace f (head (imageSourceProcedure α q hf F hF).T i)
        (head (chosenProcedure β q A F hF).T j) g :=
  (globalLift_actual_trace β γ α q hf F hF).head j

theorem globalLift_isSubmersion
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (globalLift β γ α q hf F hF) :=
  (globalLift_actual_trace β γ α q hf F hF).isSubmersion

theorem globalLift_proj_comm
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (chosenProcedure β q A F hF).T.proj (globalLift β γ α q hf F hF x) =
      f ((imageSourceProcedure α q hf F hF).T.proj x) :=
  (globalLift_actual_trace β γ α q hf F hF).proj_comm

theorem globalLift_universal
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback f (globalLift β γ α q hf F hF)
      (imageSourceProcedure α q hf F hF).T.proj (chosenProcedure β q A F hF).T.proj :=
  (globalLift_actual_trace β γ α q hf F hF).universal

/-- The original unrestricted terminal map is the genuine projection conjugate. -/
theorem globalLift_map
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    globalLift β γ α q hf F hF =
      (chosenProcedure β q A F hF).back.symm ∘ f ∘ (imageSourceProcedure α q hf F hF).back :=
  compressedImageLift_global_map β γ α q hf F hF

/-- Original geometry compares BOTH true independent OWN completions over the original map. -/
def completedGlobalLift
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedImageSourceProcedure α hf F hF).D → (chosenProcedure β (coefficientSum F) A F hF).D :=
  Subtype.val ∘ completedCompressedImageLift β γ α hf F hF

theorem completedGlobalLift_actual_trace
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSmoothTowerTrace f (completedImageSourceProcedure α hf F hF).T
      (chosenProcedure β (coefficientSum F) A F hF).T (completedGlobalLift β γ α hf F hF) :=
  smoothTrace_globalize _ (imageOpen hf) (completedCompressedImageLift_actual_trace β γ α hf F hF)

theorem completedGlobalLift_all_heads
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ∃ i : ℕ, ∃ g : (split (completedImageSourceProcedure α hf F hF).T i).1 →
        (split (chosenProcedure β (coefficientSum F) A F hF).T j).1,
      IsSmoothTowerTrace f (head (completedImageSourceProcedure α hf F hF).T i)
        (head (chosenProcedure β (coefficientSum F) A F hF).T j) g :=
  (completedGlobalLift_actual_trace β γ α hf F hF).head j

theorem completedGlobalLift_isSubmersion
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (completedGlobalLift β γ α hf F hF) :=
  (completedGlobalLift_actual_trace β γ α hf F hF).isSubmersion

theorem completedGlobalLift_proj_comm
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (chosenProcedure β (coefficientSum F) A F hF).T.proj (completedGlobalLift β γ α hf F hF x) =
      f ((completedImageSourceProcedure α hf F hF).T.proj x) :=
  (completedGlobalLift_actual_trace β γ α hf F hF).proj_comm

theorem completedGlobalLift_universal
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback f (completedGlobalLift β γ α hf F hF)
      (completedImageSourceProcedure α hf F hF).T.proj (chosenProcedure β (coefficientSum F) A F hF).T.proj :=
  (completedGlobalLift_actual_trace β γ α hf F hF).universal

theorem completedGlobalLift_map
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedGlobalLift β γ α hf F hF =
      (chosenProcedure β (coefficientSum F) A F hF).back.symm ∘ f ∘
        (completedImageSourceProcedure α hf F hF).back :=
  completedCompressedImageLift_global_map β γ α hf F hF

private theorem preimage_getD {X Y : Type u} (g : Y → X) (E : List (Set X)) (i : ℕ) :
    ((E.map (g ⁻¹' ·))[i]?).getD ∅ = g ⁻¹' ((E[i]?).getD ∅) := by
  rw [List.getElem?_map]
  cases E[i]? <;> rfl

/-- Entire coherent ideal composition and literal index filtering are proved from actual maps. -/
private theorem retained_open_pullback_eq {D : CMfd.{u} n} {Q : CMfd.{u} m}
    (V : TopologicalSpace.Opens D) (M : MarkedIdeal n D) (hM : M.ideal.IsCoherent)
    (g : Q → V) (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g)
    (L : List ℕ) :
    { markedPullback (m := m) g (markedPullback (m := n) (Subtype.val : V → D) M) with
      E := L.map (fun i => g ⁻¹' (markedPullback (m := n) (Subtype.val : V → D) M).E.getD i ∅) } =
    { markedPullback (m := m) ((Subtype.val : V → D) ∘ g) M with
      E := L.map (fun i => ((Subtype.val : V → D) ∘ g) ⁻¹' M.E.getD i ∅) } := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · apply congrArg (fun k : ℕ → Set Q => L.map k)
    funext i
    change g ⁻¹' (((M.E.map ((Subtype.val : V → D) ⁻¹' ·))[i]?).getD ∅) = _
    rw [preimage_getD]
    rfl
  · exact (coherent_pullback_comp contMDiff_subtype_val hg M.ideal hM).symm
  · rfl

/-- The actual unrestricted global control retains ALL old entries and nonempty creation events. -/
def globalRetainedMarked
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (imageSourceProcedure α q hf F hF).D :=
  let M := geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (chosenProcedure β q A F hF).T
  { markedPullback (m := m) (globalLift β γ α q hf F hF) M with
    E := ((List.range F.length) ++ newHistoryTrace (Subtype.val : imageOpen hf → A) n q F).map
      (fun i => (globalLift β γ α q hf F hF) ⁻¹' M.E.getD i ∅) }

/-- The ENTIRE actually controlled source record equals the original unrestricted global pullback. -/
theorem sourceImageMarked_whole_global
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    sourceImageMarked α q hf F hF = globalRetainedMarked β γ α q hf F hF := by
  rw [sourceImageMarked_whole_raw β γ α q hf F hF]
  unfold compressedRetainedMarked globalRetainedMarked globalLift
  rw [rawRestrictedMarked_eq]
  exact retained_open_pullback_eq _ _ (chosen_stage_coherent β q F hF) _
    (compressedImageLift_isSubmersion β γ α q hf F hF).contMDiff _

def completedGlobalRetainedMarked
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    MarkedIdeal m (completedImageSourceProcedure α hf F hF).D :=
  let M := geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
    (chosenProcedure β (coefficientSum F) A F hF).T
  { markedPullback (m := m) (completedGlobalLift β γ α hf F hF) M with
    E := ((List.range F.length) ++ newHistoryTrace (Subtype.val : imageOpen hf → A) n (coefficientSum F) F).map
      (fun i => (completedGlobalLift β γ α hf F hF) ⁻¹' M.E.getD i ∅) }

theorem completedSourceImageMarked_whole_global
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedSourceImageMarked α hf F hF = completedGlobalRetainedMarked β γ α hf F hF := by
  rw [completedSourceImageMarked_whole_raw β γ α hf F hF]
  unfold completedCompressedRetainedMarked completedGlobalRetainedMarked completedGlobalLift
  rw [rawRestrictedMarked_eq]
  exact retained_open_pullback_eq _ _ (chosen_stage_coherent β (coefficientSum F) F hF) _
    (completedCompressedImageLift_isSubmersion β γ α hf F hF).contMDiff _

/-- The genuinely transported unrestricted global ideal is unit at the independent source OWN endpoint. -/
theorem completedGlobalRetainedMarked_unit
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (completedGlobalRetainedMarked β γ α hf F hF).ideal =
      unitIdeal m (completedImageSourceProcedure α hf F hF).D := by
  rw [← completedSourceImageMarked_whole_global β γ α hf F hF]
  exact completedSourceImageMarked_unit α hf F hF

/-- Compatible original projection cones determine the actual unrestricted lift uniquely. -/
theorem globalLift_unique
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (g : (imageSourceProcedure α q hf F hF).D → (chosenProcedure β q A F hF).D)
    (hg : ∀ x, (chosenProcedure β q A F hF).T.proj (g x) =
      f ((imageSourceProcedure α q hf F hF).T.proj x)) :
    g = globalLift β γ α q hf F hF := by
  funext x
  apply (chosenProcedure β q A F hF).back.injective
  change (chosenProcedure β q A F hF).back (g x) =
    (chosenProcedure β q A F hF).back (globalLift β γ α q hf F hF x)
  rw [(chosenProcedure β q A F hF).proj_eq,hg,globalLift_proj_comm]

theorem completedGlobalLift_unique
    (β γ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (g : (completedImageSourceProcedure α hf F hF).D → (chosenProcedure β (coefficientSum F) A F hF).D)
    (hg : ∀ x, (chosenProcedure β (coefficientSum F) A F hF).T.proj (g x) =
      f ((completedImageSourceProcedure α hf F hF).T.proj x)) :
    g = completedGlobalLift β γ α hf F hF := by
  funext x
  apply (chosenProcedure β (coefficientSum F) A F hF).back.injective
  change (chosenProcedure β (coefficientSum F) A F hF).back (g x) =
    (chosenProcedure β (coefficientSum F) A F hF).back (completedGlobalLift β γ α hf F hF x)
  rw [(chosenProcedure β (coefficientSum F) A F hF).proj_eq,hg,completedGlobalLift_proj_comm]

theorem globalLift_intermediate_choice
    (β γ₁ γ₂ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    globalLift β γ₁ α q hf F hF = globalLift β γ₂ α q hf F hF := by
  rw [globalLift_map,globalLift_map]

theorem completedGlobalLift_intermediate_choice
    (β γ₁ γ₂ : CartierBlowupChoices.{u} n) (α : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    completedGlobalLift β γ₁ α hf F hF = completedGlobalLift β γ₂ α hf F hF := by
  rw [completedGlobalLift_map,completedGlobalLift_map]

/-- Independently generated source/global choice comparisons satisfy the unrestricted actual cocycle. -/
theorem globalLift_choice_cocycle
    (β₁ β₂ γ₁ γ₂ : CartierBlowupChoices.{u} n) (α₁ α₂ : CartierBlowupChoices.{u} m) (q : ℕ)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β₁ β₂ q F hF : _ → _) ∘ globalLift β₁ γ₁ α₁ q hf F hF =
      globalLift β₂ γ₂ α₂ q hf F hF ∘
        (choiceComparison (A := B) α₁ α₂ (traceCount (Subtype.val : imageOpen hf → A) n q F)
          (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
          (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF)) : _ → _) := by
  rw [globalLift_map,globalLift_map]
  funext x
  simp only [choiceComparison,Diffeomorph.coe_trans,imageSourceProcedure]
  change (chosenProcedure β₂ q A F hF).back.symm
      ((chosenProcedure β₁ q A F hF).back ((chosenProcedure β₁ q A F hF).back.symm
        (f ((imageSourceProcedure α₁ q hf F hF).back x)))) =
    (chosenProcedure β₂ q A F hF).back.symm
      (f ((imageSourceProcedure α₂ q hf F hF).back
        ((imageSourceProcedure α₂ q hf F hF).back.symm ((imageSourceProcedure α₁ q hf F hF).back x))))
  rw [Diffeomorph.apply_symm_apply,Diffeomorph.apply_symm_apply]

theorem completedGlobalLift_choice_cocycle
    (β₁ β₂ γ₁ γ₂ : CartierBlowupChoices.{u} n) (α₁ α₂ : CartierBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β₁ β₂ (coefficientSum F) F hF : _ → _) ∘ completedGlobalLift β₁ γ₁ α₁ hf F hF =
      completedGlobalLift β₂ γ₂ α₂ hf F hF ∘
        (choiceComparison (A := B) α₁ α₂
          (coefficientSum (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F)))
          (pulledWeights (imageFactor hf) (pulledWeights (Subtype.val : imageOpen hf → A) F))
          (pulledWeights_isSNCDivisor (imageFactor_isSubmersion hf) _ (image_weights_isSNCDivisor hf F hF)) : _ → _) := by
  rw [completedGlobalLift_map,completedGlobalLift_map]
  funext x
  simp only [choiceComparison,Diffeomorph.coe_trans,completedImageSourceProcedure]
  change (chosenProcedure β₂ (coefficientSum F) A F hF).back.symm
      ((chosenProcedure β₁ (coefficientSum F) A F hF).back
        ((chosenProcedure β₁ (coefficientSum F) A F hF).back.symm
          (f ((completedImageSourceProcedure α₁ hf F hF).back x)))) =
    (chosenProcedure β₂ (coefficientSum F) A F hF).back.symm
      (f ((completedImageSourceProcedure α₂ hf F hF).back
        ((completedImageSourceProcedure α₂ hf F hF).back.symm ((completedImageSourceProcedure α₁ hf F hF).back x))))
  rw [Diffeomorph.apply_symm_apply,Diffeomorph.apply_symm_apply]

end ActualOriginalInput
end
end Hironaka.HironakaSmoothSubmersionOrderedGlobalTrace
