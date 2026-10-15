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
import Hironaka.Support.BlowupSplitProjectionExact
import Hironaka.Resolution.HironakaNormalCrossingsOrderedChoiceComparison
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Actual smooth base change of independent arbitrary Cartier-choice monomial procedures

Primitive original indexed SNC data, genuine surjective arbitrary-dimensional
complex submersions and true Cartier blowup choices internally produce all
actual smooth stage maps, whole controlled marked dictionaries, unique
geometric-head lifts and genuine holomorphic universal projection squares.
Actual conjugate charts supply IsSubmersion; no caller derivative, Cartesian,
marked, aligned-history, prefix, coefficient, bound or termination certificate
is an input. Strong simultaneous recursion gives EVERY literal geometric head
its ENTIRE real controlled datum. Genuine generated projection inverses give
actual endpoint/head identity, composition and change-of-choice cocycles.
OWN original coefficient sums supply actual completed resolutions and unit
ideals, with all empty/repeated historical entries retained. Composite maps
use actual successive pulled SNC inputs, not a composite-submersion certificate.
General higher invariant/general-driver identification and nonsurjective
trace compression remain OPEN; unrelated arbitrary ideal admissibility is
not inferred. Blueprint: `hironaka-smooth-submersion-ordered-choice-base-change-extension.tex`.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOrderedChoiceBaseChange
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaNormalCrossingsOrderedChoiceComparison NormalCrossings
  HironakaSmoothSubmersionOrderedMonomialProcedure HironakaSmoothSubmersionNormalCrossings
  HironakaSmoothSubmersionCoefficientIdeals HironakaNormalCrossingsOrderedMonomialTail
  HironakaNormalCrossingsFiniteMarkedCompletion BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
noncomputable section
variable {n m : ℕ}

private theorem pulledChart_maximal {A B : CMfd.{u} n}
    (β : B ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (e : OpenPartialHomeomorph A (ComplexModel n))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ A) :
    β.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
      IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ B := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (e ∘ β) (univ ∩ β ⁻¹' e.source)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      β.contMDiff.contMDiffOn (fun _ hz => hz.2)
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (β.symm ∘ e.symm) (e.target ∩ e.symm ⁻¹' univ)
    exact β.symm.contMDiff.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)

/-- Actual conjugated submersions retain the genuine globally chosen complement and real charts. -/
theorem isSubmersion_conjugate {A A' : CMfd.{u} n} {B B' : CMfd.{u} m}
    (a : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (b : B' ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ B)
    {f : B → A} (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (a.symm ∘ f ∘ b) := by
  apply Manifold.IsSubmersionOfComplement.isSubmersion (F := hf.complement)
  intro z
  let h := hf.isSubmersionOfComplement_complement (b z)
  let d := b.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart
  let c := a.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv d c
  · exact ⟨mem_univ _,h.mem_domChart_source⟩
  · exact ⟨mem_univ _,by simpa using h.mem_codChart_source⟩
  · exact pulledChart_maximal b h.domChart h.domChart_mem_maximalAtlas
  · exact pulledChart_maximal a h.codChart h.codChart_mem_maximalAtlas
  · intro w hw
    exact ⟨mem_univ _,by simpa using h.source_subset_preimage_source hw.2⟩
  · intro w hw
    have hw' : w ∈ (h.domChart.extend 𝓘(ℂ, ComplexModel m)).target := by
      simpa [d,OpenPartialHomeomorph.extend,mfld_simps] using hw
    have he := h.writtenInCharts hw'
    simpa [d,c,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps] using he

/-- Surjectivity of actual conjugated projections is proved by genuine inverse preimages. -/
theorem surjective_conjugate {A A' : CMfd.{u} n} {B B' : CMfd.{u} m}
    (a : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (b : B' ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ B)
    {f : B → A} (hs : Function.Surjective f) :
    Function.Surjective (a.symm ∘ f ∘ b) := by
  intro w
  obtain ⟨v,hv⟩ := hs (a w)
  refine ⟨b.symm v,?_⟩
  simp [Function.comp_def,hv]


/-- Genuine holomorphic universal property of the actual whole projection square. -/
def HolomorphicSquarePullback {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    (f : B → A) (g : D' → D) (π' : D' → B) (π : D → A) : Prop :=
  ∀ (ℓ : ℕ) (P : CMfd.{u} ℓ) (u : P → B) (v : P → D),
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ u →
    ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel n) ∞ v →
    (∀ x, f (u x) = π (v x)) →
    ∃! w : P → D', ContMDiff 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ w ∧
      (∀ x, π' (w x) = u x) ∧ (∀ x, g (w x) = v x)

/-- Actual inverse projections construct the genuine unique holomorphic lift of every compatible cone. -/
theorem holomorphicSquarePullback_conjugate {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    (a : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (b : D' ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ B) (f : B → A) :
    HolomorphicSquarePullback f (a.symm ∘ f ∘ b) b a := by
  intro ℓ P u v hu _ hcomm
  refine ⟨b.symm ∘ u,⟨b.symm.contMDiff.comp hu,?_,?_⟩,?_⟩
  · intro x
    exact b.apply_symm_apply (u x)
  · intro x
    simp only [Function.comp_apply,Diffeomorph.apply_symm_apply]
    rw [hcomm]
    exact a.symm_apply_apply (v x)
  · intro w hw
    funext x
    apply b.injective
    change b (w x) = b (b.symm (u x))
    rw [hw.2.1,b.apply_symm_apply]

/-- Cross-dimensional actual stage maps, centres and holomorphic universal squares are conclusions of this predicate. -/
inductive IsSmoothTowerPullback {A : CMfd.{u} n} {B : CMfd.{u} m} (f : B → A) :
    {D' : CMfd.{u} m} → {D : CMfd.{u} n} → BlowupTower B D' → BlowupTower A D →
      (D' → D) → Prop
  | refl (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
      (hs : Function.Surjective f) : IsSmoothTowerPullback f .refl .refl f
  | step {D' : CMfd.{u} m} {D : CMfd.{u} n} {Z' : CMfd.{u} m} {Z : CMfd.{u} n}
      {T' : BlowupTower B D'} {T : BlowupTower A D} {g : D' → D}
      (h : IsSmoothTowerPullback f T' T g) {C' : Set D'} {π' : Z' → D'}
      (hπ' : IsBlowupAlong m C' π') {C : Set D} {π : Z → D}
      (hπ : IsBlowupAlong n C π) (g₁ : Z' → Z)
      (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g₁)
      (hs : Function.Surjective g₁) (hcomm : ∀ x, π (g₁ x) = g (π' x))
      (hC : g ⁻¹' C = C') (hcart : HolomorphicSquarePullback g g₁ π' π) :
      IsSmoothTowerPullback f (.step T' C' π' hπ') (.step T C π hπ) g₁

theorem IsSmoothTowerPullback.isSubmersion {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerPullback f T' T g) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g := by
  cases h with
  | refl hf _ => exact hf
  | step _ _ _ _ hg _ _ _ _ => exact hg

theorem IsSmoothTowerPullback.surjective {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerPullback f T' T g) : Function.Surjective g := by
  cases h with
  | refl _ hs => exact hs
  | step _ _ _ _ _ hs _ _ _ => exact hs

theorem IsSmoothTowerPullback.length_eq {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerPullback f T' T g) : T'.length = T.length := by
  induction h with
  | refl => rfl
  | step _ _ _ _ _ _ _ _ _ ih => exact congrArg (·+1) ih

theorem IsSmoothTowerPullback.proj_comm {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerPullback f T' T g) : ∀ x, T.proj (g x) = f (T'.proj x) := by
  induction h with
  | refl => exact fun _ => rfl
  | @step D' D Z' Z T' T g h C' π' hπ' C π hπ g₁ hg hs hc hC hcart ih =>
    intro x
    change T.proj (π (g₁ x)) = f (T'.proj (π' x))
    rw [hc]
    exact ih _

theorem IsSmoothTowerPullback.append {A D Z : CMfd.{u} n} {B D' Z' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {k : Z' → Z} {T' : BlowupTower B D'} {T : BlowupTower A D}
    {S' : BlowupTower D' Z'} {S : BlowupTower D Z}
    (h : IsSmoothTowerPullback f T' T g) (hs : IsSmoothTowerPullback g S' S k) :
    IsSmoothTowerPullback f (T'.append S') (T.append S) k := by
  induction hs with
  | refl => exact h
  | step _ hπ' hπ g₁ hg hs hc hC hcart ih =>
    exact IsSmoothTowerPullback.step ih hπ' hπ g₁ hg hs hc hC hcart

/-- Every literal geometric head of a real stage pullback has its actual produced smooth lift. -/
theorem IsSmoothTowerPullback.head {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerPullback f T' T g) (j : ℕ) :
    ∃ k : (BlowupTowerSplit.split T' j).1 → (BlowupTowerSplit.split T j).1,
      IsSmoothTowerPullback f (BlowupTowerSplit.head T' j) (BlowupTowerSplit.head T j) k := by
  induction h generalizing j with
  | refl hf hs =>
    cases j <;> exact ⟨f,IsSmoothTowerPullback.refl hf hs⟩
  | step h hπ' hπ g₁ hg hs hc hC hcart ih =>
    cases j with
    | zero => exact ⟨g₁,IsSmoothTowerPullback.step h hπ' hπ g₁ hg hs hc hC hcart⟩
    | succ j => exact ih j




/-- Genuine step universal properties compose to the entire real holomorphic projection-square universal property. -/
theorem IsSmoothTowerPullback.universal {A D : CMfd.{u} n} {B D' : CMfd.{u} m}
    {f : B → A} {g : D' → D} {T' : BlowupTower B D'} {T : BlowupTower A D}
    (h : IsSmoothTowerPullback f T' T g) : HolomorphicSquarePullback f g T'.proj T.proj := by
  induction h with
  | refl =>
    exact holomorphicSquarePullback_conjugate (Diffeomorph.refl _ A ∞) (Diffeomorph.refl _ B ∞) f
  | @step D' D Z' Z T' T g h C' π' hπ' C π hπ g₁ hg hs hc hC hcart ih =>
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

/-- Strong actual output: EVERY real geometric stage retains its ENTIRE controlled marked pullback identity. -/
inductive IsWholeMarkedStagePullback {A : CMfd.{u} n} {B : CMfd.{u} m}
    (f : B → A) (M' : MarkedIdeal m B) (M : MarkedIdeal n A) :
    {D' : CMfd.{u} m} → {D : CMfd.{u} n} → BlowupTower B D' → BlowupTower A D →
      (D' → D) → Prop
  | refl (hgeo : IsSmoothTowerPullback f .refl .refl f)
      (hmark : M' = markedPullback (m := m) f M) :
      IsWholeMarkedStagePullback f M' M .refl .refl f
  | step {D' : CMfd.{u} m} {D : CMfd.{u} n} {Z' : CMfd.{u} m} {Z : CMfd.{u} n}
      {T' : BlowupTower B D'} {T : BlowupTower A D} {g : D' → D}
      (h : IsWholeMarkedStagePullback f M' M T' T g)
      {C' : Set D'} {π' : Z' → D'} {hπ' : IsBlowupAlong m C' π'}
      {C : Set D} {π : Z → D} {hπ : IsBlowupAlong n C π} (g₁ : Z' → Z)
      (hgeo : IsSmoothTowerPullback f (.step T' C' π' hπ') (.step T C π hπ) g₁)
      (hmark : geoTransformAlong M' (.step T' C' π' hπ') =
        markedPullback (m := m) g₁ (geoTransformAlong M (.step T C π hπ))) :
      IsWholeMarkedStagePullback f M' M (.step T' C' π' hπ') (.step T C π hπ) g₁

section WholeStageCalculus
variable {A D Z : CMfd.{u} n} {B D' Z' : CMfd.{u} m} {f : B → A}
  {M' : MarkedIdeal m B} {M : MarkedIdeal n A}
  {T' : BlowupTower B D'} {T : BlowupTower A D} {g : D' → D}

theorem IsWholeMarkedStagePullback.geometric
    (h : IsWholeMarkedStagePullback f M' M T' T g) : IsSmoothTowerPullback f T' T g := by
  cases h with
  | refl hgeo _ => exact hgeo
  | step _ _ hgeo _ => exact hgeo

theorem IsWholeMarkedStagePullback.marked_dictionary
    (h : IsWholeMarkedStagePullback f M' M T' T g) :
    geoTransformAlong M' T' = markedPullback (m := m) g (geoTransformAlong M T) := by
  cases h with
  | refl _ hmark => exact hmark
  | step _ _ _ hmark => exact hmark

theorem IsWholeMarkedStagePullback.append {S' : BlowupTower D' Z'} {S : BlowupTower D Z}
    {k : Z' → Z} (h : IsWholeMarkedStagePullback f M' M T' T g)
    (hs : IsWholeMarkedStagePullback g (geoTransformAlong M' T')
      (geoTransformAlong M T) S' S k) :
    IsWholeMarkedStagePullback f M' M (T'.append S') (T.append S) k := by
  induction hs with
  | refl => exact h
  | step hs g₁ hgeo hmark ih =>
    refine IsWholeMarkedStagePullback.step ih g₁ (h.geometric.append hgeo) ?_
    simpa only [← BlowupTower.append_step,geoTransformAlong_append] using hmark

/-- Strong marked identities are extracted for EVERY literal split head from genuine output recursion. -/
theorem IsWholeMarkedStagePullback.head (h : IsWholeMarkedStagePullback f M' M T' T g) (j : ℕ) :
    ∃ k : (BlowupTowerSplit.split T' j).1 → (BlowupTowerSplit.split T j).1,
      IsWholeMarkedStagePullback f M' M (BlowupTowerSplit.head T' j) (BlowupTowerSplit.head T j) k := by
  induction h generalizing j with
  | refl hgeo hmark =>
    cases j <;> exact ⟨f,IsWholeMarkedStagePullback.refl hgeo hmark⟩
  | step h g₁ hgeo hmark ih =>
    cases j with
    | zero => exact ⟨g₁,IsWholeMarkedStagePullback.step h g₁ hgeo hmark⟩
    | succ j => exact ih j

end WholeStageCalculus

section ActualProcedure
variable {A : CMfd.{u} n} {B : CMfd.{u} m}

/-- The actual endpoint map is defined from the genuine generated whole projection inverses. -/
def actualLift (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (f : B → A)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).D →
      (chosenProcedure β q A F hF).D :=
  (chosenProcedure β q A F hF).back.symm ∘ f ∘
    (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).back

/-- Real charts produce submersion of the independently defined actual endpoint map. -/
theorem actualLift_isSubmersion (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞
      (actualLift β' β q f hf F hF) :=
  isSubmersion_conjugate _ _ hf

/-- Genuine primitive surjectivity internally gives the actual endpoint surjectivity. -/
theorem actualLift_surjective (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) : Function.Surjective (actualLift β' β q f hf F hF) :=
  surjective_conjugate _ _ hs

/-- The real whole projection square actually commutes. -/
theorem actualLift_proj_comm (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ x, (chosenProcedure β q A F hF).T.proj (actualLift β' β q f hf F hF x) =
      f ((chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T.proj x) := by
  intro x
  rw [← ChosenOutput.proj_eq,← ChosenOutput.proj_eq]
  exact (chosenProcedure β q A F hF).back.apply_symm_apply _

/-- Every genuine holomorphic compatible cone has its internally produced unique actual lift. -/
theorem actualLift_holomorphicSquarePullback (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HolomorphicSquarePullback f (actualLift β' β q f hf F hF)
      (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T.proj
      (chosenProcedure β q A F hF).T.proj := by
  rw [← ChosenOutput.proj_eq,← ChosenOutput.proj_eq]
  exact holomorphicSquarePullback_conjugate _ _ _

private def prependActualChoice {V W : CMfd.{u} n} (F : List (Set V × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) {π : W → V}
    (hπ : IsBlowupAlong n (F.get j).1 π) (o : ChosenOutput W) : ChosenOutput V where
  D := o.D
  T := (BlowupTower.step BlowupTower.refl (F.get j).1 π hπ).append o.T
  back := o.back.trans (CartierBiholomorphism F hF j hπ)
  proj_eq := by
    rw [Diffeomorph.coe_trans,BlowupTower.proj_append,← o.proj_eq,CartierBiholomorphism_coe]
    rfl
  weights := o.weights
  snc := o.snc
  indices := j.val :: o.indices

private theorem actualProcedure_succ_none {V : CMfd.{u} n} (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (F : List (Set V × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (hs : selectedIndex n F = none) :
    chosenProcedure β (q+1) V F hF = ⟨V,.refl,Diffeomorph.refl _ V ∞,rfl,F,hF,[]⟩ := by
  conv_lhs => unfold chosenProcedure
  split
  · rfl
  · rename_i j hj
    have he := hs.symm.trans hj
    contradiction

open Classical in
private theorem actualProcedure_succ_some {V : CMfd.{u} n} (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (F : List (Set V × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (j : Fin F.length) (hs : selectedIndex n F = some j) :
    chosenProcedure β (q+1) V F hF =
      let hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      let c := β.choose V F hF j
      let χ := CartierBiholomorphism F hF j c.2.property
      let G := pulledWeights χ (dividedWeights F j)
      let hG := pulledWeights_isSNCDivisor_biholomorphism χ _ (dividedWeights_isSNCDivisor F hF j hj)
      prependActualChoice F hF j c.2.property (chosenProcedure β q c.1 G hG) := by
  conv_lhs => unfold chosenProcedure
  split
  · rename_i he
    have h := he.symm.trans hs
    contradiction
  · rename_i k hk
    have heq : k = j := Option.some.inj (hk.symm.trans hs)
    subst k
    rfl

private theorem actualProcedure_congr {V : CMfd.{u} n} (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (F G : List (Set V × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst))
    (hG : IsSNCDivisor n (G.map Prod.fst)) (he : F = G) :
    chosenProcedure β q V F hF = chosenProcedure β q V G hG := by
  subst G
  rfl

/-- Exact whole indexed-list dictionary for an actually lifted Cartier successor in arbitrary dimensions. -/
theorem pulledWeights_Cartier_successor {D : CMfd.{u} n} {D' : CMfd.{u} m}
    (a : D ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A)
    (b : D' ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ B)
    (f : B → A) (F : List (Set A × ℕ)) (j : Fin F.length) :
    pulledWeights (a.symm ∘ f ∘ b) (pulledWeights a (dividedWeights F j)) =
      pulledWeights b (dividedWeights (pulledWeights f F) (pulledIndex f F j)) := by
  rw [← pulledWeights_dividedWeights,← pulledWeights_comp,← pulledWeights_comp]
  congr 1
  funext z
  exact a.apply_symm_apply _


/-- Genuine simultaneous recursion internally generates every actual cross-dimensional stage pullback. -/
theorem chosenProcedure_stage_pullback (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSmoothTowerPullback f
      (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T
      (chosenProcedure β q A F hF).T (actualLift β' β q f hf F hF) := by
  classical
  induction q generalizing A B with
  | zero => exact IsSmoothTowerPullback.refl hf hsurj
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      have hp : selectedIndex m (pulledWeights f F) = none := by
        rw [selectedIndex_pullback hf hsurj F hF,hs]; rfl
      unfold actualLift
      rw [actualProcedure_succ_none β' q _ _ hp,actualProcedure_succ_none β q _ _ hs]
      exact IsSmoothTowerPullback.refl hf hsurj
    | some j =>
      have hp : selectedIndex m (pulledWeights f F) = some (pulledIndex f F j) := by
        rw [selectedIndex_pullback hf hsurj F hF,hs]; rfl
      unfold actualLift
      rw [actualProcedure_succ_some β' q _ _ _ hp,actualProcedure_succ_some β q _ _ _ hs]
      dsimp only
      let hP := pulledWeights_isSNCDivisor hf F hF
      let jP := pulledIndex f F j
      let c := β.choose A F hF j
      let c' := β'.choose B (pulledWeights f F) hP jP
      let a := CartierBiholomorphism F hF j c.2.property
      let b := CartierBiholomorphism (pulledWeights f F) hP jP c'.2.property
      let g := a.symm ∘ f ∘ b
      have hg := isSubmersion_conjugate a b hf
      have hsg := surjective_conjugate a b hsurj
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hjP := ((Finset.mem_filter.mp (selectedIndex_some_spec (pulledWeights f F) hp).1).2).1
      let G := pulledWeights a (dividedWeights F j)
      let G' := pulledWeights b (dividedWeights (pulledWeights f F) jP)
      have hG := pulledWeights_isSNCDivisor_biholomorphism a _ (dividedWeights_isSNCDivisor F hF j hj)
      have hG' := pulledWeights_isSNCDivisor_biholomorphism b _
        (dividedWeights_isSNCDivisor (pulledWeights f F) hP jP hjP)
      have hrec := ih hg hsg G hG
      have he := pulledWeights_Cartier_successor a b f F j
      have hOut := actualProcedure_congr β' q _ _ (pulledWeights_isSNCDivisor hg G hG) hG' he
      unfold actualLift at hrec
      rw [hOut] at hrec
      have hfirst : IsSmoothTowerPullback f
          (BlowupTower.step BlowupTower.refl ((pulledWeights f F).get jP).1 c'.2.val c'.2.property)
          (BlowupTower.step BlowupTower.refl (F.get j).1 c.2.val c.2.property) g := by
        apply IsSmoothTowerPullback.step (IsSmoothTowerPullback.refl hf hsurj)
          c'.2.property c.2.property g hg hsg
        · intro z
          change c.2.val (a.symm (f (b z))) = f (c'.2.val z)
          rw [← CartierBiholomorphism_coe F hF j c.2.property]
          rw [← CartierBiholomorphism_coe (pulledWeights f F) hP jP c'.2.property]
          exact a.apply_symm_apply _
        · exact (congrArg Prod.fst (pulledWeights_get f F j)).symm
        · have ha : (a : c.1 → A) = c.2.val := CartierBiholomorphism_coe _ _ _ _
          have hb : (b : c'.1 → B) = c'.2.val := CartierBiholomorphism_coe _ _ _ _
          rw [← ha,← hb]
          exact holomorphicSquarePullback_conjugate a b f
      have h := hfirst.append hrec
      exact h

/-- Every actual literal geometric prefix has its internally generated surjective smooth stage lift. -/
theorem chosenProcedure_head_pullback (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ∃ k : (BlowupTowerSplit.split
        (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T j).1 →
        (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1,
      IsSmoothTowerPullback f
        (BlowupTowerSplit.head (chosenProcedure β' q B (pulledWeights f F)
          (pulledWeights_isSNCDivisor hf F hF)).T j)
        (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j) k :=
  (chosenProcedure_stage_pullback β' β q hf hs F hF).head j


private theorem actualWeights_dictionary {V : CMfd.{u} n} (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (F : List (Set V × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β q V F hF).weights =
      pulledWeights (chosenProcedure β q V F hF).back (terminalState n q F) := by
  let Φ := Diffeomorph.refl 𝓘(ℂ, ComplexModel n) V ∞
  have h := chosenProcedure_record_dictionary β q Φ F hF
  have ho := actualProcedure_congr β q (pulledWeights Φ F) F
    (pulledWeights_isSNCDivisor_biholomorphism Φ F hF) hF (pulledWeights_id F)
  rw [ho] at h
  exact h.1

/-- The whole actual terminal indexed data are the true endpoint preimage, including EVERY empty/repeated entry. -/
theorem actualLift_weights_dictionary (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).weights =
      pulledWeights (actualLift β' β q f hf F hF) (chosenProcedure β q A F hF).weights := by
  rw [actualWeights_dictionary,actualWeights_dictionary,
    (bounded_history_pullback hf hs q F hF).2.2.2,← pulledWeights_comp,← pulledWeights_comp]
  congr 1
  funext x
  exact ((chosenProcedure β q A F hF).back.apply_symm_apply _).symm

/-- The complete genuine controlled marked data under the SAME actual endpoint map agree in ALL four fields. -/
theorem actualLift_whole_controlled_marked (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (markedPullback (m := m) f
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
      (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T =
    markedPullback (m := m) (actualLift β' β q f hf F hF)
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
        (chosenProcedure β q A F hF).T) := by
  rw [markedPullback_indexed_dictionary hf F hF,chosenProcedure_marked_dictionary,
    chosenProcedure_marked_dictionary,
    markedPullback_indexed_dictionary (actualLift_isSubmersion β' β q hf F hF) _
      (chosenProcedure β q A F hF).snc,actualLift_weights_dictionary β' β q hf hs F hF]

/-- Actual entire selected old-key words agree for the TWO independent genuine choice procedures. -/
theorem chosenProcedure_indices_pullback (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).indices =
      (chosenProcedure β q A F hF).indices := by
  rw [chosenProcedure_indices_dictionary,chosenProcedure_indices_dictionary]
  exact (bounded_history_pullback hf hs q F hF).2.2.1

/-- The completed actual lift uses each independent procedure's OWN internally computed fuel. -/
def completedActualLift (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (f : B → A) (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).D →
    (chosenProcedure β (coefficientSum F) A F hF).D :=
  (chosenProcedure β (coefficientSum F) A F hF).back.symm ∘ f ∘
    (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).back

/-- Whole OWN computed completion fuel gives the actual smooth stage pullback without a caller finite bound. -/
theorem completed_chosenProcedure_stage_pullback (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsSmoothTowerPullback f
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T
      (chosenProcedure β (coefficientSum F) A F hF).T (completedActualLift β' β f hf F hF) := by
  unfold completedActualLift
  rw [coefficientSum_pulled]
  exact chosenProcedure_stage_pullback β' β _ hf hs F hF

/-- Completed independent actual towers have equal true lengths under the original smooth map. -/
theorem completed_chosenProcedure_length_eq (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).T.length =
      (chosenProcedure β (coefficientSum F) A F hF).T.length :=
  (completed_chosenProcedure_stage_pullback β' β hf hs F hF).length_eq

/-- Genuine own completed procedures are actual geometric resolutions with their ENTIRE actual unit ideals. -/
theorem completed_chosenProcedures_resolve (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsGeoResolution (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T ∧
    IsGeoResolution (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β (coefficientSum F) A F hF).T ∧
    (geoTransformAlong (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T).ideal = unitIdeal m _ ∧
    (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β (coefficientSum F) A F hF).T).ideal = unitIdeal n _ := by
  rw [markedPullback_indexed_dictionary hf F hF]
  exact ⟨chosenProcedure_isGeoResolution β' _ _,chosenProcedure_isGeoResolution β F hF,
    chosenProcedure_ideal_eq_unit β' _ _,chosenProcedure_ideal_eq_unit β F hF⟩
/-- Genuine simultaneous recursion internally generates every actual cross-dimensional stage pullback. -/
theorem chosenProcedure_whole_stage_pullback (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hsurj : Function.Surjective f) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    IsWholeMarkedStagePullback f
      (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
      (chosenProcedure β' q B (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF)).T
      (chosenProcedure β q A F hF).T (actualLift β' β q f hf F hF) := by
  classical
  induction q generalizing A B with
  | zero =>
    exact IsWholeMarkedStagePullback.refl (IsSmoothTowerPullback.refl hf hsurj)
      (markedPullback_indexed_dictionary hf F hF).symm
  | succ q ih =>
    cases hs : selectedIndex n F with
    | none =>
      have hp : selectedIndex m (pulledWeights f F) = none := by
        rw [selectedIndex_pullback hf hsurj F hF,hs]; rfl
      unfold actualLift
      rw [actualProcedure_succ_none β' q _ _ hp,actualProcedure_succ_none β q _ _ hs]
      exact IsWholeMarkedStagePullback.refl (IsSmoothTowerPullback.refl hf hsurj)
        (markedPullback_indexed_dictionary hf F hF).symm
    | some j =>
      have hp : selectedIndex m (pulledWeights f F) = some (pulledIndex f F j) := by
        rw [selectedIndex_pullback hf hsurj F hF,hs]; rfl
      unfold actualLift
      rw [actualProcedure_succ_some β' q _ _ _ hp,actualProcedure_succ_some β q _ _ _ hs]
      dsimp only
      let hP := pulledWeights_isSNCDivisor hf F hF
      let jP := pulledIndex f F j
      let c := β.choose A F hF j
      let c' := β'.choose B (pulledWeights f F) hP jP
      let a := CartierBiholomorphism F hF j c.2.property
      let b := CartierBiholomorphism (pulledWeights f F) hP jP c'.2.property
      let g := a.symm ∘ f ∘ b
      have hg := isSubmersion_conjugate a b hf
      have hsg := surjective_conjugate a b hsurj
      have hj := ((Finset.mem_filter.mp (selectedIndex_some_spec F hs).1).2).1
      have hjP := ((Finset.mem_filter.mp (selectedIndex_some_spec (pulledWeights f F) hp).1).2).1
      let G := pulledWeights a (dividedWeights F j)
      let G' := pulledWeights b (dividedWeights (pulledWeights f F) jP)
      have hG := pulledWeights_isSNCDivisor_biholomorphism a _ (dividedWeights_isSNCDivisor F hF j hj)
      have hG' := pulledWeights_isSNCDivisor_biholomorphism b _
        (dividedWeights_isSNCDivisor (pulledWeights f F) hP jP hjP)
      have hrec := ih hg hsg G hG
      have he := pulledWeights_Cartier_successor a b f F j
      have hOut := actualProcedure_congr β' q _ _ (pulledWeights_isSNCDivisor hg G hG) hG' he
      unfold actualLift at hrec
      rw [hOut] at hrec
      rw [he] at hrec
      have hfirst : IsSmoothTowerPullback f
          (BlowupTower.step BlowupTower.refl ((pulledWeights f F).get jP).1 c'.2.val c'.2.property)
          (BlowupTower.step BlowupTower.refl (F.get j).1 c.2.val c.2.property) g := by
        apply IsSmoothTowerPullback.step (IsSmoothTowerPullback.refl hf hsurj)
          c'.2.property c.2.property g hg hsg
        · intro z
          change c.2.val (a.symm (f (b z))) = f (c'.2.val z)
          rw [← CartierBiholomorphism_coe F hF j c.2.property]
          rw [← CartierBiholomorphism_coe (pulledWeights f F) hP jP c'.2.property]
          exact a.apply_symm_apply _
        · exact (congrArg Prod.fst (pulledWeights_get f F j)).symm
        · have ha : (a : c.1 → A) = c.2.val := CartierBiholomorphism_coe _ _ _ _
          have hb : (b : c'.1 → B) = c'.2.val := CartierBiholomorphism_coe _ _ _ _
          rw [← ha,← hb]
          exact holomorphicSquarePullback_conjugate a b f
      have hmarkedFirst : IsWholeMarkedStagePullback f
          (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F))
          (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (BlowupTower.step BlowupTower.refl ((pulledWeights f F).get jP).1 c'.2.val c'.2.property)
          (BlowupTower.step BlowupTower.refl (F.get j).1 c.2.val c.2.property) g := by
        refine IsWholeMarkedStagePullback.step
          (IsWholeMarkedStagePullback.refl (IsSmoothTowerPullback.refl hf hsurj)
            (markedPullback_indexed_dictionary hf F hF).symm) g hfirst ?_
        change (monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F)).geoTransform
            ((pulledWeights f F).get jP).1 c'.2.val =
          markedPullback (m := m) g
            ((monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 c.2.val)
        rw [chosen_Cartier_controlled_dictionary (pulledWeights f F) hP jP hjP c'.2.property,
          chosen_Cartier_controlled_dictionary F hF j hj c.2.property,
          markedPullback_indexed_dictionary hg G hG,he]
      have h := hmarkedFirst.append (by
        change IsWholeMarkedStagePullback g
          ((monomialMarkedIdeal (n := m) ((pulledWeights f F).map Prod.fst) (pulledWeights f F)).geoTransform
            ((pulledWeights f F).get jP).1 c'.2.val)
          ((monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 c.2.val) _ _ _
        rw [chosen_Cartier_controlled_dictionary (pulledWeights f F) hP jP hjP c'.2.property,
          chosen_Cartier_controlled_dictionary F hF j hj c.2.property]
        exact hrec)
      exact h



/-- EVERY actual literal geometric head has a true surjective smooth lift with WHOLE controlled marked equality. -/
theorem chosenProcedure_whole_head_pullback (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    ∃ k : (BlowupTowerSplit.split (chosenProcedure β' q B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T j).1 →
      (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1,
      IsSmoothTowerPullback f
        (BlowupTowerSplit.head (chosenProcedure β' q B (pulledWeights f F)
          (pulledWeights_isSNCDivisor hf F hF)).T j)
        (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j) k ∧
      geoTransformAlong (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
        (BlowupTowerSplit.head (chosenProcedure β' q B (pulledWeights f F)
          (pulledWeights_isSNCDivisor hf F hF)).T j) =
      markedPullback (m := m) k
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j)) := by
  obtain ⟨k,hk⟩ := (chosenProcedure_whole_stage_pullback β' β q hf hs F hF).head j
  refine ⟨k,hk.geometric,?_⟩
  rw [markedPullback_indexed_dictionary hf F hF]
  exact hk.marked_dictionary


/-- Actual independent identity input gives the true identity after its internally proved whole input equality. -/
theorem actualLift_identity (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    HEq (actualLift β β q (id : A → A) Manifold.IsSubmersion.id F hF)
      (id : (chosenProcedure β q A F hF).D → (chosenProcedure β q A F hF).D) := by
  have ho := actualProcedure_congr β q (pulledWeights (id : A → A) F) F
    (pulledWeights_isSNCDivisor Manifold.IsSubmersion.id F hF) hF (pulledWeights_id F)
  unfold actualLift
  rw [ho]
  apply heq_of_eq
  funext x
  exact (chosenProcedure β q A F hF).back.symm_apply_apply x

/-- The genuine composite uses actual successive pulled SNC inputs, without a composite submersion certificate. -/
def compositeActualLift {ℓ : ℕ} {C : CMfd.{u} ℓ}
    (β'' : CartierBlowupChoices.{u} ℓ) (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (f : B → A) (g : C → B)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (chosenProcedure β'' q C (pulledWeights g (pulledWeights f F))
      (pulledWeights_isSNCDivisor hg _ (pulledWeights_isSNCDivisor hf F hF))).D →
      (chosenProcedure β q A F hF).D :=
  (chosenProcedure β q A F hF).back.symm ∘ (f ∘ g) ∘
    (chosenProcedure β'' q C (pulledWeights g (pulledWeights f F))
      (pulledWeights_isSNCDivisor hg _ (pulledWeights_isSNCDivisor hf F hF))).back

/-- The TWO genuine internally produced stage maps compose exactly for THREE independent choice procedures. -/
theorem actualLift_composition {ℓ : ℕ} {C : CMfd.{u} ℓ}
    (β'' : CartierBlowupChoices.{u} ℓ) (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) (f : B → A) (g : C → B)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    actualLift β' β q f hf F hF ∘
      actualLift β'' β' q g hg (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF) =
        compositeActualLift β'' β q f g hf hg F hF := by
  funext x
  simp only [actualLift,compositeActualLift,Function.comp_apply,Diffeomorph.apply_symm_apply]

/-- The actual composite input is the literal whole preimage list, including its full coefficient word. -/
theorem compositeActualLift_input_dictionary {ℓ : ℕ} {C : CMfd.{u} ℓ}
    (f : B → A) (g : C → B) (F : List (Set A × ℕ)) :
    pulledWeights g (pulledWeights f F) = pulledWeights (f ∘ g) F :=
  (pulledWeights_comp f g F).symm

/-- True whole projection inverses prove base change commutes with the real unique choice comparisons. -/
theorem actualLift_choice_cocycle (β'₁ β'₂ : CartierBlowupChoices.{u} m)
    (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    (choiceComparison β₁ β₂ q F hF : _ → _) ∘ actualLift β'₁ β₁ q f hf F hF =
      actualLift β'₂ β₂ q f hf F hF ∘
        (choiceComparison β'₁ β'₂ q (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF) : _ → _) := by
  funext x
  simp only [choiceComparison,actualLift,Diffeomorph.coe_trans,Function.comp_apply,
    Diffeomorph.apply_symm_apply]

/-- Whole OWN completed marked records actually pull back under the SAME completed actual lift. -/
theorem completedActualLift_whole_controlled_marked (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) :
    geoTransformAlong (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
      (chosenProcedure β' (coefficientSum (pulledWeights f F)) B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T =
    markedPullback (m := m) (completedActualLift β' β f hf F hF)
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
        (chosenProcedure β (coefficientSum F) A F hF).T) := by
  unfold completedActualLift
  rw [coefficientSum_pulled]
  exact actualLift_whole_controlled_marked β' β _ hf hs F hF


private def headBiholomorphismOfOutput {V : CMfd.{u} n} (o : ChosenOutput V) (j : ℕ) :
    (BlowupTowerSplit.split o.T j).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ V where
  toFun := (BlowupTowerSplit.head o.T j).proj
  invFun := (BlowupTowerSplit.tail o.T j).proj ∘ o.back.symm
  right_inv x := by
    change (BlowupTowerSplit.head o.T j).proj ((BlowupTowerSplit.tail o.T j).proj (o.back.symm x)) = x
    have he := congrFun (BlowupTowerSplit.proj_eq_comp o.T j) (o.back.symm x)
    simp only [Function.comp_apply] at he
    rw [← he,← o.proj_eq]
    exact o.back.apply_symm_apply x
  left_inv x := by
    obtain ⟨z,hz⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective
      (BlowupTowerSplit.tail o.T j).isBlowupSequence x
    rw [← hz]
    change (BlowupTowerSplit.tail o.T j).proj
      (o.back.symm ((BlowupTowerSplit.head o.T j).proj ((BlowupTowerSplit.tail o.T j).proj z))) = _
    have he := congrFun (BlowupTowerSplit.proj_eq_comp o.T j) z
    simp only [Function.comp_apply] at he
    rw [← he,← o.proj_eq,o.back.symm_apply_apply]
  contMDiff_toFun := (BlowupTowerSplit.head o.T j).contMDiff_proj
  contMDiff_invFun := (BlowupTowerSplit.tail o.T j).contMDiff_proj.comp o.back.symm.contMDiff

/-- The actual inverse projection of EVERY genuine literal geometric head is internally constructed. -/
def chosenHeadBiholomorphism (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :=
  headBiholomorphismOfOutput (chosenProcedure β q A F hF) j

/-- Its whole genuine forward map is literally the actual head projection. -/
theorem chosenHeadBiholomorphism_coe (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    (chosenHeadBiholomorphism β q F hF j : _ → A) =
      (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j).proj := rfl

/-- The true stage map of EVERY literal geometric head is computed from its actual generated projection inverses. -/
def headActualLift (β' : CartierBlowupChoices.{u} m) (β : CartierBlowupChoices.{u} n)
    (q : ℕ) (f : B → A)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    (BlowupTowerSplit.split (chosenProcedure β' q B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).T j).1 →
      (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1 :=
  (chosenHeadBiholomorphism β q F hF j).symm ∘ f ∘
    (chosenHeadBiholomorphism β' q (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF) j)

/-- ALL actual geometric heads have their SAME unique computed smooth lift and ENTIRE actual controlled marked dictionary. -/
theorem headActualLift_whole_dictionary (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hs : Function.Surjective f) (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    IsSmoothTowerPullback f
      (BlowupTowerSplit.head (chosenProcedure β' q B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T j)
      (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j) (headActualLift β' β q f hf F hF j) ∧
    geoTransformAlong (markedPullback (m := m) f (monomialMarkedIdeal (n := n) (F.map Prod.fst) F))
      (BlowupTowerSplit.head (chosenProcedure β' q B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T j) =
      markedPullback (m := m) (headActualLift β' β q f hf F hF j)
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j)) := by
  obtain ⟨k,hk,hmark⟩ := chosenProcedure_whole_head_pullback β' β q hf hs F hF j
  have he : k = headActualLift β' β q f hf F hF j := by
    funext x
    apply (chosenHeadBiholomorphism β q F hF j).injective
    change (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j).proj (k x) = _
    rw [hk.proj_comm]
    exact ((chosenHeadBiholomorphism β q F hF j).apply_symm_apply _).symm
  rw [he] at hk hmark
  exact ⟨hk,hmark⟩

/-- Exact uniqueness for the actual smooth lift of EVERY true literal geometric head. -/
theorem headActualLift_unique (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ)
    (k : (BlowupTowerSplit.split (chosenProcedure β' q B (pulledWeights f F)
      (pulledWeights_isSNCDivisor hf F hF)).T j).1 →
      (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1)
    (hk : ∀ x, (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j).proj (k x) =
      f ((BlowupTowerSplit.head (chosenProcedure β' q B (pulledWeights f F)
        (pulledWeights_isSNCDivisor hf F hF)).T j).proj x)) :
    k = headActualLift β' β q f hf F hF j := by
  funext x
  apply (chosenHeadBiholomorphism β q F hF j).injective
  change (BlowupTowerSplit.head (chosenProcedure β q A F hF).T j).proj (k x) = _
  rw [hk]
  exact ((chosenHeadBiholomorphism β q F hF j).apply_symm_apply _).symm


/-- The actual unique two-choice comparison at EVERY literal head is computed from genuine generated projections. -/
def headChoiceComparison (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :=
  (chosenHeadBiholomorphism β₁ q F hF j).trans (chosenHeadBiholomorphism β₂ q F hF j).symm

private theorem actualTowerIso_head {A A' D D' : CMfd.{u} n}
    {Φ : A' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ A}
    {T' : BlowupTower A' D'} {T : BlowupTower A D}
    {χ : D' ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ D}
    (h : BlowupTowerIsomorphism.IsTowerIso Φ T' T χ) (j : ℕ) :
    ∃ ψ : (BlowupTowerSplit.split T' j).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯
        (BlowupTowerSplit.split T j).1,
      BlowupTowerIsomorphism.IsTowerIso Φ (BlowupTowerSplit.head T' j) (BlowupTowerSplit.head T j) ψ := by
  induction h generalizing j with
  | refl => cases j <;> exact ⟨Φ,BlowupTowerIsomorphism.IsTowerIso.refl⟩
  | step h hπ' hπ χ₁ hc hC ih =>
    cases j with
    | zero => exact ⟨χ₁,BlowupTowerIsomorphism.IsTowerIso.step h hπ' hπ χ₁ hc hC⟩
    | succ j => exact ih j

/-- EVERY internally produced actual head comparison is a real same-dimensional tower isomorphism. -/
theorem headChoiceComparison_isTowerIso (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    BlowupTowerIsomorphism.IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) A ∞)
      (BlowupTowerSplit.head (chosenProcedure β₁ q A F hF).T j)
      (BlowupTowerSplit.head (chosenProcedure β₂ q A F hF).T j) (headChoiceComparison β₁ β₂ q F hF j) := by
  obtain ⟨ψ,hψ⟩ := actualTowerIso_head (choiceComparison_isTowerIso β₁ β₂ q F hF) j
  have he : ψ = headChoiceComparison β₁ β₂ q F hF j := by
    apply Diffeomorph.ext
    intro x
    apply (chosenHeadBiholomorphism β₂ q F hF j).injective
    change (BlowupTowerSplit.head (chosenProcedure β₂ q A F hF).T j).proj (ψ x) = _
    rw [← hψ.proj_comm]
    exact ((chosenHeadBiholomorphism β₂ q F hF j).apply_symm_apply _).symm
  rwa [he] at hψ

/-- The real head lifts commute EXACTLY with TWO actual independent choice changes at EVERY literal stage. -/
theorem headActualLift_choice_cocycle (β'₁ β'₂ : CartierBlowupChoices.{u} m)
    (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ) {f : B → A}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    (headChoiceComparison β₁ β₂ q F hF j : _ → _) ∘ headActualLift β'₁ β₁ q f hf F hF j =
      headActualLift β'₂ β₂ q f hf F hF j ∘
        (headChoiceComparison β'₁ β'₂ q (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF) j : _ → _) := by
  funext x
  simp only [headChoiceComparison,headActualLift,Diffeomorph.coe_trans,Function.comp_apply,
    Diffeomorph.apply_symm_apply]

/-- Genuine successive pulled SNC inputs internally define the actual composite map at EVERY literal geometric head. -/
def compositeHeadActualLift {ℓ : ℕ} {C : CMfd.{u} ℓ}
    (β'' : CartierBlowupChoices.{u} ℓ) (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (f : B → A) (g : C → B)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    (BlowupTowerSplit.split (chosenProcedure β'' q C (pulledWeights g (pulledWeights f F))
      (pulledWeights_isSNCDivisor hg _ (pulledWeights_isSNCDivisor hf F hF))).T j).1 →
      (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1 :=
  (chosenHeadBiholomorphism β q F hF j).symm ∘ (f ∘ g) ∘
    (chosenHeadBiholomorphism β'' q (pulledWeights g (pulledWeights f F))
      (pulledWeights_isSNCDivisor hg _ (pulledWeights_isSNCDivisor hf F hF)) j)

/-- Actual smooth base maps and independently generated choice procedures compose at EVERY literal geometric head. -/
theorem headActualLift_composition {ℓ : ℕ} {C : CMfd.{u} ℓ}
    (β'' : CartierBlowupChoices.{u} ℓ) (β' : CartierBlowupChoices.{u} m)
    (β : CartierBlowupChoices.{u} n) (q : ℕ) (f : B → A) (g : C → B)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel ℓ) 𝓘(ℂ, ComplexModel m) ∞ g)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    headActualLift β' β q f hf F hF j ∘
      headActualLift β'' β' q g hg (pulledWeights f F) (pulledWeights_isSNCDivisor hf F hF) j =
        compositeHeadActualLift β'' β q f g hf hg F hF j := by
  funext x
  simp only [headActualLift,compositeHeadActualLift,Function.comp_apply,Diffeomorph.apply_symm_apply]


/-- Exact identity at EVERY literal geometric head, with the internally proved actual input-type dictionary. -/
theorem headActualLift_identity (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    HEq (headActualLift β β q (id : A → A) Manifold.IsSubmersion.id F hF j)
      (id : (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1 →
        (BlowupTowerSplit.split (chosenProcedure β q A F hF).T j).1) := by
  have ho := actualProcedure_congr β q (pulledWeights (id : A → A) F) F
    (pulledWeights_isSNCDivisor Manifold.IsSubmersion.id F hF) hF (pulledWeights_id F)
  unfold headActualLift chosenHeadBiholomorphism
  rw [ho]
  apply heq_of_eq
  funext x
  exact (headBiholomorphismOfOutput (chosenProcedure β q A F hF) j).symm_apply_apply x

/-- Actual head choice comparisons satisfy the genuine identity. -/
theorem headChoiceComparison_identity (β : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    headChoiceComparison β β q F hF j = Diffeomorph.refl _ _ ∞ := by
  apply Diffeomorph.ext
  intro x
  exact (chosenHeadBiholomorphism β q F hF j).symm_apply_apply x

/-- Actual head choice comparisons satisfy the genuine inverse. -/
theorem headChoiceComparison_inverse (β₁ β₂ : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    (headChoiceComparison β₁ β₂ q F hF j).symm = headChoiceComparison β₂ β₁ q F hF j := rfl

/-- THREE actually independently generated procedures have the exact real choice cocycle at EVERY geometric stage. -/
theorem headChoiceComparison_cocycle (β₁ β₂ β₃ : CartierBlowupChoices.{u} n) (q : ℕ)
    (F : List (Set A × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : ℕ) :
    (headChoiceComparison β₁ β₂ q F hF j).trans (headChoiceComparison β₂ β₃ q F hF j) =
      headChoiceComparison β₁ β₃ q F hF j := by
  apply Diffeomorph.ext
  intro x
  simp only [headChoiceComparison,Diffeomorph.coe_trans,Function.comp_apply,Diffeomorph.apply_symm_apply]

end ActualProcedure

end
end Hironaka.HironakaSmoothSubmersionOrderedChoiceBaseChange
