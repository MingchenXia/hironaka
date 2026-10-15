/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionUniversalBlowupChartEquality
import Hironaka.Blowup.BlowupIsomorphismOff
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionGlobalBlowupSubmersion
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupConstruction BlowupIsomorphismOff HironakaSmoothSubmersionBlowupLift
  HironakaSmoothSubmersionNormalCrossings HironakaSmoothSubmersionUniversalBlowupChartEquality
noncomputable section
section Complement
variable {n : ℕ} {X Z : CMfd.{u} n} {C : Set X} {π : Z → X}

def complementOpen (hπ : IsBlowupAlong n C π) : TopologicalSpace.Opens X :=
  ⟨Cᶜ,hπ.1.1.isOpen_compl⟩

def sourceComplementOpen (hπ : IsBlowupAlong n C π) : TopologicalSpace.Opens Z :=
  ⟨π ⁻¹' Cᶜ,hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous⟩

def complementBiholomorphism (hπ : IsBlowupAlong n C π) :
    sourceComplementOpen hπ ≃ₘ⟮𝓘(ℂ, ComplexModel n),𝓘(ℂ, ComplexModel n)⟯ complementOpen hπ := by
  classical
  let s : complementOpen hπ → Z := Classical.choose (exists_section_compl hπ)
  have hspec := Classical.choose_spec (exists_section_compl hπ)
  have hs := hspec.1
  have hsπ := hspec.2.1
  have hsec := hspec.2.2
  let ρ : sourceComplementOpen hπ → complementOpen hπ := fun x => ⟨π x.1,x.2⟩
  let σ : complementOpen hπ → sourceComplementOpen hπ := fun x =>
    ⟨s x,by
      have hx : π (s x) = x.1 := congrFun hsπ x
      change π (s x) ∈ Cᶜ
      exact hx.symm ▸ x.2⟩
  refine ⟨⟨ρ,σ,?_,?_⟩,?_,?_⟩
  · intro x
    apply Subtype.ext
    exact hsec x.1 x.2
  · intro x
    apply Subtype.ext
    exact congrFun hsπ x
  · intro x
    exact (ContMDiffAt.subtypeVal_comp_iff (complementOpen hπ) ρ x).mp
      ((hπ.contMDiff.comp contMDiff_subtype_val) x)
  · intro x
    exact (ContMDiffAt.subtypeVal_comp_iff (sourceComplementOpen hπ) σ x).mp (hs x)

theorem complementBiholomorphism_apply (hπ : IsBlowupAlong n C π) (x : sourceComplementOpen hπ) :
    (complementBiholomorphism hπ x).1 = π x.1 := by
  rfl


private theorem subtypeInclusion_holomorphic {A : CMfd.{u} n}
    (O : TopologicalSpace.Opens A) (hO : Nonempty O) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (O.openPartialHomeomorphSubtypeCoe hO) (O.openPartialHomeomorphSubtypeCoe hO).source ∧
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (O.openPartialHomeomorphSubtypeCoe hO).symm (O.openPartialHomeomorphSubtypeCoe hO).target := by
  refine ⟨contMDiff_subtype_val.contMDiffOn,?_⟩
  let e := O.openPartialHomeomorphSubtypeCoe hO
  have hv : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : O → A) ∘ e.symm) e.target :=
    contMDiffOn_id.congr (fun x hx => e.right_inv hx)
  intro x hx
  exact (ContMDiffWithinAt.subtypeVal_comp_iff O e.symm e.target x).mp (hv x hx)

private theorem partial_trans_holomorphic {A B D : CMfd.{u} n}
    (e : OpenPartialHomeomorph A B) (f : OpenPartialHomeomorph B D)
    (he : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm e.target)
    (hf : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f f.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f.symm f.target) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (e.trans f) (e.trans f).source ∧
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (e.trans f).symm (e.trans f).target := by
  constructor
  · exact hf.1.comp (he.1.mono inter_subset_left) (fun _ hx => hx.2)
  · exact he.2.comp (hf.2.mono inter_subset_left) (fun _ hx => hx.2)

def complementPartial (hπ : IsBlowupAlong n C π) (p : Z) (hp : π p ∉ C) :
    OpenPartialHomeomorph Z X :=
  (sourceComplementOpen hπ |>.openPartialHomeomorphSubtypeCoe ⟨⟨p,hp⟩⟩).symm.trans
    ((complementBiholomorphism hπ).toHomeomorph.toOpenPartialHomeomorph.trans
      (complementOpen hπ |>.openPartialHomeomorphSubtypeCoe ⟨⟨π p,hp⟩⟩))

theorem complementPartial_source (hπ : IsBlowupAlong n C π) (p : Z) (hp : π p ∉ C) :
    (complementPartial hπ p hp).source = π ⁻¹' Cᶜ := by
  unfold complementPartial
  rw [OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.trans_source]
  simp only [OpenPartialHomeomorph.symm_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
    Homeomorph.toOpenPartialHomeomorph_source,inter_univ,preimage_univ]
  rfl

theorem complementPartial_target (hπ : IsBlowupAlong n C π) (p : Z) (hp : π p ∉ C) :
    (complementPartial hπ p hp).target = Cᶜ := by
  unfold complementPartial
  rw [OpenPartialHomeomorph.trans_target,OpenPartialHomeomorph.trans_target]
  simp only [OpenPartialHomeomorph.symm_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
    Homeomorph.toOpenPartialHomeomorph_target,inter_univ,preimage_univ]
  rfl

theorem complementPartial_apply (hπ : IsBlowupAlong n C π) (p : Z) (hp : π p ∉ C)
    {q : Z} (hq : π q ∉ C) : complementPartial hπ p hp q = π q := by
  let O := sourceComplementOpen hπ
  let i := O.openPartialHomeomorphSubtypeCoe ⟨⟨p,hp⟩⟩
  have hqi : q ∈ i.target := by
    rw [show i.target = (O : Set Z) from O.openPartialHomeomorphSubtypeCoe_target _]
    exact hq
  have hi : (i.symm q).1 = q := i.right_inv hqi
  change π (i.symm q).1 = π q
  exact congrArg π hi

theorem complementPartial_holomorphic (hπ : IsBlowupAlong n C π) (p : Z) (hp : π p ∉ C) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (complementPartial hπ p hp) (complementPartial hπ p hp).source ∧
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (complementPartial hπ p hp).symm (complementPartial hπ p hp).target := by
  let O := sourceComplementOpen hπ
  let N := complementOpen hπ
  let i := O.openPartialHomeomorphSubtypeCoe ⟨⟨p,hp⟩⟩
  let j := N.openPartialHomeomorphSubtypeCoe ⟨⟨π p,hp⟩⟩
  let β := (complementBiholomorphism hπ).toHomeomorph.toOpenPartialHomeomorph
  have hβ : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ β β.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ β.symm β.target :=
    ⟨(complementBiholomorphism hπ).contMDiff.contMDiffOn,
      (complementBiholomorphism hπ).symm.contMDiff.contMDiffOn⟩
  exact partial_trans_holomorphic (A := Z) (B := CMfd.of O) (D := X) i.symm (β.trans j)
    (subtypeInclusion_holomorphic O ⟨⟨p,hp⟩⟩).symm
    (partial_trans_holomorphic (A := CMfd.of O) (B := CMfd.of N) (D := X) β j hβ
      (subtypeInclusion_holomorphic N ⟨⟨π p,hp⟩⟩))

end Complement

section LocalTransport
variable {n m : ℕ} {X X' : CMfd.{u} n} {Y Y' : CMfd.{u} m}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem partial_chart_maximal {k : ℕ} {A B : CMfd.{u} k}
    (b : OpenPartialHomeomorph A B)
    (hb : ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ b.symm b.target)
    (e : OpenPartialHomeomorph B (ComplexModel k))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel k) ∞ B) :
    b.trans e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel k) ∞ A := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas he).comp
      (hb.1.mono inter_subset_left) (fun _ hz => hz.2)
  · exact hb.2.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left) (fun _ hz => hz.2)

private theorem restricted_chart_maximal {k : ℕ} {A : CMfd.{u} k}
    (e : OpenPartialHomeomorph A (ComplexModel k))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel k) ∞ A) (W : Set A) :
    e.restr W ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel k) ∞ A := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left
  · exact (contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left

theorem isSubmersionAtOfComplement_local_square
    (a : OpenPartialHomeomorph X' X) (b : OpenPartialHomeomorph Y' Y)
    (ha : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a a.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ a.symm a.target)
    (hb : ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ b b.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ b.symm b.target)
    {f : Y → X} {G : Y' → X'} (hfc : Continuous f) {p : Y'}
    (hf : Manifold.IsSubmersionAtOfComplement F
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f (b p))
    (hGc : ContinuousAt G p) (hp : p ∈ b.source)
    (hsource : b.source ⊆ G ⁻¹' a.source)
    (hsquare : ∀ q ∈ b.source, a (G q) = f (b q)) :
    Manifold.IsSubmersionAtOfComplement F
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ G p := by
  let W := f ⁻¹' a.target
  have hW : IsOpen W := a.open_target.preimage hfc
  let d₀ := hf.domChart.restr W
  let d := b.trans d₀
  let c := a.trans hf.codChart
  have hfp : f (b p) ∈ a.target := by
    rw [← hsquare p hp]
    exact a.map_source (hsource hp)
  have hdp : p ∈ d.source := by
    change p ∈ b.source ∩ b ⁻¹' d₀.source
    refine ⟨hp,?_⟩
    rw [show d₀.source = hf.domChart.source ∩ W from hf.domChart.restr_source' W hW]
    exact ⟨hf.mem_domChart_source,hfp⟩
  have hcp : G p ∈ c.source := by
    change G p ∈ a.source ∩ a ⁻¹' hf.codChart.source
    refine ⟨hsource hp,?_⟩
    change a (G p) ∈ hf.codChart.source
    rw [hsquare p hp]
    exact hf.mem_codChart_source
  apply Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt hGc hf.equiv d c hdp hcp
  · exact partial_chart_maximal (A := Y') (B := Y) b hb d₀
      (restricted_chart_maximal hf.domChart hf.domChart_mem_maximalAtlas W)
  · exact partial_chart_maximal (A := X') (B := X) a ha hf.codChart hf.codChart_mem_maximalAtlas
  · intro w hw
    have hw' : w ∈ d.target := by simpa [OpenPartialHomeomorph.extend,mfld_simps] using hw
    have hq : d.symm w ∈ d.source := d.map_target hw'
    have hqb : d.symm w ∈ b.source := hq.1
    have hdw : w ∈ hf.domChart.target := hw'.1.1
    have hbd : b (d.symm w) = hf.domChart.symm w := by
      change b (b.symm (hf.domChart.symm w)) = hf.domChart.symm w
      exact b.right_inv hw'.2
    have he := hf.writtenInCharts (by simpa [OpenPartialHomeomorph.extend,mfld_simps] using hdw)
    change hf.codChart (a (G (d.symm w))) = (hf.equiv w).1
    rw [hsquare _ hqb,hbd]
    simpa [OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps] using he
end LocalTransport

section OffCentre
variable {n r : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} (n+r)}
  {f : Y → X} {C : Set X} {π : D → X} {π' : D' → Y}

theorem actualLift_off_isSubmersionAtOfComplement
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hπ : IsBlowupAlong n C π) (hπ' : IsBlowupAlong (n+r) (f ⁻¹' C) π')
    (p : D') (hp : π' p ∉ f ⁻¹' C) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ (actualLift hf hπ hπ') p := by
  let G : D' → D := actualLift hf hπ hπ'
  have hsquare (q : D') : π (G q) = f (π' q) := congrFun (actualLift_proj_comm hf hπ hπ') q
  have hGp : π (G p) ∉ C := by
    rw [hsquare p]
    exact hp
  let a := complementPartial hπ (G p) hGp
  let b := complementPartial hπ' p hp
  have hbp : p ∈ b.source := by
    rw [complementPartial_source]
    exact hp
  have hsource : b.source ⊆ G ⁻¹' a.source := by
    intro q hq
    rw [complementPartial_source] at hq ⊢
    change π (G q) ∉ C
    rw [hsquare q]
    exact hq
  have hs : ∀ q ∈ b.source, a (G q) = f (b q) := by
    intro q hq
    have hq' : π' q ∉ f ⁻¹' C := by
      rwa [complementPartial_source] at hq
    have hGq : π (G q) ∉ C := by rw [hsquare q]; exact hq'
    rw [complementPartial_apply hπ (G p) hGp hGq,
      complementPartial_apply hπ' p hp hq',hsquare]
  let h := hf.isSubmersionAt (b p)
  have hG := isSubmersionAtOfComplement_local_square a b
    (complementPartial_holomorphic hπ (G p) hGp) (complementPartial_holomorphic hπ' p hp)
    hf.contMDiff.continuous h.isSubmersionAtOfComplement_complement
    ((actualLift_contMDiff hf hπ hπ') p).continuousAt hbp hsource hs
  have ht := hG.trans_F (complementCoordinates h)
  change Manifold.IsSubmersionAtOfComplement (ComplexModel (n+r-n))
    𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ G p at ht
  exact ht.trans_F (ContinuousLinearEquiv.ofFinrankEq (show Module.finrank ℂ (ComplexModel (n+r-n)) =
    Module.finrank ℂ (ComplexModel r) by simp only [ComplexModel,finrank_euclideanSpace_fin]; omega))
end OffCentre

section OriginalGlobal
variable {n r : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} (n+r)} {f : Y → X}

theorem canonical_actualLift_isSubmersionOfComplement
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hCi' := (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) hCi'
    Manifold.IsSubmersionOfComplement (ComplexModel r)
      𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞
      (actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ') := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  intro p
  by_cases hp : p.base ∈ f ⁻¹' C
  · exact actualLift_exceptional_isSubmersionAtOfComplement hf C hC hCi p hp
  · exact actualLift_off_isSubmersionAtOfComplement
      (D := CMfd.of (BlowupSpace n C)) (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C)))
      (π := blowupProj n C) (π' := blowupProj (n+r) (f ⁻¹' C)) hf
      (isBlowupAlong_blowupProj (n := n) (C := C) hCi)
      (isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C)
        (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf
          (isBlowupAlong_blowupProj (n := n) (C := C) hCi)).2) p hp

theorem canonical_actualLift_isSubmersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞ f)
    (C : Set X) (hC : IsClosedSubmanifold n C) (hCi : interior C = ∅) :
    let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
    let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
      ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
    let hπ := isBlowupAlong_blowupProj (n := n) (C := C) hCi
    let hCi' := (actual_source_centre (D := CMfd.of (BlowupSpace n C)) hf hπ).2
    let hπ' := isBlowupAlong_blowupProj (n := n+r) (C := f ⁻¹' C) hCi'
    Manifold.IsSubmersion
      𝓘(ℂ, ComplexModel (n+r)) 𝓘(ℂ, ComplexModel n) ∞
      (actualLift (D := CMfd.of (BlowupSpace n C))
        (D' := CMfd.of (BlowupSpace (n+r) (f ⁻¹' C))) hf hπ hπ') := by
  let _ : Fact (IsClosedSubmanifold n C) := ⟨hC⟩
  let _ : Fact (IsClosedSubmanifold (n+r) (f ⁻¹' C)) :=
    ⟨HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hC⟩
  dsimp only
  exact (canonical_actualLift_isSubmersionOfComplement hf C hC hCi).isSubmersion
end OriginalGlobal



end
end Hironaka.HironakaSmoothSubmersionGlobalBlowupSubmersion
