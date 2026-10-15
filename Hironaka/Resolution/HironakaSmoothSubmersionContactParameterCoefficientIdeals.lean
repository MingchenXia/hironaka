/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCharts
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v w
namespace Hironaka.HironakaSmoothSubmersionContactParameterCoefficientIdeals
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  GermIdealPullbackCalculus RestrictedIdealExtension RelativePrincipalizationSpan
  MarkedIdeals MarkedIdeal GermIdealOrder HomogenizedIdealAlong DerivativeIdealAlongCoherent
  HironakaSmoothSubmersionContactParameterCharts HironakaSmoothSubmersionContactCoefficientRestriction
  HironakaSmoothSubmersionRelativeDifferentialIdeals HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionTangentContact GiraudAlong
  Hironaka.RegularLocusDense TangentDirectionAlong BlowupFlatCoordinates
noncomputable section

variable {n m a : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} m} {Z : CMfd.{w} a}

def parameterMapOn {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (b : ℕ) :
    parameterOpen Φ b → X := fun z => parameterMap Φ b z.val

theorem parameterMapOn_contMDiff {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (b : ℕ)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target) :
    ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) ∞ (parameterMapOn Φ b) := by
  intro z
  exact ((parameterMap_contMDiffOn Φ b hΦsrc).contMDiffAt
    ((parameterOpen Φ b).isOpen.mem_nhds z.property)).comp z contMDiff_subtype_val.contMDiffAt

theorem whole_parameter_pullback_restrictOn {σ : Y → X}
    (hσ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ σ)
    (I : GermIdeal n X) (hI : I.IsCoherent) (C : Set X)
    (hC : ∀ z : Y, σ z ∈ C) :
    GermIdeal.pullback (m := m) σ (restrictOn n C I) = GermIdeal.pullback (m := m) σ I := by
  apply GermIdeal.ext
  funext z g
  apply propext
  constructor
  · intro hg
    refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨hshol,r,t,c,ht,hc,he⟩ := hs
    have hfat : ∀ᶠ q in 𝓝 z,
        ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ σ q :=
      Eventually.of_forall fun q => hσ.contMDiffAt
    refine ⟨hshol.comp_contMDiff hfat,r,fun i => t i ∘ σ,fun i => c i ∘ σ,
      fun i => ⟨t i,ht i,rfl⟩,fun i => (hc i).comp_contMDiff hfat,?_⟩
    filter_upwards [(hσ.continuous.tendsto z).eventually he] with q hq
    exact hq (hC q)
  · intro hg
    exact GermIdeal.mem_pullback_iff.mpr ((GermIdeal.mem_pullback_iff.mp hg).mono
      (fun s hs => by
        obtain ⟨t,ht,rfl⟩ := hs
        exact ⟨t,le_restrictOn hI _ _ ht,rfl⟩))

/-- Actual whole composition with three independent carrier universes. -/
theorem coherent_parameter_pullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel m) ∞ g)
    (I : GermIdeal n X) (hI : I.IsCoherent) :
    GermIdeal.pullback (m := a) (f ∘ g) I =
      GermIdeal.pullback (m := a) g (GermIdeal.pullback (m := m) f I) := by
  refine GermIdeal.ext (funext fun z => funext fun s => propext ⟨fun hs => ?_,fun hs => ?_⟩)
  · have hfat : ∀ᶠ q in 𝓝 (g z),
        ContMDiffAt 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f q :=
      Eventually.of_forall fun q => hf.contMDiffAt
    refine GermIdeal.mem_pullback_iff.mpr ((GermIdeal.mem_pullback_iff.mp hs).mono ?_)
    rintro b ⟨c,hc,rfl⟩
    have hcf : HolomorphicAt m (c ∘ f) (g z) :=
      (GermIdeal.IsCoherent.holomorphicAt_mem hI hc).comp_contMDiff (f := f) (y := g z) hfat
    refine ⟨c ∘ f,?_,rfl⟩
    exact GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self ⟨c,hc,rfl⟩ hcf)
  · refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hs))
    rintro b ⟨c,hc,rfl⟩
    refine IsInSpanAt.mono ?_ (isInSpanAt_comp hg (GermIdeal.mem_pullback_iff.mp hc))
    rintro b' ⟨d,⟨e,he,rfl⟩,rfl⟩
    exact ⟨e,he,rfl⟩

theorem whole_parameter_markedPullback_comp {f : Y → X} {g : Z → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel m) ∞ g)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    markedPullback (m := a) (f ∘ g) M =
      markedPullback (m := a) g (markedPullback (m := m) f M) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · simp only [markedPullback,List.map_map,Function.comp_def]
    rfl
  · exact coherent_parameter_pullback_comp hf hg M.ideal hI

def intrinsicCoefficient {b : ℕ} {A : Type*} [TopologicalSpace A]
    [ChartedSpace (ComplexModel b) A] (M : MarkedIdeal n X) (σ : A → X) : MarkedIdeal b A where
  N := univ
  E := (coeffMarkedAlong M).E.map (σ ⁻¹' ·)
  ideal := GermIdeal.pullback (m := b) σ (coeffMarkedAlong M).ideal
  d := (coeffMarkedAlong M).d

theorem whole_intrinsic_parameter_record {σ : Y → X}
    (hσ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ σ)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (C : Set X) (hC : C ⊆ M.N) (hσC : ∀ z : Y, σ z ∈ C) :
    markedPullback (m := m) σ (contactCoefficient M C) = intrinsicCoefficient (b := m) M σ ∧
    markedPullback (m := m) σ (coeffMarkedAlong M) = intrinsicCoefficient (b := m) M σ ∧
    (intrinsicCoefficient (b := m) M σ).ideal.IsCoherent := by
  have hcoeff := isCoherent_coeffMarkedAlong hI hN
  refine ⟨?_,?_,isCoherent_pullback hσ hcoeff⟩
  · refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ rfl ?_ rfl
    · ext z
      change σ z ∈ C ↔ z ∈ (univ : Set Y)
      exact ⟨fun _ => mem_univ _,fun _ => hσC z⟩
    · exact whole_parameter_pullback_restrictOn hσ (coeffMarkedAlong M).ideal hcoeff C hσC
  · refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ rfl rfl rfl
    ext z
    change σ z ∈ M.N ↔ z ∈ (univ : Set Y)
    exact ⟨fun _ => mem_univ _,fun _ => hC (hσC z)⟩

private theorem intrinsicCoefficient_eq_pullback {σ : Y → X}
    (M : MarkedIdeal n X) (hσN : ∀ z : Y, σ z ∈ M.N) :
    markedPullback (m := m) σ (coeffMarkedAlong M) = intrinsicCoefficient (b := m) M σ := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ rfl rfl rfl
  ext z
  change σ z ∈ M.N ↔ z ∈ (univ : Set Y)
  exact ⟨fun _ => mem_univ _,fun _ => hσN z⟩

private theorem actual_intrinsic_coefficient_square {b c : ℕ}
    {Y₀ : CMfd.{u} m} {A : CMfd.{v} b} {B : CMfd.{w} c}
    {f : Y₀ → X} {σ : A → Y₀} {τ : B → X} {p : A → B}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hσ : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel m) ∞ σ)
    (hτ : ContMDiff 𝓘(ℂ, ComplexModel c) 𝓘(ℂ, ComplexModel n) ∞ τ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel c) ∞ p)
    (hsquare : ∀ z : A, f (σ z) = τ (p z))
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hσN : ∀ z : A, f (σ z) ∈ M.N) (hτN : ∀ z : B, τ z ∈ M.N) :
    intrinsicCoefficient (b := b) (markedPullback (m := m) f M) σ =
      markedPullback (m := b) p (intrinsicCoefficient (b := c) M τ) := by
  have hc := isCoherent_coeffMarkedAlong hI hN
  have he := pullback_coeffMarkedAlong hf M hI hN
  have hl := intrinsicCoefficient_eq_pullback (X := Y₀) (Y := A)
    (markedPullback (m := m) f M) hσN
  have hr := intrinsicCoefficient_eq_pullback (Y := B) M hτN
  rw [← hl,← he,← whole_parameter_markedPullback_comp hf.contMDiff hσ (coeffMarkedAlong M) hc]
  have hs : f ∘ σ = τ ∘ p := funext hsquare
  rw [hs,whole_parameter_markedPullback_comp hτ hp (coeffMarkedAlong M) hc,hr]

/-- Only a produced conclusion from the original geometric and marked inputs. -/
private def ActualIntrinsicContactSquare {Y₀ : CMfd.{u} m}
    (M : MarkedIdeal n X) (f : Y₀ → X) (U : Set X) (u : X → ℂ) (y : Y₀) : Prop :=
  ∃ (k t : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (Γ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) y y)),
    m = n+t ∧ 0 < k ∧ k ≤ n ∧
    Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target ∧
    Γ.source ⊆ (chartAt (ComplexModel m) y).target ∧ flatDomain Φ ⊆ U ∧
    (∀ z ∈ flatDomain Φ,
      (z ∈ M.N ↔ flatMap Φ z ∈ complexCoordinatePlane n k) ∧
      (z ∈ contactCarrier M.N U u ↔ flatMap Φ z ∈ complexCoordinatePlane n (k-1))) ∧
    (∀ z ∈ flatDomain Γ, f z ∈ flatDomain Φ ∧
      (f z ∈ M.N ↔ flatMap Γ z ∈ complexCoordinatePlane m (k+t)) ∧
      (f z ∈ contactCarrier M.N U u ↔ flatMap Γ z ∈ complexCoordinatePlane m ((k-1)+t))) ∧
    0 ∈ parameterOpen Φ (k-1) ∧ 0 ∈ parameterOpen Γ ((k-1)+t) ∧
    parameterMap Φ (k-1) 0 = f y ∧ parameterMap Γ ((k-1)+t) 0 = y ∧
    (∀ z ∈ flatDomain Φ, z ∈ contactCarrier M.N U u →
      coordinateProjection n (k-1) (flatMap Φ z) ∈ parameterOpen Φ (k-1) ∧
      parameterMap Φ (k-1) (coordinateProjection n (k-1) (flatMap Φ z)) = z) ∧
    (∀ z ∈ flatDomain Γ, f z ∈ contactCarrier M.N U u →
      coordinateProjection m ((k-1)+t) (flatMap Γ z) ∈ parameterOpen Γ ((k-1)+t) ∧
      parameterMap Γ ((k-1)+t) (coordinateProjection m ((k-1)+t) (flatMap Γ z)) = z) ∧
    ∃ hMaps : MapsTo (HironakaSmoothSubmersionRelativeDifferentialIdeals.actualTargetProjectionLinear (k-1) t)
        (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)),
    let τ := parameterMapOn Φ (k-1)
    let σ := parameterMapOn Γ ((k-1)+t)
    let p := restrictedOpenMap (X := CMfd.of (n := k-1) (ComplexModel (k-1)))
      (Y := CMfd.of (n := (k-1)+t) (ComplexModel ((k-1)+t)))
      (f := HironakaSmoothSubmersionRelativeDifferentialIdeals.actualTargetProjectionLinear (k-1) t)
      (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)) hMaps
    let A := intrinsicCoefficient (b := k-1) M τ
    let B := intrinsicCoefficient (b := (k-1)+t) (markedPullback (m := m) f M) σ
    ContMDiff 𝓘(ℂ, ComplexModel (k-1)) 𝓘(ℂ, ComplexModel n) ∞ τ ∧
    ContMDiff 𝓘(ℂ, ComplexModel ((k-1)+t)) 𝓘(ℂ, ComplexModel m) ∞ σ ∧
    (∀ z, τ z ∈ contactCarrier M.N U u) ∧
    (∀ z, f (σ z) ∈ contactCarrier M.N U u) ∧
    Manifold.IsSubmersionOfComplement (ComplexModel t)
      𝓘(ℂ, ComplexModel ((k-1)+t)) 𝓘(ℂ, ComplexModel (k-1)) ∞ p ∧
    (∀ z, f (σ z) = τ (p z)) ∧
    markedPullback (m := k-1) τ (contactCoefficient M (contactCarrier M.N U u)) = A ∧
    markedPullback (m := (k-1)+t) σ
      (contactCoefficient (markedPullback (m := m) f M) (f ⁻¹' contactCarrier M.N U u)) = B ∧
    A.ideal.IsCoherent ∧ B.ideal.IsCoherent ∧ B = markedPullback (m := (k-1)+t) p A ∧
    (∀ z q, OrderGE ((k-1)+t) B.N B.ideal z q ↔ OrderGE (k-1) A.N A.ideal (p z) q) ∧
    (∀ z, order ((k-1)+t) B.N B.ideal z = order (k-1) A.N A.ideal (p z)) ∧
    B.cosupp = p ⁻¹' A.cosupp

theorem exists_actual_intrinsic_contact_coefficient_square {Y₀ : CMfd.{u} m} {f : Y₀ → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong M.N M.ideal M.d U u)
    (y : Y₀) (hy : y ∈ f ⁻¹' contactCarrier M.N U u) :
    ActualIntrinsicContactSquare M f U u y := by
  obtain ⟨k,t,Φ,Γ,hmt,hk,hkn,hΦsrc,hΓsrc,_hΦ0,_hΓ0,hΦU,hΦflag,hΓflag,
    hW0,hV0,hτ0,hσ0,_hτOn,_hσOn,hτC,hτRound,hσC,hσRound,hMaps,hSquare,hP⟩ :=
    exists_actual_joint_contact_parameters hf hI hN hu y hy
  let τ := parameterMapOn Φ (k-1)
  let σ := parameterMapOn Γ ((k-1)+t)
  let p := restrictedOpenMap (X := CMfd.of (n := k-1) (ComplexModel (k-1)))
    (Y := CMfd.of (n := (k-1)+t) (ComplexModel ((k-1)+t)))
    (f := HironakaSmoothSubmersionRelativeDifferentialIdeals.actualTargetProjectionLinear (k-1) t)
    (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)) hMaps
  let A := intrinsicCoefficient (b := k-1) M τ
  let B := intrinsicCoefficient (b := (k-1)+t) (markedPullback (m := m) f M) σ
  have hτ : ContMDiff 𝓘(ℂ, ComplexModel (k-1)) 𝓘(ℂ, ComplexModel n) ∞ τ :=
    parameterMapOn_contMDiff Φ (k-1) hΦsrc
  have hσ : ContMDiff 𝓘(ℂ, ComplexModel ((k-1)+t)) 𝓘(ℂ, ComplexModel m) ∞ σ :=
    parameterMapOn_contMDiff Γ ((k-1)+t) hΓsrc
  have hτcontact : ∀ z : parameterOpen Φ (k-1), τ z ∈ contactCarrier M.N U u :=
    fun z => (hτC z.val z.property).1
  have hσcontact : ∀ z : parameterOpen Γ ((k-1)+t), f (σ z) ∈ contactCarrier M.N U u :=
    fun z => (hσC z.val z.property).1
  have hsquare : ∀ z : parameterOpen Γ ((k-1)+t), f (σ z) = τ (p z) :=
    fun z => hSquare z.val z.property
  have hAi := whole_intrinsic_parameter_record
    (Y := CMfd.of (n := k-1) (parameterOpen Φ (k-1))) hτ M hI hN
    (contactCarrier M.N U u) (fun _ hz => hz.1.1) hτcontact
  have hsourceI : (markedPullback (m := m) f M).ideal.IsCoherent := isCoherent_pullback hf.contMDiff hI
  have hsourceN : IsClosedSubmanifold m (markedPullback (m := m) f M).N :=
    HironakaSmoothSubmersionRelativeGeometry.isClosedSubmanifold_preimage_submersion hf hN
  have hBi := whole_intrinsic_parameter_record
    (X := Y₀) (Y := CMfd.of (n := (k-1)+t) (parameterOpen Γ ((k-1)+t)))
    hσ (markedPullback (m := m) f M) hsourceI hsourceN
    (f ⁻¹' contactCarrier M.N U u) (fun _ hz => hz.1.1) hσcontact
  have he : B = markedPullback (m := (k-1)+t) p A :=
    actual_intrinsic_coefficient_square
      (A := CMfd.of (n := (k-1)+t) (parameterOpen Γ ((k-1)+t)))
      (B := CMfd.of (n := k-1) (parameterOpen Φ (k-1)))
      hf hσ hτ hP.isSubmersion.contMDiff hsquare M hI hN
      (fun z => (hσcontact z).1.1) (fun z => (hτcontact z).1.1)
  dsimp only [ActualIntrinsicContactSquare]
  refine ⟨k,t,Φ,Γ,hmt,hk,hkn,hΦsrc,hΓsrc,hΦU,hΦflag,hΓflag,hW0,hV0,hτ0,hσ0,
    hτRound,hσRound,hMaps,hτ,hσ,hτcontact,hσcontact,hP,hsquare,hAi.1,hBi.1,hAi.2.2,hBi.2.2,he,?_,?_,?_⟩
  · intro z q
    change OrderGE ((k-1)+t) B.N B.ideal z q ↔ OrderGE (k-1) A.N A.ideal (p z) q
    rw [he]
    exact orderGE_preimage_iff (hP.isSubmersion.isSubmersionAt z)
      (fun g hg => GermIdeal.IsCoherent.holomorphicAt_mem hAi.2.2 hg) A.N q
  · intro z
    change order ((k-1)+t) B.N B.ideal z = order (k-1) A.N A.ideal (p z)
    rw [he]
    exact order_preimage_eq (hP.isSubmersion.isSubmersionAt z)
      (fun g hg => GermIdeal.IsCoherent.holomorphicAt_mem hAi.2.2 hg) A.N
  · change B.cosupp = p ⁻¹' A.cosupp
    rw [he]
    exact cosupport_preimage_eq hP.isSubmersion hAi.2.2 A.N A.d

theorem exists_original_only_intrinsic_contact_coefficient_square {Y₀ : CMfd.{u} m} {f : Y₀ → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hd : 1 ≤ M.d) (y : Y₀) (hy : y ∈ (markedPullback (m := m) f M).cosupp)
    (hmax : ¬ OrderGE n M.N M.ideal (f y) (M.d+1)) :
    ∃ (U : TopologicalSpace.Opens X) (u : X → ℂ), f y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d (U : Set X) u ∧
      IsTangentDirectionAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)
        M.d (f ⁻¹' (U : Set X)) (u ∘ f) ∧
      ActualIntrinsicContactSquare M f (U : Set X) u y := by
  obtain ⟨U,u,hyU,hu,hup,_,_,hC,_⟩ := exists_joint_original_closed_contacts hf hI hN hd y hy hmax
  have hyt : f y ∈ cosupport n M.N M.ideal M.d := by
    have hyp : y ∈ f ⁻¹' cosupport n M.N M.ideal M.d := by
      rw [← cosupport_preimage_eq hf hI M.N M.d]
      exact hy
    exact hyp
  exact ⟨U,u,hyU,hu,hup,
    exists_actual_intrinsic_contact_coefficient_square hf M hI hN hu y (hC ⟨hyt,hyU⟩)⟩

end
end Hironaka.HironakaSmoothSubmersionContactParameterCoefficientIdeals
