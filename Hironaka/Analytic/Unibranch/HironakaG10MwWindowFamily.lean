import Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow
import Hironaka.Analytic.Unibranch.HironakaG10MwPrivilegedWindow
import Hironaka.Analytic.Unibranch.HironakaG10SameWindowOneFamily
import Hironaka.Analytic.Unibranch.HironakaG10ReducedLocalMapSquare
import Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen
import Hironaka.Coherence.CartanIrreducible
import Hironaka.Analytic.AnalyticSubsetTopology

/-!
# The same-window Schur family of an actual ordinary morphism chart (G10-01-07/09, lane G10MW)

`ChartWindowCriteria d t F K` packages the chart-level asymmetric window criteria of a finite matrix
`F` on `ℂ^d × ℂ^t` over the smooth parameter space `ℂ^d`: ONE family of global sections on an open
`U ∋ 0` whose stalk ideals `𝓗 p` are locally finitely generated, proper at `0`, necessary for
quotient flatness on the CLOSED window `K` and sufficient on its interior, at every `p ∈ U` with
`𝓗 p ≠ ⊤`, for EVERY parameter ideal `I`.  `chartWindowCriteria_of_directExact` produces it from the
literal same-window theorem (`HironakaG10SameWindowOneFamily`).

`exists_actual_window` builds, for an ACTUAL morphism `f : Y ⟶ X` of reduced complex spaces and a point
`c_y` of a source chart lying over a point `c₀` of a base chart: the ambient lift and its square, Cartan
generators of the whole vanishing ideal on an open window `W`, the graph row `F`, the native graph-ideal
identity at every graph point of `W`, the unit ideal off the graph, a closed polydisc `K₁ ∋ c_y` inside
`W`, and the chart criteria for that `F` and `K₁`.  The native/singular-base flatness dictionary that
turns these chart criteria into the hypotheses of `exists_localFlattener_of_asymmetric_windows` is NOT
part of this module (plan items G10-01-08, G10-02-03/04/05).  No named input.
-/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HolGerm OkaRelationSheaf OkaGermBridge
  HironakaG10FlatPolydiscAlgebra HironakaG10FlatResolutionStart HironakaG10FlatPrivilegedEuclidean
  HironakaG10LocSectionNoether HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaHolomorphicJetRankLoci HironakaChowRelativeGraphPresentation
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspaceMaps
  Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen Hironaka.Analytic.Unibranch.HironakaG10NativeSourceFixedSchur
  Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow Hironaka.Analytic.Unibranch.HironakaG10MwPrivilegedWindow
  Hironaka.Analytic.Unibranch.HironakaG10SameWindowOneFamily Hironaka.Analytic.Unibranch.HironakaG10ReducedLocalMapSquare
  Hironaka.Analytic.Unibranch.HironakaG10OpenCoherentProjectionFlatOpen

local instance (d : ℕ) : Algebra ℂ (HolGerm (ComplexModel d)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel d)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d × ComplexModel t)) :=
  (basePullback d t).toAlgebra

/-- The literal chart cokernel at a product point. -/
abbrev chartModule (d t : ℕ) {a b : ℕ} (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (q : ComplexModel d × ComplexModel t) : Type :=
  (Fin a → HolGerm (ComplexModel d × ComplexModel t)) ⧸
    LinearMap.range (Matrix.mulVecLin (fun i j => germAt q (F i j)))

/-- Flatness of the chart cokernel at `q` after base change to `R ⧸ I` (first-projection action). -/
def ChartFlat (d t : ℕ) {a b : ℕ} (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (q : ComplexModel d × ComplexModel t) (I : Ideal (HolGerm (ComplexModel d))) : Prop :=
  Module.Flat (HolGerm (ComplexModel d) ⧸ I)
    ((HolGerm (ComplexModel d) ⧸ I) ⊗[HolGerm (ComplexModel d)] chartModule d t F q)

/-- **Chart-level asymmetric window criteria** of `F` for the window `K`, over the parameter open `U`. -/
structure ChartWindowCriteria (d t : ℕ) {a b : ℕ}
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ) (K : Set (ComplexModel t)) where
  /-- the parameter open set -/
  U : Opens (ComplexModel d)
  zero_mem : (0 : ComplexModel d) ∈ U
  /-- index type of the generating sections -/
  ι : Type
  /-- the literal global sections on `U` -/
  s : ι → (ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel d) U).presheaf.obj (op ⊤)
  finite_near : ∀ p : U, ∃ T : Finset ι, ∀ᶠ y in 𝓝 p, spanFamily s univ y = spanFamily s (T : Set ι) y
  proper_zero : Ideal.map (actualStalkChartEquiv (n := d) (⟨0, zero_mem⟩ : U)).toRingHom
    (spanFamily s univ (⟨0, zero_mem⟩ : U)) ≠ ⊤
  necessary : ∀ p : U, Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≠ ⊤ →
    ∀ I : Ideal (HolGerm (ComplexModel d)), (∀ z ∈ K, ChartFlat d t F (p.val, z) I) →
      Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≤ I
  sufficient : ∀ p : U, Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≠ ⊤ →
    ∀ I : Ideal (HolGerm (ComplexModel d)),
      Ideal.map (actualStalkChartEquiv (n := d) p).toRingHom (spanFamily s univ p) ≤ I →
      ∀ z ∈ interior K, ChartFlat d t F (p.val, z) I

/-- **The same-window theorem gives chart criteria** (one literal Schur section family). -/
theorem chartWindowCriteria_of_directExact (d t : ℕ) {a b c : ℕ}
    {K₀ K₁ : Set (ComplexModel t)} [CompactSpace K₀] [CompactSpace K₁]
    (hK₁ : K₁ ∈ closedPolydiscs t) (hK₁₀ : K₁ ⊆ interior K₀)
    {O : Set (ComplexModel d × ComplexModel t)} (hO : IsOpen O)
    {F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ}
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) O)
    (hK₀ : ∀ z ∈ K₀, (0,z) ∈ O)
    (G₀ : Fin b → Fin c → ComplexModel t → ℂ)
    (hG₀ : ∀ j l, DifferentiableOn ℂ (G₀ j l) (interior K₀))
    (hex : DirectExact (restrictMatrix K₁ hK₁₀ G₀ hG₀)
      (restrictMatrix K₁ hK₁₀ (fun i j x => F i j (0,x)) (zeroFibre_holomorphic d t hO hF hK₀))) :
    Nonempty (ChartWindowCriteria d t F K₁) := by
  obtain ⟨R₀, S₀, U, h0, hSU, hfin, hprop, hnec, hsuf⟩ :=
    original_one_schur_section_family_necessary_and_sufficient_near_support d t hK₁ hK₁₀ hO hF hK₀
      G₀ hG₀ hex
  exact ⟨⟨U, h0, _, _, hfin, hprop, hnec, hsuf⟩⟩

/-! ### The actual chart of an ordinary morphism -/

/-- The ambient extension of a holomorphic lift is complex differentiable at every point of its domain. -/
theorem differentiableAt_of_lift {m d : ℕ} {U : Opens (ComplexModel m)} {V : Opens (ComplexModel d)}
    (φ : U → V) (hφ : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel d) ∞ φ)
    (ψ : ComplexModel m → ComplexModel d) (hψ : ∀ y (hy : y ∈ U), ψ y = (φ ⟨y, hy⟩).val)
    (y : U) : DifferentiableAt ℂ ψ y.val := by
  have hT := eventually_actualTranslatedMap_eq φ ψ hψ y
  have hD := (HironakaActualWholeStalkHolomorphicPullback.actualTranslatedMap_holomorphic hφ y).self_of_nhds
  have hsh : DifferentiableAt ℂ (fun w => ψ (y.val + w)) 0 := by
    have h1 : DifferentiableAt ℂ (fun w =>
        HironakaActualWholeStalkHolomorphicPullback.actualTranslatedMap (n := d) (m := m) φ y w +
          ψ y.val) 0 := hD.add_const _
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hT] with w hw
    rw [hw, sub_add_cancel]
  have hcomp : DifferentiableAt ℂ ((fun w => ψ (y.val + w)) ∘ fun v => v - y.val) y.val := by
    apply DifferentiableAt.comp
    · simpa using hsh
    · exact differentiableAt_id.sub_const _
  refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  simp

/-- The constant `1` lies in the vanishing ideal at a point off a closed set; so the whole stalk ideal is
the unit ideal there. -/
theorem wholeChartStalkIdeal_vanishing_eq_top {m : ℕ} {U : Opens (ComplexModel m)} {C : Set U}
    (hC : IsClosed C) (y : U) (hy : y ∉ C) :
    wholeChartStalkIdeal (vanishingIdeal (n := m) C) y y (mem_chart_source _ y) = ⊤ := by
  have hhol : HolomorphicAt m (fun _ : U => (1 : ℂ)) y :=
    Eventually.of_forall fun _ => mdifferentiableAt_const
  have hmem : (vanishingIdeal (n := m) C).mem y (fun _ => 1) :=
    ⟨hhol, Filter.eventually_of_mem (hC.isOpen_compl.mem_nhds hy) fun y' hy' hy'C => absurd hy'C hy'⟩
  have hu : IsUnit (chartTranslatedGerm y y (mem_chart_source _ y) (fun _ : U => (1 : ℂ)) hhol) := by
    apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    simp [chartTranslatedGerm, translatedGerm, HolGerm.eval_mk]
  exact (wholeChartStalkIdeal (vanishingIdeal (n := m) C) y y (mem_chart_source _ y)).eq_top_of_isUnit_mem
    (Ideal.subset_span ⟨fun _ => 1, hhol, hmem, rfl⟩) hu

/-- **The actual window of an ordinary morphism at one fibre point.** -/
theorem exists_actual_window {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (eX : LocalEmbedding X) (eY : LocalEmbedding Y) (cy : eY.carrier) (c₀ : eX.carrier)
    (hc : f.hom.left.base (eY.toPoint cy) = eX.toPoint c₀) :
    ∃ (U : Opens (ComplexModel eY.dim)) (hUV : U ≤ eY.ambient) (_ : cy.val.val ∈ U)
      (φ : U → eX.ambient) (hφ : ContMDiff 𝓘(ℂ, ComplexModel eY.dim) 𝓘(ℂ, ComplexModel eX.dim) ∞ φ)
      (hCD : ∀ z ∈ (eY.restrict U hUV).carrier, φ z ∈ eX.carrier),
      actualSubspaceMap hφ hCD ≫ eX.map = (eY.restrict U hUV).map ≫ f.hom.left ∧
      ∃ (ψ : ComplexModel eY.dim → ComplexModel eX.dim) (_ : ∀ y (hy : y ∈ U), ψ y = (φ ⟨y, hy⟩).val)
        (W : Set (ComplexModel eY.dim)) (r : ℕ) (g : Fin r → ComplexModel eY.dim → ℂ)
        (K₁ : Set (ComplexModel eY.dim)),
        IsOpen W ∧ W ⊆ U ∧ K₁ ⊆ W ∧ K₁ ∈ 𝓝 cy.val.val ∧ IsCompact K₁ ∧
        DifferentiableOn ℂ ψ W ∧ (∀ j, DifferentiableOn ℂ (g j) W) ∧
        (∀ y : U, y.val ∈ W →
          wholeChartStalkIdeal (vanishingIdeal (n := eY.dim) (M := U) (eY.restrict U hUV).carrier) y y
            (mem_chart_source _ y) = Ideal.span (Set.range fun j => germAt y.val (g j))) ∧
        (∀ x : (eY.restrict U hUV).carrier, x.val.val ∈ W →
          Ideal.map (ambientGermEquiv eX.dim eY.dim).toRingHom (nativeRelativeGraphIdeal hφ _ x) =
            idealAt eX.dim eY.dim (graphRow ψ c₀.val.val g)
              (ψ x.val.val - c₀.val.val, x.val.val)) ∧
        (∀ (y : U), y.val ∈ W → y ∉ (eY.restrict U hUV).carrier → ∀ p : ComplexModel eX.dim,
          idealAt eX.dim eY.dim (graphRow ψ c₀.val.val g) (p, y.val) = ⊤) ∧
        (∀ z ∈ W, ∀ (p : ComplexModel eX.dim) (k : Fin eX.dim),
          p k + c₀.val.val k - ψ z k ≠ 0 →
          idealAt eX.dim eY.dim (graphRow ψ c₀.val.val g) (p, z) = ⊤) ∧
        Nonempty (ChartWindowCriteria eX.dim eY.dim (graphRow ψ c₀.val.val g) K₁) := by
  classical
  -- the ambient lift and its square
  obtain ⟨U, hUV, hcU, φ, hφ, hCD, hsq⟩ :=
    exists_reduced_local_map_square f eX eY cy ⟨c₀, hc.symm⟩
  let ψ : ComplexModel eY.dim → ComplexModel eX.dim :=
    fun z => if h : z ∈ U then (φ ⟨z, h⟩).val else 0
  have hψ : ∀ y (hy : y ∈ U), ψ y = (φ ⟨y, hy⟩).val := fun y hy => dif_pos hy
  -- Cartan generators of the whole vanishing ideal on an open window
  let C : Set U := (eY.restrict U hUV).carrier
  have hCan : IsComplexAnalyticSubset (n := eY.dim) C := (eY.restrict U hUV).analytic
  have hcoh : (vanishingIdeal (n := eY.dim) C).IsCoherent :=
    CartanIrreducible.cartanCoherence (n := eY.dim) (X := U) C hCan
  obtain ⟨W, hW, hcW, hWU, r, g, hg, hgen⟩ :=
    exists_generator_window U (vanishingIdeal (n := eY.dim) C) hcoh ⟨cy.val.val, hcU⟩
  have hφW : DifferentiableOn ℂ ψ W := fun z hz =>
    (differentiableAt_of_lift φ hφ ψ hψ ⟨z, hWU hz⟩).differentiableWithinAt
  have hφhol : ∀ z ∈ W, ∀ k, HolAt (fun w => ψ w k) z := fun z hz k =>
    holAt_of_differentiableOn hW
      ((EuclideanSpace.proj k : ComplexModel eX.dim →L[ℂ] ℂ).differentiable.comp_differentiableOn hφW) hz
  have hghol : ∀ z ∈ W, ∀ j, HolAt (g j) z := fun z hz j => holAt_of_differentiableOn hW (hg j) hz
  -- the row and the privileged window of its zero fibre
  let F := graphRow ψ c₀.val.val g
  have hFO := graphRow_differentiableOn (d := eX.dim) ψ c₀.val.val g hφW hg
  have hF0 : ∀ i j, HolAt (fun z => F i j (0, z)) cy.val.val := by
    intro i j
    have h := holAt_graphRow (d := eX.dim) ψ c₀.val.val g hW hφW hg
      (q := ((0 : ComplexModel eX.dim), cy.val.val)) hcW i j
    exact HolAt.comp (φ := fun z : ComplexModel eY.dim => ((0 : ComplexModel eX.dim), z))
      (y := cy.val.val) h (continuous_const.prodMk continuous_id)
      (fun _ => (differentiableAt_const _).prodMk differentiableAt_id)
  obtain ⟨K₀, K₁, hK₀c, hK₁c, hK₁, hK₁n, hK₀W, hK₁₀, c, G₀, hG₀, hFK, _, hex⟩ :=
    exists_privileged_window eY.dim (fun i j z => F i j (0, z)) cy.val.val hF0 W
      (hW.mem_nhds hcW)
  let : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c
  let : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁c
  have hO : IsOpen (univ ×ˢ W : Set (ComplexModel eX.dim × ComplexModel eY.dim)) := isOpen_univ.prod hW
  have hK₀O : ∀ z ∈ K₀, ((0 : ComplexModel eX.dim), z) ∈ (univ ×ˢ W) := fun z hz => ⟨mem_univ _, hK₀W hz⟩
  have hcrit : Nonempty (ChartWindowCriteria eX.dim eY.dim F K₁) :=
    chartWindowCriteria_of_directExact eX.dim eY.dim hK₁ hK₁₀ hO hFO hK₀O G₀ hG₀ hex
  refine ⟨U, hUV, hcU, φ, hφ, hCD, hsq, ψ, hψ, W, r, g, K₁, hW, hWU,
    (hK₁₀.trans interior_subset).trans hK₀W,
    hK₁n, hK₁c, hφW, hg, fun y hy => hgen y hy, ?_, ?_, ?_, hcrit⟩
  · intro x hxW
    exact map_nativeRelativeGraphIdeal_eq_idealAt φ hφ C x ψ hψ (hφhol _ hxW) c₀.val.val g
      (hghol _ hxW) (hgen x.val hxW)
  · intro y hyW hyC p
    apply idealAt_graphRow_eq_top_of_span ψ c₀.val.val g p y.val (hghol _ hyW)
    rw [← hgen y hyW]
    exact wholeChartStalkIdeal_vanishing_eq_top hCan.isClosed y hyC
  · intro z hz p k hk
    exact idealAt_graphRow_eq_top_of_ne ψ c₀.val.val g p z (hφhol z hz) k hk

end

end Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
