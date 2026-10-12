/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.ControlledTransformZeroExact
import Hironaka.Invariant.MemberNonContainedPullbackExact
import Hironaka.MarkedIdeal.ControlledProductTransformExact
import Hironaka.Resolution.HironakaNormalCrossingsMarkedAdmissibility

/-! # Exact original NC weights on the actual finite separation

Actual original NC coordinates internally give the COMPLETE reduced vanishing
ideal and exact intrinsic original branch-count order. True highest-centre
blowups transport the SAME entire original ideal with exact new exceptional
power r, and its SAME marking-one control with power r-1. Real old boundary
ideals pull back to their entire actual strict ideals without new powers.

The genuine internally generated separation records these exact weights at
EVERY literal prefix. Actual joint coordinates compute intrinsic original
exponents even at intersections and on true connected components, and produce
original local branches with exponent one. Complete actual whole ideal orders
are globally at most n*n, without compactness or a supplied bound/certificate.

Finite remaining Cartier division is a subsequent producer. Old ordered
colex canonical identification and arbitrary unrelated marked ideals remain
OPEN. No caller ideal/coefficient/support/tower/termination certificate enters
the original NC consumers. Blueprint:
`hironaka-normal-crossings-original-exponents-extension.tex`.
-/


set_option autoImplicit false
open Set Filter Metric
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsOriginalExponents
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm AnalyticGermDecomposition
  HolomorphicGermReducednessBridge HironakaNormalCrossingsBranchOverlap
  BlowupFlatCoordinates CartanIrreducibleReduction OkaRelationSheaf OkaIdealOperations AnalyticDescendingChain
open GermIdealOrder IdealWeightPowers OrderTaylor InvertibleIdealQuotient
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata BlowupTowers
open Hironaka
noncomputable section
variable {n : ℕ}

private theorem holomorphic_product {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => ∏ i ∈ s, f i z) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using eventually_differentiableAt_const (E := ComplexModel n) 1
  | @insert i s hi ih => simpa only [Finset.prod_insert hi] using eventually_differentiableAt_mul (hf i) ih

private theorem germ_product {ι : Type*} (s : Finset ι)
    (f : ι → ComplexModel n → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    HolGerm.mk (fun z => ∏ i ∈ s, f i z) (holomorphic_product s f hf) =
      ∏ i ∈ s, HolGerm.mk (f i) (hf i) := by
  apply Subtype.ext
  rw [HolGerm.coe_mk, SubmonoidClass.coe_finsetProd]
  simp only [HolGerm.coe_mk]
  have h := map_prod
    (Germ.coeRingHom (𝓝 (0 : ComplexModel n)) :
      (ComplexModel n → ℂ) →+* Germ (𝓝 (0 : ComplexModel n)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

/-- The whole vanishing germ ideal of an actual squarefree equation is its complete principal ideal. -/
theorem vanishingIdeal_eq_span_of_squarefree (f : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hs : Squarefree (HolGerm.mk f hf)) :
    AnalyticGermDecomposition.vanishingIdeal {z | f z = 0} = Ideal.span {HolGerm.mk f hf} := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  have hred : (Ideal.span {HolGerm.mk f hf}).radical = Ideal.span {HolGerm.mk f hf} := by
    apply Ideal.radical_eq_iff.mpr
    intro a ha
    obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp ha
    exact Ideal.mem_span_singleton.mpr (hs.isRadical N a (Ideal.mem_span_singleton.mp hN))
  apply le_antisymm
  · rw [← hred]
    simpa only [Fin.forall_fin_one] using
      RueckertNullstellensatz.vanishingIdeal_le_radical (Ideal.span {HolGerm.mk f hf})
        (fun _ : Fin 1 => f) (fun _ => ⟨hf, Ideal.subset_span (Set.mem_singleton _)⟩)
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun _ h => h)

/-- Surjective actual coordinate derivatives produce the reduced whole coordinate product internally. -/
theorem squarefree_coordinate_product {F : ComplexModel n → ComplexModel n}
    (hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z) (hF0 : F 0 = 0)
    (hsurj : Function.Surjective (fderiv ℂ F 0)) (S : Finset (Fin n))
    (hc : ∀ i : Fin n, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => F z i) z) :
    Squarefree (HolGerm.mk (fun z => ∏ i ∈ S, F z i) (holomorphic_product S _ hc)) := by
  classical
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel n)) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean n
  rw [germ_product]
  have hp : ∀ i : Fin n, Prime (HolGerm.mk (fun z => F z i) (hc i)) :=
    fun i => prime_coordinate_of_surjective_fderiv hF hF0 hsurj i
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    change IsRelPrime (HolGerm.mk (fun z => F z i) (hc i)) (HolGerm.mk (fun z => F z j) (hc j))
    rw [(hp i).irreducible.isRelPrime_iff_not_dvd]
    intro hdvd
    apply hij
    exact eq_of_associated_coordinates_of_surjective_fderiv hF hF0 hsurj i j
      ((hp i).irreducible.associated_of_dvd (hp j).irreducible hdvd)
  · intro i hi
    exact (hp i).squarefree

/-- The SAME actual reduced equation generates the COMPLETE vanishing ideal at EVERY nearby stalk. -/
theorem squarefree_equation_generates_all_nearby_stalks (f : ComplexModel n → ℂ)
    (hf : HolAt f 0) (hs : Squarefree (HolGerm.mk f hf)) :
    ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ f (Metric.ball 0 ε) ∧
      ∀ y ∈ Metric.ball 0 ε, ∀ a : ComplexModel n → ℂ,
        vanishingIdealF {x | f x = 0} y a ↔ InSpanAt (fun _ : Fin 1 => f) y a := by
  classical
  have hideal := vanishingIdeal_eq_span_of_squarefree f hf hs
  obtain ⟨Ω, hΩ, h0Ω, hfΩ⟩ := hf.exists_isOpen
  have hlocal := localCartan_of_irreducibleLocalCartan (CartanIrreducible.irreducibleLocalCartan n)
  have hcoh : IdealFGAt (vanishingIdealF {x | f x = 0}) 0 := by
    simpa only [Fin.forall_fin_one] using hlocal Ω hΩ 1 (fun _ => f) (fun _ => hfΩ) 0 h0Ω
  obtain ⟨U, hU, h0U, μ, inst, s, hsU, hsgen⟩ := hcoh
  let : Fintype μ := inst
  have hquot : ∀ i : μ, ∃ (b : ComplexModel n → ℂ) (hb : HolAt b 0),
      s i =ᶠ[𝓝 0] fun x => b x * f x := by
    intro i
    have hsi : vanishingIdealF {x | f x = 0} 0 (s i) :=
      (hsgen 0 h0U _).mpr (inSpanAt_self (fun j => holAt_of_differentiableOn hU (hsU j) h0U) i)
    have hdiv : HolGerm.mk f hf ∣ HolGerm.mk (s i) hsi.1 :=
      Ideal.mem_span_singleton.mp (hideal ▸ mem_vanishingIdeal_mk.mpr hsi.2)
    obtain ⟨B, hB⟩ := hdiv
    obtain ⟨b, hb, hrep⟩ := HolGerm.exists_eq_mk B
    have heq : HolGerm.mk (s i) hsi.1 =
        HolGerm.mk (fun x => b x * f x) (eventually_differentiableAt_mul hb hf) := by
      rw [HolGerm.mk_mul b f hb hf, mul_comm, ← hrep]
      exact hB
    exact ⟨b, hb, HolGerm.mk_eq_mk_iff.mp heq⟩
  choose b hb hbeq using hquot
  have hev : ∀ᶠ y in 𝓝 (0 : ComplexModel n), y ∈ U ∧ HolAt f y ∧
      (∀ i, HolAt (b i) y) ∧ (∀ i, s i y = b i y * f y) := by
    filter_upwards [hU.mem_nhds h0U, OkaRelationSheaf.HolAt.eventually hf,
      eventually_all.mpr (fun i => OkaRelationSheaf.HolAt.eventually (hb i)),
      eventually_all.mpr hbeq] with y hy hfy hby hsy
    exact ⟨hy, hfy, hby, hsy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun y hy => (hball y hy).2.1.differentiableAt.differentiableWithinAt, ?_⟩
  intro y hy a
  rcases hball y hy with ⟨hyU, _, hby, _⟩
  constructor
  · intro ha
    obtain ⟨hahol, c, hc, hsum⟩ := (hsgen y hyU a).mp ha
    refine ⟨hahol, fun _ x => ∑ i, c i x * b i x,
      fun _ => OkaRelationSheaf.HolAt.fintype_sum (fun i => (hc i).mul (hby i)), ?_⟩
    filter_upwards [hsum, isOpen_ball.mem_nhds hy] with x hsum hx
    simp only [Fin.sum_univ_one]
    rw [hsum]
    calc
      ∑ i, c i x * s i x = ∑ i, (c i x * b i x) * f x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hball x hx).2.2.2 i, mul_assoc]
      _ = (∑ i, c i x * b i x) * f x := (Finset.sum_mul _ _ _).symm
  · rintro ⟨hahol, c, _, heq⟩
    refine ⟨hahol, ?_⟩
    filter_upwards [heq] with x heq hfx
    simpa only [Fin.sum_univ_one, hfx, mul_zero] using heq

private theorem shifted_holomorphic {q : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) q) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => Φ.toFun (z+q)) z := by
  have ht : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
    simpa only [zero_add] using (continuous_add_const q).tendsto 0
  filter_upwards [ht.eventually (Φ.isOpen_source.mem_nhds Φ.center_mem_source)] with z hz
  exact (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)).comp z
    (differentiableAt_id.add_const q)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every true original flattening produces the whole SAME coordinate product at all nearby actual chart stalks. -/
theorem whole_original_coordinate_product_dictionary {H : Set M} (x : M)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (S : Finset (Fin n))
    (hflat : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) :
    let f : ComplexModel n → ℂ := fun z => ∏ i ∈ S, Φ.toFun (z + chartAt (ComplexModel n) x x) i
    ∃ hf : HolAt f 0, Squarefree (HolGerm.mk f hf) ∧ HolGerm.mk f hf ≠ 0 ∧
    AnalyticGermDecomposition.vanishingIdeal (chartGerm H x) =
        Ideal.span {HolGerm.mk f hf} ∧
      ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ f (ball 0 ε) ∧
        ∀ y ∈ ball 0 ε, ∀ a : ComplexModel n → ℂ,
          vanishingIdealF (chartGerm H x) y a ↔
            InSpanAt (fun _ : Fin 1 => f) y a := by
  classical
  dsimp only
  let e := chartAt (ComplexModel n) x
  let q := e x
  let F : ComplexModel n → ComplexModel n := fun z => Φ.toFun (z+q)
  have hF : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ F z := shifted_holomorphic Φ
  have hc : ∀ i : Fin n, HolAt (fun z => F z i) 0 := by
    intro i
    exact hF.mono (fun z hz => (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt.comp z hz)
  let f : ComplexModel n → ℂ := fun z => ∏ i ∈ S, F z i
  have hf : HolAt f 0 := holomorphic_product S _ hc
  have hs : Squarefree (HolGerm.mk f hf) := squarefree_coordinate_product hF
    (by simpa only [F,zero_add] using h0) (surjective_fderiv_shifted Φ) S hc
  have hzero : chartGerm H x =ᶠ[𝓝 0] {z | f z = 0} := by
    have ht : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
      simpa only [zero_add] using (continuous_add_const q).tendsto 0
    have hInv : Tendsto (fun z : ComplexModel n => e.symm (z+q)) (𝓝 0) (𝓝 x) := by
      simpa only [Function.comp_def,e.left_inv (mem_chart_source _ x)] using
        (e.continuousAt_symm (e.map_source (mem_chart_source _ x))).tendsto.comp ht
    have hdom := (ht.eventually (e.open_target.mem_nhds (e.map_source (mem_chart_source _ x)))).and
      (hInv.eventually ((isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)))
    filter_upwards [hdom] with z hz
    apply propext
    change (z+q ∈ e.target ∧ e.symm (z+q) ∈ H) ↔ f z = 0
    apply (and_iff_right hz.1).trans
    rw [hflat _ hz.2]
    simp only [flatCoord,f,F,Finset.prod_eq_zero_iff]
    change (∃ j ∈ S, Φ.toFun (e (e.symm (z+q))) j = 0) ↔ ∃ j ∈ S, Φ.toFun (z+q) j = 0
    rw [e.right_inv hz.1]
  refine ⟨hf,hs,hs.ne_zero,?_,?_⟩
  · rw [AnalyticGermDecomposition.vanishingIdeal_congr hzero,vanishingIdeal_eq_span_of_squarefree f hf hs]
  · obtain ⟨ε,hε,hfε,hgen⟩ := squarefree_equation_generates_all_nearby_stalks f hf hs
    obtain ⟨δ,hδ,hδgen⟩ := Metric.eventually_nhds_iff_ball.mp
      (CartanIrreducibleReduction.vanishingIdealF_congr_eventually hzero)
    refine ⟨min ε δ,lt_min hε hδ,hfε.mono (ball_subset_ball (min_le_left _ _)),?_⟩
    intro y hy a
    exact (hδgen y (ball_subset_ball (min_le_right _ _) hy) a).trans
      (hgen y (ball_subset_ball (min_le_left _ _) hy) a)

/-- Original genuine NC input internally supplies its true whole squarefree coordinate-product dictionary. -/
theorem exists_original_whole_coordinate_product {H : Set M}
    (hH : HironakaNormalCrossingsLocalBranches.IsNormalCrossingsCarrier (n := n) H) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)), Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) ∧
      let f : ComplexModel n → ℂ := fun z => ∏ i ∈ S, Φ.toFun (z + chartAt (ComplexModel n) x x) i
      ∃ hf : HolAt f 0, Squarefree (HolGerm.mk f hf) ∧ HolGerm.mk f hf ≠ 0 ∧
        AnalyticGermDecomposition.vanishingIdeal (chartGerm H x) = Ideal.span {HolGerm.mk f hf} ∧
        ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ f (ball 0 ε) ∧
          ∀ y ∈ ball 0 ε, ∀ a : ComplexModel n → ℂ,
            vanishingIdealF (chartGerm H x) y a ↔ InSpanAt (fun _ : Fin 1 => f) y a := by
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 x
  exact ⟨Φ,S,hsrc,h0,hflat,whole_original_coordinate_product_dictionary x Φ h0 S hflat⟩

/-- The actual complete manifold ideal, at every nearby stalk, is the SAME original coordinate product. -/
theorem vanishingIdeal_mem_iff_original_flat_product {H : Set M} (x : M)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x) = 0) (S : Finset (Fin n))
    (hflat : ∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) :
    ∀ᶠ y in 𝓝 x, ∀ g : M → ℂ,
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H).mem y g ↔
        IsInSpanAt (n := n) (· = fun p => ∏ i ∈ S, flatCoord Φ i p) y g := by
  obtain ⟨hf,_,_,_,ε,hε,_,hgen⟩ := whole_original_coordinate_product_dictionary x Φ h0 S hflat
  let e := chartAt (ComplexModel n) x
  let q := e x
  let c : M → ComplexModel n := fun y => e y - q
  let f : ComplexModel n → ℂ := fun z => ∏ i ∈ S, Φ.toFun (z+q) i
  let G : M → ℂ := fun p => ∏ i ∈ S, flatCoord Φ i p
  let U : Set M := flatDomain Φ ∩ c ⁻¹' ball 0 ε
  have hU : IsOpen U := by
    change IsOpen (flatDomain Φ ∩ e ⁻¹' ((fun w => w-q) ⁻¹' ball 0 ε))
    have hs : Continuous (fun w : ComplexModel n => w-q) := continuous_id.sub continuous_const
    have heU : IsOpen (e.source ∩ e ⁻¹' ((fun w => w-q) ⁻¹' ball (0 : ComplexModel n) ε)) :=
      e.isOpen_inter_preimage (isOpen_ball.preimage hs)
    have heq : flatDomain Φ ∩ (e.source ∩ e ⁻¹' ((fun w => w-q) ⁻¹' ball (0 : ComplexModel n) ε)) =
        flatDomain Φ ∩ e ⁻¹' ((fun w => w-q) ⁻¹' ball (0 : ComplexModel n) ε) := by
      rw [← inter_assoc,inter_eq_left.mpr (show flatDomain Φ ⊆ e.source from fun _ hy => hy.1)]
    rw [← heq]
    exact (isOpen_flatDomain Φ).inter heU
  have hxU : x ∈ U := by
    refine ⟨mem_flatDomain_self Φ,?_⟩
    change e x-e x ∈ ball (0 : ComplexModel n) ε
    simpa only [sub_self] using (mem_ball_self hε : (0 : ComplexModel n) ∈ ball 0 ε)
  have hcf : ∀ p : M, f (c p) = G p := by
    intro p
    simp only [f,c,G,q,e,sub_add_cancel,flatCoord]
  filter_upwards [hU.mem_nhds hxU] with y hy g
  constructor
  · intro hg
    let a : ComplexModel n → ℂ := fun z => g (e.symm (z+q))
    have hgh : HolAt (fun w => g (e.symm w)) (c y+q) := by
      simpa only [c,sub_add_cancel] using CartanLocalReduction.holAt_comp_chart_symm hy.1.1 hg.1
    have hah : HolAt a (c y) := hgh.comp (φ := fun z : ComplexModel n => z+q)
      (y := c y) (continuous_add_const q) (fun _ => differentiableAt_id.add_const q)
    have hadd : Tendsto (fun z : ComplexModel n => z+q) (𝓝 (c y)) (𝓝 (e y)) := by
      simpa only [c,sub_add_cancel] using (continuous_add_const q).tendsto (c y)
    have hi : Tendsto (fun z => e.symm (z+q)) (𝓝 (c y)) (𝓝 y) := by
      simpa only [Function.comp_def,e.left_inv hy.1.1] using
        (e.continuousAt_symm (e.map_source hy.1.1)).tendsto.comp hadd
    have hvan : vanishingIdealF (chartGerm H x) (c y) a := by
      refine ⟨hah,?_⟩
      filter_upwards [hi.eventually hg.2] with z hz hzH
      exact hz hzH.2
    obtain ⟨_,b,hb,heq⟩ := (hgen (c y) hy.2 a).mp hvan
    apply isInSpanAt_eq_iff.mpr
    have hbcomp : HolomorphicAt n (fun p => b 0 (c p)) y :=
      CartanLocalReduction.holomorphicAt_comp_chart hy.1.1
        ((hb 0).comp (φ := fun w : ComplexModel n => w-q) (y := e y)
          (continuous_id.sub continuous_const) (fun _ => differentiableAt_id.sub (differentiableAt_const _)))
    refine ⟨hg.1,fun p => b 0 (c p),hbcomp,?_⟩
    have hc : Tendsto c (𝓝 y) (𝓝 (c y)) := (e.continuousAt hy.1.1).sub_const q
    filter_upwards [e.open_source.mem_nhds hy.1.1,hc.eventually heq] with p hp heqp
    simp only [Fin.sum_univ_one] at heqp
    change a (c p) = b 0 (c p) * f (c p) at heqp
    rw [hcf p] at heqp
    simpa only [a,c,sub_add_cancel,e.left_inv hp,G] using heqp
  · intro hg
    obtain ⟨hgh,b,_,heq⟩ := isInSpanAt_eq_iff.mp hg
    refine ⟨hgh,?_⟩
    filter_upwards [heq,hU.mem_nhds hy] with p hp hpU hpH
    obtain ⟨i,hi,hiz⟩ := (hflat p hpU.1).mp hpH
    have hG0 : (∏ i ∈ S, flatCoord Φ i p) = 0 := Finset.prod_eq_zero hi hiz
    rw [hp,hG0,mul_zero]

/-- True whole principal generation and actual point-ideal powers compute the whole ideal order exactly. -/
theorem order_eq_of_whole_principal_generator {I : GermIdeal n M} {x : M} {f : M → ℂ}
    (hf : HolomorphicAt n f x)
    (hgen : ∀ g, I.mem x g ↔ IsInSpanAt (n := n) (· = f) x g)
    {a : ℕ} (hpow : (idealPow (pointIdeal n x) a).mem x f)
    (hnot : ¬ (idealPow (pointIdeal n x) (a+1)).mem x f) :
    GermIdealOrder.order n univ I x = (a : ℕ∞) := by
  have hhol : ∀ g, I.mem x g → HolomorphicAt n g x := fun g hg => ((hgen g).mp hg).holomorphicAt
  have hfmem : I.mem x f := (hgen f).mpr (isInSpanAt_self rfl hf)
  apply le_antisymm
  · unfold GermIdealOrder.order
    apply iSup₂_le
    intro q hq
    have hqa : q ≤ a := by
      by_contra hqa
      have ha1 : a+1 ≤ q := by omega
      exact hnot (mem_idealPow_of_vanishesToOrderOn_univ ((hq.mono ha1) f hfmem))
    exact_mod_cast hqa
  · apply (le_order_iff hhol).mpr
    intro g hg
    refine ⟨g,?_,Eventually.of_forall fun _ _ => rfl⟩
    apply mem_idealPow_of_isInSpanAt
    exact ((hgen g).mp hg).mono (fun k (hk : k = f) => hk ▸ hpow)

open HironakaNormalCrossingsBoundaryTransform NormalCrossings BlowupStrictSubmanifold

/-- Actual tangential old-boundary coordinates prove that no highest centre germ is contained in an old member. -/
theorem not_eventually_highest_subset_old_member {H : Set M} {E : List (Set M)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : M, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {x : M} (hx : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x)
    (i : Fin E.length) :
    ¬ ∀ᶠ y in 𝓝 x, r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) y → y ∈ E.get i := by
  intro hsub
  have hxi : x ∈ E.get i := hsub.self_of_nhds hx
  obtain ⟨Φ,B,hsrc,h0,hC,hH,hB,hinj,hBE⟩ := exists_highest_joint_coordinates h hbound hx
  obtain ⟨b,hBi⟩ := Finset.card_eq_one.mp (hB i hxi).1
  have hb : b.val < n-r := (hB i hxi).2 b (by rw [hBi]; simp)
  obtain ⟨y,⟨hyD,hyb,hycoord⟩,hysub⟩ :=
    ((MonomialPart.frequently_flatMap_ne_zero hsrc (mem_flatDomain_self Φ) {b}).and_eventually hsub).exists
  have hyC : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) y := by
    apply (hC y hyD).mpr
    intro a ha
    change GiraudAlong.flatMap Φ y a = 0
    rw [hycoord a (by simp only [Finset.mem_singleton]; intro hab; subst hab; omega)]
    change Φ.toFun (chartAt (ComplexModel n) x x) a = 0
    simp only [h0,PiLp.zero_apply]
  have hyE := (hBE i hxi y hyD).mp (hysub hyC)
  exact hyb b (Finset.mem_singleton_self b) (hyE b (by rw [hBi]; simp))

/-- The SAME whole original NC ideal has actual order equal to the intrinsic number of original branches. -/
theorem order_vanishingIdeal_eq_branchMultiplicity {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) :
    GermIdealOrder.order n univ (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) x =
      (branchMultiplicity hH x : ℕ∞) := by
  classical
  obtain ⟨Φ,hsrc,h0,S,hflat⟩ := hH.2 x
  have hgen := (vanishingIdeal_mem_iff_original_flat_product x Φ h0 S hflat).self_of_nhds
  have hprod := MonomialCase.prod_flatCoord_pow_order Φ (id : Fin n → Fin n) (fun _ => 1)
    (mem_flatDomain_self Φ) S (fun i _ => by simp [flatCoord,h0])
  simp only [id_eq,pow_one,Finset.sum_const,smul_eq_mul,mul_one] at hprod
  rw [branchMultiplicity_eq_card hH Φ h0 S hflat]
  exact order_eq_of_whole_principal_generator
    (MonomialPart.holomorphicAt_finset_prod S (fun i _ => holomorphicAt_flatCoord Φ i (mem_flatDomain_self Φ)))
    hgen hprod.1 hprod.2

/-- ALL natural order predicates are exactly the intrinsic original NC count predicates, including zero. -/
theorem mem_original_order_cosupport_iff {H : Set M}
    (hH : IsNormalCrossingsCarrier (n := n) H) (x : M) (q : ℕ) :
    x ∈ GermIdealOrder.cosupport n univ (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) q ↔
      q ≤ branchMultiplicity hH x := by
  change (x ∈ univ ∧ _) ↔ _
  rw [and_iff_right (mem_univ x),← le_order_iff
    (𝔞 := Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) (fun _ hg => hg.1),
    order_vanishingIdeal_eq_branchMultiplicity hH x]
  exact_mod_cast (Iff.rfl : q ≤ branchMultiplicity hH x ↔ q ≤ branchMultiplicity hH x)

variable {A D : CMfd.{u} n}

/-- Every actual old boundary member keeps its COMPLETE ideal under a genuine highest blowup. -/
theorem pullback_old_member_eq_vanishingIdeal_strict {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {π : D → A}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π)
    (i : Fin E.length) :
    GermIdeal.pullback (m := n) π (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (E.get i)) =
      Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n)
        (geoStrictTransform π {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} (E.get i)) := by
  refine GermIdeal.ext (funext fun z => funext fun g => propext ?_)
  by_cases hz : r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) (π z)
  · exact MemberPullback.mem_pullback_member_iff_of_not_subset hπ
      (isSNCDivisor_of_boundaryAdapted h) (hasNormalCrossings_highest_boundary h hbound) i
      (not_eventually_highest_subset_old_member h hbound hz i) g
  · exact (BlowupStrictIdeal.mem_pullback_iff_mem_mul_of_notMem hπ
      (h.2.1 _ (List.get_mem _ _)) hz g).trans
      (BlowupStrictIdeal.mem_mul_vanishingIdeal_iff_of_notMem hπ _ hz g)

open MarkedIdeals MarkedIdeals.MarkedIdeal HironakaNormalCrossingsTotalIdeal
  HironakaHypersurfaceStrictIdeal HironakaNormalCrossingsHighestStratumBlowup
  BlowupTowers HironakaNormalCrossingsBoundarySeparation

/-- The internally computed whole-ideal count dictionary makes the actual highest centre admissible with its exact mark. -/
theorem isAdmissibleCentre_highest_original_mark {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ}
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r) :
    (⟨univ,E,Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H,r⟩ : MarkedIdeal n A).IsAdmissibleCentre
      {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} := by
  refine ⟨isClosedSubmanifold_highest_superlevel (isNormalCrossingsCarrier_of_boundaryAdapted h) hbound,?_,
    hasNormalCrossings_highest_boundary h hbound⟩
  intro x hx
  exact (mem_original_order_cosupport_iff (isNormalCrossingsCarrier_of_boundaryAdapted h) x r).mpr hx

theorem controlledTransform_original_highest_eq_strict {m : ℕ}
    {A D : CMfd.{u} (m+1)} {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := m+1) H E) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    {π : D → A}
    (hπ : IsBlowupAlong (m+1) {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π) :
    BlowupControlledTransform.controlledTransform hπ
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := m+1) H) r =
        Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := m+1) (strictTransform (m+1) π H) := by
  let hH := isNormalCrossingsCarrier_of_boundaryAdapted h
  let C : Set A := {x | r ≤ branchMultiplicity hH x}
  let M : MarkedIdeal (m+1) A := ⟨univ,E,Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := m+1) H,r⟩
  have hI := isInvertible_vanishingIdeal_normalCrossingsCarrier hH
  have hcoh := DivisorMetric.isCoherent_of_isInvertible hI
  have hCadm : M.IsAdmissibleCentre C := isAdmissibleCentre_highest_original_mark h hbound
  have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hCadm.1 hCadm.2.1
  have hwf : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hcoh,
    isSNCDivisor_of_boundaryAdapted h,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor
      (isSNCDivisor_of_boundaryAdapted h)⟩
  have hCorder : ∀ c ∈ C, GermIdealOrder.order (m+1) univ M.ideal c = (r : ℕ∞) := by
    intro c hc
    rw [order_vanishingIdeal_eq_branchMultiplicity hH c]
    exact_mod_cast (hbound c).antisymm hc
  have hgeo := geoStrictTransform_highest_eq_strictTransform hH hr hbound hπ
  have hSDense : strictTransform (m+1) π H ⊆ closure (strictTransform (m+1) π H \ π ⁻¹' C) := by
    rw [← hgeo]
    apply closure_mono
    intro y hy
    exact ⟨subset_closure hy,hy.2⟩
  have hEnext := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hwf hCadm hπ).isSNCDivisor
  change IsSNCDivisor (m+1) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) at hEnext
  have hDreg : ∀ y ∈ π ⁻¹' C, RegularAtDim (n := m+1) (π ⁻¹' C) y m := by
    let i : Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length := ⟨E.length,by simp⟩
    have hi : (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get i = π ⁻¹' C := by simp [i,List.get_eq_getElem]
    intro y hy
    simpa only [hi] using SNCGlobalPrimeComponents.regularAtDim_member hEnext i (x := y) (by simpa only [hi] using hy)
  apply eq_vanishingIdeal_of_reduced_off_smooth_divisor _ (isInvertible_controlledTransform hπ hI r hle)
    isClosed_closure hSDense hDreg
    (fun y hy g => controlledTransform_vanishingIdeal_strict_mem_iff_of_notMem hπ h.1 r hy g)
  intro z hz
  have hzN : z ∈ geoStrictTransform π C M.N := by
    rw [MarkedIdeals.MarkedIdeal.geoStrictTransform_univ hπ]
    exact mem_univ z
  have hnot : π z ∉ GermIdealOrder.cosupport (m+1) M.N M.ideal (M.d+1) := by
    intro hzcos
    have hb := (le_order_iff (𝔞 := M.ideal) (fun _ hg => hg.1)).mpr hzcos.2
    rw [hCorder (π z) hz] at hb
    have : r+1 ≤ r := by exact_mod_cast hb
    omega
  obtain ⟨g,hg,hng⟩ := ExceptionalPushforwardAlong.exists_not_isInSpanOnAt_exceptionalDivisor
    hπ hwf.isClosedSubmanifold_N hcoh hCadm.2.1 hz hzN hnot
  refine ⟨g,?_,fun hgE => hng ?_⟩
  · rwa [MarkedIdeals.MarkedIdeal.geoTransform_ideal_eq_controlledTransform (𝔪 := M) rfl hcoh hπ] at hg
  · exact RelativePrincipalizationSpan.IsInSpanAt.restrict
      (InvertibleIdealQuotient.isInSpanAt_self
        (NonmonomialTransformTower.exceptionalDivisor_mem_of_vanishingIdeal_mem hπ
          (isSNCDivisor_of_boundaryAdapted h) hCadm.2.2 hz hgE) hgE.1)

/-- Whole original pullback has the actual highest count as its exact new exceptional power. -/
theorem pullback_original_highest_eq_power_mul_strict {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (hne : {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}.Nonempty)
    {π : D → A}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π) :
    GermIdeal.pullback (m := n) π (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) =
      (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal r).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n π H)) := by
  cases n with
  | zero =>
    obtain ⟨x,hx⟩ := hne
    change r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x at hx
    have hb := branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted h) x
    omega
  | succ m =>
    have hcoh := DivisorMetric.isCoherent_of_isInvertible
      (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted h))
    have hc := isAdmissibleCentre_highest_original_mark h hbound
    have hle := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hc.1 hc.2.1
    rw [← controlledTransform_original_highest_eq_strict h hr hbound hπ]
    exact BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hcoh hle

omit [IsComplexManifold n M] in
/-- Equality of actual invertible whole products cancels their actual invertible common factor. -/
theorem eq_of_invertible_mul_left_eq {I J L : GermIdeal n M}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hL : L.IsInvertible)
    (heq : L.mul I = L.mul J) : I = J := by
  have hle (I J : GermIdeal n M) (hI : I.IsInvertible) (hJ : J.IsInvertible)
      (heq : L.mul I = L.mul J) : I.Le J := by
    intro x f hf
    obtain ⟨U,hU,hxU,l,hl,hnl,hgenL⟩ := hL x
    obtain ⟨V,hV,hxV,j,hj,_,hgenJ⟩ := hJ x
    have hlh : HolomorphicAt n l x := holomorphicAt_of_mdifferentiableOn hU hl hxU
    have hjh : HolomorphicAt n j x := holomorphicAt_of_mdifferentiableOn hV hj hxV
    have hfh := RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem hI hf
    have hlmem : L.mem x l := (hgenL x hxU l).mpr (isInSpanAt_self rfl hlh)
    have hlfmem : (L.mul I).mem x (fun y => l y * f y) :=
      InvertibleIdealQuotient.mem_mul_iff.mpr (isInSpanAt_self ⟨l,f,hlmem,hf,rfl⟩ (hlh.mul hfh))
    rw [heq] at hlfmem
    have hgen := MemberPullback.mul_mem_iff_of_generators (hgenL x hxU) (hgenJ x hxV) hlh hjh
    obtain ⟨_,b,hb,hbeq⟩ := isInSpanAt_eq_iff.mp ((hgen _).mp hlfmem)
    have hcancel : f =ᶠ[𝓝 x] fun y => b y * j y := by
      apply eventuallyEq_of_mul_eventuallyEq hU hnl hxU hfh (hb.mul hjh)
      filter_upwards [hbeq] with y hy
      rw [hy]
      ring
    exact (hgenJ x hxV f).mpr (isInSpanAt_of_eq_mul rfl hfh hb hcancel)
  exact GermIdeal.ext (funext fun x => funext fun f => propext
    ⟨hle I J hI hJ heq x f,hle J I hJ hI heq.symm x f⟩)

/-- The SAME actual marking-one whole original transform retains exactly r-1 new exceptional powers. -/
theorem controlledTransform_original_mark_one_eq_power_mul_strict {H : Set A} {E : List (Set A)}
    (h : IsBoundaryAdaptedCarrier (n := n) H E) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x ≤ r)
    (hne : {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}.Nonempty)
    {π : D → A}
    (hπ : IsBlowupAlong n {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x} π) :
    BlowupControlledTransform.controlledTransform hπ
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) 1 =
      (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal (r-1)).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n π H)) := by
  let I := Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H
  let L := (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal
  let J := Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n π H)
  have hI : I.IsInvertible := isInvertible_vanishingIdeal_normalCrossingsCarrier
    (isNormalCrossingsCarrier_of_boundaryAdapted h)
  have hc := isAdmissibleCentre_highest_original_mark h hbound
  have hcoh := DivisorMetric.isCoherent_of_isInvertible hI
  have hle1 : I.Le (idealPow (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n)
      {x | r ≤ branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}) 1) :=
    HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hcoh hc.1
      (fun x hx => cosupport_anti (show 1 ≤ r by omega) (hc.2.1 hx))
  have hL : L.IsInvertible := (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
  have hLc := DivisorMetric.isCoherent_of_isInvertible hL
  have hJ : J.IsInvertible := by
    have hnext := isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_strict_highest h hbound hπ)
    rw [geoStrictTransform_highest_eq_strictTransform (isNormalCrossingsCarrier_of_boundaryAdapted h) hr hbound hπ] at hnext
    exact isInvertible_vanishingIdeal_normalCrossingsCarrier hnext
  have hJc := DivisorMetric.isCoherent_of_isInvertible hJ
  have hLpc := GermIdealPullbackCalculus.isCoherent_idealPow hLc (r-1)
  have hleft := BlowupControlledTransform.pullback_eq_mul_controlledTransform hπ hcoh hle1
  rw [FactorizationFromResolution.idealPow_one_of_isCoherent hLc] at hleft
  have hpow : idealPow L r = L.mul (idealPow L (r-1)) := by
    calc
      idealPow L r = idealPow L (1+(r-1)) := congrArg (idealPow L) (by omega)
      _ = L.mul (idealPow L (r-1)) := by
        rw [RestrictLeCalculus.idealPow_add hLc,
          FactorizationFromResolution.idealPow_one_of_isCoherent hLc]
  apply eq_of_invertible_mul_left_eq (isInvertible_controlledTransform hπ hI 1 hle1)
    (GermIdealTotalTransform.isInvertible_mul (BlowupExceptionalDivisor.isInvertible_idealPow hL (r-1)) hJ) hL
  calc
    L.mul (BlowupControlledTransform.controlledTransform hπ I 1) = GermIdeal.pullback (m := n) π I := hleft.symm
    _ = (idealPow L r).mul J := pullback_original_highest_eq_power_mul_strict h hr hbound hne hπ
    _ = L.mul ((idealPow L (r-1)).mul J) := by
      rw [hpow,GermIdealTotalTransform.mul_assoc hLc hLpc hJc]

open HironakaNormalCrossingsBoundarySeparation HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsMarkedAdmissibility
  HironakaStageCenters MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaDivisorResidual HironakaNormalCrossingsBoundaryTransform

/-- The actual pair supplied by a genuine higher separating centre. -/
theorem higherCentrePair {A : CMfd.{u} n} {H : Set A} {E : List (Set A)} {C : Set A}
    (hc : IsHigherSeparationCentre (n := n) H E C) : IsBoundaryAdaptedCarrier (n := n) H E :=
  Classical.choose hc

/-- The actual attained highest original count, internally extracted from the genuine centre. -/
def higherCentreMultiplicity {A : CMfd.{u} n} {H : Set A} {E : List (Set A)} {C : Set A}
    (hc : IsHigherSeparationCentre (n := n) H E C) : ℕ :=
  Classical.choose (Classical.choose_spec hc)

theorem higherCentreMultiplicity_spec {A : CMfd.{u} n} {H : Set A} {E : List (Set A)} {C : Set A}
    (hc : IsHigherSeparationCentre (n := n) H E C) :
    2 ≤ higherCentreMultiplicity hc ∧
    (∀ x : A, branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (higherCentrePair hc)) x ≤
      higherCentreMultiplicity hc) ∧
    C = {x | higherCentreMultiplicity hc ≤
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (higherCentrePair hc)) x} ∧
    C.Nonempty := Classical.choose_spec (Classical.choose_spec hc)

theorem higherCentreMultiplicity_le {A : CMfd.{u} n} {H : Set A} {E : List (Set A)} {C : Set A}
    (hc : IsHigherSeparationCentre (n := n) H E C) : higherCentreMultiplicity hc ≤ n := by
  obtain ⟨_,_,heq,hne⟩ := higherCentreMultiplicity_spec hc
  obtain ⟨x,hx⟩ := hne
  rw [heq] at hx
  exact hx.trans (branchMultiplicity_le (isNormalCrossingsCarrier_of_boundaryAdapted (higherCentrePair hc)) x)

/-- Literal actual new exceptional members, retaining each historical original exponent.
The offset 0 records the whole total ideal and offset 1 its actual controlled ideal. -/
def recordedOriginalWeights {A : CMfd.{u} n} (H : Set A) (δ : ℕ) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T →
      List (Set D × ℕ)
  | _, .refl, _ => []
  | _, .step T C π _, hc =>
      (recordedOriginalWeights H δ T hc.1).map (fun p => (geoStrictTransform π C p.1,p.2)) ++
        [(π ⁻¹' C,higherCentreMultiplicity hc.2 - δ)]

theorem recordedOriginalWeights_carriers {A : CMfd.{u} n} (H : Set A) (δ : ℕ) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D)
      (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T),
      (recordedOriginalWeights H δ T hc).map Prod.fst = (geoTransformAlong (originalMarkedIdeal H) T).E
  | _, .refl, _ => rfl
  | _, .step T C π hπ, hc => by
    simp only [recordedOriginalWeights,List.map_append,List.map_singleton,List.map_map,
      geoTransformAlong_step,geoTransform_E]
    rw [← recordedOriginalWeights_carriers H δ T hc.1,List.map_map]
    rfl

theorem recordedOriginalWeights_bounds {A : CMfd.{u} n} (H : Set A) (δ : ℕ) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D)
      (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T),
      ∀ p ∈ recordedOriginalWeights H δ T hc, 2-δ ≤ p.2 ∧ p.2 ≤ n-δ
  | _, .refl, _, p, hp => by simp [recordedOriginalWeights] at hp
  | _, .step T C π hπ, hc, p, hp => by
    simp only [recordedOriginalWeights,List.mem_append,List.mem_map,List.mem_singleton] at hp
    rcases hp with ⟨q,hq,rfl⟩ | rfl
    · exact recordedOriginalWeights_bounds H δ T hc.1 q hq
    · have hmin := (higherCentreMultiplicity_spec hc.2).1
      have hmax := higherCentreMultiplicity_le hc.2
      exact ⟨Nat.sub_le_sub_right hmin δ,Nat.sub_le_sub_right hmax δ⟩

theorem higherSeparationCentres_pair {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D),
      StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T →
      IsBoundaryAdaptedCarrier (n := n) (strictTransform n T.proj H)
        (geoTransformAlong (originalMarkedIdeal H) T).E
  | _, .refl, _ => by
    simpa only [BlowupTower.proj_refl,geoTransformAlong_refl,originalMarkedIdeal,
      strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,hH.1.closure_eq] using boundaryAdapted_nil hH
  | _, .step T C π hπ, hc => by
    obtain ⟨hr,hbound,hceq,hne⟩ := higherCentreMultiplicity_spec hc.2
    have hp := boundaryAdapted_strict_highest (higherCentrePair hc.2) hbound (hceq ▸ hπ)
    have hgeo := geoStrictTransform_highest_eq_strictTransform
      (isNormalCrossingsCarrier_of_boundaryAdapted (higherCentrePair hc.2)) hr hbound (hceq ▸ hπ)
    rw [hgeo,← hceq] at hp
    simpa only [geoTransformAlong_step,geoTransform_E,BlowupTower.proj_step,
      StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff] using hp

private theorem pullback_recorded_member {A D : CMfd.{u} n} {H : Set A} {E : List (Set A)} {C : Set A}
    (hc : IsHigherSeparationCentre (n := n) H E C) {π : D → A}
    (hπ : IsBlowupAlong n C π) {W : Set A} (hW : W ∈ E) :
    GermIdeal.pullback (m := n) π (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) W) =
      Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (geoStrictTransform π C W) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hW
  obtain ⟨_,hbound,hceq,_⟩ := higherCentreMultiplicity_spec hc
  have hp := pullback_old_member_eq_vanishingIdeal_strict (higherCentrePair hc) hbound (hceq ▸ hπ) i
  rwa [← hceq] at hp

/-- The WHOLE actual exceptional ideal is the COMPLETE vanishing ideal of its actual carrier. -/
theorem exceptionalIdeal_eq_vanishingIdeal {A D : CMfd.{u} n} {C : Set A} {π : D → A}
    (hπ : IsBlowupAlong n C π) :
    (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal =
      Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (π ⁻¹' C) := by
  refine GermIdeal.ext (funext fun z => funext fun g => propext ?_)
  by_cases hz : π z ∈ C
  · exact MemberTraceIdealAlong.exceptionalDivisor_mem_iff_vanishingIdeal hπ hz g
  · exact BlowupStrictIdeal.mem_pullback_vanishingIdeal_iff_of_notMem hπ C hz g

theorem recordedOriginalWeights_member_invertible {A : CMfd.{u} n} (H : Set A) (δ : ℕ) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D)
      (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T),
      ∀ p ∈ recordedOriginalWeights H δ T hc,
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible
  | _, .refl, _, p, hp => by simp [recordedOriginalWeights] at hp
  | _, .step T C π hπ, hc, p, hp => by
    simp only [recordedOriginalWeights,List.mem_append,List.mem_map,List.mem_singleton] at hp
    rcases hp with ⟨q,hq,rfl⟩ | rfl
    · have hqE : q.1 ∈ (geoTransformAlong (originalMarkedIdeal H) T).E := by
        rw [← recordedOriginalWeights_carriers H δ T hc.1]
        exact List.mem_map.mpr ⟨q,hq,rfl⟩
      rw [← pullback_recorded_member hc.2 hπ hqE]
      exact GermIdealTotalTransform.isInvertible_pullback hπ.contMDiff
        (BlowupExceptionalDivisor.interior_exceptionalLocus_eq_empty hπ)
        (recordedOriginalWeights_member_invertible H δ T hc.1 q hq)
    · rw [← exceptionalIdeal_eq_vanishingIdeal hπ]
      exact (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible

private theorem invertible_component_product {A : Type u} [TopologicalSpace A]
    [ChartedSpace (ComplexModel n) A] [IsComplexManifold n A] (F : List (Set A × ℕ))
    (hF : ∀ p ∈ F, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible) :
    (componentPowerProduct (n := n) F).IsInvertible := by
  induction F with
  | nil => exact BlowupExceptionalDivisor.isInvertible_unitIdeal
  | cons p F ih =>
    exact GermIdealTotalTransform.isInvertible_mul
      (BlowupExceptionalDivisor.isInvertible_idealPow (hF p (by simp)) p.2)
      (ih fun q hq => hF q (List.mem_cons_of_mem p hq))

private theorem component_product_append_one {A : CMfd.{u} n} (F : List (Set A × ℕ))
    (hF : ∀ p ∈ F, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible)
    (W : Set A) (a : ℕ) (hW : (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) W).IsInvertible) :
    componentPowerProduct (n := n) (F ++ [(W,a)]) =
      (componentPowerProduct (n := n) F).mul
        (idealPow (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) W) a) := by
  have hWc := DivisorMetric.isCoherent_of_isInvertible (BlowupExceptionalDivisor.isInvertible_idealPow hW a)
  induction F with
  | nil => simp only [List.nil_append,componentPowerProduct]
           rw [RestrictLeCalculus.mul_unitIdeal hWc,BlowupControlledTransform.unitIdeal_mul hWc]
  | cons p F ih =>
    have htail := fun q hq => hF q (List.mem_cons_of_mem p hq)
    simp only [List.cons_append,componentPowerProduct]
    rw [ih htail, GermIdealTotalTransform.mul_assoc
      (DivisorMetric.isCoherent_of_isInvertible (BlowupExceptionalDivisor.isInvertible_idealPow (hF p (by simp)) p.2))
      (DivisorMetric.isCoherent_of_isInvertible (invertible_component_product F htail)) hWc]

private theorem pullback_component_product {A D : CMfd.{u} n} {H : Set A} {E : List (Set A)} {C : Set A}
    (hc : IsHigherSeparationCentre (n := n) H E C) {π : D → A} (hπ : IsBlowupAlong n C π)
    (F : List (Set A × ℕ))
    (hF : ∀ p ∈ F, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible)
    (hFE : ∀ p ∈ F, p.1 ∈ E) :
    GermIdeal.pullback (m := n) π (componentPowerProduct (n := n) F) =
      componentPowerProduct (n := n) (F.map (fun p => (geoStrictTransform π C p.1,p.2))) := by
  induction F with
  | nil => exact BlowupExceptionalDivisor.pullback_unitIdeal
  | cons p F ih =>
    have hp := hF p (by simp)
    have hpc := DivisorMetric.isCoherent_of_isInvertible hp
    have htail := fun q hq => hF q (List.mem_cons_of_mem p hq)
    simp only [componentPowerProduct,List.map_cons]
    rw [GermIdealTotalTransform.pullback_mul hπ.contMDiff
      (GermIdealPullbackCalculus.isCoherent_idealPow hpc p.2)
      (DivisorMetric.isCoherent_of_isInvertible (invertible_component_product F htail)),
      BlowupExceptionalDivisor.pullback_idealPow hπ.contMDiff hpc,
      pullback_recorded_member hc hπ (hFE p (by simp)),
      ih htail (fun q hq => hFE q (List.mem_cons_of_mem p hq))]


theorem recordedOriginalWeights_mapped_member_invertible {A B D : CMfd.{u} n} (H : Set A) (δ : ℕ)
    (T : BlowupTower A B) (C : Set B) (π : D → B) (hπ : IsBlowupAlong n C π)
    (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) (.step T C π hπ)) :
    ∀ p ∈ (recordedOriginalWeights H δ T hc.1).map (fun p => (geoStrictTransform π C p.1,p.2)),
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible := by
  intro p hp
  exact recordedOriginalWeights_member_invertible H δ (.step T C π hπ) hc p
    (List.mem_append_left _ hp)

/-- The actual WHOLE original pullback has its internally recorded historical total exponents. -/
theorem higherSeparationCentres_total_dictionary {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D)
      (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T),
      GermIdeal.pullback (m := n) T.proj (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) =
        (componentPowerProduct (n := n) (recordedOriginalWeights H 0 T hc)).mul
          (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H))
  | _, .refl, _ => by
    have hIc := DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_normalCrossingsCarrier hH)
    simp only [BlowupTower.proj_refl,recordedOriginalWeights,componentPowerProduct,
      strictTransform,exceptionalLocus_id,sdiff_empty,preimage_id,hH.1.closure_eq]
    rw [BlowupControlledTransform.pullback_id hIc,BlowupControlledTransform.unitIdeal_mul hIc]
  | _, .step T C π hπ, hc => by
    let F := recordedOriginalWeights H 0 T hc.1
    let Q := F.map (fun p => (geoStrictTransform π C p.1,p.2))
    have hF := recordedOriginalWeights_member_invertible H 0 T hc.1
    have hQ := recordedOriginalWeights_mapped_member_invertible H 0 T C π hπ hc
    have hFc := DivisorMetric.isCoherent_of_isInvertible (invertible_component_product F hF)
    have hQc := DivisorMetric.isCoherent_of_isInvertible (invertible_component_product Q hQ)
    have hFE : ∀ p ∈ F, p.1 ∈ (geoTransformAlong (originalMarkedIdeal H) T).E := by
      intro p hp
      rw [← recordedOriginalWeights_carriers H 0 T hc.1]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    have hpair := higherSeparationCentres_pair hH T hc.1
    have hJc := DivisorMetric.isCoherent_of_isInvertible
      (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted hpair))
    have hI0c := DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_normalCrossingsCarrier hH)
    obtain ⟨hr,hbound,hceq,hne⟩ := higherCentreMultiplicity_spec hc.2
    have hne' : {x | higherCentreMultiplicity hc.2 ≤
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (higherCentrePair hc.2)) x}.Nonempty := hceq ▸ hne
    have hp := pullback_original_highest_eq_power_mul_strict (higherCentrePair hc.2) hr hbound hne' (hceq ▸ hπ)
    simp only [BlowupExceptionalDivisor.exceptionalDivisor_ideal,← hceq] at hp
    rw [BlowupTower.proj_step,GermIdealTotalTransform.pullback_comp T.contMDiff_proj hπ.contMDiff hI0c,
      higherSeparationCentres_total_dictionary hH T hc.1,
      GermIdealTotalTransform.pullback_mul hπ.contMDiff hFc hJc,
      pullback_component_product hc.2 hπ F hF hFE,hp]
    have hL := (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
    have hLvan := hL
    rw [exceptionalIdeal_eq_vanishingIdeal hπ] at hLvan
    simp only [recordedOriginalWeights,Nat.sub_zero]
    rw [component_product_append_one Q hQ (π ⁻¹' C) (higherCentreMultiplicity hc.2) hLvan,
      ← exceptionalIdeal_eq_vanishingIdeal hπ]
    have hnext := higherSeparationCentres_pair hH (.step T C π hπ) hc
    rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff] at hnext
    rw [StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
    exact (GermIdealTotalTransform.mul_assoc hQc
      (GermIdealPullbackCalculus.isCoherent_idealPow (DivisorMetric.isCoherent_of_isInvertible hL) _)
      (DivisorMetric.isCoherent_of_isInvertible
        (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted hnext)))).symm

/-- The SAME actual original marking-one transform has its internally recorded r-1 weights. -/
theorem higherSeparationCentres_controlled_dictionary {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D)
      (hc : StageCentres (fun R C => IsHigherSeparationCentre (n := n)
        (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C) T),
      (geoTransformAlong (originalMarkedIdeal H) T).ideal =
        (componentPowerProduct (n := n) (recordedOriginalWeights H 1 T hc)).mul
          (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H))
  | _, .refl, _ => by
    have hIc := DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_normalCrossingsCarrier hH)
    simp only [geoTransformAlong_refl,originalMarkedIdeal,BlowupTower.proj_refl,
      recordedOriginalWeights,componentPowerProduct,strictTransform,exceptionalLocus_id,
      sdiff_empty,preimage_id,hH.1.closure_eq]
    exact (BlowupControlledTransform.unitIdeal_mul hIc).symm
  | _, .step T C π hπ, hc => by
    let F := recordedOriginalWeights H 1 T hc.1
    let Q := F.map (fun p => (geoStrictTransform π C p.1,p.2))
    have hF := recordedOriginalWeights_member_invertible H 1 T hc.1
    have hQ := recordedOriginalWeights_mapped_member_invertible H 1 T C π hπ hc
    have hFc := DivisorMetric.isCoherent_of_isInvertible (invertible_component_product F hF)
    have hQc := DivisorMetric.isCoherent_of_isInvertible (invertible_component_product Q hQ)
    have hFE : ∀ p ∈ F, p.1 ∈ (geoTransformAlong (originalMarkedIdeal H) T).E := by
      intro p hp
      rw [← recordedOriginalWeights_carriers H 1 T hc.1]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    have hpair := higherSeparationCentres_pair hH T hc.1
    have hJc := DivisorMetric.isCoherent_of_isInvertible
      (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted hpair))
    have hI0c := DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_normalCrossingsCarrier hH)
    obtain ⟨hr,hbound,hceq,hne⟩ := higherCentreMultiplicity_spec hc.2
    have hne' : {x | higherCentreMultiplicity hc.2 ≤
      branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (higherCentrePair hc.2)) x}.Nonempty := hceq ▸ hne
    have hp := controlledTransform_original_mark_one_eq_power_mul_strict
      (higherCentrePair hc.2) hr hbound hne' (hceq ▸ hπ)
    simp only [BlowupControlledTransform.controlledTransform,
      BlowupExceptionalDivisor.exceptionalDivisor_ideal,← hceq] at hp
    have hle0 : (componentPowerProduct (n := n) F).Le
        (idealPow (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) C) 0) :=
      fun x g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hFc hg
    have hCad := isAdmissibleCentre_highest_original_mark (higherCentrePair hc.2) hbound
    have hsub1 : C ⊆ GermIdealOrder.cosupport n univ
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H)) 1 := by
      rw [hceq]
      intro x hx
      exact cosupport_anti (show 1 ≤ higherCentreMultiplicity hc.2 by omega) (hCad.2.1 hx)
    have hle1 := HadamardBridge.le_idealPow_vanishingIdeal_of_subset_cosupport hJc hπ.1 hsub1
    have hmul := MarkedIdealOperationsTransform.controlledTransform_mul hπ hFc hJc hle0 hle1
    have htest := (higherSeparationCentres_isGeoTestTower_and_strict_subset_cosupp hH (.step T C π hπ) hc).1
    have hNT := (pullback_eq_mul_geoTransformAlong (originalMarkedIdeal H) rfl hI0c T htest.1).1
    have hcurcoh := (pullback_eq_mul_geoTransformAlong (originalMarkedIdeal H) rfl hI0c T htest.1).2.1
    rw [geoTransformAlong_step,geoTransform_ideal_eq_controlledTransform hNT hcurcoh hπ,d_geoTransformAlong]
    change BlowupControlledTransform.controlledTransform hπ (geoTransformAlong (originalMarkedIdeal H) T).ideal 1 = _
    rw [higherSeparationCentres_controlled_dictionary hH T hc.1]
    rw [show (1 : ℕ) = 0+1 by rfl,hmul,BlowupControlledTransform.controlledTransform_zero hπ hFc,
      pullback_component_product hc.2 hπ F hF hFE]
    change (componentPowerProduct (n := n) Q).mul
      (BlowupControlledTransform.controlledTransform hπ
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H)) 1) = _
    change BlowupControlledTransform.controlledTransform hπ
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H)) 1 =
      (idealPow (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal (higherCentreMultiplicity hc.2-1)).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n π (strictTransform n T.proj H))) at hp
    rw [hp]
    have hL := (BlowupExceptionalDivisor.exceptionalDivisor hπ).isInvertible
    have hLvan := hL
    rw [exceptionalIdeal_eq_vanishingIdeal hπ] at hLvan
    simp only [recordedOriginalWeights]
    rw [component_product_append_one Q hQ (π ⁻¹' C) (higherCentreMultiplicity hc.2-1) hLvan,
      ← exceptionalIdeal_eq_vanishingIdeal hπ]
    have hnext := higherSeparationCentres_pair hH (.step T C π hπ) hc
    rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff] at hnext
    rw [BlowupTower.proj_step,StrictTransformComposition.strictTransform_comp T.contMDiff_proj hπ.contMDiff]
    exact (GermIdealTotalTransform.mul_assoc hQc
      (GermIdealPullbackCalculus.isCoherent_idealPow (DivisorMetric.isCoherent_of_isInvertible hL) _)
      (DivisorMetric.isCoherent_of_isInvertible
        (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted hnext)))).symm

open HironakaSNCComponentCoefficients

/-- The whole literal indexed product, including absent or repeated empty members. -/
theorem indexed_component_product_generator {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (F : List (Set M × ℕ)) (f : Fin F.length → M → ℂ) (x : M)
    (hf : ∀ i, HolomorphicAt n (f i) x)
    (hgen : ∀ i g, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (F.get i).1).mem x g ↔
      IsInSpanAt (n := n) (· = f i) x g) (g : M → ℂ) :
    (componentPowerProduct (n := n) F).mem x g ↔
      IsInSpanAt (n := n) (· = fun z => ∏ i : Fin F.length, f i z ^ (F.get i).2) x g := by
  induction F generalizing g with
  | nil =>
    simpa only [componentPowerProduct,unitIdeal,List.length_nil,Finset.univ_eq_empty,Finset.prod_empty]
      using (MemberPullback.isInSpanAt_one_iff g).symm
  | cons p F ih =>
    have hf0 : HolomorphicAt n (f 0) x := hf 0
    have hgen0 : ∀ a, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).mem x a ↔
        IsInSpanAt (n := n) (· = f 0) x a := hgen 0
    have ht : HolomorphicAt n (fun z => ∏ i : Fin F.length, f i.succ z ^ (F.get i).2) x :=
      MonomialPart.holomorphicAt_finset_prod _ (fun i _ =>
        CompanionReduction.holomorphicAt_pow_of (hf i.succ) (F.get i).2)
    have hgent : ∀ a, (componentPowerProduct (n := n) F).mem x a ↔
        IsInSpanAt (n := n) (· = fun z => ∏ i : Fin F.length, f i.succ z ^ (F.get i).2) x a :=
      ih (fun i => f i.succ) (fun i => hf i.succ) (fun i => hgen i.succ)
    have hm := MemberPullback.mul_mem_iff_of_generators
      (idealPow_mem_iff_of_generator hf0 hgen0 p.2) hgent
      (CompanionReduction.holomorphicAt_pow_of hf0 p.2) ht g
    simpa only [componentPowerProduct,List.length_cons,Fin.prod_univ_succ,List.get_eq_getElem,
      Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,List.getElem_cons_succ] using hm

open Classical in
/-- Actual joint pair charts produce the WHOLE weighted ideal generator on EVERY nearby stalk,
with literal finite indices and genuine unit factors for absent or empty members. -/
theorem exists_joint_whole_weighted_generator {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (hn : 0 < n)
    {H : Set M} (F : List (Set M × ℕ))
    (h : IsBoundaryAdaptedCarrier (n := n) H (F.map Prod.fst)) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)) (σ : Fin F.length → Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) ∧
      Set.InjOn σ {i | x ∈ (F.get i).1} ∧
      (∀ i, x ∈ (F.get i).1 → σ i ∉ S) ∧
      (∀ i, x ∈ (F.get i).1 → ∀ y ∈ flatDomain Φ,
        y ∈ (F.get i).1 ↔ flatCoord Φ (σ i) y = 0) ∧
      ∀ᶠ y in 𝓝 x, ∀ g,
        ((componentPowerProduct (n := n) F).mul
          (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)).mem y g ↔
        IsInSpanAt (n := n)
          (· = fun z => (∏ i ∈ S, flatCoord Φ i z) *
            ∏ i ∈ Finset.univ.filter (fun i => x ∈ (F.get i).1),
              flatCoord Φ (σ i) z ^ (F.get i).2) y g := by
  classical
  obtain ⟨Φ,S,B,hsrc,h0,hH,hB,hinj,hE⟩ := h.2.2 x
  let c : Fin F.length ≃ Fin (F.map Prod.fst).length := finCongr (by simp)
  have hget (i : Fin F.length) : (F.map Prod.fst).get (c i) = (F.get i).1 := by
    simp only [List.get_eq_getElem,List.getElem_map,c,finCongr_apply,Fin.val_cast]
  have hcard (i : Fin F.length) (hi : x ∈ (F.get i).1) : (B (c i)).card = 1 :=
    (hB (c i) (hget i ▸ hi)).1
  let σ : Fin F.length → Fin n := fun i => if hi : x ∈ (F.get i).1 then
    Classical.choose (Finset.card_eq_one.mp (hcard i hi)) else ⟨0,hn⟩
  have hsingle (i : Fin F.length) (hi : x ∈ (F.get i).1) : B (c i) = {σ i} := by
    dsimp only [σ]
    rw [dif_pos hi]
    exact Classical.choose_spec (Finset.card_eq_one.mp (hcard i hi))
  have hσinj : Set.InjOn σ {i | x ∈ (F.get i).1} := by
    intro i hi j hj heq
    apply c.injective
    apply hinj (show x ∈ (F.map Prod.fst).get (c i) from (hget i).symm ▸ hi)
      (show x ∈ (F.map Prod.fst).get (c j) from (hget j).symm ▸ hj)
    rw [hsingle i hi,hsingle j hj,heq]
  have hσS : ∀ i, x ∈ (F.get i).1 → σ i ∉ S := by
    intro i hi
    have hd := (hB (c i) (hget i ▸ hi)).2
    rw [hsingle i hi] at hd
    exact Finset.disjoint_singleton_right.mp hd
  have hflat : ∀ i, x ∈ (F.get i).1 → ∀ y ∈ flatDomain Φ,
      y ∈ (F.get i).1 ↔ flatCoord Φ (σ i) y = 0 := by
    intro i hi y hy
    have hh := hE (c i) (hget i ▸ hi) y hy
    rw [hget i,hsingle i hi,BlowupSNCTransform.mem_coordSubspace_singleton] at hh
    exact hh
  let f : Fin F.length → M → ℂ := fun i =>
    if x ∈ (F.get i).1 then flatCoord Φ (σ i) else fun _ => 1
  have havoid : ∀ᶠ y in 𝓝 x, ∀ i : Fin F.length, x ∉ (F.get i).1 → y ∉ (F.get i).1 := by
    apply eventually_all.mpr
    intro i
    by_cases hi : x ∈ (F.get i).1
    · exact Eventually.of_forall fun _ hh => (hh hi).elim
    · have hc := h.2.1 _ (List.mem_map.mpr ⟨F.get i,List.get_mem _ _,rfl⟩)
      have hev : ∀ᶠ y in 𝓝 x, y ∉ (F.get i).1 := hc.isOpen_compl.mem_nhds hi
      exact hev.mono fun y hy _ => hy
  have hprod : (fun z => ∏ i : Fin F.length, f i z ^ (F.get i).2) =
      fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ (F.get i).1),
        flatCoord Φ (σ i) z ^ (F.get i).2 := by
    funext z
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : x ∈ (F.get i).1 <;> simp only [f,hi,if_true,if_false,one_pow]
  refine ⟨Φ,S,σ,hsrc,h0,hH,hσinj,hσS,hflat,?_⟩
  filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ),havoid,
    vanishingIdeal_mem_iff_original_flat_product x Φ h0 S hH] with y hyD hyavoid hgenH g
  have hf : ∀ i, HolomorphicAt n (f i) y := by
    intro i
    by_cases hi : x ∈ (F.get i).1
    · simpa only [f,if_pos hi] using holomorphicAt_flatCoord Φ (σ i) hyD
    · simpa only [f,if_neg hi] using holomorphicAt_const (n := n) (x := y) (1 : ℂ)
  have hgen : ∀ i a, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (F.get i).1).mem y a ↔
      IsInSpanAt (n := n) (· = f i) y a := by
    intro i a
    by_cases hi : x ∈ (F.get i).1
    · simp only [f,if_pos hi]
      exact MemberPullback.vanishingIdeal_mem_iff_flatCoord Φ
        (fun hy1 hy2 => hflat i hi _ ⟨hy1,hy2⟩) hyD a
    · simp only [f,if_neg hi,MemberPullback.isInSpanAt_one_iff]
      constructor
      · exact fun ha => ha.1
      · intro ha
        have hc := h.2.1 _ (List.mem_map.mpr ⟨F.get i,List.get_mem _ _,rfl⟩)
        refine ⟨ha,?_⟩
        filter_upwards [hc.isOpen_compl.mem_nhds (hyavoid i hi)] with z hz hzW
        exact (hz hzW).elim
  have hfprod : HolomorphicAt n (fun z => ∏ i : Fin F.length, f i z ^ (F.get i).2) y :=
    MonomialPart.holomorphicAt_finset_prod _ (fun i _ =>
      CompanionReduction.holomorphicAt_pow_of (hf i) (F.get i).2)
  have hHprod := MonomialPart.holomorphicAt_finset_prod S (fun i _ => holomorphicAt_flatCoord Φ i hyD)
  have hwhole := MemberPullback.mul_mem_iff_of_generators
    (indexed_component_product_generator F f y hf hgen) hgenH hfprod hHprod g
  simpa only [congrFun hprod,mul_comm] using hwhole

open MonomialPart MonomialCase DivisorExponent IdealOrderArithmetic

private theorem exponent_of_actual_coordinate_product {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {ι : Type*} [DecidableEq ι] {x : M}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (T : Finset ι) (σ : ι → Fin n) (a : ι → ℕ) (hinj : Set.InjOn σ T)
    (I : GermIdeal n M) (hI : I.IsInvertible)
    (hgen : ∀ᶠ y in 𝓝 x, ∀ g, I.mem y g ↔
      IsInSpanAt (n := n) (· = fun z => ∏ i ∈ T, flatCoord Φ (σ i) z ^ a i) y g)
    (i : ι) (hi : i ∈ T) (W : Set M) (hxW : x ∈ W)
    (hflatW : ∀ y ∈ flatDomain Φ, y ∈ W ↔ flatCoord Φ (σ i) y = 0) :
    divExp n I W x = a i := by
  have hhol : ∀ y g, I.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem hI hg
  have hxD := mem_flatDomain_self Φ
  have hmonhol (y : M) (hy : y ∈ flatDomain Φ) :
      HolomorphicAt n (fun z => ∏ j ∈ T, flatCoord Φ (σ j) z ^ a j) y :=
    holomorphicAt_finset_prod T (fun j _ => CompanionReduction.holomorphicAt_pow_of
      (holomorphicAt_flatCoord Φ (σ j) hy) (a j))
  have hu : (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) W).mem x (flatCoord Φ (σ i)) := by
    refine ⟨holomorphicAt_flatCoord Φ (σ i) hxD,?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with z hz hzW
    exact (hflatW z hz).mp hzW
  have hpow := OrderMultiplicativity.pow_mem_idealPow hu (holomorphicAt_flatCoord Φ (σ i) hxD) (a i)
  have hresth := holomorphicAt_finset_prod (T.erase i) (fun j _ =>
    CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hxD) (a j))
  have hm : (idealPow (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) W) (a i)).mem x
      (fun z => ∏ j ∈ T, flatCoord Φ (σ j) z ^ a j) := by
    refine mem_idealPow_congr (mul_mem_idealPow hresth hpow) (Eventually.of_forall fun z => ?_)
    change (∏ j ∈ T.erase i, flatCoord Φ (σ j) z ^ a j) * flatCoord Φ (σ i) z ^ a i = _
    rw [mul_comm,Finset.mul_prod_erase T (fun j => flatCoord Φ (σ j) z ^ a j) hi]
  have hdiv : IsDivNear n I W (a i) x := by
    filter_upwards [hgen,eventually_mem_idealPow_vanishingIdeal hm] with z hz hzm hzW
    refine ⟨mem_univ z,fun g hg => IsInSpanAt.vanishesToOrderOn ((hz g).mp hg) ?_⟩
    rintro _ rfl
    exact GermOrderProduct.vanishesToOrderOn_of_mem (mem_idealPow_pointIdeal_of_mem_idealPow_vanishingIdeal hzW hzm)
  have hndiv : ¬ IsDivNear n I W (a i+1) x := by
    intro hd
    have hfreq := frequently_flatMap_ne_zero hsrc hxD ((T.erase i).image σ)
    obtain ⟨z,⟨hzD,hzne,hzeq⟩,hzd,hzgen⟩ := (hfreq.and_eventually (hd.and hgen)).exists
    have hσi : σ i ∉ (T.erase i).image σ := by
      intro hh
      obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hh
      exact (Finset.mem_erase.mp hj).1 (hinj (Finset.mem_erase.mp hj).2 hi hji)
    have hu0 : flatCoord Φ (σ i) z = 0 := by
      change GiraudAlong.flatMap Φ z (σ i) = 0
      rw [hzeq _ hσi]
      exact (hflatW x hxD).mp hxW
    have hzW : z ∈ W := (hflatW z hzD).mpr hu0
    have hmz : I.mem z (fun w => ∏ j ∈ T, flatCoord Φ (σ j) w ^ a j) :=
      (hzgen _).mpr (isInSpanAt_self rfl (hmonhol z hzD))
    have hord := mem_idealPow_of_vanishesToOrderOn_univ ((hzd hzW).2 _ hmz)
    have huh := holomorphicAt_flatCoord Φ (σ i) hzD
    have hrest := holomorphicAt_finset_prod (T.erase i) (fun j _ =>
      CompanionReduction.holomorphicAt_pow_of (holomorphicAt_flatCoord Φ (σ j) hzD) (a j))
    have hrest0 : ¬ (idealPow (pointIdeal n z) (0+1)).mem z
        (fun w => ∏ j ∈ T.erase i, flatCoord Φ (σ j) w ^ a j) := by
      intro hh
      have hz := apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl hh
      exact Finset.prod_ne_zero_iff.mpr
        (fun j hj => pow_ne_zero _ (hzne (σ j) (Finset.mem_image_of_mem σ hj))) hz
    have hpow0 : ¬ (idealPow (pointIdeal n z) (a i+1)).mem z
        (fun w => flatCoord Φ (σ i) w ^ a i) := by
      have hh := CompanionReduction.pow_notMem_idealPow huh (flatCoord_notMem_idealPow_two Φ (σ i) hzD) (a i)
      simpa using hh
    have hprod := GermOrderProduct.mul_notMem_idealPow hrest
      (CompanionReduction.holomorphicAt_pow_of huh (a i)) hrest0 hpow0
    apply hprod
    refine mem_idealPow_congr (by simpa using hord) (Eventually.of_forall fun w => ?_)
    change ∏ j ∈ T, flatCoord Φ (σ j) w ^ a j =
      (∏ j ∈ T.erase i, flatCoord Φ (σ j) w ^ a j) * flatCoord Φ (σ i) w ^ a i
    rw [mul_comm,Finset.mul_prod_erase T (fun j => flatCoord Φ (σ j) w ^ a j) hi]
  have h1 := (isDivNear_iff_le_divExp hhol hxW (HironakaDivisorPowers.isNonzeroAt_of_isInvertible hI x)).mp hdiv
  have h2 : ¬ a i+1 ≤ divExp n I W x := fun hh =>
    hndiv ((isDivNear_iff_le_divExp hhol hxW (HironakaDivisorPowers.isNonzeroAt_of_isInvertible hI x)).mpr hh)
  omega

open Classical in
/-- The SAME actual joint weighted WHOLE ideal has exact local order and exact original intrinsic exponents. -/
theorem exists_joint_whole_weighted_exponents {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (hn : 0 < n)
    {H : Set M} (F : List (Set M × ℕ))
    (h : IsBoundaryAdaptedCarrier (n := n) H (F.map Prod.fst))
    (hF : ∀ p ∈ F, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ H ↔ ∃ i ∈ S, flatCoord Φ i y = 0) ∧
      GermIdealOrder.order n univ ((componentPowerProduct (n := n) F).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)) x =
        ((S.card + ∑ i ∈ Finset.univ.filter (fun i => x ∈ (F.get i).1), (F.get i).2 : ℕ) : ℕ∞) ∧
      (∀ i : Fin F.length, x ∈ (F.get i).1 →
        divExp n ((componentPowerProduct (n := n) F).mul
          (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)) (F.get i).1 x = (F.get i).2) ∧
      ∀ j ∈ S, divExp n ((componentPowerProduct (n := n) F).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H))
        {z | z ∈ flatDomain Φ ∧ flatCoord Φ j z = 0} x = 1 := by
  classical
  obtain ⟨Φ,S,σ,hsrc,h0,hH,hσinj,hσS,hflat,hgen⟩ := exists_joint_whole_weighted_generator hn F h x
  let T := Finset.univ.filter (fun i => x ∈ (F.get i).1)
  let A := S.disjSum T
  let τ : Fin n ⊕ Fin F.length → Fin n := Sum.elim id σ
  let a : Fin n ⊕ Fin F.length → ℕ := Sum.elim (fun _ => 1) (fun i => (F.get i).2)
  let I := (componentPowerProduct (n := n) F).mul
    (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)
  have hI : I.IsInvertible := GermIdealTotalTransform.isInvertible_mul
    (invertible_component_product F hF)
    (isInvertible_vanishingIdeal_normalCrossingsCarrier (isNormalCrossingsCarrier_of_boundaryAdapted h))
  have hgen' : ∀ᶠ y in 𝓝 x, ∀ g, I.mem y g ↔
      IsInSpanAt (n := n) (· = fun z => ∏ i ∈ A, flatCoord Φ (τ i) z ^ a i) y g := by
    simpa only [I,A,T,τ,a,Finset.prod_disjSum,Sum.elim_inl,Sum.elim_inr,id_eq,pow_one] using hgen
  have hτinj : Set.InjOn τ A := by
    intro i hi j hj heq
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl heq
      | inr j =>
        have hiS : i ∈ S := Finset.inl_mem_disjSum.mp hi
        have hjT : j ∈ T := Finset.inr_mem_disjSum.mp hj
        have hn := hσS j (Finset.mem_filter.mp hjT).2
        change i = σ j at heq
        exact (hn (heq ▸ hiS)).elim
    | inr i =>
      cases j with
      | inl j =>
        have hiT : i ∈ T := Finset.inr_mem_disjSum.mp hi
        have hjS : j ∈ S := Finset.inl_mem_disjSum.mp hj
        have hn := hσS i (Finset.mem_filter.mp hiT).2
        change σ i = j at heq
        exact (hn (heq.symm ▸ hjS)).elim
      | inr j =>
        have hiT : i ∈ T := Finset.inr_mem_disjSum.mp hi
        have hjT : j ∈ T := Finset.inr_mem_disjSum.mp hj
        exact congrArg Sum.inr (hσinj (Finset.mem_filter.mp hiT).2 (Finset.mem_filter.mp hjT).2 heq)
  have hz : ∀ i ∈ A, flatCoord Φ (τ i) x = 0 := fun i _ => by simp [flatCoord,h0]
  have hpow := prod_flatCoord_pow_order Φ τ a (mem_flatDomain_self Φ) A hz
  have hord := order_eq_of_whole_principal_generator
    (holomorphicAt_finset_prod A (fun i _ => CompanionReduction.holomorphicAt_pow_of
      (holomorphicAt_flatCoord Φ (τ i) (mem_flatDomain_self Φ)) (a i)))
    hgen'.self_of_nhds hpow.1 hpow.2
  have hord' : GermIdealOrder.order n univ I x =
      ((S.card+∑ i ∈ T,(F.get i).2 : ℕ) : ℕ∞) := by
    simpa only [A,a,Finset.sum_disjSum,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const,smul_eq_mul,mul_one] using hord
  refine ⟨Φ,S,hsrc,h0,hH,hord',?_,?_⟩
  · intro i hi
    have hiA : Sum.inr i ∈ A := Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    exact exponent_of_actual_coordinate_product Φ hsrc A τ a hτinj I hI hgen'
      (Sum.inr i) hiA (F.get i).1 hi (hflat i hi)
  · intro j hj
    have hjA : Sum.inl j ∈ A := Finset.inl_mem_disjSum.mpr hj
    apply exponent_of_actual_coordinate_product Φ hsrc A τ a hτinj I hI hgen' (Sum.inl j) hjA
    · exact ⟨mem_flatDomain_self Φ,by simp [flatCoord,h0]⟩
    · intro y hy
      exact and_iff_right hy

private theorem stageCentres_head {A : CMfd.{u} n}
    (P : ∀ {D : CMfd.{u} n}, BlowupTower A D → Set D → Prop) :
    ∀ {D : CMfd.{u} n} (T : BlowupTower A D), StageCentres P T →
      ∀ i : ℕ, StageCentres P (BlowupTowerSplit.head T i)
  | _,.refl,hT,0 => hT
  | _,.step _ _ _ _,hT,0 => hT
  | _,.refl,_,_+1 => trivial
  | _,.step T _ _ _,hT,i+1 => stageCentres_head P T hT.1 i

/-- Actual higher centres on each LITERAL prefix of the internally generated original procedure. -/
theorem originalPrefixCentres {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    StageCentres (fun R C => IsHigherSeparationCentre (n := n)
      (strictTransform n R.proj H) (geoTransformAlong (originalMarkedIdeal H) R).E C)
      (BlowupTowerSplit.head (originalSeparation hH).T i) :=
  stageCentres_head _ _ (originalSeparation hH).centres i

/-- The internally produced historical weights on every LITERAL original prefix. -/
def originalPrefixWeights {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) :
    List (Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ) :=
  recordedOriginalWeights H δ (BlowupTowerSplit.head (originalSeparation hH).T i) (originalPrefixCentres hH i)

theorem originalPrefixWeights_carriers {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) :
    (originalPrefixWeights hH δ i).map Prod.fst =
      (geoTransformAlong (originalMarkedIdeal H) (BlowupTowerSplit.head (originalSeparation hH).T i)).E :=
  recordedOriginalWeights_carriers H δ _ _

theorem originalPrefixWeights_length_le {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) :
    (originalPrefixWeights hH δ i).length ≤ n-1 := by
  have hlen := congrArg List.length (originalPrefixWeights_carriers hH δ i)
  rw [List.length_map,length_E_geoTransformAlong] at hlen
  simp only [originalMarkedIdeal,List.length_nil,zero_add] at hlen
  rw [hlen,BlowupTowerSplit.length_head]
  exact (Nat.sub_le _ _).trans (originalSeparation_geometry hH).1

theorem originalPrefixWeights_bounds {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) :
    ∀ p ∈ originalPrefixWeights hH δ i, 2-δ ≤ p.2 ∧ p.2 ≤ n-δ :=
  recordedOriginalWeights_bounds H δ _ _

theorem originalPrefixWeights_member_invertible {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) :
    ∀ p ∈ originalPrefixWeights hH δ i,
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible :=
  recordedOriginalWeights_member_invertible H δ _ _

/-- Exact WHOLE original total pullback and exact historical r weights at each LITERAL generated prefix. -/
theorem originalPrefix_total_dictionary {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    GermIdeal.pullback (m := n) T.proj (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H) =
      (componentPowerProduct (n := n) (originalPrefixWeights hH 0 i)).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H)) :=
  higherSeparationCentres_total_dictionary hH _ _

/-- Exact SAME original controlled ideal and exact historical r-1 weights at each LITERAL generated prefix. -/
theorem originalPrefix_controlled_dictionary {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    (geoTransformAlong (originalMarkedIdeal H) T).ideal =
      (componentPowerProduct (n := n) (originalPrefixWeights hH 1 i)).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H)) :=
  higherSeparationCentres_controlled_dictionary hH _ _

private theorem weighted_order_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (hn : 0 < n)
    {H : Set M} (F : List (Set M × ℕ))
    (h : IsBoundaryAdaptedCarrier (n := n) H (F.map Prod.fst))
    (hF : ∀ p ∈ F, (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) p.1).IsInvertible)
    (hb : ∀ p ∈ F, p.2 ≤ n) (x : M) :
    GermIdealOrder.order n univ ((componentPowerProduct (n := n) F).mul
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)) x ≤
      ((n+n*F.length : ℕ) : ℕ∞) := by
  classical
  obtain ⟨Φ,S,hsrc,h0,hH,hord,_,_⟩ := exists_joint_whole_weighted_exponents hn F h hF x
  rw [hord]
  let T := Finset.univ.filter (fun i => x ∈ (F.get i).1)
  have hS : S.card ≤ n := (Finset.card_le_univ S).trans_eq (by simp)
  have hT : T.card ≤ F.length := (Finset.card_le_univ T).trans_eq (by simp)
  have hsum : (∑ i ∈ T,(F.get i).2) ≤ T.card*n := by
    calc
      (∑ i ∈ T,(F.get i).2) ≤ ∑ _i ∈ T,n := Finset.sum_le_sum (fun i _ => hb _ (List.get_mem _ _))
      _ = T.card*n := by simp
  have hnat : S.card+(∑ i ∈ T,(F.get i).2) ≤ n+n*F.length := by
    calc
      S.card+(∑ i ∈ T,(F.get i).2) ≤ n+T.card*n := Nat.add_le_add hS hsum
      _ ≤ n+n*F.length := Nat.add_le_add_left (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n hT) n
  exact_mod_cast hnat

/-- Every actual prefix weighted ideal has a GLOBAL finite order bound internally, without compactness. -/
theorem originalPrefix_weighted_order_bound {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) (hδ : δ ≤ 1)
    (x : (BlowupTowerSplit.split (originalSeparation hH).T i).1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    GermIdealOrder.order n univ ((componentPowerProduct (n := n) (originalPrefixWeights hH δ i)).mul
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H))) x ≤
      ((n*n : ℕ) : ℕ∞) := by
  dsimp only
  have hpair := higherSeparationCentres_pair hH _ (originalPrefixCentres hH i)
  have hpairF := hpair
  rw [← originalPrefixWeights_carriers hH δ i] at hpairF
  by_cases hn : 0 < n
  · have hb : ∀ p ∈ originalPrefixWeights hH δ i, p.2 ≤ n :=
      fun p hp => ((originalPrefixWeights_bounds hH δ i p hp).2).trans (Nat.sub_le _ _)
    have horder := weighted_order_le hn (originalPrefixWeights hH δ i) hpairF
      (originalPrefixWeights_member_invertible hH δ i) hb x
    apply horder.trans
    have hlen := originalPrefixWeights_length_le hH δ i
    have hmul := Nat.mul_le_mul_left n hlen
    have heq : n+n*(n-1) = n*n := by
      have hh : n-1+1=n := by omega
      have he := congrArg (fun k => n*k) hh
      rw [Nat.mul_add,Nat.mul_one] at he
      omega
    exact_mod_cast (Nat.add_le_add_left hmul n).trans_eq heq
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hnil : originalPrefixWeights hH δ i = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro p hp
      have hh := originalPrefixWeights_bounds hH δ i p hp
      omega
    have hNC := isNormalCrossingsCarrier_of_boundaryAdapted hpair
    have hcoh := DivisorMetric.isCoherent_of_isInvertible (isInvertible_vanishingIdeal_normalCrossingsCarrier hNC)
    rw [hnil,componentPowerProduct,BlowupControlledTransform.unitIdeal_mul hcoh,
      order_vanishingIdeal_eq_branchMultiplicity hNC x]
    exact_mod_cast branchMultiplicity_le hNC x

/-- The SAME WHOLE original total ideal has globally bounded finite order on EVERY literal prefix. -/
theorem originalPrefix_total_order_bound {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ)
    (x : (BlowupTowerSplit.split (originalSeparation hH).T i).1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    GermIdealOrder.order n univ (GermIdeal.pullback (m := n) T.proj
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)) x ≤ ((n*n : ℕ) : ℕ∞) := by
  dsimp only
  rw [originalPrefix_total_dictionary hH i]
  exact originalPrefix_weighted_order_bound hH 0 i (by omega) x

/-- The SAME original marking-one controlled ideal has globally bounded finite order on EVERY literal prefix. -/
theorem originalPrefix_controlled_order_bound {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ)
    (x : (BlowupTowerSplit.split (originalSeparation hH).T i).1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    GermIdealOrder.order n univ (geoTransformAlong (originalMarkedIdeal H) T).ideal x ≤ ((n*n : ℕ) : ℕ∞) := by
  dsimp only
  rw [originalPrefix_controlled_dictionary hH i]
  exact originalPrefix_weighted_order_bound hH 1 i le_rfl x

/-- Every actual recorded boundary coefficient is the intrinsic exponent of its SAME entire weighted ideal. -/
theorem originalPrefix_weighted_divExp {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ) (hδ : δ ≤ 1)
    {p : Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ}
    (hp : p ∈ originalPrefixWeights hH δ i)
    {x : (BlowupTowerSplit.split (originalSeparation hH).T i).1} (hx : x ∈ p.1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    divExp n ((componentPowerProduct (n := n) (originalPrefixWeights hH δ i)).mul
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H))) p.1 x = p.2 := by
  dsimp only
  by_cases hn : 0 < n
  · have hpair := higherSeparationCentres_pair hH _ (originalPrefixCentres hH i)
    rw [← originalPrefixWeights_carriers hH δ i] at hpair
    obtain ⟨Φ,S,hsrc,h0,hflat,hord,hE,_⟩ := exists_joint_whole_weighted_exponents hn
      (originalPrefixWeights hH δ i) hpair (originalPrefixWeights_member_invertible hH δ i) x
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hp
    have hh := hE j (hj.symm ▸ hx)
    simpa only [hj] using hh
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hh := originalPrefixWeights_bounds hH δ i p hp
    omega

/-- TRUE original whole total exponents are exactly the internally recorded attained r at every actual component point. -/
theorem originalPrefix_total_divExp {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ)
    {p : Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ}
    (hp : p ∈ originalPrefixWeights hH 0 i)
    {x : (BlowupTowerSplit.split (originalSeparation hH).T i).1} (hx : x ∈ p.1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    divExp n (GermIdeal.pullback (m := n) T.proj
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H)) p.1 x = p.2 := by
  dsimp only
  rw [originalPrefix_total_dictionary hH i]
  exact originalPrefix_weighted_divExp hH 0 i (by omega) hp hx

/-- TRUE SAME original controlled exponents are exactly the internally recorded r-1 at every actual component point. -/
theorem originalPrefix_controlled_divExp {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ)
    {p : Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ}
    (hp : p ∈ originalPrefixWeights hH 1 i)
    {x : (BlowupTowerSplit.split (originalSeparation hH).T i).1} (hx : x ∈ p.1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    divExp n (geoTransformAlong (originalMarkedIdeal H) T).ideal p.1 x = p.2 := by
  dsimp only
  rw [originalPrefix_controlled_dictionary hH i]
  exact originalPrefix_weighted_divExp hH 1 i le_rfl hp hx

/-- EVERY literal prefix internally supplies its actual original branch dictionary and true weighted exponent one. -/
theorem exists_originalPrefix_weighted_local_branches {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (δ i : ℕ)
    (x : (BlowupTowerSplit.split (originalSeparation hH).T i).1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ strictTransform n T.proj H ↔ ∃ j ∈ S, flatCoord Φ j y = 0) ∧
      ∀ j ∈ S, divExp n ((componentPowerProduct (n := n) (originalPrefixWeights hH δ i)).mul
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) (strictTransform n T.proj H)))
        {z | z ∈ flatDomain Φ ∧ flatCoord Φ j z = 0} x = 1 := by
  dsimp only
  have hpair := higherSeparationCentres_pair hH _ (originalPrefixCentres hH i)
  rw [← originalPrefixWeights_carriers hH δ i] at hpair
  by_cases hn : 0 < n
  · obtain ⟨Φ,S,hsrc,h0,hflat,_,_,hbranches⟩ := exists_joint_whole_weighted_exponents hn
      (originalPrefixWeights hH δ i) hpair (originalPrefixWeights_member_invertible hH δ i) x
    exact ⟨Φ,S,hsrc,h0,hflat,hbranches⟩
  · obtain ⟨Φ,hsrc,h0,S,hflat⟩ := (isNormalCrossingsCarrier_of_boundaryAdapted hpair).2 x
    refine ⟨Φ,S,hsrc,h0,hflat,?_⟩
    intro j _
    have hh := j.isLt
    omega

/-- The SAME whole original total pullback has exponent one on EVERY internally produced local original branch. -/
theorem exists_originalPrefix_total_local_branches {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ)
    (x : (BlowupTowerSplit.split (originalSeparation hH).T i).1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ strictTransform n T.proj H ↔ ∃ j ∈ S, flatCoord Φ j y = 0) ∧
      ∀ j ∈ S, divExp n (GermIdeal.pullback (m := n) T.proj
        (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := n) H))
        {z | z ∈ flatDomain Φ ∧ flatCoord Φ j z = 0} x = 1 := by
  dsimp only
  rw [originalPrefix_total_dictionary hH i]
  exact exists_originalPrefix_weighted_local_branches hH 0 i x

/-- The SAME marking-one controlled ideal has exponent one on EVERY internally produced local original branch. -/
theorem exists_originalPrefix_controlled_local_branches {A : CMfd.{u} n} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ)
    (x : (BlowupTowerSplit.split (originalSeparation hH).T i).1) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ y ∈ flatDomain Φ, y ∈ strictTransform n T.proj H ↔ ∃ j ∈ S, flatCoord Φ j y = 0) ∧
      ∀ j ∈ S, divExp n (geoTransformAlong (originalMarkedIdeal H) T).ideal
        {z | z ∈ flatDomain Φ ∧ flatCoord Φ j z = 0} x = 1 := by
  dsimp only
  rw [originalPrefix_controlled_dictionary hH i]
  exact exists_originalPrefix_weighted_local_branches hH 1 i x

open HironakaConnectedBoundaryComponents in
/-- Exact recorded exponent on EVERY actual connected boundary component, without connectedness input. -/
theorem originalPrefix_weighted_connectedComponent_divExp {m : ℕ} {A : CMfd.{u} (m+1)} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := m+1) H) (δ i : ℕ) (hδ : δ ≤ 1)
    {p : Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ}
    (hp : p ∈ originalPrefixWeights hH δ i)
    {c x : (BlowupTowerSplit.split (originalSeparation hH).T i).1}
    (hc : c ∈ p.1) (hx : x ∈ connectedComponentIn p.1 c) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    divExp (m+1) ((componentPowerProduct (n := m+1) (originalPrefixWeights hH δ i)).mul
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := m+1) (strictTransform (m+1) T.proj H)))
      (connectedComponentIn p.1 c) x = p.2 := by
  dsimp only
  have hpair := higherSeparationCentres_pair hH _ (originalPrefixCentres hH i)
  have hE := isSNCDivisor_of_boundaryAdapted hpair
  rw [← originalPrefixWeights_carriers hH δ i] at hE
  have hpE : p.1 ∈ (originalPrefixWeights hH δ i).map Prod.fst := List.mem_map.mpr ⟨p,hp,rfl⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hpE
  have heq := divExp_connectedComponent_eq hE j (hj.symm ▸ hc) (hj.symm ▸ hx)
    ((componentPowerProduct (n := m+1) (originalPrefixWeights hH δ i)).mul
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := m+1)
        (strictTransform (m+1) (BlowupTowerSplit.head (originalSeparation hH).T i).proj H)))
  rw [hj] at heq
  rw [heq]
  exact originalPrefix_weighted_divExp hH δ i hδ hp (connectedComponentIn_subset p.1 c hx)

/-- The TRUE entire original total exponent on EVERY actual connected component is the historical r. -/
theorem originalPrefix_total_connectedComponent_divExp {m : ℕ} {A : CMfd.{u} (m+1)} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := m+1) H) (i : ℕ)
    {p : Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ}
    (hp : p ∈ originalPrefixWeights hH 0 i)
    {c x : (BlowupTowerSplit.split (originalSeparation hH).T i).1}
    (hc : c ∈ p.1) (hx : x ∈ connectedComponentIn p.1 c) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    divExp (m+1) (GermIdeal.pullback (m := m+1) T.proj
      (Hironaka.HolomorphicIdealSheaves.vanishingIdeal (n := m+1) H))
      (connectedComponentIn p.1 c) x = p.2 := by
  dsimp only
  rw [originalPrefix_total_dictionary hH i]
  exact originalPrefix_weighted_connectedComponent_divExp hH 0 i (by omega) hp hc hx

/-- The TRUE SAME marking-one controlled exponent on EVERY actual connected component is the historical r-1. -/
theorem originalPrefix_controlled_connectedComponent_divExp {m : ℕ} {A : CMfd.{u} (m+1)} {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := m+1) H) (i : ℕ)
    {p : Set (BlowupTowerSplit.split (originalSeparation hH).T i).1 × ℕ}
    (hp : p ∈ originalPrefixWeights hH 1 i)
    {c x : (BlowupTowerSplit.split (originalSeparation hH).T i).1}
    (hc : c ∈ p.1) (hx : x ∈ connectedComponentIn p.1 c) :
    let T := BlowupTowerSplit.head (originalSeparation hH).T i
    divExp (m+1) (geoTransformAlong (originalMarkedIdeal H) T).ideal
      (connectedComponentIn p.1 c) x = p.2 := by
  dsimp only
  rw [originalPrefix_controlled_dictionary hH i]
  exact originalPrefix_weighted_connectedComponent_divExp hH 1 i le_rfl hp hc hx

end
end Hironaka.HironakaNormalCrossingsOriginalExponents
