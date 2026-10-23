import DeJongAlterations.StableModification.RiemannZariski.Refinement

/-!
# Refinements over an algebraic extension of the function field are alterations

Temkin, *Stable modification of relative curves* (J. Algebraic Geom. 19 (2010); arXiv v3,
`references/temkin10-stable-modification/source/semi-stable.tex`), §3.2, remark after
Definition 3.2.1 (T:2310–2312): a `K̄`-modification of an integral scheme `S` with function field
`K`, for `K̄` an algebraic closure of `K`, is an alteration. The proof of Theorem 1.5 (§5,
T:3379–3399) works with the valuation rings of `K̄ = K(S)ᵃ` (our decision D-DJ9: no generic
étaleness is needed downstream), so the refinements of Proposition 3.2.6 are taken with values
in the algebraic, possibly inseparable, extension `L = K(S)ᵃ` of `K(S)`.

The integrated `RiemannZariskiSpace.isAlteration_isGenericallyEtale_of_hasCharts` and
`RiemannZariskiSpace.exists_refinement_genericallyEtale` (lane RZ1) need `L / K(S)` separable
(they also prove generic étaleness). Here the alteration part is proved for any algebraic
extension, without noetherianity (node G2′ of `PLAN-T5.md`, ERRATA DJA-O22): the chart
`W ⊆ p⁻¹ V` over an affine open `V ∋ η_S` on which the finitely many chart generators are
integral is the full preimage of `V`, and its section ring `s_V(Γ(S, V))[F]` is finite over
`Γ(S, V)`, so `p` is finite over `V`.

## Main results

* `Global.exists_affine_isIntegral_of_isAlgebraic`: a nonempty affine open over which finitely
  many elements of an algebraic extension `L / K(S)` are integral.
* `Global.isAlteration_of_hasCharts`: a refinement of `(S, Spec L → S)` with charts with respect
  to a finite set is an alteration, for `S` integral and separated and `L / K(S)` algebraic.
* `Global.exists_refinement_isAlteration`: Temkin's Proposition 3.2.6 (affine pieces, with the
  covering addendum) by an alteration, for `L / K(S)` algebraic.

Blueprint: `sm-global.tex`, `lem:sm-global-refinement-alteration`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

universe u

namespace DeJongAlterations.StableModification.Global

open RiemannZariskiSpace

variable {L : Type u} [Field L] {S : Scheme.{u}} [IsIntegral S] [Algebra S.functionField L]

/-- **Integrality over a nonempty affine open** (algebraic version of
`RiemannZariskiSpace.exists_affine_isIntegral`). For an integral scheme `S`, an algebraic
extension `L` of `K(S)` and a finite set `F ⊆ L`, there is an affine open `V ∋ η_S` over whose
section ring (embedded in `L` by the generic point) every element of `F` is integral. -/
theorem exists_affine_isIntegral_of_isAlgebraic [Algebra.IsAlgebraic S.functionField L]
    {F : Set L} (hF : F.Finite) :
    ∃ (V : S.Opens) (hV : IsAffineOpen V) (hgV : genericPoint S ∈ V), ∀ x ∈ F,
      @IsIntegral Γ(S, V) L _ _ (sectionsToField (functionFieldPoint S L) V
        (functionFieldPoint_preimage hV hgV)).toAlgebra x := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hg₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint S)) isOpen_univ
  have : Nonempty V₀ := ⟨⟨_, hg₀⟩⟩
  set s₀ := sectionsToField (functionFieldPoint S L) V₀ (functionFieldPoint_preimage hV₀ hg₀)
  let _ : Algebra Γ(S, V₀) L := s₀.toAlgebra
  have : IsScalarTower Γ(S, V₀) S.functionField L := IsScalarTower.of_algebraMap_eq fun a => by
    change s₀ a = _
    rw [show s₀ = _ from sectionsToField_functionFieldPoint hV₀ hg₀]
    rfl
  have : IsFractionRing Γ(S, V₀) S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S V₀ hV₀
  have halg : ∀ x : F, IsAlgebraic Γ(S, V₀) (x : L) := fun x =>
    (IsFractionRing.isAlgebraic_iff Γ(S, V₀) S.functionField L).2
      (Algebra.IsAlgebraic.isAlgebraic (x : L))
  choose y hy0 hyint using fun x : F => (halg x).exists_integral_multiple
  have := hF.fintype
  let a : Γ(S, V₀) := ∏ x : F, y x
  have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hy0 x
  have hV₁ : IsAffineOpen (S.basicOpen a) := hV₀.basicOpen a
  have hne : (S.basicOpen a : Set S).Nonempty := by
    rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, Ne,
      TopologicalSpace.Opens.coe_inj, basicOpen_eq_bot_iff]
    exact ha0
  have hg₁ : genericPoint S ∈ S.basicOpen a :=
    ((genericPoint_spec S).mem_open_set_iff (S.basicOpen a).isOpen).2 (by simpa using hne)
  refine ⟨S.basicOpen a, hV₁, hg₁, fun x hx => ?_⟩
  set s₁ := sectionsToField (functionFieldPoint S L) (S.basicOpen a)
    (functionFieldPoint_preimage hV₁ hg₁)
  let ρ := S.presheaf.map (homOfLE (S.basicOpen_le a)).op
  let _ : Algebra Γ(S, S.basicOpen a) L := s₁.toAlgebra
  let _ : Algebra Γ(S, V₀) Γ(S, S.basicOpen a) := ρ.hom.toAlgebra
  have hρ : ∀ b, s₁ (ρ b) = s₀ b := by
    intro b
    rw [show s₁ = _ from sectionsToField_functionFieldPoint hV₁ hg₁,
      show s₀ = _ from sectionsToField_functionFieldPoint hV₀ hg₀, RingHom.comp_apply,
      RingHom.comp_apply]
    congr 1
    exact TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE (S.basicOpen_le a))
      (genericPoint S) hg₁ b
  have : IsScalarTower Γ(S, V₀) Γ(S, S.basicOpen a) L :=
    IsScalarTower.of_algebraMap_eq fun b => (hρ b).symm
  have h1 : IsIntegral Γ(S, S.basicOpen a) (y ⟨x, hx⟩ • x) := (hyint ⟨x, hx⟩).tower_top
  have hunit : IsUnit (ρ (y ⟨x, hx⟩)) := by
    refine isUnit_of_dvd_unit (map_dvd ρ.hom ?_) (S.toRingedSpace.isUnit_res_basicOpen a)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  obtain ⟨u, hu⟩ := hunit
  have hx' : x = algebraMap Γ(S, S.basicOpen a) L ↑u⁻¹ * (y ⟨x, hx⟩ • x) := by
    rw [Algebra.smul_def, ← mul_assoc, IsScalarTower.algebraMap_apply Γ(S, V₀)
      Γ(S, S.basicOpen a) L, ← map_mul]
    change x = algebraMap _ L (↑u⁻¹ * ρ (y ⟨x, hx⟩)) * x
    rw [← hu, Units.inv_mul, map_one, one_mul]
  rw [hx']
  exact (isIntegral_algebraMap).mul h1

/-- **Refinements over an algebraic extension are alterations** (Temkin, T:2310–2312, for
`K̄ = K(S)ᵃ`; algebraic version of the alteration part of
`RiemannZariskiSpace.isAlteration_isGenericallyEtale_of_hasCharts`). Let `S` be integral and
separated, `L` an algebraic extension of `K(S)` and `η` the generic point `Spec L → S`. A
refinement of `(S, η)` with charts with respect to a finite set is an alteration. -/
theorem isAlteration_of_hasCharts [S.IsSeparated] [Algebra.IsAlgebraic S.functionField L]
    {S' : Scheme.{u}} {p : S' ⟶ S} {η' : Spec (.of L) ⟶ S'}
    (hR : IsRefinement (functionFieldPoint S L) p η') {F : Set L} (hF : F.Finite)
    (hC : HasCharts (functionFieldPoint S L) p η' F) :
    IsAlteration p := by
  have := hR.isProper
  have := hR.isIntegral
  have := hR.isDominant
  have := isSeparated_of_isProper p
  obtain ⟨V, hV, hgV, hint⟩ := exists_affine_isIntegral_of_isAlgebraic (L := L) (S := S) hF
  have hηV := functionFieldPoint_preimage (L := L) hV hgV
  obtain ⟨W, hW, hη'W, hWV, hinj, hrange⟩ := hC V hV hηV
  set s₁ := sectionsToField (functionFieldPoint S L) V hηV with hs₁
  set sW := sectionsToField η' W hη'W with hsW
  have hcomp : sW.comp (p.appLE V W hWV).hom = s₁ :=
    sectionsToField_comp_appLE p hR.comp_eq hWV hη'W hηV
  -- the chart ring lies in every valuation ring containing `s₁(Γ(S, V))`
  have hFV : ∀ V' : RiemannZariskiSpace L, V' ∈ ofRingHom s₁ →
      ∀ w, sW w ∈ V'.valuationSubring := by
    intro V' hV' w
    have hF' : F ⊆ V'.valuationSubring := by
      intro x hx
      let _ : Algebra Γ(S, V) L := s₁.toAlgebra
      let _ : Algebra Γ(S, V) V'.valuationSubring :=
        (s₁.codRestrict V'.valuationSubring (mem_ofRingHom.1 hV')).toAlgebra
      have : IsScalarTower Γ(S, V) V'.valuationSubring L :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hx' : IsIntegral V'.valuationSubring x := (hint x hx).tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
      rw [← hy]
      exact y.2
    have hle : sW.range ≤ V'.valuationSubring.toSubring := by
      rw [hrange]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact mem_ofRingHom.1 hV' a
      · rw [Subring.closure_le]
        exact hF'
    exact hle ⟨w, rfl⟩
  -- the chart is the full preimage of `V`
  have hWeq : p ⁻¹ᵁ V = W := by
    refine le_antisymm (fun x hx => ?_) hWV
    obtain ⟨V', ψ, hψ, rfl⟩ := hR.exists_extension x
    have hψp : toSpecValuationSubring V' ≫ (ψ ≫ p) = functionFieldPoint S L := by
      rw [← Category.assoc, hψ, hR.comp_eq]
    have hmem := mem_ofOpen_of_extension (ψ ≫ p) hψp (U := V) hx
    rw [mem_ofOpen_iff hηV] at hmem
    have hV'W : V' ∈ ofRingHom sW := mem_ofRingHom.2 (hFV V' hmem)
    rw [extension_unique hψ (toSpecValuationSubring_comp_extensionOfMem hW hη'W V' hV'W)]
    exact extensionOfMem_closedPoint hW hη'W V' hV'W
  subst hWeq
  let _ : Algebra Γ(S, V) Γ(S', p ⁻¹ᵁ V) := (p.appLE V (p ⁻¹ᵁ V) hWV).hom.toAlgebra
  let _ : Algebra Γ(S, V) L := s₁.toAlgebra
  let _ : Algebra Γ(S', p ⁻¹ᵁ V) L := sW.toAlgebra
  have : IsScalarTower Γ(S, V) Γ(S', p ⁻¹ᵁ V) L :=
    IsScalarTower.of_algebraMap_eq fun a => (congrArg (fun φ => φ a) hcomp).symm
  -- finite type
  have hG : (sW ⁻¹' F).Finite := hF.preimage hinj.injOn
  have htop : Algebra.adjoin Γ(S, V) (sW ⁻¹' F) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have key : ∀ y ∈ Subring.closure ((s₁.range : Set L) ∪ F),
        ∃ w ∈ Algebra.adjoin Γ(S, V) (sW ⁻¹' F), sW w = y := by
      intro y hy
      induction hy using Subring.closure_induction with
      | mem y hy =>
        rcases hy with ⟨a, rfl⟩ | hy
        · exact ⟨algebraMap _ _ a, Subalgebra.algebraMap_mem _ a,
            (congrArg (fun φ => φ a) hcomp)⟩
        · obtain ⟨w, rfl⟩ : y ∈ sW.range := by
            rw [hrange]
            exact (le_sup_right : Subring.closure F ≤ _) (Subring.subset_closure hy)
          exact ⟨w, Algebra.subset_adjoin hy, rfl⟩
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | one => exact ⟨1, one_mem _, map_one _⟩
      | add y z _ _ hy hz =>
        obtain ⟨w₁, h₁, rfl⟩ := hy
        obtain ⟨w₂, h₂, rfl⟩ := hz
        exact ⟨w₁ + w₂, add_mem h₁ h₂, map_add _ _ _⟩
      | neg y _ hy =>
        obtain ⟨w₁, h₁, rfl⟩ := hy
        exact ⟨-w₁, neg_mem h₁, map_neg _ _⟩
      | mul y z _ _ hy hz =>
        obtain ⟨w₁, h₁, rfl⟩ := hy
        obtain ⟨w₂, h₂, rfl⟩ := hz
        exact ⟨w₁ * w₂, mul_mem h₁ h₂, map_mul _ _ _⟩
    obtain ⟨w', hw', he⟩ := key (sW w) (by
      rw [Subring.closure_union, Subring.closure_eq, ← hrange]
      exact ⟨w, rfl⟩)
    rwa [hinj he] at hw'
  have : Algebra.FiniteType Γ(S, V) Γ(S', p ⁻¹ᵁ V) := ⟨⟨hG.toFinset, by simpa using htop⟩⟩
  -- finiteness over `V`
  have : Algebra.IsIntegral Γ(S, V) Γ(S', p ⁻¹ᵁ V) := by
    constructor
    intro w
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom Γ(S, V) Γ(S', p ⁻¹ᵁ V) L) hinj]
    have hle : sW.range ≤ (integralClosure Γ(S, V) L).toSubring := by
      rw [hrange]
      refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap
      · rw [Subring.closure_le]
        exact hint
    exact hle ⟨w, rfl⟩
  have hRfin : (p.appLE V (p ⁻¹ᵁ V) hWV).hom.Finite := Algebra.IsIntegral.finite
  have hfac : p ∣_ V = hW.isoSpec.hom ≫ Spec.map (p.appLE V (p ⁻¹ᵁ V) hWV) ≫
      hV.isoSpec.inv := by
    rw [← cancel_mono V.ι, morphismRestrict_ι, Category.assoc, Category.assoc,
      IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec p hV hW hWV,
      ← IsAffineOpen.isoSpec_inv_ι hW, Category.assoc, Iso.hom_inv_id_assoc]
  have : IsFinite (Spec.map (p.appLE V (p ⁻¹ᵁ V) hWV)) := (IsFinite.SpecMap_iff _).2 hRfin
  have hfinite : IsFinite (p ∣_ V) := by
    rw [hfac]
    infer_instance
  have hdom : IsDominant p := by
    have : IsDominant (η' ≫ p) := by rw [hR.comp_eq]; infer_instance
    exact IsDominant.of_comp η' p
  exact
    { toIsProper := hR.isProper, toIsDominant := hdom, sourceIntegral := hR.isIntegral,
      targetIntegral := inferInstance, genericallyFinite := ⟨V, ⟨⟨_, hgV⟩⟩, hfinite⟩ }

/-- **Refinement by an alteration** (Temkin, Proposition 3.2.6 for `K̄ = K(S)ᵃ`, with the
remark T:2310–2312; algebraic version of `RiemannZariskiSpace.exists_refinement_genericallyEtale`).
Let `S` be integral and separated, `L` an algebraic extension of `K(S)` (e.g. an algebraic
closure), `η` the generic point `Spec L → S`, and `gᵢ : Tᵢ → S` finitely many morphisms locally
of finite type from affine schemes into affine opens `Vᵢ`, with points `ηTᵢ` over `η`. There is
an alteration `p : S' → S` with a dominant point `η'` over `η`, every point of `S'` the centre of
an extension of `η'` to a valuation ring of `L`, and opens `Wᵢ ⊆ S'` with proper `hᵢ : Wᵢ → Tᵢ`
over `S` compatible with dominant points over `η'` and `ηTᵢ`, such that every valuation ring of
`RZ_L(Tᵢ)` has an extension of `η'` centred in `Wᵢ`; if the `RZ_L(Tᵢ)` cover `RZ_L(S)`, the `Wᵢ`
cover `S'`. -/
theorem exists_refinement_isAlteration [S.IsSeparated] [Algebra.IsAlgebraic S.functionField L]
    {ι : Type*} [Finite ι] (T : ι → Scheme.{u})
    [∀ i, IsAffine (T i)] (g : ∀ i, T i ⟶ S) [∀ i, LocallyOfFiniteType (g i)]
    (ηT : ∀ i, Spec (.of L) ⟶ T i) (hηT : ∀ i, ηT i ≫ g i = functionFieldPoint S L)
    (V : ι → S.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hgV : ∀ i, g i ⁻¹ᵁ V i = ⊤) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (η' : Spec (.of L) ⟶ S') (W : ι → S'.Opens)
      (h : ∀ i, (W i).toScheme ⟶ T i),
      IsAlteration p ∧ IsRefinement (functionFieldPoint S L) p η' ∧
      (∀ i, IsProper (h i) ∧ h i ≫ g i = (W i).ι ≫ p ∧
        ∃ e : Spec (.of L) ⟶ (W i).toScheme, e ≫ (W i).ι = η' ∧ e ≫ h i = ηT i ∧
          IsDominant e) ∧
      (∀ i, ∀ V' ∈ ofScheme (ηT i), ∃ ψ : Spec (.of V'.valuationSubring) ⟶ S',
        toSpecValuationSubring V' ≫ ψ = η' ∧ ψ (specClosedPoint V') ∈ W i) ∧
      (ofScheme (functionFieldPoint S L) ⊆ ⋃ i, ofScheme (ηT i) → ⨆ i, W i = ⊤) := by
  obtain ⟨S', p, η', F, W, h, hR, hF, hC, hh, hRZ, hcov⟩ :=
    exists_refinement (functionFieldPoint S L) T g ηT hηT V hV hgV
  exact ⟨S', p, η', W, h, isAlteration_of_hasCharts hR hF hC, hR, hh, hRZ, hcov⟩

end DeJongAlterations.StableModification.Global
