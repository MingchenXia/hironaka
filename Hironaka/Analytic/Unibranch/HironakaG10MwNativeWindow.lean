import Hironaka.Analytic.Unibranch.HironakaG10MwChartRestriction
import Hironaka.Analytic.Unibranch.HironakaG10MwGraphChartFlat
import Hironaka.Analytic.Unibranch.HironakaG10SbChartFlatDictionary
import Hironaka.Analytic.Unibranch.HironakaG10SbChartFamilyDescent
import Hironaka.Analytic.Unibranch.HironakaG10ProperFiniteWindowFlattener

/-!
# Native asymmetric windows of an ordinary morphism, and the persistent local flattener
(G10-01-10 … 14, lane G10MW, run 0081)

`exists_native_window`: for every morphism `f : Y ⟶ X` of reduced complex spaces and every `y ∈ Y`
there are an open `V ∋ f y` of `X`, an open `W ∋ y` of `Y` and an ideal family `H` on `X`, locally
finitely generated on `V`, proper at `f y`, such that at every `x ∈ V` with `H x ≠ ⊤` and for EVERY
ideal `J ⊆ 𝒪_{X,x}`:
* flatness of `f` over `V(J)` along the whole fibre over `x` forces `H x ≤ J`;
* `H x ≤ J` forces flatness over `V(J)` at every point of the fibre lying in `W`.

Construction: the actual window of `HironakaG10MwWindowFamily` (graph row, Cartan generators,
privileged polydisc, same-window Schur family), restricted to the base open where the parameter family
lives (`HironakaG10MwChartRestriction`), descended to `X` (lane G10SB, G10-02-05), and read on native
stalks through lane G10SB's test-ideal dictionary (G10-02-04) and `graphChart_flat_iff_chartFlat`.

`persistentLocalFlattener`: for proper `f`, finitely many windows cover the compact fibre and the
asymmetric whole-fibre assembly (`exists_localFlattener_of_asymmetric_windows`) gives a local
flattener whose support contains the base point.  This proves the named input
`HironakaG10HirLocalFlattener.PersistentLocalFlattener` (Hironaka 1975 Th. 2.4 with `S = {x}`; Frisch
1968 Lemme 5).
-/

set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaHolomorphicJetRankLoci
  HironakaChowRelativeGraphPresentation HironakaG10HirFlatQuotient HironakaG10HirChartFlattener
  HironakaG10LocSectionNoether HironakaG10HirIdealGerms HironakaG10PNKernelSquare
  OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ProperFiniteWindowFlattener
  Hironaka.Analytic.Unibranch.HironakaG10MwGraphRow Hironaka.Analytic.Unibranch.HironakaG10MwWindowFamily
  Hironaka.Analytic.Unibranch.HironakaG10MwChartRestriction Hironaka.Analytic.Unibranch.HironakaG10MwGraphChartFlat
  Hironaka.Analytic.Unibranch.HironakaG10SbBaseChartStalk Hironaka.Analytic.Unibranch.HironakaG10SbChartFlatDictionary
  Hironaka.Analytic.Unibranch.HironakaG10SbChartFamilyDescent

/-- A surjective ring map between local rings sends proper ideals to proper ideals. -/
theorem map_ne_top_of_surjective {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) (hφ : Function.Surjective φ) {I : Ideal R} (hI : I ≠ ⊤) :
    I.map φ ≠ ⊤ := by
  intro htop
  rw [Ideal.eq_top_iff_one, Ideal.mem_map_iff_of_surjective φ hφ] at htop
  obtain ⟨a, ha, h1⟩ := htop
  have hm : a ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI ha
  have hu : IsUnit (1 - a) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a hm
  have h0 : φ (1 - a) = 0 := by rw [map_sub, map_one, h1, sub_self]
  exact not_isUnit_zero (h0 ▸ hu.map φ)

theorem baseChartLiftAt_congr {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    {c₁ c₂ : e.carrier} (h : c₁ = c₂) (x : X.obj.left) (h₁ : e.toPoint c₁ = x)
    (h₂ : e.toPoint c₂ = x) : baseChartLiftAt e c₁ x h₁ = baseChartLiftAt e c₂ x h₂ := by
  subst h
  rfl

/-- **One native asymmetric window around a fibre point.** -/
theorem exists_native_window {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (y : Y.obj.left) :
    ∃ (V : Set X.obj.left) (_ : IsOpen V) (_ : f.hom.left.base y ∈ V)
      (W : Set Y.obj.left) (_ : IsOpen W) (_ : y ∈ W)
      (H : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)),
      IsLocallyFinitelyGeneratedOn X.obj.left V H ∧ H (f.hom.left.base y) ≠ ⊤ ∧
      (∀ x ∈ V, H x ≠ ⊤ → ∀ J : Ideal (X.obj.left.presheaf.stalk x), FlatOverAt f x J → H x ≤ J) ∧
      (∀ x ∈ V, H x ≠ ⊤ → ∀ J : Ideal (X.obj.left.presheaf.stalk x), H x ≤ J →
        ∀ (y' : Y.obj.left) (h : f.hom.left.base y' = x), y' ∈ W →
          (quotMap (fibreStalkMap f x y' h) J).Flat) := by
  classical
  -- the two charts
  let eX := LocalEmbedding.ofPoint X (f.hom.left.base y)
  obtain ⟨c₀, hc₀⟩ := LocalEmbedding.mem_range_ofPoint X (f.hom.left.base y)
  let eY := LocalEmbedding.ofPoint Y y
  obtain ⟨cy, hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hc : f.hom.left.base (eY.toPoint cy) = eX.toPoint c₀ := by
    change f.hom.left.base ((LocalEmbedding.ofPoint Y y).toPoint cy) =
      (LocalEmbedding.ofPoint X (f.hom.left.base y)).toPoint c₀
    rw [hcy, hc₀]
  -- the actual window
  obtain ⟨U, hUV, hcU, φ, hφ, hCD, hsq, ψ, hψ, Wz, r, g, K₁, hWo, hWU, hK₁W, hK₁n, hK₁c, hφW,
    hgW, hgen, -, htopC, htopG, ⟨crit⟩⟩ := exists_actual_window f eX eY cy c₀ hc
  let e := eY.restrict U hUV
  let cc : ComplexModel eX.dim := c₀.val.val
  -- the base open where the parameter family lives
  let Ot : Opens (ComplexModel eX.dim) :=
    ⟨(fun u => u - cc) ⁻¹' (crit.U : Set (ComplexModel eX.dim)),
      crit.U.isOpen.preimage (continuous_id.sub continuous_const)⟩
  let O : Opens (ComplexModel eX.dim) := eX.ambient ⊓ Ot
  have hO : O ≤ eX.ambient := inf_le_left
  have hOU : ∀ u ∈ O, u - cc ∈ crit.U := fun u hu => hu.2
  obtain ⟨T, hT, φ', hφ', hCD', hφ'val, hTmem, hsq'⟩ :=
    exists_restricted_square f eX e φ hφ hCD hsq O hO
  let eX' := eX.restrict O hO
  let e' := e.restrict T hT
  obtain ⟨Hamb, hHamb⟩ : ∃ Hamb : ∀ z : AmbientSpace eX',
      Ideal ((AmbientSpace eX').presheaf.stalk z), Hamb = ambientFamily crit O cc hOU :=
    ⟨_, rfl⟩
  have hmapH : ∀ c : eX'.carrier, Ideal.map (actualStalkChartEquiv (n := eX'.dim) c.val).toRingHom
      (Hamb c.val) = Ideal.map (actualStalkChartEquiv (n := eX.dim)
        (translate O crit.U cc hOU c.val)).toRingHom
          (spanFamily crit.s univ (translate O crit.U cc hOU c.val)) := by
    intro c
    subst hHamb
    exact map_ambientFamily crit O cc hOU c.val
  have hfgH : ∀ c : eX'.carrier, IsLocallyFinitelyGeneratedAt (AmbientSpace eX') Hamb c.val := by
    intro c
    subst hHamb
    exact isLocallyFinitelyGeneratedAt_ambientFamily crit O cc hOU c.val
  clear hHamb
  let H := descendFamily eX' Hamb
  have hc₀O : cc ∈ O := ⟨c₀.val.property, by
    change cc - cc ∈ crit.U
    rw [sub_self]
    exact crit.zero_mem⟩
  let c₀' : eX'.carrier := restrictPoint eX hO c₀ hc₀O
  have hc₀' : eX'.toPoint c₀' = f.hom.left.base y := hc₀
  -- the restricted lift agrees with the ambient extension
  have hψ' : ∀ w (hw : w ∈ T), ψ w = (φ' ⟨w, hw⟩).val := by
    intro w hw
    rw [hφ'val, hψ w (hT hw)]
    rfl
  -- the chart image of the descended family
  have hHapply : ∀ c : eX'.carrier, H (eX'.toPoint c) = Ideal.map (baseChartLift eX' c)
      (Ideal.map (actualStalkChartEquiv (n := eX.dim) (translate O crit.U cc hOU c.val)).toRingHom
        (spanFamily crit.s univ (translate O crit.U cc hOU c.val))) := by
    intro c
    show descendFamily eX' Hamb (eX'.toPoint c) = _
    rw [descendFamily_apply, hmapH]
    rfl
  have hle_iff : ∀ (c : eX'.carrier) (J : Ideal (X.obj.left.presheaf.stalk (eX'.toPoint c))),
      H (eX'.toPoint c) ≤ J ↔
        Ideal.map (actualStalkChartEquiv (n := eX.dim) (translate O crit.U cc hOU c.val)).toRingHom
          (spanFamily crit.s univ (translate O crit.U cc hOU c.val)) ≤
            J.comap (baseChartLiftAt eX' c (eX'.toPoint c) rfl) := by
    intro c J
    show descendFamily eX' Hamb (eX'.toPoint c) ≤ J ↔ _
    rw [descendFamily_le_iff_at eX' Hamb c _ rfl J, hmapH]
    rfl
  have hne_of : ∀ c : eX'.carrier, H (eX'.toPoint c) ≠ ⊤ →
      Ideal.map (actualStalkChartEquiv (n := eX.dim) (translate O crit.U cc hOU c.val)).toRingHom
        (spanFamily crit.s univ (translate O crit.U cc hOU c.val)) ≠ ⊤ := by
    intro c hH htop
    apply hH
    rw [hHapply c, htop]
    exact Ideal.map_top _
  -- graph points over a base point: the native criterion is the chart criterion
  have hgraphPt : ∀ (c : eX'.carrier) (zC : e.carrier), zC.val.val ∈ Wz →
      (φ zC.val).val = c.val.val →
      ∃ (z' : e'.carrier) (h : f.hom.left.base (e'.toPoint z') = eX'.toPoint c),
        e'.toPoint z' = e.toPoint zC ∧
        ∀ J : Ideal (X.obj.left.presheaf.stalk (eX'.toPoint c)),
          (quotMap (fibreStalkMap f _ _ h) J).Flat ↔
            ChartFlat eX.dim eY.dim (graphRow ψ cc g)
              ((translate O crit.U cc hOU c.val).val, zC.val.val)
              (J.comap (baseChartLiftAt eX' c (eX'.toPoint c) rfl)) := by
    intro c zC hzW hφz
    have hzT : zC.val.val ∈ T := hTmem zC.val.val zC.val.property (hφz ▸ c.val.property)
    have hzC' : Opens.inclusion hT ⟨zC.val.val, hzT⟩ ∈ e.carrier := by
      have hz : Opens.inclusion hT ⟨zC.val.val, hzT⟩ = zC.val := Subtype.ext rfl
      rw [hz]
      exact zC.property
    let z' : e'.carrier := ⟨⟨zC.val.val, hzT⟩, hzC'⟩
    have hbase : (actualSubspaceMap hφ' hCD').base z' = c := by
      apply Subtype.ext
      apply Subtype.ext
      change (φ' ⟨zC.val.val, hzT⟩).val = c.val.val
      rw [hφ'val]
      exact hφz
    have hsqb := square_base f eX' e hT hφ' hCD' hsq' z'
    have hpt : (translate O crit.U cc hOU c.val).val = ψ zC.val.val - cc := by
      have h1 : ψ zC.val.val = c.val.val := (hψ _ zC.val.property).trans hφz
      rw [h1]
      rfl
    subst hbase
    refine ⟨z', hsqb.symm, rfl, fun J => ?_⟩
    refine (quotMap_fibre_flat_iff_graph f eX' e hT hφ' hCD' hsq' z' _ hsqb.symm rfl J).trans ?_
    refine (graphChart_flat_iff_chartFlat φ' hφ' e'.carrier z' ψ hψ'
      (fun k => holAt_of_differentiableOn hWo
        ((EuclideanSpace.proj k : ComplexModel eX.dim →L[ℂ] ℂ).differentiable.comp_differentiableOn hφW) hzW)
      cc g (fun j => holAt_of_differentiableOn hWo (hgW j) hzW)
      ((wholeChartStalkIdeal_vanishing_restrict hT e.carrier ⟨zC.val.val, hzT⟩).trans
        (hgen zC.val hzW)) _).trans ?_
    rw [hpt]
    exact Iff.rfl
  refine ⟨range eX'.toPoint, eX'.isOpen_range_toPoint, ⟨c₀', hc₀'⟩,
    e.toPoint '' {z : e.carrier | z.val.val ∈ interior K₁}, ?_, ?_, H, ?_, ?_, ?_, ?_⟩
  · -- the source window is open
    exact e.isOpenEmbedding_toPoint.isOpenMap _
      (isOpen_interior.preimage (continuous_subtype_val.comp continuous_subtype_val))
  · -- it contains `y`
    refine ⟨⟨⟨cy.val.val, hcU⟩, cy.property⟩, mem_interior_iff_mem_nhds.mpr hK₁n, ?_⟩
    exact hcy
  · -- coherence on `V`
    exact isLocallyFinitelyGeneratedOn_descendFamily eX' Hamb hfgH
  · -- proper at the base point
    rw [← hc₀', hHapply c₀']
    apply map_ne_top_of_surjective _ (baseChartLift_surjective eX' c₀')
    have h0 : translate O crit.U cc hOU c₀'.val = ⟨0, crit.zero_mem⟩ := by
      apply Subtype.ext
      change cc - cc = 0
      exact sub_self _
    rw [h0]
    exact crit.proper_zero
  · -- necessity
    rintro x ⟨c, rfl⟩ hHx J hflat
    rw [hle_iff c J]
    apply crit.necessary _ (hne_of c hHx)
    intro z hzK
    have hzW : z ∈ Wz := hK₁W hzK
    by_cases hk : ∃ k, (translate O crit.U cc hOU c.val).val k + cc k - ψ z k ≠ 0
    · obtain ⟨k, hk⟩ := hk
      exact flat_of_idealAt_eq_top ψ cc g _ (htopG z hzW _ k hk) _
    · have hφz : ψ z = c.val.val := by
        have htv : (translate O crit.U cc hOU c.val).val + cc = c.val.val := sub_add_cancel _ _
        rw [← htv]
        ext k
        have hk' : (translate O crit.U cc hOU c.val).val k + cc k - ψ z k = 0 :=
          not_not.mp (fun h => hk ⟨k, h⟩)
        simp only [PiLp.add_apply]
        linear_combination -hk'
      by_cases hzC : (⟨z, hWU hzW⟩ : U) ∈ e.carrier
      · let zC : e.carrier := ⟨⟨z, hWU hzW⟩, hzC⟩
        have hφzC : (φ zC.val).val = c.val.val := (hψ z (hWU hzW)).symm.trans hφz
        obtain ⟨z', h, -, hdict⟩ := hgraphPt c zC hzW hφzC
        exact (hdict J).mp (hflat _ h)
      · exact flat_of_idealAt_eq_top ψ cc g _ (htopC ⟨z, hWU hzW⟩ hzW hzC _) _
  · -- sufficiency on the source window
    rintro x ⟨c, rfl⟩ hHx J hle y' h ⟨zC, hzK, rfl⟩
    have hzW : zC.val.val ∈ Wz := hK₁W (interior_subset hzK)
    -- the base point of `zC` is `c`
    have hb := square_base f eX eY hUV hφ hCD hsq zC
    have hasm : (actualSubspaceMap hφ hCD).base zC = ⟨Opens.inclusion hO c.val, c.property⟩ :=
      eX.toPoint_injective (hb.trans h)
    have hφz : (φ zC.val).val = c.val.val := congrArg (fun a : eX.carrier => a.val.val) hasm
    obtain ⟨z', h', hz', hdict⟩ := hgraphPt c zC hzW hφz
    have hflat := (hdict J).mpr (crit.sufficient _ (hne_of c hHx) _ ((hle_iff c J).mp hle) _ hzK)
    -- transport along the equal source points
    have hpt : e'.toPoint z' = e.toPoint zC := hz'
    revert h
    rw [← hpt]
    intro h
    exact hflat

/-- **The persistent local flattener (Hironaka 1975 Th. 2.4 with `S = {x}`; Frisch 1968 Lemme 5).**
For every proper morphism of reduced complex spaces and every point of the base there is a local
flattener whose support contains the point. -/
theorem persistentLocalFlattener : PersistentLocalFlattener := by
  classical
  intro X Y f hf x₀
  let Fb := {y : Y.obj.left // f.hom.left.base y = x₀}
  choose V hV hxV W hW hyW H hfg hprop hnec hsuf using
    fun y : Fb => exists_native_window f y.val
  have hcomp : IsCompact (f.hom.left.base ⁻¹' {x₀}) := hf.isCompact_preimage isCompact_singleton
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun y : Fb => W y) (fun y => hW y) (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hyW ⟨y, hy⟩⟩)
  let V' : Set X.obj.left := ⋂ i ∈ t, V i
  have hV' : IsOpen V' := isOpen_biInter_finset fun i _ => hV i
  have hxV' : x₀ ∈ V' := by
    refine mem_iInter₂.mpr fun i _ => ?_
    have := hxV i
    rwa [i.property] at this
  have hV'i : ∀ i ∈ t, V' ⊆ V i := fun i hi x hx => mem_iInter₂.mp hx i hi
  obtain ⟨Z, hZ, -⟩ := exists_localFlattener_of_asymmetric_windows f hf x₀ (ι := t) V' hV' hxV'
    (fun i => W i.val) (fun i => hW i.val)
    (by
      intro y hy
      have hy' := ht hy
      rw [mem_iUnion₂] at hy'
      obtain ⟨i, hi, hyi⟩ := hy'
      exact ⟨⟨i, hi⟩, hyi⟩)
    (fun i => H i.val) (fun i => (hfg i.val).mono (hV'i i.val i.property))
    (fun i => by
      have := hprop i.val
      rwa [i.val.property] at this)
    (fun i x hx hne J hJ => hnec i.val x (hV'i i.val i.property hx) hne J hJ)
    (fun i x hx hne J hJ y' h hy' => hsuf i.val x (hV'i i.val i.property hx) hne J hJ y' h hy')
  exact ⟨Z, hZ⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow
