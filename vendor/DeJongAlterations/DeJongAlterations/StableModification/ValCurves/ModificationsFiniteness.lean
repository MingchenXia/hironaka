import DeJongAlterations.StableModification.ValCurves.ModificationsUnique

/-!
# Finiteness of `(C/S)⁰`, `Γ(C')` and `Γ₀(C')` (Temkin, Lemma 4.2.2, second assertion)

Let `S` be a scheme with finitely many points (e.g. the spectrum of a valuation ring of finite
height) and `g : X → S` quasi-compact and locally of finite type with all residue field
extensions of transcendence degree at most one. Then `(X/S)⁰` is finite
(`finite_fibreGenericSet`): its points in a fibre `X_s` have no proper generization in `X_s`
(`one_add_fiberTrdeg_le_of_specializes`, the strict dimension inequality, proved with
Abhyankar's inequality for a valuation ring of `κ(y)` dominating `𝒪_{X,x}` for a proper
specialization `y ⤳ x` in the fibre), so they are generic points of irreducible components of
the Noetherian fibre. Consequently, for a normal modification `f : C' → C`, the sets `Γ(C')` and
`Γ₀(C')` are finite (`finite_gammaSet`, `finite_gammaZeroSet`; M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010), Lemma 4.2.2, `semi-stable.tex` lines 2909–2915:
"obviously the sets `Γ(C')` and `Γ₀(C')` are finite").
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology IsLocalRing

universe u

namespace DeJongAlterations.StableModification.ValCurves

open _root_.DeJongAlterations.StableModification.ValuationRing (fiberTrdeg
  exists_valuationSubring_dominates)

section Algebra

/-- The rational rank of a nontrivial valuation ring is at least one. -/
theorem one_le_ratRank {L : Type*} [Field L] (V : ValuationSubring L) {w : L} (hw0 : w ≠ 0)
    (hw : V.valuation w < 1) : 1 ≤ ratRank V := by
  let x : Fin 1 → Lˣ := fun _ ↦ Units.mk0 w hw0
  let U : Fin 2 → Subgroup Lˣ := ![V.unitGroup, ⊤]
  have hU : Monotone U := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · exact le_top
    · exact absurd hij (by decide)
    · exact le_rfl
  have hsat : ∀ k (y : Lˣ) (m : ℤ), m ≠ 0 → y ^ m ∈ U k → y ∈ U k := by
    intro k y m hm hy
    fin_cases k
    · exact mem_unitGroup_of_zpow_mem V hm hy
    · trivial
  have hli := linearIndependent_mk_of_chain V.unitGroup U hU le_rfl hsat x
    (fun i ↦ by fin_cases i; trivial) (fun i ↦ by
      fin_cases i
      intro hmem
      have h1 := (ValuationSubring.mem_unitGroup_iff V _).mp hmem
      exact absurd h1 (ne_of_lt hw))
  have := hli.cardinal_lift_le_rank
  simpa [ratRank] using this

variable {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
  {R F : Type u} [CommRing R] [IsLocalRing R] [Field F] [Algebra K F]

/-- **The strict dimension inequality** (field form). Let `φ : A → R` be a local homomorphism of
local rings, `h : A → K` a surjection onto a field, `g : R → F` a homomorphism to a field over
`K` compatible with `h`, and suppose `g` does not kill the maximal ideal of `R`. Then
`1 + trdeg (κ(R)/κ(A)) ≤ trdeg (F/K)`: a valuation ring `W` of `F` dominating `R` is
nontrivial, contains `K`, and Abhyankar's inequality applies. -/
theorem one_add_trdeg_residueField_le (φ : A →+* R) [IsLocalHom φ] (h : A →+* K) (g : R →+* F)
    (hcomm : ∀ a, algebraMap K F (h a) = g (φ a)) (hsurj : Function.Surjective h)
    (hne : ∃ r ∈ maximalIdeal R, g r ≠ 0) :
    letI := (ResidueField.map φ).toAlgebra
    1 + Algebra.trdeg (ResidueField A) (ResidueField R) ≤ Algebra.trdeg K F := by
  let := (ResidueField.map φ).toAlgebra
  obtain ⟨W, hWle, hWlt⟩ := exists_valuationSubring_dominates g
  set v := W.valuation with hv
  set vK := v.comap (algebraMap K F) with hvK
  have hmemO₀ : ∀ y : K, y ∈ vK.valuationSubring ↔ v (algebraMap K F y) ≤ 1 := fun y ↦ by
    rw [Valuation.mem_valuationSubring_iff, hvK, Valuation.comap_apply]
  have hhO₀ : ∀ a, h a ∈ vK.valuationSubring := fun a ↦ by
    rw [hmemO₀, hcomm]
    exact hWle _
  have hgO : ∀ r, g r ∈ v.valuationSubring := fun r ↦ hWle r
  let h₀ : A →+* vK.valuationSubring := h.codRestrict _ hhO₀
  let g₀ : R →+* v.valuationSubring := g.codRestrict _ hgO
  have hunitO : ∀ (w : F) (hw : w ∈ v.valuationSubring),
      IsUnit (⟨w, hw⟩ : v.valuationSubring) ↔ v w = 1 := fun w hw ↦
    (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one
  have hunitO₀ : ∀ (y : K) (hy : y ∈ vK.valuationSubring),
      IsUnit (⟨y, hy⟩ : vK.valuationSubring) ↔ vK y = 1 := fun y hy ↦
    (Valuation.valuationSubring.integers vK).isUnit_iff_valuation_eq_one
  have hlocg : ∀ r, v (g r) = 1 → IsUnit r := by
    intro r hr
    by_contra hnu
    exact ((hWlt r).mpr ((mem_maximalIdeal r).mpr hnu)).ne hr
  have hloch : ∀ a, vK (h a) = 1 → IsUnit a := by
    intro a ha
    apply hlocg (φ a) _ |>.of_map
    rw [← hcomm]
    exact ha
  have : IsLocalHom g₀ := ⟨fun r hr ↦ hlocg r ((hunitO _ (hgO r)).mp hr)⟩
  have : IsLocalHom h₀ := ⟨fun a ha ↦ hloch a ((hunitO₀ _ (hhO₀ a)).mp ha)⟩
  let α : ResidueField A →+* ResidueField vK.valuationSubring := ResidueField.map h₀
  let β : ResidueField R →+* ResidueField v.valuationSubring := ResidueField.map g₀
  have hαsurj : Function.Surjective α := by
    intro z
    obtain ⟨⟨y, hy⟩, rfl⟩ := residue_surjective z
    obtain ⟨a, rfl⟩ := hsurj y
    exact ⟨residue A a, rfl⟩
  have hcomm' : (algebraMap (ResidueField vK.valuationSubring)
      (ResidueField v.valuationSubring)).comp α = β.comp (algebraMap (ResidueField A)
        (ResidueField R)) := by
    ext z
    obtain ⟨a, rfl⟩ := residue_surjective z
    change residue _ (algebraMap vK.valuationSubring v.valuationSubring (h₀ a)) =
      residue _ (g₀ (φ a))
    congr 1
    exact Subtype.ext (hcomm a)
  -- the transcendence degree of the residue field extension
  have htr : Algebra.trdeg (ResidueField A) (ResidueField R) ≤
      Algebra.trdeg (ResidueField vK.valuationSubring) (ResidueField v.valuationSubring) :=
    ciSup_le' fun s ↦
      (s.2.ringHom_of_comp_eq α β hαsurj β.injective hcomm').cardinalMk_le_trdeg
  -- `K` lies in the valuation ring, and the valuation is nontrivial
  have hKW : ∀ y : K, algebraMap K F y ∈ v.valuationSubring := by
    intro y
    obtain ⟨a, rfl⟩ := hsurj y
    rw [hcomm]
    exact hgO (φ a)
  obtain ⟨r, hrm, hr0⟩ := hne
  have h1 : 1 ≤ ratRank v.valuationSubring := by
    refine one_le_ratRank _ hr0 ?_
    rw [ValuationSubring.valuationSubring_valuation]
    exact (hWlt r).mpr hrm
  have h2 := ratRank_le_relRatRank (K := K) v.valuationSubring hKW
  calc 1 + Algebra.trdeg (ResidueField A) (ResidueField R)
      ≤ relRatRank K v.valuationSubring +
          Algebra.trdeg (ResidueField vK.valuationSubring) (ResidueField v.valuationSubring) :=
        add_le_add (h1.trans h2) htr
    _ ≤ Algebra.trdeg K F := relRatRank_add_trdeg_le vK v

end Algebra

section Scheme

variable {X S : Scheme.{u}} (g : X ⟶ S)

/-- **The strict dimension inequality along specializations in a fibre.** If `y ⤳ x` is a proper
specialization of points of `X` lying over the same point of `S`, then
`1 + trdeg (κ(x)/κ(g x)) ≤ trdeg (κ(y)/κ(g y))`. -/
theorem one_add_fiberTrdeg_le_of_specializes {y x : X} (hxy : y ⤳ x) (hne : y ≠ x)
    (hfib : g y = g x) : 1 + fiberTrdeg g x ≤ fiberTrdeg g y := by
  have hfx : g y ⤳ g x := hxy.map g.continuous
  have hfx' : g x ⤳ g y := hfib ▸ specializes_rfl
  let := (g.residueFieldMap y).hom.toAlgebra
  let h : S.presheaf.stalk (g x) →+* S.residueField (g y) :=
    (S.residue (g y)).hom.comp (S.presheaf.stalkSpecializes hfx).hom
  let g' : X.presheaf.stalk x →+* X.residueField y :=
    (X.residue y).hom.comp (X.presheaf.stalkSpecializes hxy).hom
  have hcomm : ∀ a, algebraMap (S.residueField (g y)) (X.residueField y) (h a) =
      g' ((g.stalkMap x).hom a) := by
    intro a
    change (g.residueFieldMap y).hom ((S.residue (g y)).hom _) = _
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
    change (X.residue y).hom _ = (X.residue y).hom _
    congr 1
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply g y x hxy a
  have hsurj : Function.Surjective h := by
    intro b
    obtain ⟨c, rfl⟩ := S.residue_surjective (g y) b
    refine ⟨S.presheaf.stalkSpecializes hfx' c, ?_⟩
    change (S.residue (g y)).hom ((S.presheaf.stalkSpecializes hfx' ≫
      S.presheaf.stalkSpecializes hfx).hom c) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hne' : ∃ r ∈ maximalIdeal (X.presheaf.stalk x), g' r ≠ 0 := by
    by_contra H
    push Not at H
    refine hne (hxy.antisymm ?_).eq
    rw [specializes_iff_forall_open]
    intro O hO hyO
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
    have hyU : y ∈ U := hxy.mem_open U.isOpen hxU
    obtain ⟨a, haO, hya⟩ := hU.exists_basicOpen_le (V := ⟨O, hO⟩) ⟨y, hyO⟩ hyU
    refine haO ((X.mem_basicOpen a x hxU).mpr ?_)
    by_contra hnu
    have h0 := H _ ((mem_maximalIdeal _).mpr hnu)
    have hev : g' (X.presheaf.germ U x hxU a) = X.evaluation U y hyU a := by
      change (X.residue y).hom ((X.presheaf.germ U x hxU ≫
        X.presheaf.stalkSpecializes hxy).hom a) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [hev] at h0
    exact (X.evaluation_ne_zero_iff_mem_basicOpen y hyU a).mpr hya h0
  exact one_add_trdeg_residueField_le (g.stalkMap x).hom h g' hcomm hsurj hne'

/-- In a quasi-sober space a point without proper generizations is the generic point of an
irreducible component. -/
theorem closure_mem_irreducibleComponents {T : Type*} [TopologicalSpace T] [QuasiSober T]
    {p : T} (hp : ∀ q, q ⤳ p → q = p) : closure {p} ∈ irreducibleComponents T := by
  refine ⟨isIrreducible_singleton.closure, fun Z hZ hle ↦ ?_⟩
  obtain ⟨q, hq⟩ := QuasiSober.sober hZ.closure isClosed_closure
  have hpZ : p ∈ closure Z := subset_closure (hle (subset_closure rfl))
  have hqp : q ⤳ p := specializes_iff_mem_closure.mpr (hq.def ▸ hpZ)
  rw [hp q hqp] at hq
  exact subset_closure.trans hq.def.ge

/-- **The points of `(X/S)⁰` in a fibre are finitely many**: for `g` quasi-compact, locally of
finite type and of relative dimension at most one, `(X/S)⁰ ∩ X_s` is finite. -/
theorem finite_fibreGenericSet_inter_preimage [QuasiCompact g] [LocallyOfFiniteType g]
    (hdim : ∀ x, fiberTrdeg g x ≤ 1) (s : S) : (fibreGenericSet g ∩ g ⁻¹' {s}).Finite := by
  have : IsLocallyNoetherian (g.fiber s) := inferInstanceAs (IsLocallyNoetherian (pullback _ _))
  have : IsNoetherian (g.fiber s) := {}
  let e := g.fiberHomeo s
  have : TopologicalSpace.NoetherianSpace (g ⁻¹' {s}) :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph e).mp inferInstance
  have : QuasiSober (g ⁻¹' {s}) := e.symm.isClosedEmbedding.quasiSober
  have hfinC := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := g ⁻¹' {s})
  -- the points of `(X/S)⁰` over `s` are maximal in the fibre
  have hmax : ∀ x (hx : x ∈ fibreGenericSet g ∩ g ⁻¹' {s}) (q : g ⁻¹' {s}),
      q ⤳ ⟨x, hx.2⟩ → q = ⟨x, hx.2⟩ := by
    intro x hx q hq
    have hq' : q.1 ⤳ x := (IsInducing.subtypeVal.specializes_iff).mpr hq
    by_contra hne
    have hne' : q.1 ≠ x := fun h ↦ hne (Subtype.ext h)
    have hfib : g q.1 = g x := q.2.trans hx.2.symm
    have h := (one_add_fiberTrdeg_le_of_specializes g hq' hne' hfib).trans (hdim q.1)
    rw [hx.1, one_add_one_eq_two] at h
    exact absurd h (by norm_num)
  let ψ : (fibreGenericSet g ∩ g ⁻¹' {s} : Set X) → irreducibleComponents (g ⁻¹' {s}) :=
    fun x ↦ ⟨closure {⟨x.1, x.2.2⟩}, closure_mem_irreducibleComponents (hmax x.1 x.2)⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : closure ({⟨x.1, x.2.2⟩} : Set (g ⁻¹' {s})) = closure {⟨y.1, y.2.2⟩} :=
      congrArg Subtype.val hxy
    have h2 : Inseparable (⟨x.1, x.2.2⟩ : g ⁻¹' {s}) ⟨y.1, y.2.2⟩ :=
      inseparable_iff_closure_eq.mpr h1
    exact Subtype.ext (congrArg (fun q : g ⁻¹' {s} ↦ q.1) h2.eq)
  have : Finite (irreducibleComponents (g ⁻¹' {s})) := hfinC.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_injective ψ hψ)

/-- **`(X/S)⁰` is finite** over a base with finitely many points. -/
theorem finite_fibreGenericSet [Finite S] [QuasiCompact g] [LocallyOfFiniteType g]
    (hdim : ∀ x, fiberTrdeg g x ≤ 1) : (fibreGenericSet g).Finite := by
  refine (Set.finite_iUnion fun s ↦
    finite_fibreGenericSet_inter_preimage g hdim s).subset fun x hx ↦ ?_
  exact Set.mem_iUnion.mpr ⟨g x, hx, rfl⟩

end Scheme

section Gamma

variable {S C C' : Scheme.{u}} [∀ s : S, PreValuationRing (S.presheaf.stalk s)] (φ : C ⟶ S)
  [IsIntegral C] [C.IsSeparated] [IsIntegral C'] (f : C' ⟶ C) [IsModification f]

/-- **Temkin, Lemma 4.2.2, second assertion**: for a normal modification `f : C' → C` of a
quasi-compact relative curve over a base with finitely many points, `Γ(C')` is finite. -/
theorem finite_gammaSet [Finite S] [QuasiCompact φ] [LocallyOfFiniteType φ]
    (hnormal : IsNormalScheme C') (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) :
    (gammaSet (f ≫ φ) (genericLift f)).Finite := by
  obtain ⟨e, -⟩ := exists_gammaEquiv φ f hnormal hdim
  have : Finite (fibreGenericSet (f ≫ φ)) :=
    (finite_fibreGenericSet (f ≫ φ) (fiberTrdeg_le_one φ hdim f)).to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ e.symm)

/-- **Temkin, Lemma 4.2.2, second assertion**: `Γ₀(C')` is finite. -/
theorem finite_gammaZeroSet [Finite S] [QuasiCompact φ] [LocallyOfFiniteType φ]
    (hnormal : IsNormalScheme C') (hdim : fiberTrdeg φ (genericPoint C) ≤ 1) :
    (gammaZeroSet (f ≫ φ) (genericLift f) (genericPt C)).Finite :=
  (finite_gammaSet φ f hnormal hdim).subset (gammaZeroSet_subset _ _ _)

end Gamma

end DeJongAlterations.StableModification.ValCurves
