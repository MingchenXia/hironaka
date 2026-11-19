import Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup
import Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
import Hironaka.Analytic.Unibranch.HironakaG11ModificationCalculus
import Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion

/-!
# Finite disjoint unions of modifications

A finite composition of smooth-centre blowups of an open and closed piece of a reduced complex
space extends to the whole space, leaving the rest unchanged; hence finitely many modifications of
pairwise disjoint open and closed pieces assemble to one modification of the whole space
(blueprint `hironaka-g10-gen-chow-general.tex`).  This is how modifications of the
connected components of a smooth compact space (complex manifolds of possibly different
dimensions) become one modification.

The construction blows up the image of each centre in the whole space (the native smooth-centre
blowup exists for every smooth centre, `OriginalSmoothCentreBlowup.exists_smoothCentreBlowup`), and
compares it with the given blowup of the piece by locality of blowups
(`HironakaG11BlowupLocality.exists_openImmersion_of_isSmoothCentreBlowup_of_trace`).

Main declarations:

* `IsIsoOver.exists_lift` — morphisms with image in the isomorphism locus lift;
* `exists_step_extension`, `exists_modification_extension` — extension of a smooth-centre step,
  resp. a finite modification, of an open and closed piece;
* `exists_isModification_fin`, `exists_isModification_of_cover` — finite disjoint unions.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10GenDisjointModification

open SourceReducedComplexSpace SmoothCentreModification HironakaG10ChowNativeIsoCriterion

noncomputable section

private theorem openImmersion_lift' {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  let : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

theorem hom_ext_left {A B : SourceReducedComplexSpace} {f g : A ⟶ B}
    (h : f.hom.left = g.hom.left) : f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact h

theorem comp_base_apply {A B C : SourceReducedComplexSpace} (f : A ⟶ B) (g : B ⟶ C)
    (a : A.obj.left) : (f ≫ g).hom.left.base a = g.hom.left.base (f.hom.left.base a) := rfl

/-- **Lifting through an isomorphism over `U`.**  A morphism with image in `U` lifts through a
morphism which is an isomorphism over `U`; the lift of an open immersion is an open immersion,
with range the preimage of the range. -/
theorem IsIsoOver.exists_lift {Z Z' T : SourceReducedComplexSpace} {ρ : Z' ⟶ Z}
    {U : Set Z.obj.left} (hρ : IsIsoOver ρ U) (F : T ⟶ Z)
    (hF : range F.hom.left.base ⊆ U) :
    ∃ F' : T ⟶ Z', F' ≫ ρ = F ∧
      (LocallyRingedSpace.IsOpenImmersion F.hom.left →
        LocallyRingedSpace.IsOpenImmersion F'.hom.left) ∧
      range F'.hom.left.base = ρ.hom.left.base ⁻¹' range F.hom.left.base := by
  obtain ⟨V, k, hk, hkr, hkρ, hkρr⟩ := hρ
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  let : LocallyRingedSpace.IsOpenImmersion (k ≫ ρ.hom.left) := hkρ
  have hr : range F.hom.left.base ⊆ range (k ≫ ρ.hom.left).base := by
    rw [hkρr]
    exact hF
  let l := LocallyRingedSpace.IsOpenImmersion.lift (k ≫ ρ.hom.left) F.hom.left hr
  have hl : l ≫ k ≫ ρ.hom.left = F.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac (k ≫ ρ.hom.left) F.hom.left hr
  have hw : (l ≫ k) ≫ Z'.obj.hom = T.obj.hom := by
    rw [← Over.w ρ.hom, ← Over.w F.hom, ← hl]
    simp only [Category.assoc]
  let F' : T ⟶ Z' := ObjectProperty.homMk (Over.homMk (l ≫ k) hw)
  have hF'ρ : F' ≫ ρ = F := hom_ext_left (by
    change (l ≫ k) ≫ ρ.hom.left = F.hom.left
    rw [Category.assoc]
    exact hl)
  refine ⟨F', hF'ρ, ?_, ?_⟩
  · intro hFo
    let : LocallyRingedSpace.IsOpenImmersion F.hom.left := hFo
    let : LocallyRingedSpace.IsOpenImmersion l := openImmersion_lift' _ _ hr
    change LocallyRingedSpace.IsOpenImmersion (l ≫ k)
    infer_instance
  · ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨t, ?_⟩
      exact (congrArg (fun H : T ⟶ Z => H.hom.left.base t) hF'ρ).symm
    · rintro ⟨t, ht⟩
      have hz : z ∈ range k.base := by
        rw [hkr]
        change ρ.hom.left.base z ∈ U
        rw [← ht]
        exact hF ⟨t, rfl⟩
      obtain ⟨v, rfl⟩ := hz
      refine ⟨t, ?_⟩
      have h1 : ρ.hom.left.base (F'.hom.left.base t) = F.hom.left.base t :=
        congrArg (fun H : T ⟶ Z => H.hom.left.base t) hF'ρ
      have h2 : F'.hom.left.base t ∈ range k.base := ⟨l.base t, rfl⟩
      obtain ⟨w, hw⟩ := h2
      rw [← hw]
      congr 1
      apply hkρ.base_open.injective
      change ρ.hom.left.base (k.base w) = ρ.hom.left.base (k.base v)
      rw [hw, h1, ht]

/-! ### Extension of one smooth-centre step -/

theorem isClosedEmbedding_of_isOpenImmersion {Z₀ Z : SourceReducedComplexSpace} (j : Z₀ ⟶ Z)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hjc : IsClosed (range j.hom.left.base)) :
    Topology.IsClosedEmbedding j.hom.left.base :=
  ⟨hj.base_open.isEmbedding, hjc⟩

/-- **Extension of a smooth-centre step of an open and closed piece.**  If `j : Z₀ ⟶ Z` is an
open immersion with closed range and `p₀ : Z₀' ⟶ Z₀` a smooth-centre blowup step, the blowup
`p : Z' ⟶ Z` of the image of its centre is a smooth-centre step, `p₀` is its restriction over
`Z₀` (an open immersion `j' : Z₀' ⟶ Z'` onto `p⁻¹ (range j)` with `j' ≫ p = p₀ ≫ j`), and `p`
is an isomorphism over the complement of `range j`. -/
theorem exists_step_extension {Z Z₀ Z₀' : SourceReducedComplexSpace} (j : Z₀ ⟶ Z)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (hjc : IsClosed (range j.hom.left.base))
    {p₀ : Z₀' ⟶ Z₀} (hp₀ : IsSmoothCentreStep p₀) :
    ∃ (Z' : SourceReducedComplexSpace) (p : Z' ⟶ Z) (j' : Z₀' ⟶ Z'),
      IsSmoothCentreStep p ∧ LocallyRingedSpace.IsOpenImmersion j'.hom.left ∧
      j' ≫ p = p₀ ≫ j ∧ range j'.hom.left.base = p.hom.left.base ⁻¹' range j.hom.left.base ∧
      IsIsoOver p (range j.hom.left.base)ᶜ := by
  obtain ⟨S, i₀, hblow⟩ := hp₀
  have hblow₀ : IsSmoothCentreBlowup p₀ i₀ := hblow
  obtain ⟨hS, hi₀, hst, hCa, hthin, -, -⟩ := hblow
  let i : S ⟶ Z := i₀ ≫ j
  have hjinj : Function.Injective j.hom.left.base := hj.base_open.injective
  have hrange : range i.hom.left.base = j.hom.left.base '' range i₀.hom.left.base := by
    rw [← range_comp]
    rfl
  have htrace : range i₀.hom.left.base = j.hom.left.base ⁻¹' range i.hom.left.base := by
    rw [hrange, preimage_image_eq _ hjinj]
  have hi : Topology.IsClosedEmbedding i.hom.left.base :=
    (isClosedEmbedding_of_isOpenImmersion j hj hjc).comp hi₀
  have hstalk : ∀ s : S.obj.left, Function.Surjective (i.hom.left.stalkMap s) := by
    intro s
    change Function.Surjective ((i₀.hom.left ≫ j.hom.left).stalkMap s)
    rw [LocallyRingedSpace.stalkMap_comp]
    let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
    have hjs : Function.Surjective (j.hom.left.stalkMap (i₀.hom.left.base s)) :=
      (ConcreteCategory.bijective_of_isIso (j.hom.left.stalkMap (i₀.hom.left.base s))).2
    intro r
    obtain ⟨t, rfl⟩ := hst s r
    obtain ⟨u, rfl⟩ := hjs t
    exact ⟨u, rfl⟩
  have hC : Z.IsAnalyticSubset (range i.hom.left.base) := by
    apply HironakaG11CompatibleAnalyticCover.isAnalyticSubset_of_isClosed_of_openImmersion
      (ι := PUnit.{1}) (fun _ => j) (fun _ => hj) _ hi.isClosed_range
    · rintro x ⟨s, rfl⟩
      exact ⟨PUnit.unit.{1}, i₀.hom.left.base s, rfl⟩
    · intro _
      rw [← htrace]
      exact hCa
  have hthin' : interior (range i.hom.left.base) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxj : x ∈ range i.hom.left.base := interior_subset hx
    rw [hrange] at hxj
    obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hxj
    have hopen : IsOpen (j.hom.left.base ⁻¹' interior (range i.hom.left.base)) :=
      isOpen_interior.preimage j.hom.left.base.hom.continuous
    have hsub : j.hom.left.base ⁻¹' interior (range i.hom.left.base) ⊆ range i₀.hom.left.base := by
      intro z hz
      rw [htrace]
      exact (interior_subset (s := range i.hom.left.base)) hz
    have hmem := interior_maximal hsub hopen hx
    rw [hthin] at hmem
    exact hmem
  obtain ⟨Z', p, hp, -, -, hiso⟩ :=
    OriginalSmoothCentreBlowup.exists_smoothCentreBlowup Z S i hS hi hstalk hC hthin'
  obtain ⟨L, ⟨hL, -⟩, hLo, hLr⟩ :=
    HironakaG11BlowupLocality.exists_openImmersion_of_isSmoothCentreBlowup_of_trace hp hj hblow₀
      htrace
  refine ⟨Z', p, L, ⟨S, i, hp⟩, hLo, hL, hLr, ?_⟩
  apply hiso.of_isOpen_subset hjc.isOpen_compl
  apply compl_subset_compl.mpr
  rw [hrange]
  exact image_subset_range _ _

/-- **Extension of a finite modification of an open and closed piece.** -/
theorem exists_modification_extension {Z₀ A₀ : SourceReducedComplexSpace} {ρ₀ : A₀ ⟶ Z₀}
    (hρ₀ : IsModification ρ₀) : ∀ {Z : SourceReducedComplexSpace} (j : Z₀ ⟶ Z),
      LocallyRingedSpace.IsOpenImmersion j.hom.left → IsClosed (range j.hom.left.base) →
      ∃ (A : SourceReducedComplexSpace) (ρ : A ⟶ Z) (j' : A₀ ⟶ A),
        IsModification ρ ∧ LocallyRingedSpace.IsOpenImmersion j'.hom.left ∧ j' ≫ ρ = ρ₀ ≫ j ∧
        range j'.hom.left.base = ρ.hom.left.base ⁻¹' range j.hom.left.base ∧
        IsIsoOver ρ (range j.hom.left.base)ᶜ := by
  induction hρ₀ with
  | id =>
    intro Z j hj hjc
    refine ⟨Z, 𝟙 Z, j, .id Z, hj, by rw [Category.comp_id, Category.id_comp], ?_,
      IsIsoOver.id_of_isOpen Z hjc.isOpen_compl⟩
    rfl
  | cons f g hf _ ih =>
    intro Z j hj hjc
    obtain ⟨B, ρg, jg, hρg, hjg, hcomm, hrange, hiso⟩ := ih j hj hjc
    have hjgc : IsClosed (range jg.hom.left.base) := by
      rw [hrange]
      exact hjc.preimage ρg.hom.left.base.hom.continuous
    obtain ⟨A, p, j', hp, hj', hcomm', hrange', hiso'⟩ := exists_step_extension jg hjg hjgc hf
    refine ⟨A, p ≫ ρg, j', .cons p ρg hp hρg, hj', ?_, ?_, ?_⟩
    · rw [← Category.assoc, hcomm', Category.assoc, hcomm, Category.assoc]
    · rw [hrange', hrange]
      rfl
    · apply hiso.comp
      have h : ρg.hom.left.base ⁻¹' (range j.hom.left.base)ᶜ = (range jg.hom.left.base)ᶜ := by
        rw [hrange, preimage_compl]
      rw [h]
      exact hiso'

/-! ### Finite disjoint unions -/

/-- **Finite disjoint unions of modifications**, with the bookkeeping needed for the induction:
for modifications `ρ i : A i ⟶ Z₀ i` of finitely many pairwise disjoint open and closed pieces
`j i : Z₀ i ⟶ Z` there are a modification `ρ' : Z' ⟶ Z` and open immersions `L i : A i ⟶ Z'`
with `L i ≫ ρ' = ρ i ≫ j i`, such that `ρ'` is an isomorphism off the pieces and every point of
`Z'` lies in some `range (L i)` or over the complement of the pieces. -/
theorem exists_isModification_fin : ∀ (N : ℕ) {Z : SourceReducedComplexSpace}
    {Z₀ A : Fin N → SourceReducedComplexSpace} (j : ∀ i, Z₀ i ⟶ Z),
    (∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left) →
    (∀ i, IsClosed (range (j i).hom.left.base)) →
    Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)) →
    ∀ (ρ : ∀ i, A i ⟶ Z₀ i), (∀ i, IsModification (ρ i)) →
    ∃ (Z' : SourceReducedComplexSpace) (ρ' : Z' ⟶ Z) (L : ∀ i, A i ⟶ Z'),
      IsModification ρ' ∧ (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left) ∧
      (∀ i, L i ≫ ρ' = ρ i ≫ j i) ∧
      IsIsoOver ρ' (⋃ i, range (j i).hom.left.base)ᶜ ∧
      ∀ z', (∃ i, z' ∈ range (L i).hom.left.base) ∨
        ρ'.hom.left.base z' ∉ ⋃ i, range (j i).hom.left.base
  | 0, Z, Z₀, A, j, _, _, _, ρ, _ => by
    refine ⟨Z, 𝟙 Z, fun i => Fin.elim0 i, .id Z, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      ?_, fun z' => Or.inr ?_⟩
    · exact IsIsoOver.id_of_isOpen Z (by simp)
    · simp
  | N + 1, Z, Z₀, A, j, hj, hjc, hdisj, ρ, hρ => by
    obtain ⟨Z', ρ', L, hρ', hL, hLc, hiso, hcov⟩ := exists_isModification_fin N
      (fun i => j i.castSucc) (fun i => hj _) (fun i => hjc _)
      (fun i k hik => hdisj (fun h => hik (Fin.castSucc_injective _ h)))
      (fun i => ρ i.castSucc) (fun i => hρ _)
    set k : Fin (N + 1) := Fin.last N with hkdef
    set U : Set Z.obj.left := ⋃ i : Fin N, range (j i.castSucc).hom.left.base with hU
    have hkU : range (j k).hom.left.base ⊆ Uᶜ := by
      intro x hx hxU
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      exact Set.disjoint_left.mp (hdisj (Fin.castSucc_lt_last i).ne) hi hx
    obtain ⟨J, hJ, hJo, hJr⟩ := IsIsoOver.exists_lift hiso (j k) hkU
    have hJo' := hJo (hj k)
    have hJc : IsClosed (range J.hom.left.base) := by
      rw [hJr]
      exact (hjc k).preimage ρ'.hom.left.base.hom.continuous
    obtain ⟨Z'', ρ'', Lk, hρ'', hLko, hLkc, hLkr, hiso''⟩ :=
      exists_modification_extension (hρ k) J hJo' hJc
    -- the earlier pieces avoid `range J`
    have hLJ : ∀ i : Fin N, range (L i).hom.left.base ⊆ (range J.hom.left.base)ᶜ := by
      rintro i _ ⟨a, rfl⟩ hmem
      rw [hJr] at hmem
      have h1 : ρ'.hom.left.base ((L i).hom.left.base a) ∈
          range (j i.castSucc).hom.left.base := by
        rw [← comp_base_apply, hLc i]
        exact ⟨_, rfl⟩
      exact Set.disjoint_left.mp (hdisj (Fin.castSucc_lt_last i).ne) h1 hmem
    choose L' hL'c hL'o hL'r using fun i : Fin N => IsIsoOver.exists_lift hiso'' (L i) (hLJ i)
    let Lnew : ∀ i : Fin (N + 1), A i ⟶ Z'' := Fin.lastCases Lk (fun i => L' i)
    have hLnew_last : Lnew (Fin.last N) = Lk := Fin.lastCases_last
    have hLnew_cast (i : Fin N) : Lnew i.castSucc = L' i := Fin.lastCases_castSucc i
    refine ⟨Z'', ρ'' ≫ ρ', Lnew, .comp hρ'' hρ', ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [hLnew_last]
        exact hLko
      · rw [hLnew_cast]
        exact hL'o i (hL i)
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [hLnew_last, ← Category.assoc, hLkc, Category.assoc, hJ]
      · rw [hLnew_cast, ← Category.assoc, hL'c i, hLc i]
    · have hVo : IsOpen (⋃ i : Fin (N + 1), range (j i).hom.left.base)ᶜ :=
        (isClosed_iUnion_of_finite hjc).isOpen_compl
      have hVU : (⋃ i : Fin (N + 1), range (j i).hom.left.base)ᶜ ⊆ Uᶜ := by
        apply compl_subset_compl.mpr
        intro x hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨i.castSucc, hi⟩
      apply (hiso.of_isOpen_subset hVo hVU).comp
      apply hiso''.of_isOpen_subset (hVo.preimage ρ'.hom.left.base.hom.continuous)
      intro z hz hzJ
      rw [hJr] at hzJ
      exact hz (mem_iUnion.mpr ⟨k, hzJ⟩)
    · intro z''
      by_cases hz : z'' ∈ range Lk.hom.left.base
      · exact Or.inl ⟨Fin.last N, by rw [hLnew_last]; exact hz⟩
      · have hzJ : ρ''.hom.left.base z'' ∉ range J.hom.left.base := by
          intro h
          apply hz
          rw [hLkr]
          exact h
        have hzk : ρ'.hom.left.base (ρ''.hom.left.base z'') ∉ range (j k).hom.left.base := by
          intro h
          apply hzJ
          rw [hJr]
          exact h
        rcases hcov (ρ''.hom.left.base z'') with ⟨i, a, ha⟩ | hout
        · refine Or.inl ⟨i.castSucc, ?_⟩
          rw [hLnew_cast]
          refine ⟨a, ?_⟩
          have h1 : ρ''.hom.left.base ((L' i).hom.left.base a) = (L i).hom.left.base a := by
            rw [← comp_base_apply, hL'c i]
          have hinj := injOn_of_isIsoOver hiso''
          apply hinj
          · change ρ''.hom.left.base ((L' i).hom.left.base a) ∈ (range J.hom.left.base)ᶜ
            rw [h1]
            exact hLJ i ⟨a, rfl⟩
          · exact hzJ
          · rw [h1, ha]
        · refine Or.inr ?_
          change ρ'.hom.left.base (ρ''.hom.left.base z'') ∉ _
          intro hmem
          obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
          revert hi
          refine Fin.lastCases ?_ (fun i => ?_) i
          · exact hzk
          · intro hi
            exact hout (mem_iUnion.mpr ⟨i, hi⟩)

/-- **Finite disjoint unions of modifications.**  If finitely many pairwise disjoint open and
closed pieces `j i : Z₀ i ⟶ Z` cover `Z` and `ρ i : A i ⟶ Z₀ i` are finite compositions of
smooth-centre blowups, there are a finite composition of smooth-centre blowups `ρ' : Z' ⟶ Z` and
open immersions `L i : A i ⟶ Z'` covering `Z'` with `L i ≫ ρ' = ρ i ≫ j i`. -/
theorem exists_isModification_of_cover {N : ℕ} {Z : SourceReducedComplexSpace}
    {Z₀ A : Fin N → SourceReducedComplexSpace} (j : ∀ i, Z₀ i ⟶ Z)
    (hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hjc : ∀ i, IsClosed (range (j i).hom.left.base))
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)))
    (hcover : ∀ z, ∃ i, z ∈ range (j i).hom.left.base)
    (ρ : ∀ i, A i ⟶ Z₀ i) (hρ : ∀ i, IsModification (ρ i)) :
    ∃ (Z' : SourceReducedComplexSpace) (ρ' : Z' ⟶ Z) (L : ∀ i, A i ⟶ Z'),
      IsModification ρ' ∧ (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left) ∧
      (∀ i, L i ≫ ρ' = ρ i ≫ j i) ∧ ∀ z', ∃ i, z' ∈ range (L i).hom.left.base := by
  obtain ⟨Z', ρ', L, hρ', hL, hLc, -, hcov⟩ :=
    exists_isModification_fin N j hj hjc hdisj ρ hρ
  refine ⟨Z', ρ', L, hρ', hL, hLc, fun z' => ?_⟩
  rcases hcov z' with h | h
  · exact h
  · exact (h (mem_iUnion.mpr (hcover _))).elim

end

end Hironaka.Analytic.Unibranch.HironakaG10GenDisjointModification
