import DeJongAlterations.StableModification.Global.StableOpenReduce
import DeJongAlterations.StableModification.BlowDown.ClosureComponent

/-! Whole ORIGINAL constant-map and literal residue-fibre factors used by actual stable-openness. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenOriginalPointFactors

open StableModification BlowDown.ClosureComponent Global

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reduced original source + native kernel ideals internally produce the WHOLE original point factor. -/
theorem exists_whole_rational_point_factor {K : Type u} [Field K] [IsAlgClosed K]
    {N Y : Scheme.{u}} [IsIntegral N] (p : N ⟶ Spec (.of K)) [IsProper p]
    (q : Y ⟶ Spec (.of K)) [IsSeparated q] [LocallyOfFiniteType q]
    (b : N ⟶ Y) (sq : b ≫ q = p) (hsub : (Set.range b).Subsingleton) :
    ∃ (y : Y) (_ : IsClosed ({y} : Set Y)) (σ : Spec (.of K) ⟶ Y),
      σ ≫ q = 𝟙 _ ∧ σ (IsLocalRing.closedPoint K) = y ∧
      Set.range b = {y} ∧ p ≫ σ = b := by
  let : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace p
  have : JacobsonSpace N := LocallyOfFiniteType.jacobsonSpace p
  have : IsProper (b ≫ q) := sq.symm ▸ inferInstance
  have : IsProper b := IsProper.of_comp b q
  obtain ⟨x, _, hxc⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty : (Set.univ : Set N).Nonempty)
  let y := b x
  have hyc : IsClosed ({y} : Set Y) := Curves.isClosed_image_of_isClosed b sq hxc
  let j := Y.fromSpecResidueField y
  have : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hyc
  have he : Set.range b = {y} := by
    ext z
    constructor
    · exact fun hz => hsub hz ⟨x, rfl⟩
    · rintro rfl
      exact ⟨x, rfl⟩
  have hker : j.ker = b.ker := ker_eq_of_range_eq j b (by rw [Scheme.range_fromSpecResidueField, he])
  let l := IsClosedImmersion.lift j b hker.le
  have hl : l ≫ j = b := IsClosedImmersion.lift_fac _ _ _
  have : IsIso (j ≫ q) := by
    rw [← SpecMap_residueFieldIsoBase_inv q y hyc]
    infer_instance
  let e := asIso (j ≫ q)
  let σ := e.inv ≫ j
  have hσ : σ ≫ q = 𝟙 _ := by
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  refine ⟨y, hyc, σ, hσ, ?_, he, ?_⟩
  · change Y.fromSpecResidueField y (e.inv (IsLocalRing.closedPoint K)) = y
    exact Scheme.fromSpecResidueField_apply _ _
  · have hcoeff : l ≫ e.hom = p := by
      change l ≫ (j ≫ q) = p
      rw [← Category.assoc, hl, sq]
    dsimp only [σ]
    rw [← hcoeff, Category.assoc, Iso.hom_inv_id_assoc, hl]

private theorem noContractedClopen_comp_iso {X C S : Scheme.{u}}
    (β : X ⟶ C) (q : C ⟶ S) {K K' : Type u} [Field K] [Field K']
    (a : Spec (.of K) ⟶ S) (e : Spec (.of K') ⟶ Spec (.of K)) [IsIso e]
    (hno : NoContractedClopen β q a) : NoContractedClopen β q (e ≫ a) := by
  let πX : pullback (β ≫ q) (e ≫ a) ⟶ pullback (β ≫ q) a :=
    pullback.map _ _ _ _ (𝟙 _) e (𝟙 _) (by simp) (by simp)
  let πC : pullback q (e ≫ a) ⟶ pullback q a :=
    pullback.map _ _ _ _ (𝟙 _) e (𝟙 _) (by simp) (by simp)
  have : IsIso πX := by dsimp [πX]; infer_instance
  have hmap : πX ≫ Curves.pullbackCompMap β q a =
      Curves.pullbackCompMap β q (e ≫ a) ≫ πC := by
    apply pullback.hom_ext <;> simp [πX, πC, Curves.pullbackCompMap]
  intro Z hZ hne hsub
  apply hno (πX '' Z)
  · exact ⟨πX.homeomorph.isClosedMap _ hZ.1, πX.homeomorph.isOpenMap _ hZ.2⟩
  · exact hne.image _
  · rw [Set.image_image]
    have heq : (fun z => Curves.pullbackCompMap β q a (πX z)) =
        (fun z => πC (Curves.pullbackCompMap β q (e ≫ a) z)) := by
      funext z
      exact congrArg (fun h => h z) hmap
    rw [heq, ← Set.image_image]
    exact hsub.image _

/-- Original rational no-contraction internally transfers to the LITERAL native κ(y) fibre. -/
theorem noContractedClopen_residue_of_rational {K : Type u} [Field K] [IsAlgClosed K]
    {X C V : Scheme.{u}} (pV : V ⟶ Spec (.of K)) [LocallyOfFiniteType pV]
    (β : X ⟶ C) (q : C ⟶ V) [LocallyOfFiniteType q]
    (a : Spec (.of K) ⟶ V) (ha : a ≫ pV = 𝟙 _)
    (hno : NoContractedClopen β q a) (y : C) (hy : IsClosed ({y} : Set C))
    (hya : q y = a (IsLocalRing.closedPoint K)) :
    NoContractedClopen β q (C.fromSpecResidueField y ≫ q) := by
  let t := C.fromSpecResidueField y ≫ q
  let e := C.fromSpecResidueField y ≫ q ≫ pV
  have : IsIso e := by
    change IsIso (C.fromSpecResidueField y ≫ q ≫ pV)
    rw [← SpecMap_residueFieldIsoBase_inv (q ≫ pV) y hy]
    infer_instance
  let b := (asIso e).inv ≫ t
  have hb : b ≫ pV = 𝟙 _ := by
    change (asIso e).inv ≫ e = 𝟙 _
    exact Iso.inv_hom_id _
  have hba : b = a := ext_of_apply_closedPoint_eq pV hb ha (by
    change q (C.fromSpecResidueField y ((asIso e).inv (IsLocalRing.closedPoint K))) = _
    rw [Scheme.fromSpecResidueField_apply]
    exact hya)
  have ht : t = e ≫ a := by
    rw [← hba]
    change t = (asIso e).hom ≫ (asIso e).inv ≫ t
    rw [Iso.hom_inv_id_assoc]
  change NoContractedClopen β q t
  rw [ht]
  exact noContractedClopen_comp_iso β q a e hno

end DeJongAlterations.StableModificationBridge.StableOpenOriginalPointFactors
