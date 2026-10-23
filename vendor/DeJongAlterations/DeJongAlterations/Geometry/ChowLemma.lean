import DeJongAlterations.Geometry.ProjectiveGraphModificationProperTarget
import DeJongAlterations.Geometry.ChowLemmaProduct
import DeJongAlterations.Geometry.ChowLemmaOpenLocus
import DeJongAlterations.Geometry.ChowLemmaAffineCover
import DeJongAlterations.Geometry.AffineQuasiProjective

/-!
# Genuine Chow modification for varieties

Every compactification of an affine patch is constructed internally. The
actual finite product and actual common-open graph closure give the proper
birational source. Its projection to the projective product is proved to
be an immersion by the internally proved complement-at-infinity equality.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.ChowLemma

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Actual Chow construction from a finite affine cover; no compactification or modification is supplied. -/
theorem exists_modification_of_finite_affine_cover
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p]
    {n : ℕ} (U : Fin n → X.affineOpens)
    (hU : ∀ i, ((U i).1 : Set X).Nonempty) (hcover : ⨆ i, (U i).1 = ⊤) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X),
      IsModification π ∧ IsVariety (π ≫ p) ∧ IsQuasiProjectiveOver (π ≫ p) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hcomp (i : Fin n) :
      ∃ (C : Scheme.{u}) (q : C ⟶ Spec (CommRingCat.of k)) (e : (U i).1.toScheme ⟶ C),
        IsVariety q ∧ IsProjectiveOver q ∧ IsOpenImmersion e ∧ IsDominant e ∧
          e ≫ q = (U i).1.ι ≫ p := by
    let : Nonempty (U i).1.toScheme := ⟨⟨(hU i).choose, (hU i).choose_spec⟩⟩
    let : IsVariety ((U i).1.ι ≫ p) := BoundaryRestriction.open_variety p (U i).1
    exact AffineQuasiProjective.exists_affine_variety_compactification ((U i).1.ι ≫ p)
  choose C q e hvar hproj heopen hedom hebase using hcomp
  let : ∀ i, IsOpenImmersion (e i) := heopen
  let : ∀ i, IsProper (q i) := fun i => (hproj i).isProper
  let A : Fin n → Over (Spec (CommRingCat.of k)) := fun i => Over.mk (q i)
  let P := ChowLemmaProduct.indexedProduct A
  have hP : IsProjectiveOver P.hom := ChowLemmaProduct.indexedProduct_isProjective A hproj
  let : IsProper P.hom := hP.isProper
  let L := List.ofFn U
  have hL : ∀ W ∈ L, (W.1 : Set X).Nonempty := by
    intro W hW
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW
    exact hU i
  let V := ChowLemmaAffineCover.commonOpen L
  let : Nonempty V.toScheme := ChowLemmaAffineCover.commonOpen_nonempty L hL
  have hVU (i : Fin n) : V ≤ (U i).1 := by
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_ofFn.mpr ⟨i, rfl⟩ : U i ∈ L)
    exact hj ▸ ChowLemmaAffineCover.commonOpen_le_get L j
  let a (i : Fin n) : V.toScheme ⟶ (U i).1.toScheme := X.homOfLE (hVU i)
  let Z : Over (Spec (CommRingCat.of k)) := Over.mk (V.ι ≫ p)
  let fC (i : Fin n) : Z ⟶ A i := Over.homMk (a i ≫ e i) (by
    change (a i ≫ e i) ≫ q i = V.ι ≫ p
    rw [Category.assoc, hebase, ← Category.assoc, Scheme.homOfLE_ι])
  let f : V.toScheme ⟶ P.left := (ChowLemmaProduct.indexedLift Z A fC).left
  have hf : f ≫ P.hom = V.ι ≫ p := (ChowLemmaProduct.indexedLift Z A fC).w
  let Y := ProjectiveGraphModification.ProperTarget.modification p P.hom V f hf
  let π : Y ⟶ X := ProjectiveGraphModification.ProperTarget.projection p P.hom V f hf
  let F : Y ⟶ P.left := ProjectiveGraphModification.ProperTarget.projectiveMap p P.hom V f hf
  let j : V.toScheme ⟶ Y := ProjectiveGraphModification.ProperTarget.inclusion p P.hom V f hf
  let : IsIntegral Y := ProjectiveGraphModification.ProperTarget.modification_isIntegral p P.hom V f hf
  have hbase : π ≫ p = F ≫ P.hom :=
    (ProjectiveGraphModification.ProperTarget.structure_triangle p P.hom V f hf).symm
  have hpair : pullback.lift π F hbase =
      ProjectiveGraphModification.ProperTarget.embedding p P.hom V f hf := by
    apply pullback.hom_ext <;> simp [π, F,
      ProjectiveGraphModification.ProperTarget.projection,
      ProjectiveGraphModification.ProperTarget.projectiveMap]
  let : IsImmersion (pullback.lift π F hbase) := by
    rw [hpair]
    infer_instance
  let r (i : Fin n) : P.left ⟶ C i := (ChowLemmaProduct.indexedProjection A i).left
  have hr (i : Fin n) : r i ≫ q i = P.hom :=
    (ChowLemmaProduct.indexedProjection A i).w
  let : IsImmersion F := ChowLemmaOpenLocus.isImmersion_of_dense_graph_open_cover
    p P.hom π F hbase C q r hr (fun i => (U i).1.toScheme)
    (fun i => (U i).1.ι) e (fun i => (hebase i).symm)
    (by simpa only [Scheme.Opens.opensRange_ι] using hcover) j a
    (fun i => by
      dsimp [j, π, a]
      rw [ProjectiveGraphModification.ProperTarget.inclusion_projection, Scheme.homOfLE_ι])
    (fun i => by
      change j ≫ F ≫ (ChowLemmaProduct.indexedProjection A i).left = a i ≫ e i
      rw [← Category.assoc, show j ≫ F = f from
        ProjectiveGraphModification.ProperTarget.inclusion_projectiveMap p P.hom V f hf]
      exact congrArg (fun m => m.left) (ChowLemmaProduct.indexedLift_projection Z A fC i))
  have hQP : IsQuasiProjectiveOver (π ≫ p) := by
    obtain ⟨d, b, hb, hbs⟩ := hP
    let := hb
    exact ⟨d, F ≫ b, inferInstance, by rw [Category.assoc, hbs, ← hbase]⟩
  exact ⟨Y, π, inferInstance, {}, hQP⟩

/-- Chow's lemma in the form required by de Jong 4.6, over the original field. -/
theorem exists_quasiProjective_modification
    (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X),
      IsModification π ∧ IsVariety (π ≫ p) ∧ IsQuasiProjectiveOver (π ≫ p) := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨L, hL, hcover⟩ := ChowLemmaAffineCover.exists_finite_nonempty_affine_cover X
  exact exists_modification_of_finite_affine_cover p (fun i => L.get i)
    (fun i => hL _ (List.get_mem L i)) hcover

end DeJongAlterations.Geometry.ChowLemma
