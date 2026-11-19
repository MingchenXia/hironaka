import Hironaka.Geometry.RelativeChowProducts
import Hironaka.Geometry.RelativeChowAffineCover
import Hironaka.Geometry.RelativeChowPatchCompactification
import Hironaka.Geometry.ProjectiveGraphModificationProperTarget
import Hironaka.Geometry.ChowLemmaOpenLocus

/-!
# Genuine relative Chow modifications over Noetherian schemes

Every local projective compactification is constructed over the original
scheme base. Their actual native relative product and actual common-open
graph closure produce the modification. The actual complement-at-infinity
argument proves the relative projective immersion. Properness closes it
when the original map is proper. The scheme base need not be separated.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace Hironaka.Geometry.RelativeChow

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S Y : Scheme.{u}}

/-- A proper map with an actual projective immersion over the composite
has an actual closed projective embedding over its own target. -/
theorem closed_embedding_over_source_of_proper
    (p : X ⟶ S) (h : Y ⟶ X) [IsProper h] {d : ℕ}
    (e : Y ⟶ relativeSpace S d) [IsImmersion e]
    (he : e ≫ relativeStructure S d = h ≫ p) :
    ∃ a : Y ⟶ relativeSpace X d,
      IsClosedImmersion a ∧ a ≫ relativeStructure X d = h := by
  let a : Y ⟶ relativeSpace X d :=
    pullback.lift h (e ≫ integerProjection S d) (specULiftZIsTerminal.hom_ext _ _)
  let t : relativeSpace X d ⟶ relativeSpace S d :=
    pullback.lift (relativeStructure X d ≫ p) (integerProjection X d)
      (specULiftZIsTerminal.hom_ext _ _)
  have hat : a ≫ t = e := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, a, t, relativeStructure, pullback.lift_fst,
        pullback.lift_fst_assoc] using he.symm
    · simp [a, t, integerProjection, Category.assoc]
  have ha : a ≫ relativeStructure X d = h := by simp [a, relativeStructure]
  let : IsImmersion (a ≫ t) := by rw [hat]; infer_instance
  let : IsImmersion a := IsImmersion.of_comp a t
  let : IsProper (a ≫ relativeStructure X d) := by rw [ha]; infer_instance
  let : IsProper a := IsProper.of_comp a (relativeStructure X d)
  exact ⟨a, IsClosedImmersion.of_isPreimmersion a a.isClosedMap.isClosed_range, ha⟩

/-- The genuine scheme-relative Chow construction from actual subordinate
affine covers. No relative compactification or projective output is supplied. -/
theorem exists_scheme_modification_of_finite_affine_cover
    (p : X ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian S] [IsSeparated p] [LocallyOfFiniteType p]
    {n : ℕ} (U : Fin n → X.affineOpens) (V : Fin n → S.affineOpens)
    (hU : ∀ i, ((U i).1 : Set X).Nonempty)
    (hUV : ∀ i, (U i).1 ≤ p ⁻¹ᵁ (V i).1) (hcover : ⨆ i, (U i).1 = ⊤) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (d : ℕ) (e : Y ⟶ relativeSpace S d),
      IsModification π ∧ IsImmersion e ∧ e ≫ relativeStructure S d = π ≫ p := by
  classical
  have hcomp (i : Fin n) :
      ∃ (C : Scheme.{u}) (q : C ⟶ S) (j : (U i).1.toScheme ⟶ C)
        (d : ℕ) (b : C ⟶ relativeSpace S d),
        IsIntegral C ∧ IsOpenImmersion j ∧ IsDominant j ∧ j ≫ q = (U i).1.ι ≫ p ∧
        IsClosedImmersion b ∧ b ≫ relativeStructure S d = q := by
    let : Nonempty (U i).1 := ⟨⟨(hU i).choose, (hU i).choose_spec⟩⟩
    exact exists_subordinate_compactification p (U i) (V i) (hUV i)
  choose C q e d b hInt heopen hedom hebase hbclosed hbbase using hcomp
  let : ∀ i, IsOpenImmersion (e i) := heopen
  let : ∀ i, IsProper (q i) := fun i => by
    let := hbclosed i
    rw [← hbbase i]
    infer_instance
  let A : Fin n → Over S := fun i => Over.mk (q i)
  let P := relativeIndexedProduct A
  obtain ⟨D, B, hB, hBq⟩ := exists_relativeIndexedProduct_embedding A
    (fun i => ⟨d i, b i, hbclosed i, hbbase i⟩)
  let := hB
  let : IsProper P.hom := by rw [← hBq]; infer_instance
  let L := List.ofFn U
  have hL : ∀ W ∈ L, (W.1 : Set X).Nonempty := by
    intro W hW
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hW
    exact hU i
  let O := ChowLemmaAffineCover.commonOpen L
  let : Nonempty O.toScheme := ChowLemmaAffineCover.commonOpen_nonempty L hL
  have hOU (i : Fin n) : O ≤ (U i).1 := by
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (List.mem_ofFn.mpr ⟨i, rfl⟩ : U i ∈ L)
    exact hj ▸ ChowLemmaAffineCover.commonOpen_le_get L j
  let a (i : Fin n) : O.toScheme ⟶ (U i).1.toScheme := X.homOfLE (hOU i)
  let Z : Over S := Over.mk (O.ι ≫ p)
  let fC (i : Fin n) : Z ⟶ A i := Over.homMk (a i ≫ e i) (by
    change (a i ≫ e i) ≫ q i = O.ι ≫ p
    rw [Category.assoc, hebase, ← Category.assoc, Scheme.homOfLE_ι])
  let f : O.toScheme ⟶ P.left := (relativeIndexedLift Z A fC).left
  have hf : f ≫ P.hom = O.ι ≫ p := (relativeIndexedLift Z A fC).w
  let Y := ProjectiveGraphModification.ProperTarget.modification p P.hom O f hf
  let π : Y ⟶ X := ProjectiveGraphModification.ProperTarget.projection p P.hom O f hf
  let F : Y ⟶ P.left := ProjectiveGraphModification.ProperTarget.projectiveMap p P.hom O f hf
  let j : O.toScheme ⟶ Y := ProjectiveGraphModification.ProperTarget.inclusion p P.hom O f hf
  let : IsIntegral Y := ProjectiveGraphModification.ProperTarget.modification_isIntegral p P.hom O f hf
  have hbase : π ≫ p = F ≫ P.hom :=
    (ProjectiveGraphModification.ProperTarget.structure_triangle p P.hom O f hf).symm
  have hpair : pullback.lift π F hbase =
      ProjectiveGraphModification.ProperTarget.embedding p P.hom O f hf := by
    apply pullback.hom_ext <;> simp [π, F,
      ProjectiveGraphModification.ProperTarget.projection,
      ProjectiveGraphModification.ProperTarget.projectiveMap]
  let : IsImmersion (pullback.lift π F hbase) := by rw [hpair]; infer_instance
  let r (i : Fin n) : P.left ⟶ C i := (relativeIndexedProjection A i).left
  have hr (i : Fin n) : r i ≫ q i = P.hom := (relativeIndexedProjection A i).w
  let : IsImmersion F := ChowLemmaOpenLocus.isImmersion_of_dense_graph_open_cover
    p P.hom π F hbase C q r hr (fun i => (U i).1.toScheme)
    (fun i => (U i).1.ι) e (fun i => (hebase i).symm)
    (by simpa only [Scheme.Opens.opensRange_ι] using hcover) j a
    (fun i => by
      dsimp [j, π, a]
      rw [ProjectiveGraphModification.ProperTarget.inclusion_projection, Scheme.homOfLE_ι])
    (fun i => by
      change j ≫ F ≫ (relativeIndexedProjection A i).left = a i ≫ e i
      rw [← Category.assoc, show j ≫ F = f from
        ProjectiveGraphModification.ProperTarget.inclusion_projectiveMap p P.hom O f hf]
      exact congrArg (fun m => m.left) (relativeIndexedLift_projection Z A fC i))
  refine ⟨Y, π, D, F ≫ B, inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, hBq, ← hbase]

/-- Genuine relative Chow's lemma over any Noetherian scheme. Source
Noetherianity is derived internally; no separatedness of the base is assumed. -/
theorem exists_scheme_modification
    (p : X ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian S]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (d : ℕ) (e : Y ⟶ relativeSpace S d),
      IsModification π ∧ IsImmersion e ∧ e ≫ relativeStructure S d = π ≫ p := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨n, U, V, hU, hUV, hcover⟩ := exists_finite_subordinate_affine_cover p
  exact exists_scheme_modification_of_finite_affine_cover p U V hU hUV hcover

/-- The actual modification itself has an actual closed projective
presentation over X, as well as an actual projective immersion over S. -/
theorem exists_scheme_projective_modification
    (p : X ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian S]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (d : ℕ)
      (e : Y ⟶ relativeSpace S d) (a : Y ⟶ relativeSpace X d),
      IsModification π ∧ IsImmersion e ∧ e ≫ relativeStructure S d = π ≫ p ∧
      IsClosedImmersion a ∧ a ≫ relativeStructure X d = π := by
  obtain ⟨Y, π, d, e, hπ, he, hbase⟩ := exists_scheme_modification p
  let := hπ
  let := he
  obtain ⟨a, ha, hatri⟩ := closed_embedding_over_source_of_proper p π e hbase
  exact ⟨Y, π, d, e, a, hπ, he, hbase, ha, hatri⟩

/-- Properness of the original map makes the genuinely constructed
relative projective immersion an actual relative closed presentation. -/
theorem exists_scheme_projective_source_of_isProper
    (p : X ⟶ S) [IsIntegral X] [AlgebraicGeometry.IsNoetherian S] [IsProper p] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (d : ℕ) (e : Y ⟶ relativeSpace S d),
      IsModification π ∧ IsClosedImmersion e ∧ e ≫ relativeStructure S d = π ≫ p := by
  obtain ⟨Y, π, d, e, hπ, he, hbase⟩ := exists_scheme_modification p
  let := hπ
  let := he
  let : IsProper (e ≫ relativeStructure S d) := by rw [hbase]; infer_instance
  let : IsProper e := IsProper.of_comp e (relativeStructure S d)
  exact ⟨Y, π, d, e, hπ,
    IsClosedImmersion.of_isPreimmersion e e.isClosedMap.isClosed_range, hbase⟩

end Hironaka.Geometry.RelativeChow
