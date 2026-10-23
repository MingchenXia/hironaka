/-
The native closed-pullback criterion and pasting adapt the minimal proved core of
EnvelopeProperty/deps/hironaka-ep33/Hironaka/Scheme/BlowUp/ClosedImmersionLift.lean, SHA256
56b71986145c772fa1c0be7f3b769c1e2778a2e92fcfcb4bc5b551e35bb2269d, and
EnvelopeProperty/deps/hironaka-ep33/Hironaka/Scheme/Smooth/ExceptionalChart.lean, SHA256
2610e7c584ca82f19c2ea705d0135b4940d1375bd6df6276874eab5f4e58d412.
No Hironaka or EnvelopeProperty imports; all squares and maps are actual native ones.
-/
import DeJongAlterations.Algebra.NodeFittingOmegaGluing
import DeJongAlterations.Geometry.NodeCompletedLocalGeometricChart
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The ACTUAL pulled original Fitting closed subscheme is the ACTUAL family base change -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Algebra.NodeFittingGeometricPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

universe u
variable {X Y S T : Scheme.{u}}

/-- The canonical ACTUAL map from the pulled closed subscheme to the ORIGINAL closed subscheme. -/
def closedProjection (I : X.IdealSheafData) (g : Y ⟶ X) :
    (I.comap g).subscheme ⟶ I.subscheme :=
  Scheme.IdealSheafData.subschemeMap (I.comap g) I g (I.le_map_comap g)

/-- The WHOLE actual original inclusion triangle is retained. -/
@[reassoc (attr := simp)]
theorem closedProjection_inclusion (I : X.IdealSheafData) (g : Y ⟶ X) :
    closedProjection I g ≫ I.subschemeι = (I.comap g).subschemeι ≫ g :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The actual whole native kernels prove the genuine closed-subscheme pullback square. -/
theorem closed_isPullback (I : X.IdealSheafData) (g : Y ⟶ X) :
    IsPullback (I.comap g).subschemeι (closedProjection I g) g I.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (closedProjection_inclusion I g).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])

/-- The SAME native pulled closed subscheme is actual base change of the ORIGINAL structural family map. -/
theorem family_isPullback (I : X.IdealSheafData) (f : X ⟶ S) (a : T ⟶ S) :
    IsPullback (closedProjection I (pullback.fst f a))
      ((I.comap (pullback.fst f a)).subschemeι ≫ pullback.snd f a)
      (I.subschemeι ≫ f) a :=
  (closed_isPullback I (pullback.fst f a)).flip.paste_vert (IsPullback.of_hasPullback f a)

open Geometry.NodeCompletedLocalGeometricChart

variable (f : X ⟶ S) [LocallyOfFinitePresentation f] (s : S)
  (K : Type u) [Field K] [Algebra (S.residueField s) K] (i : ℕ)

local notation "π" => pullback.fst f (originalFieldMap s K)
local notation "q" => pullback.snd f (originalFieldMap s K)
local notation "J" => NodeFittingOmegaGluing.idealSheaf f i

/-- The genuine ACTUAL geometric pullback square of the ORIGINAL intrinsic Fitting structural morphism. -/
theorem geometricFitting_isPullback :
    IsPullback (closedProjection J π) (((J).comap π).subschemeι ≫ q)
      (NodeFittingOmegaGluing.fittingMorphism f i) (originalFieldMap s K) :=
  family_isPullback J f (originalFieldMap s K)

/-- The canonical native isomorphism to the LITERAL base change of the ORIGINAL Fitting family. -/
def geometricFittingPullbackIso :
    ((J).comap π).subscheme ≅
      pullback (NodeFittingOmegaGluing.fittingMorphism f i) (originalFieldMap s K) :=
  (geometricFitting_isPullback f s K i).isoPullback

/-- The ENTIRE original closed-subscheme projection triangle is the same actual native one. -/
@[reassoc (attr := simp)]
theorem geometricFittingPullbackIso_hom_fst :
    (geometricFittingPullbackIso f s K i).hom ≫ pullback.fst _ _ = closedProjection J π :=
  (geometricFitting_isPullback f s K i).isoPullback_hom_fst

/-- The ENTIRE external-field projection is EXACTLY the ACTUAL pulled inclusion followed by q. -/
@[reassoc (attr := simp)]
theorem geometricFittingPullbackIso_hom_snd :
    (geometricFittingPullbackIso f s K i).hom ≫ pullback.snd _ _ = ((J).comap π).subschemeι ≫ q :=
  (geometricFitting_isPullback f s K i).isoPullback_hom_snd

end DeJongAlterations.Algebra.NodeFittingGeometricPullback
