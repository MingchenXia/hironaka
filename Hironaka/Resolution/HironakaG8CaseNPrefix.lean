import Hironaka.Invariant.MemberInterTowerAlong

/-!
# Ordered old-boundary prefixes in a geometric test tower

A tower retains the strict transforms of an added initial boundary before the
native transformed boundary, including every chronological exceptional member.
This is an identity of the actual records and assumes no test conditions.
-/

set_option autoImplicit false

open Set
universe u

namespace Hironaka.HironakaG8CaseNPrefix

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal

/-- Adding an ordered prefix before a boundary commutes with every geometric
transform: the prefix becomes its actual strict transforms, and the native
boundary retains all its exceptional births in chronological order. -/
theorem geoTransformAlong_prefix
    {n : ℕ} {X : CMfd.{u} n} (P : MarkedIdeal n X) (F : List (Set X)) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      geoTransformAlong { P with E := F ++ P.E } T =
        { geoTransformAlong P T with
          E := F.map (strictAlong T) ++ (geoTransformAlong P T).E }
  | _, .refl => by
    simp only [geoTransformAlong_refl]
    congr 1
    exact congrArg (fun E => E ++ P.E) (List.map_id' F).symm
  | _, .step T C π hπ => by
    rw [geoTransformAlong_step, geoTransformAlong_step, geoTransformAlong_prefix P F T]
    refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ rfl rfl
    show ((F.map (strictAlong T) ++ (geoTransformAlong P T).E).map
      (geoStrictTransform π C) ++ [π ⁻¹' C]) = _
    rw [List.map_append, List.map_map, List.append_assoc]
    rfl

end
end Hironaka.HironakaG8CaseNPrefix
