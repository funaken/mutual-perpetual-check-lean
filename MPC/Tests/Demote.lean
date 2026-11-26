import MPC.Basic.DemoteFamily
import Lean
/-!
# MPC.Tests.Demote

Concrete checks for .

- The six promoted types go back to their original pieces: tokin to pawn, dragon to
  rook, horse to bishop, promoted silver, knight and lance to silver, knight and lance.
- The other eight types are unchanged, so exactly six types change.
- The families of  and  are closed under demotion: a horse demotes into the
  bishop family, a dragon into the rook family.
-/

open Lean in
run_cmd do
  if (← getEnv).contains `MPC.GameSeq then
    throwError "Demote verification must not import GameSeq"

namespace MPC
namespace DemoteTests

/-- Every piece type, each once. -/
private def allTypes : List PieceType :=
  [.king, .rook, .bishop, .gold, .silver, .knight, .lance, .pawn,
   .dragon, .horse, .promotedSilver, .promotedKnight, .promotedLance, .tokin]

/-! ## The promoted types go back -/

example : PieceType.tokin.demote = .pawn := rfl
example : PieceType.dragon.demote = .rook := rfl
example : PieceType.horse.demote = .bishop := rfl
example : PieceType.promotedSilver.demote = .silver := rfl
example : PieceType.promotedKnight.demote = .knight := rfl
example : PieceType.promotedLance.demote = .lance := rfl

/-! ## The other types stay -/

example : ∀ pt ∈ [PieceType.king, .rook, .bishop, .gold, .silver, .knight, .lance, .pawn],
    pt.demote = pt := by decide

-- Exactly six of the fourteen types change.
example : allTypes.length = 14 := rfl
example : (allTypes.filter (fun pt => pt.demote ≠ pt)).length = 6 := by decide

-- Every original piece promotes back to the promoted type.
example : ∀ pt ∈ [PieceType.dragon, .horse, .promotedSilver, .promotedKnight,
    .promotedLance, .tokin], pt.demote.promote = pt := by decide

/-! ## Families are closed under demotion -/

example : PieceType.IsBishopFamily PieceType.horse.demote :=
  (promoteStable_bishopFamily.demote_iff _).mpr (Or.inr rfl)

example : PieceType.IsRookFamily PieceType.dragon.demote :=
  (promoteStable_rookFamily.demote_iff _).mpr (Or.inr rfl)

example : ¬ PieceType.IsRookFamily PieceType.horse.demote := by
  rw [promoteStable_rookFamily.demote_iff]
  simp [PieceType.IsRookFamily]

example : familyInd PieceType.IsBishopFamily (some ⟨.gote, PieceType.horse.demote⟩) = 1 := by
  decide

end DemoteTests
end MPC
