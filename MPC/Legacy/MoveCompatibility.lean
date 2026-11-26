import MPC.Basic.OrientedMove
import MPC.Legacy.Move
/-! Compatibility for direction-symmetric pieces only. -/
namespace MPC

-- Transforming both sides of step membership cancels the owner adjustment.
private theorem mem_map_forPlayer_iff (d : Dir) (owner : Player) (dirs : List Dir) :
    d.forPlayer owner ∈ dirs.map (Dir.forPlayer · owner) ↔ d ∈ dirs := by
  have hi : Function.Involutive (fun d : Dir => d.forPlayer owner) := by
    intro d
    cases owner <;> simp [Dir.forPlayer, Dir.flip]
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact hi.injective heq ▸ hx
  · intro hd
    exact ⟨d, hd, rfl⟩

/-- The direction correction preserves the legacy predicate for pieces whose
    step and slide direction sets are invariant under y reflection. -/
theorem canMoveToOriented_iff_canMoveTo_of_symmetric (board : Board) (owner : Player)
    (pt : PieceType) (src dst : Pos)
    (h : pt = .king ∨ pt = .rook ∨ pt = .bishop ∨ pt = .dragon ∨ pt = .horse) :
    canMoveToOriented board owner pt src dst ↔ canMoveTo board owner pt src dst := by
  have hs (d : Dir) : d ∈ pt.stepDirs.map (Dir.forPlayer · owner) ↔ d ∈ pt.stepDirs := by
    rcases h with rfl | rfl | rfl | rfl | rfl <;> cases owner <;>
      simp [PieceType.stepDirs, Dir.forPlayer, Dir.flip, or_comm, or_left_comm, or_assoc]
  have hl (d : Dir) : d ∈ pt.slideDirs.map (Dir.forPlayer · owner) ↔
      d ∈ pt.slideDirs.map (Dir.forPlayer · owner.opponent) := by
    rcases h with rfl | rfl | rfl | rfl | rfl <;> cases owner <;>
      simp [PieceType.slideDirs, Dir.forPlayer, Dir.flip, Player.opponent,
        or_comm, or_left_comm]
  simp only [canMoveToOriented, canMoveTo, mem_map_forPlayer_iff, hs, hl]

end MPC
