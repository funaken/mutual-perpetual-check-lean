import MPC.Basic.OrientedMove
/-!
# MPC.Basic.OrientedCheck

Owner-oriented attacks and checks. These predicates
do not assert move legality or the presence/uniqueness of a king at the target.
The legacy check predicates and their consumers retain their existing meaning.
-/

namespace MPC

/-- Direction/path attack by a specified piece; source presence is separate. -/
def attacksOriented (board : Board) (owner : Player) (pt : PieceType)
    (pos kingPos : Pos) : Prop := canMoveToOriented board owner pt pos kingPos

/-- A currently present opposing piece attacks the supplied target position.
    Presence and uniqueness of the target king are separate conditions. -/
def inCheckOriented (board : Board) (player : Player) (kingPos : Pos) : Prop :=
  ∃ pos : Pos, ∃ piece : Piece, board.grid pos = some piece ∧
    piece.owner = player.opponent ∧
    attacksOriented board piece.owner piece.pieceType pos kingPos

/-- Keeping every empty square empty preserves clearance. -/
theorem pathClear_mono_of_empty_preserved (before after : Board)
    (h_empty : ∀ q : Pos, before.grid q = none → after.grid q = none)
    (src dst : Pos) (h : pathClear before src dst) : pathClear after src dst := by
  intro q hq hob hproof
  exact h_empty _ (h q hq hob hproof)

theorem attacksOriented_not_self (board : Board) (owner : Player)
    (pt : PieceType) (pos : Pos) : ¬ attacksOriented board owner pt pos pos :=
  canMoveToOriented_not_self board owner pt pos

theorem attacksOriented_mono_of_empty_preserved (before after : Board)
    (h_empty : ∀ q : Pos, before.grid q = none → after.grid q = none)
    (owner : Player) (pt : PieceType) (src dst : Pos)
    (h : attacksOriented before owner pt src dst) :
    attacksOriented after owner pt src dst := by
  rcases h with hs | ⟨sd, hsd, hn, k, hk, hx, hy, hp⟩
  · exact Or.inl hs
  · exact Or.inr ⟨sd, hsd, hn, k, hk, hx, hy,
      pathClear_mono_of_empty_preserved before after h_empty src dst hp⟩

/-- Sufficient conditions for preserving check: empty squares stay empty and actual
    checkers retain their positions/owners/types. Emptiness alone is insufficient. -/
theorem inCheckOriented_mono_of_checkers_preserved (before after : Board)
    (player : Player) (kingPos : Pos)
    (h_empty : ∀ q : Pos, before.grid q = none → after.grid q = none)
    (h_keep : ∀ (pos : Pos) (piece : Piece), before.grid pos = some piece →
      piece.owner = player.opponent →
      attacksOriented before piece.owner piece.pieceType pos kingPos →
      after.grid pos = some piece)
    (h : inCheckOriented before player kingPos) :
    inCheckOriented after player kingPos := by
  obtain ⟨pos, piece, hp, ho, ha⟩ := h
  exact ⟨pos, piece, h_keep pos piece hp ho ha, ho,
    attacksOriented_mono_of_empty_preserved before after h_empty _ _ _ _ ha⟩

end MPC
