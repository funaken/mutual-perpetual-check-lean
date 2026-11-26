import MPC.Legacy.Move
/-!
# MPC.Legacy.Check

王手・直接王手・開き王手の定義。
-/

namespace MPC

/-- 位置 pos にある駒種 pt (所有者 owner) が kingPos にある玉に利きがあるか
    （盤面上の遮蔽を考慮する）-/
def attacks (board : Board) (owner : Player) (pt : PieceType) (pos kingPos : Pos) : Prop :=
  canMoveTo board owner pt pos kingPos

/-- 盤面 board 上で player の玉 (位置 kingPos) が王手されているか -/
def inCheck (board : Board) (player : Player) (kingPos : Pos) : Prop :=
  ∃ pos : Pos, ∃ piece : Piece,
    board.grid pos = some piece ∧
    piece.owner = player.opponent ∧
    attacks board piece.owner piece.pieceType pos kingPos

/-- 指し手 m の結果の盤面で、移動した駒自体が王手をかけているか（直接王手）-/
def isDirectCheck (boardAfter : Board) (m : Move) (enemyKingPos : Pos) : Prop :=
  match m with
  | .boardMove _src dst _promote =>
    ∃ piece : Piece, boardAfter.grid dst = some piece ∧
      attacks boardAfter piece.owner piece.pieceType dst enemyKingPos
  | .dropMove pt dst =>
    ∃ owner : Player, attacks boardAfter owner pt dst enemyKingPos

/-- 指し手 m の結果の盤面で、移動した駒以外の自駒が王手をかけているか（開き王手）
    player: 手番を指した側（開き王手をかける駒の所有者） -/
def isDiscoveredCheck (boardAfter : Board) (m : Move) (player : Player)
    (enemyKingPos : Pos) : Prop :=
  match m with
  | .boardMove _src dst _promote =>
    ∃ pos : Pos, pos ≠ dst ∧ ∃ piece : Piece,
      boardAfter.grid pos = some piece ∧
      piece.owner = player ∧
      attacks boardAfter piece.owner piece.pieceType pos enemyKingPos
  | .dropMove _ _ => False  -- 駒を打つ手では開き王手は発生しない

end MPC
