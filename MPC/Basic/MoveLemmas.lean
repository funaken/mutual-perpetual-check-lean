import MPC.Basic.Move
/-!
# MPC.Basic.MoveLemmas

GameSeq に依存しない applyMove の盤面更新補題。
既存の名前・型・証明を MPC.Basic.Lemmas から移したもの。
-/

namespace MPC

/-! ## applyMove (boardMove) — グリッドへの影響 -/

/-- boardMove 後、移動元は空になる (src ≠ dst の場合) -/
theorem applyMove_boardMove_grid_src (bs : BoardState) (src dst : Pos) (promote : Bool)
    (h_ne : src ≠ dst) :
    (applyMove bs (.boardMove src dst promote)).board.grid src = none := by
  unfold applyMove
  dsimp only []
  cases bs.board.grid dst <;> simp [Board.setGrid, Board.addToHand, h_ne]

/-- boardMove 後、移動先には移動した駒がある -/
theorem applyMove_boardMove_grid_dst (bs : BoardState) (src dst : Pos) (promote : Bool) :
    (applyMove bs (.boardMove src dst promote)).board.grid dst =
      match bs.board.grid src with
      | some p => some { p with pieceType := if promote then p.pieceType.promote else p.pieceType }
      | none => none := by
  unfold applyMove
  dsimp only []
  cases bs.board.grid dst <;> cases bs.board.grid src <;> simp [Board.setGrid, Board.addToHand]

/-- boardMove 後、移動元でも移動先でもない位置は変化しない -/
theorem applyMove_boardMove_grid_other (bs : BoardState) (src dst : Pos) (promote : Bool)
    (pos : Pos) (h_src : pos ≠ src) (h_dst : pos ≠ dst) :
    (applyMove bs (.boardMove src dst promote)).board.grid pos = bs.board.grid pos := by
  unfold applyMove
  dsimp only []
  cases bs.board.grid dst <;> simp [Board.setGrid, Board.addToHand, h_src, h_dst]

/-- boardMove 後、手番が入れ替わる -/
theorem applyMove_boardMove_turn (bs : BoardState) (src dst : Pos) (promote : Bool) :
    (applyMove bs (.boardMove src dst promote)).turn = bs.turn.opponent := by
  simp [applyMove]

/-! ## applyMove (dropMove) — グリッドへの影響 -/

/-- dropMove 後、打った位置には打った駒がある -/
theorem applyMove_dropMove_grid_dst (bs : BoardState) (pt : PieceType) (dst : Pos) :
    (applyMove bs (.dropMove pt dst)).board.grid dst =
      some { owner := bs.turn, pieceType := pt } := by
  simp [applyMove, Board.setGrid, Board.removeFromHand]

/-- dropMove 後、打った位置以外は変化しない -/
theorem applyMove_dropMove_grid_other (bs : BoardState) (pt : PieceType) (dst : Pos)
    (pos : Pos) (h : pos ≠ dst) :
    (applyMove bs (.dropMove pt dst)).board.grid pos = bs.board.grid pos := by
  simp [applyMove, Board.setGrid, Board.removeFromHand, h]

/-- dropMove 後、手番が入れ替わる -/
theorem applyMove_dropMove_turn (bs : BoardState) (pt : PieceType) (dst : Pos) :
    (applyMove bs (.dropMove pt dst)).turn = bs.turn.opponent := by
  simp [applyMove]

end MPC
