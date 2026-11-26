import MPC.Basic.Defs
import MPC.Basic.Demote
import MPC.Basic.Grid
/-!
# MPC.Basic.Move

指し手の定義 (盤上移動・駒打ち) と経路遮蔽の判定。
-/

namespace MPC

/-- 指し手 -/
inductive Move : Type
  | boardMove (src dst : Pos) (promote : Bool) : Move  -- 盤上の駒を移動
  | dropMove  (pieceType : PieceType) (dst : Pos) : Move  -- 持ち駒を打つ
  deriving DecidableEq, Repr

/-- スライド駒の経路上の格子点を列挙する補助関数。
    d: 正規化された方向、dstInt: 目標の整数座標、cur: 現在位置、fuel: 残りステップ -/
def slidePathAux (d : Dir) (dstInt : ℤ × ℤ) (cur : ℤ × ℤ) : Nat → List (ℤ × ℤ)
  | 0 => []
  | fuel + 1 =>
    if (cur.1 + d.1, cur.2 + d.2) = dstInt then []
    else (cur.1 + d.1, cur.2 + d.2) :: slidePathAux d dstInt (cur.1 + d.1, cur.2 + d.2) fuel

/-- スライド駒の経路上（src と dst の間、両端を含まない）にある格子点のリスト -/
def slidePath (src dst : Pos) : List (ℤ × ℤ) :=
  let d := (Pos.dirTo src dst).normalize
  if d = (0, 0) then []
  else slidePathAux d dst.toInt src.toInt 8

/-- スライド経路上に駒がないか -/
def pathClear (board : Board) (src dst : Pos) : Prop :=
  ∀ q ∈ slidePath src dst,
    onBoard q → ∀ (h : onBoard q), board.grid (toPos q h) = none

/-- 盤面の1マスを更新 -/
def Board.setGrid (b : Board) (pos : Pos) (sq : Square) : Board :=
  { b with grid := fun p => if p = pos then sq else b.grid p }

/-- 持ち駒に1枚追加 -/
def Board.addToHand (b : Board) (player : Player) (pt : PieceType) : Board :=
  { b with hand := fun p => if p = player then b.hand p + ({pt} : Hand) else b.hand p }

/-- 持ち駒から1枚除去 -/
def Board.removeFromHand (b : Board) (player : Player) (pt : PieceType) : Board :=
  { b with hand := fun p => if p = player then b.hand p - ({pt} : Hand) else b.hand p }

/-- 成りの処理: 成り可能な駒を成駒に変換 -/
def PieceType.promote : PieceType → PieceType
  | .rook   => .dragon
  | .bishop => .horse
  | .silver => .promotedSilver
  | .knight => .promotedKnight
  | .lance  => .promotedLance
  | .pawn   => .tokin
  | other   => other

/-- 指し手による局面の遷移（盤面を更新）-/
def applyMove (bs : BoardState) (m : Move) : BoardState :=
  match m with
  | .boardMove src dst promote =>
    let piece := bs.board.grid src
    let capturedPiece := bs.board.grid dst
    let movedPiece := match piece with
      | some p => some { p with pieceType := if promote then p.pieceType.promote else p.pieceType }
      | none => none
    let board₁ := (bs.board.setGrid src none).setGrid dst movedPiece
    -- 取った駒を元の駒に戻して持ち駒に追加（取った駒がある場合、）
    let board₂ := match capturedPiece with
      | some cp => board₁.addToHand bs.turn cp.pieceType.demote
      | none => board₁
    { board := board₂, turn := bs.turn.opponent }
  | .dropMove pt dst =>
    let piece : Piece := { owner := bs.turn, pieceType := pt }
    let board₁ := bs.board.setGrid dst (some piece)
    let board₂ := board₁.removeFromHand bs.turn pt
    { board := board₂, turn := bs.turn.opponent }

end MPC
