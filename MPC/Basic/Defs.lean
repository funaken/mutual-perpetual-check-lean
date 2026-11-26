import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Init
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
/-!
# MPC.Basic.Defs

将棋の基本的な型定義。盤面・駒・局面を定義する。
-/

namespace MPC

/-- 対局者 -/
inductive Player : Type
  | sente : Player  -- 先手
  | gote  : Player  -- 後手
  deriving DecidableEq, Repr

/-- 対局者の入れ替え -/
def Player.opponent : Player → Player
  | .sente => .gote
  | .gote  => .sente

/-- 駒の種類 -/
inductive PieceType : Type
  | king   : PieceType  -- 玉
  | rook   : PieceType  -- 飛車
  | bishop : PieceType  -- 角
  | gold   : PieceType  -- 金
  | silver : PieceType  -- 銀
  | knight : PieceType  -- 桂
  | lance  : PieceType  -- 香
  | pawn   : PieceType  -- 歩
  -- 成駒
  | dragon : PieceType  -- 竜 (成飛)
  | horse  : PieceType  -- 馬 (成角)
  | promotedSilver : PieceType  -- 成銀
  | promotedKnight : PieceType  -- 成桂
  | promotedLance  : PieceType  -- 成香
  | tokin          : PieceType  -- と金 (成歩)
  deriving DecidableEq, Repr

/-- 金と同じ動きをする駒か (成銀・成桂・成香・と金) -/
def PieceType.movesLikeGold : PieceType → Bool
  | .gold           => true
  | .promotedSilver => true
  | .promotedKnight => true
  | .promotedLance  => true
  | .tokin          => true
  | _               => false

/-- 駒 -/
structure Piece where
  owner : Player
  pieceType : PieceType
  deriving DecidableEq, Repr

/-- 盤上の位置 (9x9 格子点) -/
abbrev Pos := Fin 9 × Fin 9

/-- 位置を整数座標に変換 (幾何計算用) -/
def Pos.toInt (p : Pos) : ℤ × ℤ :=
  (↑p.1.val, ↑p.2.val)

/-- マスの状態: 駒があるか空か -/
abbrev Square := Option Piece

/-- 持ち駒 -/
abbrev Hand := Multiset PieceType

/-- 盤面: 盤上の配置と持ち駒 -/
structure Board where
  grid : Pos → Square
  hand : Player → Hand

/-- 局面: 盤面 + 手番 -/
structure BoardState where
  board : Board
  turn  : Player

/-! ## 駒の利き方向 -/

/-- 方向ベクトル (dx, dy)。先手視点で y 正方向が敵陣側。 -/
abbrev Dir := ℤ × ℤ

/-- 先手の駒の1マス移動先（非スライド駒用）-/
def PieceType.stepDirs : PieceType → List Dir
  | .king            => [(-1,1),(0,1),(1,1),(-1,0),(1,0),(-1,-1),(0,-1),(1,-1)]
  | .gold            => [(-1,1),(0,1),(1,1),(-1,0),(1,0),(0,-1)]
  | .silver          => [(-1,1),(0,1),(1,1),(-1,-1),(1,-1)]
  | .knight          => [(-1,2),(1,2)]
  | .pawn            => [(0,1)]
  | .lance           => []  -- スライド駒なので stepDirs は空
  | .rook            => []
  | .bishop          => []
  | .dragon          => [(-1,1),(1,1),(-1,-1),(1,-1)]  -- 竜: 飛車のスライド + 斜め1マス
  | .horse           => [(-1,0),(1,0),(0,-1),(0,1)]    -- 馬: 角のスライド + 縦横1マス
  | .promotedSilver  => [(-1,1),(0,1),(1,1),(-1,0),(1,0),(0,-1)]  -- 金と同じ
  | .promotedKnight  => [(-1,1),(0,1),(1,1),(-1,0),(1,0),(0,-1)]
  | .promotedLance   => [(-1,1),(0,1),(1,1),(-1,0),(1,0),(0,-1)]
  | .tokin           => [(-1,1),(0,1),(1,1),(-1,0),(1,0),(0,-1)]

/-- 先手の駒のスライド方向（飛車・角・香車・竜・馬用）-/
def PieceType.slideDirs : PieceType → List Dir
  | .lance   => [(0,1)]
  | .rook    => [(0,1),(0,-1),(1,0),(-1,0)]
  | .bishop  => [(1,1),(1,-1),(-1,1),(-1,-1)]
  | .dragon  => [(0,1),(0,-1),(1,0),(-1,0)]    -- 飛車と同じスライド
  | .horse   => [(1,1),(1,-1),(-1,1),(-1,-1)]  -- 角と同じスライド
  | _        => []

/-- 後手の方向ベクトルに変換（y座標を反転）-/
def Dir.flip (d : Dir) : Dir := (d.1, -d.2)

/-- プレイヤーに応じた方向ベクトルの調整 -/
def Dir.forPlayer (d : Dir) (p : Player) : Dir :=
  match p with
  | .sente => d
  | .gote  => d.flip

end MPC
