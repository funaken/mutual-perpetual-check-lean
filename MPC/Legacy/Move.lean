import MPC.Basic.Move
/-! Legacy direction convention, retained only for comparison. -/
namespace MPC

/-- src にある駒が dst に移動できるか（駒の利きと経路の遮蔽を確認）。
    スライド移動は dst が src + k * sd の形（k ≥ 1）であることを厳密に要求する
    （normalize 一致だけでは整列が保証されないため: 例 (3,6).normalize = (1,1)）。 -/
def canMoveTo (board : Board) (owner : Player) (pt : PieceType) (src dst : Pos) : Prop :=
  let d := Pos.dirTo src dst
  let pd := d.forPlayer owner.opponent  -- 先手基準に変換
  -- ステップ移動
  (pd ∈ pt.stepDirs.map (Dir.forPlayer · owner.opponent)) ∨
  -- スライド移動: 厳密整列 (dst = src + k*sd, sd は正規化方向) と経路遮蔽
  (∃ sd ∈ pt.slideDirs.map (Dir.forPlayer · owner.opponent),
    d.normalize = sd ∧
    ∃ k : ℕ, 1 ≤ k ∧ d.1 = ↑k * sd.1 ∧ d.2 = ↑k * sd.2 ∧
    pathClear board src dst)

end MPC
