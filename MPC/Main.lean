import MPC.Pieces.BishopDiscH
import MPC.Invariants.DiscoveredCheckNecessity
import MPC.Invariants.PieceFamilyStep
import MPC.Trace.PeriodicMutualCheck
/-!
# MPC.Main

定理1.1（将棋）：周期的な双方連続王手の手順は存在しない。

有限手順の遷移・移動・玉配置・安全・王手・周期性を`PeriodicMutualCheck`にまとめ、
持駒からの打ちと初期の大駒数を追加条件とする。成り場所などの規則を緩めたモデルであり、
完全な合法手判定器ではない。仕様対応は`docs/publication-model-audit.md`を参照。

証明は、命題4.1から先手の開き王手を取り出し、移動駒の種類ごとに排除する。
玉は命題2.2、桂・香・歩は前進ポテンシャル、金型・銀・飛車竜は第5節の幾何、
角・馬は表1と命題3.8の半平面不変量によって矛盾する。

`mutual_perpetual_check_impossible_of_pieceCounts`は全状態の駒数上限を仮定する形。
最終定理ではその上限と打ち先の空きを導き、仮定を初期状態と持駒の条件に集約する。
-/

namespace MPC

/-- 全状態での大駒数上限を前提にする形。命題4.1から開き王手を得て駒種別に排除する。 -/
theorem mutual_perpetual_check_impossible_of_pieceCounts :
    ¬ ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos),
      tr.MutualPerpetualCheck kp ∧ tr.PieceCountsAtMostTwo := by
  rintro ⟨tr, kp, hm, hcount⟩
  have h41 := tr.discoveredCheckByEachSide_of_mutualPerpetualCheck kp hm
  refine tr.false_of_no_openableMove kp hm h41 fun pt hpt => ?_
  cases pt with
  | king => exact absurd rfl hpt
  | knight => exact tr.not_openableMove_forward_of_periodic kp hm .sente _ (Or.inl rfl)
  | lance => exact tr.not_openableMove_forward_of_periodic kp hm .sente _ (Or.inr (Or.inl rfl))
  | pawn => exact tr.not_openableMove_forward_of_periodic kp hm .sente _ (Or.inr (Or.inr rfl))
  | gold => exact tr.not_openableMove_goldType_of_periodic kp hm .sente _ rfl
  | promotedSilver => exact tr.not_openableMove_goldType_of_periodic kp hm .sente _ rfl
  | promotedKnight => exact tr.not_openableMove_goldType_of_periodic kp hm .sente _ rfl
  | promotedLance => exact tr.not_openableMove_goldType_of_periodic kp hm .sente _ rfl
  | tokin => exact tr.not_openableMove_goldType_of_periodic kp hm .sente _ rfl
  | silver => exact tr.not_openableMove_silver_of_periodic kp hm hcount .sente
  | rook => exact tr.not_openableMove_rookDragon_of_periodic kp hm h41 hcount .sente _ (Or.inl rfl)
  | dragon =>
    exact tr.not_openableMove_rookDragon_of_periodic kp hm h41 hcount .sente _ (Or.inr rfl)
  | bishop =>
    exact tr.not_openableMove_bishopHorse_of_periodic kp hm h41 hcount .sente _ (Or.inl rfl)
  | horse =>
    exact tr.not_openableMove_bishopHorse_of_periodic kp hm h41 hcount .sente _ (Or.inr rfl)

/-- 打ち先が空である条件を含む形。初期の大駒数と持駒からの打ちから全状態の上限を導く。 -/
theorem mutual_perpetual_check_impossible_of_mutualPerpetualCheck :
    ¬ ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos),
      tr.MutualPerpetualCheck kp ∧ tr.DropsFromHand ∧ tr.InitialPieceCountsAtMostTwo := by
  rintro ⟨tr, kp, hm, hdrop, hinit⟩
  exact mutual_perpetual_check_impossible_of_pieceCounts
    ⟨tr, kp, hm, tr.pieceCountsAtMostTwo_of_dropsFromHand kp hm hdrop hinit⟩

/-- 定理1.1。打ち先の空きを周期性と持駒の条件から導き、上の形へ帰着する。 -/
theorem mutual_perpetual_check_impossible :
    ¬ ∃ (tr : MoveTrace) (kp : Fin (tr.len + 1) → Player → Pos),
      tr.PeriodicMutualCheck kp ∧ tr.DropsFromHand ∧ tr.InitialPieceCountsAtMostTwo := by
  rintro ⟨tr, kp, hm, hdrop, hinit⟩
  exact mutual_perpetual_check_impossible_of_mutualPerpetualCheck
    ⟨tr, kp, hm.toMutualPerpetualCheck hdrop, hdrop, hinit⟩

end MPC
