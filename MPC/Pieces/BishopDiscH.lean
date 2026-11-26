import MPC.Basic.Lemmas
import MPC.Pieces.BishopTable
/-!
# MPC.Pieces.BishopDiscH

The last case of the paper's §5: in Table 1's rows, Proposition 3.8 fails. The premises are those of the main theorem, and the conclusion is
`False` (`false_of_bishop_rows_of_periodic`).

**Blocking.** Two consequences of the checks around a move:
- Corollary 3.4: an occupied square strictly between a move's destination and the
  mover's king on one half-line contradicts the check the move must answer
  (`false_of_blocked_destination`).
- Lemma 2.4: an occupied square strictly between a discovered check's source and the
  enemy king blocks the unblocked checker (`false_of_blocked_source`).

**Counting.** Before a move, the openable squares are the two bishops' squares and the checker lies on the destination's side of the line through both
kings. So `|disc H|` there counts the bishops on `H` and adds one when
the destination is on `H` (`discHCount_before_move`).

**The paper's two cases.** Name `o`'s squares `X`, `X'` and the opponent's `Y`, `Y'`
so that `X` and `Y` lie on one side `H` and `X'`, `Y'` on the other.
- (i), four rows: `X` is strictly between `Y` and `K`, and `Y'` strictly between `X'`
  and `L`. When the opponent moves into `Y`, `o`'s bishop is on `X'` (blocking at the
  destination), so `|disc H| = 1`. When `o` moves into `X'`, the opponent's is on `Y`,
  so `|disc H| = 2` (`false_of_bishop_case_i`).
- (ii), the last row: `Y` is strictly between `X` and `K`, and `X'` strictly between `Y'`
  and `L`. When `o` moves off `X`, the opponent's bishop is on `Y'` (blocking at the
  source), so `|disc H| = 1`. When the opponent moves off `Y'`, `o`'s is on `X`, so
  `|disc H| = 2` (`false_of_bishop_case_ii`).
Both contradict Proposition 3.8 (`discHCount_eq_of_periodic`). -/

namespace MPC

/-- The side of the line through both kings, in coordinates relative to `o`'s enemy
    king: up to the sign `-forwardSign o`, the cross product with `o`'s king. -/
theorem lineSide_eq_cross (kp0 : Player → Pos) (o : Player) (q : Pos) :
    lineSide (kp0 .sente) (kp0 .gote) q = -forwardSign o *
      ((relTo (kp0 o.opponent) (kp0 o)).1 * (relTo (kp0 o.opponent) q).2 -
        (relTo (kp0 o.opponent) (kp0 o)).2 * (relTo (kp0 o.opponent) q).1) := by
  cases o <;> simp only [lineSide, relTo, forwardSign, Player.opponent] <;> ring

/-- A multiple of a king direction by at least two is neither a king step nor a
    knight's jump. -/
theorem not_step_of_multiple (e : Dir) (he : e ∈ PieceType.king.stepDirs) (c : ℤ) (hc : 2 ≤ c)
    (d : Dir) (hd : d = (c * e.1, c * e.2)) (o : Player) :
    ¬ (d ∈ PieceType.king.stepDirs ∨ ((d.1 = 1 ∨ d.1 = -1) ∧ d.2 = 2 * forwardSign o)) := by
  subst hd
  obtain ⟨e1, e2⟩ := e
  rw [PieceType.mem_king_stepDirs_iff] at he ⊢
  dsimp only at he ⊢
  rcases (show e1 = -1 ∨ e1 = 0 ∨ e1 = 1 by omega) with rfl | rfl | rfl <;>
    rcases (show e2 = -1 ∨ e2 = 0 ∨ e2 = 1 by omega) with rfl | rfl | rfl <;>
    cases o <;> simp only [forwardSign] <;> omega

/-- `q` lies `c` steps from `L` along `e` when its coordinates relative to `K` differ
    from `L`'s by `c • e`. -/
theorem OnRay.of_relTo_sub {K L q : Pos} {e : Dir} {c : ℤ} (he : e ∈ PieceType.king.stepDirs)
    (hc : 0 < c) (h : relTo K q = ((relTo K L).1 + c * e.1, (relTo K L).2 + c * e.2)) :
    OnRay L e c q := by
  refine ⟨he, hc, ?_⟩
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [relTo] at h1 h2
  ext <;> dsimp only <;> linarith

namespace MoveTrace

/-- Corollary 3.4: an occupied square strictly between a move's destination and the
    mover's king, on one half-line from the king, contradicts the check the move must
    answer. -/
theorem false_of_blocked_destination (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (e : Dir) (c c' : ℤ) (Z : Pos)
    (hD : OnRay (kp 0 (tr.before i).turn) e c' (tr.moves i).destination)
    (hZ : OnRay (kp 0 (tr.before i).turn) e c Z) (hcc : c < c')
    (hocc : (tr.before i).board.grid Z ≠ none) : False := by
  obtain ⟨C, X, hX, hXo, hatk, hDC⟩ := tr.checker_before_of_periodic kp ht hs hk hsafe h0 hc hr hp i
  rcases checker_cases _ X C _ _ hatk hDC with ⟨hDeq, hst⟩ |
      ⟨d, n, c'', hC, hc1, hcn, hDe, _, hempty⟩
  · -- A step from the destination cannot reach the king two or more squares away.
    rw [← hDeq] at hst
    apply not_step_of_multiple (-e.1, -e.2) (neg_mem_king_stepDirs hD.1) c' (by
      have := hZ.2.1
      omega) _ ?_ X.owner (stepDir_unit_or_forward_knight _ _ _ hst)
    obtain ⟨_, _, hDe⟩ := hD
    simp only [Pos.dirTo]
    have h1 := congrArg Prod.fst hDe
    have h2 := congrArg Prod.snd hDe
    simp only [Pos.toInt] at h1 h2
    ext <;> dsimp only <;> linarith
  · obtain ⟨hde, hcc'⟩ := OnRay.unique ⟨hC.1, by omega, hDe⟩ hD
    subst hde
    apply hocc
    exact hempty c hZ.2.1 (by omega) Z hZ.2.2

/-- Lemma 2.4: an occupied square strictly between a discovered check's source and the
    enemy king, on one half-line from the king, blocks the unblocked checker. -/
theorem false_of_blocked_source (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (e : Dir) (c c' : ℤ) (Z : Pos)
    (hsrc : OnRay (kp 0 (tr.before i).turn.opponent) e c' src)
    (hZ : OnRay (kp 0 (tr.before i).turn.opponent) e c Z) (hcc : c < c')
    (hocc : (tr.before i).board.grid Z ≠ none) : False := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hd := tr.boardMoveEndpointsDistinct_of_oriented hs hr
  have hu := tr.unblockedChecker_of_not_glares_source_of_periodic kp ht hs hk hsafe h0 hc hr hp
    i src dst promote hm hns
  rw [hm] at hu
  obtain ⟨C, X, _, _, hXb, _, hXo, hatk, hsrcmem, _, _, _⟩ := hu
  have hXo' : X.owner = (tr.before i).turn := by rw [hXo, Player.opponent_opponent]
  rw [hkp i.succ] at hatk hsrcmem
  have hstep : Pos.dirTo C (kp 0 (tr.before i).turn.opponent) ∉
      X.pieceType.stepDirs.map (Dir.forPlayer · X.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 i C X hXb hXo'
    rw [hkp i.castSucc] at h
    exact h
  obtain ⟨d, n, hC, hpc, hiff⟩ := ray_of_attack_not_step _ _ _ C _ hatk hstep
  obtain ⟨c'', hc1, hcn, hsrcEq⟩ := (hiff _).mp hsrcmem
  obtain ⟨hde, hcc'⟩ := OnRay.unique ⟨hC.1, by omega, hsrcEq⟩ hsrc
  subst hde
  -- `Z` is on the checker's path, which is clear after the move.
  have hmem : Z.toInt ∈ slidePath C (kp 0 (tr.before i).turn.opponent) :=
    (hiff _).mpr ⟨c, hZ.2.1, by omega, hZ.2.2⟩
  have hZe := hpc Z.toInt hmem (Pos.onBoard_toInt Z) (Pos.onBoard_toInt Z)
  rw [Pos.toPos_toInt] at hZe
  have hZs : Z ≠ src := by
    rintro rfl
    have := (OnRay.unique hZ hsrc).2
    omega
  by_cases hZd : Z = dst
  · subst hZd
    obtain ⟨piece, hpiece, _⟩ := hs i src Z promote hm
    have h := tr.boardMove_grid_dst ht i src Z promote hm
    rw [hpiece] at h
    rw [h] at hZe
    cases hZe
  · rw [tr.boardMove_grid_other ht i src dst promote Z hm hZs hZd] at hZe
    exact hocc hZe

/-- Under the premises of the main theorem, before a move with `o`'s bishop on `q₁` and
    the opponent's on `q₂`, `|disc H|` counts the bishops on side `s` and adds one when the
    destination is on that side. -/
theorem discHCount_before_move (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (i : Fin tr.len) (s : ℤ) (q₁ q₂ : Pos) (P₁ P₂ : Piece)
    (h₁ : (tr.before i).board.grid q₁ = some P₁) (h₁o : P₁.owner = o)
    (h₁t : P₁.pieceType = .bishop ∨ P₁.pieceType = .horse)
    (h₂ : (tr.before i).board.grid q₂ = some P₂) (h₂o : P₂.owner = o.opponent)
    (h₂t : P₂.pieceType = .bishop ∨ P₂.pieceType = .horse) :
    tr.discHCount kp i.castSucc s =
      (if 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q₁ then 1 else 0) +
      (if 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q₂ then 1 else 0) +
      (if 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) (tr.moves i).destination then 1 else 0) := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, hlen⟩ := hm
  have hq : q₁ ≠ q₂ := by
    rintro rfl
    rw [h₁] at h₂
    cases h₂
    rw [h₁o] at h₂o
    cases o <;> cases h₂o
  -- The openable squares are the two bishops' squares.
  have hopen : tr.openableSquares kp i.castSucc s =
      ({q₁, q₂} : Finset Pos).filter fun q => 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q := by
    ext q
    rw [mem_openableSquares, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hside, hqo⟩
      refine ⟨?_, hside⟩
      obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.mp hqo.1
      have hPt := tr.bishopHorse_of_openable_of_periodic kp hm' h41 hcount _ q hqo P hP
      rcases Player.eq_or_eq_opponent P.owner o with hPo | hPo
      · left
        exact tr.bishopHorse_square_unique_of_periodic kp hm' h41 hcount _ q q₁ P P₁ hP h₁
          (h₁o.trans hPo.symm) hPt h₁t
      · right
        exact tr.bishopHorse_square_unique_of_periodic kp hm' h41 hcount _ q q₂ P P₂ hP h₂
          (h₂o.trans hPo.symm) hPt h₂t
    · rintro ⟨rfl | rfl, hside⟩
      · exact ⟨hside, tr.openable_of_bishopHorse_of_periodic kp hm' h41 hcount _ _ P₁ h₁ h₁t⟩
      · exact ⟨hside, tr.openable_of_bishopHorse_of_periodic kp hm' h41 hcount _ _ P₂ h₂ h₂t⟩
  -- The unique checker is on the destination's side.
  obtain ⟨C, X, hX, hXo, hatkX⟩ := tr.inCheck_before_of_periodic kp ht hk hc hp i
  have hC : tr.IsCheckerAt kp i.castSucc C := ⟨X, hX, by
    rw [show kp i.castSucc X.owner.opponent = kp i.castSucc (tr.before i).turn by
      rw [hXo, Player.opponent_opponent]]
    exact hatkX⟩
  have huC : ∀ C', tr.IsCheckerAt kp i.castSucc C' → C' = C := fun C' h' =>
    tr.checker_unique_of_periodic kp ht hs hk hsafe h0 hc hr hp hlen i.castSucc C' C h' hC
  have hside := tr.destination_side_of_checker kp ht hs hk hsafe h0 hc hr hp i C hC s
  unfold discHCount
  rw [hopen, tr.checkerSquares_card_eq kp i.castSucc s C hC huC, if_congr hside.symm rfl rfl,
    Finset.filter_insert, Finset.filter_singleton]
  generalize (if 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) (tr.moves i).destination then 1
    else 0) = z
  by_cases h1 : 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q₁ <;>
    by_cases h2 : 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) q₂ <;>
    simp [h1, h2, Finset.card_pair hq]

/-- The paper's case (i): `X` strictly between `Y` and `K`, and `Y'` strictly between `X'`
    and `L`, with `X`, `Y` on side `s` and `X'`, `Y'` off it. -/
theorem false_of_bishop_case_i (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (X X' Y Y' : Pos)
    (hXmove : ∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove X X' pr ∧
      (tr.before i).board.grid X = some P ∧ P.owner = o ∧ ¬ tr.GlaresAtEnemyKing kp i.castSucc X)
    (hYmove : ∃ (j : Fin tr.len) (pr : Bool) (P : Piece), tr.moves j = .boardMove Y' Y pr ∧
      (tr.before j).board.grid Y' = some P ∧ P.owner = o.opponent ∧
      ¬ tr.GlaresAtEnemyKing kp j.castSucc Y')
    (hXloc : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
      P.owner = o → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = X ∨ q = X')
    (hYloc : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
      P.owner = o.opponent → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = Y ∨ q = Y')
    (e e' : Dir) (c₁ c₂ c₃ c₄ : ℤ)
    (hX : OnRay (kp 0 o.opponent) e c₁ X) (hY : OnRay (kp 0 o.opponent) e c₂ Y) (h12 : c₁ < c₂)
    (hY' : OnRay (kp 0 o) e' c₃ Y') (hX' : OnRay (kp 0 o) e' c₄ X') (h34 : c₃ < c₄) (s : ℤ)
    (hsX : 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) X)
    (hsY : 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) Y)
    (hsX' : ¬ 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) X')
    (hsY' : ¬ 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) Y') : False := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨i, pri, Pi, hmi, hPi, hPio, hngi⟩ := hXmove
  obtain ⟨j, prj, Pj, hmj, hPj, hPjo, hngj⟩ := hYmove
  have hPit := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount i X X' pri Pi hmi hPi hngi
  have hPjt := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount j Y' Y prj Pj hmj hPj hngj
  have hti : (tr.before i).turn = o := by
    obtain ⟨piece, hpiece, ho⟩ := hs i X X' pri hmi
    rw [hPi] at hpiece
    cases hpiece
    exact ho.symm.trans hPio
  have htj : (tr.before j).turn = o.opponent := by
    obtain ⟨piece, hpiece, ho⟩ := hs j Y' Y prj hmj
    rw [hPj] at hpiece
    cases hpiece
    exact ho.symm.trans hPjo
  -- When the opponent moves into `Y`, `o`'s bishop is on `X'`.
  obtain ⟨q, Q, hQ, hQo, hQt, _⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount j.castSucc o
  have hqX' : q = X' := by
    rcases hXloc _ q Q hQ hQo hQt with rfl | rfl
    · exfalso
      apply tr.false_of_blocked_destination kp ht hs hk hsafe h0 hc hr hp j e c₁ c₂ q
      · rw [htj, hmj]
        exact hY
      · rw [htj]
        exact hX
      · exact h12
      · change (tr.states j.castSucc).board.grid q ≠ none
        rw [hQ]
        exact Option.some_ne_none _
    · rfl
  subst hqX'
  have hj := tr.discHCount_before_move kp hm' h41 hcount o j s q Y' Q Pj hQ hQo hQt hPj hPjo hPjt
  rw [hmj] at hj
  change tr.discHCount kp j.castSucc s = _ + _ + (if 0 < s * lineSide _ _ Y then 1 else 0) at hj
  rw [ite_eq_right hsX', ite_eq_right hsY', ite_eq_left hsY] at hj
  -- When `o` moves into `X'`, the opponent's bishop is on `Y`.
  obtain ⟨r, R, hR, hRo, hRt, _⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount i.castSucc o.opponent
  have hrY : r = Y := by
    rcases hYloc _ r R hR hRo hRt with rfl | rfl
    · rfl
    · exfalso
      apply tr.false_of_blocked_destination kp ht hs hk hsafe h0 hc hr hp i e' c₃ c₄ r
      · rw [hti, hmi]
        exact hX'
      · rw [hti]
        exact hY'
      · exact h34
      · change (tr.states i.castSucc).board.grid r ≠ none
        rw [hR]
        exact Option.some_ne_none _
  subst hrY
  have hi := tr.discHCount_before_move kp hm' h41 hcount o i s X r Pi R hPi hPio hPit hR hRo hRt
  rw [hmi] at hi
  change tr.discHCount kp i.castSucc s = _ + _ + (if 0 < s * lineSide _ _ q then 1 else 0) at hi
  rw [ite_eq_left hsX, ite_eq_left hsY, ite_eq_right hsX'] at hi
  have e1 := tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.castSucc s
  have e2 := tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp j.castSucc s
  omega

/-- The paper's case (ii): `Y` strictly between `X` and `K`, and `X'` strictly between `Y'`
    and `L`, with `X`, `Y` on side `s` and `X'`, `Y'` off it. -/
theorem false_of_bishop_case_ii (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (X X' Y Y' : Pos)
    (hXmove : ∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove X X' pr ∧
      (tr.before i).board.grid X = some P ∧ P.owner = o ∧ ¬ tr.GlaresAtEnemyKing kp i.castSucc X)
    (hYmove : ∃ (j : Fin tr.len) (pr : Bool) (P : Piece), tr.moves j = .boardMove Y' Y pr ∧
      (tr.before j).board.grid Y' = some P ∧ P.owner = o.opponent ∧
      ¬ tr.GlaresAtEnemyKing kp j.castSucc Y')
    (hXloc : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
      P.owner = o → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = X ∨ q = X')
    (hYloc : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
      P.owner = o.opponent → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = Y ∨ q = Y')
    (e e' : Dir) (c₁ c₂ c₃ c₄ : ℤ)
    (hY : OnRay (kp 0 o.opponent) e c₁ Y) (hX : OnRay (kp 0 o.opponent) e c₂ X) (h12 : c₁ < c₂)
    (hX' : OnRay (kp 0 o) e' c₃ X') (hY' : OnRay (kp 0 o) e' c₄ Y') (h34 : c₃ < c₄) (s : ℤ)
    (hsX : 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) X)
    (hsY : 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) Y)
    (hsX' : ¬ 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) X')
    (hsY' : ¬ 0 < s * lineSide (kp 0 .sente) (kp 0 .gote) Y') : False := by
  have hm' := hm
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  obtain ⟨i, pri, Pi, hmi, hPi, hPio, hngi⟩ := hXmove
  obtain ⟨j, prj, Pj, hmj, hPj, hPjo, hngj⟩ := hYmove
  have hPit := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount i X X' pri Pi hmi hPi hngi
  have hPjt := tr.bishopHorse_of_nonGlaring_move kp hm' h41 hcount j Y' Y prj Pj hmj hPj hngj
  have hti : (tr.before i).turn = o := by
    obtain ⟨piece, hpiece, ho⟩ := hs i X X' pri hmi
    rw [hPi] at hpiece
    cases hpiece
    exact ho.symm.trans hPio
  have htj : (tr.before j).turn = o.opponent := by
    obtain ⟨piece, hpiece, ho⟩ := hs j Y' Y prj hmj
    rw [hPj] at hpiece
    cases hpiece
    exact ho.symm.trans hPjo
  -- When `o` moves off `X`, the opponent's bishop is on `Y'`.
  obtain ⟨r, R, hR, hRo, hRt, _⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount i.castSucc o.opponent
  have hrY' : r = Y' := by
    rcases hYloc _ r R hR hRo hRt with rfl | rfl
    · exfalso
      apply tr.false_of_blocked_source kp ht hs hk hsafe h0 hc hr hp i X X' pri hmi hngi e c₁ c₂ r
      · rw [hti]
        exact hX
      · rw [hti]
        exact hY
      · exact h12
      · change (tr.states i.castSucc).board.grid r ≠ none
        rw [hR]
        exact Option.some_ne_none _
    · rfl
  subst hrY'
  have hi := tr.discHCount_before_move kp hm' h41 hcount o i s X r Pi R hPi hPio hPit hR hRo hRt
  rw [hmi] at hi
  change tr.discHCount kp i.castSucc s = _ + _ + (if 0 < s * lineSide _ _ X' then 1 else 0) at hi
  rw [ite_eq_left hsX, ite_eq_right hsY', ite_eq_right hsX'] at hi
  -- When the opponent moves off `Y'`, `o`'s bishop is on `X`.
  obtain ⟨q, Q, hQ, hQo, hQt, _⟩ :=
    tr.exists_openable_bishopHorse_of_periodic kp hm' h41 hcount j.castSucc o
  have hqX : q = X := by
    rcases hXloc _ q Q hQ hQo hQt with rfl | rfl
    · rfl
    · exfalso
      apply tr.false_of_blocked_source kp ht hs hk hsafe h0 hc hr hp j r Y prj hmj hngj e' c₃ c₄ q
      · rw [htj, Player.opponent_opponent]
        exact hY'
      · rw [htj, Player.opponent_opponent]
        exact hX'
      · exact h34
      · change (tr.states j.castSucc).board.grid q ≠ none
        rw [hQ]
        exact Option.some_ne_none _
  subst hqX
  have hj := tr.discHCount_before_move kp hm' h41 hcount o j s q r Q Pj hQ hQo hQt hPj hPjo hPjt
  rw [hmj] at hj
  change tr.discHCount kp j.castSucc s = _ + _ + (if 0 < s * lineSide _ _ Y then 1 else 0) at hj
  rw [ite_eq_left hsX, ite_eq_right hsY', ite_eq_left hsY] at hj
  have e1 := tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp i.castSucc s
  have e2 := tr.discHCount_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp j.castSucc s
  omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- The last case of §5: under the premises of the main theorem there is no such trace.
    Both bishops are in a row of Table 1, and each row contradicts
    Proposition 3.8: rows `(2σ, ρ)`, `(3σ, 2ρ)`, `(σ, 2ρ)` with `t = 1`, and `(σ, 3ρ)`
    by case (i); row `(σ, 2ρ)` with `t = 2` by case (ii). -/
theorem false_of_bishop_rows_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player) :
    False := by
  obtain ⟨t, t', σ, a, b, a', b', hσ, hra, hrb, hra', hrb', hrow, hab, hba, hloc, hab', hba',
    hloc'⟩ := tr.bishop_rows_of_periodic kp hm h41 hcount o
  have hls := lineSide_eq_cross (kp 0) o
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  rw [← hKdef, ← hLdef] at hls hra' hrb' hrow
  rw [← hKdef] at hra hrb
  have hτ := forwardSign_cases o
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = forwardSign o := ⟨_, rfl⟩
  rw [← hτdef] at hls hrb hrb' hrow hτ
  have hσK : ((σ, 0) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hσ with rfl | rfl <;> decide
  have hσK' : ((-σ, 0) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hσ with rfl | rfl <;> decide
  have hρK : ((0, -τ) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hτ with rfl | rfl <;> decide
  have hρK' : ((0, τ) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hτ with rfl | rfl <;> decide
  have hside : ∀ (q : Pos) (v : ℤ × ℤ), relTo K q = v → ∀ s : ℤ,
      s * lineSide (kp 0 .sente) (kp 0 .gote) q =
        s * (-τ * ((relTo K L).1 * v.2 - (relTo K L).2 * v.1)) := by
    intro q v hq s
    rw [hls q, hq]
  have hXloc' : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece),
      (tr.states k).board.grid q = some P →
      P.owner = o → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = b ∨ q = a :=
    fun k q P h1 h2 h3 => (hloc k q P h1 h2 h3).symm
  have hYloc' : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece),
      (tr.states k).board.grid q = some P →
      P.owner = o.opponent → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = b' ∨ q = a' :=
    fun k q P h1 h2 h3 => (hloc' k q P h1 h2 h3).symm
  -- Half-line points from both kings.
  have rayK : ∀ (q : Pos) (e : Dir) (c : ℤ), e ∈ PieceType.king.stepDirs → 0 < c →
      relTo K q = (c * e.1, c * e.2) → OnRay (kp 0 o.opponent) e c q := fun q e c he hc h => by
    rw [← hKdef]
    exact OnRay.of_relTo he hc h
  have rayL : ∀ (q : Pos) (e : Dir) (c : ℤ), e ∈ PieceType.king.stepDirs → 0 < c →
      relTo K q = ((relTo K L).1 + c * e.1, (relTo K L).2 + c * e.2) →
      OnRay (kp 0 o) e c q := fun q e c he hc h => by
    rw [← hLdef]
    exact OnRay.of_relTo_sub he hc h
  unfold BishopRow at hrow
  rcases hrow with ⟨rfl, rfl, hL | hL | hL⟩ | ⟨rfl, rfl, hL | hL⟩
  · -- `l = (2σ, ρ)`, `t = t' = 1`: case (i) with `X = a`, `Y = b'`.
    rw [hL] at hra' hrb' hside
    have r1 := rayK a (σ, 0) 1 hσK one_pos (by rw [hra]; simp)
    have r2 := rayK b' (σ, 0) 2 hσK two_pos (by rw [hrb']; ext <;> simp <;> ring)
    have r3 := rayL a' (-σ, 0) 1 hσK' one_pos (by rw [hra', hL]; ext <;> simp <;> ring)
    have r4 := rayL b (-σ, 0) 2 hσK' two_pos (by rw [hrb, hL]; ext <;> simp <;> ring)
    refine tr.false_of_bishop_case_i kp hm h41 hcount o a b b' a' hab hab' hloc hYloc'
      (σ, 0) (-σ, 0) 1 2 1 2 r1 r2 one_lt_two r3 r4 one_lt_two (-σ) ?_ ?_ ?_ ?_
    · rw [hside a _ hra]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b' _ hrb']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b _ hrb]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a' _ hra']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
  · -- `l = (σ, 2ρ)`, `t = t' = 1`: case (i) with `X = b`, `Y = a'`.
    rw [hL] at hra' hrb' hside
    have r1 := rayK b (0, -τ) 1 hρK one_pos (by rw [hrb]; simp)
    have r2 := rayK a' (0, -τ) 2 hρK two_pos (by rw [hra']; ext <;> simp <;> ring)
    have r3 := rayL b' (0, τ) 1 hρK' one_pos (by rw [hrb', hL]; ext <;> simp <;> ring)
    have r4 := rayL a (0, τ) 2 hρK' two_pos (by rw [hra, hL]; ext <;> simp <;> ring)
    refine tr.false_of_bishop_case_i kp hm h41 hcount o b a a' b' hba hba' hXloc' hloc'
      (0, -τ) (0, τ) 1 2 1 2 r1 r2 one_lt_two r3 r4 one_lt_two σ ?_ ?_ ?_ ?_
    · rw [hside b _ hrb]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a' _ hra']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a _ hra]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b' _ hrb']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
  · -- `l = (σ, 3ρ)`, `t = t' = 1`: case (i) with `X = b`, `Y = a'`.
    rw [hL] at hra' hrb' hside
    have r1 := rayK b (0, -τ) 1 hρK one_pos (by rw [hrb]; simp)
    have r2 := rayK a' (0, -τ) 3 hρK (by norm_num) (by rw [hra']; ext <;> simp <;> ring)
    have r3 := rayL b' (0, τ) 1 hρK' one_pos (by rw [hrb', hL]; ext <;> simp <;> ring)
    have r4 := rayL a (0, τ) 3 hρK' (by norm_num) (by rw [hra, hL]; ext <;> simp <;> ring)
    refine tr.false_of_bishop_case_i kp hm h41 hcount o b a a' b' hba hba' hXloc' hloc'
      (0, -τ) (0, τ) 1 3 1 3 r1 r2 (by norm_num) r3 r4 (by norm_num) σ ?_ ?_ ?_ ?_
    · rw [hside b _ hrb]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a' _ hra']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a _ hra]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b' _ hrb']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
  · -- `l = (3σ, 2ρ)`, `t = t' = 2`: case (i) with `X = a`, `Y = b'`.
    rw [hL] at hra' hrb' hside
    have r1 := rayK a (σ, 0) 2 hσK two_pos (by rw [hra]; ext <;> simp <;> ring)
    have r2 := rayK b' (σ, 0) 3 hσK (by norm_num) (by rw [hrb']; ext <;> simp <;> ring)
    have r3 := rayL a' (-σ, 0) 2 hσK' two_pos (by rw [hra', hL]; ext <;> simp <;> ring)
    have r4 := rayL b (-σ, 0) 3 hσK' (by norm_num) (by rw [hrb, hL]; ext <;> simp <;> ring)
    refine tr.false_of_bishop_case_i kp hm h41 hcount o a b b' a' hab hab' hloc hYloc'
      (σ, 0) (-σ, 0) 2 3 2 3 r1 r2 (by norm_num) r3 r4 (by norm_num) (-σ) ?_ ?_ ?_ ?_
    · rw [hside a _ hra]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b' _ hrb']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b _ hrb]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a' _ hra']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
  · -- `l = (σ, 2ρ)`, `t = t' = 2`: case (ii) with `X = a`, `Y = b'`.
    rw [hL] at hra' hrb' hside
    have r1 := rayK b' (σ, 0) 1 hσK one_pos (by rw [hrb']; ext <;> simp <;> ring)
    have r2 := rayK a (σ, 0) 2 hσK two_pos (by rw [hra]; ext <;> simp <;> ring)
    have r3 := rayL b (-σ, 0) 1 hσK' one_pos (by rw [hrb, hL]; ext <;> simp <;> ring)
    have r4 := rayL a' (-σ, 0) 2 hσK' two_pos (by rw [hra', hL]; ext <;> simp <;> ring)
    refine tr.false_of_bishop_case_ii kp hm h41 hcount o a b b' a' hab hab' hloc hYloc'
      (σ, 0) (-σ, 0) 1 2 1 2 r1 r2 one_lt_two r3 r4 one_lt_two (-σ) ?_ ?_ ?_ ?_
    · rw [hside a _ hra]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b' _ hrb']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside b _ hrb]
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num
    · rw [hside a' _ hra']
      rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> norm_num

/-- No bishop or horse is moved by a discovered check: under the premises of the
    main theorem, Table 1's rows contradict Proposition 3.8. -/
theorem not_openableMove_bishopHorse_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player)
    (pt : PieceType) (_hpt : pt = .bishop ∨ pt = .horse) : ¬ tr.OpenableMoveBy kp o pt :=
  fun _ => tr.false_of_bishop_rows_of_periodic kp hm h41 hcount o

end MoveTrace
end MPC
