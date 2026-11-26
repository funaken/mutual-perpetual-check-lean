import MPC.Basic.Lemmas
import MPC.Pieces.BishopEdge
/-!
# MPC.Pieces.BishopFrontEdge

A bishop's edge never has its file square in front of the enemy king for its owner. The paper's Table 1 lists only edges with the file square behind
the king, `(0, -t)` in the mover's orientation, and says the candidates are found "as
for Lemma 5.1". The edges with `(0, t)` pass Corollary 3.4 too
(`bishop_configuration_of_periodic`). Lemma 5.1's three-rook count excludes them.

Let `o`'s bishop move between `a = (σt, 0)` and `b = (0, τt)`, where `τ` is `o`'s
forward sign. The candidates for `o`'s king `L` are `(σt, τt)` and, when `t = 1`,
`(2σ, τ)` and `(σ, 2τ)`.
- If `L` lies along the rank through `b`, at least two squares away (`(σt, τt)` with
  `t ≥ 2`, or `(2σ, τ)`), take the move `a → b`.
- If `L = (σ, 2τ)`, take the move `b → a`.
Before that move three distinct squares hold a rook or a dragon:
- the unblocked checker behind the source (`source_slider_far`);
- Proposition 3.3's glaring piece behind the destination
  (`destination_slider_far`);
- the enemy checker, on the line from the destination to `L`.
Each slides along a rank or file, not toward its owner's front. In particular the
piece behind `b = (0, τt)` slides backwards for `o`, so it is not a lance. This
contradicts the piece counts (`bishop_configuration_back_of_periodic`). For the
file square behind `K` the piece behind it may be a lance sliding forward, so this
argument does not apply there, and those edges remain (Table 1). No GameSeq is
used.
-/

namespace MPC

namespace MoveTrace

/-- In a periodic trace satisfying the periodic-check premises, the unblocked checker of a board
    move from a non-glaring square `s` steps from the enemy king along `u` slides back
    along `u` from farther away. -/
theorem source_slider_far (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (u : Dir) (s : ℤ)
    (hsrc : OnRay (kp 0 (tr.before i).turn.opponent) u s src) :
    ∃ (C : Pos) (X : Piece) (n : ℤ), (tr.before i).board.grid C = some X ∧
      X.owner = (tr.before i).turn ∧ OnRay (kp 0 (tr.before i).turn.opponent) u n C ∧
      s < n ∧ ((-u.1, -u.2) : Dir) ∈ X.pieceType.slideDirs.map (Dir.forPlayer · X.owner) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
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
  obtain ⟨d, n, hC, _, hiff⟩ := ray_of_attack_not_step _ _ _ C _ hatk hstep
  obtain ⟨c, hc1, hcn, hsrcEq⟩ := (hiff _).mp hsrcmem
  obtain ⟨hdu, hcs⟩ := OnRay.unique ⟨hC.1, by omega, hsrcEq⟩ hsrc
  subst hdu
  have hslide := slideDir_of_attack_not_step _ _ _ C _ hatk hstep hC
  exact ⟨C, X, n, hXb, hXo', hC, by omega, hslide⟩

/-- Under the same premises, Proposition 3.3's glaring piece behind the destination of
    a board move from a non-glaring square, when the two ends lie on different
    half-lines from the enemy king, stands farther along the destination's half-line
    before the move and slides back along it. -/
theorem destination_slider_far (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos)
    (ht : tr.FollowsTransitions) (hs : tr.BoardMoveSourcesOwned) (hk : tr.KingsWellPlaced kp)
    (hsafe : tr.EveryMoveLeavesOwnKingSafe kp) (h0 : tr.InitialOpponentKingSafe kp)
    (hc : tr.EveryMoveChecksOpponent kp) (hr : tr.BoardMovesFollowCanMoveToOriented)
    (hp : tr.IsPeriodic) (i : Fin tr.len) (src dst : Pos) (promote : Bool)
    (hm : tr.moves i = .boardMove src dst promote)
    (hns : ¬ tr.GlaresAtEnemyKing kp i.castSucc src) (u v : Dir) (s s' : ℤ) (huv : u ≠ v)
    (hdst : OnRay (kp 0 (tr.before i).turn.opponent) u s dst)
    (hsrc : OnRay (kp 0 (tr.before i).turn.opponent) v s' src) :
    ∃ (B : Pos) (Q : Piece) (m : ℤ), (tr.before i).board.grid B = some Q ∧
      Q.owner = (tr.before i).turn ∧ OnRay (kp 0 (tr.before i).turn.opponent) u m B ∧
      s < m ∧ ((-u.1, -u.2) : Dir) ∈ Q.pieceType.slideDirs.map (Dir.forPlayer · Q.owner) := by
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  have hngd : ¬ tr.GlaresAtEnemyKing kp i.succ (tr.moves i).destination := by
    rw [hm]
    exact fun hg => hns (tr.glares_source_of_glares_destination_of_periodic kp ht hs hk hsafe h0
      hc hr hp i src dst promote hm hg)
  obtain ⟨_, _, _, B, Q, e, b', m, _, hown, hray, hB, hbm, hall⟩ :=
    tr.openable_glaring_ray_cyclic_of_periodic kp ht hs hk hsafe h0 hc hr hp i hngd
  rw [hown] at hray hB
  rw [hm] at hray
  change OnRay _ e b' dst at hray
  obtain ⟨heu, hbs⟩ := OnRay.unique hray hdst
  subst heu
  obtain ⟨hQ1, hgl1⟩ := (hall i.succ (cyclicBetween_self_left _ _)).2
  have hBs : B ≠ src := by
    rintro rfl
    exact huv (OnRay.unique hB hsrc).1
  have hBd : B ≠ dst := by
    rintro rfl
    have := (OnRay.unique hB hdst).2
    omega
  have hQb : (tr.before i).board.grid B = some Q := by
    rw [← hQ1]
    exact (tr.boardMove_grid_other ht i src dst promote B hm hBs hBd).symm
  have hstep : Pos.dirTo B (kp 0 (tr.before i).turn.opponent) ∉
      Q.pieceType.stepDirs.map (Dir.forPlayer · Q.owner) := by
    have h := tr.not_stepAttack_of_before kp ht hsafe h0 i B Q hQb hown
    rw [hkp i.castSucc] at h
    exact h
  obtain ⟨Q', hQ', hatkQ⟩ := hgl1
  rw [hQ1] at hQ'
  cases hQ'
  rw [hkp i.succ, show kp 0 Q.owner.opponent = kp 0 (tr.before i).turn.opponent by rw [hown]]
    at hatkQ
  have hslide := slideDir_of_attack_not_step _ _ _ B _ hatkQ hstep hB
  exact ⟨B, Q, m, hQb, hown, hB, by omega, hslide⟩

/-- The configuration of a side's bishop or horse, with the edge's file square behind
    the enemy king for the side: `ρ = -τ`. -/
theorem bishop_configuration_back_of_periodic (tr : MoveTrace)
    (kp : Fin (tr.len + 1) → Player → Pos) (hm : tr.MutualPerpetualCheck kp)
    (h41 : tr.DiscoveredCheckByEachSide kp) (hcount : tr.PieceCountsAtMostTwo) (o : Player) :
    ∃ (t σ ρ : ℤ) (a b : Pos), 1 ≤ t ∧ (σ = 1 ∨ σ = -1) ∧ ρ = -forwardSign o ∧
      relTo (kp 0 o.opponent) a = (σ * t, 0) ∧ relTo (kp 0 o.opponent) b = (0, ρ * t) ∧
      0 < σ * (relTo (kp 0 o.opponent) (kp 0 o)).1 ∧
      0 < ρ * (relTo (kp 0 o.opponent) (kp 0 o)).2 ∧
      KingCandidate (forwardSign o) σ ρ t (relTo (kp 0 o.opponent) (kp 0 o)) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove a b pr ∧
        (tr.before i).board.grid a = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc a) ∧
      (∃ (i : Fin tr.len) (pr : Bool) (P : Piece), tr.moves i = .boardMove b a pr ∧
        (tr.before i).board.grid b = some P ∧ P.owner = o ∧
        ¬ tr.GlaresAtEnemyKing kp i.castSucc b) ∧
      (∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece), (tr.states k).board.grid q = some P →
        P.owner = o → (P.pieceType = .bishop ∨ P.pieceType = .horse) → q = a ∨ q = b) := by
  have hm' := hm
  obtain ⟨t, σ, ρ, a, b, ht1, hσ, hρ, hra, hrb, hl1, hl2, hcand, hab, hba, hloc⟩ :=
    tr.bishop_configuration_of_periodic kp hm h41 hcount o
  have hτ := forwardSign_cases o
  by_cases hback : ρ = -forwardSign o
  · exact ⟨t, σ, ρ, a, b, ht1, hσ, hback, hra, hrb, hl1, hl2, hcand, hab, hba, hloc⟩
  exfalso
  have hρτ : ρ = forwardSign o := by rcases hρ with h | h <;> rcases hτ with h' | h' <;> omega
  obtain ⟨ht, hs, hk, hsafe, h0, hc, hr, hp, _, _⟩ := hm
  have hkp := tr.kingPos_eq_of_periodic kp ht hs hk hsafe h0 hc hr hp
  obtain ⟨K, hKdef⟩ : ∃ K, K = kp 0 o.opponent := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L, L = kp 0 o := ⟨_, rfl⟩
  rw [← hKdef, ← hLdef] at hl1 hl2 hcand
  rw [← hKdef] at hra hrb
  have hfar := tr.relTo_king_far_of_periodic kp hm' o
  rw [← hKdef, ← hLdef] at hfar
  have hσK : ((σ, 0) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hσ with rfl | rfl <;> decide
  have hρK : ((0, ρ) : Dir) ∈ PieceType.king.stepDirs := by
    rcases hρ with rfl | rfl <;> decide
  have hrayA : OnRay K (σ, 0) t a := OnRay.of_relTo hσK (by omega) (by rw [hra]; simp [mul_comm])
  have hrayB : OnRay K (0, ρ) t b := OnRay.of_relTo hρK (by omega) (by rw [hrb]; simp [mul_comm])
  have hRD : ∀ (k : Fin (tr.len + 1)) (q : Pos) (P : Piece) (sd : Dir),
      (tr.states k).board.grid q = some P →
      sd ∈ P.pieceType.slideDirs.map (Dir.forPlayer · P.owner) → (sd.1 = 0 ∨ sd.2 = 0) →
      sd ≠ (0, forwardSign P.owner) → q ∈ tr.rookDragonSquares k :=
    fun k q P sd hq h1 h2 h3 =>
      tr.mem_rookDragonSquares_of k q P hq (rookDragon_of_slideDir _ _ sd h1 h2 h3)
  have hrel : ∀ {q q' : Pos}, q = q' → relTo K q = relTo K q' := fun h => by rw [h]
  have hτX : ∀ X : Piece, X.owner = o.opponent → forwardSign X.owner = -ρ := by
    intro X hX
    rw [hX, forwardSign_opponent, hρτ]
  -- The candidates with the file square in front of `K`.
  have hcase : (∃ mm : ℤ, 2 ≤ mm ∧ relTo K L = (σ * mm, ρ * t)) ∨
      (t = 1 ∧ relTo K L = (σ, 2 * ρ)) := by
    unfold KingCandidate at hcand
    rcases hcand with h | ⟨h1, h | h | ⟨h3, _⟩⟩ | ⟨_, h3, _⟩
    · refine Or.inl ⟨t, ?_, h⟩
      by_contra hlt
      apply hfar
      rw [h]
      dsimp only
      rcases hσ with rfl | rfl <;> rcases hρ with rfl | rfl <;> omega
    · exact Or.inr ⟨h1, h⟩
    · exact Or.inl ⟨2, le_refl _, by rw [h, h1]; ring_nf⟩
    · rcases hτ with h' | h' <;> rcases hρ with h'' | h'' <;> omega
    · rcases hτ with h' | h' <;> rcases hρ with h'' | h'' <;> omega
  have hnz : ∀ x : ℤ, (x = 1 ∨ x = -1) → x ≠ 0 := by omega
  rcases hcase with ⟨mm, hmm, hL⟩ | ⟨ht1', hL⟩
  · -- `L` along the rank through `b`: three rooks or dragons before `a → b`.
    obtain ⟨iA, prA, PA, hmA, hpA, hPAo, hngA⟩ := hab
    have htA : (tr.before iA).turn = o := by
      obtain ⟨piece, hpiece, ho⟩ := hs iA a b prA hmA
      rw [hpA] at hpiece
      cases hpiece
      exact ho.symm.trans hPAo
    have hKA : kp 0 (tr.before iA).turn.opponent = K := by rw [htA, hKdef]
    obtain ⟨C1, X1, n1, hX1, hX1o, hC1, hn1, hsl1⟩ :=
      tr.source_slider_far kp ht hs hk hsafe h0 hc hr hp iA a b prA hmA hngA (σ, 0) t
        (by rw [hKA]; exact hrayA)
    obtain ⟨B2, Q2, m2, hQ2, hQ2o, hB2, hm2, hsl2⟩ :=
      tr.destination_slider_far kp ht hs hk hsafe h0 hc hr hp iA a b prA hmA hngA (0, ρ) (σ, 0) t t
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; rcases hσ with h' | h' <;>
          omega)
        (by rw [hKA]; exact hrayB) (by rw [hKA]; exact hrayA)
    rw [hKA] at hC1 hB2
    dsimp only at hsl1 hsl2
    simp only [neg_zero] at hsl1 hsl2
    obtain ⟨CA, XA, hXA, hXAo, hatkA, hDA⟩ :=
      tr.checker_before_of_periodic kp ht hs hk hsafe h0 hc hr hp iA
    rw [htA, ← hLdef] at hatkA
    rw [htA, hmA, ← hLdef] at hDA
    rw [htA] at hXAo
    have hbL : OnRay L (-σ, 0) mm b := by
      refine ⟨neg_mem_king_stepDirs hσK, by omega, ?_⟩
      have e1 := congrArg Prod.fst hrb
      have e2 := congrArg Prod.snd hrb
      have f1 := congrArg Prod.fst hL
      have f2 := congrArg Prod.snd hL
      simp only [relTo] at e1 e2 f1 f2
      ext <;> dsimp only <;> linarith
    rcases checker_cases _ XA CA L b hatkA hDA with ⟨hbC, hst⟩ | ⟨d, n, c, hCa, hc1, hcn, hDe,
        hsl3, _⟩
    · subst hbC
      have hd : Pos.dirTo b L = (σ * mm, 0) := by
        have e1 := congrArg Prod.fst hrb
        have e2 := congrArg Prod.snd hrb
        have f1 := congrArg Prod.fst hL
        have f2 := congrArg Prod.snd hL
        simp only [relTo, Pos.toInt] at e1 e2 f1 f2
        simp only [Pos.dirTo]
        ext <;> dsimp only <;> linarith
      rw [hd] at hst
      rcases stepDir_unit_or_forward_knight _ _ _ hst with hu | ⟨_, h2⟩
      · rw [PieceType.mem_king_stepDirs_iff] at hu
        dsimp only at hu
        rcases hσ with rfl | rfl <;> omega
      · rw [hτX XA hXAo] at h2
        dsimp only at h2
        rcases hρ with rfl | rfl <;> omega
    · obtain ⟨hd, hc⟩ := OnRay.unique ⟨hCa.1, by omega, hDe⟩ hbL
      subst hd
      dsimp only at hsl3
      simp only [neg_neg, neg_zero] at hsl3
      have hCA_rd := hRD _ CA XA (σ, 0) hXA hsl3 (Or.inr rfl)
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; exact hnz σ hσ this)
      have hC1_rd := hRD _ C1 X1 (-σ, 0) hX1 hsl1 (Or.inr rfl)
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; rcases hσ with h' | h' <;>
          omega)
      have hB2_rd := hRD _ B2 Q2 (0, -ρ) hQ2 hsl2 (Or.inl rfl)
        (by rw [hQ2o, htA, ← hρτ]; intro h; have := congrArg Prod.snd h; dsimp only at this;
            rcases hρ with h' | h' <;> omega)
      have rC1 := hC1.relTo_eq
      have rB2 := hB2.relTo_eq
      have rCA : relTo K CA = ((relTo K L).1 + n * -σ, (relTo K L).2 + n * 0) := by
        obtain ⟨_, _, hCe⟩ := hCa
        simp only [relTo, hCe]
        ext <;> dsimp only <;> ring
      rw [hL] at rCA
      apply tr.false_of_three_rookDragon hcount iA.castSucc C1 B2 CA ?_ ?_ ?_ hC1_rd hB2_rd
        hCA_rd
      · intro h
        have := hrel h
        rw [rC1, rB2] at this
        have := congrArg Prod.snd this
        dsimp only at this
        rcases hρ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rC1, rCA] at this
        have := congrArg Prod.snd this
        dsimp only at this
        rcases hρ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rB2, rCA] at this
        have := congrArg Prod.snd this
        dsimp only at this
        rcases hρ with rfl | rfl <;> omega
  · -- `L = (σ, 2ρ)` and `t = 1`: three rooks or dragons before `b → a`.
    subst ht1'
    obtain ⟨iB, prB, PB, hmB, hpB, hPBo, hngB⟩ := hba
    have htB : (tr.before iB).turn = o := by
      obtain ⟨piece, hpiece, ho⟩ := hs iB b a prB hmB
      rw [hpB] at hpiece
      cases hpiece
      exact ho.symm.trans hPBo
    have hKB : kp 0 (tr.before iB).turn.opponent = K := by rw [htB, hKdef]
    obtain ⟨C1, X1, n1, hX1, hX1o, hC1, hn1, hsl1⟩ :=
      tr.source_slider_far kp ht hs hk hsafe h0 hc hr hp iB b a prB hmB hngB (0, ρ) 1
        (by rw [hKB]; exact hrayB)
    obtain ⟨B2, Q2, m2, hQ2, hQ2o, hB2, hm2, hsl2⟩ :=
      tr.destination_slider_far kp ht hs hk hsafe h0 hc hr hp iB b a prB hmB hngB (σ, 0) (0, ρ) 1 1
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; rcases hσ with h' | h' <;>
          omega)
        (by rw [hKB]; exact hrayA) (by rw [hKB]; exact hrayB)
    rw [hKB] at hC1 hB2
    dsimp only at hsl1 hsl2
    simp only [neg_zero] at hsl1 hsl2
    obtain ⟨CB, XB, hXB, hXBo, hatkB, hDB⟩ :=
      tr.checker_before_of_periodic kp ht hs hk hsafe h0 hc hr hp iB
    rw [htB, ← hLdef] at hatkB
    rw [htB, hmB, ← hLdef] at hDB
    rw [htB] at hXBo
    have haL : OnRay L (0, -ρ) 2 a := by
      refine ⟨neg_mem_king_stepDirs hρK, two_pos, ?_⟩
      have e1 := congrArg Prod.fst hra
      have e2 := congrArg Prod.snd hra
      have f1 := congrArg Prod.fst hL
      have f2 := congrArg Prod.snd hL
      simp only [relTo] at e1 e2 f1 f2
      ext <;> dsimp only <;> linarith
    rcases checker_cases _ XB CB L a hatkB hDB with ⟨haC, hst⟩ | ⟨d, n, c, hCa, hc1, hcn, hDe,
        hsl3, _⟩
    · subst haC
      have hd : Pos.dirTo a L = (0, 2 * ρ) := by
        have e1 := congrArg Prod.fst hra
        have e2 := congrArg Prod.snd hra
        have f1 := congrArg Prod.fst hL
        have f2 := congrArg Prod.snd hL
        simp only [relTo, Pos.toInt] at e1 e2 f1 f2
        simp only [Pos.dirTo]
        ext <;> dsimp only <;> linarith
      rw [hd] at hst
      rcases stepDir_unit_or_forward_knight _ _ _ hst with hu | ⟨h1, _⟩
      · rw [PieceType.mem_king_stepDirs_iff] at hu
        dsimp only at hu
        rcases hρ with rfl | rfl <;> omega
      · dsimp only at h1
        omega
    · obtain ⟨hd, hc⟩ := OnRay.unique ⟨hCa.1, by omega, hDe⟩ haL
      subst hd
      dsimp only at hsl3
      simp only [neg_neg, neg_zero] at hsl3
      have hCB_rd := hRD _ CB XB (0, ρ) hXB hsl3 (Or.inl rfl)
        (by rw [hτX XB hXBo]; intro h; have := congrArg Prod.snd h; dsimp only at this;
            rcases hρ with h' | h' <;> omega)
      have hC1_rd := hRD _ C1 X1 (0, -ρ) hX1 hsl1 (Or.inl rfl)
        (by rw [hX1o, htB, ← hρτ]; intro h; have := congrArg Prod.snd h; dsimp only at this;
            rcases hρ with h' | h' <;> omega)
      have hB2_rd := hRD _ B2 Q2 (-σ, 0) hQ2 hsl2 (Or.inr rfl)
        (by intro h; have := congrArg Prod.fst h; dsimp only at this; rcases hσ with h' | h' <;>
          omega)
      have rC1 := hC1.relTo_eq
      have rB2 := hB2.relTo_eq
      have rCB : relTo K CB = ((relTo K L).1 + n * 0, (relTo K L).2 + n * -ρ) := by
        obtain ⟨_, _, hCe⟩ := hCa
        simp only [relTo, hCe]
        ext <;> dsimp only <;> ring
      rw [hL] at rCB
      apply tr.false_of_three_rookDragon hcount iB.castSucc C1 B2 CB ?_ ?_ ?_ hC1_rd hB2_rd
        hCB_rd
      · intro h
        have := hrel h
        rw [rC1, rB2] at this
        have := congrArg Prod.fst this
        dsimp only at this
        rcases hσ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rC1, rCB] at this
        have := congrArg Prod.fst this
        dsimp only at this
        rcases hσ with rfl | rfl <;> omega
      · intro h
        have := hrel h
        rw [rB2, rCB] at this
        have := congrArg Prod.fst this
        dsimp only at this
        rcases hσ with rfl | rfl <;> omega

end MoveTrace
end MPC
