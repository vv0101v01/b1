///|
/// batch14_wbtest.mbt — 批次十四白盒測試（剛性拓撲 → 點空間）。
///
/// 每個定理族至少一個測試，數值全部來自 `report14` 的實跑輸出，
/// 因此報告零 [FAIL] 的前提是本檔零 test 失敗。

// ═════════ 模組一：剛性拓撲 / 覆蓋 / 譜空間 / 斯科特 ═════════

test "b14-rigid-axioms" {
  let r = @b14.b14_rigid(@b14.b14_m_sier(), [1])
  // 有理開集族經 ⋂ 閉包化後 = {∅, {0}, X}
  inspect(@b14.b14_full(2), content="3")
  let (g1, g2, g3, g4) = @b14.b14_rigid_axioms(r)
  inspect(g1, content="true")
  inspect(g2, content="true")
  inspect(g3, content="true")
  inspect(g4, content="true")
  inspect(@b14.b14_all_covers(r, @b14.b14_full(2)).length(), content="4")
}

///|
test "b14-tate-acyclic" {
  // 可縮圓盤模型（鏈 0>1>2 的 Alexandrov 拓撲）上常數層被所有覆蓋非循環
  let disc = @b14.b14_m_chain3()
  let (ok1, h1) = @b14.b14_tate_check(disc, [4, 6, 7], 1)
  inspect(ok1, content="true")
  inspect(h1.length(), content="3")
  inspect(h1[0], content="1")
  inspect(h1[1], content="0")
  // 圓環 S¹ 上常數層對覆蓋 [13,14] 有 H¹ = 1
  let circ = @b14.b14_m_circle()
  let (ok2, h2) = @b14.b14_tate_check(circ, [13, 14], 1)
  inspect(ok2, content="false")
  inspect(h2[1], content="1")
  // Čech 上同調依賴覆蓋（不是覆蓋無關的）
  inspect(
    @b14.b14_cover_independent(circ, [13, 14], [12, 15], 1),
    content="false",
  )
  // 但函數層恆非循環
  inspect(@b14.b14_tate_check(circ, [13, 14], 0).0, content="true")
}

///|
test "b14-spectral-space" {
  let (spec, t0, sob, dist, bij, op) = @b14.b14_spectral_check(
    3,
    @b14.b14_chain(3),
  )
  inspect(t0, content="true")
  inspect(sob, content="true")
  inspect(dist, content="true")
  inspect(bij, content="true")
  inspect(op, content="4")
  let (pts, _) = @b14.b14_spec_of_lat(@b14.b14_lat_of_top(spec))
  inspect(pts.n, content="3")
  // 菱形也給 4 點的譜
  let (spec4, _, _, _, _, _) = @b14.b14_spectral_check(4, @b14.b14_diamond())
  let (pts4, _) = @b14.b14_spec_of_lat(@b14.b14_lat_of_top(spec4))
  inspect(pts4.n, content="4")
}

///|
test "b14-scott-and-finite" {
  let v = @b14.b14_v_shape()
  let (_, ok, t0, sob, eq, principal, n) = @b14.b14_scott_check(3, v)
  inspect(ok, content="true")
  inspect(t0, content="true")
  inspect(sob, content="true")
  inspect(eq, content="true")
  // 有限的 V 形上並非所有開集都主開集
  inspect(principal, content="false")
  inspect(n, content="5")
  // 生成元數：V 形 3、不可分 3 點空間 1
  inspect(
    @b14.b14_gen_number(@b14.b14_top(3, @b14.b14_alex_opens(3, v))),
    content="3",
  )
  inspect(@b14.b14_gen_number(@b14.b14_indiscrete(3)), content="1")
}

// ═════════ 模組二：全子範疇 / 史崔特 / 2-單子 / 可近 / 正則 ═════════

///|
test "b14-lex-reflective" {
  let (refl, lex, fails) = @b14.b14_lex_check(3, @b14.b14_chain(3), [0, 2])
  inspect(refl, content="true")
  inspect(lex, content="true")
  inspect(fails, content="0")
  // S = {1} 不是反射子範疇
  inspect(@b14.b14_lex_check(3, @b14.b14_chain(3), [1]).0, content="false")
}

///|
test "b14-idempotents" {
  // [n] 上冪等自映射個數 1, 3, 10, 41
  let pairs = [
    (@b14.b14_idempotents_split(1), 1),
    (@b14.b14_idempotents_split(2), 3),
    (@b14.b14_idempotents_split(3), 10),
    (@b14.b14_idempotents_split(4), 41),
  ]
  for p in pairs {
    inspect(p.0.0, content=p.1.to_string())
    inspect(p.0.1, content="true")
  }
  // 一般 2-範疇中存在不分裂冪等 ⇒ 冪等分裂不可由公理推出
  inspect(@b14.b14_no_splitting_witness(), content="true")
}

///|
test "b14-monad-and-regular" {
  let (nmon, cmp, nalg) = @b14.b14_monad_comparison(3)
  inspect(nmon, content="33")
  inspect(nalg, content="33")
  inspect(cmp, content="true")
  let (r1, r2, r3, rn) = @b14.b14_regular_check()
  inspect(r1, content="true")
  inspect(r2, content="true")
  inspect(r3, content="true")
  inspect(rn, content="395")
  let (fok, fnum, fprod) = @b14.b14_filtered_check()
  inspect(fok, content="true")
  inspect(fnum, content="1296")
  inspect(fprod, content="true")
}

// ═════════ 模組三：t-結構 / 中介擴張 / IC / 對偶 ═════════

///|
test "b14-t-structures" {
  let (a, b, c, n) = @b14.b14_std_ts_check()
  inspect(a, content="true")
  inspect(b, content="true")
  inspect(c, content="true")
  inspect(n, content="147")
  let (p1, p2, p3, p4, pn) = @b14.b14_perverse_check()
  inspect(p1, content="true")
  inspect(p2, content="true")
  inspect(p3, content="true")
  inspect(p4, content="true")
  inspect(pn, content="36")
}

///|
test "b14-intermediate-and-ic" {
  let (ok1, subs1) = @b14.b14_intermediate_check(1)
  inspect(ok1, content="true")
  inspect(subs1, content="3")
  let (ok2, subs2) = @b14.b14_intermediate_check(2)
  inspect(ok2, content="true")
  inspect(subs2, content="9")
  let (lr, rl, adjn) = @b14.b14_adjunction_check()
  inspect(lr, content="true")
  inspect(rl, content="true")
  inspect(adjn, content="24")
  let ((ia, ib), _, _, icd) = @b14.b14_ic_profile(1)
  inspect(ia, content="0")
  inspect(ib, content="1")
  inspect(icd, content="true")
}

///|
test "b14-serre-duality" {
  // h⁰(O(d)) = h¹(O(−d−2))，χ = d+1
  inspect(@b14.b14_h0_p1(3), content="4")
  inspect(@b14.b14_h1_p1(-5), content="4")
  inspect(@b14.b14_h1_p1(3), content="0")
  let (d, chi, n) = @b14.b14_serre_duality_check()
  inspect(d, content="true")
  inspect(chi, content="true")
  inspect(n, content="11")
}

// ═════════ 模組四：𝔸¹ / 動機 / 函子幾何 / 下降 ═════════

///|
test "b14-a1-invariance" {
  let (ok, n, _) = @b14.b14_a1_invariance_check()
  inspect(ok, content="true")
  inspect(n, content="4")
  // 緊支撐上同調不具 𝔸¹-不變性
  let (differs, hc) = @b14.b14_compact_support_counterexample()
  inspect(differs, content="true")
  inspect(hc.length(), content="2")
  inspect(hc[1], content="1")
}

///|
test "b14-milnor-k2" {
  // K^M₂(F_p) = 0（Matsumoto + Quillen）：三例全部平凡
  for p in ([3, 5, 7] : Array[Int32]) {
    let (free, inv) = @b14.b14_milnor_k2(p)
    inspect(free, content="0")
    inspect(inv.length(), content="0")
  }
  // Smith 標準形基本檢查
  let m21 : Array[Array[Int32]] = []
  m21.push([2, 0])
  m21.push([0, 3])
  let (rk21, inv21) = @b14.b14_snf(m21)
  inspect(rk21, content="2")
  inspect(inv21[0], content="1")
  inspect(inv21[1], content="6")
  let m : Array[Array[Int32]] = []
  m.push([6, 0])
  m.push([0, 10])
  let (rk, inv) = @b14.b14_snf(m)
  inspect(rk, content="2")
  inspect(inv[0], content="2")
  inspect(inv[1], content="30")
}

///|
test "b14-yoneda-and-descent" {
  let (yok, yn) = @b14.b14_yoneda_check()
  inspect(yok, content="true")
  inspect(yn, content="8")
  let (p1ok, p1n) = @b14.b14_p1_points(5)
  inspect(p1ok, content="true")
  inspect(p1n, content="6")
  let (d2ok, d2data, d2glob) = @b14.b14_descent_two_cover()
  inspect(d2ok, content="true")
  inspect(d2data, content="2")
  inspect(d2glob, content="2")
  let (d3h1, d3nz) = @b14.b14_descent_three_cover()
  inspect(d3h1, content="1")
  inspect(d3nz, content="true")
  let (h90, hc, hb) = @b14.b14_hilbert90()
  inspect(h90, content="true")
  inspect(hc, content="3")
  inspect(hb, content="3")
}

// ═════════ 模組五：吉羅 / ∞-層化 / 群oid / 穩定化 / 點空間 ═════════

///|
test "b14-giraud-and-sheafification" {
  let (u, d, n) = @b14.b14_giraud_check()
  inspect(u, content="true")
  inspect(d, content="true")
  inspect(n, content="128")
  let (i, l, c, sn) = @b14.b14_sheafification_check()
  inspect(i, content="true")
  inspect(l, content="true")
  inspect(c, content="true")
  inspect(sn, content="8")
  let (e1, e2, en) = @b14.b14_effective_groupoid_check()
  inspect(e1, content="true")
  inspect(e2, content="true")
  inspect(en, content="11")
}

///|
test "b14-stabilization-and-points" {
  let (gc, gck) = @b14.b14_group_completion()
  inspect(gc, content="true")
  inspect(gck, content="5")
  let (s1, s2, s3, sn) = @b14.b14_stabilization_check()
  inspect(s1, content="true")
  inspect(s2, content="true")
  inspect(s3, content="true")
  inspect(sn, content="32")
  // 真懸掛：χ(ΣS¹) = −χ(S¹)
  inspect(@b14.b14_cx_euler(@b14.b14_cx_susp(@b14.b14_s1())), content="0")
  inspect(@b14.b14_cx_euler(@b14.b14_s2()), content="2")
  let (p1, p2, p3, p4) = @b14.b14_pointed_check()
  inspect(p1, content="true")
  inspect(p2, content="true")
  inspect(p3, content="true")
  inspect(p4, content="true")
  inspect(@b14.b14_graph_pi1_rank(1, 3), content="3")
}
