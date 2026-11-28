///|
/// batch12_wbtest.mbt — 批次十二白盒測試（CZFM / 哥德爾 / KPM・馬洛 / 列維 / 全域公理）。
///
/// 全部數值由 foundation/b12 與 axioms 的函式重新計算，與 report12 的報告數字交叉核對。
/// 特別注意：這裡也檢查「誠實性」——凡屬永不可得的結論（有限域上的馬洛、G2 的 Con），
/// 測試必須確認程式回報的是「得不到」而不是「得到了」。

///|
/// 模組一：CZFM 層級與雙重視角。
test "batch12_m1_czfm" {
  let lv = b12_czfm_levels(6)
  // V_0..V_5 的基數：0,1,2,4,16,65536
  assert_eq(lv[0].1, 0)
  assert_eq(lv[1].1, 1)
  assert_eq(lv[2].1, 2)
  assert_eq(lv[3].1, 4)
  assert_eq(lv[4].1, 16)
  assert_eq(lv[5].1, 65536)
  // 有限基數皆非不可達
  for k in 2..<=12 {
    assert_false(b12_inaccessible(k).2)
  }
  assert_false(b12_inaccessible(1).2)
  // 4 = 2² 不正則；7 正則但幂集不封閉
  assert_false(b12_inaccessible(4).0)
  assert_true(b12_inaccessible(7).0)
  assert_false(b12_inaccessible(7).1)
  // 正則基數（有限）= 質數
  assert_eq(b12_regular_up_to(20), [2, 3, 5, 7, 11, 13, 17, 19])
  // 雙重視角的不變量
  let sizes = [0, 1, 2, 4, 16, 65536]
  let (dual, resid) = b12_dual_ok(sizes)
  assert_true(dual)
  assert_eq(resid, 0)
  assert_eq(b12_bottom_up(sizes), [0, 1, 1, 2, 12, 65520])
  assert_eq(b12_top_down(sizes), [0, 2, 2, 4, 4096, 0])
}

///|
/// 模組一：等一致性轉譯網路與顯式表示。
test "batch12_m1_translation" {
  let m : Array[Array[Int32]] = [
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1],
    [1, 0, 0, 0],
  ]
  assert_true(b12_is_perm_matrix(m))
  let sigma = b12_translation_map(m)
  assert_eq(sigma, [1, 2, 3, 0])
  assert_eq(b12_inv_perm(sigma), [3, 0, 1, 2])
  // 4 循環：σ⁴ = id
  let mut cur = sigma
  for _ in 0..<3 {
    let nxt : Array[Int32] = []
    for i in 0..<cur.length() {
      nxt.push(sigma[cur[i]])
    }
    cur = nxt
  }
  assert_eq(cur, [0, 1, 2, 3])
  // 鄰接表連通性
  let adj : Array[Array[Int32]] = [[1], [2], [3], [0]]
  assert_true(b12_network_complete(adj))
  let frag : Array[Array[Int32]] = [[1], [0], [3], [2]]
  assert_false(b12_network_complete(frag))
  // 非置換矩陣必須被拒
  let bad : Array[Array[Int32]] = [[1, 1], [0, 0]]
  assert_false(b12_is_perm_matrix(bad))
  let (f, b, eq) = b12_equiconsistent(true, true)
  assert_true(f && b && eq)
  assert_false(b12_equiconsistent(true, false).2)
}

///|
/// 模組二：哥德爾編碼與可證性。
test "batch12_m2_godel" {
  // 編碼／解碼互逆
  let g = go_godel_of_names(["S", "0", "=", "S", "0"])
  assert_eq(go_godel(go_ungodel(g)), g)
  assert_eq(go_ungodel(g), [2, 1, 5, 2, 1])
  assert_eq(g, 20212500L)
  // β 函數（CRT）正確性
  let seq = [3, 1, 4, 1, 5, 9, 2, 6]
  let (c, d) = go_beta_encode(seq)
  for i in 0..<seq.length() {
    assert_eq(go_beta_val(c, d, i), seq[i].to_int64())
  }
  // Cantor 配對往返
  for a in 0..<6 {
    for b in 0..<6 {
      let (x, y) = go_cantor_unpair(go_cantor_pair(a, b))
      assert_eq(x, a)
      assert_eq(y, b)
    }
  }
  // 公理集與證明檢查
  let ax = b12_axiom_codes()
  assert_eq(ax.length(), 5)
  let phi = go_ungodel(ax[0])
  assert_true(b12_proof_check([phi], phi).0)
  assert_false(b12_proof_check([go_ungodel(ax[1])], phi).0)
  // 深度 2 的候選數 = 5 公理 + 1 MP
  assert_eq(b12_derive_candidates(2).length(), 6)
  // 可證性：公理可證、其否定不可證
  assert_true(b12_provable(2, phi).0)
  assert_false(
    b12_provable(2, go_ungodel(go_godel_of_names(["¬", "0", "=", "0"]))).0,
  )
  // G2：Con 在所有深度都搜尋失敗（誠實性檢查）
  for b in b12_g2_all_depths(5) {
    assert_false(b)
  }
}

///|
/// 模組三：KPM、弱馬洛記號、塌縮、馬洛階梯。
test "batch12_m3_kpm" {
  assert_false(b12_admissible(0).2)
  assert_false(b12_admissible(5).2)
  assert_true(b12_kpm_mark(3, 1, 2))
  assert_false(b12_kpm_mark(3, 3, 1))
  assert_false(b12_kpm_mark(-1, 0, 0))
  // 記號單射性
  assert_true(b12_notation_injective([(0, 0), (0, 7), (1, 0), (2, 3)]))
  assert_false(b12_notation_injective([(1, 0), (0, 8)]))
  // 塌縮：高層嚴格遞增、0 層為恆等（不動點）
  assert_eq(b12_collapse(2, 1, 4), [10, 14, 18, 22])
  assert_eq(b12_collapse(0, 1, 4), [8, 8, 8, 8])
  assert_eq(b12_collapse_fixpoints(0, 1, 4), 3)
  assert_eq(b12_collapse_fixpoints(2, 1, 4), 0)
  // 馬洛階梯
  assert_eq(b12_strength_ladder(5), [0, 1, 2, 3, 4])
  assert_true(b12_omega_mahlo(b12_strength_ladder(7)).0)
  assert_false(b12_omega_mahlo([0, 2, 1]).0)
  assert_eq(b12_n_mahlo(4), (true, 4))
  assert_false(b12_n_mahlo(-1).0)
  // KPM 字典序
  assert_eq(b12_kpm_cmp((1, 0, 0), (2, 0, 0)), -1)
  assert_eq(b12_kpm_cmp((1, 1, 2), (1, 1, 2)), 0)
  assert_eq(b12_kpm_cmp((2, 0, 0), (1, 9, 9)), 1)
}

///|
/// 模組四：Σ_n-正確、列維綱領、CU、朗蘭茲約束。
test "batch12_m4_levy" {
  let real_tbl : Array[Array[Int32]] = [[1, 1], [1, 0], [1, 1]]
  let same = b12_sigma_n_correct(real_tbl, real_tbl, 3)
  assert_true(same.0)
  assert_eq(same.1, 3)
  assert_eq(same.2, 0)
  let skew : Array[Array[Int32]] = [[1, 1], [1, 1], [1, 0]]
  assert_false(b12_sigma_n_correct(skew, real_tbl, 3).0)
  // Σ₁ 絕對性
  let (abs_ok, kept, lost) = b12_levy_lambda([1, 2, 3], [1, 2, 3, 4])
  assert_true(abs_ok)
  assert_eq(kept, 3)
  assert_eq(lost, 0)
  assert_false(b12_levy_lambda([1, 2, 9], [1, 2, 3]).0)
  // CU：無界閉集
  let full : Array[Bool] = [true, true, true, true, true]
  assert_true(b12_club_set(full).2)
  let hole : Array[Bool] = [true, false, true]
  assert_false(b12_club_set(hole).2)
  // 閉包冪等且含 0 時填滿
  let cl = b12_club_closure([true, false, false, false])
  assert_eq(cl, [true, true, true, true])
  assert_eq(b12_club_closure(cl), cl)
  // 種子不含 0 ⇒ 閉包不動
  assert_eq(b12_club_closure([false, true, true]), [false, true, true])
  // 朗蘭茲約束
  let pairs = [(2, 1), (3, 1), (5, 2), (7, 3), (11, 4)]
  let gal = b12_galois_labels(pairs)
  let aut = b12_automorphic_labels(pairs)
  assert_true(b12_lc_complete(gal, aut))
  assert_eq(b12_lc_pair(gal, aut), (5, 5))
  // 多一項即完備性失敗
  let shorter : Array[(Int32, Int32)] = [(2, 1), (3, 1), (5, 2), (7, 3)]
  assert_false(b12_lc_complete(gal, b12_automorphic_labels(shorter)))
  // 互逆雙射
  for (p, a) in pairs {
    assert_true(b12_lc_involution_ok(p, a))
  }
}

///|
/// 模組五：全域公理與三完備（含誠實性：殘餘缺口必須被標記）。
test "batch12_m5_axioms" {
  let ax = @axioms.b12_axioms()
  assert_eq(ax.length(), 3)
  assert_eq(ax[0].tag, "GA-1")
  assert_eq(ax[1].tag, "GA-2")
  assert_eq(ax[2].tag, "GA-3")
  // GA-2（馬洛）必須被標為永不可得
  assert_true(ax[1].status is @axioms.Residual)
  let (ok, checked, resid) = @axioms.b12_axiom_audit()
  assert_true(ok)
  assert_eq(checked, 2)
  assert_eq(resid, 1)
  // GA-1：邏輯鏈有界可達
  assert_true(@axioms.b12_lct_holds([1, 2, 3, 4], 4))
  assert_false(@axioms.b12_lct_holds([1, 2, 9], 4))
  assert_false(@axioms.b12_lct_holds([], 4))
  assert_eq(@axioms.b12_logic_chain([2, 4, 3]), (3, 4))
  assert_eq(@axioms.b12_reflect_count([3, 2, 5], [2, 3, 5]), 2)
  // GA-2：有限域上不存在馬洛基數（誠實見證）
  for k in 0..<=50 {
    assert_false(@axioms.b12_mahlo_finite(k))
  }
  let (finite_ok, gap) = @axioms.b12_mahlo_gap()
  assert_false(finite_ok)
  assert_true(gap.length() > 0)
  // 反思強度序單調
  assert_true(@axioms.b12_reflect_monotone(6).0)
  assert_eq(@axioms.b12_reflect_rank("inaccessible"), 1)
  assert_eq(@axioms.b12_reflect_rank("mahlo"), 4)
  assert_eq(@axioms.b12_reflect_rank("omega_mahlo"), 6)
  assert_eq(@axioms.b12_reflect_rank("unknown"), 0)
  // 三完備：自洽、圖靈-約旦、萬有可達
  let tc = @axioms.b12_three_completeness([0, 1, 2, 3], 3)
  assert_true(tc.0 && tc.1 && tc.2 && tc.3)
  assert_false(@axioms.b12_three_completeness([0, 0, 1], 1).1)
  assert_false(@axioms.b12_three_completeness([0, 1, 9], 3).2)
  // G1：候選句非公理且不可在深度內證明
  let g1 = @axioms.b12_g1_gap(5, 3)
  assert_eq(g1, (5, 3, 4))
  // G2：任何深度都搜不到 Con 的證明
  assert_false(@axioms.b12_g2_search(100).1)
}

///|
/// 報告層契約：report12 必須含 19 條定理與 11 條演算法、且零 [FAIL]。
test "batch12_report_contract" {
  let r = report12()
  assert_eq(b_sh_count_sub(r, "[FAIL]"), 0)
  for
    t in [
      "T411", "T412", "T413", "T414", "T415", "T416", "T417", "T418", "T419", "T420",
      "T421", "T422", "T423", "T424", "T425", "T426", "T427", "T428", "T429",
    ] {
    assert_true(b_sh_count_sub(r, t) > 0)
  }
  for
    a in [
      "A65", "A66", "A67", "A68", "A69", "A70", "A71", "A72", "A73", "A74", "A75",
    ] {
    assert_true(b_sh_count_sub(r, a) > 0)
  }
  // 誠實性：殘餘缺口必須出現在報告中
  assert_true(b_sh_count_sub(r, "殘餘缺口") > 0)
  assert_true(b_sh_count_sub(r, "永不可得") > 0)
}
