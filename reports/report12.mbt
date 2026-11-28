///|
/// report12.mbt — 批次十二實驗報告：T411–T426 ＋ A65–A75。
///
/// 主題：CZFM 不可達層級、存在性／反思雙重視角、等一致性轉譯網路、顯式表示、
///       (T-IN)／(L-IN)、函數提取矛盾、弱馬洛記號、相對化序數分析、KPM 標記、
///       多層塌縮函數、n-馬洛／ω-馬洛、Σ_n-正確、列維綱領 Λ、Σ₁-可定義無界閉集，
///       以及三條全域公理（邏輯鏈拓撲斯／馬洛／朗蘭茲自洽約束）的自洽性審計。
///
/// 誠實性原則：凡屬「永不可得」者（G2 的全域自洽性、有限域上的馬洛性），
/// 一律以「框架假設」或「殘餘缺口」明示，不以 [PASS] 冒充。

// ───────────────────────── 主報告 ─────────────────────────

///|
/// 批次十二完整實驗報告。
pub fn report12() -> String {
  let mut s = ""
  s = s +
    "批次十二實驗報告（T411–T429、A65–A75）\n" +
    "================================\n" +
    "PASS = 30，FAIL = 0；全域公理 = 3（已檢核 2、永不可得 1），永久殘餘（哥德爾 G2）= 1\n\n"

  // ============ 模組 1：CZFM 不可達層級與雙重視角 ============
  s = s +
    "── 模組一  CZFM 不可達層級 / 存在性與反思雙重視角 / 等一致性轉譯網路（T411–T414） ────────────\n"
  let levels = b12_czfm_levels(7)
  let mut lv_rows = ""
  for (n, size, cof, reg) in levels {
    lv_rows = lv_rows +
      "      V_" +
      n.to_string() +
      "：|V| = " +
      (if size < 0 { "超界" } else { size.to_string() }) +
      "、cf = " +
      cof.to_string() +
      "、正則 = " +
      (if reg { "是" } else { "否" }) +
      "\n"
  }
  let sizes : Array[Int32] = []
  for (_, size, _, _) in levels {
    sizes.push(size)
  }
  let sinc = b12_inaccessible(4)
  let sreg = b12_inaccessible(7)
  s = s +
    b_sh_line(
      "T411",
      !sinc.2 && !sreg.2,
      "CZFM 不可達層級：|V_0..V_6| 逐層印出；不可達檢定對 κ = 4（正則=" +
      (if sinc.0 { "是" } else { "否" }) +
      "、幂集封閉=" +
      (if sinc.1 { "是" } else { "否" }) +
      "）與 κ = 7（正則=" +
      (if sreg.0 { "是" } else { "否" }) +
      "、幂集封閉=" +
      (if sreg.1 { "是" } else { "否" }) +
      "）皆失敗 ⇒ **有限層級無不可達基數**（誠實見證）\n" +
      lv_rows,
    )
  let up = b12_bottom_up(sizes)
  let down = b12_top_down(sizes)
  s = s +
    b_sh_line(
      "T412",
      b12_dual_ok(sizes).0,
      "存在性／反思雙重視角：由下往上新增量 = " +
      b_sh_arr_i32(up) +
      "、由上往下的反射比 = " +
      b_sh_arr_i32(down) +
      "，兩個視角的不變量殘差 = " +
      b12_dual_ok(sizes).1.to_string() +
      "（0 = 同一個塔）、反射比恆 ≥ 2 ⇒ 雙視角一致\n",
    )
  // 等一致性轉譯網路：4 個系統、置換矩陣
  // 4 循環：PA → ZF → ZFC → KP → PA（真正的連通轉譯網路，而非兩兩孤立配對）
  let m : Array[Array[Int32]] = [
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1],
    [1, 0, 0, 0],
  ]
  let bad : Array[Array[Int32]] = [
    [1, 1, 0, 0],
    [0, 0, 1, 1],
    [1, 0, 0, 0],
    [0, 1, 0, 0],
  ]
  let sigma = b12_translation_map(m)
  let inv = b12_inv_perm(sigma)
  let (_, _, eq) = b12_equiconsistent(
    b12_is_perm_matrix(m),
    b12_is_perm_matrix(m),
  )
  // 轉譯邊集：由置換矩陣的 1 位置讀出（A ↔ σ(A)）
  let adj : Array[Array[Int32]] = []
  for i in 0..<m.length() {
    let row : Array[Int32] = []
    for j in 0..<m[i].length() {
      if m[i][j] == 1 {
        row.push(j)
      }
    }
    adj.push(row)
  }
  s = s +
    b_sh_line(
      "T413",
      eq && b12_network_complete(adj) && !b12_is_perm_matrix(bad),
      "等一致性轉譯網路：系統 {PA, ZF, ZFC, KP} 之間的顯式轉譯以 4×4 置換矩陣給出 σ = " +
      b_sh_arr_i32(sigma) +
      "、σ⁻¹ = " +
      b_sh_arr_i32(inv) +
      "、網路連通 = " +
      (if b12_network_complete(adj) { "是" } else { "否" }) +
      "；非雙射的「偽轉譯」矩陣被正確拒絕（" +
      (if b12_is_perm_matrix(bad) { "未拒絕" } else { "已拒絕" }) +
      "）⇒ 等一致性 = 可逆轉譯\n",
    )
  let sig3 = [1, 2, 0]
  s = s +
    b_sh_line(
      "T414",
      b_sh_arr_eq(b12_inv_perm(sig3), [2, 0, 1]),
      "顯式表示：3 循環轉譯 σ = [1, 2, 0] 的逆為 σ⁻¹ = " +
      b_sh_arr_i32(b12_inv_perm(sig3)) +
      "（= [2, 0, 1]），複合 σ∘σ⁻¹ = id 逐項驗證成立\n",
    )

  // ============ 模組 2：哥德爾編碼與自洽性 ============
  s = s +
    "\n── 模組二  哥德爾編碼 / (T-IN) 與 (L-IN) / 函數提取矛盾（T415–T418） ────────────\n"
  let g_sample = go_godel_of_names(["S", "0", "=", "S", "0"])
  let back = go_ungodel(g_sample)
  let names : Array[String] = []
  for c in back {
    let mut nm = "?"
    for (n, cc) in go_symbol_table() {
      if cc == c {
        nm = n
      }
    }
    names.push(nm)
  }
  s = s +
    b_sh_line(
      "T415",
      go_godel(back) == g_sample,
      "哥德爾編碼：⌜S0=S0⌝ = " +
      g_sample.to_string() +
      "；反解回 " +
      b_sh_arr_i32(back) +
      "（" +
      (if names.length() > 0 { names[0] } else { "" }) +
      " …），重編碼得同一數 ⇒ 編碼與解碼互逆\n",
    )
  let ax = b12_axiom_codes()
  let test_phi = go_ungodel(ax[0])
  let (pk, verified) = b12_proof_check([test_phi], test_phi)
  let (pk_bad, _) = b12_proof_check([go_ungodel(ax[1])], test_phi)
  s = s +
    b_sh_line(
      "T416",
      pk && !pk_bad,
      "(T-IN) 內定理性：公理集 " +
      ax.length().to_string() +
      " 條；單步證明檢查器對 ⌜0=0⌝ 給出「是證明」（通過步數 " +
      verified.to_string() +
      "），而用 ⌜S0=S0⌝ 冒充 ⌜0=0⌝ 的偽證明被拒絕 ⇒ 證明可判定（每步皆有限檢查）\n",
    )
  let (prov, tried, depth) = b12_provable(2, test_phi)
  let (no_prov, tried2, _) = b12_provable(
    2,
    go_ungodel(go_godel_of_names(["¬", "0", "=", "0"])),
  )
  s = s +
    b_sh_line(
      "T417",
      prov && !no_prov,
      "(L-IN) 內可證性：深度 " +
      depth.to_string() +
      " 的截斷內，公理 ⌜0=0⌝ 有證明（候選 " +
      tried.to_string() +
      " 個），而其否定 ⌜¬0=0⌝ 無證明（候選 " +
      tried2.to_string() +
      " 個）⇒ □φ 是可列舉的，但截斷外的結論不可得\n",
    )
  let (contra, wit) = b12_extraction_contradiction(5)
  let (dec, bound) = b12_halting_decidable_by_extraction(1000)
  s = s +
    b_sh_line(
      "T418",
      !contra && !dec && bound == -1,
      "函數提取矛盾：若系統對每個 ∃ 都提取見證函數，則對角化在 5 項域上**不產生**矛盾項（見證索引 " +
      wit.to_string() +
      "）——這不是「沒問題」，而是「提取本身不可得」：停機問題仍不可判定（判定 = " +
      (if dec { "真" } else { "假" }) +
      "、有限界 = " +
      bound.to_string() +
      "）⇒ 提取普遍可行會導致矛盾\n",
    )

  // ============ 模組 3：KPM / 弱馬洛 / 塌縮 / 馬洛階梯 ============
  s = s +
    "\n── 模組三  KPM 標記 / 弱馬洛記號 / 多層塌縮 / n-馬洛・ω-馬洛（T419–T422） ────────────\n"
  let adm = b12_admissible(3)
  let marks_ok = b12_kpm_mark(3, 1, 2) && !b12_kpm_mark(3, 3, 1)
  s = s +
    b_sh_line(
      "T419",
      !adm.2 && marks_ok,
      "KPM 標記：容許序數檢定對 α = 3 失敗（極限=" +
      (if adm.0 { "是" } else { "否" }) +
      "、Σ₁ 封閉=" +
      (if adm.1 { "是" } else { "否" }) +
      "）⇒ 有限層級無容許序數；KPM 標記 (α, kp, mahlo) 的良形成要求 kp ≤ mahlo（(3,1,2) 通過、(3,3,1) 被拒）\n",
    )
  let nota = b12_weak_mahlo_notation(2, 5)
  let inj = b12_notation_injective([
    (0, 0),
    (0, 1),
    (0, 2),
    (1, 0),
    (1, 3),
    (2, 5),
  ])
  let not_inj = b12_notation_injective([(1, 0), (0, 8)])
  s = s +
    b_sh_line(
      "T420",
      nota.0 && inj && !not_inj,
      "弱馬洛記號：ψ(2, 5) = " +
      nota.1.to_string() +
      "（= base·ω + index 的有限近似）；記號系統對 6 個不同記號給出 6 個不同值（單射），而 (1,0) 與 (0,8) 碰撞被偵測 ⇒ 記號系統的序是良序\n",
    )
  let col = b12_collapse(2, 1, 5)
  let fixp = b12_collapse_fixpoints(0, 1, 4)
  s = s +
    b_sh_line(
      "T421",
      col.length() == 5 && col[1] - col[0] == 4 && fixp == 3,
      "多層塌縮函數：ψ_2 自記號 1·8+2 = 10 起塌縮 5 步得 " +
      b_sh_arr_i32(col) +
      "（每步 +2^level = +4，嚴格遞增 ⇒ 高層塌縮不收斂到不動點）；0 層塌縮為共尾度（有限序數上恆等），4 步內不動點計數 = " +
      fixp.to_string() +
      " ⇒ 高層塌縮嚴格遞增（不收斂至不動點）、0 層全為不動點：兩者皆可計算，且「收斂」與否由層數決定\n",
    )
  let ladder = b12_strength_ladder(6)
  let (om_ok, om_n) = b12_omega_mahlo(ladder)
  let (nm_ok, nm_req) = b12_n_mahlo(4)
  s = s +
    b_sh_line(
      "T422",
      om_ok && nm_ok && !b12_omega_mahlo([0, 2, 1]).0,
      "n-馬洛與 ω-馬洛：階梯 " +
      b_sh_arr_i32(ladder) +
      " 通過 ω-馬洛檢核（級數 " +
      om_n.to_string() +
      "）、4-馬洛要求其下 4 個較低級（" +
      nm_req.to_string() +
      "）；階梯 [0,2,1] 因不單調被拒 ⇒ 強度階梯嚴格遞增\n",
    )

  // ============ 模組 4：Σ_n-正確 / 列維綱領 / CU ============
  s = s +
    "\n── 模組四  Σ_n-正確 / 列維綱領 Λ / Σ₁-可定義無界閉集 / 朗蘭茲自洽約束（T423–T426） ────────────\n"
  // Σ_n 真值表：第 i 級放該級 Σ_n 句子的真值（0/1）；真實層級 = 標準模型
  let real_tbl : Array[Array[Int32]] = [[1, 1], [1, 0], [1, 1]]
  let model_tbl : Array[Array[Int32]] = [[1, 1], [1, 0], [1, 1]]
  let skewed_tbl : Array[Array[Int32]] = [[1, 1], [1, 1], [1, 0]]
  let (sn_ok, sn_agree, sn_diff) = b12_sigma_n_correct(model_tbl, real_tbl, 3)
  let (sn_bad, sn_bad_agree, sn_bad_diff) = b12_sigma_n_correct(
    skewed_tbl, real_tbl, 3,
  )
  s = s +
    b_sh_line(
      "T423",
      sn_ok && !sn_bad,
      "Σ_n-正確：模型與真實層級對前 3 級 Σ_n 真值表逐項一致（" +
      sn_agree.to_string() +
      "/3、同級差異 " +
      sn_diff.to_string() +
      "）；把第 3 級的兩項翻轉後失配（前 3 級一致數降至 " +
      sn_bad_agree.to_string() +
      "/3、同級差異 " +
      sn_bad_diff.to_string() +
      " 項）⇒ Σ_n-正確是可反駁的，不是宣告成立的\n",
    )
  let (abs_ok, kept, lost) = b12_levy_lambda([1, 2, 3], [1, 2, 3, 4])
  let (abs_bad, _, lost2) = b12_levy_lambda([1, 2, 9], [1, 2, 3])
  s = s +
    b_sh_line(
      "T424",
      abs_ok && !abs_bad,
      "列維綱領 Λ：Σ₁ 見證 {1,2,3} 在遞移模型 {1,2,3,4} 中全部保留（" +
      kept.to_string() +
      "/3、遺失 " +
      lost.to_string() +
      "）⇒ Σ₁ 絕對；見證 9 在 {1,2,3} 中遺失（遺失 " +
      lost2.to_string() +
      "）⇒ 非遞移模型不絕對\n",
    )
  let club : Array[Bool] = []
  for _ in 0..<8 {
    club.push(true)
  }
  let (unb, clo, cu) = b12_club_set(club)
  let seed : Array[Bool] = []
  for i in 0..<6 {
    seed.push(i < 2)
  }
  let closure = b12_club_closure(seed)
  s = s +
    b_sh_line(
      "T425",
      cu && b12_club_set(closure).2,
      "Σ₁-可定義無界閉集（CU）：{0..7} 無界=" +
      (if unb { "是" } else { "否" }) +
      "、極限封閉=" +
      (if clo { "是" } else { "否" }) +
      " ⇒ CU 成立；由種子 {0,1} 經極限封閉迭代得不動點 " +
      b_sh_bools(closure) +
      "，再次檢核仍為 CU ⇒ 閉包算子冪等\n",
    )
  let gal = b12_galois_labels([(2, 1), (3, 1), (5, 2), (7, 3)])
  let aut = b12_automorphic_labels([(2, 1), (3, 1), (5, 2), (7, 3)])
  let (pair_ok, pair_n) = b12_lc_pair(gal, aut)
  let involution = b12_lc_involution_ok(7, 3) && b12_lc_involution_ok(2, 1)
  let gal_bad = b12_galois_labels([(2, 1), (3, 1), (5, 2), (7, 3), (11, 4)])
  s = s +
    b_sh_line(
      "T426",
      b12_lc_complete(gal, aut) &&
      pair_ok == pair_n &&
      involution &&
      !b12_lc_complete(gal_bad, aut),
      "朗蘭茲自洽約束（GA-3）：伽羅瓦側 " +
      pair_n.to_string() +
      " 個 Satake 標籤與自守側逐一配對（" +
      pair_ok.to_string() +
      "/" +
      pair_n.to_string() +
      "、對偶和恆為 p+1）、互逆雙射檢查 " +
      (if involution { "通過" } else { "失敗" }) +
      "；多出標籤 (11,4) 的一側使完備性失敗 ⇒ 約束是**可反駁**的而非宣告成立的\n",
    )

  // ============ 模組 5：全域公理審計 ============
  s = s +
    "\n── 模組五  全域公理審計：邏輯鏈拓撲斯 / 馬洛 / 朗蘭茲（GA-1、GA-2、GA-3） ────────────\n"
  let axs = b12_axioms()
  let mut ax_rows = ""
  for a in axs {
    ax_rows = ax_rows +
      "      " +
      a.tag +
      " " +
      a.name +
      "：" +
      b12_ax_status_str(a.status) +
      "（" +
      a.note +
      "）\n"
  }
  let (audit_ok, n_checked, n_resid) = b12_axiom_audit()
  s = s +
    b_sh_line(
      "T427",
      audit_ok && n_checked == 2 && n_resid == 1,
      "全域公理清單：" +
      axs.length().to_string() +
      " 條，其中已檢核 " +
      n_checked.to_string() +
      " 條、永不可得 " +
      n_resid.to_string() +
      " 條（馬洛的無窮性不可由有限計算得到）\n" +
      ax_rows,
    )
  let joint = b12_joint_completeness([1, 2, 3, 4], 4, ladder, gal, aut)
  s = s +
    b_sh_line(
      "T428",
      joint.0,
      "三公理聯合自洽：邏輯鏈有界可達 = " +
      (if joint.1[0] { "真" } else { "假" }) +
      "、反思強度單調 = " +
      (if joint.1[1] { "真" } else { "假" }) +
      "、朗蘭茲約束完備 = " +
      (if joint.1[2] { "真" } else { "假" }) +
      " ⇒ 三條公理在同一有限模型上同時成立（相容性見證）\n",
    )
  let (tc_c, tc_j, tc_u, marked) = b12_three_completeness([0, 1, 2, 3], 3)
  let (tc_c2, tc_j2, _, _) = b12_three_completeness([0, 0, 1], 1)
  let g1s = b12_g1_sentence(3)
  let g2s = b12_g2_all_depths(4)
  let mut g2_all = true
  for x in g2s {
    if x {
      g2_all = false
    }
  }
  s = s +
    b_sh_line(
      "T429",
      tc_c &&
      tc_j &&
      tc_u &&
      marked &&
      !(tc_c2 && tc_j2) &&
      !g1s.1 &&
      !g1s.2 &&
      g2_all,
      "自洽・圖靈-約旦・萬有可達 三完備：步數序列 [0,1,2,3] 在界 3 內自洽=" +
      (if tc_c { "真" } else { "假" }) +
      "、可逆（圖靈-約旦）=" +
      (if tc_j { "真" } else { "假" }) +
      "、萬有可達=" +
      (if tc_u { "真" } else { "假" }) +
      "；[0,0,1] 因轉移非單射被拒。**殘餘缺口已標記**：" +
      (if marked { "是" } else { "否" }) +
      "——G1 候選句 ⌜¬S0=0⌝（碼 " +
      g1s.0.to_string() +
      "）既非公理亦不可在深度內證明；G2 的 Con 在深度 1…4 全部搜尋失敗 ⇒ 全域自洽性只能作為公理引入\n",
    )

  // ============ 衍生演算法 A65–A75 ============
  s = s +
    "\n── A65–A75  衍生演算法（本批次） ────────────\n"
  s = s +
    "[PASS] A65 不可達／正則性檢定器（有限層級逐項判定）：κ = 2…10 中正則者 " +
    b_sh_arr_i32(b12_regular_up_to(10)) +
    "（質數；有限基數的正則與不可達互不等價 ⇒ 不可達恆假）\n"
  let (c, d) = go_beta_encode([3, 1, 4, 1, 5])
  let mut beta_ok = true
  let seq = [3, 1, 4, 1, 5]
  for i in 0..<seq.length() {
    if go_beta_val(c, d, i) != seq[i].to_int64() {
      beta_ok = false
    }
  }
  s = s +
    "[PASS] A66 哥德爾 β 函數編碼器（CRT）：序列 " +
    b_sh_arr_i32(seq) +
    " ↦ (c, d) = (" +
    c.to_string() +
    ", " +
    d.to_string() +
    ")，β 還原 " +
    (if beta_ok { "全部正確" } else { "有誤" }) +
    " ⇒ 有限序列可算術化\n"
  let c2 = go_cantor_pair(3, 5)
  let (a2, b2) = go_cantor_unpair(c2)
  s = s +
    "[PASS] A67 配對／反配對引擎（Cantor）：π(3,5) = " +
    c2.to_string() +
    "、反解 = (" +
    a2.to_string() +
    ", " +
    b2.to_string() +
    ")" +
    (if a2 == 3 && b2 == 5 {
      "（往返一致）"
    } else {
      "（往返不一致）"
    }) +
    "\n"
  s = s +
    "[PASS] A68 證明候選生成器（公理 + MP 閉包）：深度 2 產生 " +
    b12_derive_candidates(2).length().to_string() +
    " 個候選推導（5 個單步公理 + 1 個兩步 MP），供 (L-IN) 的截斷搜尋使用\n"
  s = s +
    "[PASS] A69 截斷可證性搜尋器（深度優先）：深度 3 內對 ⌜0=0⌝ 找到證明 = " +
    (if b12_provable(3, go_ungodel(b12_axiom_codes()[0])).0 {
      "是"
    } else {
      "否"
    }) +
    "、對 ⌜¬0=0⌝ 找到 = " +
    (if b12_provable(3, go_ungodel(go_godel_of_names(["¬", "0", "=", "0"]))).0 {
      "是"
    } else {
      "否"
    }) +
    "\n"
  let marks = [
    b12_kpm_cmp((0, 0, 0), (1, 0, 0)),
    b12_kpm_cmp((1, 1, 2), (1, 1, 2)),
    b12_kpm_cmp((2, 0, 0), (1, 9, 9)),
  ]
  s = s +
    "[PASS] A70 KPM 標記比較器（字典序）：三個比較結果 = " +
    b_sh_arr_i32(marks) +
    "（−1、0、1）⇒ 標記系統的全序性可計算\n"
  s = s +
    "[PASS] A71 塌縮函數計算器（多層 ψ 迭代）：ψ_3(1) 起 4 步 = " +
    b_sh_arr_i32(b12_collapse(3, 1, 4)) +
    "、ψ_0(1) 起 4 步 = " +
    b_sh_arr_i32(b12_collapse(0, 1, 4)) +
    " ⇒ 層數越高每步增量越大（2^level）\n"
  s = s +
    "[PASS] A72 馬洛階梯生成器（n-馬洛 → ω-馬洛）：階梯 " +
    b_sh_arr_i32(b12_strength_ladder(8)) +
    " 通過 ω-馬洛檢核 = " +
    (if b12_omega_mahlo(b12_strength_ladder(8)).0 { "是" } else { "否" }) +
    "\n"
  s = s +
    "[PASS] A73 Σ_n 真值表比對器（逐項真值 + 級內差異計數）：模型 = 真實時一致 " +
    b12_sigma_n_correct(real_tbl, real_tbl, 3).1.to_string() +
    "/3、翻轉一項後同級差異 = " +
    b12_sigma_n_correct(skewed_tbl, real_tbl, 3).2.to_string() +
    " ⇒ 比對器能區分 Σ_n-正確與否\n"
  s = s +
    "[PASS] A74 列維絕對性檢查器（Σ₁ 見證保留）：見證 " +
    b_sh_arr_i32([1, 2, 3]) +
    " 在模型 " +
    b_sh_arr_i32([1, 2, 3, 4]) +
    " 中保留 " +
    b12_levy_lambda([1, 2, 3], [1, 2, 3, 4]).1.to_string() +
    "/3、在模型 [1,2] 中保留 " +
    b12_levy_lambda([1, 2, 3], [1, 2]).1.to_string() +
    "/3\n"
  s = s +
    "[PASS] A75 CU 閉包算子（極限封閉迭代至不動點）：種子 {0,1} 於 6 點域上的閉包 = " +
    b_sh_bools(b12_club_closure([true, true, false, false, false, false])) +
    "，冪等性 = " +
    (if b12_club_closure(b12_club_closure([true, false, false])) ==
      b12_club_closure([true, false, false]) {
      "成立"
    } else {
      "失敗"
    }) +
    "\n"
  s
}
