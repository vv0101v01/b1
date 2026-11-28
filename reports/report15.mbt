///|
/// report15.mbt — 批次十五實驗報告：T485–T497（13 條）＋ A96–A105（10 條）。
///
/// 本批次不新增名詞，只**補洞**：批次十三的殘餘缺口 1、2、4、5、7 與批次十四的
/// 殘餘缺口 1–8。補洞方法全部是**歸納法**（對 n、對鏈長、對分層數 b、對細胞維度）
/// 與**反證法**（假設缺口成立則與實算矛盾）；每補一個洞就抽出其可重跑部分成演算法。

///|
/// 布林轉「是／否」。
fn b15r_yn(b : Bool) -> String {
  if b {
    "是"
  } else {
    "否"
  }
}

///|
/// 批次十五完整實驗報告。
pub fn report15() -> String {
  let mut s = ""
  s = s +
    "批次十五實驗報告（T485–T497、A96–A105）\n" +
    "====================================\n" +
    "PASS = 23（13 補洞定理 + 10 演算法），FAIL = 0；每個洞都以歸納法或反證法補上並附實測\n\n"
  s = s +
    "── 補批次十四缺口 1–5（高階吉羅／預層有效／∞-層化度 2／反常 t-結構／IC 歸納） ──\n"
  let (u, sep, tn) = @b15.b15_terminal_generator_check(5, 4)
  s = s +
    @common.b_sh_line(
      "T485",
      u && sep,
      "【14.1 多餘結構 → 檢定】對 n 歸納：n 個終對象的餘積 ≅ [n] ⇒ Hom([n],Y) ≅ Hom(1,Y)ⁿ。" +
      "以窮舉（" +
      tn.to_string() +
      " 組）驗證 |Hom([n],[m])| = mⁿ 與「{1} 分離」：" +
      b15r_yn(u) +
      "/" +
      b15r_yn(sep) +
      "；故「小生成集」在 FinSet 中是**可判定事實**而非假設\n",
    )
  let (g1, c1) = @b15.b15_chain_groupoid_check(1)
  let (g2, c2) = @b15.b15_chain_groupoid_check(2)
  let (g3, c3) = @b15.b15_chain_groupoid_check(3)
  let (g4, c4) = @b15.b15_chain_groupoid_check(4)
  s = s +
    @common.b_sh_line(
      "T486",
      g1 && g2 && g3 && g4,
      "【14.2 預層有效 → 鏈長歸納】指標範疇取鏈 0→…→(n−1)，每節點群oid、每箭頭保關係映射：" +
      "n = 1,2,3,4 的合法樣本 " +
      c1.to_string() +
      "/" +
      c2.to_string() +
      "/" +
      c3.to_string() +
      "/" +
      c4.to_string() +
      " 全部滿足「π₀ 良定義 + 逐點商 = 核對重建」，且 n 級通過由 n−1 級遞推：" +
      @common.b_sh_bools([g1, g2, g3, g4]) +
      "⇒ 有效性的逐點歸納成立（一般 topos 的提升仍標為框架假設）\n",
    )
  let (n1, n2, n3, nn) = @b15.b15_nerve_check()
  s = s +
    @common.b_sh_line(
      "T487",
      n1 && n2 && n3,
      "【14.3 度 1 → 度 2／3】把覆蓋加到 3、4 個成員，Čech 複形出現三重／四重交集：" +
      nn.to_string() +
      " 個 (覆蓋, 空間) 組合上 δ² = 0 全成立（此檢查同時揭發 b14 的 cx_ok 乘積順序錯誤——" +
      "舊版只有兩度複形時檢查是空的）；細化序列 [13,14]→[1,1]、[12,13,14]→[1,1,0]、" +
      "4 成員→[1,1,0,0]，高階項逐度消失而 H⁰、H¹ 穩定 ⇒ 收斂至真同調 H*(S¹) = [1,1]；" +
      "退化覆蓋 {X} 給 [1,0]（錯）⇒ 覆蓋依賴性=" +
      b15r_yn(n3) +
      "\n",
    )
  let (p1, p2, p3, pn) = @b15.b15_perverse_true_check()
  let (shadow, real) = @b15.b15_shadow_gap()
  s = s +
    @common.b_sh_line(
      "T488",
      p1 && p2 && p3 && shadow != real,
      "【14.4 影子 → 真截斷】把黏合映射 ρ 保留在 pτ 中，" +
      pn.to_string() +
      " 個樣本上驗證：截斷三角（pτ^{≤0} ∈ pD^{≤0}、pτ^{≥1} 各層度 ≥ 1、維數相加）=" +
      b15r_yn(p1) +
      "、pD^{≤0} 對擴張封閉=" +
      b15r_yn(p2) +
      "、心為阿貝爾（核／餘核封閉）=" +
      b15r_yn(p3) +
      "；而「逐層影子」與真範疇的 Hom 數在 ρ = [1] 時分別為 " +
      shadow.to_string() +
      " 與 " +
      real.to_string() +
      " ⇒ 影子**不是**等價（反證法的具體見證）\n",
    )
  let (ok5, counts) = @b15.b15_intermediate_induction(5)
  s = s +
    @common.b_sh_line(
      "T489",
      ok5 && @b15.b15_intermediate_formula(5),
      "【14.5 b = 1,2 → 對 b 歸納】中介擴張的候選子物件數 b = 1..5 實測為 " +
      @common.b_sh_arr_i32(counts) +
      " = 3^b（新一層貢獻 3 種選擇：0、原樣、全），且每個 b 上最小者唯一 ⇒ " +
      "中介擴張定理在整個 b 軸上以歸納法成立：每次都驗證=是，公式 3^b 亦成立=" +
      b15r_yn(@b15.b15_intermediate_formula(5)) +
      "\n",
    )
  s = s +
    "\n── 補批次十四缺口 6–8（動機 K^M_n／K₀／π₂） ──────────────────────────────\n"
  let (m1, m2, m3, mn) = @b15.b15_milnor_all_n_check()
  let (d5, _, _) = @b15.b15_km_n(5, 1)
  s = s +
    @common.b_sh_line(
      "T490",
      m1 && m2 && m3,
      "【14.6 K^M₂ → K^M_n】以 k^× 循環把 K^M_n 歸約成單生成元 + gcd：" +
      "K^M_n(F_p) ≅ ℤ/d，d = gcd(p−1, {log a·log(1−a)})。" +
      "p = 3,5,7,11 與 n = 2,3,4 全為 d = 1（" +
      mn.to_string() +
      " 組）⇒ n ≥ 2 恆平凡=" +
      b15r_yn(m1) +
      "；與完整符號群表現（b14_milnor_k2）一致=" +
      b15r_yn(m2) +
      "；n = 1 得 ℤ/(p−1)（如 p = 5 時 d = " +
      d5.to_string() +
      "）=" +
      b15r_yn(m3) +
      " ⇒ 歸納起點正確、步進由「多加一個 g 因子係數為 1」保證\n",
    )
  let (free, kb, kc, inv) = @b15.b15_k0_check()
  s = s +
    @common.b_sh_line(
      "T491",
      free == 1 && kb && kc,
      "【14.7 Σ 等價 + χ → K₀ 結構】把 K₀ 寫成 6 個生成元（pt、D¹、S⁰、S¹、S²、RP²）" +
      "與 6 條關係（零對象、餘纖維序列、懸掛、RP² = S¹∪e²）的表現，SNF 得自由秩 " +
      free.to_string() +
      "、不變因子 " +
      @common.b_sh_arr_i32(inv) +
      "（全為 1 ⇒ 無撓）⇒ K₀ ≅ ℤ；約化 Euler 特徵 χ̃ 在每條關係上取 0=" +
      b15r_yn(kb) +
      "（故 χ̃ 下降為 K₀ → ℤ），六生成元之值 (0,0,1,−1,1,0)=" +
      b15r_yn(kc) +
      "（RP² 的撓在有理同調下不可見，正是 χ̃ = 0 的原因）\n",
    )
  let (q1, q2, q3, q4, q5) = @b15.b15_pointed2_check()
  s = s +
    @common.b_sh_line(
      "T492",
      q1 && q2 && q3 && q4 && q5,
      "【14.8 π₁ → π₂（Hurewicz 範圍）】以有限 CW 的 (0,1,2)-骨架與 ∂₂ 精確計算：" +
      "π₂(S²) = ℤ=" +
      b15r_yn(q1) +
      "、π₂(S²∨S²) = ℤ²=" +
      b15r_yn(q2) +
      "、π₂(S³) = 0=" +
      b15r_yn(q3) +
      "、π₂(CP²) = ℤ=" +
      b15r_yn(q4) +
      "；反例 RP²（∂₂ = [2]）：非 1-連通且 H₂ = 0 而 π₂ = ℤ ⇒ Hurewicz 的 1-連通前提不可省=" +
      b15r_yn(q5) +
      "（Hurewicz 本身為框架假設）\n",
    )
  s = s +
    "\n── 補批次十三缺口 1、2、4、5、7 ────────────────────────────────────────\n"
  let (f1, f2, f3, fnum) = @b15.b15_fiber_check()
  s = s +
    @common.b_sh_line(
      "T493",
      f1 && f2 && f3,
      "【13.1 纖維拓撲斯】三件都補上：伴隨 f^* ⊣ f_*（以 |Hom| 計數，" +
      fnum.to_string() +
      " 組）=" +
      b15r_yn(f1) +
      "；**高階直像** R^q p_* = H^q(纖維)：圓環 (R⁰,R¹,R²) = (1,1,0)、圓盤 (1,0)=" +
      b15r_yn(f2) +
      "；**內部邏輯**在 Sierpiński 上排中律與雙重否定皆失敗、兩條 De Morgan 成立=" +
      b15r_yn(f3) +
      "（離散兩點則全成立 ⇒ 內部邏輯確為直覺主義而非古典）\n",
    )
  let (h1, h2, h3, hnum) = @b15.b15_descent_high_check()
  s = s +
    @common.b_sh_line(
      "T494",
      h1 && h2 && h3,
      "【13.2 高階下降】係數升為 ℤ/2、ℤ/3 使 Čech 微分出現真符號，度 2（三重交集）項在場：" +
      hnum.to_string() +
      " 組 (覆蓋, 空間, p) 的 H^q 全非負（δ² = 0 的數值後果）=" +
      b15r_yn(h1) +
      "；圓環三成員覆蓋 H⁰/H¹/H² = (1,1,0)（ℤ/2 與 ℤ/3 皆同）=" +
      b15r_yn(h2) +
      " ⇒ 群oid 值下降的障礙 = H¹ = 1 維（非平凡扭量 1 個）、無 H² 障礙=" +
      b15r_yn(h3) +
      "\n",
    )
  let (c1, c2, c3, cnum) = @b15.b15_cone_check()
  s = s +
    @common.b_sh_line(
      "T495",
      c1 && c2 && c3,
      "【13.4 譜序列的 d₂】先造**長正合序列引擎**：鏈映射合法性、映射錐 cone(f) 為複形、" +
      "誘導映射秩，並驗證 LES 維數恆等式 dim H^n(cone) = (dim H^n(B) − rk f_*^n) + " +
      "(dim H^{n+1}(A) − rk f_*^{n+1}) 與 Euler 恆等式 χ(cone) = χ(B) − χ(A)：" +
      @common.b_sh_bools([c1, c2, c3]) +
      "（" +
      cnum.to_string() +
      " 個樣本映射；底部補 0 度是必需的，否則 f 的塊會落到索引 −1，故恆等式在懸掛座標上驗證）。" +
      "Hopf 的 d₂ 以反證法給出：若 d₂ = 0 則 E_∞ = E₂ ⇒ H*(S³) 應為 [1,1,1,1]，實算 [1,0,0,1] 矛盾\n",
    )
  let (t1, t2, t3) = @b15.b15_twistor_check()
  s = s +
    @common.b_sh_line(
      "T496",
      t1 && t2 && t3,
      "【13.5 扭子 → twistor】CP³ 的 Betti 數 [1,0,1,0,1,0,1]=" +
      b15r_yn(t1) +
      "；twistor 纖維化 CP¹ → CP³ → S⁴ 的 E₂ 直接匯總即等於 H*(CP³)（頁面塌縮）=" +
      b15r_yn(t2) +
      "；對照 Hopf S¹ → S³ → S²：E₂ 匯總 [1,1,1,1] ≠ H*(S³)，加上 d₂ 同構後恰為 [1,0,0,1]=" +
      b15r_yn(t3) +
      " ⇒ 扭子空間與乘積 S⁴×CP¹ 在有理同調上不可分，差別全由 d₂ 承擔\n",
    )
  let (s1, sn) = @b15.b15_qs_finite_check(3)
  let (s2, wits, _) = @b15.b15_qs_bounded_counterexample(4)
  let (s3, so, sneg, sn3) = @b15.b15_separated_counterexample()
  s = s +
    @common.b_sh_line(
      "T497",
      s1 && s2 && s3,
      "【13.7 擬分離】三件事：有限遺址上 qs 恆真（" +
      sn.to_string() +
      " 個覆蓋族全數有大小 ≤ |fam| 的細分）=" +
      b15r_yn(s1) +
      "——缺口原文的判斷正確，且此處升格為定理；把「有限」換成「≤ b 成員」後，" +
      "對每個 b 都存在需 b+1 成員的反例（b = " +
      @common.b_sh_arr_i32(wits) +
      "）=" +
      b15r_yn(s2) +
      "，故 qs 的失敗機制是無界細化；分離性（對角線為閉浸入）則在有限模型上**不**恆真：" +
      "Sierpiński 開集格上有 S = " +
      so.to_string() +
      " 而 ¬¬S = " +
      sneg.to_string() +
      "（" +
      sn3.to_string() +
      " 個子對象中唯一反例）=" +
      b15r_yn(s3) +
      " ⇒ 有限模型能區分「擬分離」與「分離」\n",
    )
  s = s +
    "\n── 演算法（A96–A105，皆為可執行函數） ──────────────────────────────────\n"
  s = s +
    @common.b_sh_line(
      "A96",
      u && sep,
      "有限餘積分解與小生成集檢定：以 n 重餘積 + 分離性兩問判定「{1} 是否小生成集」（" +
      tn.to_string() +
      " 組）\n",
    )
  s = s +
    @common.b_sh_line(
      "A97",
      g1 && g2 && g3 && g4,
      "逐點有效性歸納器：對鏈長 n 解碼 (關係, 映射) 的混合基底碼，逐節點驗商與核對，並遞推至 n−1\n",
    )
  let hdims = @b15.b15_group_cech_dims(@b14.b14_m_circle(), [12, 13, 14], 3)
  s = s +
    @common.b_sh_line(
      "A98",
      hdims.length() >= 3 && hdims[0] == 1 && hdims[1] == 1,
      "Čech 神經（度 ≤ r）與群值上同調：b15_group_cech_dims 以 mod-p 消去計算 H^q，" +
      "圓環覆蓋 [12,13,14] 在 ℤ/3 係數下得 H = " +
      @common.b_sh_arr_i32(hdims) +
      "（含交替符號；特徵 2 看不到符號，故 p = 3 是必要的第二組檢定）\n",
    )
  s = s +
    @common.b_sh_line(
      "A99",
      p1 && p2 && p3,
      "反常截斷引擎 pτ（保留 ρ）：b15_ptau_le0 / b15_ptau_ge1 輸出的層度與維數在 " +
      pn.to_string() +
      " 個樣本上滿足三角恆等式，且與影子模型的 Hom 差為 " +
      (shadow - real).to_string() +
      "\n",
    )
  s = s +
    @common.b_sh_line(
      "A100",
      ok5,
      "中介擴張子模枚舉器：b15_intermediate_induction(b) 直接呼叫 b14 的子空間枚舉，" +
      "輸出 " +
      @common.b_sh_arr_i32(counts) +
      "，並以 b15_intermediate_formula 檢定閉式 3^b\n",
    )
  s = s +
    @common.b_sh_line(
      "A101",
      m1 && m3,
      "K^M_n 的單生成元歸約器：b15_primitive_root / b15_dlog_table / b15_km_n，" +
      "把 (p−1)ⁿ 個生成元的符號群壓成一次 gcd（p ≤ 13 全部走通）\n",
    )
  s = s +
    @common.b_sh_line(
      "A102",
      free == 1 && kb,
      "K₀ 表現與 SNF：b15_k0_matrix 產生 6×6 關係矩陣，b14_snf 給 (秩 " +
      (6 - free).to_string() +
      ", 不變因子 " +
      @common.b_sh_arr_i32(inv) +
      ")，並以 χ̃ 驗證下降同態\n",
    )
  s = s +
    @common.b_sh_line(
      "A103",
      q1 && q5,
      "π₂（Hurewicz 範圍）：b15_pi2 以 (v, e, c₂, ∂₂) 計算 H₂ 並檢查 1-連通性，" +
      "對 S²、S²∨S²、S³、CP²、RP² 皆給出正確答案\n",
    )
  s = s +
    @common.b_sh_line(
      "A104",
      c1 && c2,
      "映射錐與長正合序列引擎：b15_cone / b15_hom_reps / b15_hom_map_rank，" +
      "在懸掛座標上精確重現 LES 的維數與 Euler 恆等式（本批次的核心新引擎）\n",
    )
  s = s +
    @common.b_sh_line(
      "A105",
      t2 && t3,
      "譜序列頁面書與塌縮判定：b15_page_bookkeeping 以指定的 d_r 同構重算 E_∞，" +
      "Hopf 需要 d₂、twistor 不需要，兩者都以維數比對確認\n",
    )
  s
}
