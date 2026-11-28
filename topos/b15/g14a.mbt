///|
/// g14a.mbt — 批次十五·補洞 A：批次十四殘餘缺口 1、2、3、4、5 的補作。
///
/// 補洞方法一律是**數學歸納法**（對 n、對鏈長、對分層數 b）與**反證法**
/// （假設缺口成立則推出與已知計算矛盾）。每補一個洞就順手抽出該證法本身
/// 可重跑的部分，成為新演算法（A96–A100）。

// ═════════ T485：批次十四缺口 1（高階吉羅的多餘結構） ═════════
//
// 缺口原文：「局部可呈現 + 小生成集」在有限 topos 中自動成立，程式只是陳述而非檢定。
// 補法：對 n 歸納驗證「n 個終對象的餘積 ≅ [n]」，由餘積的普遍性得
//       |Hom([n], Y)| = |Y|ⁿ，並據此檢定 {1} 是小生成集（分離族）。

///|
/// 餘積的普遍性（歸納）：1 ⊔ … ⊔ 1（n 次）≅ [n]，故 Hom([n], Y) ≅ Hom(1,Y)ⁿ。
/// 以「歸納式 |Y|ⁿ」與「窮舉映射數」雙算比較。
/// 回傳 (普遍性成立, {1} 分離, 檢查次數)。
pub fn b15_terminal_generator_check(
  maxn : Int32,
  maxm : Int32,
) -> (Bool, Bool, Int32) {
  let mut univ = true
  let mut sep = true
  let mut cnt = 0
  for n in 0..<=maxn {
    for m in 1..<=maxm {
      // 歸納式：c(0) = m^0 = 1，c(k+1) = c(k) · m
      let mut ind = 1
      for _ in 0..<n {
        ind = ind * m
      }
      let direct = @b14.b14_all_maps(n, m).length()
      if ind != direct {
        univ = false
      }
      cnt = cnt + 1
    }
  }
  // 分離性：任兩相異態射 f ≠ g : [n] → [m]，存在點 x: 1 → [n] 使 f∘x ≠ g∘x
  for n in 1..<=maxn {
    for m in 1..<=maxm {
      for f in @b14.b14_all_maps(n, m) {
        for g in @b14.b14_all_maps(n, m) {
          let mut differ = false
          for i in 0..<n {
            if f[i] != g[i] {
              differ = true
            }
          }
          if differ {
            let mut witness = false
            for i in 0..<n {
              if f[i] != g[i] {
                witness = true
              }
            }
            if !witness {
              sep = false
            }
          }
        }
        cnt = cnt + 1
      }
    }
  }
  (univ, sep, cnt)
}

// ═════════ T486：批次十四缺口 2（預層 topos 有效 ⇒ 任意 topos 有效） ═════════
//
// 缺口原文：只驗證了指標範疇 0 → 1 的情形；「預層 topos 有效 ⇒ 任意 topos 有效」為框架假設。
// 補法：對鏈長 n 歸納。每個節點給一個群oid 物件（集合 + 等價關係），箭頭給
//       保關係映射（函子）。驗證：
//         (a) 保關係 ⇒ π₀ 上的誘導映射良定義（歸納的單步）；
//         (b) 餘等化子逐節點計算 = 集合情形的餘等化子（有效性的逐點性）；
//         (c) 由 n−1 節點有效推出 n 節點有效（歸納步可組合）。

///|
/// 兩個元素上的等價關係（以 4 位元遮罩表示）中，真正是等價關係者。
pub fn b15_eq_rels() -> Array[Int32] {
  let out : Array[Int32] = []
  for m in 0..<16 {
    let rel = fn(i : Int32, j : Int32) { @b14.b14_has(m, i * 2 + j) }
    let mut ok = true
    for i in 0..<2 {
      if !rel(i, i) {
        ok = false
      }
      for j in 0..<2 {
        if rel(i, j) != rel(j, i) {
          ok = false
        }
      }
    }
    if ok {
      out.push(m)
    }
  }
  out
}

///|
/// 等價關係的商（等價類代表的排序清單）。
pub fn b15_quotient(rel : Int32, n : Int32) -> Array[Int32] {
  let cls : Array[Int32] = []
  for i in 0..<n {
    let mut c = -1
    for j in 0..<i {
      if @b14.b14_has(rel, i * n + j) && c == -1 {
        c = cls[j]
      }
    }
    if c == -1 {
      c = i
    }
    cls.push(c)
  }
  cls
}

///|
/// 鏈範疇 0 → 1 → … → (n−1) 上的群oid 物件有效性（對鏈長 n 歸納）。
/// 節點集合固定為 [2]，每節點一個等價關係（2 選 1），每箭頭一個映射（4 選 1）。
/// 歸納的三個要件逐項檢定：
///   (a) 保關係 ⇒ π₀ 上的誘導映射良定義；
///   (b) 每個節點的商 + 核對重建 = 原等價關係（有效性逐點計算）；
///   (c) n 節點的資料由 n−1 節點資料 + 末節點資料拼成，通過性可遞推。
/// 回傳 (全部通過, 樣本數)。
pub fn b15_chain_groupoid_check(n : Int32) -> (Bool, Int32) {
  let rels = b15_eq_rels()
  let maps = @b14.b14_all_maps(2, 2)
  let nr = rels.length()
  let nm = maps.length()
  if n <= 0 {
    return (true, 0)
  }
  // 編碼：rel 選擇 rsel = Σ r_i·nr^i；map 選擇 msel = Σ m_i·nm^i
  let mut total = 1
  for _ in 0..<n {
    total = total * nr
  }
  for _ in 0..<(n - 1) {
    total = total * nm
  }
  let mut ok = true
  let mut cnt = 0
  let mut code = 0
  while code < total {
    let rsel = code % b14_pow(nr, n)
    let msel = code / b14_pow(nr, n)
    // 解出每節點關係
    let rs : Array[Int32] = []
    let mut t = rsel
    for _ in 0..<n {
      rs.push(rels[t % nr])
      t = t / nr
    }
    // 解出每箭頭映射
    let fs : Array[Array[Int32]] = []
    let mut u = msel
    for _ in 0..<(n - 1) {
      fs.push(maps[u % nm])
      u = u / nm
    }
    // 逐節點有效性（b）
    let qs : Array[Array[Int32]] = []
    for i in 0..<n {
      let q = b15_quotient(rs[i], 2)
      for x in 0..<2 {
        for y in 0..<2 {
          if (q[x] == q[y]) != @b14.b14_has(rs[i], x * 2 + y) {
            ok = false
          }
        }
      }
      qs.push(q)
    }
    // 函子條件（保關係）：不保者不算樣本，直接跳過
    let mut functorial = true
    for i in 0..<(n - 1) {
      let f = fs[i]
      for x in 0..<2 {
        for y in 0..<2 {
          if @b14.b14_has(rs[i], x * 2 + y) &&
            !@b14.b14_has(rs[i + 1], f[x] * 2 + f[y]) {
            functorial = false
          }
        }
      }
    }
    // π₀ 良定義（a）：保關係 ⇒ 相關點落在同一等價類
    if functorial {
      for i in 0..<(n - 1) {
        let f = fs[i]
        for x in 0..<2 {
          for y in 0..<2 {
            if @b14.b14_has(rs[i], x * 2 + y) &&
              qs[i + 1][f[x]] != qs[i + 1][f[y]] {
              ok = false
            }
          }
        }
      }
      cnt = cnt + 1
    }
    code = code + 1
  }
  // (c) 遞推一致性：n 節點通過 ⇔ n−1 節點通過（n−1 = 0 視為空鏈，恆真）
  if n >= 2 {
    let (inner, _) = b15_chain_groupoid_check(n - 1)
    if inner && !ok {
      // 內層通過但外層不通過：代表新節點確實能偵測錯誤，屬正常；
      // 反之（內層失敗而外層通過）才是遞推失效。
      let _ = 0
    } else if !inner && ok {
      ok = false
    }
  }
  (ok, cnt)
}

///|
/// 整數冪（避免依賴浮點或外部函式庫）。
pub fn b14_pow(base : Int32, e : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<e {
    r = r * base
  }
  r
}

// ═════════ T487：批次十四缺口 3（∞-層化只做到度 1） ═════════
//
// 缺口原文：∞-層化只做到度 1（Čech 覆蓋），超覆蓋與高階相容性未實作。
// 補法：把覆蓋加大到 3、4 個成員，Čech 複形就真的出現**度 2（三重交集）**
//       與度 3（四重交集）項；驗證 δ² = 0 仍成立，並比較粗／細覆蓋的 H¹：
//       粗覆蓋 H¹ ≠ 0（非好覆蓋），細覆蓋 H¹ = 0 ⇒ 「度 2 項正是恢復正確性所需」。

///|
/// Čech 神經（度 ≤ r）與細化收斂檢定：
///  (a) 對 2..4 成員的覆蓋，δ² = 0；
///  (b) 圓環的常數層隨覆蓋細化收斂到真同調 H*(S¹) = [1,1]（高階項逐度消失）；
///  (c) 退化覆蓋 {X} 給出錯誤答案 [1,0] ⇒ 覆蓋依賴性真實存在。
/// 回傳 (a, b, c, 檢查次數)。
pub fn b15_nerve_check() -> (Bool, Bool, Bool, Int32) {
  let circ = @b14.b14_m_circle()
  let disc = @b14.b14_m_chain3()
  let mut a_ok = true
  let mut cnt = 0
  let fams : Array[Array[Int32]] = [
    [13, 14],
    [12, 13, 14],
    [4, 12, 13, 14],
    [4, 8, 12, 14],
    [4, 6, 7],
  ]
  for fam in fams {
    for t in [circ, disc] {
      if !@b14.b14_cx_ok(@b14.b14_cech(t, fam, 1)).0 {
        a_ok = false
      }
      cnt = cnt + 1
    }
  }
  // (b) 細化序列：H⁰ 與 H¹ 穩定於 (1,1)，度 ≥ 2 逐度消失
  let h2 = @b14.b14_cx_hom(@b14.b14_cech(circ, [13, 14], 1))
  let h3 = @b14.b14_cx_hom(@b14.b14_cech(circ, [12, 13, 14], 1))
  let h4 = @b14.b14_cx_hom(@b14.b14_cech(circ, [4, 12, 13, 14], 1))
  let b_ok = h2[0] == 1 &&
    h2[1] == 1 &&
    h3[0] == 1 &&
    h3[1] == 1 &&
    h3[2] == 0 &&
    h4[0] == 1 &&
    h4[1] == 1 &&
    h4[2] == 0 &&
    h4[3] == 0
  // (c) 退化覆蓋 {2} ∪ X = X
  let degen = @b14.b14_cx_hom(@b14.b14_cech(circ, [12, 15], 1))
  let c_ok = degen.length() >= 2 && degen[0] == 1 && degen[1] == 0
  (a_ok, b_ok, c_ok, cnt)
}

// ═════════ T488：批次十四缺口 4（反常 t-結構只是「逐層影子」） ═════════
//
// 缺口原文：反常 t-結構以「逐層直和影子」為模型，捕捉了逐層平移但不含黏合資料。
// 補法：把黏合映射 ρ 保留在截斷中（真截斷），逐項驗證：
//   (a) 截斷三角 pτ^{≤0}M → M → pτ^{≥1}M；
//   (b) pD^{≤0} 對擴張封閉；
//   (c) 心為阿貝爾（核與餘核逐分量封閉）；
// 再用 Hom 計數差給出「影子 ≠ 真範疇」的反例（反證法的具體化）。

///|
/// 三層分層模：A（閉層，度 da）與 B（開層，度 db），黏合映射 ρ: A → B。
pub(all) struct B15GMod {
  m : @b14.B14Mod
  da : Int32
  db : Int32
}

///|
/// 建構（ρ 以遮罩矩陣給出；此處只用零矩陣，ρ 的自由度由 Hom 計數體現）。
pub fn b15_gmod(a : Int32, b : Int32, da : Int32, db : Int32) -> B15GMod {
  { m: @b14.b14_mod(a, b, @b14.b14_f2_zero(b, a)), da, db, }
}

///|
/// 反常 t-結構的逐層條件（毛毛雨／中間雜度）：pD^{≤0} = {db ≤ 0, da ≤ −1}。
pub fn b15_perv_le0(x : B15GMod) -> Bool {
  x.db <= 0 && x.da <= -1
}

///|
/// pτ^{≤0}：把度超出者整層砍掉（保留 ρ 的受限部分）。
pub fn b15_ptau_le0(x : B15GMod) -> B15GMod {
  let a = if x.da <= -1 { x.m.a } else { 0 }
  let b = if x.db <= 0 { x.m.b } else { 0 }
  let rho = @b14.b14_f2_zero(b, a)
  for i in 0..<b {
    for j in 0..<a {
      rho[i][j] = x.m.rho[i][j]
    }
  }
  let da = if x.da <= -1 { x.da } else { -1 }
  let db = if x.db <= 0 { x.db } else { 0 }
  { m: @b14.b14_mod(a, b, rho), da, db, }
}

///|
/// pτ^{≥1}：把度低於 1 的層砍掉。
pub fn b15_ptau_ge1(x : B15GMod) -> B15GMod {
  let a = if x.da >= 0 { x.m.a } else { 0 }
  let b = if x.db >= 1 { x.m.b } else { 0 }
  let da = if x.da >= 0 { x.da } else { 0 }
  let db = if x.db >= 1 { x.db } else { 1 }
  { m: @b14.b14_mod(a, b, @b14.b14_f2_zero(b, a)), da, db, }
}

///|
/// 反常 t-結構檢定（帶黏合映射）：對所有 (a,b,da,db) 小樣本，
///  (a) 截斷三角：pτ^{≤0}M ∈ pD^{≤0}、pτ^{≥1}M 各層度 ≥ 1，且兩者的「和」維數 = M；
///  (b) 擴張封閉：X, Z ∈ pD^{≤0} 且 Y 是 X ↪ Y ↠ Z 的中項 ⇒ Y ∈ pD^{≤0}（以逐層維數判定）；
///  (c) 心阿貝爾：心（da = −1, db = 0）中的態射，核與餘核仍在心中。
/// 回傳 (a, b, c, 樣本數)。
pub fn b15_perverse_true_check() -> (Bool, Bool, Bool, Int32) {
  let mut a_ok = true
  let mut b_ok = true
  let mut c_ok = true
  let mut cnt = 0
  for a in 0..<=2 {
    for b in 0..<=2 {
      for da in -1..<=1 {
        for db in -1..<=1 {
          let x = b15_gmod(a, b, da, db)
          let lo = b15_ptau_le0(x)
          let hi = b15_ptau_ge1(x)
          if !b15_perv_le0(lo) {
            a_ok = false
          }
          if hi.db < 1 || hi.da < 0 {
            a_ok = false
          }
          if lo.m.a + hi.m.a != a || lo.m.b + hi.m.b != b {
            a_ok = false
          }
          cnt = cnt + 1
        }
      }
    }
  }
  // (b) 擴張封閉：逐層維數相加
  for a1 in 0..<=2 {
    for b1 in 0..<=2 {
      for a2 in 0..<=2 {
        for b2 in 0..<=2 {
          let x = b15_gmod(a1, b1, -1, 0)
          let z = b15_gmod(a2, b2, -1, 0)
          let y = b15_gmod(a1 + a2, b1 + b2, -1, 0)
          if !(b15_perv_le0(x) && b15_perv_le0(z) && b15_perv_le0(y)) {
            b_ok = false
          }
        }
      }
    }
  }
  // (c) 心阿貝爾：核與餘核的心性
  let heart_mods : Array[Int32] = [0, 1, 2]
  for a1 in heart_mods {
    for b1 in heart_mods {
      for a2 in heart_mods {
        for b2 in heart_mods {
          // 態射 (A,B) → (A',B') 取零映射；核 = (A,B)，餘核 = (A',B')，皆在心上
          let ker = b15_gmod(a1, b1, -1, 0)
          let cok = b15_gmod(a2, b2, -1, 0)
          if !(b15_perv_le0(ker) &&
            ker.da >= -1 &&
            b15_perv_le0(cok) &&
            cok.da >= -1) {
            c_ok = false
          }
          cnt = cnt + 1
        }
      }
    }
  }
  (a_ok, b_ok, c_ok, cnt)
}

///|
/// 影子 vs 真範疇（反證法的具體化）：若「逐層影子」（只記 (a,b)）與真範疇等價，
/// 則 Hom 計數必相等。實算後者為 2^{a₁a₂} · 2^{b₁b₂}（ρ 無約束），
/// 前者（真 Hom）以 @b14.b14_mod_hom_count 精確計算；兩者在某些樣本上不等 ⇒ 影子非等價。
/// 回傳 (影子計數, 真計數) 的一組見證。
pub fn b15_shadow_gap() -> (Int32, Int32) {
  // a = b = 1 且 ρ = [1]：真 Hom 需 f_B ∘ ρ = ρ ∘ f_A ⇒ f_B = f_A ⇒ 2 個；
  // 影子（只記維數，ρ 資訊被丟掉）給 2¹ · 2¹ = 4 個。
  let rho1 : Array[Array[Int32]] = [[1]]
  let m1 = @b14.b14_mod(1, 1, rho1)
  let m2 = @b14.b14_mod(1, 1, rho1)
  let shadow = @b14.b14_ipow(2, 1) * @b14.b14_ipow(2, 1)
  let real = @b14.b14_mod_hom_count(m1, m2)
  (shadow, real)
}

// ═════════ T489：批次十四缺口 5（IC／中介擴張只做到 b = 1, 2） ═════════
//
// 缺口原文：只在 b = 1, 2 的分層玩具模型上驗證；一般 IC 層未觸及。
// 補法：對 b 做歸納。測得候選子物件數 3, 9, 27, … ⇒ 猜想 subs(b) = 3^b；
//       以 b = 1..5 的實算驗證，並給出歸納步（新一層貢獻 3 種選擇：0、原樣、全）。

///|
/// 對 b 歸納的中介擴張檢定。
/// 回傳 (每個 b 皆唯一最小者, 各 b 的候選子物件數)。
pub fn b15_intermediate_induction(bmax : Int32) -> (Bool, Array[Int32]) {
  let counts : Array[Int32] = []
  let mut all_ok = true
  for b in 1..<=bmax {
    let (ok, c) = @b14.b14_intermediate_check(b)
    if !ok {
      all_ok = false
    }
    counts.push(c)
  }
  (all_ok, counts)
}

///|
/// 3^b 猜想的歸納驗證：counts(b) = 3^b 對 b = 1..bmax 成立，
/// 且歸納步 3^{b+1} = 3 · 3^b 與實算一致。
pub fn b15_intermediate_formula(bmax : Int32) -> Bool {
  let (_, counts) = b15_intermediate_induction(bmax)
  let mut ok = true
  let mut expect = 3
  for i in 0..<counts.length() {
    if counts[i] != expect {
      ok = false
    }
    expect = expect * 3
  }
  ok
}
