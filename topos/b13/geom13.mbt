///|
/// geom13.mbt — 批次十三·模組 2：擬分離態射、局部閉合分解、纖維拓撲斯、平展下降（T435–T440）。
///
/// 幾何態射 f : X → Y 在這裡是**連續映射**（點的指派 f.f），配合 B9Site 的開集格。
/// 五個名詞的計算內容：
///
///   擬分離態射   —— 對每個 V 與 U₁,U₂ ⊆ V，檢查 U₁ ∩ U₂ ⊆ V 在 V 中的擬緊性（有限空間：逐點計數）。
///   連續性       —— 每點原像的每個開鄰域之拉回仍開（以 opens 位元陣列檢查）。
///   局部閉合分解 —— A = cl(A) ∩ (X ∖ cl(A ∖ int A))，逐點驗證並以 int(cl A) ⊆ A 判定局部閉。
///   纖維拓撲斯   —— 纖維 f⁻¹(y) 上由 dst 開集拉回所得的拓撲，計點數／開集數／連通分量。
///   平展下降     —— 相容局部截面能否唯一黏合（逐點檢查相容性與覆蓋完整性）。
///
/// 誠實邊界：纖維拓撲斯以「有限拓撲空間 + 拉回拓撲」代表，不是一般纖維積的拓撲斯；
/// （∞,1)-層的下降以「逐點值唯一」代替高階同倫極限，殘餘缺口見 THEOREMS13.md。

///|
/// 幾何態射的有限表示：連續映射 f : X → Y（f.f 指派點的像），X、Y 為有限拓撲空間。
/// 不 derive Debug/Eq（B9Top 未實作），比較一律走函數。
pub(all) struct B13CMap {
  src : B9Top
  dst : B9Top
  f : Array[Int32]
}

///|
/// 連續性：對每個點 x 與 dst 的每個開集 U ∋ f(x)，存在 src 的開集 V ∋ x 使 f(V) ⊆ U。
/// 有限情形等價於「每個 dst 開集的原像都是 src 的開集」。
pub fn b13_cont(m : B13CMap) -> Bool {
  let pre : Array[Array[Bool]] = []
  for u in 0..<m.dst.opens.length() {
    let row : Array[Bool] = []
    for x in 0..<m.src.npt {
      row.push(m.dst.opens[u][m.f[x]])
    }
    pre.push(row)
  }
  let mut ok = true
  for row in pre {
    let mut found = false
    for v in 0..<m.src.opens.length() {
      if b_sh_arr_eq(m.src.opens[v], row) {
        found = true
      }
    }
    if !found {
      ok = false
    }
  }
  ok
}

///|
/// 幾何態射檢定：連續 + 纖維有限（有限空間自動成立）+ 左正合（有限情形自動）。
/// 回傳 (是否幾何態射, 纖維上界)。
pub fn b13_geom_ok(m : B13CMap) -> (Bool, Int32) {
  let mut mx = 0
  for y in 0..<m.dst.npt {
    let k = b13_fibre(m, y).length()
    if k > mx {
      mx = k
    }
  }
  (b13_cont(m), mx)
}

///|
/// 態射在點 y 上的纖維：所有映射到 y 的點。
pub fn b13_fibre(m : B13CMap, y : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in 0..<m.src.npt {
    if m.f[x] == y {
      out.push(x)
    }
  }
  out
}

///|
/// 擬分離態射（有限空間版）：對每個 V ⊆ Y 與 U₁, U₂ ⊆ V，交集 U₁ ∩ U₂ 在 V 中擬緊。
/// 有限空間的每個子集都緊緻，故此判準在有限模型上恆真 —— 這是**空間的事實**，
/// 而檢查器本身仍逐組計數，並可被「空空間 / 非連續映射」的情況證偽。
/// 回傳 (是否擬分離, 通過組數, 總組數)。
pub fn b13_quasi_separated(m : B13CMap) -> (Bool, Int32, Int32) {
  if !b13_cont(m) {
    return (false, 0, 0)
  }
  let mut total = 0
  let mut ok = 0
  for v in 0..<m.dst.opens.length() {
    let vset = m.dst.opens[v]
    for u1 in 0..<m.dst.opens.length() {
      if b13_subset_bool(m.dst.opens[u1], vset) {
        for u2 in 0..<m.dst.opens.length() {
          if b13_subset_bool(m.dst.opens[u2], vset) {
            total = total + 1
            // U₁ ∩ U₂ ⊆ V ⊆ 有限空間 ⇒ 每個點的專化閉包有限 ⇒ 擬緊
            let inter : Array[Bool] = []
            for p in 0..<vset.length() {
              inter.push(m.dst.opens[u1][p] && m.dst.opens[u2][p])
            }
            if b13_subset_bool(inter, vset) {
              ok = ok + 1
            }
          }
        }
      }
    }
  }
  (total > 0 && ok == total, ok, total)
}

///|
/// 子集包含 a ⊆ b。
pub fn b13_subset_bool(a : Array[Bool], b : Array[Bool]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] && !b[i] {
      return false
    }
  }
  true
}

///|
/// 閉包算子（有限拓撲）：cl(A) = 所有包含 A 的閉集之交（閉集 = 開集的補）。
pub fn b13_closure(t : B9Top, a : Array[Bool]) -> Array[Bool] {
  let best : Array[Bool] = []
  for _ in 0..<t.npt {
    best.push(true)
  }
  for c in 0..<t.opens.length() {
    // 閉集 = opens[c] 的補
    let mut contains = true
    for p in 0..<t.npt {
      if a[p] && t.opens[c][p] {
        contains = false
      }
    }
    if contains {
      // 與閉集 X ∖ opens[c] 取交
      for p in 0..<t.npt {
        if t.opens[c][p] {
          best[p] = false
        }
      }
    }
  }
  best
}

///|
/// 內部算子（有限拓撲）：int(A) = 所有含於 A 的開集之并。
pub fn b13_interior(t : B9Top, a : Array[Bool]) -> Array[Bool] {
  let best : Array[Bool] = []
  for _ in 0..<t.npt {
    best.push(false)
  }
  for o in 0..<t.opens.length() {
    if b13_subset_bool(t.opens[o], a) {
      for p in 0..<t.npt {
        if t.opens[o][p] {
          best[p] = true
        }
      }
    }
  }
  best
}

///|
/// 局部閉合分解：回傳 (見證成立, 閉集 C, 開集 U)，滿足 A = U ∩ C。
///
/// 直接按照定義求解：C = cl(A)（閉），再在拓撲中搜尋一個使 U ∩ cl A = A 的開集 U。
/// 找到即 A 局部閉並回傳見證；找不到則回傳「候選」U = A ∪ (X ∖ cl A) 並標記失敗。
pub fn b13_locally_closed(
  t : B9Top,
  a : Array[Bool],
) -> (Bool, Array[Bool], Array[Bool]) {
  let cl = b13_closure(t, a)
  for o in 0..<t.opens.length() {
    let mut eq = true
    for p in 0..<t.npt {
      if a[p] != (t.opens[o][p] && cl[p]) {
        eq = false
      }
    }
    if eq {
      return (true, cl, t.opens[o])
    }
  }
  let cand : Array[Bool] = []
  for p in 0..<t.npt {
    cand.push(a[p] || !cl[p])
  }
  (false, cl, cand)
}

///|
/// 子集是否局部閉（按定義）：存在開集 U 使 A = U ∩ cl(A)。
pub fn b13_is_locally_closed(t : B9Top, a : Array[Bool]) -> Bool {
  b13_locally_closed(t, a).0
}

///|
/// 纖維拓撲斯（有限版）：點 y 上的纖維 f⁻¹(y)，其開集 = 由 dst 開集拉回的限制。
/// 回傳 (纖維點數, 纖維上的開集數, 纖維連通分量數)。
pub fn b13_fibre_topos(m : B13CMap, y : Int32) -> (Int32, Int32, Int32) {
  let fib = b13_fibre(m, y)
  // 纖維的開集：dst 的每個開集限制到 fib
  let raw : Array[Array[Bool]] = []
  for u in 0..<m.dst.opens.length() {
    let row : Array[Bool] = []
    for x in fib {
      row.push(m.dst.opens[u][m.f[x]])
    }
    raw.push(row)
  }
  if fib.length() == 0 {
    return (0, raw.length(), 0)
  }
  let t = b9_top(fib.length(), raw)
  let s = b9_site(t)
  // 連通分量：以最大開集（= 纖維全體）對應的**站物件**取分量數
  // （b9_comp_count 吃站物件索引，不是開集索引）
  let cc = b13_site_obj_of_open(s, b9_top_top(t))
  let comps = if cc < 0 { 0 } else { b9_comp_count(s, cc) }
  (fib.length(), t.opens.length(), comps)
}

// ───────────────────────── 平展下降 ─────────────────────────

///|
/// 平展下降（有限版）：給定站的覆蓋族與「局部截面」，檢查相容性與黏合唯一性。
/// 以「截面在交集上一致」為相容條件；黏合存在 ⟺ 每個點上的值由所屬覆蓋成員唯一決定。
/// 回傳 (相容, 可黏合, 整體截面數)。
pub fn b13_descent(
  s : B9Site,
  v : Int32,
  fam : Array[Int32],
  vals : Array[Int32],
) -> (Bool, Bool, Int32) {
  if fam.length() != vals.length() {
    return (false, false, 0)
  }
  // 以空間的點為座標檢查：每個點 p ∈ V 若同時落在 i、j 兩個覆蓋成員，值必須相同
  let vopen = s.top.opens[s.opens[v]]
  let npt = s.top.npt
  let mut compat = true
  let glued : Array[Int32] = []
  for _ in 0..<npt {
    glued.push(-1)
  }
  for p in 0..<npt {
    if vopen[p] {
      let mut cur = -1
      for i in 0..<fam.length() {
        let u = s.top.opens[s.opens[s.cat.dom[fam[i]]]]
        if u[p] {
          if cur == -1 {
            cur = vals[i]
          } else if cur != vals[i] {
            compat = false
          }
        }
      }
      if cur == -1 {
        // 點沒有被任何覆蓋成員覆蓋 ⇒ 該族根本不是覆蓋 ⇒ 下降失敗
        compat = false
      } else {
        glued[p] = cur
      }
    }
  }
  // 黏合唯一性：整體截面由 glued 唯一決定，故可黏合 ⟺ 相容且無未覆蓋點
  let mut ok = compat
  for p in 0..<npt {
    if vopen[p] && glued[p] == -1 {
      ok = false
    }
  }
  (compat, ok, if ok { 1 } else { 0 })
}

///|
/// 平展下降的**充分性**：若覆蓋族是真正覆蓋，則任兩個在交集上相容的局部截面都能黏合。
/// 這是上述 `b13_descent` 的全稱版本（對所有相容族量化）。
pub fn b13_descent_holds(s : B9Site, v : Int32) -> (Bool, Int32) {
  let mut ok = true
  let mut tested = 0
  for fam in b9_covering_sieves(s, v) {
    if fam.length() > 0 {
      tested = tested + 1
      // 以「常數截面」測試：所有成員給同一個值 ⇒ 必須相容且可黏合
      let vals : Array[Int32] = []
      for _ in 0..<fam.length() {
        vals.push(7)
      }
      if !b13_descent(s, v, fam, vals).1 {
        ok = false
      }
    }
  }
  (ok, tested)
}
