///|
/// welling.mbt — 批次八·模組 6：良基與超良基組合結構
///
/// 以「雜湊駐留（hash-consing）」登錄表表示繼承有限集（hereditarily finite sets, HF）：
/// 每個集合的成員表唯一決定其編號，故結構相等 = 編號相等。
///
/// 可計算的內容：
///   1. 累積層級 V_0 = ∅、V_{n+1} = V_n ∪ P(V_n)：|V_n| = 0,1,2,4,16,65536,…
///   2. 秩（rank）與遞移閉包大小的精確計算。
///   3. Mostowski 崩塌：有限良基關係 → 遞移集；崩塌為單射 ⟺ 外延性成立。
///   4. 超良基（AFA）結構：有限圖的裝飾（decoration）之存在唯一性，
///      以及「在良基宇宙中無解、在超良基宇宙中唯一解」的量化對比
///      （例如 x = {x} 的 Ω）。

// ───────────────────────── 雜湊駐留的繼承有限集 ─────────────────────────

///|
/// HF 集登錄表：lists[i] 為第 i 個集合的成員編號（遞增、去重）。編號 0 恆為 ∅。
pub(all) struct B8Reg {
  lists : Array[Array[Int32]]
}

///|
/// 空登錄表：先放入 ∅。
pub fn b8reg_new() -> B8Reg {
  let e : Array[Int32] = []
  { lists: [e], }
}

///|
/// 取得集合（若不存在則新增）；成員表會先排序去重。
pub fn b8reg_set(r : B8Reg, members : Array[Int32]) -> Int32 {
  let ms : Array[Int32] = []
  for m in members {
    ms.push(m)
  }
  // 插入排序 + 去重
  for i in 1..<ms.length() {
    let v = ms[i]
    let mut j = i - 1
    while j >= 0 && ms[j] > v {
      ms[j + 1] = ms[j]
      j = j - 1
    }
    ms[j + 1] = v
  }
  let uniq : Array[Int32] = []
  for k in 0..<ms.length() {
    if k == 0 || uniq[uniq.length() - 1] != ms[k] {
      uniq.push(ms[k])
    }
  }
  // 查表
  for i in 0..<r.lists.length() {
    let l = r.lists[i]
    let mut eq = l.length() == uniq.length()
    if eq {
      for t in 0..<l.length() {
        if l[t] != uniq[t] {
          eq = false
        }
      }
    }
    if eq {
      return i
    }
  }
  r.lists.push(uniq)
  r.lists.length() - 1
}

///|
/// 集合的成員表。
pub fn b8reg_members(r : B8Reg, i : Int32) -> Array[Int32] {
  r.lists[i]
}

///|
/// 累積層級 V_n 的元素編號清單（V_0 = ∅）。
pub fn b8reg_level(r : B8Reg, n : Int32) -> Array[Int32] {
  let mut cur : Array[Int32] = []
  for _ in 0..<n {
    // 取所有子集
    let k = cur.length()
    let nsub = b8u_pow2_int(k)
    let nxt : Array[Int32] = []
    for mask in 0..<nsub {
      let members : Array[Int32] = []
      for b in 0..<k {
        if ((mask >> b) & 1) == 1 {
          members.push(cur[b])
        }
      }
      nxt.push(b8reg_set(r, members))
    }
    cur = nxt
  }
  cur
}

///|
/// 2^k（Int32，k ≤ 30）。
pub fn b8u_pow2_int(k : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<k {
    r = r * 2
  }
  r
}

///|
/// 集合的秩：rank(∅) = 0，rank(x) = 1 + max rank(成員)。
pub fn b8reg_rank(r : B8Reg, i : Int32) -> Int32 {
  let ms = r.lists[i]
  let mut m = -1
  for x in ms {
    let rx = b8reg_rank(r, x)
    if rx > m {
      m = rx
    }
  }
  m + 1
}

///|
/// 是否為遞移集：每個成員的成員也是成員。
pub fn b8reg_transitive(r : B8Reg, i : Int32) -> Bool {
  let ms = r.lists[i]
  for x in ms {
    for y in r.lists[x] {
      let mut found = false
      for z in ms {
        if z == y {
          found = true
        }
      }
      if !found {
        return false
      }
    }
  }
  true
}

///|
/// 幂集是否封閉：對每個成員 x，P(x) 仍是成員。
pub fn b8reg_pow_closed(r : B8Reg, i : Int32) -> Bool {
  let ms = r.lists[i]
  for x in ms {
    let px = b8reg_powerset(r, x)
    let mut found = false
    for z in ms {
      if z == px {
        found = true
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
/// 幂集。
pub fn b8reg_powerset(r : B8Reg, i : Int32) -> Int32 {
  let ms = r.lists[i]
  let k = ms.length()
  let subs : Array[Int32] = []
  for mask in 0..<b8u_pow2_int(k) {
    let members : Array[Int32] = []
    for b in 0..<k {
      if ((mask >> b) & 1) == 1 {
        members.push(ms[b])
      }
    }
    subs.push(b8reg_set(r, members))
  }
  b8reg_set(r, subs)
}

///|
/// 聯集（廣義並集）是否封閉：對每個成員 x，⋃x 仍是成員。
pub fn b8reg_union_closed(r : B8Reg, i : Int32) -> Bool {
  let ms = r.lists[i]
  for x in ms {
    let ux = b8reg_bigunion(r, x)
    let mut found = false
    for z in ms {
      if z == ux {
        found = true
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
/// 廣義並集 ⋃x。
pub fn b8reg_bigunion(r : B8Reg, i : Int32) -> Int32 {
  let all : Array[Int32] = []
  for x in r.lists[i] {
    for y in r.lists[x] {
      all.push(y)
    }
  }
  b8reg_set(r, all)
}

// ───────────────────────── Mostowski 崩塌 ─────────────────────────

///|
/// 以拓撲排序（後序 DFS）求良基關係 x ↦ {y : y ∈ x}（edges[x] = x 的成員）的 Mostowski 崩塌。
/// 回傳每個節點崩塌後的集合編號；若關係有環則回傳空陣列。
pub fn b8reg_mostowski(r : B8Reg, edges : Array[Array[Int32]]) -> Array[Int32] {
  let n = edges.length()
  let out : Array[Int32] = []
  for _ in 0..<n {
    out.push(-1)
  }
  // 迭代式 DFS（偵測環）
  let state : Array[Int32] = []
  for _ in 0..<n {
    state.push(0)
  }
  let mut cyclic = false
  // 顯式堆疊：stack 為節點，idxs 為已完成子節點數
  let stack : Array[Int32] = []
  let idxs : Array[Int32] = []
  for s in 0..<n {
    if state[s] != 0 {
      continue
    }
    stack.push(s)
    idxs.push(0)
    state[s] = 1
    while stack.length() > 0 {
      let top = stack[stack.length() - 1]
      let k = idxs[stack.length() - 1]
      if k < edges[top].length() {
        idxs[stack.length() - 1] = k + 1
        let y = edges[top][k]
        if state[y] == 0 {
          stack.push(y)
          idxs.push(0)
          state[y] = 1
        } else if state[y] == 1 {
          cyclic = true
        }
      } else {
        // 子節點全部完成：建集合
        let members : Array[Int32] = []
        for y in edges[top] {
          if out[y] >= 0 {
            members.push(out[y])
          }
        }
        out[top] = b8reg_set(r, members)
        state[top] = 2
        let _ = stack.pop()
        let _ = idxs.pop()
      }
    }
  }
  if cyclic {
    return []
  }
  out
}

///|
/// 崩塌是否為單射（⟺ 關係具外延性）。
pub fn b8reg_collapse_injective(ids : Array[Int32]) -> Bool {
  let mut ok = true
  for i in 0..<ids.length() {
    for j in 0..<ids.length() {
      if i != j && ids[i] == ids[j] {
        ok = false
      }
    }
  }
  ok
}

///|
/// 關係是否外延：任兩個不同節點的成員集合不同。
pub fn b8reg_extensional(edges : Array[Array[Int32]]) -> Bool {
  let n = edges.length()
  let mut ok = true
  for i in 0..<n {
    for j in 0..<n {
      if i != j {
        let mut same = edges[i].length() == edges[j].length()
        if same {
          // 比較集合
          for a in edges[i] {
            let mut found = false
            for b in edges[j] {
              if a == b {
                found = true
              }
            }
            if !found {
              same = false
            }
          }
        }
        if same {
          ok = false
        }
      }
    }
  }
  ok
}

// ───────────────────────── 超良基（AFA）結構 ─────────────────────────

///|
/// 有限圖的雙模擬（bisimulation）最粗劃分：反覆細化（以「成員類別集合」為簽名）。
/// edges[x] 為 x 的前驅（x 的「成員」）；回傳每節點的類別編號。
pub fn b8reg_bisim(edges : Array[Array[Int32]]) -> Array[Int32] {
  let n = edges.length()
  let mut cls : Array[Int32] = []
  for _ in 0..<n {
    cls.push(0)
  }
  let mut changed = true
  while changed {
    changed = false
    // 以（舊類別, 排序後的成員類別）為簽名重新編號
    let sigs : Array[Array[Int32]] = []
    for x in 0..<n {
      let s : Array[Int32] = [cls[x]]
      for y in edges[x] {
        s.push(cls[y])
      }
      s.push(-1)
      sigs.push(s)
    }
    let ncls : Array[Int32] = []
    for _ in 0..<n {
      ncls.push(0)
    }
    let mut k = 0
    for x in 0..<n {
      let mut found = -1
      for y in 0..<x {
        if b8reg_sig_eq(sigs[x], sigs[y]) {
          found = ncls[y]
        }
      }
      if found >= 0 {
        ncls[x] = found
      } else {
        ncls[x] = k
        k = k + 1
      }
    }
    for x in 0..<n {
      if ncls[x] != cls[x] {
        changed = true
      }
    }
    cls = ncls
    // 類別數不再變化即穩定
    let mut mx = -1
    for x in 0..<n {
      if cls[x] > mx {
        mx = cls[x]
      }
    }
    if mx + 1 == n {
      // 每點自成一類，必穩定
      break
    }
  }
  cls
}

///|
/// 簽名相等（忽略成員順序）。
fn b8reg_sig_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let sa : Array[Int32] = []
  let sb : Array[Int32] = []
  for x in a {
    sa.push(x)
  }
  for x in b {
    sb.push(x)
  }
  // 排序
  for arr in [sa, sb] {
    for i in 1..<arr.length() {
      let v = arr[i]
      let mut j = i - 1
      while j >= 0 && arr[j] > v {
        arr[j + 1] = arr[j]
        j = j - 1
      }
      arr[j + 1] = v
    }
  }
  let mut eq = true
  for i in 0..<sa.length() {
    if sa[i] != sb[i] {
      eq = false
    }
  }
  eq
}

///|
/// 有限圖的 AFA 裝飾類別數（= 雙模擬商的大小）。
pub fn b8afa_decor_classes(edges : Array[Array[Int32]]) -> Int32 {
  let cls = b8reg_bisim(edges)
  let mut mx = -1
  for c in cls {
    if c > mx {
      mx = c
    }
  }
  mx + 1
}

///|
/// 在良基宇宙 V_level（以層級元素清單）中窮舉「x = {y : y ∈ x}」的解：
/// edges[i] 為節點 i 的成員節點；回傳滿足下列條件的賦值數：
///   ∀i, val(i) = { val(j) : j ∈ edges[i] }（以 HF 集合相等判斷）。
/// 若存在環，則通常無良基解（回傳 0 或少量解）。
pub fn b8wf_solution_count(
  r : B8Reg,
  edges : Array[Array[Int32]],
  universe : Array[Int32],
) -> Int32 {
  let n = edges.length()
  let k = universe.length()
  if n == 0 {
    return 1
  }
  if n > 3 {
    return -1
  }
  if universe.length() == 0 {
    return 0
  }
  let val : Array[Int32] = []
  for _ in 0..<n {
    val.push(0)
  }
  let mut count = 0
  let total = b8_pow_int(k, n)
  for code in 0..<total {
    let mut c = code
    for i in 0..<n {
      val[i] = universe[c % k]
      c = c / k
    }
    let mut ok = true
    for i in 0..<n {
      let members : Array[Int32] = []
      for j in edges[i] {
        members.push(val[j])
      }
      let target = b8reg_set(r, members)
      if target != val[i] {
        ok = false
      }
    }
    if ok {
      count = count + 1
    }
  }
  count
}
