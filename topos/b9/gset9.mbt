///|
/// gset9.mbt — 批次九·模組 6：群作用拓撲斯（Set^G ≅ Sh(BG)）
///
/// 有限群以乘法表給出（mul[g*k+h] = g·h，單位元編號 0）。
/// G-集合 = (n, act)，act[g*n+x] = g·x。BG 為單物件範疇，其上的預層即 G-集合；
/// 由於 BG 的唯一覆蓋篩是極大篩，Sh(BG) = PSh(BG) = Set^G。
///
/// 定理路線：
///   不變量 (−)^G ⊣ 平凡作用 triv ⊣ 餘不變量（軌道）(−)_G
///   軌道–穩定化子定理、Burnside 引理
///   扭子（torsor）：自由遞移作用 ⟹ 恰一個同構類、自同構群 ≅ G
///   分類拓撲斯：Set^G 的「點」= G-扭子（H¹(G;G) 的分類性質）

// ───────────────────────── 有限群 ─────────────────────────

///|
/// 有限群：k 個元素，mul[g*k+h] = g·h，單位元為 0。
pub(all) struct B9Group {
  k : Int32
  mul : Array[Int32]
}

///|
/// 群公理：封閉、結合、單位元、反元素存在。
pub fn b9_group_ok(g : B9Group) -> Bool {
  for a in 0..<g.k {
    for b in 0..<g.k {
      for c in 0..<g.k {
        let l = g.mul[g.mul[a * g.k + b] * g.k + c]
        let r = g.mul[a * g.k + g.mul[b * g.k + c]]
        if l != r {
          return false
        }
      }
    }
  }
  for a in 0..<g.k {
    if g.mul[0 * g.k + a] != a || g.mul[a * g.k + 0] != a {
      return false
    }
  }
  for a in 0..<g.k {
    let mut inv = false
    for b in 0..<g.k {
      if g.mul[a * g.k + b] == 0 && g.mul[b * g.k + a] == 0 {
        inv = true
      }
    }
    if !inv {
      return false
    }
  }
  true
}

///|
/// 循環群 Z/n。
pub fn b9_group_zn(n : Int32) -> B9Group {
  let mul : Array[Int32] = []
  for a in 0..<n {
    for b in 0..<n {
      mul.push((a + b) % n)
    }
  }
  { k: n, mul, }
}

///|
/// Klein 四元群 Z/2 × Z/2（以位元編碼）。
pub fn b9_group_v4() -> B9Group {
  let mul : Array[Int32] = []
  for a in 0..<4 {
    for b in 0..<4 {
      mul.push(a ^ b)
    }
  }
  { k: 4, mul, }
}

///|
/// 對稱群 S_3（以置換的合成表給出，元素以陣列的字典序編號）。
pub fn b9_group_s3() -> B9Group {
  // 6 個置換，編號 = 其 (p0,p1,p2) 的排列序
  let perms : Array[Array[Int32]] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
  ]
  let idx : Array[Array[Int32]] = []
  let mul : Array[Int32] = []
  // 合成 (a∘b)(i) = a[b[i]]
  let comp : Array[Array[Int32]] = []
  for a in 0..<6 {
    for b in 0..<6 {
      let c : Array[Int32] = []
      for i in 0..<3 {
        c.push(perms[a][perms[b][i]])
      }
      comp.push(c)
    }
  }
  for a in 0..<6 {
    for b in 0..<6 {
      let c = comp[a * 6 + b]
      let mut pos = -1
      for t in 0..<6 {
        if b_sh_arr_eq(c, perms[t]) {
          pos = t
        }
      }
      mul.push(pos)
    }
  }
  let _ = idx
  { k: 6, mul, }
}

// ───────────────────────── G-集合 ─────────────────────────

///|
/// G-集合：n 個元素，act[g*n+x] = g·x。
pub(all) struct B9GSet {
  grp : B9Group
  n : Int32
  act : Array[Int32]
}

///|
/// 作用公理。
pub fn b9_gset_ok(s : B9GSet) -> Bool {
  let g = s.grp
  for x in 0..<s.n {
    if s.act[0 * s.n + x] != x {
      return false
    }
  }
  for a in 0..<g.k {
    for b in 0..<g.k {
      let ab = g.mul[a * g.k + b]
      for x in 0..<s.n {
        if s.act[ab * s.n + x] != s.act[a * s.n + s.act[b * s.n + x]] {
          return false
        }
      }
    }
  }
  true
}

///|
/// 平凡作用。
pub fn b9_gset_triv(g : B9Group, n : Int32) -> B9GSet {
  let act : Array[Int32] = []
  for _ in 0..<g.k {
    for x in 0..<n {
      act.push(x)
    }
  }
  { grp: g, n, act, }
}

///|
/// 正則作用：G 作用於自身（左乘）。act[g*k+h] = g·h。
pub fn b9_gset_reg(g : B9Group) -> B9GSet {
  let act : Array[Int32] = []
  for a in 0..<g.k {
    for x in 0..<g.k {
      act.push(g.mul[a * g.k + x])
    }
  }
  { grp: g, n: g.k, act, }
}

///|
/// 左乘作用在任意表上（由生成元的置換生成整個作用）。
pub fn b9_gset_of_perms(g : B9Group, n : Int32, perms : Array[Int32]) -> B9GSet {
  // perms[g*n+x] = g·x 已給定
  { grp: g, n, act: perms, }
}

///|
/// 不動點個數。
pub fn b9_fix_count(s : B9GSet, gi : Int32) -> Int32 {
  let mut c = 0
  for x in 0..<s.n {
    if s.act[gi * s.n + x] == x {
      c = c + 1
    }
  }
  c
}

///|
/// 不變量個數 |X^G|。
pub fn b9_invariants(s : B9GSet) -> Int32 {
  let mut c = 0
  for x in 0..<s.n {
    let mut inv = true
    for gi in 0..<s.grp.k {
      if s.act[gi * s.n + x] != x {
        inv = false
      }
    }
    if inv {
      c = c + 1
    }
  }
  c
}

///|
/// 軌道分解：回傳每個元素的軌道編號（以最小元素為代表）。
pub fn b9_orbit_ids(s : B9GSet) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in 0..<s.n {
    out.push(x)
  }
  for gi in 0..<s.grp.k {
    for x in 0..<s.n {
      let y = s.act[gi * s.n + x]
      let rx = out[x]
      let ry = out[y]
      let lo = if rx < ry { rx } else { ry }
      out[x] = lo
      out[y] = lo
    }
  }
  // 迭代至穩定
  let mut changed = true
  while changed {
    changed = false
    for x in 0..<s.n {
      for gi in 0..<s.grp.k {
        let y = s.act[gi * s.n + x]
        let lo = if out[x] < out[y] { out[x] } else { out[y] }
        if out[x] != lo || out[y] != lo {
          out[x] = lo
          out[y] = lo
          changed = true
        }
      }
    }
  }
  out
}

///|
/// 軌道個數。
pub fn b9_orbit_count(s : B9GSet) -> Int32 {
  let ids = b9_orbit_ids(s)
  let mut c = 0
  for x in 0..<s.n {
    let mut first = true
    for y in 0..<x {
      if ids[y] == ids[x] {
        first = false
      }
    }
    if first {
      c = c + 1
    }
  }
  c
}

///|
/// 穩定化子大小。
pub fn b9_stab_size(s : B9GSet, x : Int32) -> Int32 {
  let mut c = 0
  for gi in 0..<s.grp.k {
    if s.act[gi * s.n + x] == x {
      c = c + 1
    }
  }
  c
}

///|
/// G-等變映射個數 |Hom_G(A, B)|（暴力枚舉）。
pub fn b9_hom_gset(a : B9GSet, b : B9GSet) -> Int32 {
  let g = a.grp
  if b.n == 0 {
    return if a.n == 0 { 1 } else { 0 }
  }
  let cur : Array[Int32] = []
  for _ in 0..<a.n {
    cur.push(0)
  }
  let mut cnt = 0
  let mut done = false
  while !done {
    let mut ok = true
    for gi in 0..<g.k {
      for x in 0..<a.n {
        let lhs = cur[a.act[gi * a.n + x]]
        let rhs = b.act[gi * b.n + cur[x]]
        if lhs != rhs {
          ok = false
        }
      }
    }
    if ok {
      cnt = cnt + 1
    }
    let mut k = 0
    let mut carry = true
    while carry && k < a.n {
      cur[k] = cur[k] + 1
      if cur[k] >= b.n {
        cur[k] = 0
        k = k + 1
      } else {
        carry = false
      }
    }
    if carry {
      done = true
    }
  }
  cnt
}

///|
/// 集合間的映射個數 |S^T|。
pub fn b9_hom_set(t : Int32, s : Int32) -> Int32 {
  b8_pow_int(s, t)
}

// ───────────────────────── 扭子 ─────────────────────────

///|
/// 階乘。
pub fn b9_fact(n : Int32) -> Int32 {
  let mut r = 1
  for i in 1..<=n {
    r = r * i
  }
  r
}

///|
/// 自由遞移 G-作用的**暴力**計數（僅 |G| ≤ 3 可行）：在 |G| 個點上窮舉全部作用。
pub fn b9_torsor_bruteforce(g : B9Group) -> Int32 {
  let n = g.k
  let cur : Array[Int32] = []
  for _ in 0..<(n * n) {
    cur.push(0)
  }
  let mut acts = 0
  let mut done = false
  while !done {
    let cand : B9GSet = { grp: g, n, act: cur, }
    let mut ok = b9_gset_ok(cand)
    if ok {
      for gi in 1..<n {
        if b9_fix_count(cand, gi) != 0 {
          ok = false
        }
      }
      if ok && b9_orbit_count(cand) != 1 {
        ok = false
      }
    }
    if ok {
      acts = acts + 1
    }
    let mut k = 0
    let mut carry = true
    while carry && k < n * n {
      cur[k] = cur[k] + 1
      if cur[k] >= n {
        cur[k] = 0
        k = k + 1
      } else {
        carry = false
      }
    }
    if carry {
      done = true
    }
  }
  acts
}

///|
/// 自由遞移 G-作用的計數（結構性）：任一自由遞移作用同構於正則作用，
/// 作用個數 = |G|! / |Aut(正則)| = |G|! / |G| = (|G| − 1)!；同構類 = 1。
pub fn b9_torsor_count(g : B9Group) -> Int32 {
  b9_fact(g.k) / g.k
}

///|
/// 扭子的自同構群 = 與正則作用交換的雙射個數（= |G|）。
pub fn b9_torsor_aut(g : B9Group) -> Int32 {
  let reg = b9_gset_reg(g)
  b9_hom_gset(reg, reg)
}

///|
/// 兩份正則作用的餘積（G ⊔ G）。
pub fn b9_gset_regular2(g : B9Group) -> B9GSet {
  let n = 2 * g.k
  let act : Array[Int32] = []
  for a in 0..<g.k {
    for x in 0..<n {
      let base = x % g.k
      act.push(g.mul[a * g.k + base] + x / g.k * g.k)
    }
  }
  { grp: g, n, act, }
}
