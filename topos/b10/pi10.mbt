///|
/// pi10.mbt — 批次十·模組 3：局部常數層、拓撲斯基本群、射影有限基本群、局部群oid、等變層
///
/// 局部常數層 F：每個物件都有一個覆蓋，使 F 在覆蓋成員上為常數。
/// 拓撲斯基本群 π₁(E) = 纖維函子 ω : LC(E) → Set 的自同構群；
/// 對 Galois 拓撲斯 Set[G]：LC = 全部 G-集合，ω = 遺忘函子，Aut(ω) = G。
/// 射影有限基本群：以「指數 n 子群 = 連通 n 度覆蓋」的 Galois 對應計算。

// ───────────────────────── 局部常數層 ─────────────────────────

///|
/// F 在子物件 w 上是否為常數：所有 z ≤ w 皆有 |F(z)| = |F(w)|，且限制映射單射。
pub fn b10_const_on(s : B9Site, f : B8PS, w : Int32) -> Bool {
  for z in 0..<s.cat.nob {
    if z != w && b9_site_incl(s, z, w) >= 0 {
      if f.sz[z] != f.sz[w] {
        return false
      }
      // 找 z → w 的態射，檢查限制映射單射
      let mut inj = false
      for m in 0..<s.cat.nmor {
        if s.cat.dom[m] == z && s.cat.cod[m] == w {
          let seen : Array[Int32] = []
          for _ in 0..<f.sz[w] {
            seen.push(0)
          }
          let mut ok = true
          for x in 0..<f.sz[w] {
            let y = f.res[m * f.mx + x]
            seen[y] = seen[y] + 1
            if seen[y] > 1 {
              ok = false
            }
          }
          if ok {
            inj = true
          }
        }
      }
      if !inj {
        return false
      }
    }
  }
  true
}

///|
/// F 在 v 上局部常數：存在覆蓋 v 的族，其成員皆為 const_on。
pub fn b10_lc_at(s : B9Site, f : B8PS, v : Int32) -> Bool {
  let base = s.top.opens[s.opens[v]]
  let acc : Array[Bool] = []
  for _ in 0..<s.top.npt {
    acc.push(false)
  }
  let mut any = false
  for w in 0..<s.cat.nob {
    if b9_site_incl(s, w, v) >= 0 && b10_const_on(s, f, w) {
      let ow = s.top.opens[s.opens[w]]
      for p in 0..<s.top.npt {
        if ow[p] {
          acc[p] = true
        }
      }
      any = true
    }
  }
  if !any {
    return false
  }
  for p in 0..<s.top.npt {
    if base[p] && !acc[p] {
      return false
    }
  }
  true
}

///|
/// F 是局部常數層。
pub fn b10_is_locally_constant(s : B9Site, f : B8PS) -> Bool {
  for v in 0..<s.cat.nob {
    if !b10_lc_at(s, f, v) {
      return false
    }
  }
  true
}

///|
/// 局部常數見證計數：滿足「局部常數」的物件數。
pub fn b10_lc_witness(s : B9Site, f : B8PS) -> Int32 {
  let mut c = 0
  for v in 0..<s.cat.nob {
    if b10_lc_at(s, f, v) {
      c = c + 1
    }
  }
  c
}

// ───────────────────────── 基本群 ─────────────────────────

///|
/// 纖維函子的自同構群大小（對 Set[G]：= |G|）。
pub fn b10_fiber_aut(g : B9Group) -> Int32 {
  b9_torsor_aut(g)
}

///|
/// 指數 n 子群個數（= 連通 n 度覆蓋個數）。
pub fn b10_subgroup_index_count(g : B9Group, n : Int32) -> Int32 {
  if g.k % n != 0 {
    return 0
  }
  let want = g.k / n
  let mut cnt = 0
  let total = b8_pow_int(2, g.k)
  for mask in 0..<total {
    // 必須含單位元 0
    if ((mask >> 0) & 1) == 1 {
      let mut size = 0
      for i in 0..<g.k {
        if ((mask >> i) & 1) == 1 {
          size = size + 1
        }
      }
      if size == want {
        // 乘法封閉 + 逆元封閉
        let mut ok = true
        for a in 0..<g.k {
          for b in 0..<g.k {
            if ((mask >> a) & 1) == 1 && ((mask >> b) & 1) == 1 {
              if ((mask >> g.mul[a * g.k + b]) & 1) != 1 {
                ok = false
              }
            }
          }
        }
        if ok && want > 0 {
          // 逆元封閉由有限性自動（乘法封閉的有限子么半群即子群）
          cnt = cnt + 1
        }
      }
    }
  }
  cnt
}

///|
/// 指數 n 子群的共軛類數（= 同構類意義下的連通 n 度覆蓋數）。
pub fn b10_conj_class_count(g : B9Group, n : Int32) -> Int32 {
  if g.k % n != 0 {
    return 0
  }
  let want = g.k / n
  let total = b8_pow_int(2, g.k)
  let subs : Array[Int32] = []
  for mask in 0..<total {
    if ((mask >> 0) & 1) == 1 {
      let mut size = 0
      for i in 0..<g.k {
        if ((mask >> i) & 1) == 1 {
          size = size + 1
        }
      }
      if size == want {
        let mut ok = true
        for a in 0..<g.k {
          for b in 0..<g.k {
            if ((mask >> a) & 1) == 1 && ((mask >> b) & 1) == 1 {
              if ((mask >> g.mul[a * g.k + b]) & 1) != 1 {
                ok = false
              }
            }
          }
        }
        if ok {
          subs.push(mask)
        }
      }
    }
  }
  // 共軛作用 h·a = h a h⁻¹
  let seen : Array[Bool] = []
  for _ in 0..<subs.length() {
    seen.push(false)
  }
  let mut classes = 0
  for i in 0..<subs.length() {
    if !seen[i] {
      classes = classes + 1
      for j in 0..<subs.length() {
        // 檢查 subs[j] 是否為 subs[i] 的共軛
        for h in 0..<g.k {
          let mut hinv = 0
          for x in 0..<g.k {
            if g.mul[h * g.k + x] == 0 {
              hinv = x
            }
          }
          let mut same = true
          for a in 0..<g.k {
            let conj = g.mul[g.mul[h * g.k + a] * g.k + hinv]
            let in_i = ((subs[i] >> a) & 1) == 1
            let in_j = ((subs[j] >> conj) & 1) == 1
            if in_i != in_j {
              same = false
            }
          }
          if same {
            seen[j] = true
          }
        }
      }
    }
  }
  classes
}

///|
/// 子群總數（= 連通覆蓋的總數，含各度數）。
pub fn b10_subgroup_total(g : B9Group) -> Int32 {
  let mut t = 0
  for n in 1..<=g.k {
    t = t + b10_subgroup_index_count(g, n)
  }
  t
}

// ───────────────────────── 局部群oid 與等變層 ─────────────────────────

///|
/// 作用群oid 的規模：(物件數, 態射數) = (|X|, |G|·|X|)。
pub fn b10_groupoid_sizes(s : B9GSet) -> (Int32, Int32) {
  (s.n, s.grp.k * s.n)
}

///|
/// 作用群oid 全可逆：(g, x) : x → g·x 的逆為 (g⁻¹, g·x)。
pub fn b10_groupoid_invertible(s : B9GSet) -> Bool {
  let g = s.grp
  for a in 0..<g.k {
    let mut inv = -1
    for h in 0..<g.k {
      if g.mul[a * g.k + h] == 0 {
        inv = h
      }
    }
    if inv < 0 {
      return false
    }
    for x in 0..<s.n {
      let y = s.act[a * s.n + x]
      if s.act[inv * s.n + y] != x {
        return false
      }
    }
  }
  true
}

///|
/// 等變層分類（自由作用 X = G）：等變層 ↔ 集合，故大小 ≤ n·|G| 的同構類有 n+1 個。
pub fn b10_equivariant_classes(g : B9Group, n : Int32) -> Int32 {
  // 對每個 k ≤ n，G^k 是唯一的（自由作用上等變層的）同構類；
  // 逐個核對 G^k 的每個軌道皆正則。
  let mut ok = true
  for k in 0..<=n {
    if !b10_regular_power_ok(g, k) {
      ok = false
    }
  }
  if ok {
    n + 1
  } else {
    -1
  }
}

///|
/// 驗證 G^k 確實是「每個軌道都正則」的等變層：軌道數 k，穩定子皆 1。
pub fn b10_regular_power_ok(g : B9Group, k : Int32) -> Bool {
  if k == 0 {
    // 空 G-集合：0 個軌道、無穩定子需檢
    return b9_orbit_count({ grp: g, n: 0, act: [], }) == 0
  }
  let mut cur = b9_gset_reg(g)
  for _ in 1..<k {
    cur = b10_coprod_gset(cur, b9_gset_reg(g))
  }
  if b9_orbit_count(cur) != k {
    return false
  }
  for x in 0..<cur.n {
    if b9_stab_size(cur, x) != 1 {
      return false
    }
  }
  true
}

///|
/// 兩個 G-集合的餘積。
pub fn b10_coprod_gset(a : B9GSet, b : B9GSet) -> B9GSet {
  let g = a.grp
  let n = a.n + b.n
  let act : Array[Int32] = []
  for gi in 0..<g.k {
    for x in 0..<n {
      if x < a.n {
        act.push(a.act[gi * a.n + x])
      } else {
        act.push(a.n + b.act[gi * b.n + (x - a.n)])
      }
    }
  }
  { grp: g, n, act, }
}
