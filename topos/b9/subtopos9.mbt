// ───────────────────────── 餘域分類器 Ω ─────────────────────────

///|
/// 篩在 m : W → V 下的拉回。
pub fn b9_pull_sieve(c : B8Cat, m : Int32, sv : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for h in 0..<c.nmor {
    if c.cod[h] == c.dom[m] {
      let mh = c.cmp[m * c.nmor + h]
      if b9_pos_in(sv, mh) >= 0 {
        out.push(h)
      }
    }
  }
  out
}

///|
/// Ω 作為預層：Ω(V) = 篩(V)，限制為拉回。
pub fn b9_omega(s : B9Site) -> B8PS {
  let c = s.cat
  let all : Array[Array[Array[Int32]]] = []
  let sz : Array[Int32] = []
  for v in 0..<c.nob {
    let sv = b9_all_sieves(c, v)
    sz.push(sv.length())
    all.push(sv)
  }
  let mx = if sz.length() == 0 {
    1
  } else {
    let mut m = 1
    for x in sz {
      if x > m {
        m = x
      }
    }
    m
  }
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * mx) {
    res.push(0)
  }
  for m in 0..<c.nmor {
    let v = c.cod[m]
    let w = c.dom[m]
    for j in 0..<sz[v] {
      let pulled = b9_pull_sieve(c, m, all[v][j])
      let mut idx = 0
      for k in 0..<sz[w] {
        if b9_sieve_eq(all[w][k], pulled) {
          idx = k
        }
      }
      res[m * mx + j] = idx
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// 子預層的個數：逐物件選子集，且對限制映射封閉。
pub fn b9_sub_count(f : B8PS) -> Int32 {
  let c = f.cat
  let nob = c.nob
  let masks : Array[Int32] = []
  for v in 0..<nob {
    masks.push(1 << f.sz[v])
  }
  let cur : Array[Int32] = []
  for _ in 0..<nob {
    cur.push(0)
  }
  let mut cnt = 0
  let mut done = false
  while !done {
    let mut ok = true
    for m in 0..<c.nmor {
      let w = c.dom[m]
      let v = c.cod[m]
      for x in 0..<f.sz[v] {
        if ((cur[v] >> x) & 1) == 1 {
          let y = f.res[m * f.mx + x]
          if ((cur[w] >> y) & 1) != 1 {
            ok = false
          }
        }
      }
    }
    if ok {
      cnt = cnt + 1
    }
    let mut k = 0
    let mut carry = true
    while carry && k < nob {
      cur[k] = cur[k] + 1
      if cur[k] >= masks[k] {
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
/// 分類器定理的計數核對：|Sub(F)| 對 |Nat(F, Ω)|。
pub fn b9_classifier_check(s : B9Site, f : B8PS) -> (Int32, Int32) {
  (b9_sub_count(f), b8_nat_count(f, b9_omega(s)))
}

// ───────────────────────── Lawvere–Tierney 拓撲 ─────────────────────────

///|
/// LT 拓撲的候選表示：lt[v][i] = j_V(第 i 個篩) 的編號。
pub(all) struct B9LT {
  site : B9Site
  lt : Array[Array[Int32]]
}

///|
fn b9_sieve_index(all : Array[Array[Int32]], sv : Array[Int32]) -> Int32 {
  for k in 0..<all.length() {
    if b9_sieve_eq(all[k], sv) {
      return k
    }
  }
  -1
}

///|
/// 由 j 的「每個篩的像」資料建構 LT 資料（不做公理檢查）。
pub fn b9_lt_make(s : B9Site, table : Array[Array[Int32]]) -> B9LT {
  { site: s, lt: table, }
}

///|
/// LT 公理：自然性、j(true) = true、冪等、保 ∧。
pub fn b9_lt_ok(l : B9LT) -> (Bool, Bool, Bool, Bool) {
  let s = l.site
  let c = s.cat
  let all : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    all.push(b9_all_sieves(c, v))
  }
  let mut nat = true
  let mut unit = true
  let mut idem = true
  let mut meet = true
  for v in 0..<c.nob {
    let mx = b9_sieve_index(all[v], b9_sieve_max(c, v))
    if l.lt[v][mx] != mx {
      unit = false
    }
    for i in 0..<all[v].length() {
      if l.lt[v][l.lt[v][i]] != l.lt[v][i] {
        idem = false
      }
      for j in 0..<all[v].length() {
        let inter = b9_sieve_inter(all[v][i], all[v][j])
        let pi = b9_sieve_index(all[v], inter)
        let a = l.lt[v][pi]
        let b0 = b9_sieve_index(
          all[v],
          b9_sieve_inter(all[v][l.lt[v][i]], all[v][l.lt[v][j]]),
        )
        if a != b0 {
          meet = false
        }
      }
    }
  }
  for m in 0..<c.nmor {
    let v = c.cod[m]
    let w = c.dom[m]
    for i in 0..<all[v].length() {
      let pulled = b9_pull_sieve(c, m, all[v][i])
      let pidx = b9_sieve_index(all[w], pulled)
      let jp = l.lt[w][pidx]
      let jv = l.lt[v][i]
      let pulled2 = b9_pull_sieve(c, m, all[v][jv])
      let pidx2 = b9_sieve_index(all[w], pulled2)
      if jp != pidx2 {
        nat = false
      }
    }
  }
  (nat, unit, idem, meet)
}

///|
/// 窮舉小站上的全部 LT 拓撲（只適用於極小站）。
pub fn b9_lt_enumerate(s : B9Site) -> Array[B9LT] {
  let c = s.cat
  let all : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    all.push(b9_all_sieves(c, v))
  }
  // 逐物件枚舉函數 j_V：篩 → 篩
  let tables : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let k = all[v].length()
    let funcs : Array[Array[Int32]] = []
    let total = b8_pow_int(k, k)
    for code in 0..<total {
      let f : Array[Int32] = []
      let mut rem = code
      for _ in 0..<k {
        f.push(rem % k)
        rem = rem / k
      }
      funcs.push(f)
    }
    tables.push(funcs)
  }
  // 笛卡爾積
  let out : Array[B9LT] = []
  let idx : Array[Int32] = []
  for _ in 0..<c.nob {
    idx.push(0)
  }
  let mut done = false
  while !done {
    let table : Array[Array[Int32]] = []
    for v in 0..<c.nob {
      table.push(tables[v][idx[v]])
    }
    let cand = b9_lt_make(s, table)
    let (n, u, i2, m2) = b9_lt_ok(cand)
    if n && u && i2 && m2 {
      out.push(cand)
    }
    let mut k = 0
    let mut carry = true
    while carry && k < c.nob {
      idx[k] = idx[k] + 1
      if idx[k] >= tables[k].length() {
        idx[k] = 0
        k = k + 1
      } else {
        carry = false
      }
    }
    if carry {
      done = true
    }
  }
  out
}

///|
/// 由 LT 拓撲 j 誘導的 Grothendieck 拓撲：S 覆蓋 V ⟺ j_V(S) = 極大篩。
pub fn b9_topology_of_lt(l : B9LT) -> B9Groth {
  let s = l.site
  let c = s.cat
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let all = b9_all_sieves(c, v)
    let mx = b9_sieve_index(all, b9_sieve_max(c, v))
    let cov : Array[Array[Int32]] = []
    for i in 0..<all.length() {
      if l.lt[v][i] == mx {
        cov.push(all[i])
      }
    }
    j.push(cov)
  }
  { site: s, j, }
}

///|
/// 由 Grothendieck 拓撲 J 得到其 Lawvere–Tierney 閉包 j：
///     j_V(S) = { m : W → V  :  m*(S) ∈ J(W) }.
/// 這是 J 對應的閉包算子（古典構造），其固定點即 J-閉篩。
pub fn b9_lt_of_groth(g : B9Groth) -> B9LT {
  let s = g.site
  let c = s.cat
  let table : Array[Array[Int32]] = []
  for v in 0..<c.nob {
    let all = b9_all_sieves(c, v)
    let row : Array[Int32] = []
    for i in 0..<all.length() {
      // j_V(S) = { m : W→V : m*(S) ∈ J(W) }，取為篩的態射集
      let clos : Array[Int32] = []
      for m in 0..<c.nmor {
        if c.cod[m] == v {
          let w = c.dom[m]
          let pulled = b9_pull_sieve(c, m, all[i])
          if b9_in_j(g, w, pulled) {
            clos.push(m)
          }
        }
      }
      row.push(b9_sieve_index(all, clos))
    }
    table.push(row)
  }
  { site: s, lt: table, }
}

///|
/// 由 J 得到的分類器 Ω_j(V) = { S : j_V(S) = S }（J-閉篩）。
pub fn b9_omega_j(g : B9Groth) -> B8PS {
  let s = g.site
  let c = s.cat
  let l = b9_lt_of_groth(g)
  let all : Array[Array[Array[Int32]]] = []
  let sz : Array[Int32] = []
  for v in 0..<c.nob {
    let sv = b9_all_sieves(c, v)
    let cl : Array[Int32] = []
    for i in 0..<sv.length() {
      if l.lt[v][i] == i {
        cl.push(i)
      }
    }
    sz.push(cl.length())
    let arr : Array[Array[Int32]] = []
    for i in cl {
      arr.push(sv[i])
    }
    all.push(arr)
  }
  build_omega_from(s, all, sz)
}

///|
/// Sh_J 中的子對象個數：F 的預層子對象中本身也是 J-層者。
pub fn b9_sub_count_sh(g : B9Groth, f : B8PS) -> Int32 {
  let c = f.cat
  let nob = c.nob
  let masks : Array[Int32] = []
  for v in 0..<nob {
    masks.push(1 << f.sz[v])
  }
  let cur : Array[Int32] = []
  for _ in 0..<nob {
    cur.push(0)
  }
  let mut cnt = 0
  let mut done = false
  while !done {
    let mut ok = true
    for m in 0..<c.nmor {
      let w = c.dom[m]
      let v = c.cod[m]
      for x in 0..<f.sz[v] {
        if ((cur[v] >> x) & 1) == 1 {
          let y = f.res[m * f.mx + x]
          if ((cur[w] >> y) & 1) != 1 {
            ok = false
          }
        }
      }
    }
    if ok {
      // 檢查子預層本身是層
      let sz : Array[Int32] = []
      let res : Array[Int32] = []
      for v in 0..<nob {
        sz.push(f.sz[v])
      }
      for _ in 0..<(c.nmor * f.mx) {
        res.push(0)
      }
      // 建構子預層：把不在子集中的元素折到 0（用於層檢定的「代表」）
      let sub : Array[Array[Int32]] = []
      for v in 0..<nob {
        let e : Array[Int32] = []
        for x in 0..<f.sz[v] {
          if ((cur[v] >> x) & 1) == 1 {
            e.push(x)
          }
        }
        sub.push(e)
      }
      if b9_sub_is_sheaf(g, f, sub) {
        cnt = cnt + 1
      }
      let _ = sz
      let _ = res
    }
    let mut k = 0
    let mut carry = true
    while carry && k < nob {
      cur[k] = cur[k] + 1
      if cur[k] >= masks[k] {
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
/// 判定逐物件的子集族（子預層）是否滿足 J 的層條件。
fn b9_sub_is_sheaf(g : B9Groth, f : B8PS, sub : Array[Array[Int32]]) -> Bool {
  let c = f.cat
  for v in 0..<c.nob {
    for sv in g.j[v] {
      // 相容族（值域限於子預層）
      let fams = b9_matching(f, v, sv)
      let good : Array[Array[Int32]] = []
      for fam in fams {
        let mut inside = true
        for i in 0..<sv.length() {
          let d = c.dom[sv[i]]
          let mut hit = false
          for e in sub[d] {
            if e == fam[i] {
              hit = true
            }
          }
          if !hit {
            inside = false
          }
        }
        if inside {
          good.push(fam)
        }
      }
      // 子預層的截面數
      let mut nsub = 0
      let secs : Array[Int32] = []
      for x in 0..<f.sz[v] {
        let mut hit = false
        for e in sub[v] {
          if e == x {
            hit = true
          }
        }
        if hit {
          nsub = nsub + 1
          secs.push(x)
        }
      }
      if good.length() != nsub {
        return false
      }
      // 融合須落在子預層內
      for x in secs {
        let fam : Array[Int32] = []
        for m in sv {
          fam.push(f.res[m * f.mx + x])
        }
        let mut hit = false
        for gg in good {
          if b_sh_arr_eq(gg, fam) {
            hit = true
          }
        }
        if !hit {
          return false
        }
      }
    }
  }
  true
}

///|
/// 開子拓撲斯 Sh(U) ⊂ Sh(X)：S 覆蓋 V ⟺ S 在 V∩U 上覆蓋（聯集 ⊇ V∩U），
/// 等價於層在 V 上的限制由 V∩U 決定。
pub fn b9_open_topology(s : B9Site, u : Int32) -> B9Groth {
  let c = s.cat
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let cov : Array[Array[Int32]] = []
    for sv in b9_all_sieves(c, v) {
      let acc = b9_union_dom(s, sv)
      let mut ok = true
      for p in 0..<s.top.npt {
        let op = s.top.opens[s.opens[v]]
        let uo = s.top.opens[s.opens[u]]
        if op[p] && uo[p] && !acc[p] {
          ok = false
        }
      }
      if ok {
        cov.push(sv)
      }
    }
    j.push(cov)
  }
  { site: s, j, }
}

///|
/// 閉子拓撲斯 Sh(X∖U) ⊂ Sh(X)：S 覆蓋 V ⟺ S 在 V∖U 上覆蓋。
pub fn b9_closed_topology(s : B9Site, u : Int32) -> B9Groth {
  let c = s.cat
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let cov : Array[Array[Int32]] = []
    for sv in b9_all_sieves(c, v) {
      let acc = b9_union_dom(s, sv)
      let mut ok = true
      for p in 0..<s.top.npt {
        let op = s.top.opens[s.opens[v]]
        let uo = s.top.opens[s.opens[u]]
        if op[p] && !uo[p] && !acc[p] {
          ok = false
        }
      }
      if ok {
        cov.push(sv)
      }
    }
    j.push(cov)
  }
  { site: s, j, }
}

///|
/// 篩中各態射的定義域之聯集（點位元表）。
pub fn b9_union_dom(s : B9Site, sv : Array[Int32]) -> Array[Bool] {
  let acc : Array[Bool] = []
  for _ in 0..<s.top.npt {
    acc.push(false)
  }
  for m in sv {
    let u = s.top.opens[s.opens[s.cat.dom[m]]]
    for p in 0..<s.top.npt {
      if u[p] {
        acc[p] = true
      }
    }
  }
  acc
}

///|
/// 稠密（¬¬）拓撲：S 覆蓋 V ⟺ 每個非空 W ⊆ V 都有非空 W′ ⊆ W 落在 S 中。
pub fn b9_dense_topology(s : B9Site) -> B9Groth {
  let c = s.cat
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let cov : Array[Array[Int32]] = []
    for sv in b9_all_sieves(c, v) {
      let mut ok = true
      for w in 0..<c.nob {
        if b9_site_inter(s, w, v) == w {
          let mut hit = false
          for w2 in 0..<c.nob {
            if b9_site_inter(s, w2, w) == w2 {
              let m = b9_site_incl(s, w2, v)
              if b9_pos_in(sv, m) >= 0 {
                hit = true
              }
            }
          }
          if !hit {
            ok = false
          }
        }
      }
      if ok {
        cov.push(sv)
      }
    }
    j.push(cov)
  }
  { site: s, j, }
}

///|
/// 拓撲包含：J ⊆ J′（J′ 更細 ⟹ Sh_{J′} ⊂ Sh_J）。
pub fn b9_groth_le(g : B9Groth, h : B9Groth) -> Bool {
  let c = g.site.cat
  for v in 0..<c.nob {
    for sv in g.j[v] {
      if !b9_in_j(h, v, sv) {
        return false
      }
    }
  }
  true
}

///|
/// 由「每物件的閉篩族」與大小表建構 Ω_j 預層。
fn build_omega_from(
  s : B9Site,
  all : Array[Array[Array[Int32]]],
  sz2 : Array[Int32],
) -> B8PS {
  let c = s.cat
  let mx = if sz2.length() == 0 {
    1
  } else {
    let mut m = 1
    for x in sz2 {
      if x > m {
        m = x
      }
    }
    m
  }
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * mx) {
    res.push(0)
  }
  for m in 0..<c.nmor {
    let v = c.cod[m]
    let w = c.dom[m]
    for j in 0..<all[v].length() {
      let pulled = b9_pull_sieve(c, m, all[v][j])
      let mut idx = 0
      for k in 0..<all[w].length() {
        if b9_sieve_eq(all[w][k], pulled) {
          idx = k
        }
      }
      res[m * mx + j] = idx
    }
  }
  b8_ps_make(c, sz2, res)
}
