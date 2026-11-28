///|
/// shf9.mbt — 批次九·模組 2：層、分離預層、加號構造與層化
///
/// 給定站（空間）上的 Grothendieck 拓撲 J（以「覆蓋篩族」表示），
/// 對預層 F 與覆蓋篩 S（在物件 V 上）定義**相容族**：對每個 m ∈ S 給 x_m ∈ F(dom m)，
/// 且對每個可合成對 (m, g)（cod g = dom m）滿足 F(g)(x_m) = x_{m∘g}。
///
/// 層條件：對每個 V 與每個 S ∈ J(V)，典範映射 F(V) → 相容族集是**雙射**。
/// 加號構造 F⁺：F⁺(V) = colim_{S ∈ J(V)} 相容族(S)，其中不同 S 上的族以「在 S ∩ S′ 上一致」等價
/// （J 對交集封閉 ⟹ S ∩ S′ 仍覆蓋 ⟹ 這是餘濾過系統的餘極限）。
/// 層化：a(F) = F⁺⁺，a ⊣ i（i 為包含）。
///
/// 全部條件化為有限計數：|F(V)| 是否等於相容族個數、雙射是否真的打到每個族。

// ───────────────────────── 拓撲（覆蓋篩族）─────────────────────────

///|
/// 站上的 Grothendieck 拓撲：J[v] = V 上的覆蓋篩清單。
pub(all) struct B9Groth {
  site : B9Site
  j : Array[Array[Array[Int32]]]
}

///|
/// 空間站的開覆蓋拓撲。
pub fn b9_groth_spatial(s : B9Site) -> B9Groth {
  let j : Array[Array[Array[Int32]]] = []
  for v in 0..<s.cat.nob {
    j.push(b9_covering_sieves(s, v))
  }
  { site: s, j, }
}

///|
/// 拓撲公理檢定（在此表示下）：每個 J(v) 含極大篩、對超篩封閉、對交集封閉且交集仍覆蓋。
pub fn b9_groth_ok(g : B9Groth) -> (Bool, Bool, Bool) {
  let c = g.site.cat
  let mut a1 = true
  let mut a2 = true
  let mut a3 = true
  for v in 0..<c.nob {
    let mx = b9_sieve_max(c, v)
    if !b9_sieve_le2(g.j[v], mx) {
      a1 = false
    }
    for s in g.j[v] {
      for q in b9_all_sieves(c, v) {
        if b9_sieve_le(s, q) && !b9_sieve_le2(g.j[v], q) {
          a2 = false
        }
      }
      for r in g.j[v] {
        if !b9_sieve_le2(g.j[v], b9_sieve_inter(s, r)) {
          a3 = false
        }
      }
    }
  }
  (a1, a2, a3)
}

///|
/// 篩是否在 J(v) 中（以集合比較，避免列舉順序差異）。
pub fn b9_in_j(g : B9Groth, v : Int32, sv : Array[Int32]) -> Bool {
  for s in g.j[v] {
    if b9_sieve_eq(s, sv) {
      return true
    }
  }
  false
}

// ───────────────────────── 相容族 ─────────────────────────

///|
fn b9_pos_in(sv : Array[Int32], m : Int32) -> Int32 {
  for i in 0..<sv.length() {
    if sv[i] == m {
      return i
    }
  }
  -1
}

///|
/// 覆蓋篩 S 上的全部相容族（每個族是與 S 平行排列的值陣列）。
pub fn b9_matching(
  f : B8PS,
  _v : Int32,
  sv : Array[Int32],
) -> Array[Array[Int32]] {
  let c = f.cat
  let n = sv.length()
  let out : Array[Array[Int32]] = []
  if n == 0 {
    out.push([])
    return out
  }
  let rad : Array[Int32] = []
  let mut zero = false
  for m in sv {
    let r = f.sz[c.dom[m]]
    rad.push(r)
    if r == 0 {
      zero = true
    }
  }
  if zero {
    return out
  }
  let ti : Array[Int32] = []
  let tg : Array[Int32] = []
  let tp : Array[Int32] = []
  for i in 0..<n {
    for gg in 0..<c.nmor {
      if c.cod[gg] == c.dom[sv[i]] {
        let mg = c.cmp[sv[i] * c.nmor + gg]
        let p = b9_pos_in(sv, mg)
        if p >= 0 {
          ti.push(i)
          tg.push(gg)
          tp.push(p)
        }
      }
    }
  }
  let cur : Array[Int32] = []
  for _ in 0..<n {
    cur.push(0)
  }
  let mut done = false
  while !done {
    let mut ok = true
    for t in 0..<ti.length() {
      if f.res[tg[t] * f.mx + cur[ti[t]]] != cur[tp[t]] {
        ok = false
      }
    }
    if ok {
      let fam : Array[Int32] = []
      for i in 0..<n {
        fam.push(cur[i])
      }
      out.push(fam)
    }
    let mut k = 0
    let mut carry = true
    while carry && k < n {
      cur[k] = cur[k] + 1
      if cur[k] >= rad[k] {
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
  out
}

///|
/// 在 V 與覆蓋篩 S 上的層條件：F(V) → 相容族 是否雙射。
pub fn b9_sheaf_at(f : B8PS, v : Int32, sv : Array[Int32]) -> Bool {
  let c = f.cat
  let fams = b9_matching(f, v, sv)
  if fams.length() != f.sz[v] {
    return false
  }
  let seen : Array[Bool] = []
  for _ in 0..<fams.length() {
    seen.push(false)
  }
  for x in 0..<f.sz[v] {
    let fam : Array[Int32] = []
    for m in sv {
      fam.push(f.res[m * f.mx + x])
    }
    let mut hit = -1
    for i in 0..<fams.length() {
      if b_sh_arr_eq(fams[i], fam) {
        hit = i
      }
    }
    if hit < 0 || seen[hit] {
      return false
    }
    seen[hit] = true
  }
  let _ = c
  true
}

///|
/// 分離預層：F(V) → 相容族 單射（至多一個融合）。
pub fn b9_separated_at(f : B8PS, v : Int32, sv : Array[Int32]) -> Bool {
  let fams = b9_matching(f, v, sv)
  let seen : Array[Bool] = []
  for _ in 0..<fams.length() {
    seen.push(false)
  }
  for x in 0..<f.sz[v] {
    let fam : Array[Int32] = []
    for m in sv {
      fam.push(f.res[m * f.mx + x])
    }
    let mut hit = -1
    for i in 0..<fams.length() {
      if b_sh_arr_eq(fams[i], fam) {
        hit = i
      }
    }
    if hit >= 0 {
      if seen[hit] {
        return false
      }
      seen[hit] = true
    }
  }
  true
}

///|
/// 整個站的層條件。
pub fn b9_is_sheaf(g : B9Groth, f : B8PS) -> Bool {
  for v in 0..<g.site.cat.nob {
    for sv in g.j[v] {
      if !b9_sheaf_at(f, v, sv) {
        return false
      }
    }
  }
  true
}

///|
/// 整個站的分離條件。
pub fn b9_is_separated(g : B9Groth, f : B8PS) -> Bool {
  for v in 0..<g.site.cat.nob {
    for sv in g.j[v] {
      if !b9_separated_at(f, v, sv) {
        return false
      }
    }
  }
  true
}

// ───────────────────────── 加號構造 ─────────────────────────

///|
/// 併查集：路徑壓縮 + 按秩合併（以簡單陣列實現）。
fn b9_uf_find(par : Array[Int32], x : Int32) -> Int32 {
  let mut r = x
  while par[r] != r {
    r = par[r]
  }
  let mut y = x
  while par[y] != r {
    let ny = par[y]
    par[y] = r
    y = ny
  }
  r
}

///|
fn b9_uf_union(par : Array[Int32], a : Int32, b : Int32) -> Unit {
  let ra = b9_uf_find(par, a)
  let rb = b9_uf_find(par, b)
  if ra != rb {
    par[rb] = ra
  }
}

///|
/// 加號構造 F⁺(V) = colim_{S ∈ J(V)} 相容族(S)。
pub fn b9_plus(g : B9Groth, f : B8PS) -> B8PS {
  let c = g.site.cat
  let nob = c.nob
  // 每物件：所有 (篩, 相容族) 對
  let pairs : Array[Array[Array[Int32]]] = []
  let svs : Array[Array[Array[Int32]]] = []
  let par : Array[Array[Int32]] = []
  for v in 0..<nob {
    let ps : Array[Array[Int32]] = []
    let ss : Array[Array[Int32]] = []
    for sv in g.j[v] {
      for fam in b9_matching(f, v, sv) {
        ps.push(fam)
        ss.push(sv)
      }
    }
    let p : Array[Int32] = []
    for i in 0..<ps.length() {
      p.push(i)
    }
    // 在 S ∩ S′ 上一致的對合併
    for i in 0..<ps.length() {
      for k in 0..<ps.length() {
        let inter = b9_sieve_inter(ss[i], ss[k])
        let mut agree = true
        for m in inter {
          let pi = b9_pos_in(ss[i], m)
          let pk = b9_pos_in(ss[k], m)
          if ps[i][pi] != ps[k][pk] {
            agree = false
          }
        }
        if agree {
          b9_uf_union(p, i, k)
        }
      }
    }
    pairs.push(ps)
    svs.push(ss)
    par.push(p)
  }
  // 類編號與代表
  let cls : Array[Array[Int32]] = []
  let rep : Array[Array[Int32]] = []
  let sz : Array[Int32] = []
  for v in 0..<nob {
    let cl : Array[Int32] = []
    let rp : Array[Int32] = []
    for _ in 0..<pairs[v].length() {
      cl.push(-1)
    }
    for i in 0..<pairs[v].length() {
      let r = b9_uf_find(par[v], i)
      if cl[r] < 0 {
        cl[r] = rp.length()
        rp.push(r)
      }
      cl[i] = cl[r]
    }
    cls.push(cl)
    rep.push(rp)
    sz.push(rp.length())
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
  for u in 0..<c.nmor {
    let w = c.dom[u]
    let v = c.cod[u]
    for j in 0..<sz[v] {
      let i = rep[v][j]
      let sv = svs[v][i]
      let fam = pairs[v][i]
      // 拉回篩 u*S = { h : cod h = W, u∘h ∈ S }，拉回族在 h 上的值 = x_{u∘h}
      let ps : Array[Int32] = []
      for h in 0..<c.nmor {
        if c.cod[h] == w {
          if b9_pos_in(sv, c.cmp[u * c.nmor + h]) >= 0 {
            ps.push(h)
          }
        }
      }
      let pfam : Array[Int32] = []
      for h in ps {
        pfam.push(fam[b9_pos_in(sv, c.cmp[u * c.nmor + h])])
      }
      // 在 W 的對集中找對應項
      let mut idx = 0
      for k in 0..<pairs[w].length() {
        if b9_sieve_eq(svs[w][k], ps) && b_sh_arr_eq(pairs[w][k], pfam) {
          idx = cls[w][k]
        }
      }
      res[u * mx + j] = idx
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// 層化 a(F) = F⁺⁺。
pub fn b9_sheafify(g : B9Groth, f : B8PS) -> B8PS {
  b9_plus(g, b9_plus(g, f))
}

///|
/// 加號構造的階段表：回傳 (各階段總基數, 首次穩定步)。
pub fn b9_plus_stages(g : B9Groth, f : B8PS) -> (Array[Int32], Int32) {
  let tot : Array[Int32] = []
  let mut cur = f
  let mut stage = 0
  let mut stab = -1
  for _ in 0..<4 {
    let mut t = 0
    for v in 0..<g.site.cat.nob {
      t = t + cur.sz[v]
    }
    tot.push(t)
    let nxt = b9_plus(g, cur)
    let mut same = true
    for v in 0..<g.site.cat.nob {
      if nxt.sz[v] != cur.sz[v] {
        same = false
      }
    }
    if same && stab < 0 {
      stab = stage
    }
    cur = nxt
    stage = stage + 1
  }
  (tot, stab)
}

///|
/// 逐物件大小是否相等。
pub fn b9_sz_eq(a : B8PS, b : B8PS) -> Bool {
  if a.cat.nob != b.cat.nob {
    return false
  }
  for v in 0..<a.cat.nob {
    if a.sz[v] != b.sz[v] {
      return false
    }
  }
  true
}

///|
/// 層化的冪等性：|a(a(F))| = |a(F)| 逐物件。
pub fn b9_sheafify_idem(g : B9Groth, f : B8PS) -> Bool {
  let a = b9_sheafify(g, f)
  let aa = b9_sheafify(g, a)
  b9_sz_eq(a, aa)
}
