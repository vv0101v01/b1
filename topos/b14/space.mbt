///|
/// space.mbt — 批次十四工具箱 B：有限拓撲空間、偏序、格、Čech 複形。
///
/// 表示法約定：
///   * 有限空間的點編號為 0..n−1，子集用 Int32 位元遮罩表示（n ≤ 20）。
///   * 開集族以「所有開集的遮罩清單」給出，含 ∅ 與全集，遞增排序。
///   * 偏序以 n×n 的 0/1 矩陣 `le` 給出（含自反、已遞移）。
///   * 層以「每個開集上的自由 F₂-向量空間 + 限制映射」給出；本檔提供兩個具體層：
///     函數層（截面 = 開集上的函數）與常數層（截面 = 連通分支上的函數）。
///     Čech 複形因此是真實矩陣，其同調維數以 rank–nullity 精確計算。
///
/// 註：MoonBit 中 `&`、`|`、`^` 與比較運算子的優先序屬「歧義」級，
/// 本套件一律透過 helper（`b14_has`／`b14_subset`／`b14_disjoint`）存取位元，
/// 以免依賴優先序。

///|
/// 全集遮罩。
pub fn b14_full(n : Int32) -> Int32 {
  (1 << n) - 1
}

///|
/// 第 i 位是否為 1。
pub fn b14_has(m : Int32, i : Int32) -> Bool {
  ((m >> i) & 1) == 1
}

///|
/// a ⊆ b。
pub fn b14_subset(a : Int32, b : Int32) -> Bool {
  (a & b) == a
}

///|
/// a ∩ b = ∅。
pub fn b14_disjoint(a : Int32, b : Int32) -> Bool {
  (a & b) == 0
}

///|
/// 位元個數。
pub fn b14_popcount(m : Int32) -> Int32 {
  let mut c = 0
  let mut x = m
  while x != 0 {
    c = c + (x & 1)
    x = x >> 1
  }
  c
}

///|
/// 遮罩中的點清單（遞增）。
pub fn b14_bits(m : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut i = 0
  let mut x = m
  while x != 0 {
    if (x & 1) == 1 {
      out.push(i)
    }
    x = x >> 1
    i = i + 1
  }
  out
}

///|
/// 有限拓撲空間。
pub(all) struct B14Top {
  n : Int32
  opens : Array[Int32]
}

///|
/// 以開集清單建構（去重、遞增排序）。
pub fn b14_top(n : Int32, raw : Array[Int32]) -> B14Top {
  let out : Array[Int32] = []
  for m in raw {
    let mut seen = false
    for x in out {
      if x == m {
        seen = true
      }
    }
    if !seen {
      out.push(m)
    }
  }
  let s : Array[Int32] = []
  for m in out {
    let t : Array[Int32] = []
    let mut placed = false
    for x in s {
      if !placed && m < x {
        t.push(m)
        placed = true
      }
      t.push(x)
    }
    if !placed {
      t.push(m)
    }
    s.clear()
    for x in t {
      s.push(x)
    }
  }
  { n, opens: s, }
}

///|
/// 以「基」生成拓撲：對 ∩、∪ 取閉包至不動點。
pub fn b14_top_basis(n : Int32, basis : Array[Int32]) -> B14Top {
  let cur : Array[Int32] = []
  cur.push(0)
  cur.push(b14_full(n))
  for m in basis {
    cur.push(m)
  }
  let mut changed = true
  while changed {
    changed = false
    let len = cur.length()
    for i in 0..<len {
      for j in 0..<len {
        let u = cur[i] | cur[j]
        let v = cur[i] & cur[j]
        let mut hu = false
        let mut hv = false
        for x in cur {
          if x == u {
            hu = true
          }
          if x == v {
            hv = true
          }
        }
        if !hu {
          cur.push(u)
          changed = true
        }
        if !hv {
          cur.push(v)
          changed = true
        }
      }
    }
  }
  b14_top(n, cur)
}

///|
/// 拓撲公理檢定：(含 ∅、含全集、對 ∪ 封閉、對 ∩ 封閉) 與違反次數。
pub fn b14_top_ok(t : B14Top) -> (Bool, Int32) {
  let mut bad = 0
  let mut has0 = false
  let mut hasf = false
  for m in t.opens {
    if m == 0 {
      has0 = true
    }
    if m == b14_full(t.n) {
      hasf = true
    }
  }
  if !has0 || !hasf {
    bad = bad + 1
  }
  for a in t.opens {
    for b in t.opens {
      let u = a | b
      let v = a & b
      let mut hu = false
      let mut hv = false
      for x in t.opens {
        if x == u {
          hu = true
        }
        if x == v {
          hv = true
        }
      }
      if !hu {
        bad = bad + 1
      }
      if !hv {
        bad = bad + 1
      }
    }
  }
  (bad == 0, bad)
}

///|
/// 是否為開集。
pub fn b14_is_open(t : B14Top, m : Int32) -> Bool {
  let mut r = false
  for x in t.opens {
    if x == m {
      r = true
    }
  }
  r
}

///|
/// 閉包：包含 s 的最小閉集。
pub fn b14_closure(t : B14Top, s : Int32) -> Int32 {
  let mut acc = b14_full(t.n)
  for o in t.opens {
    let c = b14_full(t.n) ^ o
    if b14_subset(s, c) {
      acc = acc & c
    }
  }
  acc
}

///|
/// T0 檢定。
pub fn b14_t0(t : B14Top) -> Bool {
  let mut ok = true
  for x in 0..<t.n {
    for y in 0..<t.n {
      if x != y {
        let mut sep = false
        for o in t.opens {
          if b14_has(o, x) != b14_has(o, y) {
            sep = true
          }
        }
        if !sep {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 閉集清單。
pub fn b14_closed_sets(t : B14Top) -> Array[Int32] {
  let out : Array[Int32] = []
  for o in t.opens {
    out.push(b14_full(t.n) ^ o)
  }
  out
}

///|
/// 不可約閉集清單：非空，且 C ⊆ A∪B（A,B 閉）⇒ C ⊆ A 或 C ⊆ B。
pub fn b14_irreducible_closed(t : B14Top) -> Array[Int32] {
  let cl = b14_closed_sets(t)
  let out : Array[Int32] = []
  for c in cl {
    if c != 0 {
      let mut irr = true
      for a in cl {
        for b in cl {
          if b14_subset(c, a | b) {
            if !b14_subset(c, a) && !b14_subset(c, b) {
              irr = false
            }
          }
        }
      }
      if irr {
        out.push(c)
      }
    }
  }
  out
}

///|
/// 清醒性：(sober, 反例數)。
pub fn b14_sober(t : B14Top) -> (Bool, Int32) {
  let irr = b14_irreducible_closed(t)
  let mut bad = 0
  for c in irr {
    let mut found = false
    for x in 0..<t.n {
      if b14_closure(t, 1 << x) == c {
        found = true
      }
    }
    if !found {
      bad = bad + 1
    }
  }
  (bad == 0, bad)
}

///|
/// 子空間 U 上的克利開集。
pub fn b14_clopens(t : B14Top, u : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut s = 0
  let lim = b14_full(t.n)
  while s <= lim {
    if b14_subset(s, u) {
      let comp = u ^ s
      let mut so = false
      for o in t.opens {
        if (o & u) == s {
          so = true
        }
      }
      let mut co = false
      for o in t.opens {
        if (o & u) == comp {
          co = true
        }
      }
      if so && co {
        out.push(s)
      }
    }
    s = s + 1
  }
  out
}

///|
/// 子空間 U 的連通分支（克利開代數的原子）。
pub fn b14_components(t : B14Top, u : Int32) -> Array[Int32] {
  let cl = b14_clopens(t, u)
  let out : Array[Int32] = []
  for s in cl {
    if s != 0 {
      let mut atom = true
      for r in cl {
        if r != 0 && r != s && b14_subset(r, s) {
          atom = false
        }
      }
      if atom {
        out.push(s)
      }
    }
  }
  out
}

///|
/// 函數層 F(U) = F₂^{U} 的維數。
pub fn b14_fun_dim(u : Int32) -> Int32 {
  b14_popcount(u)
}

///|
/// 常數層 F(U) = F₂^{π₀(U)} 的維數。
pub fn b14_const_dim(t : B14Top, u : Int32) -> Int32 {
  b14_components(t, u).length()
}

///|
/// 限制映射 res: F(v) → F(u)（u ⊆ v）：dim F(u) 列 × dim F(v) 行。
/// kind = 0：函數層；kind = 1：常數層。
pub fn b14_res_matrix(
  t : B14Top,
  u : Int32,
  v : Int32,
  kind : Int32,
) -> Array[Array[Int32]] {
  if kind == 0 {
    let pu = b14_bits(u)
    let pv = b14_bits(v)
    let m = b14_f2_zero(pu.length(), pv.length())
    for i in 0..<pu.length() {
      for j in 0..<pv.length() {
        if pu[i] == pv[j] {
          m[i][j] = 1
        }
      }
    }
    m
  } else {
    let cu = b14_components(t, u)
    let cv = b14_components(t, v)
    let m = b14_f2_zero(cu.length(), cv.length())
    for i in 0..<cu.length() {
      for j in 0..<cv.length() {
        if b14_subset(cu[i], cv[j]) {
          m[i][j] = 1
        }
      }
    }
    m
  }
}

///|
/// 族的交集（在空間的點遮罩上）。
pub fn b14_fam_inter(fam : Array[Int32], mask : Int32) -> Int32 {
  let mut acc = 0
  let mut first = true
  for j in 0..<fam.length() {
    if b14_has(mask, j) {
      if first {
        acc = fam[j]
        first = false
      } else {
        acc = acc & fam[j]
      }
    }
  }
  acc
}

///|
/// Čech 複形：C^q = ⊕_{|K|=q+1} F(∩K)，微分取限制映射之交替和（特徵 2 ⇒ 純和）。
pub fn b14_cech(t : B14Top, fam : Array[Int32], kind : Int32) -> B14Cx {
  let k = fam.length()
  let nsub = 1 << k
  let sd : Array[Int32] = []
  for m in 0..<nsub {
    let inter = b14_fam_inter(fam, m)
    let d = if kind == 0 { b14_fun_dim(inter) } else { b14_const_dim(t, inter) }
    sd.push(if m == 0 { 0 } else { d })
  }
  let dims : Array[Int32] = []
  let offset = b14_f2_zero(nsub, 1)
  for q in 0..<k {
    let mut off = 0
    for m in 0..<nsub {
      if b14_popcount(m) == q + 1 {
        offset[m][0] = off
        off = off + sd[m]
      }
    }
    dims.push(off)
  }
  let diffs : Array[Array[Array[Int32]]] = []
  for q in 0..<(k - 1) {
    let mat = b14_f2_zero(dims[q + 1], dims[q])
    for big in 0..<nsub {
      if b14_popcount(big) == q + 2 {
        let inner = b14_fam_inter(fam, big)
        for j in 0..<k {
          if b14_has(big, j) {
            let small = big ^ (1 << j)
            let res = b14_res_matrix(t, inner, b14_fam_inter(fam, small), kind)
            let nc = if res.length() == 0 { 0 } else { res[0].length() }
            for r in 0..<res.length() {
              for c in 0..<nc {
                let rr = offset[big][0] + r
                let cc = offset[small][0] + c
                mat[rr][cc] = (mat[rr][cc] + res[r][c]) % 2
              }
            }
          }
        }
      }
    }
    diffs.push(mat)
  }
  b14_cx(dims, diffs)
}

///|
/// 有限格的表示（元素以 0..n−1 編號）。
pub(all) struct B14Lat {
  n : Int32
  meet : Array[Array[Int32]]
  join : Array[Array[Int32]]
  top : Int32
  bot : Int32
}

///|
/// 由有限拓撲空間的開集族建構格（元素 = 開集）。
pub fn b14_lat_of_top(t : B14Top) -> B14Lat {
  let n = t.opens.length()
  let meet = b14_f2_zero(n, n)
  let join = b14_f2_zero(n, n)
  for i in 0..<n {
    for j in 0..<n {
      let mi = t.opens[i] & t.opens[j]
      let jo = t.opens[i] | t.opens[j]
      for k in 0..<n {
        if t.opens[k] == mi {
          meet[i][j] = k
        }
        if t.opens[k] == jo {
          join[i][j] = k
        }
      }
    }
  }
  let mut top = 0
  let mut bot = 0
  for i in 0..<n {
    if t.opens[i] == b14_full(t.n) {
      top = i
    }
    if t.opens[i] == 0 {
      bot = i
    }
  }
  { n, meet, join, top, bot, }
}

///|
/// 分配律檢定。
pub fn b14_lat_distributive(l : B14Lat) -> Bool {
  let mut ok = true
  for a in 0..<l.n {
    for b in 0..<l.n {
      for c in 0..<l.n {
        if l.meet[a][l.join[b][c]] != l.join[l.meet[a][b]][l.meet[a][c]] {
          ok = false
        }
        if l.join[a][l.meet[b][c]] != l.meet[l.join[a][b]][l.join[a][c]] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 格的完全素濾子（Hochster／Priestley 對偶的點）：含 top、上閉、meet 封閉、join 素。
pub fn b14_cprime_filters(l : B14Lat) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let nsub = 1 << l.n
  for m in 0..<nsub {
    if b14_has(m, l.top) && !b14_has(m, l.bot) {
      let mem : Array[Bool] = []
      for i in 0..<l.n {
        mem.push(b14_has(m, i))
      }
      let mut ok = true
      for a in 0..<l.n {
        for b in 0..<l.n {
          if mem[a] && !mem[l.join[a][b]] {
            ok = false
          }
          if mem[a] && mem[b] && !mem[l.meet[a][b]] {
            ok = false
          }
          if mem[l.join[a][b]] && !mem[a] && !mem[b] {
            ok = false
          }
        }
      }
      if ok {
        let f : Array[Int32] = []
        for i in 0..<l.n {
          if mem[i] {
            f.push(i)
          }
        }
        out.push(f)
      }
    }
  }
  out
}

///|
/// 偏序：由關係對生成遞移自反閉包，回傳 n×n 0/1 矩陣。
pub fn b14_poset(
  n : Int32,
  rels : Array[(Int32, Int32)],
) -> Array[Array[Int32]] {
  let le = b14_f2_zero(n, n)
  for i in 0..<n {
    le[i][i] = 1
  }
  for r in rels {
    le[r.0][r.1] = 1
  }
  let mut changed = true
  while changed {
    changed = false
    for i in 0..<n {
      for j in 0..<n {
        for k in 0..<n {
          if le[i][j] == 1 && le[j][k] == 1 && le[i][k] == 0 {
            le[i][k] = 1
            changed = true
          }
        }
      }
    }
  }
  le
}

///|
/// 亞歷山大拓撲：開集 = 上集。
pub fn b14_alex_opens(n : Int32, le : Array[Array[Int32]]) -> Array[Int32] {
  let out : Array[Int32] = []
  let nmax = 1 << n
  for m in 0..<nmax {
    let mut up = true
    for i in 0..<n {
      if b14_has(m, i) {
        for j in 0..<n {
          if le[i][j] == 1 && !b14_has(m, j) {
            up = false
          }
        }
      }
    }
    if up {
      out.push(m)
    }
  }
  out
}

///|
/// 有向子集判定。
pub fn b14_directed(n : Int32, le : Array[Array[Int32]], d : Int32) -> Bool {
  if d == 0 {
    return false
  }
  for i in 0..<n {
    if b14_has(d, i) {
      for j in 0..<n {
        if b14_has(d, j) {
          let mut has = false
          for k in 0..<n {
            if b14_has(d, k) && le[i][k] == 1 && le[j][k] == 1 {
              has = true
            }
          }
          if !has {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 子集 d 的最小上界（不存在回傳 −1）。
pub fn b14_lub(n : Int32, le : Array[Array[Int32]], d : Int32) -> Int32 {
  let mut cand = -1
  for x in 0..<n {
    let mut upper = true
    for i in 0..<n {
      if b14_has(d, i) && le[i][x] == 0 {
        upper = false
      }
    }
    if upper {
      if cand == -1 {
        cand = x
      } else if le[x][cand] == 1 && x != cand {
        cand = x
      }
    }
  }
  cand
}

///|
/// 斯科特開集。
pub fn b14_scott_opens(n : Int32, le : Array[Array[Int32]]) -> Array[Int32] {
  let alex = b14_alex_opens(n, le)
  let out : Array[Int32] = []
  for u in alex {
    let mut ok = true
    for d in 1..<(1 << n) {
      if b14_directed(n, le, d) {
        let l = b14_lub(n, le, d)
        if l >= 0 && b14_has(u, l) && b14_disjoint(d, u) {
          ok = false
        }
      }
    }
    if ok {
      out.push(u)
    }
  }
  out
}

///|
/// 拓撲的「∪-生成數」：最少幾個開集，使每個開集都是它們的聯集（小空間窮舉）。
pub fn b14_gen_number(t : B14Top) -> Int32 {
  let m = t.opens.length()
  for k in 1..<=3 {
    if k > m {
      break
    }
    let idx : Array[Int32] = []
    for i in 0..<k {
      idx.push(i)
    }
    let mut done = false
    while !done {
      let cover : Array[Int32] = []
      let sub = 1 << k
      for s in 0..<sub {
        let mut acc = 0
        for j in 0..<k {
          if b14_has(s, j) {
            acc = acc | t.opens[idx[j]]
          }
        }
        cover.push(acc)
      }
      let mut all = true
      for o in t.opens {
        let mut has = false
        for c in cover {
          if c == o {
            has = true
          }
        }
        if !has {
          all = false
        }
      }
      if all {
        return k
      }
      let mut i = k - 1
      while i >= 0 && idx[i] == m - k + i {
        i = i - 1
      }
      if i < 0 {
        done = true
      } else {
        idx[i] = idx[i] + 1
        for j in (i + 1)..<k {
          idx[j] = idx[j - 1] + 1
        }
      }
    }
  }
  4
}
