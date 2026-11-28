///|
/// colim.mbt — 批次八·模組 3：餘極限與層化合成在無窮組合中的作用
///
/// (A) 有限餘極限的顯式計算：餘等化子 = 併查集商集；鏈的餘極限 = 極限階段的穩定化。
/// (B) 有限站（site）上的「加號構造」F ↦ F⁺：
///       F⁺(c) = { 覆蓋篩 sieve(c) 上的相容族 }，
///     層化 a = F⁺⁺。可數的事實：a∘a = a（冪等）、a 保餘積、
///     以及加號構造在有限站上的穩定步數（∞-拓撲斯需超限迭代）。
/// (C) 無窮組合：Kőnig 引理的有限截斷、Cantor 集測度的精確有理數計算、
///     有限階段性質的極限提升。

// ───────────────────────── (A) 有限餘極限 ─────────────────────────

///|
/// 併查集根。
fn b8q_root(par : Array[Int32], i : Int32) -> Int32 {
  let mut r = i
  while par[r] != r {
    r = par[r]
  }
  r
}

///|
/// 由生成關係對求 n 元集合的商集：回傳 (類數, 每元素類編號)。
pub fn b8q_quot(
  n : Int32,
  pairs : Array[(Int32, Int32)],
) -> (Int32, Array[Int32]) {
  let par : Array[Int32] = []
  for i in 0..<n {
    par.push(i)
  }
  for (a, b) in pairs {
    let ra = b8q_root(par, a)
    let rb = b8q_root(par, b)
    if ra != rb {
      par[ra] = rb
    }
  }
  let ids : Array[Int32] = []
  for _ in 0..<n {
    ids.push(-1)
  }
  let mut k = 0
  for i in 0..<n {
    let r = b8q_root(par, i)
    let mut found = -1
    for j in 0..<i {
      if b8q_root(par, j) == r {
        found = ids[j]
      }
    }
    if found >= 0 {
      ids[i] = found
    } else {
      ids[i] = k
      k = k + 1
    }
  }
  (k, ids)
}

///|
/// 餘等化子基數：|Y| 模去 f(x) ∼ g(x)。
pub fn b8q_coeq_size(ny : Int32, f : Array[Int32], g : Array[Int32]) -> Int32 {
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<f.length() {
    pairs.push((f[i], g[i]))
  }
  let (k, _) = b8q_quot(ny, pairs)
  k
}

///|
/// 鏈 X₀ → X₁ → … → X_k 的餘極限：回傳 (類數, 穩定指數)。
pub fn b8q_chain_colim(
  sizes : Array[Int32],
  maps : Array[Array[Int32]],
) -> (Int32, Int32) {
  let off : Array[Int32] = []
  let mut total = 0
  for s in sizes {
    off.push(total)
    total = total + s
  }
  let pairs : Array[(Int32, Int32)] = []
  for k in 0..<maps.length() {
    let mp = maps[k]
    for i in 0..<mp.length() {
      pairs.push((off[k] + i, off[k + 1] + mp[i]))
    }
  }
  let (ncls, ids) = b8q_quot(total, pairs)
  let mut stab = sizes.length() - 1
  for stage in 0..<sizes.length() {
    let marks : Array[Bool] = []
    for _ in 0..<ncls {
      marks.push(false)
    }
    let mut cnt = 0
    let end = off[stage] + sizes[stage]
    for j in 0..<end {
      if !marks[ids[j]] {
        marks[ids[j]] = true
        cnt = cnt + 1
      }
    }
    if cnt == ncls {
      stab = stage
      break
    }
  }
  (ncls, stab)
}

// ───────────────────────── (B) 有限站上的加號構造 ─────────────────────────

///|
/// 有限站：位向範疇 + 每個物件的覆蓋篩（態射編號清單，向下封閉且穩定）。
pub(all) struct B8Site {
  cat : B8Cat
  sieve : Array[Array[Int32]]
}

///|
/// 建構站。
pub fn b8_site(cat : B8Cat, sieve : Array[Array[Int32]]) -> B8Site {
  { cat, sieve, }
}

///|
/// 站的良定義：篩由 cod 為該物件的態射組成、向下封閉、且對篩中態射的拉回是滿的。
pub fn b8_site_ok(s : B8Site) -> Bool {
  let c = s.cat
  for cc in 0..<c.nob {
    let sv = s.sieve[cc]
    let inset : Array[Bool] = []
    for _ in 0..<c.nmor {
      inset.push(false)
    }
    for m in sv {
      if c.cod[m] != cc {
        return false
      }
      inset[m] = true
    }
    for m in sv {
      for n in 0..<c.nmor {
        if c.cod[n] == c.dom[m] && !inset[c.cmp[m * c.nmor + n]] {
          return false
        }
      }
    }
    // 穩定性：對篩中每個 n，n 的拉回篩等於整個 sieve(dom n)
    for n in 0..<c.nmor {
      if inset[n] {
        for nu in s.sieve[c.dom[n]] {
          let comp = c.cmp[n * c.nmor + nu]
          if !inset[comp] {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 篩上的相容族：對 m ∈ sieve(c) 給 x_m ∈ F(dom m)，且對可合成對 (m, n) 有 F(n)(x_m) = x_{m∘n}。
fn b8_plus_families(s : B8Site, f : B8PS, cc : Int32) -> Array[Array[Int32]] {
  let c = s.cat
  let sv = s.sieve[cc]
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
  // 預先算出所有相容性三元組 (i, j, pos)
  let ti : Array[Int32] = []
  let tj : Array[Int32] = []
  let tp : Array[Int32] = []
  for i in 0..<n {
    for nn in 0..<c.nmor {
      if c.cod[nn] == c.dom[sv[i]] {
        let mn = c.cmp[sv[i] * c.nmor + nn]
        let mut pos = -1
        for k in 0..<n {
          if sv[k] == mn {
            pos = k
          }
        }
        ti.push(i)
        tj.push(nn)
        tp.push(pos)
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
      if tp[t] < 0 {
        ok = false
      } else if f.res[tj[t] * f.mx + cur[ti[t]]] != cur[tp[t]] {
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
/// 預層行距。
fn b8q_st(sz : Array[Int32]) -> Int32 {
  let mut st = 1
  for v in sz {
    if v > st {
      st = v
    }
  }
  st
}

///|
/// 加號構造 F⁺：物件 c 上放 sieve(c) 的相容族，限制沿 u: c' → c 為 ν ↦ x_{u∘ν}。
pub fn b8_plus(s : B8Site, f : B8PS) -> B8PS {
  let c = s.cat
  let fams : Array[Array[Array[Int32]]] = []
  let sz : Array[Int32] = []
  for cc in 0..<c.nob {
    let fs = b8_plus_families(s, f, cc)
    sz.push(fs.length())
    fams.push(fs)
  }
  let st = b8q_st(sz)
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * st) {
    res.push(0)
  }
  for u in 0..<c.nmor {
    let cd = c.cod[u]
    let dm = c.dom[u]
    let sv = s.sieve[cd]
    let fcd = fams[cd]
    for j in 0..<fcd.length() {
      let key : Array[Int32] = []
      for nu in s.sieve[dm] {
        let un = c.cmp[u * c.nmor + nu]
        let mut pos = -1
        for k in 0..<sv.length() {
          if sv[k] == un {
            pos = k
          }
        }
        key.push(if pos >= 0 { fcd[j][pos] } else { 0 })
      }
      let mut idx = 0
      for k in 0..<fams[dm].length() {
        let g2 = fams[dm][k]
        let mut eq = g2.length() == key.length()
        if eq {
          for t in 0..<key.length() {
            if g2[t] != key[t] {
              eq = false
            }
          }
        }
        if eq {
          idx = k
        }
      }
      res[u * st + j] = idx
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// 層化 a(F) = F⁺⁺。
pub fn b8_sheafify(s : B8Site, f : B8PS) -> B8PS {
  b8_plus(s, b8_plus(s, f))
}

///|
/// 是否為層：F⁺ 與 F 逐物件基數相等（相容族與元素一一對應）。
pub fn b8_is_sheaf(s : B8Site, f : B8PS) -> Bool {
  let p = b8_plus(s, f)
  for cc in 0..<s.cat.nob {
    if p.sz[cc] != f.sz[cc] {
      return false
    }
  }
  true
}

///|
/// 加號構造的階段表：回傳 (|F⁽⁰⁾|,…,|F⁽³⁾| 的總和, 首次穩定步數)。
pub fn b8_plus_stages(s : B8Site, f : B8PS) -> (Array[Int32], Int32) {
  let tot : Array[Int32] = []
  let mut cur = f
  let mut stage = 0
  let mut stab = -1
  for _ in 0..<4 {
    let mut t = 0
    for cc in 0..<s.cat.nob {
      t = t + cur.sz[cc]
    }
    tot.push(t)
    let nxt = b8_plus(s, cur)
    let mut same = true
    for cc in 0..<s.cat.nob {
      if nxt.sz[cc] != cur.sz[cc] {
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
/// 手工預層：每物件大小給定、恆等態射上為恆等、其餘限制映射全為 0（必為良定義的預層）。
pub fn b8_ps_zero(cat : B8Cat, sz : Array[Int32]) -> B8PS {
  let st = b8q_st(sz)
  let res : Array[Int32] = []
  for _ in 0..<(cat.nmor * st) {
    res.push(0)
  }
  for a in 0..<cat.nob {
    let e = cat.idm[a]
    for j in 0..<sz[a] {
      res[e * st + j] = j
    }
  }
  b8_ps_make(cat, sz, res)
}

// ───────────────────────── (C) 無窮組合的有限截斷 ─────────────────────────

///|
/// Kőnig 引理（有限截斷）：二元樹第 L 層有 2^L 個節點，每層至多禁掉一個；
/// 回傳 (每層可用節點數, 貪心無限分支是否存在)。
pub fn b8_konig(
  depth : Int32,
  forbidden : Array[Int32],
) -> (Array[Int32], Bool) {
  let counts : Array[Int32] = []
  let mut cur : Array[Bool] = [true]
  let mut ok = true
  let mut node = 0
  for lvl in 0..<depth {
    let n = 1 << lvl
    let nxt : Array[Bool] = []
    for i in 0..<n {
      let mut a = cur[i / 2]
      if lvl < forbidden.length() && forbidden[lvl] == i {
        a = false
      }
      nxt.push(a)
    }
    let mut cnt = 0
    let mut pick = -1
    for i in 0..<n {
      if nxt[i] {
        cnt = cnt + 1
        if pick < 0 && i / 2 == node {
          pick = i
        }
      }
    }
    counts.push(cnt)
    if pick < 0 {
      ok = false
    } else {
      node = pick
    }
    cur = nxt
  }
  (counts, ok)
}

///|
/// Cantor 集測度：在每個存活子樹中移除一個子節點（質量 2^{-(L+1)}），
/// 回傳前 depth 層累積移除質量（分子, 分母 = 2^depth），以及殘餘質量（分子, 分母）。
pub fn b8_cantor_removed(depth : Int32) -> (Int64, Int64, Int64, Int64) {
  let den = 1L << depth
  let rem = den - 1L
  (rem, den, 1L, den)
}
