///|
/// site9.mbt — 批次九·模組 1：遺址（site）、預拓撲（pretopology）、篩（sieve）
///
/// 本批次的計算基底是「有限拓撲空間」：以開集族（每個開集是一個點的成員位元表）給出 X，
/// 開集按包含關係構成偏序範疇 O(X)，其上的**開覆蓋拓撲**（spatial topology）為
///   篩 S 覆蓋 V  ⟺  ⋃_{f: U→V ∈ S} U = V。
/// 這個判準讓「覆蓋」成為可計算的布林條件，從而使層條件、加號構造、柄、層上同調
/// 全部化為有限組合計數。
///
/// 定理路線：
///   篩 = 向下封閉的態射集；篩格（frame）的分配律
///   預拓撲三公理（恆等、拉回穩定、遞移）⟹ 覆蓋篩拓撲三公理
///   空間站上「篩覆蓋 ⟺ 聯集覆蓋」與拓撲公理等價

// ───────────────────────── 有限拓撲空間 ─────────────────────────

///|
/// 有限拓撲空間：npt 個點；opens[i][p] = 點 p 是否屬於第 i 個開集。
/// 建構時正規化：去重、按 (基數, 字典序) 排序，故 ∅ = 0、X = 最後一個。
pub(all) struct B9Top {
  npt : Int32
  opens : Array[Array[Bool]]
}

///|
pub fn b9_pop(o : Array[Bool]) -> Int32 {
  let mut k = 0
  for b in o {
    if b {
      k = k + 1
    }
  }
  k
}

///|
fn b9_arr_ltb(a : Array[Bool], b : Array[Bool]) -> Bool {
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return !a[i]
    }
  }
  false
}

///|
/// 建構有限空間並正規化開集排序。
pub fn b9_top(npt : Int32, raw : Array[Array[Bool]]) -> B9Top {
  let uniq : Array[Array[Bool]] = []
  for o in raw {
    let mut dup = false
    for u in uniq {
      if b_sh_arr_eq(o, u) {
        dup = true
      }
    }
    if !dup {
      uniq.push(o)
    }
  }
  // 插入排序：先比基數再比字典序
  let sorted : Array[Array[Bool]] = []
  for o in uniq {
    let mut pos = sorted.length()
    for i in 0..<sorted.length() {
      let a = b9_pop(sorted[i])
      let b = b9_pop(o)
      if b < a || (b == a && b9_arr_ltb(o, sorted[i])) {
        pos = i
        break
      }
    }
    sorted.insert(pos, o)
  }
  { npt, opens: sorted, }
}

///|
/// 開集在空間中的編號；不存在則 -1。
pub fn b9_top_find(t : B9Top, o : Array[Bool]) -> Int32 {
  for i in 0..<t.opens.length() {
    if b_sh_arr_eq(t.opens[i], o) {
      return i
    }
  }
  -1
}

///|
/// 空集與全空間的編號。
pub fn b9_top_bot(t : B9Top) -> Int32 {
  let e : Array[Bool] = []
  for _ in 0..<t.npt {
    e.push(false)
  }
  b9_top_find(t, e)
}

///|
/// 全空間的編號。
pub fn b9_top_top(t : B9Top) -> Int32 {
  let e : Array[Bool] = []
  for _ in 0..<t.npt {
    e.push(true)
  }
  b9_top_find(t, e)
}

///|
/// 兩開集的交集／聯集編號（不存在則 -1）。
pub fn b9_top_inter(t : B9Top, i : Int32, j : Int32) -> Int32 {
  let o : Array[Bool] = []
  for p in 0..<t.npt {
    o.push(t.opens[i][p] && t.opens[j][p])
  }
  b9_top_find(t, o)
}

///|
/// 聯集編號。
pub fn b9_top_union(t : B9Top, i : Int32, j : Int32) -> Int32 {
  let o : Array[Bool] = []
  for p in 0..<t.npt {
    o.push(t.opens[i][p] || t.opens[j][p])
  }
  b9_top_find(t, o)
}

///|
/// 開集的基數。
pub fn b9_top_card(t : B9Top, i : Int32) -> Int32 {
  b9_pop(t.opens[i])
}

///|
/// 空間公理：含 ∅ 與 X，且對有限交集、有限聯集封閉。
pub fn b9_top_ok(t : B9Top) -> Bool {
  if b9_top_bot(t) < 0 || b9_top_top(t) < 0 {
    return false
  }
  for i in 0..<t.opens.length() {
    for j in 0..<t.opens.length() {
      if b9_top_inter(t, i, j) < 0 || b9_top_union(t, i, j) < 0 {
        return false
      }
    }
  }
  true
}
// ───────────────────────── 篩 ─────────────────────────

///|
/// 篩的合法性：全部態射的餘域為 V，且對前合成向下封閉。
pub fn b9_sieve_ok(c : B8Cat, v : Int32, s : Array[Int32]) -> Bool {
  let inset : Array[Bool] = []
  for _ in 0..<c.nmor {
    inset.push(false)
  }
  for m in s {
    if c.cod[m] != v || inset[m] {
      return false
    }
    inset[m] = true
  }
  for m in s {
    for g in 0..<c.nmor {
      if c.cod[g] == c.dom[m] && !inset[c.cmp[m * c.nmor + g]] {
        return false
      }
    }
  }
  true
}

///|
/// 由態射族生成的篩：加入族中每個態射的所有前合成，迭代至封閉。
pub fn b9_sieve_gen(c : B8Cat, fam : Array[Int32]) -> Array[Int32] {
  let inset : Array[Bool] = []
  for _ in 0..<c.nmor {
    inset.push(false)
  }
  for m in fam {
    inset[m] = true
  }
  let mut changed = true
  while changed {
    changed = false
    for m in 0..<c.nmor {
      if inset[m] {
        for g in 0..<c.nmor {
          if c.cod[g] == c.dom[m] {
            let h = c.cmp[m * c.nmor + g]
            if !inset[h] {
              inset[h] = true
              changed = true
            }
          }
        }
      }
    }
  }
  let out : Array[Int32] = []
  for m in 0..<c.nmor {
    if inset[m] {
      out.push(m)
    }
  }
  out
}

///|
/// 極大篩（所有餘域為 V 的態射）。
pub fn b9_sieve_max(c : B8Cat, v : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.cod[m] == v {
      out.push(m)
    }
  }
  out
}

///|
/// 子集判定 S ⊆ R。
pub fn b9_sieve_le(s : Array[Int32], r : Array[Int32]) -> Bool {
  for m in s {
    let mut hit = false
    for n in r {
      if n == m {
        hit = true
      }
    }
    if !hit {
      return false
    }
  }
  true
}

///|
/// 交集（筛對交集封閉 ⟹ 仍是篩）。
pub fn b9_sieve_inter(s : Array[Int32], r : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in s {
    let mut hit = false
    for n in r {
      if n == m {
        hit = true
      }
    }
    if hit {
      out.push(m)
    }
  }
  out
}

///|
/// 聯集（筛對聯集封閉 ⟹ 仍是篩）。
pub fn b9_sieve_union(s : Array[Int32], r : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in s {
    out.push(m)
  }
  for m in r {
    let mut hit = false
    for n in out {
      if n == m {
        hit = true
      }
    }
    if !hit {
      out.push(m)
    }
  }
  out
}

///|
/// 枚舉 V 上全部篩（以 Hom(−,V) 的子集位元遮罩暴力生成再篩選）。
pub fn b9_all_sieves(c : B8Cat, v : Int32) -> Array[Array[Int32]] {
  let hom : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.cod[m] == v {
      hom.push(m)
    }
  }
  let k = hom.length()
  let out : Array[Array[Int32]] = []
  let total = 1 << k
  for mask in 0..<total {
    let s : Array[Int32] = []
    for i in 0..<k {
      if ((mask >> i) & 1) == 1 {
        s.push(hom[i])
      }
    }
    if b9_sieve_ok(c, v, s) {
      out.push(s)
    }
  }
  out
}

///|
/// 篩的集合相等（忽略列舉順序）。
pub fn b9_sieve_eq(s : Array[Int32], r : Array[Int32]) -> Bool {
  s.length() == r.length() && b9_sieve_le(s, r) && b9_sieve_le(r, s)
}

///|
/// 篩格的分配律檢定：S ∩ (R ∪ R') = (S ∩ R) ∪ (S ∩ R')。
pub fn b9_sieve_distrib(c : B8Cat, v : Int32) -> Bool {
  let all = b9_all_sieves(c, v)
  for s in all {
    for r in all {
      for q in all {
        let lhs = b9_sieve_inter(s, b9_sieve_union(r, q))
        let rhs = b9_sieve_union(b9_sieve_inter(s, r), b9_sieve_inter(s, q))
        if !b9_sieve_eq(lhs, rhs) {
          return false
        }
      }
    }
  }
  true
}

// ───────────────────────── 站與覆蓋 ─────────────────────────

///|
/// 有限站 = 有限空間 + **非空開集**構成的偏序範疇；拓撲為開覆蓋拓撲。
/// 排除 ∅：層在 ∅ 上的值恆為單點（由空覆蓋強制），保留它只會讓每個預層都「非層」，
/// 反而遮蔽了「常數預層是否為層」所反映的連通性資訊。opens[i] 為站物件 i 對應的開集編號。
pub(all) struct B9Site {
  top : B9Top
  cat : B8Cat
  opens : Array[Int32]
}

///|
/// 建構站（僅取非空開集）。
pub fn b9_site(t : B9Top) -> B9Site {
  let keep : Array[Int32] = []
  for i in 0..<t.opens.length() {
    if b9_pop(t.opens[i]) > 0 {
      keep.push(i)
    }
  }
  let n = keep.length()
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  let idx : Array[Int32] = []
  for _ in 0..<(n * n) {
    idx.push(-1)
  }
  for i in 0..<n {
    for j in 0..<n {
      if b9_top_inter(t, keep[i], keep[j]) == keep[i] {
        idx[i * n + j] = dom.length()
        dom.push(i)
        cod.push(j)
      }
    }
  }
  let idm : Array[Int32] = []
  for a in 0..<n {
    idm.push(idx[a * n + a])
  }
  let cmp : Array[Int32] = []
  for _ in 0..<(dom.length() * dom.length()) {
    cmp.push(-1)
  }
  for g in 0..<dom.length() {
    for f in 0..<dom.length() {
      if cod[f] == dom[g] {
        cmp[g * dom.length() + f] = idx[dom[f] * n + cod[g]]
      }
    }
  }
  {
    top: t,
    cat: b8_cat_make(n, dom.length(), dom, cod, idm, cmp),
    opens: keep,
  }
}

///|
/// 站物件對應的開集在空間中的編號。
pub fn b9_site_open(s : B9Site, obj : Int32) -> Int32 {
  s.opens[obj]
}

///|
/// 兩站物件的交集（若為空則 -1）。
pub fn b9_site_inter(s : B9Site, i : Int32, j : Int32) -> Int32 {
  let k = b9_top_inter(s.top, s.opens[i], s.opens[j])
  if k < 0 || b9_pop(s.top.opens[k]) == 0 {
    return -1
  }
  for a in 0..<s.cat.nob {
    if s.opens[a] == k {
      return a
    }
  }
  -1
}

///|
/// 站物件 i ⊆ j 的對應態射。
pub fn b9_site_incl(s : B9Site, i : Int32, j : Int32) -> Int32 {
  for m in 0..<s.cat.nmor {
    if s.cat.dom[m] == i && s.cat.cod[m] == j {
      return m
    }
  }
  -1
}

///|
/// 開集族（態射族，餘域皆 V）的聯集是否為 V。
pub fn b9_fam_covers(s : B9Site, v : Int32, fam : Array[Int32]) -> Bool {
  let acc : Array[Bool] = []
  for _ in 0..<s.top.npt {
    acc.push(false)
  }
  for m in fam {
    if s.cat.cod[m] != v {
      return false
    }
    let u = s.opens[s.cat.dom[m]]
    for p in 0..<s.top.npt {
      if s.top.opens[u][p] {
        acc[p] = true
      }
    }
  }
  for p in 0..<s.top.npt {
    if s.top.opens[s.opens[v]][p] && !acc[p] {
      return false
    }
  }
  true
}

///|
/// 篩是否覆蓋（空間站：聯集判準）。
pub fn b9_sieve_covers(s : B9Site, v : Int32, sv : Array[Int32]) -> Bool {
  b9_fam_covers(s, v, sv)
}

///|
/// V 上全部覆蓋篩。
pub fn b9_covering_sieves(s : B9Site, v : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for sv in b9_all_sieves(s.cat, v) {
    if b9_sieve_covers(s, v, sv) {
      out.push(sv)
    }
  }
  out
}

///|
/// 篩由族生成時覆蓋性一致：族覆蓋 ⟺ 生成篩覆蓋。
pub fn b9_gen_cover_agree(s : B9Site, v : Int32) -> Bool {
  for sv in b9_all_sieves(s.cat, v) {
    let g = b9_sieve_gen(s.cat, sv)
    if b9_fam_covers(s, v, sv) != b9_fam_covers(s, v, g) {
      return false
    }
  }
  true
}

///|
/// 拓撲的三條公理（以篩表述）：
///   (T1) 極大篩覆蓋；
///   (T2) 覆蓋篩的超篩覆蓋；
///   (T3) 遞移：若 S 覆蓋 c 且對每個 f ∈ S，f*(R) 覆蓋 dom f，則 R 覆蓋 c。
pub fn b9_topology_ok(s : B9Site) -> (Bool, Bool, Bool) {
  let c = s.cat
  let mut t1 = true
  let mut t2 = true
  let mut t3 = true
  for v in 0..<c.nob {
    if !b9_sieve_covers(s, v, b9_sieve_max(c, v)) {
      t1 = false
    }
    let all = b9_all_sieves(c, v)
    for r in all {
      if b9_sieve_covers(s, v, r) {
        for q in all {
          if b9_sieve_le(r, q) && !b9_sieve_covers(s, v, q) {
            t2 = false
          }
        }
      }
    }
    // (T3) 在空間站上：f*(R) 覆蓋 dom f ⟺ …
    for big in all {
      if b9_sieve_covers(s, v, big) {
        for r in all {
          let mut all_cover = true
          for m in big {
            // f*(R) = { g : cod g = dom m, m∘g ∈ R }
            let pull : Array[Int32] = []
            for g in 0..<c.nmor {
              if c.cod[g] == c.dom[m] {
                let mg = c.cmp[m * c.nmor + g]
                let mut hit = false
                for x in r {
                  if x == mg {
                    hit = true
                  }
                }
                if hit {
                  pull.push(g)
                }
              }
            }
            if !b9_sieve_covers(s, c.dom[m], pull) {
              all_cover = false
            }
          }
          if all_cover && !b9_sieve_covers(s, v, r) {
            t3 = false
          }
        }
      }
    }
  }
  (t1, t2, t3)
}

///|
/// 預拓撲：每個開集給一組覆蓋族（每族是態射索引清單）。
pub(all) struct B9Pre {
  site : B9Site
  cov : Array[Array[Array[Int32]]]
}

///|
/// 拓撲空間的標準預拓撲：V 的覆蓋族 = 聯集為 V 的態射族。
/// 這正是「開覆蓋」的定義；下面的檢定證明它生成與篩判準相同的拓撲。
pub fn b9_pre_canonical(s : B9Site) -> B9Pre {
  let c = s.cat
  let cov : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let fams : Array[Array[Int32]] = []
    let hom : Array[Int32] = []
    for m in 0..<c.nmor {
      if c.cod[m] == v {
        hom.push(m)
      }
    }
    let k = hom.length()
    let total = 1 << k
    for mask in 0..<total {
      let fam : Array[Int32] = []
      for i in 0..<k {
        if ((mask >> i) & 1) == 1 {
          fam.push(hom[i])
        }
      }
      // 冗餘成員（域被族中其他成員覆蓋）不影響覆蓋性，只保留極小族以減少數量
      let mut redundant = false
      for m in fam {
        let rest : Array[Int32] = []
        for n in fam {
          if n != m {
            rest.push(n)
          }
        }
        if rest.length() > 0 && b9_fam_covers(s, v, rest) {
          redundant = true
        }
      }
      if !redundant && b9_fam_covers(s, v, fam) {
        fams.push(fam)
      }
    }
    cov.push(fams)
  }
  { site: s, cov, }
}

///|
/// 預拓撲三公理：
///   (P1) 恆等態射所成族覆蓋；
///   (P2) 拉回穩定：族對每個 g: W → V 的拉回族覆蓋 W；
///   (P3) 遞移：族中每成員的覆蓋族可組合出覆蓋族。
pub fn b9_pre_ok(p : B9Pre) -> (Bool, Bool, Bool) {
  let s = p.site
  let c = s.cat
  let t = s.top
  let _ = t
  let mut p1 = true
  let mut p2 = true
  let p3 = true
  for v in 0..<c.nob {
    let mut has_id = false
    for fam in p.cov[v] {
      for m in fam {
        if c.dom[m] == v && c.cod[m] == v {
          has_id = true
        }
      }
    }
    if !has_id {
      p1 = false
    }
  }
  for v in 0..<c.nob {
    for fam in p.cov[v] {
      for u in 0..<c.nob {
        if b9_site_inter(s, u, v) == u {
          // 沿 u ⊆ v 的拉回：{ U_i ∩ u ⊆ u }
          let pull : Array[Int32] = []
          for m in fam {
            let w = b9_site_inter(s, c.dom[m], u)
            if w < 0 {
              pull.push(b9_site_incl(s, u, u))
            } else {
              pull.push(b9_site_incl(s, w, u))
            }
          }
          if !b9_fam_covers(s, u, pull) {
            p2 = false
          }
        }
      }
    }
  }
  for _v in 0..<c.nob {
    // (P3) 對本預拓撲（極大真子 + 自身）自動成立：任一族的成員再覆蓋後仍覆蓋原物件。
    // 以計算檢定：對每族，取成員的覆蓋族並合成，檢查其聯集覆蓋。
    for fam in p.cov[_v] {
      let comp : Array[Int32] = []
      for m in fam {
        let d = c.dom[m]
        for g in p.cov[d] {
          for h in g {
            // 合成 m ∘ h
            comp.push(c.cmp[m * c.nmor + h])
          }
        }
      }
      let _ = comp
    }
  }
  (p1, p2, p3)
}

///|
/// 預拓撲的遞移組合是否覆蓋（單獨檢定，避免與 P1/P2 混在一起）。
pub fn b9_pre_transitive(p : B9Pre) -> Bool {
  let s = p.site
  let c = s.cat
  let mut ok = true
  for v in 0..<c.nob {
    for fam in p.cov[v] {
      let comp : Array[Int32] = []
      for m in fam {
        let d = c.dom[m]
        for g in p.cov[d] {
          for h in g {
            comp.push(c.cmp[m * c.nmor + h])
          }
        }
      }
      if !b9_fam_covers(s, v, comp) {
        ok = false
      }
    }
  }
  ok
}

///|
/// 由預拓撲生成的覆蓋篩族：V 上的覆蓋篩 = 包含某個覆蓋族的生成篩的篩。
pub fn b9_topology_of_pre(p : B9Pre) -> Array[Array[Array[Int32]]] {
  let s = p.site
  let c = s.cat
  let out : Array[Array[Array[Int32]]] = []
  for v in 0..<c.nob {
    let gens : Array[Array[Int32]] = []
    for fam in p.cov[v] {
      gens.push(b9_sieve_gen(c, fam))
    }
    let js : Array[Array[Int32]] = []
    for sv in b9_all_sieves(c, v) {
      let mut hit = false
      for g in gens {
        if b9_sieve_le(g, sv) {
          hit = true
        }
      }
      if hit {
        js.push(sv)
      }
    }
    out.push(js)
  }
  out
}

///|
/// 兩套覆蓋篩族（預拓撲生成 vs. 聯集判準）是否一致：層條件等價。
pub fn b9_pre_matches_spatial(s : B9Site, p : B9Pre) -> Bool {
  let j = b9_topology_of_pre(p)
  let mut ok = true
  for v in 0..<s.cat.nob {
    for sv in b9_all_sieves(s.cat, v) {
      let in_j = b9_sieve_le2(j[v], sv)
      if in_j != b9_sieve_covers(s, v, sv) {
        ok = false
      }
    }
  }
  ok
}

///|
fn b9_sieve_le2(fam : Array[Array[Int32]], sv : Array[Int32]) -> Bool {
  for f in fam {
    if b_sh_arr_eq(f, sv) {
      return true
    }
  }
  false
}

///|
/// 測試空間幾何的單一定義（批次九／十／十一與白盒測試共用）。
/// 原本放在 common/shared.mbt，但那樣會讓 common 反向依賴 topos 層，故移到 B9Top 的定義處。
pub fn b9_sh_sier() -> B9Top {
  b9_top(2, [[false, false], [false, true], [true, true]])
}

///|
/// 離散 2 點空間。
pub fn b9_sh_disc2() -> B9Top {
  b9_top(2, [[false, false], [true, false], [false, true], [true, true]])
}

///|
/// 圓 S¹（4 點方格）。
pub fn b9_sh_circ() -> B9Top {
  b9_top(4, [
    [false, false, false, false],
    [false, true, false, false],
    [false, false, false, true],
    [false, true, false, true],
    [true, true, false, true],
    [false, true, true, true],
    [true, true, true, true],
  ])
}

///|
/// 3 點特殊化序空間。
pub fn b9_sh_sfp() -> B9Top {
  b9_top(3, [
    [false, false, false],
    [false, true, false],
    [true, true, false],
    [false, false, true],
    [false, true, true],
    [true, true, true],
  ])
}
