///|
/// rigid.mbt — 批次十四·模組 1：剛性拓撲、可容許覆蓋、Tate 非循環性、
/// 譜空間、有限型拓撲、斯科特拓撲。
///
/// 這五個名詞分屬三個世界（剛性解析幾何／譜空間理論／域論），
/// 但在**有限模型**裡共用同一個骨架：一個有限拓撲空間，加上「哪些族算覆蓋」的規則。
/// 本模組把每個名詞降為可判定條件：
///
///   剛性拓撲（rigid / G-topology）＝ 拓撲 + 一個對 ∩ 封閉的有理開集族（Tate）。
///   可容許覆蓋（admissible cover）＝ 由有理開集組成的**有限**族，其並等於目標。
///   Tate 非循環性 ＝ 仿射空間上可容許覆蓋的 Čech 複形在 q ≥ 1 消失。
///   譜空間（spectral space）＝ 清醒 + 開集格為分配格的 T₀ 空間（Hochster）。
///   有限型拓撲 ＝ 拓撲可由有限多個開集的 ∪、∩ 生成；生成數 = 聯集不可約元素數。
///   斯科特拓撲（Scott topology）＝ 上集 + 「導向上界不可被繞過」的拓撲。

///|
/// 有限剛性空間模型：有限拓撲空間 + 有理（可容許）開集族（遮罩清單）。
pub(all) struct B14Rigid {
  top : B14Top
  rational : Array[Int32]
}

///|
/// 建構：只保留真正是開集的有理集，並對 ∩ 取閉包（Tate 的 G-拓撲要求 G1）。
pub fn b14_rigid(top : B14Top, rational : Array[Int32]) -> B14Rigid {
  let base : Array[Int32] = []
  base.push(0)
  base.push(b14_full(top.n))
  for m in rational {
    if b14_is_open(top, m) {
      base.push(m)
    }
  }
  let cur = base
  let mut changed = true
  while changed {
    changed = false
    let len = cur.length()
    for i in 0..<len {
      for j in 0..<len {
        let v = cur[i] & cur[j]
        let mut has = false
        for x in cur {
          if x == v {
            has = true
          }
        }
        if !has {
          cur.push(v)
          changed = true
        }
      }
    }
  }
  { top, rational: b14_top(top.n, cur).opens, }
}

///|
/// 可容許覆蓋：fam 全為有理開集、且並 = u。
pub fn b14_admissible(r : B14Rigid, u : Int32, fam : Array[Int32]) -> Bool {
  let mut all_rational = true
  let mut acc = 0
  for m in fam {
    let mut isr = false
    for x in r.rational {
      if x == m {
        isr = true
      }
    }
    if !isr {
      all_rational = false
    }
    acc = acc | m
  }
  all_rational && acc == u
}

///|
/// 所有可容許覆蓋（有理族的所有子集，過濾出真正覆蓋 u 者）。
pub fn b14_all_covers(r : B14Rigid, u : Int32) -> Array[Array[Int32]] {
  let k = r.rational.length()
  let out : Array[Array[Int32]] = []
  for m in 0..<(1 << k) {
    let fam : Array[Int32] = []
    for j in 0..<k {
      if b14_has(m, j) {
        fam.push(r.rational[j])
      }
    }
    if b14_admissible(r, u, fam) {
      out.push(fam)
    }
  }
  out
}

///|
/// G-拓撲公理：(G1 ∩ 封閉有理族, G2 限制/穩定, G3 遞移, G4 極限族不覆蓋)。
pub fn b14_rigid_axioms(r : B14Rigid) -> (Bool, Bool, Bool, Bool) {
  let mut g1 = b14_is_open(r.top, 0) && b14_is_open(r.top, b14_full(r.top.n))
  for a in r.rational {
    for b in r.rational {
      let v = a & b
      let mut has = false
      for x in r.rational {
        if x == v {
          has = true
        }
      }
      if !has {
        g1 = false
      }
    }
  }
  let mut g2 = true
  let covers = b14_all_covers(r, b14_full(r.top.n))
  for fam in covers {
    for u in r.rational {
      let restr : Array[Int32] = []
      for m in fam {
        restr.push(m & u)
      }
      if !b14_admissible(r, u, restr) {
        g2 = false
      }
    }
  }
  let mut g3 = true
  for fam in covers {
    // 遞移性：每個成員取任一覆蓋，其總並仍須覆蓋 X（窮舉所有組合）
    let lists : Array[Array[Array[Int32]]] = []
    let mut total = 1
    for m in fam {
      let cs = b14_all_covers(r, m)
      lists.push(cs)
      total = total * (if cs.length() == 0 { 1 } else { cs.length() })
    }
    for t in 0..<total {
      let all : Array[Int32] = []
      let mut rem = t
      for cs in lists {
        if cs.length() > 0 {
          let j = rem % cs.length()
          rem = rem / cs.length()
          for x in cs[j] {
            all.push(x)
          }
        }
      }
      if !b14_admissible(r, b14_full(r.top.n), all) {
        g3 = false
      }
    }
  }
  let g4 = b14_rigid_limit_family_ok(r)
  (g1, g2, g3, g4)
}

///|
/// 「剛性單位圓盤」的有限影子：有理開集是遞增鏈 B₀ ⊂ B₁ ⊂ … ⊂ B_{n−1} = X。
/// 取「所有 B_k（k 不含頂端）」這個家族：其並嚴格小於 X，
/// 所以它**不是** X 的可容許覆蓋 —— 這正是剛性拓撲與普通拓撲的分野
/// （可容許性 = 有限性條件，與點集覆蓋無關）。
/// 回傳 true 表示「該家族確實不構成 X 的可容許覆蓋」。
pub fn b14_rigid_limit_family_ok(r : B14Rigid) -> Bool {
  let n = r.top.n
  let fam : Array[Int32] = []
  for k in 0..<n {
    let b = b14_full(k + 1)
    if b14_is_open(r.top, b) && b != b14_full(n) {
      fam.push(b)
    }
  }
  !b14_admissible(r, b14_full(n), fam)
}

///|
/// Čech 同調維數（kind = 0 函數層、1 常數層）。
pub fn b14_cech_hom(
  t : B14Top,
  fam : Array[Int32],
  kind : Int32,
) -> Array[Int32] {
  b14_cx_hom(b14_cech(t, fam, kind))
}

///|
/// 仿射非循環性（Tate）：可容許覆蓋的 Čech 複形滿足 h⁰ = dim Γ(X)、h^q = 0（q ≥ 1）。
pub fn b14_tate_check(
  t : B14Top,
  fam : Array[Int32],
  kind : Int32,
) -> (Bool, Array[Int32]) {
  let h = b14_cech_hom(t, fam, kind)
  let g0 = if kind == 0 {
    b14_fun_dim(b14_full(t.n))
  } else {
    b14_const_dim(t, b14_full(t.n))
  }
  let mut ok = h[0] == g0
  for q in 1..<h.length() {
    if h[q] != 0 {
      ok = false
    }
  }
  (ok, h)
}

///|
/// 覆蓋無關性：兩個可容許覆蓋給出相同的 Čech 同調維數。
pub fn b14_cover_independent(
  t : B14Top,
  fam1 : Array[Int32],
  fam2 : Array[Int32],
  kind : Int32,
) -> Bool {
  b14_cech_hom(t, fam1, kind) == b14_cech_hom(t, fam2, kind)
}

// ───────────────────────── 譜空間 ─────────────────────────

///|
/// 點的完全素濾子 F_x = {開集 U : x ∈ U}，以開集索引表示。
pub fn b14_point_filters(t : B14Top) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for x in 0..<t.n {
    let f : Array[Int32] = []
    for i in 0..<t.opens.length() {
      if b14_has(t.opens[i], x) {
        f.push(i)
      }
    }
    out.push(f)
  }
  out
}

///|
/// 兩族（索引陣列）作為集合是否相同。
pub fn b14_same_families(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut ok = true
  for f in a {
    let mut found = false
    for g in b {
      if f == g {
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
/// 譜空間檢定：(空間, T0, sober, 開集格分配, 點 ↔ 完全素濾子 雙射, 開集數)。
pub fn b14_spectral_check(
  n : Int32,
  le : Array[Array[Int32]],
) -> (B14Top, Bool, Bool, Bool, Bool, Int32) {
  let t = b14_top(n, b14_alex_opens(n, le))
  let lat = b14_lat_of_top(t)
  let (sob, _) = b14_sober(t)
  let bij = b14_same_families(b14_point_filters(t), b14_cprime_filters(lat))
  (t, b14_t0(t), sob, b14_lat_distributive(lat), bij, t.opens.length())
}
// ───────────────────────── 有限型拓撲 ─────────────────────────

///|
/// 格的聯集不可約元素計數：x ≠ ⊥ 且 (x = a∨b ⇒ x = a 或 x = b)。
pub fn b14_join_irreducibles(l : B14Lat) -> Int32 {
  let mut c = 0
  for x in 0..<l.n {
    if x != l.bot {
      let mut irr = true
      for a in 0..<l.n {
        for b in 0..<l.n {
          if l.join[a][b] == x && a != x && b != x {
            irr = false
          }
        }
      }
      if irr {
        c = c + 1
      }
    }
  }
  c
}

// ───────────────────────── 斯科特拓撲 ─────────────────────────

///|
/// 斯科特空間檢定：
/// (空間, 拓撲公理, T0, sober, 斯科特 = 亞歷山大, 全為主要開集, 開集數)。
pub fn b14_scott_check(
  n : Int32,
  le : Array[Array[Int32]],
) -> (B14Top, Bool, Bool, Bool, Bool, Bool, Int32) {
  let sopen = b14_scott_opens(n, le)
  let t = b14_top(n, sopen)
  let aopen = b14_alex_opens(n, le)
  let (ok, _) = b14_top_ok(t)
  let (sob, _) = b14_sober(t)
  let eq = sopen.length() == aopen.length()
  let mut principal = true
  for u in sopen {
    if u != 0 {
      let mut mn = -1
      let mut cnt = 0
      for x in 0..<n {
        if b14_has(u, x) {
          let mut minimal = true
          for y in 0..<n {
            if b14_has(u, y) && y != x && le[y][x] == 1 {
              minimal = false
            }
          }
          if minimal {
            mn = x
            cnt = cnt + 1
          }
        }
      }
      if cnt != 1 {
        mn = -1
      }
      if mn < 0 {
        principal = false
      } else {
        for y in 0..<n {
          if le[mn][y] == 1 && !b14_has(u, y) {
            principal = false
          }
        }
      }
    }
  }
  (t, ok, b14_t0(t), sob, eq, principal, sopen.length())
}

// ───────────────────────── 標準模型 ─────────────────────────

///|
/// 鏈 0 < 1 < … < n−1。
pub fn b14_chain(n : Int32) -> Array[Array[Int32]] {
  let rels : Array[(Int32, Int32)] = []
  for i in 0..<(n - 1) {
    rels.push((i, i + 1))
  }
  b14_poset(n, rels)
}

///|
/// V 形：0 < 1、0 < 2。
pub fn b14_v_shape() -> Array[Array[Int32]] {
  b14_poset(3, [(0, 1), (0, 2)])
}

///|
/// S¹ 的麥科德（McCord）極小模型：兩最小元 0,1、兩最大元 2,3，四條關係全給。
/// 其序複形 = 完全二分圖 K_{2,2} = 四邊環，故弱同倫於 S¹。
pub fn b14_circle_poset() -> Array[Array[Int32]] {
  b14_poset(4, [(0, 2), (0, 3), (1, 2), (1, 3)])
}

///|
/// 菱形：0 < 1、0 < 2、1 < 3、2 < 3（可縮）。
pub fn b14_diamond() -> Array[Array[Int32]] {
  b14_poset(4, [(0, 1), (0, 2), (1, 3), (2, 3)])
}

///|
/// 離散 n 點空間。
pub fn b14_discrete(n : Int32) -> B14Top {
  let out : Array[Int32] = []
  for m in 0..<(1 << n) {
    out.push(m)
  }
  b14_top(n, out)
}

///|
/// 不可分（粗）n 點空間：只有 ∅ 與 X。
pub fn b14_indiscrete(n : Int32) -> B14Top {
  b14_top(n, [0, b14_full(n)])
}

///|
/// 由有限分配格 L 造出它的譜空間 Spec(L)（Hochster／Priestley）：
/// 點 = L 的完全素濾子；基本開集 D(a) = {F : a ∈ F}。
/// 回傳 (空間, 每個格元素 a 對應的基本開集遮罩)。
pub fn b14_spec_of_lat(l : B14Lat) -> (B14Top, Array[Int32]) {
  let filters = b14_cprime_filters(l)
  let np = filters.length()
  let basis : Array[Int32] = []
  for a in 0..<l.n {
    let mut m = 0
    for i in 0..<np {
      let mut mem = false
      for x in filters[i] {
        if x == a {
          mem = true
        }
      }
      if mem {
        m = m | (1 << i)
      }
    }
    basis.push(m)
  }
  (b14_top_basis(np, basis), basis)
}
