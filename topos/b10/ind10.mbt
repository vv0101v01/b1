///|
/// ind10.mbt — 批次十·模組 5：局部化／原子／格里森／空間／索引／相對拓撲斯
///
/// 局部化拓撲斯 E/F（切片）：物件數 = Σ_v |F(v)|，終對象的子對象 = F 的子對象。
/// 原子拓撲斯：每個可表預層恰有 2 個子對象（有限判準）。
/// 格里森拓撲斯：以正則開集布爾代數的 Stone 空間（絕對空間）為底。
/// 空間拓撲斯：點充足。索引／相對拓撲斯：纖維與總範疇的計數分解。

// ───────────────────────── 局部化（切片） ─────────────────────────

///|
/// 切片終對象的子對象數 = E 中 F 的子對象數（分類子的切片版本）。
pub fn b10_slice_sub_terminal(f : B8PS) -> Int32 {
  b9_sub_count(f)
}

///|
/// 開局部化的層數比較：對開集 U，局部化 Sh(X)/よ(U) 的終對象子對象數
/// 應等於 Sh(X) 中 よ(U) 的子對象數（= U 上的篩數）。
pub fn b10_open_localization(s : B9Site, u : Int32) -> (Int32, Int32) {
  let y = b8_ps_yoneda(s.cat, u)
  (b9_sub_count(y), b9_all_sieves(s.cat, u).length())
}

// ───────────────────────── 原子性 ─────────────────────────

///|
/// 子終對象格 O(X) 為布爾代數：每個開集都有補開集。
pub fn b10_frame_boolean(t : B9Top) -> Bool {
  for i in 0..<t.opens.length() {
    let mut has = false
    for j in 0..<t.opens.length() {
      if b10_disjoint(t, i, j) {
        let u = b9_top_union(t, i, j)
        if u >= 0 && b9_pop(t.opens[u]) == t.npt {
          has = true
        }
      }
    }
    if !has {
      return false
    }
  }
  true
}

///|
/// 終對象的子層數（= 子終對象 = 開集）：以層層判準直接枚舉。
pub fn b10_sub_terminal_sh(s : B9Site) -> Int32 {
  b9_sub_count_sh(b9_groth_spatial(s), b8_ps_const(s.cat, 1))
}

///|
/// 原子拓撲斯判準（空間拓撲斯）：Sub(1) = O(X) 為布爾代數 ⟺ X 離散 ⟺ Sh(X) ≅ Set^n 原子。
/// 框架假設：有限空間拓撲斯上「Sub(1) 布爾」與「拓撲斯原子」等價。
pub fn b10_atomic(s : B9Site) -> Bool {
  b10_frame_boolean(s.top) && b10_sub_terminal_sh(s) == s.top.opens.length()
}

// ───────────────────────── 格里森（絕對空間） ─────────────────────────

///|
/// 兩個開集是否不交（交集為空）。
fn b10_disjoint(t : B9Top, i : Int32, j : Int32) -> Bool {
  let k = b9_top_inter(t, i, j)
  k < 0 || b9_pop(t.opens[k]) == 0
}

///|
/// 開集 i 是否包含於開集 j。
fn b10_open_le(t : B9Top, i : Int32, j : Int32) -> Bool {
  for p in 0..<t.npt {
    if t.opens[i][p] && !t.opens[j][p] {
      return false
    }
  }
  true
}

///|
/// int(cl(U)) 的開集編號。
fn b10_int_cl(t : B9Top, i : Int32) -> Int32 {
  // cl(U) = X ∖ ⋃{開集 j : U ∩ j = ∅}
  let inner : Array[Bool] = []
  for _ in 0..<t.npt {
    inner.push(false)
  }
  for j in 0..<t.opens.length() {
    if b10_disjoint(t, i, j) {
      for p in 0..<t.npt {
        if t.opens[j][p] {
          inner[p] = true
        }
      }
    }
  }
  let cl : Array[Bool] = []
  for p in 0..<t.npt {
    cl.push(!inner[p])
  }
  // int(cl(U)) = ⋃{開集 k : k ⊆ cl(U)}
  let acc : Array[Bool] = []
  for _ in 0..<t.npt {
    acc.push(false)
  }
  for k in 0..<t.opens.length() {
    let mut sub = true
    for p in 0..<t.npt {
      if t.opens[k][p] && !cl[p] {
        sub = false
      }
    }
    if sub {
      for p in 0..<t.npt {
        if t.opens[k][p] {
          acc[p] = true
        }
      }
    }
  }
  b9_top_find(t, acc)
}

///|
/// 正則開集：U = int(cl U)。
pub fn b10_regular_opens(t : B9Top) -> Array[Bool] {
  let out : Array[Bool] = []
  for i in 0..<t.opens.length() {
    out.push(b10_int_cl(t, i) == i)
  }
  out
}

///|
/// 正則開集布爾代數的原子數（極小非空正則開集）——格里森覆蓋的點數。
pub fn b10_gleason_atoms(t : B9Top) -> Int32 {
  let reg = b10_regular_opens(t)
  let mut c = 0
  for i in 0..<t.opens.length() {
    if reg[i] && b9_pop(t.opens[i]) > 0 {
      let mut minimal = true
      for j in 0..<t.opens.length() {
        if j != i &&
          reg[j] &&
          b9_pop(t.opens[j]) > 0 &&
          b10_open_le(t, j, i) &&
          !b10_open_le(t, i, j) {
          minimal = false
        }
      }
      if minimal {
        c = c + 1
      }
    }
  }
  c
}

///|
/// 正則開集代數是否為布爾代數（每個元素有補）。
pub fn b10_gleason_boolean(t : B9Top) -> Bool {
  let reg = b10_regular_opens(t)
  for i in 0..<t.opens.length() {
    if reg[i] {
      let mut has = false
      for j in 0..<t.opens.length() {
        if reg[j] && b10_disjoint(t, i, j) {
          // i ∪ j = X ？
          let u = b9_top_union(t, i, j)
          if u >= 0 && b9_pop(t.opens[u]) == t.npt {
            has = true
          }
        }
      }
      if !has {
        return false
      }
    }
  }
  true
}

///|
/// 正則開集計數（含空集）。
pub fn b10_regular_open_count(t : B9Top) -> Int32 {
  let reg = b10_regular_opens(t)
  let mut c = 0
  for i in 0..<t.opens.length() {
    if reg[i] {
      c = c + 1
    }
  }
  c
}

// ───────────────────────── 空間性 ─────────────────────────

///|
/// 空間拓撲斯：點充足且可區分截面。
pub fn b10_spatial(s : B9Site) -> Bool {
  b9_points_distinguished(s)
}

///|
/// Set[G] 的空間性：單一點的纖維函子決定物件（|Hom(U, X)| = |X|）。
pub fn b10_spatial_gset(g : B9Group, xs : Array[B9GSet]) -> Bool {
  for x in xs {
    let (a, b) = b9_classify_check(g, x)
    if a != b {
      return false
    }
    let (c, d) = b9_represent(x)
    if c != d {
      return false
    }
  }
  true
}

// ───────────────────────── 索引與相對拓撲斯 ─────────────────────────

///|
/// 索引拓撲斯的總範疇物件數 = Σ_i |C_i|。
pub fn b10_indexed_total(sites : Array[B9Site]) -> Int32 {
  let mut t = 0
  for s in sites {
    t = t + s.cat.nob
  }
  t
}

///|
/// 相對拓撲斯的纖維計數：沿連結 u 的拉回保乘積與餘積。
pub fn b10_link_preserves(u : B8Fun, f : B8PS, g : B8PS) -> (Bool, Bool) {
  let p1 = b8_ps_eq(
    b8_pull(u, b8_ps_prod(f, g)),
    b8_ps_prod(b8_pull(u, f), b8_pull(u, g)),
  )
  let p2 = b8_ps_eq(
    b8_pull(u, b8_ps_coprod(f, g)),
    b8_ps_coprod(b8_pull(u, f), b8_pull(u, g)),
  )
  (p1, p2)
}
