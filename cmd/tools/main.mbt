///|
/// main.mbt — `moon run cmd/tools --target native -- <子命令>`
///
/// 子命令：
///   deps [--check]   維護／檢查 zz_deps.mbt 與 moon.pkg（取代 tools/regen_deps.py）
///   qualify [--check] 把「只在 test 區塊使用」的名稱改成 @als.name（取代 tools/qualify_test_uses.py）
///   audit            死碼與未使用宣告清單（減債用）
///   dups             逐字重複的函式體（去重用）
///   stats            行數／宣告數統計

///|
const USAGE : String = "用法: moon run cmd/tools --target native -- deps|qualify|audit|dups|stats|why <套件> [--check]"

///|
fn main {
  let argv = @env.args()
  let mut root = "."
  let mut check_only = false
  let pos : Array[String] = []
  let mut i = 1
  while i < argv.length() {
    let a = argv[i]
    if a == "--check" {
      check_only = true
    } else if a == "--root" && i + 1 < argv.length() {
      root = argv[i + 1]
      i = i + 1
    } else {
      pos.push(a)
    }
    i = i + 1
  }
  let cmd = if pos.length() > 0 { pos[0] } else { "stats" }
  let arg1 = if pos.length() > 1 { pos[1] } else { "" }
  match cmd {
    "deps" => run_deps(root, check_only)
    "qualify" => run_qualify(root, check_only)
    "audit" => run_audit(root)
    "dups" => run_dups(root)
    "stats" => run_stats(root)
    "why" => run_why(root, arg1)
    _ => println(USAGE)
  }
}

///|
/// 診斷：某套件為何要 import 某個上層套件（列出被判定的外來名稱）
fn run_why(root : String, target : String) -> Unit {
  let idx = build_index(root)
  let qs = qualified_aliases(idx, target)
  println("qualified: " + qs.length().to_string())
  for q in qs {
    println("  @" + q + " -> [" + alias_to_path2(idx, q) + "]")
  }
  let uses = foreign_uses(idx, target)
  for name, owner in uses {
    println(target + " -> " + owner + " : " + name)
  }
}

///|
fn run_deps(root : String, check_only : Bool) -> Unit {
  let idx = build_index(root)
  let mut drift = 0
  let mut fixed = 0
  for p in idx.pkgs {
    if p.dir == "cmd/tools" {
      continue
    }
    // ── zz_deps：語義比較（忽略排版，moon fmt 可以自由斷行）──
    let want = desired_groups(idx, root, p.dir)
    let have = current_groups(root, p.dir)
    let want_keys = flatten_groups(want)
    let have_keys = flatten_groups(have)
    let zz_path = root + "/" + p.dir + "/zz_deps.mbt"
    let need_write = want_keys.length() != have_keys.length() ||
      ({
        let mut diff = false
        let mut i = 0
        while i < want_keys.length() {
          if i >= have_keys.length() || want_keys[i] != have_keys[i] {
            diff = true
          }
          i = i + 1
        }
        diff
      })
    if need_write {
      drift = drift + 1
      println("[zz_deps 漂移] " + p.dir)
      if !check_only {
        if want_keys.length() == 0 {
          // 沒有需要 using 的名稱：保留既有檔案（可能含手寫註解）
          if have_keys.length() > 0 {
            write_text(zz_path, "")
            fixed = fixed + 1
          }
        } else {
          write_text(zz_path, render_zz(want))
          fixed = fixed + 1
        }
      }
    }
    // ── moon.pkg：同樣以「路徑＋別名」的集合比較 ──
    let aliases : Array[String] = []
    for a in qualified_aliases(idx, p.dir) {
      aliases.push(a)
    }
    for a, _ in want {
      aliases.push(a)
    }
    let pkg_path = root + "/" + p.dir + "/moon.pkg"
    let old = read_text(pkg_path)
    let executable = has_executable(old)
    let new_txt = render_pkg(
      idx.pkgs,
      rank_filter(idx.pkgs, p.dir, aliases),
      executable,
    )
    let want_imp = parse_imports(new_txt)
    let have_imp = parse_imports(old)
    let same = want_imp.length() == have_imp.length() &&
      ({
        let mut eq = true
        let mut i = 0
        while i < want_imp.length() {
          if i >= have_imp.length() || want_imp[i] != have_imp[i] {
            eq = false
          }
          i = i + 1
        }
        eq
      })
    if !same {
      drift = drift + 1
      println("[moon.pkg 漂移] " + p.dir)
      if !check_only {
        write_text(pkg_path, new_txt)
        fixed = fixed + 1
      }
    }
  }
  if drift == 0 {
    println(
      "[PASS] deps：zz_deps.mbt 與 moon.pkg 皆與靜態分析一致（0 漂移）",
    )
  } else {
    println(
      (if check_only {
        "[FAIL] deps：發現 "
      } else {
        "[FIX] deps：已修正 "
      }) +
      drift.to_string() +
      " 處漂移（實際寫入 " +
      fixed.to_string() +
      " 個檔案）",
    )
  }
}

///|
fn has_executable(pkg_txt : String) -> Bool {
  let toks = tokenize(pkg_txt)
  let mut i = 0
  let mut hit = false
  while i + 1 < toks.length() {
    if toks[i] == Ident("pkgtype") && toks[i + 1] == Sym('(') {
      hit = true
    }
    i = i + 1
  }
  hit
}

///|
fn run_stats(root : String) -> Unit {
  let idx = build_index(root)
  println("套件數：" + idx.pkgs.length().to_string())
  let mut files = 0
  let mut lines = 0
  let mut decls = 0
  let mut pub_decls = 0
  for p in idx.pkgs {
    for f in p.files {
      files = files + 1
      let t = read_text(root + "/" + f)
      lines = lines + t.split("\n").count()
    }
    for _d, ds in idx.decls {
      for d in ds {
        if d.pkg == p.dir {
          decls = decls + 1
          if d.is_pub {
            pub_decls = pub_decls + 1
          }
        }
      }
    }
  }
  println("檔案數：" + files.to_string())
  println("行數：" + lines.to_string())
  println(
    "頂層宣告：" +
    decls.to_string() +
    "（公開 " +
    pub_decls.to_string() +
    "）",
  )
}

///|
/// 宣告位置（`fn x` 的 x、`type T` 的 T）不算引用
fn is_decl_pos(toks : Array[Tok], i : Int32) -> Bool {
  if i == 0 {
    return false
  }
  match toks[i - 1] {
    Ident(k) => is_kw_decl(k)
    _ => false
  }
}

///|
/// 全倉引用計數：name → 出現次數（不含宣告位置本身）
fn ref_counts(idx : Index) -> Map[String, Int32] {
  let m : Map[String, Int32] = Map([])
  for _p, srcs in idx.sources {
    for src in srcs {
      let n = src.toks.length()
      let mut i = 0
      while i < n {
        match src.toks[i] {
          Ident(x) =>
            if !is_keyword(x) && !is_decl_pos(src.toks, i) {
              let c = match m.get(x) {
                Some(v) => v
                None => 0
              }
              m[x] = c + 1
            }
          _ => ()
        }
        i = i + 1
      }
    }
  }
  m
}

///|
fn is_kw_decl(k : String) -> Bool {
  k == "fn" ||
  k == "struct" ||
  k == "enum" ||
  k == "type" ||
  k == "trait" ||
  k == "let" ||
  k == "const"
}

///|
fn run_audit(root : String) -> Unit {
  let idx = build_index(root)
  let refs = ref_counts(idx)
  let dead : Array[Decl] = []
  for name, ds in idx.decls {
    let c = match refs.get(name) {
      Some(v) => v
      None => 0
    }
    if c == 0 {
      for d in ds {
        // 程式入口不算死碼
        if (d.kind == "fn" || d.kind == "let" || d.kind == "const") &&
          d.name != "main" {
          dead.push(d)
        }
      }
    }
  }
  println("=== 死碼（宣告後全倉零引用） ===")
  let mut n = 0
  let sorted_names = sort_strs(dead.map(fn(d) { d.name }))
  for nm in sorted_names {
    for d in dead {
      if d.name == nm {
        println("  " + d.file + " : " + d.kind + " " + d.name)
        n = n + 1
      }
    }
  }
  println("死碼合計：" + n.to_string())
  // 只有一個引用的（可疑：可能只是自我遞迴或單點呼叫）
  let once : Array[String] = []
  for name, c in refs {
    if c == 1 && idx.decls.contains(name) {
      let ds = idx.decls[name]
      let mut is_fn = false
      for d in ds {
        if d.kind == "fn" {
          is_fn = true
        }
      }
      if is_fn {
        once.push(name)
      }
    }
  }
  println(
    "僅被引用一次（呼叫鏈葉端）：" + once.length().to_string(),
  )
}

///|
/// 抽出函式體的 token 字串（用於逐字重複偵測）
fn body_key(src : Source, start : Int32) -> String? {
  let toks = src.toks
  let n = toks.length()
  let mut i = start
  let mut seen_brace = false
  let mut depth = 0
  let sb = StringBuilder()
  while i < n {
    match toks[i] {
      Sym('{') => {
        seen_brace = true
        depth = depth + 1
      }
      Sym('}') => {
        depth = depth - 1
        if seen_brace && depth == 0 {
          return Some(sb.to_string())
        }
      }
      _ => ()
    }
    if seen_brace {
      sb.write_string(tok_text(toks[i]))
      sb.write_string(" ")
    }
    i = i + 1
  }
  None
}

///|
fn run_dups(root : String) -> Unit {
  let idx = build_index(root)
  let entries : Map[String, Array[String]] = Map([])
  let mut total = 0
  for p in idx.pkgs {
    for f in p.files {
      let text = read_text(root + "/" + f)
      let src = make_source(p.dir, f, text)
      for d in parse_decls(p.dir, f, text) {
        if d.kind != "fn" {
          continue
        }
        match body_key(src, d.pos) {
          Some(key) =>
            if key.length() >= 120 {
              total = total + 1
              let tag = f + ":" + d.name
              match entries.get(key) {
                Some(a) => a.push(tag)
                None => entries[key] = [tag]
              }
            }
          None => ()
        }
      }
    }
  }
  println(
    "=== 逐字重複的函式體（token 正規化後完全相同，長度 ≥ 120） ===",
  )
  let mut groups = 0
  let mut extra = 0
  let keys : Array[(String, Int32)] = []
  for k, v in entries {
    if v.length() > 1 {
      keys.push((k, v.length()))
    }
  }
  let sorted = keys.copy()
  let mut a = 0
  while a < sorted.length() {
    let mut b = a + 1
    while b < sorted.length() {
      if sorted[b].1 > sorted[a].1 {
        let t = sorted[a]
        sorted[a] = sorted[b]
        sorted[b] = t
      }
      b = b + 1
    }
    a = a + 1
  }
  for pair in sorted {
    groups = groups + 1
    extra = extra + (pair.1 - 1)
    println("  ── 重複 " + pair.1.to_string() + " 份 ──")
    for tag in entries[pair.0] {
      println("     " + tag)
    }
  }
  println(
    "重複群組：" +
    groups.to_string() +
    "，可消除副本：" +
    extra.to_string() +
    "，已掃描函式：" +
    total.to_string(),
  )
}
