///|
/// deps.mbt — 套件圖的靜態維護（取代 `tools/regen_deps.py`）。
///
/// 舊腳本的做法是「跑 `moon check`、解析診斷文字、再改檔案」，那是把編譯器的
/// 人類可讀輸出當成 API，既脆弱又必須 subprocess。這裡改成純靜態：
///
/// 1. 掃出所有套件（`*/moon.pkg` 與 `*/*/moon.pkg`）。
/// 2. 掃出每個檔案的頂層宣告（`fn`/`struct`/`enum`/`type`/`trait`/`let`/`const`）。
/// 3. 對每個套件找「非 test 區塊內、未限定、且非本地宣告」的識別字；
///    若它由別的套件公開宣告，就需要一條 `using @als { name }`。
/// 4. 由 `@als.` 的實際出現位置＋using 反推 `moon.pkg` 的 import。
///
/// 與編譯器語義的對齊點：**test 區塊內的引用不計入 using**（編譯器的未使用偵測
/// 也不計），所以那些名稱必須寫成 `@als.name`——這正是 `qualify` 子命令在做的事。

///|
pub struct Decl {
  name : String
  /// 名稱 token 在檔案 token 串中的位置（供 body_key 使用）
  pos : Int32
  /// "fn" / "struct" / … / "type"
  kind : String
  is_pub : Bool
  pkg : String
  file : String
}

///|
pub struct PkgUnit {
  /// 相對於倉庫根的目錄，例如 "topos/b14"
  dir : String
  als : String
  files : Array[String]
}

///|
fn is_keyword(s : String) -> Bool {
  let kws : Array[String] = [
    "fn", "let", "mut", "const", "type", "typealias", "struct", "enum", "trait",
    "impl", "priv", "pub", "using", "test", "if", "else", "match", "for", "in", "while",
    "loop", "break", "continue", "return", "true", "false", "raise", "suberror",
    "async", "try", "catch", "guard", "extern", "derive", "nominal", "is", "not",
    "as", "with", "default", "static", "declare", "open", "self", "all", "noraise",
    "init",
  ]
  let mut hit = false
  for k in kws {
    if k == s {
      hit = true
    }
  }
  hit
}

///|
fn basename(p : String) -> String {
  let a = p.to_array()
  let mut i = 0
  let mut last = -1
  while i < a.length() {
    if a[i] == '/' {
      last = i
    }
    i = i + 1
  }
  let sb = StringBuilder()
  let mut j = last + 1
  while j < a.length() {
    sb.write_char(a[j])
    j = j + 1
  }
  sb.to_string()
}

///|
/// 套件層級（0 = 最底層）。import 只允許由高 rank 指向低 rank，故圖必然無環。
/// 這個順序是專案的架構契約，寫在工具裡而不是靠慣例。
pub fn pkg_rank(dir : String) -> Int32 {
  if dir == "core" {
    0
  } else if dir == "common" {
    1
  } else if dir == "foundation/b1" {
    2
  } else if dir == "foundation/b2" {
    3
  } else if dir == "foundation/b3" {
    4
  } else if dir == "foundation/b4" {
    5
  } else if dir == "foundation/b5" {
    6
  } else if dir == "foundation/b6" {
    7
  } else if dir == "foundation/b7" {
    8
  } else if dir == "foundation/b8" {
    9
  } else if dir == "topos/b9" {
    10
  } else if dir == "topos/b10" {
    11
  } else if dir == "topos/b11" {
    12
  } else if dir == "topos/b13" {
    13
  } else if dir == "topos/b14" {
    14
  } else if dir == "topos/b15" {
    15
  } else if dir == "foundation/b12" {
    16
  } else if dir == "axioms" {
    17
  } else if dir == "reports" {
    18
  } else if dir == "cmd/main" {
    19
  } else if dir == "cmd/tools" {
    20
  } else {
    99
  }
}

///|
fn is_pkg_dir(path : String) -> Bool {
  @fs.path_exists(path + "/moon.pkg")
}

///|
/// 掃出所有套件（深度 1 與 2；跳過 `_build`／`.` 開頭與 `cmd/tools` 本身）
pub fn list_pkgs(root : String) -> Array[PkgUnit] {
  let out : Array[PkgUnit] = []
  for e in list_dir(root) {
    if e == "" || e[0] == '_' || e[0] == '.' {
      continue
    }
    let d1 = root + "/" + e
    if is_pkg_dir(d1) {
      out.push({ dir: e, als: "@" + e, files: mbt_files(d1, e), })
    }
    // 深度 2（foundation/b1、topos/b14、cmd/main…）
    for e2 in list_dir(d1) {
      if e2 == "" || e2[0] == '_' || e2[0] == '.' {
        continue
      }
      let d2 = d1 + "/" + e2
      if is_pkg_dir(d2) {
        out.push({
          dir: e + "/" + e2,
          als: "@" + e2,
          files: mbt_files(d2, e + "/" + e2),
        })
      }
    }
  }
  out
}

///|
fn mbt_files(dir : String, rel : String) -> Array[String] {
  let out : Array[String] = []
  for f in list_dir(dir) {
    if has_suffix(f, ".mbt") && f != "zz_deps.mbt" {
      out.push(rel + "/" + f)
    }
  }
  sort_strs(out)
}

///|
/// 解析一個檔案的頂層宣告
pub fn parse_decls(pkg : String, file : String, text : String) -> Array[Decl] {
  let src = make_source(pkg, file, text)
  let toks = src.toks
  let n = toks.length()
  let out : Array[Decl] = []
  let mut depth = 0
  let mut i = 0
  while i < n {
    if src.in_test[i] {
      i = i + 1
      continue
    }
    match toks[i] {
      Sym(c) =>
        if c == '{' {
          depth = depth + 1
        } else if c == '}' {
          depth = depth - 1
        }
      _ => ()
    }
    if depth == 0 {
      // 避免重複計數：`pub fn f` 會在 pub 與 fn 兩個 token 各觸發一次
      let prev_is_pub = i >= 1 && toks[i - 1] == Ident("pub")
      let prev_is_pub_all = i >= 4 &&
        toks[i - 4] == Ident("pub") &&
        toks[i - 3] == Sym('(') &&
        toks[i - 2] == Ident("all") &&
        toks[i - 1] == Sym(')')
      if prev_is_pub || prev_is_pub_all {
        i = i + 1
        continue
      }
      let mut j = i
      let mut is_pub = false
      match toks[j] {
        Ident("pub") => {
          is_pub = true
          j = j + 1
          if j < n {
            match toks[j] {
              Sym('(') =>
                if j + 2 < n &&
                  toks[j + 1] == Ident("all") &&
                  toks[j + 2] == Sym(')') {
                  j = j + 3
                }
              _ => ()
            }
          }
        }
        _ => ()
      }
      if j < n {
        match toks[j] {
          Ident(kind) =>
            if kind == "fn" ||
              kind == "struct" ||
              kind == "enum" ||
              kind == "type" ||
              kind == "trait" ||
              kind == "let" ||
              kind == "const" {
              // 跳過泛型參數 `fn[T : Eq] name`
              let mut js = j + 1
              if js < n && toks[js] == Sym('[') {
                let mut depth2 = 0
                let mut moved = true
                while js < n && moved {
                  match toks[js] {
                    Sym('[') => depth2 = depth2 + 1
                    Sym(']') => {
                      depth2 = depth2 - 1
                      if depth2 == 0 {
                        js = js + 1
                        moved = false
                      }
                    }
                    _ => ()
                  }
                  if moved {
                    js = js + 1
                  }
                }
              }
              // fn Type::method / fn name
              if js < n {
                match toks[js] {
                  Ident(name) =>
                    if name != "(" {
                      let mut nm = name
                      if js + 3 < n &&
                        toks[js + 2] == Sym(':') &&
                        toks[js + 3] == Sym(':') {
                        if js + 4 < n {
                          match toks[js + 4] {
                            Ident(m) => nm = m
                            _ => ()
                          }
                        }
                      }
                      out.push({ name: nm, pos: js, kind, is_pub, pkg, file, })
                    }
                  _ => ()
                }
              }
            }
          _ => ()
        }
      }
    }
    i = i + 1
  }
  out
}

///|
pub struct Index {
  /// name → 宣告清單
  decls : Map[String, Array[Decl]]
  /// 套件 → 原始碼（已切好 token）
  sources : Map[String, Array[Source]]
  pkgs : Array[PkgUnit]
}

///|
pub fn build_index(root : String) -> Index {
  let pkgs = list_pkgs(root)
  let decls : Map[String, Array[Decl]] = Map([])
  let sources : Map[String, Array[Source]] = Map([])
  for p in pkgs {
    let srcs : Array[Source] = []
    for f in p.files {
      let text = read_text(root + "/" + f)
      let src = make_source(p.dir, f, text)
      for d in parse_decls(p.dir, f, text) {
        let cur = decls.get(d.name)
        if cur is Some(a) {
          a.push(d)
        } else {
          decls[d.name] = [d]
        }
      }
      srcs.push(src)
    }
    sources[p.dir] = srcs
  }
  { decls, sources, pkgs, }
}

///|
pub fn pkg_of_alias(pkgs : Array[PkgUnit], als : String) -> PkgUnit? {
  let mut r : PkgUnit? = None
  for p in pkgs {
    if p.als == als {
      r = Some(p)
    }
  }
  r
}

///|
/// 本套件宣告過的名字（任何可見性）
pub fn local_names(idx : Index, pkg : String) -> Map[String, Bool] {
  let m : Map[String, Bool] = Map([])
  for _name, ds in idx.decls {
    for d in ds {
      if d.pkg == pkg {
        m[_name] = true
      }
    }
  }
  m
}

///|
/// 本套件所有可能遮蔽外來名字的區域綁定（`let x`、`for x in`、參數、`Some(x) =>`…）
pub fn shadow_names(idx : Index, pkg : String) -> Map[String, Bool] {
  let m : Map[String, Bool] = Map([])
  let srcs = idx.sources.get(pkg)
  if srcs is None {
    return m
  }
  for src in srcs.unwrap() {
    let toks = src.toks
    let n = toks.length()
    let mut i = 0
    while i < n {
      // 參數／欄位宣告 `x : T` 的 x 是綁定名，不是對外來宣告的引用
      match toks[i] {
        Ident(z) =>
          if i + 1 < n &&
            toks[i + 1] == Sym(':') &&
            !(i + 2 < n && toks[i + 2] == Sym(':')) &&
            !is_keyword(z) {
            m[z] = true
          }
        _ => ()
      }
      match toks[i] {
        Ident(k) =>
          if k == "let" || k == "mut" || k == "for" || k == "const" {
            let mut j = i + 1
            if j < n && toks[j] == Ident("mut") {
              j = j + 1
            }
            // 收集綁定名，遇到 `=`／`in`／`:` 即停（`let mut x : T = …`、`for x in …`）
            let mut k2 = 0
            let mut stop = false
            while j + k2 < n && k2 < 12 && !stop {
              match toks[j + k2] {
                Ident("in") => stop = true
                Ident(z) => if !is_keyword(z) { m[z] = true }
                Sym(c) => if c == '=' || c == ':' || c == '{' { stop = true }
                _ => ()
              }
              k2 = k2 + 1
            }
          }
        _ => ()
      }
      i = i + 1
    }
  }
  m
}

///|
/// 找出「本套件非 test 區塊中、未限定引用、且屬於別的套件」的名字
pub fn foreign_uses(idx : Index, pkg : String) -> Map[String, String] {
  let locals = local_names(idx, pkg)
  let shadows = shadow_names(idx, pkg)
  let out : Map[String, String] = Map([])
  let srcs = idx.sources.get(pkg)
  if srcs is None {
    return out
  }
  for src in srcs.unwrap() {
    let n = src.toks.length()
    let mut i = 0
    while i < n {
      if src.in_test[i] {
        i = i + 1
        continue
      }
      match src.toks[i] {
        Ident(x) =>
          if !is_keyword(x) && !locals.contains(x) && !shadows.contains(x) {
            let mut qualified = false
            // 結構體字面量的欄位標籤 `{ q: … }` 不是引用；但 `T::method` 的 T 是
            if i + 1 < n &&
              src.toks[i + 1] == Sym(':') &&
              !(i + 2 < n && src.toks[i + 2] == Sym(':')) {
              qualified = true
            }
            if i > 0 {
              match src.toks[i - 1] {
                At(_) => qualified = true
                Sym(c) =>
                  if c == '.' {
                    qualified = true
                  } else if c == ':' && i > 1 && src.toks[i - 2] == Sym(':') {
                    // `Type::method` 的 method 不算自由引用
                    qualified = true
                  }
                _ => ()
              }
            }
            if !qualified {
              match idx.decls.get(x) {
                Some(ds) => {
                  let mut best : Decl? = None
                  for d in ds {
                    if d.is_pub && d.pkg != pkg {
                      match best {
                        None => best = Some(d)
                        Some(b) => if s_cmp(d.pkg, b.pkg) < 0 { best = Some(d) }
                      }
                    }
                  }
                  match best {
                    Some(b) =>
                      // 只能指向更底層（rank 更小）；否則視為誤判，丟棄
                      if !out.contains(x) && pkg_rank(b.pkg) < pkg_rank(pkg) {
                        out[x] = b.pkg
                      }
                    None => ()
                  }
                }
                None => ()
              }
            }
          }
        _ => ()
      }
      i = i + 1
    }
  }
  out
}

///|
/// 掃出套件內所有 `@als.` 的限定引用（用於反推 import）
pub fn qualified_aliases(idx : Index, pkg : String) -> Array[String] {
  let out : Array[String] = []
  let srcs = idx.sources.get(pkg)
  if srcs is None {
    return out
  }
  for src in srcs.unwrap() {
    let n = src.toks.length()
    let mut i = 0
    while i + 1 < n {
      match src.toks[i] {
        At(a) => if src.toks[i + 1] == Sym('.') { out.push(a) }
        _ => ()
      }
      i = i + 1
    }
  }
  out
}

///|
pub fn alias_to_path2(idx : Index, als : String) -> String {
  alias_to_path(idx.pkgs, als)
}

///|
fn alias_to_path(pkgs : Array[PkgUnit], als : String) -> String {
  match pkg_of_alias(pkgs, "@" + als) {
    Some(p) => "arena/langlands/" + p.dir
    None =>
      if als == "fs" {
        "moonbitlang/x/fs"
      } else if als == "env" {
        "moonbitlang/core/env"
      } else if als == "math" {
        "moonbitlang/core/math"
      } else if als == "bigint" {
        "moonbitlang/core/bigint"
      } else {
        ""
      }
  }
}

///|
/// 產生某套件的 zz_deps.mbt 內容（groups 為 als → 名稱集合）
pub fn render_zz(groups : Map[String, Array[String]]) -> String {
  let aliases = sort_strs(groups.keys().collect())
  let sb = StringBuilder()
  sb.write_string("///|")
  sb.write_string("\n")
  sb.write_string(
    "// 本套件所有檔案共用的跨套件名稱別名（using），由 cmd/tools 維護，請勿手改。",
  )
  for a in aliases {
    sb.write_string("\n\n///|\n")
    let names = sort_strs(groups[a])
    sb.write_string("using @" + a + " {")
    for nm in names {
      sb.write_string("\n  " + nm + ",")
    }
    sb.write_string("\n}")
  }
  sb.write_string("\n")
  sb.to_string()
}

///|
/// 產生某套件的 moon.pkg 內容

///|
/// 把 groups 攤平成排序後的 "alias|name" 清單（語義比較用，忽略排版）
pub fn flatten_groups(groups : Map[String, Array[String]]) -> Array[String] {
  let out : Array[String] = []
  for a, items in groups {
    for it in items {
      out.push("@" + a + "|" + it)
    }
  }
  sort_strs(out)
}

///|
/// 解析 moon.pkg 的 import 區塊 → ["路徑 別名", …]（別名一律帶 @）
pub fn parse_imports(text : String) -> Array[String] {
  let cs = text.to_array()
  let n = cs.length()
  let out : Array[String] = []
  let mut i = 0
  while i < n {
    if cs[i].to_int() == 34 {
      let sb = StringBuilder()
      i = i + 1
      while i < n && cs[i].to_int() != 34 {
        sb.write_char(cs[i])
        i = i + 1
      }
      i = i + 1
      let path = sb.to_string()
      while i < n && cs[i].to_int() == 32 {
        i = i + 1
      }
      let mut als = ""
      if i < n && cs[i].to_int() == 64 {
        let sb2 = StringBuilder()
        i = i + 1
        while i < n && is_ident_char(cs[i].to_int()) {
          sb2.write_char(cs[i])
          i = i + 1
        }
        als = "@" + sb2.to_string()
      } else {
        als = "@" + basename(path)
      }
      out.push(path + " " + als)
      continue
    }
    i = i + 1
  }
  sort_strs(out)
}

///|
/// 依架構層級過濾：只保留 rank 嚴格更小的套件（低層被高層引用；保證 import 圖無環）
pub fn rank_filter(
  pkgs : Array[PkgUnit],
  self_dir : String,
  als : Array[String],
) -> Array[String] {
  let out : Array[String] = []
  for a in als {
    match pkg_of_alias(pkgs, "@" + a) {
      Some(p) => if pkg_rank(p.dir) < pkg_rank(self_dir) { out.push(a) }
      None => out.push(a)
    }
  }
  out
}

///|
/// 產生某套件的 moon.pkg 內容
pub fn render_pkg(
  pkgs : Array[PkgUnit],
  als : Array[String],
  executable : Bool,
) -> String {
  let entries : Array[String] = []
  for a in uniq_strs(als) {
    let path = alias_to_path(pkgs, a)
    if path == "" {
      continue
    }
    let ent = if basename(path) == a {
      "  \"" + path + "\","
    } else {
      "  \"" + path + "\" @" + a + ","
    }
    entries.push(ent)
  }
  let sorted = sort_strs(entries)
  let sb = StringBuilder()
  if sorted.length() > 0 {
    sb.write_string("import {\n")
    for e in sorted {
      sb.write_string(e + "\n")
    }
    sb.write_string("}\n")
  }
  if executable {
    if sorted.length() > 0 {
      sb.write_string("\n")
    }
    sb.write_string("pkgtype(kind: \"executable\")\n")
  }
  sb.to_string()
}

///|
/// 計算某套件應有的 using 分組
pub fn desired_groups(
  idx : Index,
  root : String,
  pkg : String,
) -> Map[String, Array[String]] {
  let uses = foreign_uses(idx, pkg)
  let groups : Map[String, Array[String]] = Map([])
  for name, owner in uses {
    let als = basename(owner)
    let item = if is_upper(name[0].to_int()) { "type " + name } else { name }
    match groups.get(als) {
      Some(a) => a.push(item)
      None => groups[als] = [item]
    }
  }
  let _ = root
  groups
}

///|
/// 事實上的現況（讀回 zz_deps，支援單行與多行兩種排版）
pub fn current_groups(
  root : String,
  pkg : String,
) -> Map[String, Array[String]] {
  let groups : Map[String, Array[String]] = Map([])
  let text = read_text(root + "/" + pkg + "/zz_deps.mbt")
  let toks = tokenize(text)
  let n = toks.length()
  let mut i = 0
  while i + 2 < n {
    match toks[i] {
      Ident("using") =>
        match toks[i + 1] {
          At(a) => {
            let items : Array[String] = []
            let mut k = i + 2
            while k < n && toks[k] != Sym('}') {
              match toks[k] {
                Ident("type") =>
                  if k + 1 < n {
                    match toks[k + 1] {
                      Ident(y) => {
                        items.push("type " + y)
                        k = k + 2
                        continue
                      }
                      _ => ()
                    }
                  }
                Ident(x) => items.push(x)
                _ => ()
              }
              k = k + 1
            }
            groups[a] = items
            i = k
          }
          _ => ()
        }
      _ => ()
    }
    i = i + 1
  }
  groups
}
