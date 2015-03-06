show: "Data.Bool"
bool-int { package: bool-int-1.17 }
bool-ext { import: bool-int package: bool-ext-1.12 }
bool-class { import: bool-int import: bool-ext package: bool-class-1.26 }
himp {
  import: bool-int
  import: bool-class
  article: "HOL4Imp.art"
}
hbool {
  import: bool-int
  import: himp
  article: "HOL4Bool.art"
}
main {
  import: bool-int
  import: bool-class
  import: bool-ext
  import: hbool
  import: himp
}
