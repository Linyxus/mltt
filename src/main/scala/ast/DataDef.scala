package ast

case class ConsDef(name: String, sig: Expr) {
  override def toString(): String =
    s"case $name : $sig"
}

case class DataDef(name: String, sig: Expr, constructors: List[ConsDef]) extends Definition {
  override def toString(): String =
    s"data $name : $sig { ${constructors.map(_.toString).mkString("; ")} }"
}
