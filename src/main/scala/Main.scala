import driver.Driver._

@main def run(): Unit = {
  val source = """
enum Nat extends Type:
  case Zero() extends Nat()
"""
  println(check(source))
}
